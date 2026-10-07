#!/usr/bin/env python3
"""Diagnose recursive evaluator dictionaries; failures are expected evidence."""

import argparse
import json
from pathlib import Path
import re
import subprocess

from verify import AENEAS_REV, CHARON_REV, ROOT, output, run


def logged(command, directory, name, *, cwd=ROOT, failure=None):
    result = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    log = directory / f"{name}.log"
    log.write_text(result.stdout)
    if failure is None:
        if result.returncode:
            raise RuntimeError(f"unexpected failure; see {log}")
    elif result.returncode == 0 or failure not in result.stdout:
        raise RuntimeError(f"expected failure containing {failure!r}; see {log}")
    return result.stdout


def inspect_dependencies(llbc, snippet, *, present, mixed):
    crate = json.loads(llbc.read_text())["translated"]
    implementations = [d for d in crate["trait_impls"] if d and
                       snippet in (d["item_meta"]["source_text"] or "")]
    if len(implementations) != 1:
        raise RuntimeError(f"expected exactly one recursive implementation in {llbc}")
    impl = implementations[0]
    impl_id = {"TraitImpl": impl["def_id"]}
    method_id = {"Fun": impl["methods"][0]["skip_binder"]["id"]}
    groups = []
    for group in crate["ordered_decls"]:
        kind, items = next(iter(group.items()))
        ids = items.get("Rec", [items.get("NonRec")])
        ids = ids if kind == "Mixed" else [{kind: i} for i in ids]
        groups.append((kind, ids))
    found = any(impl_id in ids for _, ids in groups)
    cycle = any(kind == "Mixed" and impl_id in ids and method_id in ids
                for kind, ids in groups)
    if found != present or cycle != mixed:
        raise RuntimeError(f"unexpected implementation dependencies in {llbc}")
    (llbc.parent / "dependencies.json").write_text(json.dumps({
        "implementation": impl_id, "method": method_id,
        "implementation_is_ordered": found, "mixed_cycle": cycle,
        "relevant_groups": [ids for _, ids in groups if impl_id in ids or method_id in ids],
    }, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--aeneas-dir", type=Path, default=ROOT / "target/extraction-tools/aeneas")
    parser.add_argument("--candidate-charon", type=Path,
                        help="add a separately built dependency-patch diagnostic; pins stay unchanged")
    args = parser.parse_args()
    checkout = args.aeneas_dir.expanduser().resolve()
    for directory, revision in ((checkout, AENEAS_REV), (checkout / "charon", CHARON_REV)):
        if output("git", "rev-parse", "HEAD", cwd=directory) != revision:
            parser.error(f"{directory}: expected {revision}")
        if output("git", "status", "--porcelain", "--untracked-files=no", cwd=directory):
            parser.error(f"baseline checkout must be clean: {directory}")
    charon, aeneas = checkout / "charon/bin/charon", checkout / "bin/aeneas"
    if CHARON_REV not in output(charon, "version") or AENEAS_REV[:8] not in output(aeneas, "-version"):
        parser.error("rebuild the baseline extraction binaries at the pinned revisions")
    tools = [("baseline", charon)]
    if args.candidate_charon:
        candidate = args.candidate_charon.expanduser().resolve()
        if CHARON_REV not in output(candidate, "version"):
            parser.error("the diagnostic candidate must be based on the pinned Charon revision")
        tools.append(("candidate", candidate))

    work = ROOT / "target/recursive-extraction"
    work.mkdir(parents=True, exist_ok=True)
    (work / "tools.json").write_text(json.dumps({
        "aeneas": output(aeneas, "-version"),
        "charon": [{"kind": name, "path": str(tool), "version": output(tool, "version")}
                   for name, tool in tools],
    }, indent=2) + "\n")
    source = ROOT / "probes/backend_recursive_trait.rs"
    manifest = ROOT / "probes/direct_recursion/Cargo.toml"
    run("rustfmt", "--edition", "2021", "--check", source)
    run("rustc", "--test", "--edition", "2021", "-D", "warnings", source, "-o", work / "tests")
    run(work / "tests")
    run("cargo", "fmt", "--manifest-path", manifest, "--check")
    run("cargo", "test", "--manifest-path", manifest, "--target-dir", work / "cargo", "--locked")

    # This is a separately authored target-language experiment, never a repair of
    # failed generated output. Keep its result distinct from extraction checks.
    model = ROOT / "probes/recursive_extraction/DictionaryFixedPoint.lean"
    audit = logged(["lake", "env", "lean", "-DwarningAsError=true", model],
                   work, "handwritten-model", cwd=ROOT / "lean")
    axioms = re.search(r"depends on axioms: \[([^]]*)\]", audit)
    if not axioms or set(axioms[1].split(", ")) - {"propext", "Classical.choice", "Quot.sound"}:
        raise RuntimeError("unexpected axioms in the handwritten model")

    for tool_name, tool in tools:
        for mir in ("promoted", "optimized"):
            for root in ("plain", "run", "indirect", "named", "named_parser"):
                directory = work / tool_name / mir / root
                directory.mkdir(parents=True, exist_ok=True)
                is_parser = root.startswith("named")
                crate_name = "direct_recursion" if is_parser else "backend_recursive_trait"
                llbc = directory / f"{crate_name}.llbc"
                common = [tool, "cargo" if is_parser else "rustc", "--preset=aeneas",
                          "--sysroot", "default", "--mir", mir, "--dest-file", llbc]
                if is_parser:
                    command = [*common, "--start-from-if-exists",
                               f"rusthammer_direct_recursion_probe::candidates::{root}",
                               "--include", "rusthammer::_",
                               "--include", "rusthammer_direct_recursion_probe::_", "--", "--lib",
                               "--manifest-path", manifest, "--target-dir", directory / "cargo", "--locked"]
                else:
                    command = [*common, "--start-from", f"backend_recursive_trait::{root}", "--",
                               "--crate-type", "lib", "--edition", "2021", source]
                logged(command, directory, "charon")
                recursive = root != "plain"
                candidate_cycle = recursive and tool_name == "candidate"
                omitted = tool_name == "baseline" and root in ("run", "named")
                if recursive:
                    snippet = "Eval<'input, Direct> for Named" if is_parser else "impl Eval<Direct> for Rule"
                    inspect_dependencies(llbc, snippet, present=not omitted, mixed=candidate_cycle)
                expected = ("mixed mutually recursive definitions" if candidate_cycle else
                            "Could not find: trait_impl_id" if omitted else None)
                logged([aeneas, "-backend", "lean", "-namespace", "RecursiveExtraction", "-dest",
                        directory, "-abort-on-error", "-warnings-as-errors", "-no-progress-bar", llbc],
                       directory, "aeneas", failure=expected)
                if expected is None:
                    generated = list(directory.glob("*.lean"))
                    if len(generated) != 1:
                        raise RuntimeError(f"expected one generated file in {directory}")
                    code = generated[0].read_text()
                    if re.search(r"\b(?:sorry|admit)\b|^\s*(?:axiom|opaque)\s", code, re.M):
                        raise RuntimeError(f"admitted/opaque output: {generated[0]}")
                    entry = f"candidates.{root}" if is_parser else root
                    if not re.search(rf"^def {re.escape(entry)}\s", code, re.M):
                        raise RuntimeError(f"missing entry point {entry}")
                    expected = "Unknown constant" if recursive else None
                    diagnostic = logged(["lake", "env", "lean", "-DwarningAsError=true", generated[0]],
                                        directory, "lean", cwd=ROOT / "lean", failure=expected)
                    if recursive:
                        impl_name = "Named.Insts.RusthammerEvalInputDirectTuple" if is_parser else "Rule.Insts.Backend_recursive_traitEvalDirect"
                        if impl_name not in diagnostic:
                            raise RuntimeError(f"unexpected unknown constant; see {directory / 'lean.log'}")
                print(f"{tool_name} {mir} {root}: {expected or 'Lean checked'}", flush=True)
    print("Diagnostics reproduced. Only the ordinary-recursion control passed extraction and Lean.")


if __name__ == "__main__":
    main()
