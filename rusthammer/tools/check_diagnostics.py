#!/usr/bin/env python3
"""Check the private diagnostic hooks, downstream extraction, and preservation proofs."""

import argparse
import json
from pathlib import Path
import re
import subprocess

from verify import AENEAS_REV, CHARON_REV, ROOT, output, run


ENTRIES = {
    "probe": ("run", "quiet", "sample", "close", "decorate", "observe_byte"),
    "consumer": ("alternatives", "borrowed", "backwards", "owned", "effects"),
}

NEGATIVE_ENTRIES = {
    "static_location": ("located", "There should be no bottoms in the value"),
    "inline_static_location": ("negative::located", "There should be no bottoms in the value"),
    "static_effects": ("negative::effects", "interp/InterpProjectors.ml, line 109"),
}

PROOFS = {"collecting_total", "close_preserves", "decorate_preserves", "scoped_preserves",
          "observe_byte_preserves", "run_erases"}


def logged(command, log, cwd=ROOT):
    with log.open("w") as handle:
        result = subprocess.run([str(arg) for arg in command], cwd=cwd,
                                stdout=handle, stderr=subprocess.STDOUT, text=True)
    if result.returncode:
        raise RuntimeError(f"exit {result.returncode}; see {log}\n{log.read_text()[-6000:]}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--aeneas-dir", type=Path, default=ROOT / "target/extraction-tools/aeneas")
    parser.add_argument("--lean-dir", type=Path, default=ROOT / "lean",
                        help="Lean project providing the pinned Aeneas dependency")
    parser.add_argument("--native-only", action="store_true")
    args = parser.parse_args()
    work = ROOT / "target/diagnostics"
    work.mkdir(parents=True, exist_ok=True)
    if not args.native_only:
        (work / "results.json").unlink(missing_ok=True)
    manifests = {"probe": ROOT / "probes/diagnostics/Cargo.toml",
                 "consumer": ROOT / "probes/diagnostics/consumer/Cargo.toml"}
    for manifest in manifests.values():
        run("cargo", "fmt", "--manifest-path", manifest, "--check")
        for features in ("--no-default-features", "--features=alloc"):
            run("cargo", "test", "--manifest-path", manifest, "--target-dir", work / "cargo",
                "--locked", features)
    if args.native_only:
        print("Native diagnostic checks passed; extraction/proofs were not requested.")
        return
    checkout = args.aeneas_dir.expanduser().resolve()
    lean_dir = args.lean_dir.expanduser().resolve()
    charon, aeneas = checkout / "charon/bin/charon", checkout / "bin/aeneas"
    for directory, revision in ((checkout, AENEAS_REV), (checkout / "charon", CHARON_REV)):
        if output("git", "rev-parse", "HEAD", cwd=directory) != revision:
            parser.error(f"{directory}: expected {revision}")
    if CHARON_REV not in output(charon, "version") or AENEAS_REV[:8] not in output(aeneas, "-version"):
        parser.error("rebuild extraction binaries at the pinned revisions")

    results = []
    for case, entries in ENTRIES.items():
        crate = f"rusthammer_diagnostic_{case}"
        for mir in ("promoted", "optimized"):
            destination = work / case / mir
            destination.mkdir(parents=True, exist_ok=True)
            llbc, lean = destination / "diagnostic.llbc", destination / "lean"
            llbc.unlink(missing_ok=True)
            for previous in lean.glob("*.lean"):
                previous.unlink()
            logged([
                charon, "cargo", "--preset=aeneas", "--sysroot", "default", "--mir", mir,
                *(arg for name in entries for arg in ("--start-from-if-exists", f"{crate}::{name}")),
                "--include", "rusthammer::_", "--include", "rusthammer_diagnostic_probe::_",
                "--dest-file", llbc, "--", "--lib", "--manifest-path", manifests[case],
                "--target-dir", work / "cargo", "--locked",
            ], destination / "charon.log")
            logged([
                aeneas, "-backend", "lean", "-namespace", "DiagnosticProbe",
                "-dest", lean, "-abort-on-error", "-warnings-as-errors", "-no-progress-bar", llbc,
            ], destination / "aeneas.log")
            generated = list(lean.glob("*.lean"))
            if len(generated) != 1:
                raise RuntimeError(f"expected one generated module in {lean}")
            code = generated[0].read_text()
            if re.search(r"\b(?:sorry|admit)\b|^\s*(?:axiom|opaque)\s", code, re.M):
                raise RuntimeError(f"unproved or opaque declaration in {generated[0]}")
            for root in entries:
                if not re.search(rf"^def {re.escape(root)}\s", code, re.M):
                    raise RuntimeError(f"missing root {root} in {generated[0]}")
            logged(["lake", "env", "lean", "-DwarningAsError=true", "-DautoImplicit=false", generated[0]],
                   destination / "lean.log", cwd=lean_dir)
            proofs = ROOT / "probes/diagnostics/Preservation.lean"
            if case == "probe":
                # Keep evidence tied to this freshly extracted implementation;
                # no checked-in generated module or handwritten replacement.
                checked = destination / "Preservation.lean"
                checked.write_text(code + "\n" + proofs.read_text())
                logged(["lake", "env", "lean", "-DwarningAsError=true", "-DautoImplicit=false", checked],
                       destination / "proofs.log", cwd=lean_dir)
                proof_log = (destination / "proofs.log").read_text()
                audits = re.findall(r"'DiagnosticProbe.Preservation.(\w+)' depends on axioms:\s*\[([^]]*)\]",
                                    proof_log)
                if {name for name, _ in audits} != PROOFS:
                    raise RuntimeError("missing preservation theorem audits")
                for name, dependencies in audits:
                    if set(dependencies.replace(",", " ").split()) - {"propext", "Quot.sound", "Classical.choice"}:
                        raise RuntimeError(f"unexpected axioms in {name}: {dependencies}")
            results.append({"case": case, "mir": mir, "roots": list(entries), "passed": True,
                            "preservation_proofs": case == "probe"})
            (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")
            print(f"PASS {case}/{mir}: {len(entries)} roots, strict Lean checking", flush=True)
    for case, (entry, expected) in NEGATIVE_ENTRIES.items():
        for mir in ("promoted", "optimized"):
            destination = work / case / mir
            destination.mkdir(parents=True, exist_ok=True)
            llbc = destination / "diagnostic.llbc"
            llbc.unlink(missing_ok=True)
            logged([charon, "cargo", "--preset=aeneas", "--sysroot", "default", "--mir", mir,
                    "--start-from-if-exists", f"rusthammer_diagnostic_consumer::{entry}",
                    "--include", "rusthammer::_", "--include", "rusthammer_diagnostic_probe::_",
                    "--dest-file", llbc, "--", "--lib", "--manifest-path", manifests["consumer"],
                    "--target-dir", work / "cargo", "--locked"], destination / "charon.log")
            try:
                logged([aeneas, "-backend", "lean", "-dest", destination / "lean", "-abort-on-error",
                        "-warnings-as-errors", "-no-progress-bar", llbc], destination / "aeneas.log")
            except RuntimeError:
                if expected not in (destination / "aeneas.log").read_text():
                    raise
            else:
                raise RuntimeError(f"{case} behavior changed; update the investigation")
            results.append({"case": case, "mir": mir, "roots": [entry], "passed": False,
                            "expected_failure": expected})
            (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")
            print(f"EXPECTED UNSUPPORTED {case}/{mir}: retained Aeneas regression", flush=True)

    # Minimize the static-metadata failure away from parsing and mutable backends.
    source = ROOT / "probes/diagnostics/static_metadata.rs"
    run("rustfmt", "--check", source)
    run("rustc", "--crate-type=lib", "--edition=2021", source, "--out-dir", work)
    for entry in ("borrowed", "literal_label", "literal_store"):
        for mir in ("promoted", "optimized"):
            destination = work / "static_metadata" / entry / mir
            destination.mkdir(parents=True, exist_ok=True)
            llbc, lean = destination / "metadata.llbc", destination / "lean"
            llbc.unlink(missing_ok=True)
            for previous in lean.glob("*.lean"):
                previous.unlink()
            logged([charon, "rustc", "--preset=aeneas", "--sysroot", "default", "--mir", mir,
                    "--start-from", f"static_metadata::{entry}", "--dest-file", llbc, "--",
                    "--crate-type=lib", "--edition=2021", source], destination / "charon.log")
            try:
                logged([aeneas, "-backend", "lean", "-dest", lean, "-abort-on-error",
                        "-warnings-as-errors", "-no-progress-bar", llbc], destination / "aeneas.log")
            except RuntimeError:
                expected = "There should be no bottoms in the value"
                if entry == "borrowed" or expected not in (destination / "aeneas.log").read_text():
                    raise
                results.append({"case": f"static_metadata/{entry}", "mir": mir, "passed": False,
                                "expected_failure": expected})
                print(f"EXPECTED UNSUPPORTED static_metadata/{entry}/{mir}", flush=True)
            else:
                if entry != "borrowed":
                    raise RuntimeError(f"{entry} behavior changed; update the investigation")
                generated = list(lean.glob("*.lean"))
                if len(generated) != 1 or not re.search(r"^def borrowed\s", generated[0].read_text(), re.M):
                    raise RuntimeError("missing standalone borrowed metadata control")
                if re.search(r"\b(?:sorry|admit)\b|^\s*(?:axiom|opaque)\s", generated[0].read_text(), re.M):
                    raise RuntimeError("unproved standalone metadata control")
                logged(["lake", "env", "lean", "-DwarningAsError=true", "-DautoImplicit=false", generated[0]],
                       destination / "lean.log", cwd=lean_dir)
                results.append({"case": f"static_metadata/{entry}", "mir": mir, "passed": True})
                print(f"PASS static_metadata/{entry}/{mir}: strict Lean checking", flush=True)
            (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")

    # The unit-valued mark is valid Rust, but Aeneas drops a unit component from
    # the method result while retaining it in the trait dictionary signature.
    source = ROOT / "probes/diagnostics/unit_mark.rs"
    run("rustfmt", "--check", source)
    run("rustc", "--crate-type=lib", "--edition=2021", source, "--out-dir", work)
    for mir in ("promoted", "optimized"):
        destination = work / "unit_mark" / mir
        destination.mkdir(parents=True, exist_ok=True)
        llbc = destination / "unit_mark.llbc"
        generated = destination / "UnitMark.lean"
        llbc.unlink(missing_ok=True)
        generated.unlink(missing_ok=True)
        logged([charon, "rustc", "--preset=aeneas", "--sysroot", "default", "--mir", mir,
                "--start-from", "unit_mark::run", "--dest-file", llbc, "--",
                "--crate-type=lib", "--edition=2021", source], destination / "charon.log")
        logged([aeneas, "-backend", "lean", "-dest", destination, "-abort-on-error",
                "-warnings-as-errors", "-no-progress-bar", llbc], destination / "aeneas.log")
        try:
            logged(["lake", "env", "lean", "-DwarningAsError=true", "-DautoImplicit=false", generated],
                   destination / "lean.log", cwd=lean_dir)
        except RuntimeError:
            error = (destination / "lean.log").read_text()
            if "Type mismatch" not in error or "Silent → Result (Unit × Silent)" not in error:
                raise
        else:
            raise RuntimeError("unit-mark behavior changed; update the investigation")
        results.append({"case": "unit_mark", "mir": mir, "passed": False,
                        "expected_failure": "Lean: unit mark/state return differs from trait signature"})
        (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(f"EXPECTED UNSUPPORTED unit_mark/{mir}: strict Lean type mismatch", flush=True)
    print("Diagnostic probe checks passed; see the report for proof scope and production obligations.")


if __name__ == "__main__":
    main()
