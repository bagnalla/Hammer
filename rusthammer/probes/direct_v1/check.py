#!/usr/bin/env python3
"""Check the private direct-only API probe and specific known-failure controls."""

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

# Reuse the production verifier's tool pins and command helpers.
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from verify import AENEAS_REV, CHARON_REV, ROOT, output, run


PROBE = "rusthammer_direct_v1_probe"
CONSUMER = "rusthammer_direct_v1_consumer"
CASES = {
    "core": (PROBE, (
        "seq", "map", "try_map", "verify", "bind", "choice", "optional",
        "run_parser", "local_callbacks", "opaque_payload", "opaque_number",
        "mapped_number", "owned", "checked", "independent", "ordered",
    )),
    "mavlink": (PROBE, ("mavlink::frame_grammar", "mavlink::parse_frame", "mavlink::heartbeat")),
    "consumer": (CONSUMER, ("local", "owned", "borrowed", "ordered", "dependent", "custom")),
    "consumer_mavlink": (CONSUMER, ("frame",)),
    "borrowed_identity": (PROBE, ("candidates::borrowed_identity",)),
    "named_identity": (PROBE, ("candidates::named_identity",)),
    "consumer_identity": (CONSUMER, ("borrowed_identity",)),
    "function_item_lookup": (PROBE, ("candidates::function_item_lookup",)),
    "pattern_loop": (PROBE, ("candidates::pattern_loop",)),
    "predicate_header": (PROBE, ("mavlink::predicate_header",)),
    "backend_generic": ("backend_closure", ("generic",)),
    "backend_fixed": ("backend_closure", ("fixed",)),
    "partial_pair": ("partial_enum_move", ("partial_pair",)),
    "whole_pair": ("partial_enum_move", ("whole_pair",)),
    "partial_error": ("partial_enum_move", ("partial_error",)),
    "whole_error": ("partial_enum_move", ("whole_error",)),
}

# Match the phase AND the diagnostic. A tool crash or missing dependency is not
# evidence that the intended negative control reproduced its known limitation.
EXPECTED = {
    "borrowed_identity": ("Aeneas", ("Can't end abstraction", "set as non-endable")),
    "consumer_identity": ("Aeneas", ("Can't end abstraction", "set as non-endable")),
    "named_identity": ("Aeneas", ("higher-ranked",)),
    "backend_generic": ("Lean", ("synthesize implicit argument", "Backend")),
    "function_item_lookup": ("Aeneas", ("Arrow types are not supported yet",)),
    "pattern_loop": ("Aeneas", ("Could not match the contexts", "interp/InterpJoin.ml, line 1542")),
    "predicate_header": ("Lean", ("invalid {...} notation, expected type is not known",)),
}


def logged(command, log, cwd=ROOT):
    with log.open("w") as handle:
        result = subprocess.run([str(arg) for arg in command], cwd=cwd,
                                stdout=handle, stderr=subprocess.STDOUT, text=True)
    return result.returncode


def audit(path, roots):
    code = path.read_text()
    if re.search(r"\b(?:sorry|admit)\b|^\s*(?:axiom|opaque)\s", code, re.M):
        raise RuntimeError(f"unproved or opaque declaration in {path}")
    for root in roots:
        name = root.replace("::", ".")
        # Lean quotes reserved identifiers, e.g. the consumer's `local` root.
        if not re.search(rf"^def (?:{re.escape(name)}|«{re.escape(name)}»)\s", code, re.M):
            raise RuntimeError(f"missing extracted root {name} in {path}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--aeneas-dir", type=Path, default=ROOT / "target/extraction-tools/aeneas")
    parser.add_argument("--lean-packages", type=Path, help="optional local Lake package overrides")
    parser.add_argument("--native-only", action="store_true")
    parser.add_argument("--case", choices=CASES, action="append", help="default: all cases")
    args = parser.parse_args()
    work = ROOT / "target/direct-v1"
    work.mkdir(parents=True, exist_ok=True)
    manifests = {
        PROBE: ROOT / "probes/direct_v1/Cargo.toml",
        CONSUMER: ROOT / "probes/direct_v1/consumer/Cargo.toml",
    }
    for manifest in manifests.values():
        run("cargo", "fmt", "--manifest-path", manifest, "--check")
        run("cargo", "test", "--manifest-path", manifest, "--target-dir", work / "cargo", "--locked")
    if args.native_only:
        print("Native direct-v1 checks passed; extraction was not requested.")
        return

    checkout = args.aeneas_dir.expanduser().resolve()
    charon, aeneas = checkout / "charon/bin/charon", checkout / "bin/aeneas"
    for directory, revision in ((checkout, AENEAS_REV), (checkout / "charon", CHARON_REV)):
        if output("git", "rev-parse", "HEAD", cwd=directory) != revision:
            parser.error(f"{directory}: expected {revision}")
    if CHARON_REV not in output(charon, "version") or AENEAS_REV[:8] not in output(aeneas, "-version"):
        parser.error("rebuild the extraction binaries at the pinned revisions")
    lake_args = [] if args.lean_packages is None else [
        f"--packages={args.lean_packages.expanduser().resolve()}",
    ]

    results = []
    for case in args.case or CASES:
        crate, roots = CASES[case]
        for mir in ("promoted", "optimized"):
            destination = work / case / mir
            destination.mkdir(parents=True, exist_ok=True)
            llbc = destination / f"{crate}.llbc"
            lean = destination / "lean"
            lean.mkdir(exist_ok=True)
            llbc.unlink(missing_ok=True)
            for previous in lean.glob("*.lean"):
                previous.unlink()

            if crate in manifests:
                extraction = [
                    charon, "cargo", "--preset=aeneas", "--sysroot", "default", "--mir", mir,
                    *(arg for root in roots for arg in ("--start-from-if-exists", f"{crate}::{root}")),
                    "--include", f"{PROBE}::_",
                    # The MAVLink wrapper borrows the caller's lookup closure.
                    # Extract &F forwarding bodies instead of emitting axioms.
                    "--include", "core::ops::function::impls::_", "--dest-file", llbc,
                    "--", "--lib", "--manifest-path", manifests[crate],
                    "--target-dir", work / "cargo", "--locked",
                ]
            else:
                extraction = [
                    charon, "rustc", "--preset=aeneas", "--sysroot", "default", "--mir", mir,
                    *(arg for root in roots for arg in ("--start-from", f"{crate}::{root}")),
                    "--dest-file", llbc, "--", "--crate-type", "lib", "--edition", "2021",
                    ROOT / "probes" / f"{crate}.rs",
                ]
            commands = (
                ("Charon", extraction),
                ("Aeneas", [
                    aeneas, "-backend", "lean", "-namespace", "DirectV1Probe", "-dest", lean,
                    "-abort-on-error", "-warnings-as-errors", "-no-progress-bar", llbc,
                ]),
            )
            record = {"case": case, "mir": mir}
            for phase, command in commands:
                log = destination / f"{phase.lower()}.log"
                if logged(command, log):
                    record.update(passed=False, phase=phase, log=str(log.relative_to(ROOT)))
                    break
            else:
                generated = list(lean.glob("*.lean"))
                if len(generated) != 1:
                    raise RuntimeError(f"expected one generated Lean module in {lean}")
                try:
                    audit(generated[0], roots)
                except RuntimeError as error:
                    log = destination / "audit.log"
                    log.write_text(str(error) + "\n")
                    record.update(passed=False, phase="audit", log=str(log.relative_to(ROOT)))
                else:
                    log = destination / "lean.log"
                    failed = logged([
                        "lake", *lake_args, "env", "lean", "-DwarningAsError=true",
                        "-DautoImplicit=false", generated[0],
                    ], log, cwd=ROOT / "lean")
                    record.update(passed=not failed, phase="Lean", log=str(log.relative_to(ROOT)))

            expected = EXPECTED.get(case)
            if case in ("partial_pair", "partial_error") and mir == "optimized":
                expected = ("Aeneas", ("There should be no bottoms in the value",))
            if expected is None:
                record["matches_expectation"] = record["passed"]
            else:
                phase, diagnostics = expected
                record["matches_expectation"] = (
                    not record["passed"] and record["phase"] == phase
                    and all(text in (ROOT / record["log"]).read_text() for text in diagnostics)
                )
            results.append(record)
            label = "PASS" if record["passed"] else "EXPECTED FAILURE"
            if not record["matches_expectation"]:
                label = "UNEXPECTED RESULT"
                print("\n".join((ROOT / record["log"]).read_text().splitlines()[:20]), flush=True)
            print(f"{case}/{mir}: {label} ({record['phase']})", flush=True)
            (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")

    passed = sum(result["passed"] for result in results)
    negative = sum(not result["passed"] and result["matches_expectation"] for result in results)
    print(f"{passed} passing translations; {negative} specific expected failures reproduced.")
    if not all(result["matches_expectation"] for result in results):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
