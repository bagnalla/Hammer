#!/usr/bin/env python3
"""Check integer controls and reproduce unsupported floating-point translations."""

import argparse
import json
from pathlib import Path
import re
import subprocess

from verify import AENEAS_REV, CHARON_REV, ROOT, output, run


CASES = (
    "identity32", "identity64", "decode32", "decode64", "encode32", "encode64",
    "range32", "range64", "range32_double_bounds", "equal32", "nan32", "widen", "literal", "raw_field",
    "float_field", "mapped_field", "nan_bits32", "half_bits", "decode16",
)

BODY_CASES = {
    # The Charon CLI parses f32/f64 in an impl pattern as paths rather than
    # primitive types. A module pattern reliably includes the reached methods.
    "decode32_body": ("decode32", "core::f32::_"),
    "decode64_body": ("decode64", "core::f64::_"),
    "encode32_body": ("encode32", "core::f32::_"),
    "encode64_body": ("encode64", "core::f64::_"),
}

CONSUMER_CASES = {"consumer_encoding": "encoding", "consumer_packet": "packet"}

# A passing command must reproduce the particular limitation, not merely fail.
# Missing F32/F64 must not silently become implicit polymorphic type parameters.
EXPECTED_FAILURES = {
    "identity32": ("Lean", "Unknown identifier `F32`"),
    "identity64": ("Lean", "Unknown identifier `F64`"),
    "decode32": ("audit", "axiom core.f32.F32.from_bits"),
    "decode64": ("audit", "axiom core.f64.F64.from_bits"),
    "encode32": ("audit", "axiom core.f32.F32.to_bits"),
    "encode64": ("audit", "axiom core.f64.F64.to_bits"),
    "range32": ("Aeneas", "Invalid inputs for binop"),
    "range64": ("Aeneas", "Invalid inputs for binop"),
    "range32_double_bounds": ("Aeneas", "Invalid inputs for binop"),
    "equal32": ("Lean", "Unknown identifier `F32`"),
    "nan32": ("audit", "axiom core.f32.F32.is_nan"),
    "widen": ("Aeneas", "Compiler source: extract/Extract.ml, line 487"),
    "literal": ("Aeneas", "Improperly typed constant value"),
    "float_field": ("audit", "axiom core.f32.F32.from_bits"),
    "mapped_field": ("audit", "axiom core.f32.F32.from_bits"),
    "decode16": ("audit", "axiom core.f32.F32.from_bits"),
    **{case: ("Aeneas", "Invalid input for unop: transmute") for case in BODY_CASES},
    "consumer_packet": ("audit", "axiom core.f32.F32.from_bits"),
}


def logged(command, log, cwd=ROOT):
    with log.open("w") as handle:
        result = subprocess.run([str(arg) for arg in command], cwd=cwd,
                                stdout=handle, stderr=subprocess.STDOUT, text=True)
    return result.returncode


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--aeneas-dir", type=Path, default=ROOT / "target/extraction-tools/aeneas")
    cases = CASES + tuple(BODY_CASES) + tuple(CONSUMER_CASES)
    parser.add_argument("--case", choices=cases, action="append", help="default: all cases")
    parser.add_argument("--native-only", action="store_true")
    args = parser.parse_args()
    work = ROOT / "target/floating-point"
    work.mkdir(parents=True, exist_ok=True)
    manifests = {
        "probe": ROOT / "probes/floating_point/Cargo.toml",
        "consumer": ROOT / "probes/floating_point/consumer/Cargo.toml",
    }
    for manifest in manifests.values():
        run("cargo", "fmt", "--manifest-path", manifest, "--check")
        run("cargo", "test", "--manifest-path", manifest, "--target-dir", work / "cargo", "--locked")
    if args.native_only:
        print("Native floating-point checks passed; extraction was not requested.")
        return
    checkout = args.aeneas_dir.expanduser().resolve()
    charon, aeneas = checkout / "charon/bin/charon", checkout / "bin/aeneas"
    for directory, revision in ((checkout, AENEAS_REV), (checkout / "charon", CHARON_REV)):
        if output("git", "rev-parse", "HEAD", cwd=directory) != revision:
            parser.error(f"{directory}: expected {revision}")
    if CHARON_REV not in output(charon, "version") or AENEAS_REV[:8] not in output(aeneas, "-version"):
        parser.error("rebuild the extraction binaries at the pinned revisions")

    results = []
    for case in args.case or cases:
        consumer = case in CONSUMER_CASES
        manifest = manifests["consumer" if consumer else "probe"]
        crate = "rusthammer_float_consumer" if consumer else "rusthammer_float_probe"
        if consumer:
            root = CONSUMER_CASES[case]
        elif case in BODY_CASES:
            root = BODY_CASES[case][0]
        else:
            root = case
        extra = ["--include", BODY_CASES[case][1]] if case in BODY_CASES else []
        for mir in ("promoted", "optimized"):
            destination = work / case / mir
            destination.mkdir(parents=True, exist_ok=True)
            llbc = destination / "float_probe.llbc"
            lean = destination / "lean"
            llbc.unlink(missing_ok=True)
            for previous in lean.glob("*.lean"):
                previous.unlink()
            record = {"case": case, "mir": mir}
            commands = (
                ("Charon", [
                    charon, "cargo", "--preset=aeneas", "--sysroot", "default", "--mir", mir,
                    "--start-from-if-exists", f"{crate}::{root}", "--include", "rusthammer::_",
                    "--include", "rusthammer_float_probe::_", *extra,
                    "--dest-file", llbc, "--", "--lib", "--manifest-path", manifest,
                    "--target-dir", work / "cargo", "--locked",
                ]),
                ("Aeneas", [
                    aeneas, "-backend", "lean", "-namespace", "FloatProbe",
                    "-dest", lean, "-abort-on-error", "-warnings-as-errors", "-no-progress-bar", llbc,
                ]),
            )
            for phase, command in commands:
                log = destination / f"{phase.lower()}.log"
                if logged(command, log):
                    record.update(passed=False, phase=phase, log=str(log.relative_to(ROOT)))
                    break
            else:
                generated = list(lean.glob("*.lean"))
                if len(generated) != 1:
                    raise RuntimeError(f"expected one generated module in {lean}")
                code = generated[0].read_text()
                if re.search(r"\b(?:sorry|admit)\b|^\s*(?:axiom|opaque)\s", code, re.M):
                    record.update(passed=False, phase="audit", log=str(generated[0].relative_to(ROOT)))
                elif not re.search(rf"^def {re.escape(root)}\s", code, re.M):
                    raise RuntimeError(f"missing root {root} in {generated[0]}")
                else:
                    log = destination / "lean.log"
                    failed = logged(["lake", "env", "lean", "-DwarningAsError=true",
                                     "-DautoImplicit=false", generated[0]],
                                    log, cwd=ROOT / "lean")
                    record.update(passed=not failed, phase="Lean", log=str(log.relative_to(ROOT)))
            expected = EXPECTED_FAILURES.get(case)
            if expected is None:
                record["matches_expectation"] = record["passed"]
            else:
                phase, diagnostic = expected
                record["matches_expectation"] = (
                    not record["passed"] and record["phase"] == phase
                    and diagnostic in (ROOT / record["log"]).read_text()
                )
            results.append(record)
            label = "SUPPORTED" if record["passed"] else "UNSUPPORTED"
            if not record["matches_expectation"]:
                label = "UNEXPECTED " + label
            print(f"{case}/{mir}: {label} ({record['phase']})", flush=True)
            (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    supported = sum(result["passed"] for result in results)
    expected_failures = sum(not result["passed"] and result["matches_expectation"] for result in results)
    print(f"{supported} supported translations; {expected_failures} expected unsupported cases reproduced.")
    if not all(result["matches_expectation"] for result in results):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
