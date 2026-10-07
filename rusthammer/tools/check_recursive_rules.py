#!/usr/bin/env python3
"""Check the private recursive-rule/left-recursion design against pinned tools."""
import argparse
from pathlib import Path
import subprocess

from check_backend_memo import check_lean
from verify import AENEAS_REV, CHARON_REV, ROOT, output, run


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--aeneas-dir", type=Path, default=ROOT / "target/extraction-tools/aeneas")
    parser.add_argument("--stage", choices=("promoted", "optimized", "consumer", "all"), default="all")
    args = parser.parse_args()
    checkout = args.aeneas_dir.expanduser().resolve()
    for directory, revision in ((checkout, AENEAS_REV), (checkout / "charon", CHARON_REV)):
        if output("git", "rev-parse", "HEAD", cwd=directory) != revision:
            parser.error(f"{directory}: expected {revision}")
    charon, aeneas = checkout / "charon/bin/charon", checkout / "bin/aeneas"
    if CHARON_REV not in output(charon, "version") or AENEAS_REV[:8] not in output(aeneas, "-version"):
        parser.error("rebuild the extraction binaries at the pinned revisions")
    work = ROOT / "target/recursive-rules"
    work.mkdir(parents=True, exist_ok=True)
    manifest = ROOT / "probes/recursive_rules/Cargo.toml"
    consumer_manifest = ROOT / "probes/recursive_rules/consumer/Cargo.toml"
    run("cargo", "fmt", "--manifest-path", manifest, "--check")
    run("cargo", "fmt", "--manifest-path", consumer_manifest, "--check")
    run("cargo", "test", "--manifest-path", manifest, "--target-dir", work / "cargo", "--locked")
    for stage in ("promoted", "optimized", "consumer"):
        if args.stage not in (stage, "all"):
            continue
        destination = work / stage
        destination.mkdir(parents=True, exist_ok=True)
        consumer = stage == "consumer"
        package = "recursive_rules_consumer" if consumer else "rusthammer_recursive_rules_probe"
        roots = ("recursive" if consumer else "parse", "borrowed", "pattern", "owned", "lowered", "bit_span")
        selected_manifest = consumer_manifest if consumer else manifest
        llbc = destination / "rules.llbc"
        run(charon, "cargo", "--preset=aeneas", "--sysroot", "default",
            "--mir", "optimized" if consumer else stage,
            *(arg for name in roots for arg in ("--start-from-if-exists", f"{package}::{name}")),
            "--include", "rusthammer::_", "--include", "rusthammer_recursive_rules_probe::_",
            "--dest-file", llbc, "--", "--lib", "--manifest-path", selected_manifest,
            "--target-dir", work / "cargo", "--locked")
        run(aeneas, "-backend", "lean", "-namespace", "RecursiveRules", "-dest", destination,
            "-abort-on-error", "-warnings-as-errors", "-no-progress-bar", llbc)
        check_lean(destination, roots)
    if args.stage == "all":
        source = ROOT / "probes/recursive_rules/borrowed_sum.rs"
        for stage in ("promoted", "optimized"):
            destination = work / f"borrowed-sum-{stage}"
            destination.mkdir(parents=True, exist_ok=True)
            llbc = destination / "borrowed_sum.llbc"
            run("rustc", "--crate-type", "lib", "--edition", "2021", "-D", "warnings",
                "--emit=metadata", "-o", destination / "native.rmeta", source)
            run(charon, "rustc", "--preset=aeneas", "--sysroot", "default", "--mir", stage,
                "--start-from", "borrowed_sum::replay", "--dest-file", llbc,
                "--", "--crate-type", "lib", "--edition", "2021", source)
            result = subprocess.run([aeneas, "-backend", "lean", "-dest", destination,
                "-abort-on-error", "-warnings-as-errors", "-no-progress-bar", llbc],
                cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (destination / "aeneas.log").write_text(result.stdout)
            if result.returncode == 0 or "Unreachable" not in result.stdout or "InterpBorrowsCore.ml" not in result.stdout:
                raise RuntimeError(f"borrowed-sum diagnostic changed ({stage}); inspect {destination}")
            print(f"Expected borrowed-sum extraction failure reproduced ({stage}).")
    print(f"Recursive-rule design checks passed ({args.stage}); this is not a correctness proof.")


if __name__ == "__main__":
    main()
