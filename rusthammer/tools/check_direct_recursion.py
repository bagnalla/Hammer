#!/usr/bin/env python3
"""Check direct-recursion evidence and isolated expected extraction failures."""

import argparse
from pathlib import Path
import subprocess

from check_backend_memo import check_lean
from verify import AENEAS_REV, CHARON_REV, ROOT, output, run


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--aeneas-dir", type=Path, default=ROOT / "target/extraction-tools/aeneas")
    parser.add_argument("--stage", choices=("promoted", "optimized", "consumer", "negative", "all"), default="all")
    args = parser.parse_args()
    checkout = args.aeneas_dir.expanduser().resolve()
    for directory, revision in ((checkout, AENEAS_REV), (checkout / "charon", CHARON_REV)):
        if output("git", "rev-parse", "HEAD", cwd=directory) != revision:
            parser.error(f"{directory}: expected {revision}")
    charon, aeneas = checkout / "charon/bin/charon", checkout / "bin/aeneas"
    if CHARON_REV not in output(charon, "version") or AENEAS_REV[:8] not in output(aeneas, "-version"):
        parser.error("rebuild the extraction binaries at the pinned revisions")
    work = ROOT / "target/direct-recursion"
    work.mkdir(parents=True, exist_ok=True)
    manifest = ROOT / "probes/direct_recursion/Cargo.toml"
    consumer = ROOT / "probes/direct_recursion/consumer/Cargo.toml"
    run("cargo", "fmt", "--manifest-path", manifest, "--check")
    run("cargo", "test", "--manifest-path", manifest, "--target-dir", work / "cargo", "--locked")
    roots = ("configured", "spanned", "recognized", "complete", "twice", "count")

    def extract(mir, directory, names, selected_manifest=manifest, package="rusthammer_direct_recursion_probe", extra=()):
        directory.mkdir(parents=True, exist_ok=True)
        llbc = directory / "direct_recursion.llbc"
        run(charon, "cargo", "--preset=aeneas", "--sysroot", "default", "--mir", mir, *extra,
            *(arg for name in names for arg in ("--start-from-if-exists", f"{package}::{name}")),
            "--include", "rusthammer::_", "--include", "rusthammer_direct_recursion_probe::_",
            "--dest-file", llbc, "--", "--lib", "--manifest-path", selected_manifest,
            "--target-dir", work / "cargo", "--locked")
        return [aeneas, "-backend", "lean", "-namespace", "DirectRecursion", "-dest", directory,
                "-abort-on-error", "-warnings-as-errors", "-no-progress-bar", llbc]

    for stage in ("promoted", "optimized", "consumer"):
        if args.stage not in (stage, "all"):
            continue
        destination = work / stage
        if stage == "consumer":
            run("cargo", "fmt", "--manifest-path", consumer, "--check")
            command = extract("optimized", destination, roots, consumer, "direct_recursion_consumer")
        else:
            command = extract(stage, destination, roots)
        run(*command)
        check_lean(destination, roots)

    if args.stage in ("negative", "all"):
        expected = {
            "named": "Could not find: trait_impl_id",
            "closure": "mixed mutually recursive definitions",
            "function_item": "mixed mutually recursive definitions",
            "pointer": "Arrow types are not supported yet",
        }
        for name, diagnostic in expected.items():
            for mir in ("promoted", "optimized"):
                destination = work / f"negative-{name}-{mir}"
                command = extract(mir, destination, (f"candidates::{name}",))
                result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                (destination / "aeneas.log").write_text(result.stdout)
                if result.returncode == 0 or diagnostic not in result.stdout:
                    raise RuntimeError(f"expected {name}/{mir} failure changed; inspect {destination}")
                print(f"Expected {name} extraction failure reproduced ({mir}).", flush=True)
        # Monomorphization changes the extraction path rather than the API. It is
        # not a drop-in fix with these pins: Aeneas's array-Default prepass fails.
        for mir in ("promoted", "optimized"):
            destination = work / f"negative-monomorphized-{mir}"
            command = extract(mir, destination, ("candidates::named",), extra=("--monomorphize",))
            result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (destination / "aeneas.log").write_text(result.stdout)
            if result.returncode == 0 or "PrePasses.update_array_default" not in result.stdout:
                raise RuntimeError(f"monomorphization diagnostic changed ({mir}); inspect {destination}")
            print(f"Expected monomorphization failure reproduced ({mir}).", flush=True)
    print(f"Direct-recursion checks passed ({args.stage}); positive cases use ordinary recursive functions, not a general recursive combinator.")


if __name__ == "__main__":
    main()
