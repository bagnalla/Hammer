#!/usr/bin/env python3
"""Check the private backend/typed-cache probe, without changing the library API."""

import argparse
from pathlib import Path
import re

from verify import AENEAS_REV, CHARON_REV, ROOT, output, run


def check_lean(destination, entries):
    generated = list(destination.glob("*.lean"))
    if len(generated) != 1:
        raise RuntimeError(f"expected one generated module in {destination}")
    code = generated[0].read_text()
    if re.search(r"\b(?:sorry|admit)\b|^\s*(?:axiom|opaque)\s", code, re.M):
        raise RuntimeError(f"unproved or opaque declaration in {generated[0]}")
    for name in entries:
        if not re.search(rf"^def {name}\s", code, re.M):
            raise RuntimeError(f"missing entry point {name} in {generated[0]}")
    run("lake", "env", "lean", "-DwarningAsError=true", generated[0], cwd=ROOT / "lean")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--aeneas-dir", type=Path, default=Path.home() / "source" / "aeneas")
    args = parser.parse_args()
    checkout = args.aeneas_dir.expanduser().resolve()
    for directory, revision in [(checkout, AENEAS_REV), (checkout / "charon", CHARON_REV)]:
        if output("git", "rev-parse", "HEAD", cwd=directory) != revision:
            parser.error(f"{directory}: expected {revision}")
    charon, aeneas = checkout / "charon/bin/charon", checkout / "bin/aeneas"
    if CHARON_REV not in output(charon, "version") or AENEAS_REV[:8] not in output(aeneas, "-version"):
        parser.error("rebuild the extraction binaries at the pinned revisions")

    source = ROOT / "probes/backend_memo.rs"
    work = ROOT / "target/backend-memo"
    work.mkdir(parents=True, exist_ok=True)
    run("rustfmt", "--edition", "2021", "--config", "skip_children=true", "--check", source)
    run("rustc", "--test", "--edition", "2021", "-D", "warnings", source, "-o", work / "tests")
    run(work / "tests")
    roots = ("direct", "packrat", "owned_output", "recursive_direct", "recursive_packrat", "distinct_borrows")
    for mode in ("promoted", "optimized"):
        destination = work / mode
        destination.mkdir(parents=True, exist_ok=True)
        llbc = destination / "backend_memo.llbc"
        run(charon, "rustc", "--preset=aeneas", "--sysroot", "default", "--mir", mode,
            *(arg for name in roots for arg in ("--start-from", f"backend_memo::{name}")),
            "--dest-file", llbc, "--", "--crate-type", "lib", "--edition", "2021", source)
        run(aeneas, "-backend", "lean", "-namespace", "BackendProbe", "-dest", destination,
            "-abort-on-error", "-warnings-as-errors", "-no-progress-bar", llbc)
        check_lean(destination, roots)

    consumer = work / "consumer"
    consumer.mkdir(parents=True, exist_ok=True)
    manifest = ROOT / "probes/backend_memo/consumer/Cargo.toml"
    cargo_args = ("--manifest-path", manifest, "--target-dir", work / "cargo", "--locked")
    run("cargo", "fmt", "--manifest-path", manifest, "--check")
    run("cargo", "check", *cargo_args)
    entries = ("borrowed", "owned", "recursive", "independent_borrows")
    run(charon, "cargo", "--preset=aeneas", "--sysroot", "default",
        *(arg for name in entries for arg in ("--start-from-if-exists", f"backend_consumer::{name}")),
        "--include", "rusthammer_backend_probe::_", "--dest-file", consumer / "backend_consumer.llbc",
        "--", "--lib", *cargo_args)
    run(aeneas, "-backend", "lean", "-namespace", "BackendConsumer", "-dest", consumer,
        "-abort-on-error", "-warnings-as-errors", "-no-progress-bar", consumer / "backend_consumer.llbc")
    check_lean(consumer, entries)
    print("Backend probe passed: native tests, both MIR stages, Cargo consumer, and Lean type-checking.")


if __name__ == "__main__":
    main()
