#!/usr/bin/env python3
"""Test Rust, check Lean proofs, and guard dependency extraction compatibility."""

import argparse
from pathlib import Path
import re
import subprocess


AENEAS_REV = "557eff83ecef5083b98a52a94ca7fae63d6c1dab"
CHARON_REV = "c8f15d7d658c86a95658f71ad99cddd4be002e04"
ROOT = Path(__file__).resolve().parents[1]


def output(*args, cwd=None):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def run(*args, cwd=ROOT):
    print("+ " + " ".join(str(arg) for arg in args), flush=True)
    subprocess.run(args, cwd=cwd, check=True)


def translate(aeneas, llbc, destination, namespace):
    run(
        str(aeneas), "-backend", "lean", "-dest", destination,
        "-namespace", namespace, "-abort-on-error", "-warnings-as-errors",
        "-no-progress-bar", llbc,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--aeneas-dir",
        type=Path,
        default=Path.home() / "source" / "aeneas",
        help="local Aeneas checkout containing bin/aeneas and charon/bin/charon",
    )
    args = parser.parse_args()
    checkout = args.aeneas_dir.expanduser().resolve()
    aeneas = checkout / "bin" / "aeneas"
    charon = checkout / "charon" / "bin" / "charon"

    for directory, expected in [(checkout, AENEAS_REV), (checkout / "charon", CHARON_REV)]:
        actual = output("git", "rev-parse", "HEAD", cwd=directory)
        if actual != expected:
            parser.error(f"{directory}: expected revision {expected}, found {actual}")
    if AENEAS_REV[:8] not in output(str(aeneas), "-version"):
        parser.error("the Aeneas binary does not match the pinned revision; rebuild it")
    if CHARON_REV not in output(str(charon), "version"):
        parser.error("the Charon binary does not match the pinned revision; rebuild it")

    run("cargo", "fmt", "--check")
    run("cargo", "test", "--locked", "--no-default-features")
    run("cargo", "test", "--locked", "--features", "alloc")
    # Reuse the exact same roots at both MIR stages. Dependencies expose the
    # later stage, which can contain cleanup code absent from promoted MIR.
    library_extraction = (
        str(charon), "cargo", "--preset=aeneas", "--sysroot", "default",
        "--start-from", "rusthammer::parse_flags",
        "--start-from", "rusthammer::take_aligned",
        "--start-from", "rusthammer::read_bits",
        "--start-from", "rusthammer::parse_marker",
        "--start-from", "rusthammer::parse_record",
        "--start-from", "rusthammer::Bits::new",
        "--start-from", "rusthammer::Bits::width",
        "--start-from", "rusthammer::Literal::new",
        "--start-from", "rusthammer::Literal::width",
        "--start-from", "rusthammer::Literal::value",
        "--start-from", "rusthammer::Marker::new",
        "--start-from", "rusthammer::RecordParser::new",
        "--start-from", "rusthammer::Fail::new",
        "--start-from", "{impl core::default::Default for rusthammer::Fail}",
        "--start-from", "rusthammer::Repeat::new",
        "--start-from", "rusthammer::Repeat::exact",
        "--start-from", "rusthammer::Repeat::at_least",
        "--start-from", "rusthammer::Repeat::min",
        "--start-from", "rusthammer::Repeat::max",
        "--start-from", "{impl rusthammer::Parser for _}",
        "--start-from", "{impl core::clone::Clone for rusthammer::_}",
        "--include", "core::option::{impl core::clone::Clone for core::option::Option}",
    )
    run(
        *library_extraction,
        "--dest-file", "target/rusthammer.llbc", "--", "--lib", "--locked", "--features", "alloc",
    )
    translate(aeneas, "target/rusthammer.llbc", "lean/RustHammer", "RustHammer.Code")

    optimized = ROOT / "target" / "optimized"
    optimized.mkdir(parents=True, exist_ok=True)
    run(
        *library_extraction, "--mir", "optimized",
        "--dest-file", optimized / "rusthammer.llbc",
        "--", "--lib", "--locked", "--features", "alloc",
    )
    translate(aeneas, optimized / "rusthammer.llbc", optimized / "lean", "RustHammer.Optimized")

    # This is a separate Cargo package with a normal path dependency. Keep its
    # outputs under the main target directory; Charon runs in each package's cwd,
    # so its output path must be absolute. The consumer is compiled last.
    consumer = ROOT / "target" / "cross-crate"
    consumer.mkdir(parents=True, exist_ok=True)
    manifest = ROOT / "probes" / "cross_crate" / "Cargo.toml"
    cargo_args = ("--manifest-path", manifest, "--target-dir", consumer / "cargo", "--locked")
    run("cargo", "fmt", "--manifest-path", manifest, "--check")
    run("cargo", "test", *cargo_args, "--no-default-features")
    run("cargo", "test", *cargo_args, "--features", "alloc")
    entries = ("checked_flag", "packet", "complete_bit", "blocks", "leading_ones")
    entry_args = [
        arg for name in entries
        for arg in ("--start-from-if-exists", f"rusthammer_cross_crate_probe::{name}")
    ]
    run(
        str(charon), "cargo", "--preset=aeneas", "--sysroot", "default",
        *entry_args, "--include", "rusthammer::_",
        "--dest-file", consumer / "rusthammer_cross_crate_probe.llbc",
        "--", "--lib", *cargo_args, "--features", "alloc",
    )
    translate(
        aeneas, consumer / "rusthammer_cross_crate_probe.llbc",
        consumer / "lean", "RustHammer.Consumer",
    )
    consumer_lean = consumer / "lean" / "RusthammerCrossCrateProbe.lean"
    # The if-exists roots intentionally skip the dependency's own compiler run.
    # Do not mistake an empty dependency extraction for a successful consumer run.
    for name in entries:
        if not re.search(rf"^def {name}\s", consumer_lean.read_text(), re.M):
            parser.error(f"missing consumer entry point {name} in {consumer_lean}")

    compatibility_files = [optimized / "lean" / "Rusthammer.lean", consumer_lean]

    # Check project code only; dependency models remain part of the trust boundary.
    for path in [*(ROOT / "lean" / "RustHammer").glob("*.lean"), *compatibility_files]:
        if re.search(r"\b(?:sorry|admit)\b|^\s*(?:axiom|opaque)\s", path.read_text(), re.M):
            parser.error(f"unproved or opaque declaration in {path}")
    run("lake", "build", cwd=ROOT / "lean")
    for path in compatibility_files:
        run("lake", "env", "lean", "-DwarningAsError=true", path, cwd=ROOT / "lean")


if __name__ == "__main__":
    main()
