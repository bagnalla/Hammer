#!/usr/bin/env python3
"""Compare RustHammer's library ordering with C for high-first bits and both byte orders."""

import argparse
from pathlib import Path

from check_restricted_order import cases, compare, run
from verify import ROOT


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hammer-lib", required=True, type=Path)
    args = parser.parse_args()
    work = ROOT / "target" / "ordering-comparison"
    work.mkdir(parents=True, exist_ok=True)
    driver = work / "driver"
    # Like the existing primitive/match runners, compile the library source as a
    # module. The no_std crate attribute is irrelevant to the native test driver.
    run("rustc", "--edition", "2021", "-D", "warnings", "-A", "unused_attributes",
        ROOT / "tests" / "compat" / "ordering.rs", "-o", driver)
    corpus = (
        (kind, data, args) for kind, data, args in cases()
        if (args[2] & 2 if kind == "R" else all(flags & 2 for flags in args[:3]))
    )
    compare(args.hammer_lib.expanduser().resolve(), driver, work, corpus)


if __name__ == "__main__":
    main()
