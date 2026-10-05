#!/usr/bin/env python3
"""Compare RustHammer's library ordering with C within the supported scope policy."""

import argparse
from pathlib import Path

from check_restricted_order import compare, run
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
    compare(args.hammer_lib.expanduser().resolve(), driver, work)


if __name__ == "__main__":
    main()
