#!/usr/bin/env python3
"""Check the historical unrestricted-order probe, not the revised scope policy."""

import argparse
import ctypes as C
from itertools import islice, product
import os
from pathlib import Path
import re
import subprocess

from verify import AENEAS_REV, CHARON_REV, ROOT, output


PROBES = ROOT / "probes"
WORK = ROOT / "target" / "input-order"


def run(*args, cwd=ROOT, env=None):
    print("+ " + " ".join(map(str, args)), flush=True)
    subprocess.run(args, cwd=cwd, env=env, check=True)


def cases():
    # Exhaustive single-byte contents and normalized two-edge geometries.
    for value, high in product(range(256), range(8)):
        for low in range(8 - high):
            available = 8 - high - low
            for flags, width in product(range(4), sorted({0, available - 1, available, available + 1})):
                yield "R", bytes([value]), (0, high, low, flags, width)
    # Every field width, all orders, both edges, byte boundaries and truncation.
    data = bytes.fromhex("d6ab618217ff005bc9")
    for length in range(len(data) + 1):
        for high in range(8):
            for low in range(8 - high):
                if length == 0 and high + low != 0:
                    continue
                for flags, width in product(range(4), range(65)):
                    yield "R", data[:length], (0, high, low, flags, width)
                    yield "S", data[:length], (0, high, low, flags, width)
        for flags, width in product(range(4), [0, 1, 7, 8, 64]):
            yield "R", data[:length], (length, 0, 0, flags, width)
            yield "S", data[:length], (length, 0, 0, flags, width)
    # Real h_with_endianness scopes, including restoration after inner/outer
    # scopes and zero-width children. No reader-state adapter substitutes for it.
    widths = [(3, 2, 3, 4, 4), (2, 1, 2, 1, 9), (0, 5, 0, 3, 8),
              (7, 8, 10, 9, 16), (0, 64, 0, 0, 1), (0, 0, 0, 0, 0),
              (1, 7, 8, 16, 32), (5, 10, 3, 9, 8)]
    for base, outer, inner, counts, length in product(range(4), range(4), range(4), widths, range(10)):
        yield "N", data[:length], (base, outer, inner, *counts)


def compare(hammer):
    adapter = WORK / "input-order-c.so"
    # internal.h needs POSIX timespec declarations and has unused inline
    # parameters. Keep the adapter warning-clean without auditing those headers.
    run("gcc", "-shared", "-fPIC", "-std=c99", "-D_POSIX_C_SOURCE=200809L",
        "-Wall", "-Wextra", "-Werror", "-isystem", ROOT.parent / "src", PROBES / "input_order_c.c", hammer,
        f"-Wl,-rpath,{hammer.parent}", "-o", adapter)
    driver = WORK / "driver"
    run("rustc", "--edition", "2021", "--cfg", "input_order_driver",
        PROBES / "input_order.rs", "-o", driver)
    library = C.CDLL(str(adapter))
    ptr = C.POINTER(C.c_uint8)
    outptr = C.POINTER(C.c_uint64)
    library.order_read.argtypes = [ptr, C.c_size_t, C.c_size_t, C.c_uint8, C.c_uint8,
                                  C.c_uint8, C.c_size_t, C.c_int, outptr]
    library.order_read.restype = None
    library.order_nested.argtypes = [ptr, C.c_size_t, C.c_uint8, C.c_uint8, C.c_uint8, ptr, outptr]
    library.order_nested.restype = None
    corpus = iter(cases())
    counts = {"R": 0, "S": 0, "N": 0}
    while batch := list(islice(corpus, 4096)):
        requests = [f"{kind} {data.hex() or '-'} {' '.join(map(str, args))}"
                    for kind, data, args in batch]
        actual = subprocess.check_output([driver], input="\n".join(requests) + "\n", text=True).splitlines()
        if len(actual) != len(batch):
            raise AssertionError("missing Rust results")
        for request, (kind, data, args), line in zip(requests, batch, actual):
            input_array = (C.c_uint8 * len(data)).from_buffer_copy(data)
            if kind == "N":
                result = (C.c_uint64 * 7)()
                widths = (C.c_uint8 * 5)(*args[3:])
                library.order_nested(input_array, len(data), *args[:3], widths, result)
            else:
                result = (C.c_uint64 * 5)()
                library.order_read(input_array, len(data), *args, kind == "S", result)
            expected = " ".join(map(str, result)) if result[0] else "0"
            if line != expected:
                raise AssertionError(f"{request}: Rust {line}; C {expected}")
            counts[kind] += 1
    print(f"C agreement: {sum(counts.values()):,} cases {counts}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--aeneas-dir", type=Path, default=Path.home() / "source" / "aeneas")
    parser.add_argument("--hammer-lib", type=Path, help="optional local libhammer.so for differential tests")
    args = parser.parse_args()
    checkout = args.aeneas_dir.expanduser().resolve()
    for directory, revision in [(checkout, AENEAS_REV), (checkout / "charon", CHARON_REV)]:
        if output("git", "rev-parse", "HEAD", cwd=directory) != revision:
            parser.error(f"{directory}: expected {revision}")
    aeneas = checkout / "bin" / "aeneas"
    charon = checkout / "charon" / "bin" / "charon"
    if AENEAS_REV[:8] not in output(aeneas, "-version") or CHARON_REV not in output(charon, "version"):
        parser.error("rebuild the extraction binaries at the pinned revisions")
    WORK.mkdir(parents=True, exist_ok=True)
    run("rustfmt", "--edition", "2021", "--check", PROBES / "input_order.rs",
        PROBES / "input_order_tests.rs", PROBES / "input_order_driver.rs")
    run("rustc", "--edition", "2021", "--test", PROBES / "input_order.rs", "-o", WORK / "native-tests")
    run(WORK / "native-tests")
    proof = PROBES / "input_order_proofs.lean"
    for stage in ["promoted", "optimized"]:
        dest = WORK / stage
        dest.mkdir(exist_ok=True)
        llbc = dest / "input_order.llbc"
        run(charon, "rustc", "--preset=aeneas", "--sysroot", "default", "--mir", stage,
            "--start-from", "input_order::nested", "--start-from", "input_order::skip_bits",
            "--start-from", "input_order::Cursor::new", "--start-from", "input_order::Cursor::parts",
            "--dest-file", llbc, "--", "--crate-type", "lib", "--edition", "2021", PROBES / "input_order.rs")
        run(aeneas, "-backend", "lean", "-namespace", "InputOrder", "-dest", dest,
            "-abort-on-error", "-warnings-as-errors", "-no-progress-bar", llbc)
        generated = dest / "InputOrder.lean"
        for path in [generated, proof]:
            if re.search(r"\b(?:sorry|admit)\b|^\s*(?:axiom|opaque)\s", path.read_text(), re.M):
                parser.error(f"unproved or opaque declaration in {path}")
        run("lake", "env", "lean", "-DwarningAsError=true", "-R", dest,
            "-o", dest / "InputOrder.olean", generated, cwd=ROOT / "lean")
        env = os.environ.copy()
        env["LEAN_PATH"] = str(dest) + (os.pathsep + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
        run("lake", "env", "lean", "-DwarningAsError=true", proof, cwd=ROOT / "lean", env=env)
    if args.hammer_lib:
        compare(args.hammer_lib.expanduser().resolve())
    else:
        print("C comparison skipped; pass --hammer-lib to enable it.")


if __name__ == "__main__":
    main()
