#!/usr/bin/env python3
"""Check the private probe of byte-boundary ordering scopes and its Lean contracts."""

import argparse
import ctypes as C
from itertools import islice, product
import os
from pathlib import Path
import re
import subprocess

from verify import AENEAS_REV, CHARON_REV, ROOT, output


PROBES = ROOT / "probes"
WORK = ROOT / "target" / "restricted-order"
THEOREMS = {
    "cursor_valid_spec", "boundary_error_spec", "bit_order_ne_spec", "finish_scope_spec",
    "with_order_spec", "with_order_blocked", "finish_success_aligned",
    "guard_none_iff", "scope_success_aligned",
}


def run(*args, cwd=ROOT, env=None):
    print("+ " + " ".join(map(str, args)), flush=True)
    subprocess.run(args, cwd=cwd, env=env, check=True)


def cases():
    for value, bit, flags, width in product(range(256), range(8), range(4), range(10)):
        yield "R", bytes([value]), (0, bit, flags, width)
    data = bytes.fromhex("d6ab618217ff005bc912345678")
    for length in range(10):
        for bit, flags, width in product(range(8) if length else [0], range(4), range(65)):
            yield "R", data[:length], (0, bit, flags, width)
        for flags, width in product(range(4), [0, 1, 8, 64]):
            yield "R", data[:length], (length, 0, flags, width)
    widths = [(3, 2, 3, 4, 4), (0, 3, 5, 0, 8), (8, 8, 8, 8, 16),
              (0, 3, 0, 5, 8), (0, 0, 0, 0, 0), (0, 16, 8, 8, 8),
              (7, 8, 10, 9, 16), (0, 64, 0, 0, 1), (1, 7, 8, 16, 32),
              (5, 10, 3, 9, 8), (16, 16, 16, 16, 16)]
    for base, outer, inner, counts, length in product(range(4), range(4), range(4), widths, range(13)):
        yield "N", data[:length], (base, outer, inner, *counts)


def scope_policy(length, args):
    """Independent abstract interpreter: absolute bit counts, no numeric decoder.

    The event stream is: a; enter outer; b; enter inner; c; exit inner;
    d; exit outer; e. Abort on the first shortage or disallowed transition.
    """
    base, outer, inner, a, b, c, d, e = args
    events = [a, (base, outer), b, (outer, inner), c, (inner, outer),
              d, (outer, base), e]
    position = 0
    for event in events:
        if isinstance(event, tuple):
            before, after = event
            if (before ^ after) & 2 and position % 8:
                return "U"
        else:
            position += event
            if position > 8 * length:
                return "E"
    return None


def compare(hammer, driver=None, work=WORK):
    """Compare this corpus against either the probe or a supplied library driver."""
    adapter = work / "c-adapter.so"
    # Reuse only the C reader/grammar adapter, not the superseded Rust probe or
    # its unrestricted expected outcomes. Internal C headers need POSIX types.
    run("gcc", "-shared", "-fPIC", "-std=c99", "-D_POSIX_C_SOURCE=200809L",
        "-Wall", "-Wextra", "-Werror", "-isystem", ROOT.parent / "src",
        PROBES / "input_order_c.c", hammer, f"-Wl,-rpath,{hammer.parent}", "-o", adapter)
    if driver is None:
        driver = work / "driver"
        run("rustc", "--edition", "2021", "--cfg", "restricted_order_driver", "-D", "warnings",
            PROBES / "restricted_order.rs", "-o", driver)
    library = C.CDLL(str(adapter))
    ptr, outptr = C.POINTER(C.c_uint8), C.POINTER(C.c_uint64)
    library.order_read.argtypes = [ptr, C.c_size_t, C.c_size_t, C.c_uint8, C.c_uint8,
                                  C.c_uint8, C.c_size_t, C.c_int, outptr]
    library.order_read.restype = None
    library.order_nested.argtypes = [ptr, C.c_size_t, C.c_uint8, C.c_uint8, C.c_uint8, ptr, outptr]
    library.order_nested.restype = None
    corpus = iter(cases())
    counts = {"fields_agree": 0, "scopes_agree": 0, "scope_rejections": 0, "rejected_c_successes": 0}
    while batch := list(islice(corpus, 4096)):
        requests = [f"{kind} {data.hex() or '-'} {' '.join(map(str, args))}" for kind, data, args in batch]
        actual = subprocess.check_output([driver], input="\n".join(requests) + "\n", text=True).splitlines()
        if len(actual) != len(batch):
            raise AssertionError("missing Rust results")
        for request, (kind, data, args), line in zip(requests, batch, actual):
            input_array = (C.c_uint8 * len(data)).from_buffer_copy(data)
            if kind == "R":
                byte, bit, flags, width = args
                high, low = (bit, 0) if flags & 2 else (0, bit)
                result = (C.c_uint64 * 5)()
                library.order_read(input_array, len(data), byte, high, low, flags, width, 0, result)
                expected = f"1 {result[1]} {result[2] + result[3]} {result[4]}" if result[0] else "E"
                counts["fields_agree"] += 1
            else:
                result = (C.c_uint64 * 7)()
                library.order_nested(input_array, len(data), *args[:3], (C.c_uint8 * 5)(*args[3:]), result)
                policy = scope_policy(len(data), args)
                if policy == "U":
                    expected = "U"
                    counts["scope_rejections"] += 1
                    counts["rejected_c_successes"] += bool(result[0])
                else:
                    if bool(result[0]) != (policy is None):
                        raise AssertionError(f"C acceptance disagrees with size model: {request}")
                    expected = " ".join(map(str, result)) if result[0] else "E"
                    counts["scopes_agree"] += 1
            if line != expected:
                raise AssertionError(f"{request}: Rust {line}; expected {expected}")
    print(f"Differential checks: {counts}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--aeneas-dir", type=Path, default=Path.home() / "source" / "aeneas")
    parser.add_argument("--hammer-lib", type=Path, help="optional local libhammer.so for differential tests")
    args = parser.parse_args()
    checkout = args.aeneas_dir.expanduser().resolve()
    for directory, revision in [(checkout, AENEAS_REV), (checkout / "charon", CHARON_REV)]:
        if output("git", "rev-parse", "HEAD", cwd=directory) != revision:
            parser.error(f"{directory}: expected {revision}")
    aeneas, charon = checkout / "bin" / "aeneas", checkout / "charon" / "bin" / "charon"
    if AENEAS_REV[:8] not in output(aeneas, "-version") or CHARON_REV not in output(charon, "version"):
        parser.error("rebuild the extraction binaries at the pinned revisions")
    WORK.mkdir(parents=True, exist_ok=True)
    run("rustfmt", "--edition", "2021", "--check", PROBES / "restricted_order.rs",
        PROBES / "restricted_order_tests.rs", PROBES / "restricted_order_driver.rs")
    run("rustc", "--edition", "2021", "-D", "warnings", "--test", PROBES / "restricted_order.rs", "-o", WORK / "native-tests")
    run(WORK / "native-tests")
    proof = PROBES / "restricted_order_proofs.lean"
    for stage in ["promoted", "optimized"]:
        dest = WORK / stage
        dest.mkdir(exist_ok=True)
        llbc = dest / "restricted_order.llbc"
        run(charon, "rustc", "--preset=aeneas", "--sysroot", "default", "--mir", stage,
            "--start-from", "restricted_order::nested", "--start-from", "restricted_order::escaped_span",
            "--start-from", "restricted_order::lookahead", "--dest-file", llbc,
            "--", "--crate-type", "lib", "--edition", "2021", "-D", "warnings", PROBES / "restricted_order.rs")
        run(aeneas, "-backend", "lean", "-namespace", "RestrictedOrder", "-dest", dest,
            "-abort-on-error", "-warnings-as-errors", "-no-progress-bar", llbc)
        generated = dest / "RestrictedOrder.lean"
        for path in [generated, proof]:
            if re.search(r"\b(?:sorry|admit)\b|^\s*(?:axiom|opaque)\s", path.read_text(), re.M):
                parser.error(f"unproved or opaque declaration in {path}")
        run("lake", "env", "lean", "-DwarningAsError=true", "-R", dest,
            "-o", dest / "RestrictedOrder.olean", generated, cwd=ROOT / "lean")
        env = os.environ.copy()
        env["LEAN_PATH"] = str(dest) + (os.pathsep + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
        command = ["lake", "env", "lean", "-DwarningAsError=true", str(proof)]
        print("+ " + " ".join(command), flush=True)
        result = subprocess.run(command, cwd=ROOT / "lean", env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        print(result.stdout, end="", flush=True)
        result.check_returncode()
        audits = re.findall(r"'RestrictedOrder\.Proofs\.([^']+)' depends on axioms: \[([^]]*)\]", result.stdout)
        if {name for name, _ in audits} != THEOREMS:
            parser.error("missing proof axiom audit")
        for name, axioms in audits:
            if set(filter(None, map(str.strip, axioms.split(",")))) - {"propext", "Classical.choice", "Quot.sound"}:
                parser.error(f"unexpected axioms in {name}: {axioms}")
    if args.hammer_lib:
        compare(args.hammer_lib.expanduser().resolve())
    else:
        print("C comparison skipped; pass --hammer-lib to enable it.")


if __name__ == "__main__":
    main()
