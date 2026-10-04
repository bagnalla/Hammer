#!/usr/bin/env python3
"""Compare Byte/BytePattern with C Hammer's direct backend on complete input.

Requires GCC, rustc, and an already built C Hammer shared library. The ordinary
Rust/Lean verification command does not require a C build or this optional tool.
"""

import argparse
import ctypes as c
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]


def cases():
    for first in range(256):
        for second in (0, 0x55, 0xFF):
            for offset in range(8):
                yield "byte", offset, b"", bytes((first, second))
        for offset in range(8):
            yield "byte", offset, b"", bytes((first,))
    yield "byte", 0, b"", b""
    for pattern in (b"", b"\0", b"\xff", b"ab", b"foobar", b"\xab\0\xcd", bytes(range(256))):
        for offset in range(8):
            bits = "1010101"[:offset] + "".join(f"{byte:08b}" for byte in pattern) + "01100101"
            bits += "0" * (-len(bits) % 8)
            input_bytes = bytes(int(bits[i:i + 8], 2) for i in range(0, len(bits), 8))
            # A C skip parser cannot reach a nonzero offset in an empty buffer.
            # Rust empty patterns deliberately accept even raw invalid cursors;
            # comparisons here start only at valid cursors in both implementations.
            for length in range(int(offset != 0), len(input_bytes) + 1):
                yield "pattern", offset, pattern, input_bytes[:length]
            for index in set((0, len(pattern) // 2, len(pattern) - 1)):
                if pattern:
                    different = bytearray(pattern)
                    different[index] ^= 0x80
                    yield "pattern", offset, bytes(different), input_bytes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hammer-library", type=Path, required=True)
    args = parser.parse_args()
    library = args.hammer_library.resolve(strict=True)
    target = ROOT / "target" / "byte-comparison"
    target.mkdir(parents=True, exist_ok=True)
    adapter = target / "adapter.so"
    driver = target / "rust-bytes"
    subprocess.run([
        "gcc", "-shared", "-fPIC", "-std=c99", "-Wall", "-Wextra", "-Werror",
        "-I", str(ROOT.parent / "src"), str(ROOT / "tests/compat/bytes.c"),
        str(library), f"-Wl,-rpath,{library.parent}", "-o", str(adapter),
    ], check=True)
    subprocess.run([
        "rustc", "--edition=2021", "-A", "unused_attributes",
        str(ROOT / "tests/compat/bytes.rs"), "-o", str(driver),
    ], check=True, cwd=ROOT)
    hammer = c.CDLL(str(adapter))
    parse = hammer.compare_bytes
    parse.argtypes = [c.c_uint, c.c_char_p, c.c_size_t, c.c_char_p, c.c_size_t,
                      c.c_uint, c.POINTER(c.c_size_t), c.POINTER(c.c_uint)]
    parse.restype = c.c_int
    corpus = list(cases())
    wire = "".join(f"{kind} {offset} {pattern.hex() or '-'} {data.hex() or '-'}\n"
                   for kind, offset, pattern, data in corpus)
    rust = subprocess.run([str(driver)], input=wire, text=True, capture_output=True, check=True)
    results = rust.stdout.splitlines()
    assert len(results) == len(corpus)
    for case, actual in zip(corpus, results):
        kind, offset, pattern, data = case
        position, value = c.c_size_t(), c.c_uint()
        accepted = parse(kind == "byte", pattern, len(pattern), data, len(data), offset,
                         c.byref(position), c.byref(value))
        expected = f"{position.value} {value.value}" if accepted else "error"
        assert actual == expected, (case, actual, expected)
    print(f"C/Rust byte comparison passed: {len(corpus)} cases (acceptance, consumption, output).")


if __name__ == "__main__":
    main()
