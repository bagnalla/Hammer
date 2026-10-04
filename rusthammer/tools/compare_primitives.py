#!/usr/bin/env python3
"""Compare byte, signed-field, and fixed-width primitives with C Hammer on complete input.

Requires GCC, rustc, and an already built C Hammer shared library. The ordinary
Rust/Lean verification command does not require a C build or this optional tool.
"""

import argparse
import ctypes as c
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]


def byte_cases():
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


def signed_cases():
    for width in range(65):
        mask = (1 << width) - 1
        sign = (1 << (width - 1)) if width else 0
        values = {value & mask for value in (
            0, 1, sign - 1, sign, sign + 1, mask - 1, mask,
            0xAAAAAAAAAAAAAAAA, 0x5555555555555555,
        )}
        for value in sorted(values):
            for offset in range(8):
                bits = "1010101"[:offset]
                if width:
                    bits += f"{value:0{width}b}"
                bits += "01100101"
                bits += "0" * (-len(bits) % 8)
                data = bytes(int(bits[i:i + 8], 2) for i in range(0, len(bits), 8))
                for length in range(int(offset != 0), len(data) + 1):
                    yield "signed", offset, width, data[:length]


def integer_cases():
    # Reuse the boundary/truncation corpus, now invoking the named C primitives
    # and the corresponding native-output Rust readers on both signednesses.
    for _, offset, width, data in signed_cases():
        if width in (8, 16, 32, 64):
            yield "uint", offset, width, data
            yield "int", offset, width, data
    # Exhaust all aligned 8- and 16-bit patterns as well as their signed values.
    for width in (8, 16):
        for value in range(1 << width):
            data = value.to_bytes(width // 8, "big")
            yield "uint", 0, width, data
            yield "int", 0, width, data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hammer-library", type=Path, required=True)
    args = parser.parse_args()
    library = args.hammer_library.resolve(strict=True)
    target = ROOT / "target" / "primitive-comparison"
    target.mkdir(parents=True, exist_ok=True)
    adapter = target / "adapter.so"
    driver = target / "rust-primitives"
    subprocess.run([
        "gcc", "-shared", "-fPIC", "-std=c99", "-Wall", "-Wextra", "-Werror",
        "-I", str(ROOT.parent / "src"), str(ROOT / "tests/compat/primitives.c"),
        str(library), f"-Wl,-rpath,{library.parent}", "-o", str(adapter),
    ], check=True)
    subprocess.run([
        "rustc", "--edition=2021", "-A", "unused_attributes",
        str(ROOT / "tests/compat/primitives.rs"), "-o", str(driver),
    ], check=True, cwd=ROOT)
    hammer = c.CDLL(str(adapter))
    parse = hammer.compare_bytes
    parse.argtypes = [c.c_uint, c.c_char_p, c.c_size_t, c.c_char_p, c.c_size_t,
                      c.c_uint, c.POINTER(c.c_size_t), c.POINTER(c.c_uint)]
    parse.restype = c.c_int
    parse_signed = hammer.compare_signed
    parse_signed.argtypes = [c.c_uint, c.c_char_p, c.c_size_t, c.c_uint,
                            c.POINTER(c.c_size_t), c.POINTER(c.c_int64)]
    parse_signed.restype = c.c_int
    parse_integer = hammer.compare_integer
    parse_integer.argtypes = [c.c_uint, c.c_uint, c.c_char_p, c.c_size_t, c.c_uint,
                             c.POINTER(c.c_size_t), c.POINTER(c.c_uint64), c.POINTER(c.c_int64)]
    parse_integer.restype = c.c_int
    byte_corpus = list(byte_cases())
    signed_corpus = list(signed_cases())
    integer_corpus = list(integer_cases())
    corpus = byte_corpus + signed_corpus + integer_corpus
    lines = []
    for kind, offset, config, data in corpus:
        setting = (config.hex() or "-") if kind in ("byte", "pattern") else str(config)
        lines.append(f"{kind} {offset} {setting} {data.hex() or '-'}\n")
    wire = "".join(lines)
    rust = subprocess.run([str(driver)], input=wire, text=True, capture_output=True, check=True)
    results = rust.stdout.splitlines()
    assert len(results) == len(corpus)
    for case, actual in zip(corpus, results):
        kind, offset, config, data = case
        position = c.c_size_t()
        if kind == "signed":
            value = c.c_int64()
            accepted = parse_signed(config, data, len(data), offset, c.byref(position), c.byref(value))
        elif kind in ("uint", "int"):
            unsigned_value, signed_value = c.c_uint64(), c.c_int64()
            accepted = parse_integer(config, kind == "int", data, len(data), offset,
                                     c.byref(position), c.byref(unsigned_value), c.byref(signed_value))
            value = signed_value if kind == "int" else unsigned_value
        else:
            value = c.c_uint()
            accepted = parse(kind == "byte", config, len(config), data, len(data), offset,
                             c.byref(position), c.byref(value))
        expected = f"{position.value} {value.value}" if accepted else "error"
        assert actual == expected, (case, actual, expected)
    print(f"C/Rust primitive comparison passed: {len(corpus)} cases "
          f"({len(byte_corpus)} byte/pattern, {len(signed_corpus)} signed, "
          f"{len(integer_corpus)} fixed-width).")
    print("Acceptance, consumption, and decoded outputs agree.")


if __name__ == "__main__":
    main()
