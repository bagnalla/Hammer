#!/usr/bin/env python3
"""Compare ButNot, Difference, and Xor with C Hammer's direct backend.

Requires GCC, rustc, and an already built C Hammer shared library. Checks complete
inputs; Rust's distinct errors and NeedMore are covered by native tests/proofs.
"""

import argparse
import ctypes as c
from itertools import islice, product
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]


def cases():
    # Literal, skip, lookahead, discarded prefix/suffix, empty, and rejecting
    # children. Matching is measured in consumed bits, not output size.
    atoms = [(0, width, value) for width, value in (
        (0, 0), (1, 0), (1, 1), (3, 0), (3, 5), (7, 0), (8, 0), (8, 0x61),
        (8, 0xff), (9, 0), (16, 0), (16, 0x6162), (64, 0), (64, (1 << 64) - 1),
    )]
    atoms += [(1, width, 0) for width in (0, 1, 7, 8, 9, 16, 65)]
    atoms += [(2, 8, 0), (2, 8, 0x61), (3, 3, 0), (3, 8, 0x61),
              (4, 3, 0), (4, 8, 0x61), (5, 0, 0), (6, 0, 0)]
    samples = [bytes(10), b'\xff' * 10, b'\xaa' * 10, b'\x55' * 10,
               b'abcdefghij', bytes.fromhex('0c2c4000000000000000')]
    inputs = sorted({sample[:length] for sample in samples for length in range(11)})
    for data in inputs:
        for offset in (*range(8), 8, 15, 16, 17, 63, 64, 65):
            if offset > len(data) * 8:
                continue  # C reaches the same valid cursor with a leading skip.
            for operation, first, second in product(range(3), atoms, atoms):
                yield operation, offset, first, second, data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--hammer-library', type=Path, required=True)
    args = parser.parse_args()
    library = args.hammer_library.resolve(strict=True)
    target = ROOT / 'target' / 'match-comparison'
    target.mkdir(parents=True, exist_ok=True)
    adapter, driver = target / 'adapter.so', target / 'rust-matches'
    subprocess.run([
        'gcc', '-shared', '-fPIC', '-std=c99', '-Wall', '-Wextra', '-Werror',
        '-I', str(ROOT.parent / 'src'), str(ROOT / 'tests/compat/matches.c'),
        str(library), f'-Wl,-rpath,{library.parent}', '-o', str(adapter),
    ], check=True)
    subprocess.run([
        'rustc', '--edition=2021', '-A', 'unused_attributes',
        str(ROOT / 'tests/compat/matches.rs'), '-o', str(driver),
    ], check=True, cwd=ROOT)
    hammer = c.CDLL(str(adapter))
    parse = hammer.compare_matches
    parse.argtypes = [c.c_uint, c.c_uint, c.c_uint, c.c_uint64,
                      c.c_uint, c.c_uint, c.c_uint64, c.c_char_p, c.c_size_t,
                      c.c_uint, c.POINTER(c.c_size_t), c.POINTER(c.c_uint64)]
    parse.restype = c.c_int
    corpus, total = iter(cases()), 0
    while batch := list(islice(corpus, 5000)):
        wire = ''.join(f"{op} {offset} {':'.join(map(str, first))} "
                       f"{':'.join(map(str, second))} {data.hex() or '-'}\n"
                       for op, offset, first, second, data in batch)
        rust = subprocess.run([str(driver)], input=wire, text=True, capture_output=True, check=True)
        results = rust.stdout.splitlines()
        assert len(results) == len(batch)
        for case, actual in zip(batch, results):
            op, offset, first, second, data = case
            position, value = c.c_size_t(), c.c_uint64()
            accepted = parse(op, *first, *second, data, len(data), offset,
                             c.byref(position), c.byref(value))
            expected = f'{position.value} {value.value}' if accepted else 'error'
            assert actual == expected, (case, actual, expected)
        total += len(batch)
    print(f'C/Rust match comparison passed: {total} cases.')
    print('Acceptance, consumption, and selected outputs agree on complete input.')


if __name__ == '__main__':
    main()
