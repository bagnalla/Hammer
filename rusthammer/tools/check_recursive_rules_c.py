#!/usr/bin/env python3
"""Compare the private recursion fixtures with the repository's C packrat engine."""
import ctypes
import json
from verify import ROOT, output, run


def main():
    work = ROOT / "target/recursive-rules"
    work.mkdir(parents=True, exist_ok=True)
    src = ROOT.parent / "src"
    # The core has no GLib dependency. Do not accidentally compile legacy tests
    # in src/, or the obsolete alternative platform implementation.
    sources = [p for p in src.glob("*.c") if not p.name.startswith(("t_", "test_"))
               and p.name != "platform_bsdlike.c"]
    sources += list((src / "parsers").glob("*.c")) + list((src / "backends").glob("*.c"))
    library = work / "libhammer-reference.so"
    run("gcc", "-shared", "-fPIC", "-std=gnu99", "-O1", "-pthread",
        "-Werror=int-conversion", "-Werror=implicit-function-declaration", f"-I{src}",
        ROOT / "probes/recursive_rules/reference.c", *sorted(sources), "-lm", "-o", library)
    run("cargo", "build", "--manifest-path", ROOT / "probes/recursive_rules/Cargo.toml",
        "--target-dir", work / "cargo", "--locked", "--bin", "recursive-rule-cases")
    oracle = ctypes.CDLL(str(library)).recursive_probe
    oracle.argtypes = [ctypes.c_uint, ctypes.c_void_p, ctypes.c_size_t, ctypes.POINTER(ctypes.c_size_t)]
    oracle.restype = ctypes.c_int
    corpus = output(work / "cargo/debug/recursive-rule-cases")
    count = 0
    differences = []
    for line in corpus.splitlines():
        mode, length, mask, success, consumed, value = map(int, line.split())
        data = bytes(ord('x') if mask & (1 << bit) else ord('a') for bit in range(length))
        storage = ctypes.create_string_buffer(data)
        bits = ctypes.c_size_t()
        result = oracle(mode, storage, length, ctypes.byref(bits))
        if (result, bits.value) != (success, consumed):
            # The context-changing mutual cycle is a recorded semantic gap, not
            # normalized into agreement. These byte literals are order-insensitive.
            if mode != 7 or not data.startswith(b"aa") or (result, bits.value) != (1, 8) or success != 1 or consumed <= 8:
                raise RuntimeError(f"mode={mode}, input={data!r}: Rust={(success, consumed)}, C={(result, bits.value)}")
            differences.append({"mode": mode, "input": data.decode(), "rust_bits": consumed, "c_bits": bits.value})
        if success and value * 8 != consumed:
            raise RuntimeError(f"unexpected Rust decoded count: {line}")
        count += 1
    if count != 1016:
        raise RuntimeError(f"recursive corpus changed: expected 1016 cases, found {count}")
    if len(differences) != 31:
        raise RuntimeError(f"context-cycle baseline changed: {len(differences)} differences; investigate it")
    # Check actual end-of-input behavior as well as reported bit_length on the
    # minimal discrepancy: the scoped grammar fails complete parsing, whereas
    # the equivalent unscoped mutual recursion succeeds.
    minimal = ctypes.create_string_buffer(b"aa")
    bits = ctypes.c_size_t()
    if oracle(16 + 7, minimal, 2, ctypes.byref(bits)) != 0 or oracle(16 + 1, minimal, 2, ctypes.byref(bits)) != 1:
        raise RuntimeError("the complete-parse context-cycle reproducer changed")
    (work / "c-differences.json").write_text(json.dumps(differences, indent=2) + "\n")
    print(f"C packrat comparison: {count - len(differences)} acceptance/consumption agreements; "
          f"{len(differences)} documented context-cycle differences. Rust fixture counts also checked.")


if __name__ == '__main__':
    main()
