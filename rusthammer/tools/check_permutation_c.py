#!/usr/bin/env python3
"""Compare typed permutations with C Hammer on ambiguous and nullable entries."""
import ctypes
from verify import ROOT, output, run


def main():
    work = ROOT / "target/permutation-c"
    work.mkdir(parents=True, exist_ok=True)
    src = ROOT.parent / "src"
    sources = [p for p in src.glob("*.c") if not p.name.startswith(("t_", "test_"))
               and p.name != "platform_bsdlike.c"]
    sources += list((src / "parsers").glob("*.c")) + list((src / "backends").glob("*.c"))
    library = work / "libhammer-reference.so"
    run("gcc", "-shared", "-fPIC", "-std=gnu99", "-O1", "-pthread",
        "-Werror=int-conversion", "-Werror=implicit-function-declaration", f"-I{src}",
        ROOT / "probes/permutation/reference.c", *sorted(sources), "-lm", "-o", library)
    run("cargo", "build", "--manifest-path", ROOT / "probes/permutation/Cargo.toml",
        "--target-dir", work / "cargo", "--locked", "--bin", "permutation-cases")
    oracle = ctypes.CDLL(str(library)).permutation_probe
    oracle.argtypes = [ctypes.c_uint] * 5 + [ctypes.c_void_p, ctypes.c_size_t,
                      ctypes.POINTER(ctypes.c_size_t), ctypes.POINTER(ctypes.c_uint)]
    oracle.restype = ctypes.c_int
    corpus = output(work / "cargo/debug/permutation-cases")
    count = 0
    for line in corpus.splitlines():
        a, b, c, optional, length, mask, offset, success, consumed, present = map(int, line.split())
        data = bytearray((offset + length * 8 + 7) // 8)
        for i in range(length):
            byte = ord('b') if mask & (1 << i) else ord('a')
            for bit in range(8):
                position = offset + i * 8 + bit
                data[position // 8] |= ((byte >> (7 - bit)) & 1) << (7 - position % 8)
        storage = ctypes.create_string_buffer(bytes(data))
        bits, values = ctypes.c_size_t(), ctypes.c_uint()
        result = oracle(a, b, c, optional, offset, storage, len(data), ctypes.byref(bits), ctypes.byref(values))
        if (result, bits.value, values.value) != (success, consumed, present):
            raise RuntimeError(f"case {line}: C={(result, bits.value, values.value)}")
        count += 1
    if count != 217728:
        raise RuntimeError(f"permutation corpus changed: expected 217728 cases, found {count}")
    print(f"C permutation comparison: {count} acceptance/consumption/optional-presence agreements; "
          "both adapters also checked every value in declaration order.")


if __name__ == '__main__':
    main()
