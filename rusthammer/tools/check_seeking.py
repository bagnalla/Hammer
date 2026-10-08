#!/usr/bin/env python3
"""Check the private seeking design against RustHammer, extraction, and optionally C."""

import argparse
import ctypes as c
import json
from pathlib import Path
import re
import subprocess

from verify import AENEAS_REV, CHARON_REV, ROOT, output, run


ENTRIES = {
    "probe": ("seek_position", "run"),
    "consumer": ("absolute", "relative", "end_relative", "packet", "spanned",
                 "repeated", "compared", "backend", "saved_position"),
    "function_item": ("saved_position_function_item",),
}


def logged(command, log, cwd=ROOT):
    with log.open("w") as handle:
        result = subprocess.run([str(arg) for arg in command], cwd=cwd,
                                stdout=handle, stderr=subprocess.STDOUT, text=True)
    if result.returncode:
        raise RuntimeError(f"exit {result.returncode}; see {log}\n{log.read_text()[-5000:]}")


def compare_c(work):
    src = ROOT.parent / "src"
    sources = [p for p in src.glob("*.c") if not p.name.startswith(("t_", "test_"))
               and p.name != "platform_bsdlike.c"]
    sources += list((src / "parsers").glob("*.c")) + list((src / "backends").glob("*.c"))
    library = work / "libhammer-reference.so"
    logged(["gcc", "-shared", "-fPIC", "-std=gnu99", "-O1", "-pthread",
            "-Werror=int-conversion", "-Werror=implicit-function-declaration", f"-I{src}",
            ROOT / "probes/seeking/reference.c", *sorted(sources), "-lm", "-o", library],
           work / "c-build.log")
    seek = c.CDLL(str(library)).seek_probe
    seek.argtypes = [c.c_uint, c.c_ssize_t, c.c_size_t, c.c_void_p, c.c_size_t,
                     c.POINTER(c.c_size_t), c.POINTER(c.c_size_t)]
    seek.restype = c.c_int
    width = 8 * c.sizeof(c.c_ssize_t)
    offsets = [-(1 << (width - 1)), *range(-80, 81), (1 << (width - 1)) - 1]
    agreements, eof_quirks = 0, 0
    first_quirk = None
    for size in range(9):
        data = c.create_string_buffer(bytes(size))
        for start in range(8 * size + 1):
            for origin in range(3):
                base = (0, start, 8 * size)[origin]
                for offset in offsets:
                    target = base + offset
                    position, length = c.c_size_t(), c.c_size_t()
                    success = seek(origin, offset, start, data, size, c.byref(position), c.byref(length))
                    expected = int(0 <= target <= 8 * size)
                    if success == expected and (not success or position.value == target):
                        agreements += 1
                    elif (start == 8 * size and 8 * size < target < 8 * size + 8
                          and success and position.value == target):
                        # h_seek_bits updates an equal byte index before checking bounds.
                        eof_quirks += 1
                        if first_quirk is None:
                            first_quirk = dict(size=size, start=start, origin=origin, offset=offset,
                                              returned_position=position.value)
                    else:
                        raise RuntimeError(f"unexpected C result: {size=}, {start=}, {origin=}, "
                                           f"{offset=}, {success=}, position={position.value}")
    # The adapter records the seek child's unsigned bit_length before its parent
    # can replace it with the net length of the enclosing parse.
    position, length = c.c_size_t(), c.c_size_t()
    success = seek(0, 0, 8, c.create_string_buffer(b"a"), 1, c.byref(position), c.byref(length))
    wrapped = (1 << (8 * c.sizeof(c.c_size_t))) - 8
    if (success, position.value, length.value) != (1, 0, wrapped):
        raise RuntimeError(f"C backward-length behavior changed: {success}, {position.value}, {length.value}")
    if not eof_quirks:
        raise RuntimeError("C EOF behavior changed; update the investigation and expected results")
    record = {"agreements": agreements, "eof_quirks": eof_quirks, "first_quirk": first_quirk,
              "backward_bit_length": length.value}
    (work / "c-results.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"C: {agreements} mathematical-contract agreements, {eof_quirks} known EOF differences; "
          f"backward child bit_length={length.value}.", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--aeneas-dir", type=Path, default=ROOT / "target/extraction-tools/aeneas")
    parser.add_argument("--native-only", action="store_true")
    parser.add_argument("--c", action="store_true", help="also characterize the current C implementation")
    args = parser.parse_args()
    work = ROOT / "target/seeking"
    work.mkdir(parents=True, exist_ok=True)
    (work / "results.json").unlink(missing_ok=True)
    if args.c:
        (work / "c-results.json").unlink(missing_ok=True)
    manifests = {
        "probe": ROOT / "probes/seeking/Cargo.toml",
        "consumer": ROOT / "probes/seeking/consumer/Cargo.toml",
    }
    for manifest in manifests.values():
        run("cargo", "fmt", "--manifest-path", manifest, "--check")
        run("cargo", "test", "--manifest-path", manifest, "--target-dir", work / "cargo", "--locked")
    if args.c:
        compare_c(work)
    if args.native_only:
        print("Native seeking checks passed; extraction was not requested.")
        return
    checkout = args.aeneas_dir.expanduser().resolve()
    charon, aeneas = checkout / "charon/bin/charon", checkout / "bin/aeneas"
    for directory, revision in ((checkout, AENEAS_REV), (checkout / "charon", CHARON_REV)):
        if output("git", "rev-parse", "HEAD", cwd=directory) != revision:
            parser.error(f"{directory}: expected {revision}")
    if CHARON_REV not in output(charon, "version") or AENEAS_REV[:8] not in output(aeneas, "-version"):
        parser.error("rebuild the extraction binaries at the pinned revisions")

    results = []
    for case, entries in ENTRIES.items():
        crate = "rusthammer_seek_probe" if case == "probe" else "rusthammer_seek_consumer"
        manifest = manifests["probe" if case == "probe" else "consumer"]
        for mir in ("promoted", "optimized"):
            destination = work / case / mir
            destination.mkdir(parents=True, exist_ok=True)
            llbc = destination / "seek_probe.llbc"
            lean = destination / "lean"
            llbc.unlink(missing_ok=True)
            for previous in lean.glob("*.lean"):
                previous.unlink()
            logged([
                charon, "cargo", "--preset=aeneas", "--sysroot", "default", "--mir", mir,
                *(arg for name in entries for arg in ("--start-from-if-exists", f"{crate}::{name}")),
                "--include", "rusthammer::_", "--include", "rusthammer_seek_probe::_",
                "--dest-file", llbc, "--", "--lib", "--manifest-path", manifest,
                "--target-dir", work / "cargo", "--locked",
            ], destination / "charon.log")
            try:
                logged([
                    aeneas, "-backend", "lean", "-namespace", "SeekProbe",
                    "-dest", lean, "-abort-on-error", "-warnings-as-errors", "-no-progress-bar", llbc,
                ], destination / "aeneas.log")
            except RuntimeError:
                if case != "function_item" or "Arrow types are not supported yet" not in (destination / "aeneas.log").read_text():
                    raise
                results.append({"case": case, "mir": mir, "roots": list(entries),
                                "passed": False, "expected_failure": "Aeneas: Arrow types are not supported yet"})
                (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")
                print(f"EXPECTED UNSUPPORTED {case}/{mir}: function-item callback", flush=True)
                continue
            if case == "function_item":
                raise RuntimeError("function-item extraction behavior changed; update the investigation")
            generated = list(lean.glob("*.lean"))
            if len(generated) != 1:
                raise RuntimeError(f"expected one generated module in {lean}")
            code = generated[0].read_text()
            if re.search(r"\b(?:sorry|admit)\b|^\s*(?:axiom|opaque)\s", code, re.M):
                raise RuntimeError(f"unproved or opaque declaration in {generated[0]}")
            for root in entries:
                if not re.search(rf"^def {re.escape(root)}\s", code, re.M):
                    raise RuntimeError(f"missing root {root} in {generated[0]}")
            logged(["lake", "env", "lean", "-DwarningAsError=true", "-DautoImplicit=false", generated[0]],
                   destination / "lean.log", cwd=ROOT / "lean")
            results.append({"case": case, "mir": mir, "roots": list(entries), "passed": True})
            (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")
            print(f"PASS {case}/{mir}: {len(entries)} roots, strict Lean checking", flush=True)
    print("Seeking translations passed; function-item limitation reproduced at both MIR stages. "
          "This checks translation, not semantic correctness proofs.")


if __name__ == "__main__":
    main()
