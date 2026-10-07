#!/usr/bin/env python3
"""Check experimental constructors and opaque returns with the pinned tools."""

import argparse
import json
from pathlib import Path
import re
import subprocess

from verify import AENEAS_REV, CHARON_REV, ROOT, output, run


CASES = {
    "baseline": ("baseline",),
    "constructors": (
        "seq", "map", "try_map", "verify", "choice", "bind", "optional",
        "concrete_header", "checked_choice", "dependent_payload",
    ),
    "borrowed_sources": ("borrowed_sources",),
    "borrowed_callback": ("borrowed_callback",),
    "direct_borrowed_callback": ("direct_borrowed_callback",),
    "named_borrowed_callback": ("named_borrowed_callback",),
    "backend": ("backend_only",),
    "opaque_output": ("opaque_header", "run_opaque_header"),
    "opaque_borrow": ("opaque_payload", "run_opaque_payload"),
    "opaque_callback": ("mapped_header", "callback_backend"),
    "consumer": ("header", "borrows", "backend", "generic_backend", "owned"),
    "consumer_callback": ("callback",),
    "consumer_named_callback": ("named_callback",),
}


def logged(args, log, cwd=ROOT):
    with log.open("w") as handle:
        result = subprocess.run([str(arg) for arg in args], cwd=cwd, stdout=handle,
                                stderr=subprocess.STDOUT, text=True)
    if result.returncode:
        lines = log.read_text().splitlines()
        excerpt = lines if len(lines) <= 24 else lines[:16] + ["..."] + lines[-7:]
        print("\n".join(excerpt), flush=True)
        raise RuntimeError(f"exit {result.returncode}; see {log}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--aeneas-dir", type=Path, default=Path.home() / "source" / "aeneas")
    parser.add_argument("--native-only", action="store_true")
    parser.add_argument("--case", choices=CASES, action="append", help="default: all cases")
    args = parser.parse_args()
    work = ROOT / "target/constructor-api"
    work.mkdir(parents=True, exist_ok=True)
    manifests = {
        "probe": ROOT / "probes/constructors/Cargo.toml",
        "consumer": ROOT / "probes/constructors/consumer/Cargo.toml",
    }
    for manifest in manifests.values():
        run("cargo", "fmt", "--manifest-path", manifest, "--check")
        run("cargo", "test", "--manifest-path", manifest, "--target-dir", work / "cargo", "--locked")
    if args.native_only:
        print("Native constructor probes passed; extraction was not requested.")
        return

    checkout = args.aeneas_dir.expanduser().resolve()
    charon = checkout / "charon/bin/charon"
    aeneas = checkout / "bin/aeneas"
    for directory, revision in [(checkout, AENEAS_REV), (checkout / "charon", CHARON_REV)]:
        if output("git", "rev-parse", "HEAD", cwd=directory) != revision:
            parser.error(f"{directory}: expected {revision}")
    if CHARON_REV not in output(charon, "version") or AENEAS_REV[:8] not in output(aeneas, "-version"):
        parser.error("rebuild the extraction binaries at the pinned revisions")

    results = []
    for case in args.case or CASES:
        entries = CASES[case]
        consumer = case.startswith("consumer")
        crate = "rusthammer_constructor_consumer" if consumer else "rusthammer_constructor_probe"
        manifest = manifests["consumer" if consumer else "probe"]
        for mode in ("promoted", "optimized"):
            destination = work / case / mode
            destination.mkdir(parents=True, exist_ok=True)
            llbc = destination / f"{crate}.llbc"
            lean = destination / "lean"
            print(f"Checking {case}, {mode} MIR", flush=True)
            phase = "Charon"
            try:
                llbc.unlink(missing_ok=True)
                # Dependencies receive the same flags but lack the consumer roots.
                # The final compiler invocation must extract the requested crate.
                logged([
                    charon, "cargo", "--preset=aeneas", "--sysroot", "default", "--mir", mode,
                    *(arg for name in entries for arg in ("--start-from-if-exists", f"{crate}::{name}")),
                    "--include", "rusthammer::_",
                    *(["--include", "rusthammer_constructor_probe::_"] if consumer else []),
                    "--dest-file", llbc,
                    "--", "--lib", "--manifest-path", manifest,
                    "--target-dir", work / "cargo", "--locked",
                ], destination / "charon.log")
                phase = "Aeneas"
                for previous in lean.glob("*.lean"):
                    previous.unlink()
                logged([
                    aeneas, "-backend", "lean", "-namespace", f"ConstructorProbe.{case}.{mode}",
                    "-dest", lean, "-abort-on-error", "-warnings-as-errors", "-no-progress-bar", llbc,
                ], destination / "aeneas.log")
                phase = "declaration audit"
                generated = list(lean.glob("*.lean"))
                if len(generated) != 1:
                    raise RuntimeError(f"expected one generated Lean module in {lean}")
                code = generated[0].read_text()
                if re.search(r"\b(?:sorry|admit)\b|^\s*(?:axiom|opaque)\s", code, re.M):
                    raise RuntimeError(f"unproved or opaque declaration in {generated[0]}")
                for name in entries:
                    if not re.search(rf"^def {re.escape(name)}\s", code, re.M):
                        raise RuntimeError(f"missing extracted entry point {name}")
                phase = "Lean"
                logged(["lake", "env", "lean", "-DwarningAsError=true", generated[0]],
                       destination / "lean.log", cwd=ROOT / "lean")
            except RuntimeError as error:
                print(f"FAIL {case}/{mode}: {phase}: {error}", flush=True)
                results.append({"case": case, "mir": mode, "passed": False,
                                "phase": phase, "error": str(error)})
            else:
                print(f"PASS {case}/{mode}", flush=True)
                results.append({"case": case, "mir": mode, "passed": True})

    (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"{sum(result['passed'] for result in results)}/{len(results)} extraction checks passed.")
    if not all(result["passed"] for result in results):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
