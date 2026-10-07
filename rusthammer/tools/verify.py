#!/usr/bin/env python3
"""Test Rust, check Lean proofs, and guard dependency extraction compatibility."""

import argparse
from pathlib import Path
import re
import subprocess


AENEAS_REV = "557eff83ecef5083b98a52a94ca7fae63d6c1dab"
CHARON_REV = "c8f15d7d658c86a95658f71ad99cddd4be002e04"
ROOT = Path(__file__).resolve().parents[1]

ORDER_THEOREMS = (
    "RustHammer.Ordering.unsigned_default",
    "RustHammer.Proofs.read_ordered_bits_spec",
    "RustHammer.Proofs.read_bit_ordered_spec",
    *(f"RustHammer.Ordering.{name}" for name in (
        "with_order_spec", "with_order_blocked", "scope_success_aligned",
        "bits_with_spec", "bit_with_spec", "literal_with_spec", "signed_bits_with_spec",
        "byte_with_spec", "i8_with_spec", "be_u16_with_spec", "be_u32_with_spec",
        "be_u64_with_spec", "be_i16_with_spec", "be_i32_with_spec", "be_i64_with_spec",
        "byte_pattern_with_spec", "byte_in_with_spec", "byte_not_in_with_spec",
        "take_aligned_with_spec", "skip_bits_with_spec", "tell_with_spec", "end_with_spec",
    )),
)

BACKEND_THEOREMS = (
    "RustHammer.Code.eval_direct",
    "RustHammer.Code.direct_entry_with",
    "RustHammer.Code.direct_entry",
    "RustHammer.Code.direct_projection_spec",
    "RustHammer.Backend.seq_eval_spec",
    "RustHammer.Backend.choice_eval_spec",
)

SPAN_THEOREMS = tuple(f"RustHammer.Span.{name}" for name in (
    "cursor_valid_spec", "new_spec", "checked_success", "input_spec", "start_spec",
    "end_spec", "bit_order_spec", "clone_spec", "is_empty_spec", "as_bytes_spec",
    "with_span_eval_spec", "recognize_eval_spec", "with_span_with_spec", "recognize_with_spec",
    "capture_need_more", "recognize_need_more", "with_span_complete_spec", "recognize_complete_spec",
    "with_span_clone_spec", "recognize_clone_spec", "capture_success",
    "offset_physical", "physical_offset", "physical_injective", "consumed_length",
    "bits_distinct", "mem_bits", "selected_in_input", "high_same_byte", "low_same_byte",
    "interior_byte", "crossing_start", "crossing_end", "aligned_region",
))

CONSTRUCTOR_THEOREMS = tuple(f"RustHammer.Constructors.{name}" for name in (
    "seq_eq", "choice_eq", "optional_eq", "map_eq", "try_map_eq", "verify_eq", "bind_eq",
    "reuse_spec", "seq_eval_spec",
))

PERMUTATION_THEOREMS = tuple(f"RustHammer.Permutation.{name}" for name in (
    "search_spec", "eval_spec", "required_eq", "permutation_eq", "required_eval_spec",
    "required_slot_spec", "optional_slot_spec", "required_entry_spec", "optional_entry_spec",
    "empty_eval_spec",
    *(f"tuple{arity}_{operation}" for arity in range(1, 13)
      for operation in ("initial", "matched", "clear", "finish", "output_order", "dispatch")),
))


def output(*args, cwd=None):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def run(*args, cwd=ROOT):
    print("+ " + " ".join(str(arg) for arg in args), flush=True)
    subprocess.run(args, cwd=cwd, check=True)


def translate(aeneas, llbc, destination, namespace):
    run(
        str(aeneas), "-backend", "lean", "-dest", destination,
        "-namespace", namespace, "-abort-on-error", "-warnings-as-errors",
        "-no-progress-bar", llbc,
    )


def audit_proofs():
    theorems = (ORDER_THEOREMS + BACKEND_THEOREMS + SPAN_THEOREMS
                + CONSTRUCTOR_THEOREMS + PERMUTATION_THEOREMS)
    audit = ROOT / "target" / "proof-axioms.lean"
    audit.write_text("import RustHammer\n" + "".join(
        f"#print axioms {name}\n" for name in theorems
    ))
    result = output("lake", "env", "lean", "-DwarningAsError=true", audit, cwd=ROOT / "lean")
    audits = re.findall(
        r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result,
    )
    if {name for name, _ in audits} != set(theorems):
        raise RuntimeError(f"missing proof axiom audit:\n{result}")
    for name, axioms in audits:
        if set(filter(None, map(str.strip, axioms.split(",")))) - {"propext", "Classical.choice", "Quot.sound"}:
            raise RuntimeError(f"unexpected axioms in {name}: {axioms}")
    print(f"Proof axiom audit: {len(audits)} theorems use only standard Lean axioms.", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--aeneas-dir",
        type=Path,
        default=Path.home() / "source" / "aeneas",
        help="local Aeneas checkout containing bin/aeneas and charon/bin/charon",
    )
    args = parser.parse_args()
    checkout = args.aeneas_dir.expanduser().resolve()
    aeneas = checkout / "bin" / "aeneas"
    charon = checkout / "charon" / "bin" / "charon"

    for directory, expected in [(checkout, AENEAS_REV), (checkout / "charon", CHARON_REV)]:
        actual = output("git", "rev-parse", "HEAD", cwd=directory)
        if actual != expected:
            parser.error(f"{directory}: expected revision {expected}, found {actual}")
    if AENEAS_REV[:8] not in output(str(aeneas), "-version"):
        parser.error("the Aeneas binary does not match the pinned revision; rebuild it")
    if CHARON_REV not in output(str(charon), "version"):
        parser.error("the Charon binary does not match the pinned revision; rebuild it")

    run("cargo", "fmt", "--check")
    run("cargo", "test", "--locked", "--no-default-features")
    run("cargo", "test", "--locked", "--features", "alloc")
    # Reuse the exact same roots at both MIR stages. Dependencies expose the
    # later stage, which can contain cleanup code absent from promoted MIR.
    library_extraction = (
        str(charon), "cargo", "--preset=aeneas", "--sysroot", "default",
        # Private fixture modules share source with the runnable examples; they
        # are excluded from ordinary library builds and do not expand the API.
        "--rustc-arg=--cfg=rusthammer_verify",
        "--start-from", "rusthammer::dependent_examples::payload",
        "--start-from", "rusthammer::dependent_examples::fields",
        "--start-from", "rusthammer::flags_example::parse_flags",
        "--start-from", "rusthammer::grammar::bytes::take_aligned",
        "--start-from", "rusthammer::grammar::numeric::read_bits",
        "--start-from", "rusthammer::input_types::ParseContext::PARTIAL",
        "--start-from", "rusthammer::grammar::sequence::seq",
        "--start-from", "rusthammer::grammar::control::choice",
        "--start-from", "rusthammer::grammar::control::optional",
        "--start-from", "rusthammer::grammar::transform::map",
        "--start-from", "rusthammer::grammar::transform::try_map",
        "--start-from", "rusthammer::grammar::transform::verify",
        "--start-from", "rusthammer::grammar::sequence::bind",
        "--start-from", "rusthammer::grammar::permutation::permutation",
        "--start-from", "rusthammer::grammar::permutation::required",
        "--start-from", "{impl rusthammer::grammar::permutation::Layout for _}",
        "--start-from", "{impl rusthammer::grammar::permutation::Items for _}",
        "--start-from", "{impl rusthammer::grammar::permutation::ItemEval for _}",
        "--start-from", "{impl core::clone::Clone for rusthammer::grammar::permutation::Permutation}",
        "--start-from", "{impl core::clone::Clone for rusthammer::grammar::permutation::Required}",
        "--start-from", "rusthammer::marker_example::parse_marker",
        "--start-from", "rusthammer::record_example::parse_record",
        "--start-from", "rusthammer::grammar::numeric::Bits::new",
        "--start-from", "rusthammer::grammar::numeric::Bits::width",
        "--start-from", "rusthammer::span_types::BitSpan::new",
        "--start-from", "rusthammer::span_types::BitSpan::input",
        "--start-from", "rusthammer::span_types::BitSpan::start",
        "--start-from", "rusthammer::span_types::BitSpan::end",
        "--start-from", "rusthammer::span_types::BitSpan::bit_order",
        "--start-from", "rusthammer::span_types::BitSpan::is_empty",
        "--start-from", "rusthammer::span_types::BitSpan::as_bytes",
        "--start-from", "rusthammer::grammar::position::SkipBits::new",
        "--start-from", "rusthammer::grammar::position::SkipBits::bits",
        "--start-from", "rusthammer::grammar::numeric::SignedBits::new",
        "--start-from", "rusthammer::grammar::numeric::SignedBits::width",
        "--start-from", "rusthammer::grammar::bytes::BytePattern::new",
        "--start-from", "rusthammer::grammar::bytes::BytePattern::pattern",
        "--start-from", "rusthammer::grammar::bytes::ByteIn::new",
        "--start-from", "rusthammer::grammar::bytes::ByteIn::accepts",
        "--start-from", "rusthammer::grammar::bytes::ByteNotIn::new",
        "--start-from", "rusthammer::grammar::bytes::ByteNotIn::accepts",
        "--start-from", "rusthammer::grammar::transform::IntRange::new",
        "--start-from", "rusthammer::grammar::transform::IntRange::lower",
        "--start-from", "rusthammer::grammar::transform::IntRange::upper",
        "--start-from", "rusthammer::grammar::numeric::Literal::new",
        "--start-from", "rusthammer::grammar::numeric::Literal::width",
        "--start-from", "rusthammer::grammar::numeric::Literal::value",
        "--start-from", "rusthammer::marker_example::Marker::new",
        "--start-from", "rusthammer::record_example::RecordParser::new",
        "--start-from", "rusthammer::grammar::control::Fail::new",
        "--start-from", "{impl core::default::Default for rusthammer::grammar::control::Fail}",
        "--start-from", "rusthammer::grammar::repeat::Repeat::new",
        "--start-from", "rusthammer::grammar::repeat::Repeat::exact",
        "--start-from", "rusthammer::grammar::repeat::Repeat::at_least",
        "--start-from", "rusthammer::grammar::repeat::Repeat::min",
        "--start-from", "rusthammer::grammar::repeat::Repeat::max",
        "--start-from", "rusthammer::grammar::repeat::FoldRepeat::new",
        "--start-from", "rusthammer::grammar::repeat::FoldRepeat::exact",
        "--start-from", "rusthammer::grammar::repeat::FoldRepeat::at_least",
        "--start-from", "rusthammer::grammar::repeat::FoldRepeat::min",
        "--start-from", "rusthammer::grammar::repeat::FoldRepeat::max",
        "--start-from", "rusthammer::grammar::repeat::SepBy::new",
        "--start-from", "rusthammer::grammar::repeat::SepBy::exact",
        "--start-from", "rusthammer::grammar::repeat::SepBy::at_least",
        "--start-from", "rusthammer::grammar::repeat::SepBy::min",
        "--start-from", "rusthammer::grammar::repeat::SepBy::max",
        "--start-from", "rusthammer::grammar::repeat::FoldSepBy::new",
        "--start-from", "rusthammer::grammar::repeat::FoldSepBy::exact",
        "--start-from", "rusthammer::grammar::repeat::FoldSepBy::at_least",
        "--start-from", "rusthammer::grammar::repeat::FoldSepBy::min",
        "--start-from", "rusthammer::grammar::repeat::FoldSepBy::max",
        "--start-from", "{impl rusthammer::parser_traits::Parser for _}",
        "--start-from", "{impl rusthammer::parser_traits::Eval for _}",
        # Clone roots follow definition paths, including the private family modules.
        *(
            arg
            for module in (
                "input_types", "parser_traits", "span_types", "grammar::numeric", "grammar::bytes",
                "grammar::position", "grammar::order", "grammar::sequence",
                "grammar::control", "grammar::transform", "grammar::span", "grammar::repeat",
            )
            for arg in ("--start-from", f"{{impl core::clone::Clone for rusthammer::{module}::_}}")
        ),
        "--start-from", "{impl core::clone::Clone for rusthammer::marker_example::Marker}",
        "--start-from", "{impl core::clone::Clone for rusthammer::record_example::RecordParser}",
        "--include", "core::option::{impl core::clone::Clone for core::option::Option}",
    )
    run(
        *library_extraction,
        "--dest-file", "target/rusthammer.llbc", "--", "--lib", "--locked", "--features", "alloc",
    )
    translate(aeneas, "target/rusthammer.llbc", "lean/RustHammer", "RustHammer.Code")
    run("python3", ROOT / "tools/generate_permutation_tuple_proofs.py", "--check")

    optimized = ROOT / "target" / "optimized"
    optimized.mkdir(parents=True, exist_ok=True)
    run(
        *library_extraction, "--mir", "optimized",
        "--dest-file", optimized / "rusthammer.llbc",
        "--", "--lib", "--locked", "--features", "alloc",
    )
    translate(aeneas, optimized / "rusthammer.llbc", optimized / "lean", "RustHammer.Optimized")

    # This is a separate Cargo package with a normal path dependency. Keep its
    # outputs under the main target directory; Charon runs in each package's cwd,
    # so its output path must be absolute. The consumer is compiled last.
    consumer = ROOT / "target" / "cross-crate"
    consumer.mkdir(parents=True, exist_ok=True)
    manifest = ROOT / "probes" / "cross_crate" / "Cargo.toml"
    cargo_args = ("--manifest-path", manifest, "--target-dir", consumer / "cargo", "--locked")
    run("cargo", "fmt", "--manifest-path", manifest, "--check")
    run("cargo", "test", *cargo_args, "--no-default-features")
    run("cargo", "test", *cargo_args, "--features", "alloc")
    entries = (
        "checked_flag", "packet", "complete_bit", "blocks", "leading_ones", "backend_payload",
        "folded_checksum", "leading_ones_count",
        "separated_blocks", "separated_checksum",
        "bound_payload", "bound_literal", "bound_blocks", "bound_reference",
        "matched_pattern", "pattern_and_input",
        "signed_field", "signed_and_unsigned",
        "integers16", "integers32", "integers64", "complete_i8",
        "ranged_u64", "ranged_pair", "ranged_count", "complete_range",
        "byte_in", "byte_not_in", "byte_set_pair", "complete_byte_set",
        "owned_byte_set", "byte_set_accepts",
        "skipped_position", "reported_position", "complete_skip", "skip_configuration",
        "restricted_payload", "difference_pattern", "exclusive_patterns", "exclusive_value",
        "complete_matches",
        "ordered_fields", "scoped_payload", "scoped_pattern",
        "spanned_pattern", "recognized_payload", "scoped_span", "span_views", "backend_span",
        "constructor_header", "constructor_choice", "constructor_payload",
        "permuted_borrows", "permuted_headers", "permuted_backend", "permuted_empty", "permuted_twelve",
    )
    entry_args = [
        arg for name in entries
        for arg in ("--start-from-if-exists", f"rusthammer_cross_crate_probe::{name}")
    ]
    run(
        str(charon), "cargo", "--preset=aeneas", "--sysroot", "default",
        *entry_args, "--include", "rusthammer::_",
        "--dest-file", consumer / "rusthammer_cross_crate_probe.llbc",
        "--", "--lib", *cargo_args, "--features", "alloc",
    )
    translate(
        aeneas, consumer / "rusthammer_cross_crate_probe.llbc",
        consumer / "lean", "RustHammer.Consumer",
    )
    consumer_lean = consumer / "lean" / "RusthammerCrossCrateProbe.lean"
    # The if-exists roots intentionally skip the dependency's own compiler run.
    # Do not mistake an empty dependency extraction for a successful consumer run.
    for name in entries:
        if not re.search(rf"^def {name}\s", consumer_lean.read_text(), re.M):
            parser.error(f"missing consumer entry point {name} in {consumer_lean}")

    compatibility_files = [optimized / "lean" / "Rusthammer.lean", consumer_lean]

    # Check project code only; dependency models remain part of the trust boundary.
    for path in [*(ROOT / "lean" / "RustHammer").glob("*.lean"), *compatibility_files]:
        if re.search(r"\b(?:sorry|admit)\b|^\s*(?:axiom|opaque)\s", path.read_text(), re.M):
            parser.error(f"unproved or opaque declaration in {path}")
    run("lake", "build", cwd=ROOT / "lean")
    audit_proofs()
    for path in compatibility_files:
        run("lake", "env", "lean", "-DwarningAsError=true", path, cwd=ROOT / "lean")


if __name__ == "__main__":
    main()
