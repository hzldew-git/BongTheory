# Canonical number-field arithmetic adapter

Status: `PROVED_CANONICAL_ARITHMETIC_ADAPTER` / `LOWERED_GLOBAL_INTERFACE`.

Code checkpoint:
`129f19e896c38f70b7c63bea9d8b3bd48ed0ffcb` on
`release/heclassic-v0.5.0-rc.1-prep`.

## Source authority and role

The sole semantic authority remains the author-corrected v5 TeX manuscript
`classic_dyadic-n-uni-v5.tex`, SHA-256
`C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
Section 8 uses the standard non-archimedean primes of a number field, the
dyadic primes among them, their ramification indices over two, and parity of
the field discriminant. This checkpoint fixes those meanings in the formal
global-data layer.

## Construction

`HeClassic2024NumberFieldGlobalData` asks for an equivalence between the
abstract place type and
`IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)`, together
with only the non-arithmetic fields of the Section 8 model. Its
`toGlobalData` constructor defines:

- `isDyadic p` by membership of two in the prime ideal at `p`;
- `ramificationIndexAt p` by the actual prime-ideal ramification index; and
- `discriminantOdd` by nondivisibility of the number-field discriminant by two.

Consequently `heightOneSpectrumIdentification` proves all three compatibility
statements by definitional equality. It then constructs
`NumberFieldDiscriminantBridge`, including primality and dyadic-prime
coverage, using the result of Report 34.

`SectionEightInputs` retains the actual lattice-theoretic obligations but has
no fields asserting discriminant parity, ramification-index positivity, the
discriminant--ramification equivalence, or the odd-discriminant-to-index-one
implication. `sectionEightLaws` obtains all of them from the concrete
number-field theorem and builds the finite-place universality package from
the three remaining local representation branches.

## Mechanical evidence

With Lean 4.32.1, the new module and its focused audit complete a 5,646-job
build. The canonical paper entry and combined Classic audit complete a
5,667-job build. The four audited constructors use only `propext`,
`Classical.choice`, and `Quot.sound`. Added Lean lines are at most 100 columns,
and `git diff --check` passes. All 30 CI policy tests pass, the
comment-aware scanner checks 2,798 tracked Lean sources, and the focused
imported-closure gate reports
`AXIOM_GATE_PASS: 62790 declarations checked`.

These are incremental local checks. A later exact source-only Review Kit must
record the final commit, payload hashes, fresh extraction, all manifest
audits, dependency pins, policy tests, and the enforcing axiom gate.

## Remaining boundary

This adapter does not construct a global quadratic-lattice carrier,
localization at finite completions, the equivalence between a future model's
place type and the height-one spectrum, positive-definite globalization,
local sum-of-squares representation branches, scalar extension of good BONGs,
or strong approximation. It also does not repair the false odd clause of v5
Corollary 6.3 or the affected unrestricted odd global statements. The
whole-paper grade therefore remains D and the completion verdict remains
`NOT_COMPLETE`.
