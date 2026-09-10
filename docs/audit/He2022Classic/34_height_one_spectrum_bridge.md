# Height-one-spectrum finite-place bridge

Status: `PROVED_BRIDGE_CONSTRUCTION` / `LOWERED_GLOBAL_INTERFACE`.

Code checkpoint:
`48956eb32d2aa1ba7220ef5d9fb2c8c06904b0c8` on
`release/heclassic-v0.5.0-rc.1-prep`.

## Source role

The sole semantic authority remains the author-corrected v5 TeX manuscript
`classic_dyadic-n-uni-v5.tex`, SHA-256
`C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
Section 8 quantifies over finite primes of the number field. Reports 30 and 32
proved the discriminant--ramification theorem for actual prime ideals but
used `NumberFieldDiscriminantBridge` to relate them to the abstract place
type of `GlobalLocalLatticeSystem`.

## Interface reduction

`HeightOneSpectrumIdentification` now asks only for:

- an equivalence from the abstract place type to
  `IsDedekindDomain.HeightOneSpectrum` of the ring of integers;
- compatibility of the dyadic predicate;
- compatibility of the ramification-index function; and
- compatibility of the odd-discriminant proposition.

Its definition
`HeightOneSpectrumIdentification.numberFieldDiscriminantBridge` constructs
the older bridge automatically. Lean obtains primality from the height-one
spectrum. For coverage, an arbitrary dyadic prime ideal contains the image of
two; characteristic zero proves that this ideal is nonzero, so it defines a
height-one-spectrum point, and surjectivity of the equivalence supplies the
abstract place.

Thus callers no longer provide separate proofs that every abstract place maps
to a prime ideal or that every dyadic prime ideal is covered. These are proved
consequences of the standard finite-place type.

## Mechanical evidence

With Lean 4.32.1, the canonical paper entry and the two affected audit modules
complete a 5,665-job build. The new bridge constructor reports only
`propext`, `Classical.choice`, and `Quot.sound`. All 30 CI policy tests pass;
the scanner checks 2,796 tracked Lean sources; added Lean lines are at most
100 columns; `git diff --check` passes; and the full imported-closure gate
reports `AXIOM_GATE_PASS: 70718 declarations checked`.

These are incremental checks. Exact fresh-extraction and GitHub CI receipts
belong to the later release checkpoint.

## Remaining boundary

The repository still needs a concrete number-field global-lattice system and
proof that its place type, dyadic predicate, ramification index, and
discriminant proposition agree with this standard height-one-spectrum model.
Localization, positive-definite globalization, scalar extension, the local
sum-of-squares branches, and strong approximation also remain open. This
interface reduction does not repair the false odd clause of v5 Corollary 6.3
or the unsupported odd clauses of Lemma 8.3 and Theorems 1.7--1.8, so the
whole-paper grade remains D.
