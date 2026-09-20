# Theorem 1.7 even-scope checkpoint

Status: `CONDITIONAL_FORMALIZATION_EVEN_SCOPE` /
`SOURCE_PROOF_SCOPE_MATCH`.

Code checkpoint:
`89714ff139144299a56853131c23725d1b426374` on
`release/heclassic-v0.5.0-rc.1-prep`.

## Source authority and locator

The sole semantic authority is the author-corrected v5 TeX manuscript
`classic_dyadic-n-uni-v5.tex`, SHA-256
`C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
Theorem 1.7 is stated at line 227. Its proof at lines 1675--1679 performs the
coefficient calculation for even `n` and then says only that a similar
argument applies for odd `n`. No odd calculation or cited parity reduction is
provided. Reports 24 and 26 independently record the surrounding odd-parity
failure in Corollary 6.3; that counterexample does not itself decide whether
Theorem 1.7 has a different valid odd proof.

## Formal change

The former source-facing `he2022ClassicTheorem17` had no parity hypothesis.
Its proof depended on the structure field
`diagonal_localAdjacentDefectsLarge_of_universal`, which silently packaged the
missing coefficient calculation for every rank. This overstates the evidence
available from v5.

The field is replaced by
`diagonal_localAdjacentDefectsLarge_of_universal_even`, with an explicit
`Even n` premise. Two theorems now separate the proof layers:

- `he2022ClassicTheorem17_even` states the proof-supported source conclusion
  for `2 <= n` and `Even n`;
- `he2022ClassicTheorem17_of_localAdjacentDefectsLarge` proves the
  parity-independent final contradiction for `1 <= n`, but requires as an
  explicit premise the local adjacent-defect profile at every relevant
  ramified dyadic place.

The second theorem is a reusable logical reduction, not an unrestricted
formalization of the paper theorem. It makes the exact missing mathematical
obligation visible to a future odd-rank proof.

## Proof structure retained

Given the explicit local-defect premise, Lean derives a contradiction by:

1. obtaining a ramified dyadic prime from the concrete
   discriminant--ramification theorem and the typed place bridge;
2. using ramification-index positivity to strengthen `e != 1` to `1 < e`;
3. localizing global universality via Proposition 8.2;
4. applying the local Theorem 1.5 obstruction to force `e = 1`.

For even `n`, the new structure field supplies the source's coefficient
calculation and the public theorem invokes this common logical reduction.

## Mechanical evidence

With Lean 4.32.1, the canonical paper entry and both affected audit modules
complete a 5,665-job build. Both new endpoints print only `propext`,
`Classical.choice`, and `Quot.sound`. All 30 CI policy tests pass. The
comment-aware scanner checks 2,796 tracked Lean sources without a forbidden
proof token outside comments. All added Lean lines are at most 100 columns,
and `git diff --check` passes. The full imported-closure gate reports
`AXIOM_GATE_PASS: 70695 declarations checked`.

These are incremental working-tree checks. A fresh-extraction Review Kit and
GitHub CI receipt for the final release commit remain separate requirements.

## Fidelity boundary

No unrestricted odd Theorem 1.7 endpoint is exported. The v5 odd sentence
remains unsupported until the author supplies a complete coefficient
calculation or restricts the theorem in a later manuscript. Concrete
number-field lattice/localization instances also remain unfinished. This
scope correction therefore improves fidelity but does not alter the Grade-D
whole-paper verdict.
