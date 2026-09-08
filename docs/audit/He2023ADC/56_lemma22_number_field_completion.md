# Lemma 2.2 number-field completion checkpoint

## Source authority and conclusion

The sole semantic authority remains the publisher version of record:

- Zilong He, *On n-ADC integral quadratic lattices over algebraic number
  fields*, Doc. Math. 30 (2025), 981--1022;
- DOI: <https://doi.org/10.4171/DM/1003>;
- Lemma 2.2 and its proof: pp. 986--987;
- publisher-PDF SHA-256:
  `E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Checkpoint: `83cc791bf7b2ae80c6d812da7f26f562bf40c859`.

At this checkpoint Lemma 2.2 is no longer conditional on a separately
supplied one-dimensional descent premise. For every number field `K`, finite
place `p`, finite-dimensional nondegenerate quadratic space `V` over `K`, and
represented nondegenerate quadratic space over `p.adicCompletion K`, the
formal endpoint returns an actual nondegenerate submodule of `V` whose scalar
extension is isometric to the represented local space.

## Formal proof chain

The new module
`Bong.QuadraticSpace.He2025SubspaceDescentTopology` completes the base case
left explicit in Report 55.

1. `hasOpenNonzeroSquareClasses_of_complete` proves that every nonzero square
   class is open in a complete nontrivially normed characteristic-zero field.
   It applies the one-dimensional inverse function theorem to
   `x |-> A * x^2` at each nonzero `x`; the strict derivative
   `A * 2 * x` is nonzero.
2. `hasOneDimensionalSubspaceDescent_of_denseRange_of_openSquareClasses`
   diagonalizes the global quadratic space, pulls an open local square class
   back along the diagonal quadratic polynomial, and uses coordinatewise
   density to select a global vector. The chosen value is proved nonzero.
3. `numberFieldFiniteCompletionHasOneDimensionalSubspaceDescent` obtains
   density from mathlib's
   `IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap` and obtains
   square-class openness from step 1.
4. `heADC2025Lemma22_numberFieldFiniteCompletion` combines that base case
   with the induction from Report 55. Its result is the literal range
   submodule inside the original global space, not merely an abstract
   diagonal coefficient list.

Supporting additions prove the representation of a scaled line by a vector,
the isometry of square-equivalent scaled lines, and compatibility of a scaled
line with scalar extension.

## Statement-strength and trust findings

- proof status for Lemma 2.2: `FULLY_FORMALIZED`;
- semantic status: `PROVISIONAL_MATCH` pending human comparison;
- source discrepancy: none found in this lemma;
- human-review status: unsigned;
- whole-paper completion status: unchanged, `NOT_COMPLETE`.

The theorem is specialized to mathlib's finite-place completion of a number
field, which is the publisher setting. The generic density/open-square-class
theorem remains visible for auditing. No project axiom or proposition-valued
law package is used by the concrete finite-completion endpoint.

The use of a general inverse function theorem replaces the publisher's cited
local-field square-class fact with a kernel-checked proof of the needed
openness. This is a proof-method variation, not a change in conclusion.

## Mechanical evidence

The following checks pass with Lean 4.32.1:

```text
lake build Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
lake env lean Bong/QuadraticSpace/He2025SubspaceDescentTopology.lean
lake build Bong.Papers.He2023ADC
lake env lean BongTest/FieldDiagonalizationAudit.lean
lake env lean BongTest/ScalarExtensionAudit.lean
lake env lean BongTest/He2023ADCAudit.lean
python scripts/ci/check_lean_proof_commands.py
python scripts/ci/run_axiom_gate.py --entry Bong.Papers.He2023ADC
```

The paper entry build completes 5,540 jobs. The source scanner checks 2,764
tracked Lean sources and finds no forbidden proof command outside comments.
The focused imported-closure gate reports:

```text
AXIOM_GATE_PASS: 60485 declarations checked
```

The selected new endpoints depend only on:

```text
propext
Classical.choice
Quot.sound
```

This is local cached evidence. An exact clean extracted Review Kit, GitHub CI,
release asset, and independent human approval remain separate gates.

## Human review card

Reviewers should verify:

1. that mathlib's finite-place completion and scalar-extension instances
   agree with the paper's `F_p` and `V_p` conventions;
2. that openness of the full nonzero square class is exactly the neighborhood
   fact used on pp. 986--987;
3. that the coordinatewise density step preserves the intended quadratic
   value and excludes zero;
4. that the returned range submodule is the paper's `U` and not only an
   isometric external model.

Author decision: unsigned. Domain-expert decision: unsigned.
Formalization-expert decision: unsigned.
