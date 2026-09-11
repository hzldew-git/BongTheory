# Lemma 2.2 subspace-descent checkpoint

## Source authority and statement

The sole semantic authority is the publisher version of record:

- Zilong He, *On n-ADC integral quadratic lattices over algebraic number
  fields*, Doc. Math. 30 (2025), 981--1022;
- DOI: <https://doi.org/10.4171/DM/1003>;
- Lemma 2.2 and its proof: pp. 986--987;
- publisher-PDF SHA-256:
  `E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

The paper starts with a nondegenerate subspace `U(p)` of the completion
`V_p` and concludes that there is a nondegenerate subspace `U` of `V` whose
completion is isometric to `U(p)`. Its one-dimensional case uses density of
the number field in the completion and openness of the relevant nonzero
square class. For higher dimension, the proof splits off a line, applies the
induction hypothesis to its orthogonal complement, and invokes Witt
cancellation.

## Formal endpoints

Checkpoint: `04b721092c911d94932d871ec21815a5286da3d6`.

- `QuadraticSpace.scalarExtension` implements extension of scalars by the
  tensor product and proves the expected formulas on pure tensors.
- `QuadraticSpace.Representation.scalarExtension` transports an embedding of
  quadratic spaces across a field extension.
- `QuadraticSpace.fieldDiagonalizationIsometry` diagonalizes every
  finite-dimensional nondegenerate quadratic space over a field of
  characteristic zero.
- `QuadraticSpace.fieldOrthogonalSumLeftCancelRepresents` proves the
  representation form of Witt cancellation needed in the induction.
- `QuadraticSpace.HasOneDimensionalSubspaceDescent` states exactly the
  remaining one-dimensional arithmetic input.
- `QuadraticSpace.finiteDiagonalSubspaceDescent` proves the full induction
  while preserving the number of diagonal coefficients.
- `QuadraticSpace.heADC2025Lemma22_representation` handles an arbitrary
  finite-dimensional local quadratic space after diagonalization.
- `QuadraticSpace.heADC2025Lemma22_of_oneDimensionalDescent` returns the
  actual range submodule of the original global space, proves it
  nondegenerate, and identifies its scalar extension with the prescribed
  local space.

## Boundary of the result

This checkpoint does not assume the desired higher-dimensional conclusion.
All diagonalization, orthogonal splitting, scalar extension, induction, and
cancellation steps are theorem bodies. The only proposition-valued premise is
the one-dimensional descent statement. A concrete instance for an algebraic
number field and one finite completion still has to be proved from the
publisher's density and square-class references.

The status is therefore:

- proof status: `CONDITIONAL_FORMALIZATION`;
- semantic status: `SOURCE_LOGIC_MATCH`;
- human-review status: unsigned;
- whole-paper completion status: unchanged, `NOT_COMPLETE`.

## Mechanical evidence

The following commands pass with Lean 4.32.1:

```text
lake build Bong.QuadraticSpace.FieldDiagonalization
lake build Bong.QuadraticSpace.ScalarExtension
lake build Bong.QuadraticSpace.He2025SubspaceDescent
lake env lean BongTest/FieldDiagonalizationAudit.lean
lake env lean BongTest/ScalarExtensionAudit.lean
lake env lean BongTest/He2023ADCAudit.lean
python scripts/ci/run_axiom_gate.py --entry Bong.Papers.He2023ADC
```

The three module builds completed 3,050, 3,054, and 3,069 jobs,
respectively. Selected axiom reports for the induction, representation form,
and literal subspace endpoint contain only:

```text
propext
Classical.choice
Quot.sound
```

The repository proof-token scanner checks 2,763 tracked Lean sources and
finds no forbidden proof command outside comments. The focused imported-
closure gate reports `AXIOM_GATE_PASS: 60455 declarations checked`. This is
local cached evidence, not a clean extracted Review Kit, GitHub CI, release
promotion, or human semantic approval.

## Human review card

Reviewers should verify:

1. that `HasOneDimensionalSubspaceDescent` is neither stronger nor weaker
   than the one-dimensional square-class step on pp. 986--987;
2. that tensor-product scalar extension agrees with the paper's `V_p`;
3. that representation-form cancellation has the same orientation as the
   displayed decomposition in the publisher proof;
4. that the range submodule is the intended `U`, rather than only an abstract
   isometric diagonal model.

Author decision: unsigned. Domain-expert decision: unsigned.
Formalization-expert decision: unsigned.
