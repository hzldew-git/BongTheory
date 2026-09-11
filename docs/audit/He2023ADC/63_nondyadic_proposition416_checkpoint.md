# Non-dyadic Proposition 4.16 checkpoint

## Status

Checkpoint: `2cf9133`.

Classification: `CONCRETE_FINITE_DATA_CERTIFICATE` for the Table 4.7 case
split and `CONDITIONAL_FORMALIZATION` for Proposition 4.16 over non-dyadic
local fields.

## Authoritative source

The statement authority is Zilong He, *On n-ADC integral quadratic lattices
over algebraic number fields*, *Documenta Mathematica* 30 (2025), no. 4,
981--1022, DOI 10.4171/DM/1003. The publisher PDF has SHA-256

`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Proposition 4.16 and its one-sentence proof from Lemmas 4.7(i) and 4.9(i)
occur on p. 996. This report covers its non-dyadic branch only. The already
formalized dyadic branch remains separate.

## Finite table argument now internal

The rank-four specialization of the publisher's non-dyadic table is proved
to have the exact following dichotomy:

- the row `N_2^4(1)` is the ordered symbolic sum
  `<1, Delta> perp <pi, Delta*pi>`, corresponding to `A perp A(pi)`; or
- the row contains a displayed hyperbolic-plane block `H`.

The first row equality and the exhaustive dichotomy are kernel theorems, not
an assumption or an informal inspection of the table. The independent
Mathematica verifier also checks the exceptional row and confirms that each
of the other seven rank-four rows contains `H`.

`He2023ADCNonDyadicProposition416` then proves the published maximal-lattice
conclusion from two explicit interfaces:

1. `CatalogueLaws`, which classifies every maximal rank-four lattice by a
   defined Table 4.7 row; and
2. `QuaternaryTableRealizationLaws`, which interprets a displayed `H` block
   as actual lattice representation, identifies the exceptional row with
   `A perp A(pi)`, and transports representation and isometry.

The main theorem returns the exceptional integral-isometry class or actual
representation of the supplied hyperbolic plane. A corollary proves the
literal "outside the exceptional class, represents `H`" formulation.

## Mechanical evidence

The new theorem module, focused audit, canonical paper entry, and all
dependencies complete a 5,557-job build with Lean 4.32.1. Both new endpoints
report only `propext`. The comment-aware scanner checks 2,774 tracked Lean
sources, all 27 CI policy and scanner tests pass, changed Lean lines are at
most 100 columns, and `git diff --check` passes.

The expanded Mathematica result ends with:

```text
exceptionalQuaternaryRow -> True,
otherQuaternaryRowsContainH -> True
```

## Remaining trust boundary

This is not yet an unconditional proof over the repository's concrete local
lattice type. The actual non-dyadic maximal-lattice classification, the
interpretation of every symbolic row as an integral lattice, the direct-sum
representation bridge, and the integral isometry
`N_2^4(1) ~= A perp A(pi)` remain visible fields. No field states the final
Proposition 4.16 dichotomy itself.

Consequently, the non-dyadic branch advances from `FAIL / pending` to a
conditional theorem with its complete finite table deduction internal, but
does not count as a concrete local-field completion. A new exact Review Kit
for this later checkpoint and independent human semantic sign-off remain
separate requirements.
