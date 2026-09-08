# Non-dyadic Lemma 4.6 checkpoint

## Status

Checkpoint: `b335b1f2fef52e46bac59c8572d0cbdb94007e24`.

Classification: `CONDITIONAL_FORMALIZATION` / `SOURCE_LOGIC_MATCH`. The full
published non-dyadic deduction is internal; the concrete local-field instance
of its explicit lower-level laws remains pending.

## Authoritative source

The statement authority is Zilong He, *On n-ADC integral quadratic lattices
over algebraic number fields*, *Documenta Mathematica* 30 (2025), no. 4,
981--1022, pp. 993--994, DOI 10.4171/DM/1003. Publisher-PDF SHA-256:

`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

The standing convention (4.1) says that every discussed `W_nu^n(c)` and
`N_nu^n(c)` must be defined. This matters at the omitted non-dyadic rows
`(n,nu)=(1,2)` and `(n,nu,c)=(2,2,1)`.

## Formal statement

`Bong.Bong.He2023ADCNonDyadicLemma46` defines the opposite column `nu.other`,
the ambient and actual exactly-one predicates, and three public endpoints:

- `heADC2025Lemma46iNonDyadic` retains `n >= 2`, the table-definedness
  conditions, the disjunction `rank M=n+1` or `rank M=n+2` with equal
  determinant square class, and both positive and negative actual-lattice
  alternatives;
- `heADC2025Lemma46iiNonDyadic` quantifies over every integral rank-`n`
  lattice whose ambient space is not the opposite table row and concludes
  actual representation; and
- `heADC2025Lemma46iiNonDyadicMaximal` derives the publisher's following
  maximal-lattice sentence from the same general result.

The large row is indexed by `nu` in rank `n+2`; the unique excluded row is
`nu.other` in rank `n`, matching `3-nu` in the paper. Its definedness is
explicit. Since `n>=2`, the large rank is at least four and its table row is
proved internally to be defined.

## Exposed mathematical input

`Lemma46Laws` contains only lower-level facts used by the one-line publisher
proof:

- `lemma45i_corankOne` and `lemma45i_corankTwo` are the ambient exactly-one
  assertions from Lemma 4.5(i);
- `proposition42iii` is the unique-excluding-space assertion from Proposition
  4.2(iii);
- `represents_ambient` and `spaceRepresents_of_isometric_left` are the two
  representation-transport facts; and
- `sectionFive` supplies target rank, target integrality, ambient rank, and
  maximal-lattice integrality.

Neither the actual exactly-one conclusion nor either actual representation
conclusion is a structure field. The proof applies `IsNADC` to the positive
ambient alternatives, converts any prohibited actual representation back to
an ambient one for the negative alternatives, and transports Proposition
4.2(iii) across the source ambient isometry.

The abstract parameter `sameDeterminant` records equality of determinant
square classes. A concrete non-dyadic lattice hierarchy and an instance of
`Lemma46Laws` are still required before this result can be called an
unconditional theorem over every non-dyadic completion.

## Mechanical evidence

The focused audit completes 3,001 jobs. The canonical paper entry, expanded
main audit, and focused audit complete 5,561 jobs with Lean 4.32.1. Part (i)
and the column involution report no axioms; both part-(ii) endpoints report
only `propext`, `Classical.choice`, and `Quot.sound`. The comment-aware scanner
checks 2,782 tracked Lean sources, all 27 CI tests pass, changed Lean lines are
at most 100 columns, JSON parses, and `git diff --check` passes.

The exact clean Review Kit in Report 60 predates this checkpoint. A later
exact kit, the concrete non-dyadic law instance, GitHub exact-tag CI, and
independent human semantic sign-off remain separate gates.
