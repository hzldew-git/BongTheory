# Non-dyadic Lemma 4.8 representation checkpoint

## Status

Checkpoint: `7fbb6b9`.

Classification: `CONCRETE_FINITE_DATA_CERTIFICATE` for the printed Table 4.7
Jordan assertion and `CONDITIONAL_FORMALIZATION` for the complete lattice
representation equivalence.

## Authoritative source

The statement authority is Zilong He, *On n-ADC integral quadratic lattices
over algebraic number fields*, *Documenta Mathematica* 30 (2025), no. 4,
981--1022, DOI 10.4171/DM/1003. The publisher PDF has SHA-256

`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Lemma 4.8 occurs on p. 994. For a defined maximal row
`N = N_nu^n(c)`, it first states `J_{0,1}(N) = N`. It then states that `M`
represents `N` exactly when `FJ_0(M)` represents `FJ_0(N)` and
`FJ_{0,1}(M)` represents `FN`. The proof cites O. T. O'Meara, *The integral
representations of quadratic forms over local fields*, *American Journal of
Mathematics* 80 (1958), 843--878, Theorem 1.

## Formal statement

`CatalogueLaws.heADC2025Lemma48_jordanZeroOne` quantifies over the exact
common row-definedness predicate. It proves that the corresponding target is
maximal and satisfies the abstract actual-lattice predicate
`isJordanZeroOne`. The row-domain, rank, and symbolic Jordan arithmetic were
already certified independently in Reports 61--62.

`CatalogueLaws.heADC2025Lemma48` then exports the complete printed
equivalence:

```text
represents M (target nu n c) <->
  spaceRepresents (jordanZero M) (jordanZero (target nu n c)) and
  spaceRepresents (jordanZeroOne M) (ambient (target nu n c)).
```

Thus the final Lemma 4.8 statement is no longer merely listed as missing and
is not itself a field of the interface.

## Exposed mathematical input

The second sentence is derived by applying the generic field
`omeara1958Theorem1_of_isJordanZeroOne`. This field records the cited
O'Meara theorem for arbitrary source and target lattices satisfying the
`J_{0,1}=N` condition. It is not specialized to a Table 4.7 row and does not
state He's Lemma 4.8 conclusion as a field.

The repository still lacks a concrete non-dyadic local-field implementation
of that O'Meara interface and of the actual target maximality/classification
laws. Therefore the representation equivalence is conditional and must not
be described as an unconditional concrete-local-field proof.

## Mechanical evidence

The focused module/audit build completes 3,000 jobs. The canonical paper
entry, expanded main audit, and focused Lemma 4.8 audit complete 5,559 jobs
with Lean 4.32.1. Both new endpoints report no axioms. The comment-aware
scanner checks 2,778 tracked Lean sources, all 27 CI policy and scanner tests
pass, changed Lean lines are at most 100 columns, and `git diff --check`
passes.

The exact clean Review Kit in Report 60 predates this checkpoint. A later
exact kit, the concrete O'Meara/local-lattice instances, and independent
human semantic sign-off remain separate gates.
