# Non-dyadic Lemma 4.7 table-profile certificate

## Status

Checkpoint: `ec135d8bdaedb35bf3f29b0518661e23f2251ccf`.

Classification: `CONCRETE_FINITE_DATA_CERTIFICATE` and
`CONDITIONAL_FORMALIZATION` for Lemmas 4.7--4.8 as whole statements.

This checkpoint makes the publisher's literal non-dyadic block table and its
Jordan-rank arithmetic internal. It does not promote the whole non-dyadic
local-field branch to an unconditional theorem.

## Authoritative source

The statement authority is Zilong He, *On n-ADC integral quadratic lattices
over algebraic number fields*, *Documenta Mathematica* 30 (2025), no. 4,
981--1022, DOI 10.4171/DM/1003. The publisher PDF has SHA-256

`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Lemma 4.7 and its two-column maximal-lattice table are on p. 993. Lemma 4.8
and its proof are on p. 994. The proof of Lemma 5.3, which uses the relevant
`J_0` and `J_{0,1}` ranks, is on pp. 996--997.

## What is now internal

`Bong.Bong.He2023ADCNonDyadicTable` represents each displayed block by one of
the following symbolic atoms:

- a unimodular hyperbolic plane `H`, of total and scale-zero rank two; or
- a unary block in one of the four square classes `1`, `Delta`, `pi`, and
  `Delta*pi`, with scale zero for the first two and scale one for the last two.

The module transcribes all eight even-rank and all eight odd-rank
column/square-class formulas. The powers of `H` and every ordered unary tail
are explicit data, including multiplication by `Delta`. Lean proves:

- every defined even row has rank `2*k`;
- every defined odd row has rank `2*k+1`;
- the scale-zero and scale-one components exhaust each defined row, which is
  the finite table content of `J_{0,1}(N)=N`;
- every uniformizer-class row has `J_0` rank one below the total rank;
- every first-column unit-class row is wholly of scale zero;
- in rank one only the first column is defined;
- the sole missing row from the eight rank-two pairs is `N_2^2(1)`;
- exactly seven rank-two rows are defined; and
- the parity-specific definedness predicates agree, in the ranks used by
  Theorem 1.10, with the common catalogue predicate.

The existing `He2023ADCNonDyadicTheorem110` module now imports this table
certificate and reuses its common definedness predicate. Thus the seven-row
binary index and the symbolic source table cannot silently drift apart.

The independent Mathematica program
`scripts/verification/verify_he2023adc_nondyadic_table.wl` separately checks
the 16 formulas symbolically. Its exact result is:

```text
<|evenRows -> True, oddRows -> True, jordanZeroOne -> True,
  uniformizerJ0Ranks -> True, firstUnitJ0Ranks -> True,
  deltaTwistInvolution -> True, binaryUndefinedRow -> True,
  binaryDefinedCount -> True|>
```

## What remains external

The symbolic certificate does not prove:

- realization of the rows as actual integral lattices over every non-dyadic
  local field;
- maximality, isometry classification, exhaustion, or irredundancy of those
  realized rows, including Lemma 4.7(ii)'s minimal testing-set assertion;
- the representation equivalence in the second sentence of Lemma 4.8;
- the quadratic-space separation and ambient-representation inputs from
  Lemmas 4.4--4.6;
- a concrete instance of `SectionFiveLaws` or `CatalogueLaws`; or
- the non-dyadic case of Proposition 4.16.

In particular, a proof about ranks of the transcribed block expressions is
not a proof of the cited local-lattice classification theorem.

## Mechanical evidence and trust boundary

At the stated code checkpoint, the table module, non-dyadic Theorem 1.10
module, canonical paper entry, full paper audit, and the new focused table
audit complete a 5,557-job build with Lean 4.32.1. The focused audit reports
only `propext`, `Classical.choice`, and `Quot.sound`, with several endpoints
using proper subsets. The comment-aware scanner checks 2,772 tracked Lean
sources, the 25 scanner/deployment-policy tests pass, all changed Lean lines
are at most 100 columns, `git diff --check` passes, and both Mathematica
verification programs exit successfully.

This build used the repository's existing dependency worktrees, for which
Lean reported local-change warnings. It is therefore local kernel evidence,
not an exact clean Review Kit receipt. A source-only archive, fresh extraction,
locked clean dependencies, full rebuild, paper gates, and the enforcing axiom
gate remain required for reproducibility promotion. Human semantic review also
remains unsigned. The whole-paper verdict stays Grade D and `NOT_COMPLETE`.
