# Theorem 7.1 and corrected binary classification

Status: Theorem 7.1 is `FULLY_FORMALIZED` / `PROVISIONAL_MATCH`.
The publisher's theorem statement is correct, but its printed proof is
`INCOMPLETE_PROOF`: it relies on the false binary specialization of Theorem
6.2 and omits a second nonmaximal rank-four 2-ADC isometry class.

Code checkpoint: `c3e6092f05a0f3b2872fefbd21554cc5461104ce`.

## Source authority

The sole semantic authority is the publisher version of record:

- Zilong He, *On n-ADC integral quadratic lattices over algebraic number
  fields*, *Documenta Mathematica* 30 (2025), no. 4, 981--1022;
- DOI: <https://doi.org/10.4171/DM/1003>;
- publisher PDF SHA-256:
  `E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Page 1006 states that, for odd `n>=3` and `rank M=n+1`, the lattice `M` is
`n`-ADC if and only if it is maximal. The printed necessity proof descends
from `n`-ADC to `(n-1)`-ADC and invokes Theorem 6.2. It then excludes only the
exceptional lattice of Lemma 6.12 by its failure to be 3-ADC.

## The omitted branch

The formal refutations in reports 31 and 34 show that Theorem 6.2 has a
second binary exception: an actual nonmaximal 2-ADC lattice in
`W_2^4(Delta)`. Consequently the published proof of Theorem 7.1 does not
exhaust the `n=3` case. This is a proof gap, not a counterexample to Theorem
7.1, because the omitted lattice can also be excluded from 3-ADC.

`GoodBONG.heADCQuaternaryBoundaryCandidate_not_is3ADC` proves that exclusion
against an actual maximal ternary target. The proof computes the terminal
mixed defect and comparison alpha for both maximal ternary profiles and
derives failure of the literal representation criterion.

## Corrected binary classification

`Lattice.heADC2025Theorem62_binary_corrected` proves that every rank-four
2-ADC lattice belongs to exactly the required exhaustive disjunction:

1. it is maximal;
2. it is isometric to the Lemma 6.12 exception in `W_1^4(Delta)`; or
3. it is isometric to the additional boundary lattice in `W_2^4(Delta)`.

The new second-discriminant argument first proves the exact order alternatives
for an arbitrary 2-ADC lattice in `W_2^4(Delta)`. The endpoint tests force the
third order to be `1`, and the terminal tests leave only the maximal value
`1-2e` or the boundary value `3-2e`. In the boundary case, the proof derives
the complete alpha profile, prefix-defect inequalities, and internal
representations required by Beli's integral-isometry classification. Thus
the conclusion is an actual lattice isometry, not merely an order-profile
classification.

## Formal proof of Theorem 7.1

`Lattice.IsNADC.of_succ` proves the monotonicity step used by the paper:
`(m+1)`-ADC descends to `m`-ADC when one ambient dimension remains. It extends
an arbitrary integral rank-`m` target by a sufficiently rescaled integral
anisotropic line in the orthogonal complement and then restricts the resulting
representation.

`Lattice.heADC2025Theorem71` has the literal public hypotheses

- `3 <= n`;
- `Odd n`;
- `finrank K V = n+1`;

and concludes `IsNADC q L n <-> IsOMaximal q L`. Its necessity proof has two
branches:

- at `n=3`, apply the corrected three-way binary classification and contradict
  the independently proved failure of 3-ADC for each nonmaximal class;
- at odd `n>=5`, apply the already proved, valid `n-1>=4` restriction of
  Theorem 6.2.

The converse is the general maximal-implies-ADC theorem. No good BONG,
classification law, supplied profile, or testing-catalogue premise remains in
the public statement.

## Mechanical trust checks

The four new proof modules, canonical paper entry, and focused paper audit
compile directly with Lean 4.32.1. The seven new transitive dependency reports
contain exactly `propext`, `Classical.choice`, and `Quot.sound`. The focused
enforcing gate reports `AXIOM_GATE_PASS: 58019 declarations checked`. The
comment-aware scanner checks 2,715 tracked Lean sources and finds no forbidden
proof token outside comments. All new Lean source lines satisfy the
100-column limit.

These are local checks at the stated commit. Exact-revision Review Kit CI,
release promotion, and human sign-off remain separate gates.

## Coverage consequence

Theorem 7.1 is the first of the 21 directly numbered Section 7 items to be
fully formalized. Theorem 7.2 through Corollary 7.21 remain pending. This
checkpoint does not repair the false statements of Lemma 6.8(iv) or Theorem
6.2; it repairs the downstream proof of a separately true theorem.

Author decision: unsigned. Domain-expert decision: unsigned.
Formalization-expert decision: unsigned.
