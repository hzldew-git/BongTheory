# Lemma 7.15 isometry classification

Status: `FULLY_FORMALIZED` / `PROVISIONAL_MATCH`.

Code checkpoint: `06d25079c6dac69bc0439b94e694fa52c81961ed`.

## Source authority

The sole semantic authority is the publisher version of record:

- Zilong He, *On n-ADC integral quadratic lattices over algebraic number
  fields*, *Documenta Mathematica* 30 (2025), no. 4, 981--1022;
- DOI: <https://doi.org/10.4171/DM/1003>;
- publisher PDF SHA-256:
  `E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Lemma 7.15 begins on p. 1013 and its proof ends on p. 1014. The
post-publication arXiv revision remains comparison-only.

## Formal statement

For odd `n=2k+3`, let `L` and `M` be two `n`-ADC lattices of rank `n+2`,
equipped with good BONGs `a` and `b`. The public endpoint
`heADC2025Lemma715` proves

```text
L is integrally isometric to M
  iff
their ambient quadratic spaces are isometric
  and R_(n+1)(L) = R_(n+1)(M).
```

The Lean index `2*k+3` is zero-based and therefore denotes the paper's
one-based invariant `R_(n+1)`. Both directions are proved. Necessity derives
ambient isometry and equality of the complete order sequence from an actual
integral lattice isometry.

## Equality of orders and alpha invariants

`heADC2025Lemma715_sameOrders` first uses Theorem 7.4 to identify the orders
through `R_n`. The hypothesis identifies `R_(n+1)`. Lemma 7.14 and the
ambient-space isometry then identify the last order by determinant parity,
without assuming that the two ambient columns are definitionally equal.

In the nonmaximal branch `R_(n+1) != -2e`, the alpha sequence is calculated
internally. The alternating part is `0,2e`, the boundary value is `alpha_n=1`,
and the terminal value is `alpha_(n+1)=1-R_(n+1)`. The last formula uses the
odd-gap case when the last order is one and Beli Corollary 2.3(i) when it is
zero. Thus `heADC2025Lemma715_sameAlphas` discharges condition (ii) of Beli's
classification theorem rather than retaining it as caller data.

## Prefix defects and internal representation

`heADC2025Lemma715_prefixDefectBounds` proves condition (iii) for every
prefix. Odd prefixes use parity of the doubled order sum, early even prefixes
use the alternating signed prefix and the domination principle, and the
terminal prefix uses Proposition 3.5(v) together with the preceding
`2e`-defect bound.

For condition (iv), the formal proof shows that the only possible strict
alpha-sum trigger is the source index `i=n-1`. Proposition 3.5(iv)--(v)
identifies the two actual prefix space classes, and the already formalized
Lemma 4.4(ii) representation theorem supplies the required map. The endpoint
`heADC2025Lemma715_internalRepresentations` therefore contains no uniqueness,
classification, or representation-law premise.

With all four concrete Beli Theorem 3.1 conditions proved,
`heADC2025Lemma715_nonmaximal` concludes actual integral lattice isometry.

## Maximal branch

When `R_(n+1)=-2e`, Theorem 7.4 gives the standard odd maximal order profile.
`heADC2025Lemma715_isOMaximal_of_penultimate` applies the proved volume-order
criterion to show that each lattice is `O`-maximal. Uniqueness of maximal
lattices in isometric ambient spaces then gives their integral isometry.
This is the formal counterpart of the two Lemma 4.12 cases used in the
published proof and avoids adding a model-identification premise.

## Statement-strength conclusion

The public theorem retains the two source invariants and assumes only the
two `n`-ADC conditions together with chosen good BONGs used to name
`R_(n+1)`. Its four Beli classification conditions, all alpha formulas,
prefix representations, determinant parity, and maximality are proved
internally. The theorem is therefore `LOGICALLY_EQUIVALENT` to Lemma 7.15
under the paper's standing good-BONG convention.

## Mechanical trust checks

The Lemma 7.15 module, canonical paper entry, and focused audit compile
directly with Lean 4.32.1. Six selected dependency reports, including the
main theorem and both maximality branches, contain exactly `propext`,
`Classical.choice`, and `Quot.sound`. The enforcing focused gate reports
`AXIOM_GATE_PASS: 59348 declarations checked`. The comment-aware scanner
checks 2,729 tracked Lean files and finds no forbidden proof token outside
comments. All changed Lean source lines satisfy the 100-column limit, and
`git diff --check` passes.

These are local checks at the stated code commit. Exact-revision Review Kit
CI, release promotion, and independent human sign-off remain separate gates.

## Coverage consequence

Section 7 now has twelve fully formalized numbered items: Theorems 7.1 and
7.4 and Lemmas 7.5--7.12, 7.14, and 7.15. Lemma 7.13 remains a documented
source quantifier mismatch. Theorem 7.2, Remark 7.3, Definition 7.16,
Remark 7.17, Lemmas 7.18--7.20, and Corollary 7.21 remain pending.

Author decision: unsigned. Domain-expert decision: unsigned.
Formalization-expert decision: unsigned.
