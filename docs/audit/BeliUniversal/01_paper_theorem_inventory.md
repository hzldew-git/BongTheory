# Paper theorem inventory

## Conventions

The paper works over a finite extension of `Q_2`, with valuation ring
`O`, prime ideal `p`, normalized order `ord), and
`e = ord(2)`.  Quadratic spaces are nondegenerate.  A lattice is integral
when `Q(M) subseteq O` and universal when `Q(M) = O`.  Good-BONG
coefficients are `a_i`, their orders are `R_i`, and their adjacent
invariants are `alpha_i`.

## Imported introductory results

| Identifier | Content | Formal dependency |
| --- | --- | --- |
| Theorem 1.1 | Good-BONG classification criterion | Audited Beli 2009/2010 endpoint |
| Theorem 1.2 | Four-condition representation criterion, including revised `(iii')` | Audited Beli 2019-v2 endpoint |

## Section 2

| Identifier | Content |
| --- | --- |
| Theorem 2.1 | For an integral lattice with a good BONG, universality is equivalent to rank at least two, `R_1=0`, and the complete Case I or Case II conditions. |
| Lemma 2.2 | Integrality is equivalent to `R_1 >= 0`. |
| Lemma 2.3 | Universality reduces to all unary targets of order zero or one and the specialized representation conditions. |
| Lemma 2.4 | Representing the order-zero and order-one lines is equivalent to ambient line-universality. |
| Lemmas 2.5--2.10 | Order, alpha, and unary-defect reductions leading to Case I(a) or II(a'). |
| Corollary 2.9 | First-index specialization of the alpha consequences. |
| Lemmas 2.11--2.14 | Central and long endpoint reductions, including all rank-two and rank-three guards. |

Case I and Case II retain every printed low-rank condition.  Missing
`R_3`, `R_4`, or `alpha_3` entries are represented by typed rank
hypotheses rather than sentinel values.

## Section 3

| Identifier | Content | Fidelity note |
| --- | --- | --- |
| Theorem 3.1 | Jordan-component criterion split by the rank of the first component | Stated without proof in the paper; derived formally from Theorem 2.1 for an arbitrary prescribed Jordan decomposition. |

All cases except (3.2.1) and (3.2.2) translate literally.  Write `r_1` for
the first fundamental scale order and `u_2` for the effective norm order of
the second component.  The paper prints ideal orders corresponding to

- (3.2.1): `2e + r_1 + u_2 - 2 floor(u_2/2)`;
- (3.2.2): `2e + r_1 - 2 floor(u_2/2)`.

The good-BONG/Jordan dictionary gives `R_2 = 2r_1` when the first
component has rank two and `u_1=0`.  Substitution in Theorem 2.1, II(b),
therefore gives `2r_1`, not `r_1`, in both displayed orders.  The literal
and direct predicates coincide when `r_1=0`; no general coincidence is
asserted.

## Section 4

| Identifier | Content |
| --- | --- |
| Lemma 4.1 | `n`-universality is equivalent to representing every `O`-maximal rank-`n` lattice, with source integrality explicit. |
| Lemma 4.2 | Isometric ambient spaces carry `O`-maximal lattices to integrally isometric lattices. |
| Lemma 4.3 | A family with `k` half-hyperbolic planes reduces to a common split source and residual representations. |
| Lemma 4.4 | Maximal-Witt-index targets reduce to lower-rank universality after splitting `k` planes. |
| Corollary 4.5 | Explicit rank 3, rank 4, and stable odd/even reductions. |
| Lemma 4.6 | Alternating good-BONG order pattern characterizes the half-modular unit-norm block. |
| Lemma 4.7 | Concatenation with a residual good BONG gives a good BONG of the orthogonal sum. |
| Lemma 4.8 | Exact good-BONG criterion for splitting the standard half-hyperbolic tower. |
| Lemma 4.9 | Residual order, alpha, defect, and prefix-space shifts after removing the tower. |
| Corollary 4.10 | Exact odd-rank maximal-Witt-index criterion, including the boundary case `m=n+1`. |

The rank and tail parameters are encoded so that every referenced coefficient
or boundary index carries an existence proof.
