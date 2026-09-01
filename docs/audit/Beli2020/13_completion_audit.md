# Completion audit

## Outcome

The mathematical scope of Constantin-Nicolae Beli's
*Universal integral quadratic forms over dyadic local fields* is represented
by checked Lean definitions and proof endpoints.  The umbrella import is:

```lean
import Bong.Bong.BeliUniversalComplete
```

The completion claim covers Theorem 2.1, the Jordan translation, and all
numbered Section 4 results.  It does not claim that the frozen source contains
no typo: Theorem 3.1(3.2.1--2) has a documented normalization discrepancy.

## Public endpoints

| Paper region | Public endpoint |
| --- | --- |
| Theorem 2.1 | `BONG.GoodBONG.isUniversal_iff_universalTheorem21Conditions` |
| Theorem 3.1, direct derivation | `Lattice.JordanDecomposition.isUniversal_iff_universalTheorem31DirectConditions` |
| Theorem 3.1, literal text at first scale zero | `Lattice.JordanDecomposition.isUniversal_iff_universalTheorem31Conditions_of_firstScaleOrder_eq_zero` |
| Lemmas 4.1--4.4 | `Lattice.beliUniversalLemma41` through `beliUniversalLemma44` |
| Corollary 4.5 | `Lattice.beliUniversalCorollary45i` through `beliUniversalCorollary45iv` |
| Lemmas 4.6--4.9 | `BONG.GoodBONG.beliUniversalLemma46` through `beliUniversalLemma49` |
| Corollary 4.10 | `BONG.GoodBONG.beliUniversalCorollary410` |

All listed signatures have zero project-specific law/data parameters.

## Theorem 3.1 proof architecture

The source calls Theorem 3.1 a translation of Theorem 2.1 but supplies no
proof.  The Lean derivation performs the following checked steps:

1. obtain a good BONG from the lattice;
2. align its order profile with the user-supplied strict Jordan
   decomposition;
3. turn that decomposition into the weak form required by the 2019
   approximation theorem;
4. use determinant defect and codimension-one cancellation to identify the
   relevant prescribed Jordan prefix with the good-BONG prefix;
5. translate Cases 1, 2, 3, and 4, including all low-rank branches;
6. eliminate the internal good BONG and profile witness.

The proof separately establishes that a universal lattice cannot have rank
one: a one-dimensional form represents only one determinant square class,
contradicting a chosen nonsquare multiplier.

## Source discrepancy

For first Jordan component rank two and `u_1=0`, the profile gives
`R_1=0`, `R_2=2r_1`, and `R_3=u_2`.  Substitution in Theorem 2.1,
II(b), produces ideal order

```text
2e + 2r_1 + u_2 - 2 floor(u_2/2)
```

in (3.2.1), and the analogous expression with `u_2` omitted in (3.2.2).
The frozen paper prints coefficient `r_1`.  The formalization records both
forms and proves that they coincide when `r_1=0`.  No stronger source repair
is inferred.

## Section 4 closure

The Section 4 chain is constructive at theorem level:

- maximal integral superlattices reduce `n`-universality to maximal targets;
- maximal-lattice uniqueness and half-hyperbolic splitting prove Lemmas
  4.2--4.4;
- the rank 3, rank 4, and stable cases give Corollary 4.5;
- alternating BONG blocks, concatenation, and exact splitting prove Lemmas
  4.6--4.8;
- Lemma 4.9 transports all residual invariants and prefix spaces;
- Corollary 4.10 combines Lemma 4.9 with Theorem 2.1 and includes the minimal
  tail.

## Trust and semantic verdict

The focused audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.  Placeholder and custom-axiom scans are required by the
reproducibility report.

Kernel status: **checked**.

Coverage status: **`FORMALIZATION_COMPLETE_WITH_SOURCE_DISCREPANCY`**.

Semantic status: **`PROVISIONAL_MATCH`**, because the review cards remain
unsigned and the Theorem 3.1 coefficient awaits independent or author
confirmation.
