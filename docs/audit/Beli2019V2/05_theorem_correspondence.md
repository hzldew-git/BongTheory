# Theorem Correspondence

> Historical snapshot notice (28 August 2026): the field-law comparison and
> final verdict below predate complete interface discharge.  See
> `15_unconditional_completion_audit.md` for the current correspondence card.

## Main theorem card

| Feature | Paper Theorem 2.1 | Lean `beli2019Theorem21` | Assessment |
|---|---|---|---|
| Base field | Dyadic local field | Abstract field with dyadic context and 49 project-specific law/data-instance slots | `FORMAL_ASSUMPTIONS_STRONGER` |
| Lattices | Integral quadratic lattices \(M,N\) | `L : Lattice K V` and `M : Lattice K W` | `MATCH_CANDIDATE` |
| Rank | \(n\leq m\) | `hRank : n ≤ m` with actual ranks `n+1,m+1` | Positive-rank restriction |
| Ambient hypothesis | \(FN\) represented by \(FM\) | `ambient : q.Represents r` | `MATCH_CANDIDATE` |
| Integral conclusion | \(N\) represented by \(M\) | `Lattice.Represents q r L M` | `MATCH_CANDIDATE` |
| Condition (i) | Direct/order-pair disjunction | `RepresentationOrderCondition` | `MATCH_CANDIDATE` |
| Condition (ii) | Truncated prefix defect at least \(A_i\) | `RepresentationDefectCondition` | `MATCH_CANDIDATE` |
| Condition (iii) | Triggered central prefix representation | `CentralRepresentationConditions` | `MATCH_CANDIDATE` |
| Condition (iv) | Triggered long prefix representation | `LongRepresentationConditions` | `MATCH_CANDIDATE` |
| Logical form | Integral representation iff four conditions | Iff with `RepresentationConditions` | `MATCH_CANDIDATE` |

No independent author confirmation has been recorded. Consequently the table
uses `MATCH_CANDIDATE` rather than `VERIFIED_MATCH`.

## Revised-v2 theorem card

`beli2019Theorem21_prime` has the same field, lattice, rank, ambient, and
integral-representation components. It replaces only
`CentralRepresentationConditions` by
`CentralRepresentationConditionsPrime`. The conversion is proved through
`BONG.GoodBONG.beli2019Lemma216`, under conditions (i) and (ii), in both
directions.

The revised theorem therefore matches the paper's v2 logical presentation at
the same conditional law boundary. Status:
`FORMAL_ASSUMPTIONS_STRONGER` and overall `FORMALIZATION_WEAKER`.

## Proof-direction correspondence

| Direction | Lean theorem | Paper architecture |
|---|---|---|
| Integral representation implies conditions | `beli2019_necessity` | Prime-index chain, Sections 4--6, and unequal-rank completion |
| Conditions imply representation, equal rank | `not_counterexample_of_equalRank_complete` | Sections 7--9 rank-volume descent |
| Conditions imply representation, strict rank | `beli2019_strictRank_sufficiency_of_equalRank` | Lemmas 2.20--2.21 |
| Conditions imply representation, all ranks | `beli2019_sufficiency_complete` | Equal-rank theorem plus strict-rank completion |
| Original/v2 trigger conversion | `beli2019Lemma216` | Lemma 2.16 |

## Sections 7--9 correspondence

The former abstract final-step typeclass has been eliminated from the public
theorem. The concrete path is:

1. `sectionSeven_equalNorm_or_counterexampleDescent` reaches equal norm or a
   smaller counterexample.
2. `Beli2019SectionNineComplete` dispatches rank three, rank four, and rank at
   least five.
3. Lemma 9.3 supplies the ordinary head reduction.
4. Lemma 9.6 supplies the exceptional head reduction.
5. Lemma 9.12 supplies the residual index-\(\mathfrak p\) descent.
6. `not_counterexample_of_equalRank_reductions` performs well-founded
   induction.
7. unary and binary results close the low-rank base cases.

This is a material improvement over a theorem that merely assumes a final
descent oracle.

## Final correspondence status

The conclusion and four-condition logical shape are plausible matches, and
the v2 trigger replacement is explicit. The unresolved issue is not the final
assembly but the absence of proofs that all required law classes follow from
the paper's single “dyadic local field” hypothesis. The final theorem-level
status is therefore:

**`FORMALIZATION_WEAKER`.**
