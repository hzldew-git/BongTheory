# Formalization fidelity audits

Every audit artifact in this directory is written in English and distinguishes
kernel acceptance, proof completeness, semantic fidelity, coverage, and
reproducibility.

- `Beli2003`: the three integral spinor-norm main theorems.
- `Beli2006`: the announced classification and representation criteria.
- `Beli2009`: the classification proof and final binary-transformation results.
- `Beli2019V2`: the complete representation proof, including revised condition
  `(iii')`.
- `BeliUniversal`: the 2022 universal-forms paper; Theorem 2.1, the arbitrary-
  Jordan derivation, and every numbered Section 4 result are complete.  The
  printed exponent in Theorem 3.1(3.2.1--2) is retained as a documented source
  discrepancy.

The paper statements and formal statements were extracted independently before
comparison. Current theorem cards are `PROVISIONAL_MATCH`; none is
`VERIFIED_MATCH` until the required human decisions are recorded.

| Source | Current decision report | Human review cards | Current status |
|---|---|---|---|
| Beli 2003 | [`Beli2003/12_executive_summary.md`](Beli2003/12_executive_summary.md) | [`Beli2003/10_author_review_cards.md`](Beli2003/10_author_review_cards.md) | `PROVISIONAL_MATCH` |
| Beli 2006 | [`Beli2006/12_executive_summary.md`](Beli2006/12_executive_summary.md) | [`Beli2006/10_author_review_cards.md`](Beli2006/10_author_review_cards.md) | `PROVISIONAL_MATCH` |
| Beli 2009/2010 | [`Beli2009/12_executive_summary.md`](Beli2009/12_executive_summary.md) | [`Beli2009/10_author_review_cards.md`](Beli2009/10_author_review_cards.md) | `PROVISIONAL_MATCH` |
| Beli 2019 v2 | [`Beli2019V2/15_unconditional_completion_audit.md`](Beli2019V2/15_unconditional_completion_audit.md) | [`Beli2019V2/10_author_review_cards.md`](Beli2019V2/10_author_review_cards.md) | `PROVISIONAL_MATCH` |
| Beli Universal | [`BeliUniversal/13_completion_audit.md`](BeliUniversal/13_completion_audit.md) | [`BeliUniversal/10_author_review_cards.md`](BeliUniversal/10_author_review_cards.md) | `FORMALIZATION_COMPLETE_WITH_SOURCE_DISCREPANCY` |

The two independent reviewer roles, required evidence, and intentionally blank
approval fields are consolidated in
[`IndependentReviewSignoff.md`](IndependentReviewSignoff.md).  Public review is
also requested in
[`semantic-review` issue 4](https://github.com/hzldew-git/BongTheory/issues/4).

Local committed-source reproducibility is recorded separately in
[`../reproducibility/clean-clone-ee826e7.md`](../reproducibility/clean-clone-ee826e7.md).
Public hosted-run evidence is recorded in
[`../reproducibility/github-actions-v0.1.0-rc.1.md`](../reproducibility/github-actions-v0.1.0-rc.1.md).
Neither technical record replaces the independent mathematical and
Lean-review signatures.
