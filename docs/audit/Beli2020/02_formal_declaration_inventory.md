# Formal declaration inventory

The umbrella module is `Bong.Bong.BeliUniversalComplete`.

## Section 2

| Paper item | Principal Lean endpoint |
| --- | --- |
| Lemma 2.2 | `BONG.beliUniversalLemma22` |
| Lemma 2.3 | `beliUniversalLemma23` |
| Lemma 2.4 | `beliUniversalLemma24` |
| Lemma 2.5 | `BONG.GoodBONG.universalUnaryOrderConditions_iff_order_zero` |
| Lemmas 2.6--2.10 | `BeliUniversalDefect`, `BeliUniversalAlpha`, and `universalUnaryDefectConditions_iff_alphaZero_or_caseIIPrime` |
| Lemmas 2.11--2.14 | Endpoint, central, and long equivalences in `BeliUniversalEndpoint`, `BeliUniversalCentral`, and `BeliUniversalLong` |
| Theorem 2.1 | `BONG.GoodBONG.beliUniversalTheorem21`; `BONG.GoodBONG.isUniversal_iff_universalTheorem21Conditions` |

`UniversalTheorem21CaseAnalysisObligation` is proposition-valued audit data;
it is inhabited by `universalTheorem21CaseAnalysis_proved` and is not an
assumption.

## Section 3

| Object | Principal Lean declaration |
| --- | --- |
| Literal printed cases | `Lattice.JordanDecomposition.UniversalJordanCase1` through `UniversalJordanCase4` |
| Literal printed RHS | `UniversalTheorem31Conditions` |
| Directly substituted (3.2.1--2) | `UniversalJordanCase321Direct`, `UniversalJordanCase322Direct` |
| Direct complete RHS | `UniversalTheorem31DirectConditions` |
| Arbitrary-Jordan theorem | `Lattice.JordanDecomposition.isUniversal_iff_universalTheorem31DirectConditions` |
| Literal zero-scale theorem | `Lattice.JordanDecomposition.isUniversal_iff_universalTheorem31Conditions_of_firstScaleOrder_eq_zero` |
| Predicate comparison | `universalTheorem31DirectConditions_iff_of_firstScaleOrder_eq_zero` |

The public arbitrary-Jordan endpoint accepts only the Jordan decomposition.  A
good BONG and its alignment profile are chosen and discharged internally.

## Section 4

| Paper item | Principal Lean endpoint |
| --- | --- |
| Lemma 4.1 | `Lattice.beliUniversalLemma41` |
| Lemma 4.2 | `Lattice.beliUniversalLemma42` |
| Lemma 4.3 | `Lattice.beliUniversalLemma43` |
| Lemma 4.4 | `Lattice.beliUniversalLemma44` |
| Corollary 4.5(i--iv) | `Lattice.beliUniversalCorollary45i` through `beliUniversalCorollary45iv` |
| Lemma 4.6 | `BONG.GoodBONG.beliUniversalLemma46` |
| Lemma 4.7 | `BONG.GoodBONG.beliUniversalLemma47` |
| Lemma 4.8 | `BONG.GoodBONG.beliUniversalLemma48` |
| Lemma 4.9 | `BONG.GoodBONG.beliUniversalLemma49` |
| Corollary 4.10 | `BONG.GoodBONG.beliUniversalCorollary410` |

Supporting structures such as `UniversalLemma49AdaptedData` and
`UniversalCorollary410Conditions` package proof data and the printed case
split.  They are conclusions or definitions, not hypotheses of a paper-wide
endpoint.
