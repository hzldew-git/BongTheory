# Headline theorem checkpoint and independent review

Date: 2026-09-05. Fixed code commit:
`31873263c5390f1df802cf9b25d125ee65f79d07`.
Source: publisher version of record, pp. 559-595, SHA-256
`51F3626A15692E2FF0BAAE62F0EBCC4B8BEE02052C4D3CB1EA579B02E17480C1`.
Lean: 4.32.1. Mathlib revision:
`520045ab14e26149ee970e2e617ca04b09bde5d6`.

## Independent extraction and comparison

A separate read-only AI reviewer first extracted Theorems 1.1, 1.3, and 1.5
from the publisher text and only then inspected the formal types and their
definitions. The reviewer was not the author of the audited proof changes.
This is independent AI review, not author or human expert approval.

| Result | Coverage | Semantic assessment |
|---|---|---|
| Theorem 1.1 | `FULLY_FORMALIZED` | `PROVISIONAL_MATCH` |
| Theorem 1.3 | `PARTIALLY_FORMALIZED` | `PARTIAL_FORMALIZATION` |
| Theorem 1.5 | `SPECIAL_CASE_ONLY` | `PARTIAL_FORMALIZATION` |

These are three reviewed headline results, not a fresh whole-paper count.
None of the three is marked `VERIFIED_MATCH`.

Theorem 1.1's full iff, variable domains, index translation, signed defects,
strict inequalities, both parity branches, and small-rank exclusions were
checked. Its proof is separate from the proposition-valued definition.

Theorem 1.5 requires n >= 2 in the code, while the source permits n = 1 and
treats that case separately on p. 586. The local endpoint does not formalize
number-field localization, the all-primes quantifier, or odd discriminant.

For Theorem 1.3, `he2022ClassicLemma74_even` is a genuine even testing iff.
`classicUniversal_implies_all_publishedOdd` proves odd necessity;
`all_publishedOdd_implies_ambientlyUniversal` proves ambient exhaustion;
`all_publishedOdd_implies_classicUniversal_of_lowerJ2` requires the additional
lower-even J2 condition. The explicit residue-cardinality formulas depend on
`HeClassicPublishedCountingLaws`, for which no proved instance was located.
No theorem establishing `IsLiteralMinimalClassicUniversalityTestingFamily`
for either published family was found.

## Source obstruction

The checked endpoint
`he2022ClassicLemma71ii_literal_disjunction_fails` supplies a classic integral
counterexample for e > 1 to the literal Lemma 7.1(ii). The source's standing
integrality convention does not exclude that counterexample. This prevents
using the printed Corollary 7.2 chain as a proof. It does not by itself refute
Theorem 1.3, which could have another proof or require an explicit correction.

No author-approved erratum is claimed. See `SOURCE_DELTA.md` for the detailed
witnesses and other intermediate discrepancies.

## Trust and reproducibility evidence

Both the main worker and the independent reviewer ran the existing Classic
audit module successfully at this code checkpoint. The principal endpoints
for Theorems 1.1 and 1.5, even Lemma 7.4, and the source refutation report only
`propext`, `Classical.choice`, and `Quot.sound`.

The field-law interfaces have generic proved implementations. The counting
interface does not yet have one. No `sorry`, `admit`, new axiom declaration,
or native evaluation was found in the inspected Classic files. These checks
do not replace an inspection of the actual theorem premises.

Both runs used the local cache and reported pre-existing changes in mathlib,
aesop, and batteries. No clean-build claim is inferred from them. Exact-commit
clean-kit CI and final release verification remain separate obligations.

## Conclusion

Grade C is appropriate for this partial development with a disclosed source
obstruction. The refutation is not advertised as a positive proof of the
literal lemma, and the qualified odd theorem is not advertised as an
unconditional match. The remaining work includes proof coverage, concrete
counting arithmetic, source resolution, clean verification, and human review.
