# Author review cards

These cards supersede the historical local-law-boundary cards. At formal
baseline commit `10e8c666bfda81dcac44332cd38f481d8d02e31a`, the public
Theorem 2.1 endpoints have no project-specific law/data parameters.

## Card 1: Base field and normalization

Paper statement: \(F\) is a dyadic local field, with valuation, prime element,
ramification index \(e\), quadratic defect, and Hilbert symbol normalized as in
the paper.

Formal translation: `Field K`, `CharZero K`, the valuative topology, and
`DyadicContext K`; the latter packages a nonarchimedean local field, normalized
additive valuation, selected uniformizer of valuation one, and positive
valuation of two.

Questions: Does this expanded formal structure cover exactly the intended
fields and normalization? Is the project's quadratic-form factor-of-two
convention consistent with every defect and Hilbert-symbol formula?

Decision: [ ] agree  [ ] valid strengthening  [ ] special case  [ ] disagree

## Card 2: Representation orientation

Paper statement: \(N\to M\) means that \(N\) is represented by \(M\), under the
ambient premise \(FN\to FM\).

Formal translation: `q.Represents r` and `Lattice.Represents q r L M`, where
the larger target object supplies an injective form-preserving map from the
smaller source object and the source lattice maps into the target lattice.

Questions: Is this exactly the paper's target/source orientation? Does
integral representation require containment rather than equality of image
lattices at every use?

Decision: [ ] agree  [ ] valid strengthening  [ ] special case  [ ] disagree

## Card 3: Rank and endpoint conventions

Paper statement: target and source ranks are \(m\ge n\), with one-based indices
and instructions to ignore meaningless endpoint conditions.

Formal translation: `hRank : n ≤ m`, good-BONG lengths `m+1` and `n+1`, and
typed finite-index structures for internal, central, long-prefix, and terminal
branches.

Questions: Does every paper index occur exactly once after zero-based
translation? Is positive rank intended throughout? Are all terminal formulas,
especially \(S_{n+1}+A_{n+1}\), represented correctly?

Decision: [ ] agree  [ ] valid strengthening  [ ] special case  [ ] disagree

## Card 4: Conditions (i) and (ii)

Paper statement: the order sequence satisfies condition (i), and every
relevant truncated determinant defect satisfies condition (ii).

Formal translation: `RepresentationOrderCondition` and
`RepresentationDefectCondition`, assembled into `RepresentationConditions`.

Questions: Are inequality directions, strictness, minima, parity cases, and
the value \(∞\) identical to the source? Do the definitions quantify over the
same range when ranks differ?

Decision: [ ] agree  [ ] valid strengthening  [ ] special case  [ ] disagree

## Card 5: Conditions (iii) and (iv)

Paper statement: triggered central prefixes and longer prefixes of the source
are represented by the prescribed target prefixes, with terminal conventions.

Formal translation: `CentralRepresentationConditions` and
`LongRepresentationConditions` use explicit prefix quadratic spaces and typed
trigger indices.

Questions: Are all trigger inequalities strict in the same places? Are prefix
lengths and determinant products free of an off-by-one shift? Is ambient-space
representation, rather than integral lattice representation, intended in each
prefix clause?

Decision: [ ] agree  [ ] valid strengthening  [ ] special case  [ ] disagree

## Card 6: Revised condition (iii')

Paper statement: the v2 paragraph following Theorem 2.1 replaces condition
(iii) by `(iii')`, and Lemma 2.16 proves equivalence under (i)–(ii).

Formal translation: `RepresentationConditionsPrime` uses
`CentralRepresentationConditionsPrime`; `beli2019Lemma216` supplies the
equivalence; `beli2019Theorem21_prime` is the public revised endpoint.

Questions: Does the formal quantifier domain contain exactly every v2
`(iii')` index? Are both truncated defects and exceptional terminal clauses
identical to the revised TeX source?

Decision: [ ] agree  [ ] valid strengthening  [ ] special case  [ ] disagree

## Card 7: Main equivalence and proof scope

Paper statement: under ambient representation, integral representation is
equivalent to conditions (i)–(iv), or to the revised condition package.

Formal translation: `beli2019Theorem21` and `beli2019Theorem21_prime` state
both equivalences for arbitrary positive target/source ranks with `n ≤ m`.
All internal Section 4/5, complement, scaling, Jordan, and local-field law
packages are constructed on the public proof path.

Questions: Does this statement have exactly the paper's object domain and
logical strength? Does any paper-wide convention remain absent from the
formal definitions?

Decision: [ ] agree  [ ] valid strengthening  [ ] special case  [ ] disagree

## Required approval record

- Reviewer name:
- Affiliation or public profile:
- Reviewer role: paper author / domain expert / formalization expert
- Paper PDF and TeX hashes checked:
- Repository full commit checked:
- Reservations or exclusions:
- Date:
- Signature or immutable approval link:

Until these fields and the decisions above are completed by an independent
human reviewer, every card remains `PROVISIONAL_MATCH`.
