# Published maximal-profile checkpoint

## Frozen materials

- Paper: Zilong He, *On n-ADC integral quadratic lattices over algebraic
  number fields*, Documenta Mathematica 30 (2025), 981--1022.
- Authority: publisher version of record, DOI 10.4171/DM/1003; publisher
  SHA-256 as recorded in `00_audit_scope.md`.
- Locations: page 986 standing integrality convention; pages 994--995,
  Lemmas 4.11--4.12 and the notation in Definition 4.1.
- Code: `976883e6cda7c17402c4c1f0bc768db555460eae` on
  `feat/he-formalization`, Lean 4.32.1, locked `lake-manifest.json`.
- Audit date: 5 September 2026, Asia/Shanghai.
- New files: `Bong/Bong/He2023ADCPublishedProfiles.lean` and
  `Bong/Bong/He2023ADCGenericProfiles.lean`.

## Result and declaration inventory

All names below have prefix `Bong.BONG.GoodBONG.`. The two paper lemmas
are split into thirteen public branches; thirteen declarations do not mean
thirteen numbered paper results.

| Paper branch | Public declaration | Tail after the indicated hyperbolic pairs |
|---|---|---|
| 4.11(i), `c=1` | `heADC2025Lemma411iOnePublished` | `0,-2e` |
| 4.11(i), `c=Delta` | `heADC2025Lemma411iDeltaPublished` | `0,-2e` |
| 4.11(ii), `c=1` | `heADC2025Lemma411iiOnePublished` | `0,-2e,1,1-2e` |
| 4.11(ii), `c=Delta` | `heADC2025Lemma411iiDeltaPublished` | `1,1-2e` |
| 4.11(iii), nonexceptional unit, first column | `heADC2025Lemma411iiiUnitFirstPublished` | `0,1-d(c)` |
| 4.11(iii), nonexceptional unit, second column | `heADC2025Lemma411iiiUnitSecondPublished` | `0,1-d(c)` |
| 4.11(iii), unit-uniformizer, first column | `heADC2025Lemma411iiiUniformizerFirstPublished` | `0,1` |
| 4.11(iii), unit-uniformizer, second column | `heADC2025Lemma411iiiUniformizerSecondPublished` | `0,1` |
| 4.12(i), rank at least three | `heADC2025Lemma412iPublished` | `0` |
| 4.12(ii), rank at least three | `heADC2025Lemma412iiPublished` | `0,2-2e,0` |
| 4.12(iii), first column, rank at least three | `heADC2025Lemma412iiiFirstPublished` | `1` |
| 4.12(iii), second column, rank at least three | `heADC2025Lemma412iiiSecondPublished` | `0,-2e,1` |
| 4.12(i)(iii), rank one | `heADC2025Lemma412UnaryPublished` | the parameter's order, zero or one |

Every hyperbolic pair contributes `0,-2e`. In the odd first-column theorems,
the number of pairs is `k+1`; this gives every rank at least three. The unary
endpoint supplies rank one. The even second-column square row starts at
rank four. There is no unary second-column row and no binary second-column
square row.

## Actual formal meaning and proof boundary

Each public theorem concerns an arbitrary integral lattice `L`, any good
BONG of `L`, and an isometry of its ambient space with the specified named
`W` space. It proves an equivalence: `L` is integrally isometric to the
chosen named maximal lattice `N` if and only if every good-BONG order is
the displayed order. Integral isometry is not a hypothesis.

The common transport is `isIsometric_publishedModel_iff_orderProfile`.
Its proof uses the whole-space isometry obtained from the checked
equal-rank diagonal representation, then maximal-lattice uniqueness to
identify the concrete maximal lattice with the chosen `N`. It transfers a
good BONG by that integral isometry. The underlying converse uses the
maximal-volume criterion proved at the preceding checkpoint.

The nonexceptional unit domain is `IsValuationUnit` together with exclusion
of the square and discriminant square classes. These are the classes
excluded by the published representative domain. The finite defect and its
oddness, nonnegativity and strict upper bound are derived by
`heADCUnitSharpDefectData`. Finiteness is obtained from `HeHuSharpData`;
the proof does not infer a finite defect merely from conversion to a natural
number. The sharp partner is a proved valuation unit. For a unit times a
uniformizer, the odd valuation proves defect zero and excludes both
exceptional classes.

The final second odd-column theorem does not assume existence of a special
unit. `exists_unit_defectOrder_eq_twoE_sub_one` constructs such a unit from
the proved dyadic defect theorem. `heADC2025Lemma412iiPublishedOfKappa`
is an intermediate theorem only; the public endpoint above discharges it.

## Adversarial and trust checks

- Both directions are kernel-checked for arbitrary input lattices, not only
  for the reference examples.
- Public conclusions now use Definition 4.1's `W/N` families. The earlier
  model-correspondence gap is closed for these two lemmas.
- The integrality premise agrees with the standing convention on page 986.
- All thirteen public endpoints passed `#print axioms`: only `propext`,
  `Classical.choice`, and `Quot.sound` occur.
- Both new modules, the paper entry and the expanded paper audit passed
  incremental compilation. Neither new module contains an admitted proof,
  project axiom or native-computation shortcut.
- Reused mathematics: proved Beli classification, He--Hu concrete models
  and diagonal identifications, and maximal-lattice uniqueness. This is a
  reuse-based formalization, not a claim to reprove those dependencies in
  isolation within this paper's files.
- A separate read-only AI reviewer independently checked all thirteen
  public types against the publisher and reran their axiom checks. No
  blocking semantic issue was found. The reviewer confirmed the `W/N`
  linkage, all rank boundaries, the auxiliary-unit discharge, finite-defect
  parity, square-class domains, and the standing integrality convention.
  Independent human review remains outstanding.
- Exact-revision clean-kit CI is still required; local incremental checks
  do not certify a clean environment.

## Author review card: Lemma 4.11

Paper statement in ordinary mathematical language: for an integral lattice
of even rank on one of the stated spaces, integral isometry to the named
maximal lattice is equivalent to the listed BONG order conditions.

Formal statement in ordinary mathematical language: the same equivalence
is provided in eight branches, for every good BONG of the input lattice.
The generic unit branch is formulated on the corresponding nonexceptional
square classes, and the unit-uniformizer branches allow every valuation unit.

Assumptions in both: dyadic local field, integral lattice, specified even
rank, specified ambient-space isometry and parameter square class. The
formal field interface also spells out characteristic zero and the valuation
and topology structures. No reference-lattice isometry or desired order
conclusion is assumed. The mathematical meaning of `DyadicContext` remains
part of the shared foundational audit.

Quantifiers and conclusion: universal over the input lattice and its good
BONG; both directions; equality means integral lattice isometry. Boundary:
rank two is included except for the undefined second-column square case.
Normalization: `e=ord(2)`, integral hyperbolic BONG orders `0,-2e`, zero-based
formal indices corresponding to one-based paper indices.

Status: `PROVISIONAL_MATCH`; scoped code coverage: `FULLY_FORMALIZED`.

Author/domain-expert questions: confirm the square-class domain translation,
sign conventions and all rank-two exclusions. Formalization-expert questions:
review the public types, exact diagonal transport and clean-kit replay.
No human approval or signature is recorded.

## Author review card: Lemma 4.12

Paper statement in ordinary mathematical language: for an integral lattice
of odd rank on one of the stated spaces, integral isometry to the named
maximal lattice is equivalent to the listed BONG order conditions.

Formal statement in ordinary mathematical language: four branches cover
odd rank at least three, and a fifth covers rank one. The second unit-column
branch internally constructs its auxiliary unit of defect `2e-1`.

Assumptions in both: the same dyadic field, integrality, odd rank, unit or
unit-uniformizer parameter, and ambient-space isometry. The unary theorem
uses the equivalent normalized order condition `0 <= ord(c) <= 1`.
Quantifiers and conclusion: universal over the input lattice and its good
BONG; both directions; integral lattice isometry. Boundary: first column
includes rank one; second column begins at rank three. Normalization and
indexing agree with the preceding card.

Status: `PROVISIONAL_MATCH`; scoped code coverage: `FULLY_FORMALIZED`.

Author/domain-expert questions: confirm the second-column terminal orders
and the unary normalization. Formalization-expert questions: inspect the
absence of an auxiliary-unit or classification-law premise, the actual
chosen maximal lattice and the clean replay. No human approval or signature
is recorded.

## Scoped outcome and exclusions

This checkpoint reviews two numbered lemmas, not any additional main theorem.
Both have complete branch proofs with provisional semantic matches. No result
is promoted to `VERIFIED_MATCH` without the required human approval.

Proposition 4.13, Proposition 4.16, unary testing-set minimality, non-dyadic
results, the ADC classifications of Sections 5--7, concrete global arithmetic,
and enumeration remain outside this checkpoint. Whole-paper coverage stays
in progress, grade C; reproducibility stays `PARTIALLY_REPRODUCIBLE` pending
clean-kit validation. This report is not a whole-paper certificate.
