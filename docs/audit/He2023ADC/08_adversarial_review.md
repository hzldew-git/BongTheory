# Adversarial review

An independent read-only AI reviewer checked each frozen Lemma 6.4 clause
through final code `d94cc797ad8ed83c53447c139b496d5a2ca8f4fb`. It confirmed
all four clauses, the five actual tests, derived profiles and ranks, raw
defects, both kappa columns, binary/e=1/codimension-one boundaries, and
absence of circularity. It independently recompiled every new module with
queries, each frozen entry and complete audit; all twenty new axiom sets
were standard-only. It also checked that earlier clauses were unchanged at
the final commit. Combined local proof coverage: `FULLY_FORMALIZED`;
semantics: `PROVISIONAL_MATCH`. See report 17. Clean-kit CI and human
sign-off remain separate, unfulfilled gates.

The separate reviewer audited the frozen dyadic Proposition 4.16 code at
`5fff59784a0a3dd4442405f204519c36e0a8e468` after independently extracting
the published scope. No semantic blocker was found. Both directions of the
exception, integral rather than only ambient isometry, the exact half-scaled
Gram matrix, form rather than vector scaling, and all public premises were
checked. The reviewer reran the module, entry and complete audit successfully.
The dyadic restriction is `FULLY_FORMALIZED` / `PROVISIONAL_MATCH`; the whole
published proposition remains `SPECIAL_CASE_ONLY`. See report 16.

The focused independent review of Proposition 4.13 at `9c432a6` found no
blocking mismatch. It checked all three clauses, the n=3 and e=1 boundaries,
the capped rather than raw defect, finite rational embedding into `WithTop`,
all derived auxiliary data, and absence of circularity. Report 15 records
the evidence and remaining human-review and clean-build obligations.

Primary risks are omitting the ambient-space representation hypothesis,
confusing local with global `n`-ADC, replacing integral representation by space
representation, and overstating the dyadic specialization. Boundary ranks and
the preservation of rank when passing to maximal over-lattices require explicit
checking.

The volume proof was checked for a potentially circular converse. It chooses
a maximal integral superlattice `P` of the arbitrary lattice `L`, identifies
`P` with the independently proved maximal reference `M`, and uses equal
volume to prove `L=P`. It does not assume that `L` was maximal.

The predicate `HeADCMaximalProfileCriterion` was expanded for inspection:
its reference BONG selects the reference space, lattice and length. Its
conclusion still quantifies over every good BONG of the arbitrary input
lattice. The new endpoints do not have a classification-law hypothesis.

An independent read-only AI review of code snapshot
`2a151a8024d10ae094df958cd3626dbd13c447c2` compared the publisher's
pages 994--995 with the expanded declarations. It confirmed both logical
directions, all ten displayed order profiles, the signed odd-row parameters,
rank-one inclusion in the first column, and exclusion of the undefined
binary second-column square row. Its live type and axiom inspection found
only the three disclosed foundational axioms.

The review identified a correspondence gap: the criteria use concrete
half-hyperbolic extensions, whereas Definition 4.1 uses chosen diagonal
`W` spaces and their chosen maximal `N` lattices. Explicit whole-row
transport, generic-row parameter specializations, and the named-lattice
existence component of Remark 4.10 remain to be assembled at this snapshot.
Thus these are complete concrete-model proofs, not yet fully connected
paper-definition endpoints. No sign error or false converse was found.

That finding applies to checkpoint `2a151a8`. The subsequent checkpoint
`976883e6cda7c17402c4c1f0bc768db555460eae` adds the whole-row transport
and all thirteen published-family endpoints. The follow-up independent
review found no blocking semantic issue in all thirteen public endpoints.
It confirmed the named `W/N` linkage, the source's standing integrality
convention, the rank boundaries, finite-defect arithmetic and absence of
undischarged auxiliary-unit or project-law premises. It recommends
`FULLY_FORMALIZED` coverage for these two lemmas with `PROVISIONAL_MATCH`
semantics pending human confirmation. Its scope is recorded in report 14.

Other open checks include the rank-one portion of Lemma 4.9(ii) and the
remaining small-rank clauses of Section 3. This AI review is not human
author or expert sign-off, and did not perform a clean-environment build.
