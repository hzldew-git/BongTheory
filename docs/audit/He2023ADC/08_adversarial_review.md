# Adversarial review

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
