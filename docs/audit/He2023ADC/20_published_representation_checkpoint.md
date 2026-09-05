# The literal published Theorem 3.6 interface

Date: 2026-09-05. Frozen code:
`218cfb917fed8d1123af0d64e28c206312676f77`.
Authority: the publisher version of record, Doc. Math. 30 (2025), p. 990,
DOI 10.4171/DM/1003, with the PDF hash recorded in `00_audit_scope.md`.

`Bong.BONG.GoodBONG.heADC2025Theorem36Published` exports the printed
four-condition package with ambient representation as a premise.
`heADC2025Theorem36PublishedFull` includes ambient representation in the
right-hand conjunction, matching the printed logical form.

The new interfaces use `RepresentationConditionsPrime`. Its central
condition has the strict cross-order bound and the strict sum bound on the
two capped defects, followed by the required prefix-space representation:

    R_(i+1) > S_(i-1),
    d[-a_(1,i)b_(1,i-2)] + d[-a_(1,i+1)b_(1,i-1)]
      > 2e + S_(i-1) - R_(i+1).

The index is one-based and includes i=n+1 when defined. Missing endpoint
caps are infinity. Conditions (i), (ii) and (iv), including the terminal
omission in (iv), are unchanged. Full lattices, nondegenerate spaces and
the proved dyadic context are the inherited mathematical assumptions.

The older `heADC2025Theorem36` remains a valid equivalent-package adapter.
Its alpha-trigger package and the new defect-trigger package are proved
equivalent using Beli Lemma 2.16 after conditions (i) and (ii) hold. This
does not justify exchanging isolated triggers in an obstruction theorem
that has not proved those hypotheses. Lemma 6.6 therefore must use the
literal trigger and prove failure of the required prefix representation.
No earlier declaration, signature or proof was changed.

The separate read-only reviewer compared the publisher statement with the
elaborated public types, checked caps and terminal indices, and independently
re-elaborated the frozen module, both queries, canonical entry and complete
audit. Both new transitive axiom sets are exactly `propext`,
`Classical.choice`, and `Quot.sound`. There is no supplied law, classification
or trigger-equivalence premise. The proof intentionally reuses the already
proved Beli representation theorem; it is not an independent new proof of it.

Verdict: `PROVISIONAL_MATCH` for two interfaces to one already represented
numbered theorem. No additional numbered-result coverage is claimed.
Author/domain-expert review should confirm the exact bracketed-defect
interpretation; formalization-expert review should check the package versus
isolated-trigger distinction. All human approval fields remain unsigned.

These are cached-local checks with preserved modified dependency worktrees,
not clean-kit or release certification. Whole-paper grade: C;
whole-paper verdict: `NOT_COMPLETE`.
