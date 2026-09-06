# Audit scope

The sole semantic authority is the 37-page publisher version of record, DOI
10.1007/s00229-023-01516-0, SHA-256
`51F3626A15692E2FF0BAAE62F0EBCC4B8BEE02052C4D3CB1EA579B02E17480C1`.
The 2025 arXiv v3 revision is comparison-only.

Code checkpoint: `cf2f474d7bb82ad076ba39b92bcba9f7a2de082a`, branch
`feat/he-formalization`, reviewed on 2026-09-06 with Lean 4.32.1 and the
repository's pinned `lake-manifest.json`.

The checkpoint includes the proved Theorem 1.1 equivalence, local Section 2-6
proof chains, the complete n >= 1 local-field implication underlying Theorem
1.5, the even testing equivalence in Lemma 7.4, and the `C`-row deletion
mechanism in Lemma 7.10(iii). It does not complete
Theorem 1.3, the number-field localization and discriminant clause of Theorem
1.5, or the global results in Section 8.

`SOURCE_DELTA.md` records discrepancies rather than silently changing the
publisher's assertions. In particular, the literal Lemma 7.1(ii) disjunction
has a checked refutation for e > 1; no proof of that false assertion is claimed.

This refresh supersedes the earlier statement-only progress descriptions. It
is not a fresh item-by-item semantic certificate for all 66 numbered items.
Independent human approvals and clean-build evidence at the final release
commit remain required. Overall status: partial coverage, Grade C.
