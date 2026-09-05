# Formalization certificate draft

This is a partial-scope draft, not a certificate for the whole paper.

Source: the publisher version of Zilong He, *On n-ADC integral quadratic
lattices over algebraic number fields*, Doc. Math. 30 (2025), 981--1022,
DOI 10.4171/DM/1003. The exact SHA-256 is recorded in `00_audit_scope.md`
and the paper manifest. The arXiv version is comparison-only.

Checked classification checkpoint: `272d810ea2ca8bd0e19ac97f6d9cda1853502cde`.
Later central-obstruction checkpoint: `cd8ecbddef7b18979cfabcc1b1ba0afd640268cb`.
Later terminal-alpha checkpoint: `b0f832e5ff4dd1fe0f305371c029ce2015b004e5`.
Later partial Lemma 6.8 checkpoint: `b624d40be62d4e939f28715e631ce7c42a9e642e`,
only clauses (i)--(ii), independently AI-reviewed with 15 standard-only queries.
Later generic checkpoint: `b728bce20942191785d0b50f2c068e0b5ee7c2f7`,
clauses (v),(vi) with 16 standard-only queries and independent AI review.
Printed wrappers explicitly require compatible Delta in U; report 24 and
`SOURCE_DELTA.md` record the convention. That checkpoint supplied 4/6.
Later second-endpoint checkpoint: `074f2cdcd63637fb6f6d8c65879e55968a1dc675`,
full (iii) and only n>=4 of (iv), with independent replay of twelve new
standard-only queries. Report 25 records 5/6 whole clauses and partial (iv).
Complete binary-testing checkpoint: `0aa3848ca5aae079c2944174e687af8c068b9573`.
Explicit mismatch checkpoint: `fe2a459a4152ade94299a61d1c4958fefa646ba0`.
Reports 30--31 prove and independently audit a nonvacuous counterexample to
the n=2 instance printed in Lemma 6.8(iv). That clause is
`SEMANTIC_MISMATCH`; the n>=4 formal endpoint remains provisional.
Full Lemma 6.12 checkpoint: `cf9f83be635d6e459cfb429ad73b4c7a31f1ddf4`.
Report 32 source-first audits the actual exceptional quaternary lattice as
2-ADC, not 3-ADC, and nonmaximal, with sixteen standard-only axiom reports and
a concrete `Q_2` nonvacuity entry.
Toolchain: Lean 4.32.1; dependency revisions are in `lake-manifest.json`.
The listed concrete dyadic endpoints pass incremental kernel checks. The
new maximal-profile criteria, thirteen published-family endpoints, complete
Proposition 4.13, both dyadic clauses of Proposition 4.16, all four clauses of
Lemma 6.4, both clauses of Lemmas 6.5--6.7, full Theorem 6.1, and volume criterion depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

The audited declaration groups and scope limitations are in
`05_theorem_correspondence.md`. Semantic matches remain provisional. In
particular, explicit arithmetic premises in the global reductions are not
proved by their axiom reports. No statement here certifies the unformalized
classifications, enumeration, or omitted boundary cases.

Independent author approval: pending. Independent domain-expert approval:
pending. Independent formalization-expert approval: pending. Reproducibility:
the f6f7485/c82668b tree passed clean-kit CI with enforced dependencies
through full Lemma 6.7. The later partial Lemma 6.8 revision has passed
incremental checks, and the later full Lemma 6.12 revision has passed direct
local checks; both still require exact-revision clean-kit CI. Exact
commit distinctions are in report 11. Overall project grade: D because one
core source result has a substantive semantic mismatch. Whole-paper
completion: not achieved.
