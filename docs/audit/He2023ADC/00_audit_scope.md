# Audit scope

The sole semantic authority is the 42-page Doc. Math. version of record, DOI
10.4171/DM/1003, SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.
The 2025 arXiv v3 revision is comparison-only. The publisher hash was checked
again while validating code commit `2a151a8024d10ae094df958cd3626dbd13c447c2`.

The current audited code checkpoint is `b728bce20942191785d0b50f2c068e0b5ee7c2f7`,
branch `feat/he-formalization`, Lean 4.32.1, audited on 5 September 2026
(Asia/Shanghai). Its additional published-family endpoints for Lemmas
4.11--4.12 are detailed in `14_published_profile_checkpoint.md`; the subsequent
complete Proposition 4.13 is audited in `15_odd_maximal_structure_checkpoint.md`.
The dyadic specialization of both clauses of Proposition 4.16 is recorded
in `16_quaternary_maximal_checkpoint.md`. Its non-dyadic scope remains open.
The four clauses of Lemma 6.4 are recorded in `17_even_testing_checkpoint.md`.
Both clauses of Lemma 6.5 are recorded in `18_even_obstruction_checkpoint.md`.
The complete Theorem 6.1 is recorded in `19_even_corank_one_checkpoint.md`.
The literal published Theorem 3.6 interface is independently reviewed at
`218cfb917fed8d1123af0d64e28c206312676f77` in report 20.
Both complete Lemma 6.6 clauses are independently reviewed at
`cd8ecbddef7b18979cfabcc1b1ba0afd640268cb` in report 21.
Both complete Lemma 6.7 clauses are independently reviewed at
`b0f832e5ff4dd1fe0f305371c029ce2015b004e5` in report 22.
Lemma 6.8(i)--(ii), only 2/6 clauses of that lemma, are independently
reviewed at `b624d40` in report 23. The clean-kit receipt through full
Lemma 6.7 is f6f7485/c82668b; it does not include report 23's new proofs.
The later report 24 independently reviews clauses (v)--(vi) at b728bce,
including the explicit Delta-in-U convention for the printed domain.
Lemma 6.8 now has 4/6 clauses; (iii)--(iv) remain open. Neither later
addition is certified by the f6f7485/c82668b clean run.

Current concrete coverage includes the dyadic definition and maximal-testing
reduction, the stable-rank local equivalence, Section 3 endpoints, and the
Section 4 endpoints, Theorem 6.1, Lemmas 6.4--6.7 and Lemma 6.8(i),(ii),(v),(vi) listed in
`05_theorem_correspondence.md`. The global
predicates and logical reductions are also in scope, with their arithmetic
premises still undischarged. This audit does not certify the missing local,
global, or enumerative classifications.
