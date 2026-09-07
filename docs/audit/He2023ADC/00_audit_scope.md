# Audit scope

The sole semantic authority is the 42-page Doc. Math. version of record, DOI
10.4171/DM/1003, SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.
The 2025 arXiv v3 revision is comparison-only. The publisher hash was checked
again while validating code commit `2a151a8024d10ae094df958cd3626dbd13c447c2`.

The current audited code checkpoint is `da6fbd41a4dc0323380b1013283bd20f9fa6b729`,
branch `feat/he-formalization`, Lean 4.32.1, audited on 7 September 2026
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
Report 25 independently reviews full (iii) and the n>=4 special case of (iv)
at 074f2cd. Reports 26--30 then construct and independently audit an actual
nonmaximal 2-ADC lattice in `W_2^4(Delta)`. Report 31 records the formal
negation of the binary instance printed in Lemma 6.8(iv), together with a
concrete `Q_2` nonvacuity check. These later additions are not certified by
the f6f7485/c82668b clean run.
Report 32 gives the source-first audit of full Lemma 6.12 at `cf9f83b`: the
actual exceptional quaternary lattice is 2-ADC, not 3-ADC, and nonmaximal,
with a separate concrete `Q_2` check. It also awaits exact-revision clean CI.
Reports 33--34 complete the valid Section 6 chain, prove the stable part of
Theorem 6.2, and formally refute its false binary biconditional. Report 35
adds the corrected complete binary classification and proves Theorem 7.1;
the source theorem statement matches, while its printed proof omits the
second boundary class. Report 36 proves Theorem 7.4 and the complete
Lemmas 7.5--7.10 and 7.12 chain and records the Lemma 7.13 source mismatch.
Report 37 completes both normalized parameter rows of Lemma 7.11. These
additions also await exact-revision clean CI. Report 38 proves both ambient
columns and both parameter rows of Lemma 7.14 from determinant parity.
Report 39 proves the complete Lemma 7.15 isometry classification, including
the maximal branch and all four Beli conditions in the nonmaximal branch.
Reports 40--42 formalize Definition 7.16, both assertions of Remark 7.17,
Lemma 7.18, and the two literal named-product branches of Lemma 7.19.
Report 43 completes Lemma 7.20: all maximal endpoints, the Hilbert-symbol
selection and named products, existence in every lower row, and the unique
undefined triple.
Report 44 proves Theorem 7.2 in both a representative-independent form and
the literal published finite-parameter form. It also proves the maximal
overlap assertion by comparing the product order with all four normalized
maximal profiles.
Report 45 proves all three literal integral-isometry formulas of Remark 7.3,
including the exact exponent range, negative powers of the uniformizer,
the sharp factor, and the ordered `pi A perp <Delta epsilon>` tail.
Report 46 constructs the complete and irredundant Corollary 7.21 isometry
catalogue, proves its exact maximal partition and counts in terms of `|U|`,
and isolates the cited O'Meara 63:9 numerical substitution as an explicit
undischarged premise.
Report 47 proves every numbered logical deduction in Sections 5 and 8,
together with Theorems 1.5 and 1.7, relative to explicit non-dyadic and
number-field law packages. Their concrete arithmetic instances remain open.
Report 48 propagates the binary boundary audit to Theorems 1.9(ii) and 1.10,
constructs a complete irredundant rank-four catalogue, and proves that the
printed `+1` count must be replaced by `+2` under the paper's own counting
input.
Report 49 records the independently extracted clean Review Kit receipt through
Reports 47--48 at `85772de`. Report 50 closes the later dyadic unary table,
classification, count, and rank-one minimality boundary at `da6fbd4`; this
later checkpoint has exact local evidence but is not contained in that kit.
Report 51 assembles every dyadic branch of Theorem 1.10 at `125dcf2` as an
exact integral-isometry catalogue. It covers equal rank, corank one, stable
even corank two, odd corank two, and the corrected binary boundary. The
cited O'Meara 63:9 input remains a separate gap.
Report 52 assembles the non-dyadic branch of Theorem 1.10 at `d4c56cc` into
exact seven- and eight-row catalogues, including all three rank branches and
the exponent-zero count. This conclusion is conditional on an explicit
non-dyadic catalogue-law package whose concrete instance remains open.

Current concrete coverage includes the dyadic definition and maximal-testing
reduction, the stable-rank local equivalence, Section 3 endpoints, and the
Section 4 endpoints, Theorem 6.1, Lemmas 6.4--6.7, Lemma 6.8(i),(ii),(iii),(v),(vi),
the n>=4 part of (iv), the refutation of its printed n=2 boundary, and full
Lemmas 6.9--6.12, the boundary-complete audit of Theorem 6.2, Remark 6.3,
Theorem 7.1, Theorem 7.4, complete Lemmas 7.5--7.12, full Lemmas 7.14--7.15,
Definition 7.16, Remark 7.17, full Lemmas 7.18--7.20, and the corrected
Lemma 7.13 consequence, together with complete Theorem 7.2 and Remark 7.3,
and the Corollary 7.21 catalogue and conditional numerical wrapper, listed in
`05_theorem_correspondence.md`. The dyadic unary table and the rank-one case
of Lemma 4.9(ii), together with every dyadic branch and the conditional
non-dyadic catalogue deduction of Theorem 1.10, are also complete in their
stated scopes. The Section 5 and Section 8 deductions are
also proved over explicit law packages. The global predicates and logical
reductions are in scope, with their non-dyadic and arithmetic premises still
undischarged. This audit does not certify those concrete instances or the
remaining local and enumerative classifications.
