# Audit scope

The sole semantic authority is the 42-page Doc. Math. version of record, DOI
10.4171/DM/1003, SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.
The 2025 arXiv v3 revision is comparison-only. The publisher hash was checked
again while validating code commit `2a151a8024d10ae094df958cd3626dbd13c447c2`.

The current audited code checkpoint is `7d7a4d5`, branch
`feat/he-formalization`, Lean 4.32.1, audited on 8 September 2026
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
and originally isolated the cited O'Meara 63:9 numerical substitution as an
explicit undischarged premise. Report 57 supersedes that boundary with an
internal proof.
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
cited O'Meara 63:9 input at that historical checkpoint is closed by report 57.
Report 52 assembles the non-dyadic branch of Theorem 1.10 at `d4c56cc` into
exact seven- and eight-row catalogues, including all three rank branches and
the exponent-zero count. This conclusion is conditional on an explicit
non-dyadic catalogue-law package whose concrete instance remains open.
Report 53 formalizes the finite deductions in Corollary 1.8 and Theorem 1.11
at `8cdd338`. The 586 and 21 counts and the literal Table 2 source-row
selection are proved, while the cited Hanke--Kirschmer--Oh catalogues and the
prime-by-prime local computations remain explicit external inputs.
Report 55 proves the entire higher-dimensional algebraic argument of Lemma
2.2 at `04b7210`, including scalar extension, orthogonal-complement descent,
Witt cancellation, and an actual descended subspace. The publisher's
one-dimensional density and open-square-class input remains explicit.
Report 56 closes that input at `83cc791`: mathlib supplies density of the
number field in its finite-place completion, the inverse function theorem
proves openness of every nonzero square class, and the resulting endpoint is
the publisher's literal descended-subspace statement.
Report 57 proves O'Meara 63:9 at `4ad37e1` from the power-ideal and
principal-unit quotients, the odd square-class layers, the even collapses,
and the two-class discriminant endpoint. It removes the counting premise
from every dyadic numerical conclusion used by He.
Report 58 records the exact independently extracted clean Review Kit at
`7d7a4d5`. It contains Reports 55--57, verifies all 2,060 payload hashes,
completes the 5,560-job build and all four He ADC gates, and therefore
supersedes Report 54 for the current local reproducibility checkpoint.
Report 59 advances Theorem 1.11 at `e0ef033`: all 48 publisher Table 1
coordinate rows, printed discriminants, positive-definiteness certificates,
and last-column entries are now concrete. The 21 retained rows are identified
with the existing Table 2 selection. Oh-catalogue exhaustion and the actual
prime-by-prime local `2`-ADC calculations remain explicit external inputs.
Report 61 transcribes the 16 parity/column/square-class block formulas in the
non-dyadic Lemma 4.7(i) table at `ec135d8`. Their total ranks, `J_0` and `J_1`
ranks, `J_{0,1}=N` table arithmetic, the missing binary row, and the seven-row
count are concrete. Actual local-field realization, classification,
minimality, the concrete cited-theorem instance behind representation, and the
remaining non-dyadic Section 4 results remain open.
Report 62 makes the common table domain exact at rank one as well as rank two.
Report 63 proves the complete finite rank-four table split used by non-dyadic
Proposition 4.16 and derives that proposition from explicit catalogue and
realization laws. Those law instances, rather than the finite case split, are
the remaining boundary.
Report 64 gives Lemma 4.7(ii) its literal defined-row family, proves the
four/seven/eight cardinalities, and derives testing sufficiency plus deletion
minimality from explicit maximal-overlattice and deletion-witness laws.
Report 65 adds literal non-dyadic endpoints for Lemma 4.14 and Proposition
4.15. The latter is now derived from maximal-lattice existence and same-rank
maximality transfer, rather than stored as a conclusion in `CatalogueLaws`.
Concrete instances of these lower-level local-lattice laws remain open.
Report 66 adds the complete Lemma 4.8 representation biconditional for every
defined Table 4.7 row. Its finite Jordan assertion is internal, while the
general O'Meara 1958 representation theorem remains an explicit interface
requiring a concrete non-dyadic instance.
Report 67 completes both parts of Lemma 4.6 after restricting to the dyadic
context. All parity, column, and corank-one/corank-two alternatives now end in
actual lattice representation. The unrestricted non-dyadic specialization
and independent semantic approval remain open.
Report 68 supplies the complete non-dyadic Lemma 4.6 deduction over an
explicit lower-level law package. Lemma 4.5(i), Proposition 4.2(iii),
determinant-square-class equality, and representation transport remain visible
inputs; no actual Lemma 4.6 conclusion is a field. A concrete non-dyadic
local-field instance of those laws remains open.
Report 70 derives both directions of non-dyadic Lemma 4.5 from determinant,
Hasse, and codimension criteria. Report 71 then derives Proposition 4.2(ii)--
(iii) and all three parts of Lemma 4.4 from a lower invariant interface. The
target-pair and unique-excluding-space fields formerly used by Lemma 4.6 have
been removed. A concrete non-dyadic local-field instance remains open.
Report 72 derives Remark 4.3's maximal-row exhaustion from Proposition
4.2(ii) and maximal-lattice uniqueness, and derives row irredundancy from
Lemma 4.4(i). Neither conclusion remains a `CatalogueLaws` field.

Current concrete coverage includes the dyadic definition and maximal-testing
reduction, the stable-rank local equivalence, the full number-field version
of Lemma 2.2, Section 3 endpoints, and the
Section 4 endpoints, Theorem 6.1, Lemmas 6.4--6.7, Lemma 6.8(i),(ii),(iii),(v),(vi),
the n>=4 part of (iv), the refutation of its printed n=2 boundary, and full
Lemmas 6.9--6.12, the boundary-complete audit of Theorem 6.2, Remark 6.3,
Theorem 7.1, Theorem 7.4, complete Lemmas 7.5--7.12, full Lemmas 7.14--7.15,
Definition 7.16, Remark 7.17, full Lemmas 7.18--7.20, and the corrected
Lemma 7.13 consequence, together with complete Theorem 7.2 and Remark 7.3,
and the Corollary 7.21 catalogue and unconditional numerical wrapper, listed in
`05_theorem_correspondence.md`. The dyadic unary table and the rank-one case
of Lemma 4.9(ii), together with every dyadic branch and the conditional
non-dyadic catalogue deduction of Theorem 1.10, are also complete in their
stated scopes. The symbolic non-dyadic Lemma 4.7 table data are concrete,
while its minimal-testing conclusion is conditional on visible local-lattice
laws. The Section 5 and Section 8 deductions are
also proved over explicit law packages. The global predicates and logical
reductions are in scope, with their non-dyadic and arithmetic premises still
undischarged. This audit does not certify those concrete instances or the
remaining local classifications and concrete external enumeration inputs.
The literal Table 1 matrix data and non-dyadic Table 4.7 block/rank data are no
longer among those remaining inputs; their actual lattice classifications and
representation consequences are.
