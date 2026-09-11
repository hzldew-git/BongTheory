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
Full Lemmas 6.9--6.11 checkpoint:
`382ef7ab3014e08834342ae8b806b15b33aaabb8`. Report 33 source-first audits
the terminal dichotomy, the four-condition exceptional-lattice
classification, and the arbitrary-lattice maximal-or-exceptional theorem.
Ten new axiom reports are standard-only and the focused gate checks 57,918
declarations.
Theorem 6.2 and Remark 6.3 checkpoint:
`70580bbd2b4386bec53f046b54a96e3dd69bcaae`. Report 34 proves the complete
`n>=4` restriction of Theorem 6.2, formally refutes its exact published `n=2`
biconditional, and proves the actual integral isometry in Remark 6.3. Eight
new axiom reports are standard-only, the focused gate checks 57,933
declarations, and the scanner checks 2,711 tracked Lean sources.
Theorem 7.1 corrected-proof checkpoint:
`c3e6092f05a0f3b2872fefbd21554cc5461104ce`. Report 35 proves a corrected
complete three-way binary classification, proves that the omitted second
boundary is not 3-ADC, and uses those results to prove the exact published
Theorem 7.1 for every odd `n>=3`. The publisher theorem statement is a
provisional match, while its printed proof is classified `INCOMPLETE_PROOF`.
Seven new axiom reports are standard-only, the focused gate checks 58,019
declarations, and the scanner checks 2,715 tracked Lean sources.
Theorem 7.4 and Lemma 7.5 checkpoint:
`2417a4f31e4a9f96e22c4da6d2276e2e94210fdd`. Report 36 proves Theorem 7.4
and the complete Lemmas 7.5--7.10 and 7.12 chain. Lemma 7.13
has a printed quantifier mismatch; the proof-supported disjunction is
formalized and suffices for Lemma 7.5. Nine selected axiom reports are
standard-only, and the focused gate checks 59,190 declarations.
Complete Lemma 7.11 checkpoint:
`832d10c95f56dd3ae80fc4f912de248f25316da1`. Report 37 proves both
normalized parameter rows and the combined all-parameter endpoint. The two
new dependency reports are standard-only, the focused gate checks 59,204
declarations, and the scanner checks 2,727 tracked Lean sources.
Lemma 7.14 checkpoint:
`6c528031d27cc050a1f10c2ec953500f9b4c3c2c`. Report 38 proves both
published parameter rows in both ambient columns. The two public endpoint
reports are standard-only, the focused gate checks 59,218 declarations, and
the scanner checks 2,728 tracked Lean sources.
Lemma 7.15 checkpoint:
`06d25079c6dac69bc0439b94e694fa52c81961ed`. Report 39 proves the complete
integral-isometry biconditional, including all four concrete Beli conditions
and the maximal-lattice branch. Six selected dependency reports are
standard-only, the focused gate checks 59,348 declarations, and the scanner
checks 2,729 tracked Lean sources.
Definition 7.16 through Lemma 7.19 checkpoint:
`7b21fe0e07e97ba082dd9e78a79e3ec8091630af`. Reports 40--42 prove the exact
conditional class symbol, uniqueness and exhaustion, the second-column
endpoint exclusion, and both literal named-product constructions. Eleven
selected dependency reports are standard-only, the focused gate checks
59,555 declarations, and the scanner checks 2,735 tracked Lean sources.
Lemma 7.20 checkpoint:
`b86a9d4cca78d1f016b1d550fc586df3b90bd8d4`. Report 43 proves the exact
definedness biconditional, all maximal endpoints, all four Hilbert-symbol
column combinations, both named products, and the integral-isometry
conclusions. Eleven selected dependency reports are standard-only, the
focused gate checks 59,643 declarations, and the scanner checks 2,738 tracked
Lean sources.
Theorem 7.2 checkpoint:
`07cd54844a61931cb8b7b6e0ec237448e94b074c`. Report 44 proves the intrinsic
and literal finite maximal-or-product biconditionals, the integral-isometry
normalization of both displayed parameters, and the published maximal-overlap
assertion. Six selected dependency reports are standard-only, the focused
gate checks 59,692 declarations, and the scanner checks 2,740 tracked Lean
sources.
Remark 7.3 checkpoint:
`287b202cfd78c97efe00761798c6914d9715e151`. Report 45 proves all three
literal integral-isometry formulas, including the exact defect exponent,
negative uniformizer powers, sharp factor, half-scaled `A` normalization,
ordered ternary tail, and exact finite representative specialization. Eight
selected dependency reports are standard-only, the focused gate checks
59,743 declarations, and the scanner checks 2,741 tracked Lean sources.
Corollary 7.21 checkpoint:
`bd0c9a3f66d3465cd518bae2d75386887f79d5a5`. Report 46 proves a complete
and irredundant integral-isometry catalogue, the exact maximal/nonmaximal
partition, and the intermediate cardinalities in terms of `|U|`. The printed
residue-norm formulas retained the cited O'Meara 63:9 identity as an explicit
premise at this checkpoint. Seven selected dependency reports are standard-only, the focused
gate checks 59,853 declarations, and the scanner checks 2,742 tracked Lean
sources.
Sections 5 and 8 logical checkpoint:
`d447cd3af10de9ff176df7f9bb48594d72fc4e44`. Report 47 proves every
numbered deduction in those sections, together with Theorems 1.5 and 1.7,
relative to explicit non-dyadic and number-field law packages. Selected
endpoint reports are standard-only; concrete instances of those packages
remain pending.
Binary main-theorem checkpoint:
`f7e8fb7e1b8d43b66a62e500f61f7eeba004f136`. Report 48 proves an exact
complete and irredundant rank-four 2-ADC catalogue with two nonmaximal
classes, formally refutes the printed binary Theorem 1.9(ii) and Theorem
1.10 count, and proves the corrected `8(N p)^e+2` formula relative to the
then-visible O'Meara 63:9 law. Selected dependency reports are standard-only.
Unary table checkpoint:
`da6fbd41a4dc0323380b1013283bd20f9fa6b729`. Report 50 proves the finite
rank-one table's completeness and irredundancy, Proposition 4.2(iii)'s exact
excluding ternary space, literal deletion-minimality in Lemma 4.9(ii), and
the unconditional `2|U|` count. The printed `4(N p)^e` form retains the
O'Meara premise at this checkpoint. Six selected reports are standard-only and the focused gate
checks 60,154 declarations.
Dyadic Theorem 1.10 checkpoint:
`125dcf24f39f0b22a5f69fb33241885169314c06`. Report 51 proves exact
integral-isometry catalogues for every dyadic rank and parity branch and
packages them in `heADC2025Theorem110DyadicCorrected`. The binary
corank-two catalogue retains the formal source refutation and corrected
`8(N p)^e+2` value. The generic proof of the cited counting law is supplied
by the later checkpoint below.
Non-dyadic Theorem 1.10 logical checkpoint:
`d4c56cc`. Report 52 proves exact seven- and eight-row catalogues for equal
rank and both coranks and the printed formulas at ramification index zero.
This is conditional on the visible `SectionFiveLaws` and `CatalogueLaws`
parameters; their concrete non-dyadic instances remain pending.
Non-dyadic Lemma 4.7 table-profile checkpoint:
`ec135d8bdaedb35bf3f29b0518661e23f2251ccf`. Report 61 transcribes all
16 even/odd symbolic block rows and proves their total rank, `J_0` and `J_1`
ranks, table-level `J_{0,1}=N`, parity-specific definedness, and seven-row
binary boundary. At that checkpoint, actual local-lattice realization,
classification, minimality, and Lemma 4.8's representation equivalence were
pending; Report 66 later derives the complete biconditional from the generic
O'Meara 1958 Theorem 1 interface, whose concrete non-dyadic instance remains
pending.
Low-rank and quaternary refinements: `ef4fcf4` and `2cf9133`. Reports 62--63
make the unary/binary table domain exact, prove the exceptional rank-four row
as `A perp A(pi)`, prove that every other row contains `H`, and derive the
non-dyadic Proposition 4.16 conclusion from explicit actual-lattice
realization and transport laws. Concrete instances of those laws remain
pending.
Non-dyadic minimal-testing checkpoint: `5b2c411`. Report 64 gives the exact
defined-row subtype and its four/seven/eight cardinalities, then proves
universality-testing sufficiency and literal deletion minimality from visible
maximal-overlattice, catalogue, transport, and deletion-witness laws. Their
concrete local-lattice instances remain pending.
Non-dyadic Lemma 4.14 and Proposition 4.15 checkpoint: `66c6e66`. Report 65
retains both published rank ranges and derives Proposition 4.15 from
lower-level maximal-lattice existence and same-rank representation transfer;
the final proposition is not a law-package field. Concrete local-field
instances and human review remain pending.
Non-dyadic Lemma 4.8 checkpoint: `7fbb6b9`. Report 66 exports the literal
defined-row Jordan assertion and full representation biconditional. The
latter is derived from the generic O'Meara 1958 Theorem 1 interface; a
concrete non-dyadic instance and human review remain pending.
Corollary 1.8 and Theorem 1.11 logical checkpoint:
`8cdd338f064934f9e3dc1f2af2011cb998705b97`. Report 53 proves the
`115+471=586` deduction, the literal 21-row Table 2 source selection and its
nonrepetition, and every conclusion of Theorem 1.11 from visible external
enumeration and local-verification inputs. The Hanke--Kirschmer--Oh catalogue
instances and local computations remain pending.
Publisher Table 1 matrix checkpoint:
`e0ef0330a8eaa85c74dfa9b91cc706ce3c81efad`. Report 59 transcribes
all 48 matrices and checks their symmetry, printed discriminants, exact
rational positive definiteness, literal bad-prime column, and 21 `None` rows.
It proves that those rows are the Table 2 selection. Oh-catalogue exhaustion,
global-lattice identification, and the actual local calculations remain
pending, so the Theorem 1.11 certificate remains conditional.
Lemma 2.2 algebraic checkpoint:
`04b721092c911d94932d871ec21815a5286da3d6`. Report 55 proves the
complete dimension induction and literal descended-subspace conclusion from
the explicit one-dimensional premise.
Lemma 2.2 concrete finite-completion checkpoint:
`83cc791bf7b2ae80c6d812da7f26f562bf40c859`. Report 56 proves density,
nonzero square-class openness, and the exact one-dimensional descent premise,
then combines them with the algebraic checkpoint to obtain the publisher's
literal subspace conclusion for every number field and finite place.
O'Meara 63:9 checkpoint:
`4ad37e1`. Report 57 proves the intrinsic unit square-class cardinality from
the principal-unit filtration and transports it to every finite complete and
irredundant representative system. All downstream dyadic numerical endpoints
are unconditional. The focused gate checks 60,573 declarations, and the
scanner checks 2,769 tracked Lean sources.
Toolchain: Lean 4.32.1; dependency revisions are in `lake-manifest.json`.
The listed concrete dyadic endpoints pass incremental kernel checks. The
new maximal-profile criteria, thirteen published-family endpoints, complete
Proposition 4.13, both dyadic clauses of Proposition 4.16, all four clauses of
Lemma 6.4, both clauses of Lemmas 6.5--6.7, full Theorem 6.1, and volume criterion depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

The audited declaration groups and scope limitations are in
`05_theorem_correspondence.md`. Semantic matches remain provisional. In
particular, explicit arithmetic premises in the global reductions are not
proved by their axiom reports. No statement here certifies the uninstantiated
external classifications, local computations, or omitted boundary cases.

Independent author approval: pending. Independent domain-expert approval:
pending. Independent formalization-expert approval: pending. Reproducibility:
the f6f7485/c82668b tree passed clean-kit CI with enforced dependencies
through full Lemma 6.7. The later exact locally extracted kit at 26dc391
covers the developments through Report 53 and passes its `5,051`-job full
build, all direct audits, and the `60,374`-declaration enforcing
gate. It includes the unary, Theorem 1.10, and finite-enumeration checkpoints.
Exact commit distinctions are in reports 11 and 54.
The still later exact clean kit at `7d7a4d5` supersedes that local receipt for
the current source closure: it includes Lemma 2.2 and O'Meara 63:9, verifies
2,060 payload hashes, completes 5,560 build jobs, and passes all direct audits
plus the 60,594-declaration enforcing gate. Exact dependency-transport and
build details are in Reports 11 and 58.
The exact clean kit at `8ead7f4` advances that evidence through the publisher
Table 1 certificate. It verifies 2,064 payload hashes, completes all 5,569
fresh-extraction build jobs, passes the canonical audit, both concrete `Q_2`
audits, and the 60,683-declaration enforcing gate, and independently reruns
the Mathematica matrix certificate. It predates Reports 61--68; details are
in Reports 11 and 60.
The later Lemma 4.6 checkpoint `bc043fe` completes all eight dyadic
actual-lattice branches. Its focused audit reports only the standard axioms,
the combined canonical build completes 5,560 jobs, and the source scanner
checks 2,780 files. Report 67 records its statement bridge and explains why
this local build is not a clean-kit receipt.
The non-dyadic Lemma 4.6 checkpoint `b335b1f` derives both published parts
and the maximal-lattice corollary over explicit lower-level laws. Its focused
audit completes 3,001 jobs and its combined build completes 5,561 jobs. The
concrete non-dyadic instance remains outside this draft certificate; see
Report 68.
The non-dyadic Lemma 4.5 checkpoint
`b2dba36476d6dea37762bc6b1b00b7d952aafa62` supersedes the Lemma 4.5 input
boundary in that checkpoint. Both directions and both table-specific clauses
are proved from determinant/Hasse classification and codimension-one/two
criteria, and Lemma 4.6 now invokes that proof. The six new endpoints use only
standard axioms; the concrete invariant package remains outside this draft
certificate. See Report 70.
The non-dyadic Proposition 4.2/Lemma 4.4 checkpoint
`bdc8c2993efc716f9b4edd5d4c4617229fb4e9f4` derives the full space-table
exhaustion, all three representation biconditionals, the all-other-spaces
property, failure on the named exception, and uniqueness of the excluding
space. Lemma 4.6 now reuses these proofs. The focused audit completes 3,001
jobs and the combined build 5,564; the concrete invariant instance and a clean
kit remain outside this draft certificate. See Report 71.
Non-dyadic Remark 4.3 catalogue checkpoint:
`5194689170d3287eff67d442d62b3b5ff526cd89`. Report 72 derives maximal-row
exhaustion from Proposition 4.2(ii), target maximality, and maximal-lattice
uniqueness, and derives row irredundancy from Lemma 4.4(i) and ambient-isometry
transport. Neither conclusion remains a `CatalogueLaws` field. The lower
invariant and lattice-level interfaces, clean-kit evidence, and human review
remain outside this draft certificate.
Overall project grade: D because one
omitted binary class causes substantive mismatches in four printed claims,
with a separate quantifier mismatch in Lemma 7.13. Whole-paper
completion: not achieved.
