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
residue-norm formulas retain the cited O'Meara 63:9 identity as an explicit
premise. Seven selected dependency reports are standard-only, the focused
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
same visible O'Meara 63:9 law. Selected dependency reports are standard-only.
Unary table checkpoint:
`da6fbd41a4dc0323380b1013283bd20f9fa6b729`. Report 50 proves the finite
rank-one table's completeness and irredundancy, Proposition 4.2(iii)'s exact
excluding ternary space, literal deletion-minimality in Lemma 4.9(ii), and
the unconditional `2|U|` count. The printed `4(N p)^e` form retains the
O'Meara premise. Six selected reports are standard-only and the focused gate
checks 60,154 declarations.
Dyadic Theorem 1.10 checkpoint:
`125dcf24f39f0b22a5f69fb33241885169314c06`. Report 51 proves exact
integral-isometry catalogues for every dyadic rank and parity branch and
packages them in `heADC2025Theorem110DyadicCorrected`. The binary
corank-two catalogue retains the formal source refutation and corrected
`8(N p)^e+2` value. The non-dyadic branch and a generic proof of the cited
counting law remain pending.
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
through full Lemma 6.7. The exact locally extracted kit at 85772de covers
the later developments through Reports 47--48 and passes its full build,
audits, and enforcing gate. The unary checkpoint postdates that kit and has
only exact local evidence. Exact commit distinctions are in report 11.
Overall project grade: D because one
omitted binary class causes substantive mismatches in four printed claims,
with a separate quantifier mismatch in Lemma 7.13. Whole-paper
completion: not achieved.
