# He--Hu and He ADC deployment roadmap

This public roadmap governs the deployment of two published papers:

1. Zilong He and Yong Hu, *On n-universal quadratic forms over dyadic local
   fields*, Sci. China Math. 67 (2024), 1481--1506.
2. Zilong He, *On n-ADC integral quadratic lattices over algebraic number
   fields*, Doc. Math. 30 (2025), no. 4, 981--1022.

The He classic formalization is maintained outside this deployment branch and
will not be uploaded as a GitHub Review Kit or Release asset until the user
authorizes a later deployment.

The publisher version of record is the sole semantic authority for every
definition, hypothesis, and theorem. The paper manifests record exact hashes;
arXiv copies are non-authoritative comparison sources.

The exact independently extracted He ADC Review Kit at `26dc391` passes all
5,051 build jobs, its canonical audit, both concrete `Q_2` audits, and the
60,374-declaration enforcing gate. It covers the developments through Report
53. Rows below retain the first implementation checkpoint, so an older row's
"own clean CI pending" note describes that historical checkpoint, not the
current aggregate kit. GitHub exact-tag CI, release publication, remaining
mathematical work, and human semantic sign-off are separate gates.

## Current milestone

| Work package | Current endpoint | State |
|---|---|---|
| Shared representation API | inclusion representations and maximal extensions | proved |
| He--Hu Theorem 1.1 | complete published equivalence | proved; provisional semantic review |
| He--Hu Theorem 1.2 | literal finite normalized-unit table, counts, and deletion-minimality | proved; human review pending |
| He ADC Definition 1.1(ii) | local dyadic predicate | formalized |
| He ADC Lemma 2.1 | local dyadic maximal-testing reduction | proved specialization |
| He ADC Lemmas 4.11-4.12 | public W/N families and all maximal order-profile branches | proved; independent AI review completed, human review pending |
| He ADC Proposition 4.13 | all three clauses for arbitrary odd-rank maximal lattices | local/independent checks and clean-kit CI at f6f7485/c82668b pass; human approval pending |
| He ADC Proposition 4.16 | both dyadic clauses, with the exact integral exceptional model | dyadic checks, AI review and clean-kit CI at f6f7485/c82668b pass; non-dyadic part remains |
| He ADC Lemma 6.4 | all four even-rank testing clauses on the actual named lattices | local/independent checks and clean-kit CI at f6f7485/c82668b pass; report 17; release promotion pending |
| He ADC Lemma 6.5 | both exact pointwise defect obstructions, including n=2 | local/independent checks and clean-kit CI at f6f7485/c82668b pass; report 18; release promotion pending |
| He ADC Theorem 6.1 | full equivalence: even n >= 2, rank n+1, ADC iff maximal | local/independent checks and clean-kit CI at f6f7485/c82668b pass; report 19; human approval pending |
| He ADC Lemma 6.6 | both exact central-condition failures on the actual named targets | local/independent checks and clean-kit CI at f6f7485/c82668b pass; report 21; human approval pending |
| He ADC Lemma 6.7 | both actual-representation implications, with alpha alternatives and raw/capped defect equality | local/independent checks and clean-kit CI at f6f7485/c82668b pass; report 22; human approval pending |
| He ADC Lemma 6.8(i)--(ii) | first-column endpoint isometries on arbitrary n-ADC lattices; exact n=2/n>=4 boundaries | only 2/6 clauses, locally proved and independently AI-reviewed at b624d40; report 23; its own clean CI pending |
| He ADC Lemma 6.8(v)--(vi) | nonexceptional columns, original-parameter lattice isometries and explicit printed-domain bridge | locally proved and independently AI-reviewed at b728bce; Delta-in-U convention disclosed; report 24; whole lemma now 4/6, own clean CI pending |
| He ADC Lemma 6.8(iii)--(iv) | actual second-column isometries: full (iii), n>=4 of (iv), and an actual nonmaximal 2-ADC counterexample at its printed n=2 boundary | n>=4 result passes at 074f2cd; binary implication is `SEMANTIC_MISMATCH` and formally refuted through fe2a459; reports 25--31; exact-revision clean CI pending |
| He ADC Lemma 6.12 | exceptional quaternary lattice in `W_1^4(Delta)` is 2-ADC, not 3-ADC, and nonmaximal | full local proof and source-first audit at cf9f83b; report 32; exact-revision clean CI and human sign-off pending |
| He ADC Theorem 7.1 | exact odd `n>=3`, rank `n+1` equivalence; corrected three-way binary classification and both nonmaximal 3-ADC exclusions | full local proof at c3e6092; statement `PROVISIONAL_MATCH`, publisher proof `INCOMPLETE_PROOF`; report 35; exact-revision clean CI and human sign-off pending |
| He ADC Theorem 7.4 and Lemmas 7.5--7.14 | complete odd-corank-two BONG criterion and its order, alpha, defect, representation and determinant-parity chain | full local proof in the audited scopes through 6c52803; Lemma 7.13 has a disclosed quantifier mismatch; reports 36--38; exact-revision clean CI pending |
| He ADC Lemma 7.15 | integral isometry iff ambient-space isometry and equality of `R_(n+1)` | full local proof at 06d2507, including both maximal and four-condition nonmaximal branches; report 39; exact-revision clean CI pending |
| He ADC Definition 7.16 and Remark 7.17 | conditional `M_(nu,r)` class symbol, uniqueness, and exhaustion | full local proof at 7b21fe0; report 40; exact-revision clean CI pending |
| He ADC Lemma 7.18 | second-column unit endpoint `r=e` is excluded | full local proof at 7b21fe0 on the actual named maximal model; report 41; exact-revision clean CI pending |
| He ADC Lemma 7.19 | both named products `N_nu^(n+1)(delta) orthogonal-sum <c>` are n-ADC with `R_(n+1)=1-d(delta)` | full local construction and integral-isometry bridge at 7b21fe0; report 42; exact-revision clean CI pending |
| He ADC Lemma 7.20 | maximal endpoints, the unique undefined triple, and both Hilbert-selected named products | full local classification at b86a9d4; report 43; exact-revision clean CI pending |
| He ADC Theorem 7.2, Remark 7.3, Corollary 7.21 | full odd rank-`n+2` classification, literal models, exact catalogue and counts | local proofs through bd0c9a3; numerical Corollary 7.21 uses explicit O'Meara 63:9 premise; reports 44--46; clean CI pending |
| He ADC Section 5 | Theorem 5.1 and Lemmas 5.2--5.4 | all numbered deductions proved at d447cd3 from explicit non-dyadic laws; concrete instance pending; report 47 |
| He ADC Section 8 and global main logic | Lemma 8.1 through Corollary 8.5, Theorems 1.5 and 1.7 | all deductions proved at d447cd3 from explicit arithmetic laws; concrete number-field instances pending; report 47 |
| He ADC binary main theorems | exact six-family catalogue and corrected Theorems 1.9(ii), 1.10 | printed binary classification and `+1` count refuted; corrected `+2` count proved at f7e8fb7; report 48; clean CI pending |

The current milestone is not whole-project completion. In ADC, one independently
audited `n=2` counterexample affects Lemma 6.8(iv), Theorem 6.2, Theorem
1.9(ii), and Theorem 1.10. Theorem 7.1 has a repaired proof, and the binary
classification/count now has an exact corrected catalogue. Concrete
non-dyadic and number-field law instances, remaining classifications, and
  enumeration remain active proof work. GitHub-hosted exact-tag CI and release
  publication are separate gates from local kernel acceptance.

## Proof order

1. Preserve the checked He--Hu proof chain and finish its independent-review
   and exact-release-commit reproducibility gates.
2. Instantiate the ADC Section 5 non-dyadic laws and Section 8 number-field
   laws, then complete Lemma 2.2, the remaining Section 4/unary results,
   cited unit-square-class counting, and enumeration. Conditional law packages
   record the source logic but are not substitutes for their arithmetic
   hypotheses.

## Gate for every promoted theorem

A theorem may move from `STATEMENT_ONLY_UNPROVED` to a proved status only when:

- the Lean declaration has no `sorry`, project axiom, or opaque proof;
- its transitive axiom report contains only the declared foundational axioms;
- its hypotheses, quantifiers, indices, exceptional cases, and conclusion have
  been compared line by line with the publisher version;
- the paper-specific Review Kit builds after clean extraction; and
- the audit package records remaining exclusions and independent-review status.

Compilation proves kernel acceptance of the formal statement; it is never
reported as independent confirmation that the transcription matches the paper.

## Distribution rule

Each paper retains its own canonical entry module, audit module, schema-2
manifest, fidelity directory, and source-only Review Kit. New BONG-related
papers must follow the same metadata-driven workflow described in
`papers/SCHEMA.md`, so reviewers can download and verify one paper without
obtaining the full repository history or unrelated milestone tests.
