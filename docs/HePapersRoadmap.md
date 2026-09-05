# He-paper formalization roadmap

This roadmap governs the formalization of three published papers:

1. Zilong He and Yong Hu, *On n-universal quadratic forms over dyadic local
   fields*, Sci. China Math. 67 (2024), 1481--1506.
2. Zilong He, *On classic n-universal quadratic forms over dyadic local
   fields*, manuscripta math. 174 (2024), 559--595.
3. Zilong He, *On n-ADC integral quadratic lattices over algebraic number
   fields*, Doc. Math. 30 (2025), no. 4, 981--1022.

The publisher version of record is the sole semantic authority for every
definition, hypothesis, and theorem. The paper manifests record exact hashes;
arXiv copies are non-authoritative comparison sources.

## Current milestone

| Work package | Current endpoint | State |
|---|---|---|
| Shared representation API | inclusion representations and maximal extensions | proved |
| He--Hu Theorem 1.1 | complete published equivalence | proved; provisional semantic review |
| He--Hu Theorem 1.2 | literal finite normalized-unit table, counts, and deletion-minimality | proved; human review pending |
| He classic Theorem 1.1 | complete local equivalence for n >= 2 | proved; human review pending |
| He classic Theorem 1.3 | literal table and even testing equivalence | partial; odd sufficiency and full minimality/counting remain |
| He classic Theorem 1.5 | local implication for n >= 2 | special case; unary and global clauses remain |
| He ADC Definition 1.1(ii) | local dyadic predicate | formalized |
| He ADC Lemma 2.1 | local dyadic maximal-testing reduction | proved specialization |
| He ADC Lemmas 4.11-4.12 | public W/N families and all maximal order-profile branches | proved; independent AI review completed, human review pending |
| He ADC Proposition 4.13 | all three clauses for arbitrary odd-rank maximal lattices | local kernel and independent AI checks complete; clean-kit CI pending |
| He ADC Proposition 4.16 | both dyadic clauses, with the exact integral exceptional model | dyadic specialization locally checked and AI-reviewed; non-dyadic part and clean-kit CI pending |
| He ADC Lemma 6.4 | all four even-rank testing clauses on the actual named lattices | local kernel checks complete; report 17 records semantic review; clean-kit CI and release promotion pending |
| He ADC Lemma 6.5 | both exact pointwise defect obstructions, including n=2 | local kernel and independent AI checks complete; report 18; clean-kit CI and release promotion pending |
| He ADC Theorem 6.1 | full equivalence: even n >= 2, rank n+1, ADC iff maximal | local kernel and independent AI checks complete; report 19; clean-kit CI and human approval pending |

The current milestone is not whole-project completion. The Classic publisher
Lemma 7.1(ii) has a checked refutation when e > 1; affected statements remain
excluded until an explicit source resolution or separately justified route is
available. ADC even/odd classifications and concrete global consequences
remain active proof work. Exact-commit clean-kit CI and release publication
are separate gates from local kernel acceptance.

## Proof order

1. Preserve the checked He--Hu proof chain and finish its independent-review
   and exact-release-commit reproducibility gates.
2. Complete the remaining Classic testing and global obligations, keeping
   scale integrality distinct from norm integrality and source corrections
   distinct from literal publisher claims. Do not replace a missing odd-rank
   proof with an unproved lower-even condition.
3. Continue ADC through the remaining Section 4 structural results, local
   Sections 5-7 classifications, and the concrete number-field consequences.
   Abstract local-to-global predicates and conditional law packages are not
   substitutes for proving the arithmetic hypotheses in Sections 1 and 8.

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
