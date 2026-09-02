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
| He--Hu Theorem 1.1 | complete proposition and condition layer | statement only |
| He--Hu Theorem 1.2 | abstract maximal-testing reduction | proved core; explicit list pending |
| He classic Theorem 1.1 | complete proposition and condition layer | statement only |
| He classic Theorem 1.3 | abstract classic-maximal testing reduction | proved core; explicit list pending |
| He ADC Definition 1.1(ii) | local dyadic predicate | formalized |
| He ADC Lemma 2.1 | local dyadic maximal-testing reduction | proved specialization |

## Proof order

1. Complete the He--Hu local proof chain in publisher order: representation
   criterion bridges, even branch, odd branch, exceptional quaternary case,
   and then Theorem 1.1. Formalize the explicit maximal lattices and minimality
   in Theorem 1.2 only after the classification equivalence is kernel checked.
2. Reuse the verified He--Hu/Beli bridges for the classic paper, while keeping
   scale integrality separate from norm integrality. Prove the even and odd
   branches of Theorem 1.1 before formalizing the explicit minimal testing sets
   of Theorem 1.3 and the global consequences.
3. Extend the ADC layer from the proved local Lemma 2.1 to localization,
   global `n`-ADC, and `n`-regularity. Then follow the publisher dependency
   order through Theorems 1.3--1.11; do not import a local classification as a
   substitute for proving its stated hypotheses.

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
