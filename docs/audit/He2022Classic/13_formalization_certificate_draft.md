# Partial formalization certificate draft

Paper: Zilong He, *On classic n-universal quadratic forms over dyadic local
fields*, manuscripta math. 174 (2024), 559-595, DOI
10.1007/s00229-023-01516-0. Authority: the publisher PDF identified in
`00_audit_scope.md`; the later arXiv revision is comparison-only.

Code checkpoint: `31873263c5390f1df802cf9b25d125ee65f79d07`.
Proof assistant: Lean 4.32.1. Dependencies: the committed Lake manifest.
Date: 2026-09-05. Project grade: C.

Theorem 1.1 has a checked proof and provisional semantic correspondence.
Theorem 1.3 is partial. Theorem 1.5 has only a local n >= 2 specialization.
Theorems 1.7-1.9 are not covered by complete published endpoints. The even
Lemma 7.4 result and the refutation of literal Lemma 7.1(ii) are separate
checked declarations, not a certificate for the full testing theorem.

Foundational axioms expected by the audit are propositional extensionality,
classical choice, and quotient soundness. Arithmetic interfaces and all
additional premises remain disclosed in reports 03 and 07. No source result
is assumed to bypass the recorded obstruction.

Reproducibility: `PARTIALLY_REPRODUCIBLE` at this checkpoint, pending its
exact-commit clean-kit verification. Author approval: not provided. Domain
expert approval: not provided. Independent human formalization-expert
approval: not provided. No theorem is marked `VERIFIED_MATCH` here.

This draft applies only to the explicitly delimited results above. It is not
a certificate of the entire paper, bibliographic accuracy, novelty, or
unformalized prose. Whole-paper completion remains `NOT_COMPLETE`.
