# Partial formalization certificate draft

Paper: Zilong He, *On classic n-universal quadratic forms over dyadic local
fields*, manuscripta math. 174 (2024), 559-595, DOI
10.1007/s00229-023-01516-0. Authority: the author-corrected v5 TeX identified
in `00_audit_scope.md`; the publisher PDF and later arXiv revision are
comparison-only.

Code checkpoint: current local v5 working tree on `feat/he-formalization`;
exact clean release commit pending. Proof assistant: Lean 4.32.1.
Dependencies: the committed Lake manifest. Date: 2026-09-09. Project grade: C.

Theorem 1.1 has a checked proof and provisional semantic correspondence.
Theorem 1.3 is checked in both parity branches, including literal minimality.
Theorem 1.5 has its complete local n >= 1 implication,
and its final global deduction is conditionally checked over explicit
number-field laws. Theorems 1.7-1.9 and all numbered Section 8 deductions have
conditional endpoints; their concrete arithmetic instances are not supplied.
Corollary 6.3 is checked only for even `n`; v5 supplies no reduction for its
odd branch, and Lemma 8.3/Theorem 1.8 inherit this source boundary (Report 24).
The even Lemma 7.4 result,
Lemma 7.7, all three clauses of Lemma 7.10, the even literal-minimal endpoint,
the corrected v5 Lemma 7.1, both testing equivalences, both literal-minimal
endpoints, and the regression refuting the obsolete publisher Lemma 7.1(ii)
are checked declarations.

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
