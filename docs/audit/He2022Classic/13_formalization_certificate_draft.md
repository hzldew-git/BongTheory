# Partial formalization certificate draft

Paper: Zilong He, *On classic n-universal quadratic forms over dyadic local
fields*, manuscripta math. 174 (2024), 559-595, DOI
10.1007/s00229-023-01516-0. Authority: the author-corrected v5 TeX identified
in `00_audit_scope.md`; the publisher PDF and later arXiv revision are
comparison-only.

Code checkpoint: `e3b18be95c813885a421b83fe0a0148d6b561ae0` on
`release/heclassic-v0.5.0-rc.1-prep`; packaged audit commit `ab1901a` has the
exact local Review Kit receipt in Report 43, while an exact public release
commit remains pending. Proof assistant: Lean 4.32.1.
Dependencies: the committed Lake manifest. Date: 2026-09-13. Project grade: D.

Theorem 1.1 has a checked proof and provisional semantic correspondence.
Theorem 1.3 is checked in both parity branches, including literal minimality.
Theorem 1.5 has its complete local n >= 1 implication,
and its final global deduction is conditionally checked over explicit
number-field laws. Theorem 1.9 and the even-rank parts of Theorems 1.7 and 1.8
have conditional endpoints; their concrete arithmetic instances are not
supplied. Theorem 1.7's parity-independent final contradiction is separately
proved from an explicit local-defect premise. The unrestricted odd Lemma 8.3,
Theorem 1.7, and Theorem 1.8 endpoints are excluded.
Corollary 6.3 is checked for even `n`, while a kernel-checked `e=2`, `n=3`
counterexample refutes its unrestricted odd statement. Lemma 8.3/Theorem
1.7/Theorem 1.8 therefore require a parity restriction or a replacement odd
proof (Reports 24, 26, 28, and 33).
The even Lemma 7.4 result,
Lemma 7.7, all three clauses of Lemma 7.10, the even literal-minimal endpoint,
the corrected v5 Lemma 7.1, both testing equivalences, both literal-minimal
endpoints, and the regression refuting the obsolete publisher Lemma 7.1(ii)
are checked declarations.

Lemma 8.1(i)--(ii) are proved over actual dyadic local-field structures on the
selected finite completions. Their BONG orders, defects, and ramification
indices are identified with the completion-side invariants. For part (iii),
every actual lower good BONG is sent to a coefficient row realized by an
actual upper integral lattice and good BONG. This is the strongest conclusion
supported by the written v5 proof. The literal claim that these vectors form a
good BONG of the preassigned localized scalar-extension lattice `L_P` remains
unproved: the cited He--Hu Lemma 2.2 concludes only "for some lattice," and v5
provides no carrier-identification lemma. See Report 42.

Foundational axioms expected by the audit are propositional extensionality,
classical choice, and quotient soundness. Arithmetic interfaces and all
additional premises remain disclosed in reports 03 and 07. No source result
is assumed to bypass the recorded obstruction.
The discriminant theorem is concrete, and the height-one-spectrum bridge now
derives primality and dyadic-prime coverage. Canonical number-field global data
makes the arithmetic compatibility statements definitional; the concrete
global lattice model still must supply its place equivalence and lattice laws.

Reproducibility: `FRESH_EXTRACTION_RESUMED_LOCAL_PASS` for packaged commit
`ab1901a`, with the exact receipt in Report 43. GitHub exact-tag CI and release
verification remain pending. Author approval: not provided. Domain expert
approval: not provided. Independent human formalization-expert approval: not
provided. No theorem is marked `VERIFIED_MATCH` here.

This draft applies only to the explicitly delimited results above. The false
odd Corollary 6.3 and the Lemma 8.1(iii) carrier gap prevent a whole-paper
certificate. It is not a certificate of the entire paper, bibliographic
accuracy, novelty, or
unformalized prose. Whole-paper completion remains `NOT_COMPLETE`.
