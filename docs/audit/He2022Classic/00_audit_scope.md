# Audit scope

The sole semantic authority is the author-corrected v5 TeX manuscript
`classic_dyadic-n-uni-v5.tex`, SHA-256
`C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
The 2024 publisher version of record and the 2025 arXiv v3 revision are
comparison-only. The source files are author-held and are not redistributed.

Working-tree checkpoint: branch `feat/he-formalization`, reviewed on
2026-09-09 with Lean 4.32.1 and the repository's pinned
`lake-manifest.json`. An exact clean release commit remains pending.

The checkpoint includes the proved Theorem 1.1 equivalence, local Section 2-6
proof chains, the complete n >= 1 local-field implication underlying Theorem
1.5, corrected v5 Lemma 7.1, both testing equivalences in Lemma 7.4, and both
literal-minimality branches of Theorem 1.3. It does not complete the
concrete number-field localization, finite-extension, discriminant, and
strong-approximation inputs. The final global deduction of Theorem 1.5,
Lemmas 8.1 and 8.3, Proposition 8.2, and Theorems 1.7--1.9 are checked only
conditionally over the explicit proof-data packages documented in Report 23.
The unrestricted odd branch of Corollary 6.3 is false: the repository now
contains a kernel-checked `e=2`, `n=3` counterexample. The same unsupported
step reaches Lemma 8.3 and Theorem 1.8. See Reports 24 and 26.

`SOURCE_DELTA.md` records every comparison-source discrepancy. In particular,
the obsolete broader publisher Lemma 7.1(ii) has a checked refutation for
`e>1`; the v5 replacement is proved separately and does not assert it.

This refresh supersedes the earlier statement-only progress descriptions. It
is not a fresh item-by-item semantic certificate for all 66 numbered items.
Independent human approvals and clean-build evidence at the final release
commit remain required. Overall status: partial coverage with a refuted
source statement, Grade D.
