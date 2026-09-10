# Audit scope

The sole semantic authority is the author-corrected v5 TeX manuscript
`classic_dyadic-n-uni-v5.tex`, SHA-256
`C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
The 2024 publisher version of record and the 2025 arXiv v3 revision are
comparison-only. The source files are author-held and are not redistributed.

Working-tree checkpoint: branch `release/heclassic-v0.5.0-rc.1-prep`, updated
on 2026-09-11 with Lean 4.32.1 and the repository's pinned
`lake-manifest.json`. An exact clean release commit remains pending.

The checkpoint includes the proved Theorem 1.1 equivalence, local Section 2-6
proof chains, the complete n >= 1 local-field implication underlying Theorem
1.5, corrected v5 Lemma 7.1, both testing equivalences in Lemma 7.4, and both
literal-minimality branches of Theorem 1.3. It does not complete the
concrete number-field localization, finite-extension, discriminant, and
strong-approximation inputs. The final global deduction of Theorem 1.5,
Lemma 8.1, Proposition 8.2, Theorems 1.7 and 1.9, and the even-rank parts of
Lemma 8.3 and Theorem 1.8 are checked only conditionally over the explicit
proof-data packages documented in Reports 23, 27, and 28.
Report 27 strengthens this boundary: Proposition 8.2 itself is now derived
from positive-definite globalization, localization, and representation
transport laws rather than stored as a final-conclusion field.
Report 29 likewise derives the local-to-global half of Theorem 1.9 from
integrality, localization, and an explicit strong-approximation representation
law rather than storing global universality as a field.
The unrestricted odd branch of Corollary 6.3 is false: the repository now
contains a kernel-checked `e=2`, `n=3` counterexample. The same unsupported
step reaches Lemma 8.3 and Theorem 1.8. See Reports 24 and 26.
Report 28 removes the unrestricted formal endpoints and retains only the
conditional `n >= 2`, even-rank parts of Lemma 8.3 and Theorem 1.8.

`SOURCE_DELTA.md` records every comparison-source discrepancy. In particular,
the obsolete broader publisher Lemma 7.1(ii) has a checked refutation for
`e>1`; the v5 replacement is proved separately and does not assert it.

This refresh supersedes the earlier statement-only progress descriptions. It
is not a fresh item-by-item semantic certificate for all 66 numbered items.
Independent human approvals and clean-build evidence at the final release
commit remain required. Overall status: partial coverage with a refuted
source statement, Grade D.
