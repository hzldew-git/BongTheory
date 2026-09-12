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
concrete number-field localization, finite-extension, and
strong-approximation inputs. The final global deduction of Theorem 1.5,
Lemma 8.1, Proposition 8.2, Theorem 1.9, and the even-rank parts of Lemma 8.3,
Theorem 1.7, and Theorem 1.8 are checked only conditionally over the explicit
proof-data packages documented in Reports 23, 27, 28, and 33.
Report 27 strengthens this boundary: Proposition 8.2 itself is now derived
from positive-definite globalization, localization, and representation
transport laws rather than stored as a final-conclusion field.
Report 29 likewise derives the local-to-global half of Theorem 1.9 from
integrality, localization, and an explicit strong-approximation representation
law rather than storing global universality as a field.
Report 30 replaces a full discriminant/ramification biconditional by the
necessity-side direction and derives the ramified dyadic-place witness required
by Theorem 1.7.  Report 31 records that the converse direction, previously
hidden inside an all-places field, is required by Theorem 1.9's unary
sufficiency branch and exposes it there separately.
Report 31 replaces the all-places local-universality premise in Theorem 1.9 by
the three finite-place branches actually used in v5 and derives their
quantified conclusion in Lean.
Report 32 proves the discriminant--ramification equivalence for actual prime
ideals of a number field, including both directed uses, the ramified-prime
witness, and positivity. A structural place-to-prime-ideal bridge now
constructs the formerly abstract discriminant fields; that bridge remains to
be instantiated as part of the concrete global lattice model.
Report 34 lowers this interface further: an equivalence with the standard
height-one spectrum now proves prime-ideal primality and dyadic-prime coverage
automatically. Report 36 supplies canonical number-field global data whose
dyadic predicate, ramification index, and discriminant proposition are defined
from that spectrum, so all three compatibility statements are definitional.
The concrete global lattice model and its place equivalence remain open.
The unrestricted odd branch of Corollary 6.3 is false: the repository now
contains a kernel-checked `e=2`, `n=3` counterexample. The same unsupported
step reaches Lemma 8.3 and Theorem 1.8. See Reports 24 and 26.
Report 28 removes the unrestricted formal endpoints and retains only the
conditional `n >= 2`, even-rank parts of Lemma 8.3 and Theorem 1.8.
Report 33 applies the same safeguard to Theorem 1.7. It retains a source-facing
`n >= 2`, even-rank endpoint and separately proves the parity-independent
final contradiction with the missing local-defect calculation as an explicit
premise. No unrestricted odd Theorem 1.7 endpoint is exported.

`SOURCE_DELTA.md` records every comparison-source discrepancy. In particular,
the obsolete broader publisher Lemma 7.1(ii) has a checked refutation for
`e>1`; the v5 replacement is proved separately and does not assert it.

This refresh supersedes the earlier statement-only progress descriptions. It
is not a fresh item-by-item semantic certificate for all 66 numbered items.
Independent human approvals and clean-build evidence at the final release
commit remain required. Overall status: partial coverage with a refuted
source statement, Grade D.
