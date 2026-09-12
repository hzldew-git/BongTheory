# Executive summary

Paper: Zilong He, *On classic n-universal quadratic forms over dyadic local
fields*, manuscripta math. 174 (2024), 559-595. Semantic authority:
author-corrected v5 TeX, SHA-256
`C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
Proof assistant: Lean 4.32.1. Review date: 2026-09-13. Exact clean release
commit: pending.

Theorem 1.1 now has a proof of both directions for n >= 2 and arbitrary source
rank. The local proof chain and even-rank testing equivalence are substantial
advances beyond the earlier statement-only milestone. Theorem 1.5 is proved
in its full local n >= 1 scope, including the separate unary argument; its
concrete number-field localization remains excluded.
The final global deduction, Theorem 1.9, and the even-rank parts of Theorems
1.7 and 1.8 now have kernel-checked conditional endpoints over explicit
Section 8 arithmetic packages. Theorem 1.7's parity-independent final
contradiction is separately proved from an explicit local-defect premise.
Concrete global number-field lattice/localization, orthogonal-basis scalar-
extension identification, and strong-approximation instances remain excluded,
so this is not unconditional global coverage.
Proposition 8.2 is no longer stored as a final arithmetic field: Report 27
derives it from positive-definite globalization, localization, and local
equivalence transport.  Those lower facts still require concrete
number-field implementations.
Report 29 also derives Theorem 1.9's local-to-global step by localizing an
arbitrary global target and invoking an explicit strong-approximation
representation law; global universality itself is no longer a package field.
Report 30 separates the necessity-side discriminant direction and derives the
ramified dyadic-place witness used by Theorem 1.7.  Report 31 exposes the
converse direction at its actual use in Theorem 1.9's unary sufficiency branch.
Report 32 proves both directions, the ramified-prime witness, and positivity
for actual number-field prime ideals and transports them through a typed place
bridge; only that structural identification remains at this step.
Report 34 derives primality and dyadic-prime coverage from an equivalence with
the standard height-one spectrum. Report 36 supplies canonical number-field
global data in which the dyadic predicate, ramification index, and discriminant
proposition are standard definitions and all compatibility is definitional.
A concrete global model still needs the place equivalence at this bridge layer.
Report 38 proves finite-prime order scaling, relative ramification positivity,
and the absolute ramification tower for nonzero coefficients in the underlying
number field. This is the first concrete part of Lemma 8.1(i).
Report 39 constructs the actual continuous finite-dimensional extension
between the two finite completions and proves compatibility with the dense
number-field embedding.
Report 40 proves that remaining equality by continuous extensionality and
deduces the additive order formula on all `K_pˣ`.
Report 41 defines completed relative quadratic defect and proves its
ramification-scaled inequality, then transports the exact He--Hu good-BONG
coefficient criterion under the completed embedding. Report 42 constructs the
actual dyadic local-field structures on both completions, identifies their
BONG orders, defects, and ramification indices with those numerical notions,
and realizes the mapped coefficient row as an actual upper good BONG. Hence
Lemma 8.1(i)--(ii), together with the existence conclusion supported by the
written proof of part (iii), are proved. The literal claim in part (iii) that
the resulting vectors form a good BONG of the preassigned localized scalar-
extension lattice `L_P` remains open: the cited He--Hu Lemma 2.2 produces
"some lattice" and the v5 proof supplies no carrier-identification argument.
Report 31 derives Theorem 1.9's finite-place local-universality conclusion from
the separate non-dyadic, dyadic unary, and dyadic higher-rank laws in v5; the
all-places conclusion is no longer stored as a package field.

Both branches of Theorem 1.3 are complete at the literal table level.
Author-corrected v5 Lemma 7.1, both branches of Lemma 7.4, Lemma 7.7, all
clauses of Lemma 7.10, the finite-index nonisometry bridge, all exceptional
`H` rows, and the unified row-by-row deletion theorems are checked. Lemma 7.11
gives the odd witnesses, and its combined endpoint proves odd literal
minimality.
Every literal model in both tables is also proved classic-maximal: its volume
order is computed as zero or one and the generic volume-index argument rules
out a proper classic integral over-lattice. This strengthens Proposition 2.8
but does not supply a classification of all classic-maximal lattices.
The obsolete broader publisher Lemma 7.1(ii) disjunction has a kernel-checked
refutation when `e>1`; it is retained as a regression theorem and is not used
to prove v5. O'Meara 63:5 and 63:9 and all three numerical counts are
internally proved. `SOURCE_DELTA.md`, Reports 22--36, and Reports 38--42 are part of
the review scope. Reports 24 and 26 record a kernel-checked `e=2`, `n=3` counterexample
to the unrestricted odd statement of Corollary 6.3. Lemma 8.3 and Theorem 1.8
therefore need either an even-rank restriction or a replacement odd proof.
Report 28 applies that restriction in Lean: the remaining Lemma 8.3 and
Theorem 1.8 endpoints require `n >= 2` and even rank, and no unrestricted odd
compatibility theorem remains.
Report 33 applies the same restriction to the source-facing Theorem 1.7
endpoint and preserves only its common logical tail behind an explicit
local-defect premise.

Report 35 records an exact source-only local Review Kit for commit `c1ee018`:
2,010 payload hashes, a resumed fresh-extraction 5,671-job build, all six
Classic audits, the 62,746-declaration enforcing axiom gate, and clean exact
dependency pins all pass. This closes the current local packaging gate, but it
is not GitHub CI or a release and does not alter the semantic verdict.

Project grade: D, because the authoritative v5 source contains a refuted
unrestricted statement, in addition to incomplete global arithmetic coverage.
Theorem 1.1 correspondence remains provisional, not human-approved
`VERIFIED_MATCH`. Trust reports inspect standard logical axioms separately
from arithmetic interfaces and restricted theorem premises. Reproducibility
has historical exact local clean-kit evidence at `c1ee018`; the newer
`e3b18be` code checkpoint and its Report 42 audit update still require a fresh
clean-kit run after the audit documents are committed.
GitHub CI and release evidence remain absent by design.

Safe claim: a checked local classification, full v5 Theorem 1.3 testing
development, and checked conditional Section 8 deductions. Unsafe claim:
complete formalization or final deployment of the whole paper. Next actions
are a v6 restriction of Corollary 6.3 and a source decision for the affected
Lemma 8.3/Theorem 1.7/Theorem 1.8 odd branches,
the concrete global lattice/localization, local sum-of-squares, and strong-
approximation instances, independent review, and exact-commit release
verification.
