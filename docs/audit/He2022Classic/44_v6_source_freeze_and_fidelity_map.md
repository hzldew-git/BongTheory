# He Classic v6 source freeze and theorem-fidelity map

Status: `V6_SOURCE_FROZEN` / `LEAN_SYNC_IN_PROGRESS` /
`NOT_WHOLE_PAPER_COMPLETE` / `NOT_RELEASED`.

## Authority and privacy

The user-approved semantic authority is the author-held
`classic_dyadic-n-uni-v6.tex` (140,696 bytes, SHA-256
`4D3903083188E2823CCA930477A43F82A1FC3C69AD96056ADB099D924B14EC5A`).
Its PDF is 427,011 bytes, SHA-256
`227C4AB3053993941E7CF07B7FDFDB9FBBE95CE68D921CB4E92842E69F42735D`.
The v5-to-v6 latexdiff TeX and PDF have SHA-256 values
`D3FDCA2A8EA2B12184D1C3B4636751721EBB2471EB9D102E0D60F2F8B905DC6E`
and `6F25F4083EB944C365C559D5E5C4BE54672C4E694583541F8ECE9294F0319D5A`.
These files remain outside Git history and Review Kits. The published paper
and arXiv revision remain comparison sources, not the current authority.

## Source-first v5-to-v6 map

| v6 source location | Actual v6 change | Lean endpoint and fidelity status |
| --- | --- | --- |
| Theorem 1.7, TeX line 226 | Diagonal rank-`n+3` obstruction explicitly assumes `n >= 2` even. The unsupported odd sentence is deleted. | `HeClassic2024GlobalData.SectionEightLaws.he2022ClassicTheorem17_even` has both hypotheses, but its number-field lattice and local-defect premises remain in a conditional data package. |
| Theorem 1.8, line 230 | Ramified extension obstruction explicitly assumes `n >= 2` even. | `HeClassic2024ExtensionData.Lemma83Laws.he2022ClassicTheorem18_even` has both hypotheses. It is conditional on a local obstruction and localization packages, not a concrete global theorem. |
| Corollary 6.3, line 1361 | Diagonalizability explicitly assumes `n >= 2` even. | `BONG.GoodBONG.he2022ClassicCorollary63_even` proves equality with the BONG basis lattice. The checked `e=2, n=3` counterexample concerns the obsolete unrestricted v5 statement and is retained as regression evidence only. |
| Lemma 8.1(iii), line 1632 | The mapped vectors form a good BONG for *some* upper integral lattice on the extended quadratic space, not necessarily for the preassigned scalar-extension lattice. | `goodBONG_mappedValues_haveRealization` constructs an actual upper integral lattice and good BONG with the mapped values in the canonical diagonal space. The isometry connecting that standard ambient space to the literal scalar extension has not yet been constructed in Lean. The abstract `Lemma81Laws.he2022ClassicLemma81iii` is a numerical/predicate interface, not an additional concrete carrier proof. |
| Lemma 8.3, line 1680 | The statement explicitly assumes `n >= 2` even. Its proof now uses monotone upper orders and Beli diagonalizability to identify the Lemma 8.1(iii) lattice with the specified scalar extension. | `mappedValues_order_monotone_of_lower` proves upper-order monotonicity from lower monotonicity and ramification scaling for the actual finite-completion coefficient realization. `HeClassic2024Carrier.he2022ClassicLemma83_carrier_eq_of_basisTransport` proves the carrier-equality deduction from lower Corollary 6.3, upper monotone-order diagonalization, and explicit basis transport. The basis-transport hypothesis is not instantiated for concrete scalar extension. `Lemma83Laws.he2022ClassicLemma83_even` has the correct parity/rank range but still assumes the remaining `local_ramified_obstruction` as a field. |
| Lemma 8.3 proof, line 1692 | The witness index is consistently `j`; the surplus parenthesis in the Lemma 8.1(iii) defect estimate is removed. | Presentation corrections: no change to Lean theorem propositions. |

The v6 revision does **not** discharge the independent Section 8 arithmetic
boundaries: a concrete global/local lattice system, the place equivalence,
positive-definite globalization and localization of representation, non-dyadic
and dyadic sum-of-squares instances, and strong approximation. These remain
explicitly conditional. The odd `n=3` counterexample remains valid against
v5 but is not a counterexample to v6's restricted corollary.

## Initial Lean development check

`Bong/Lattice/He2022ClassicLemma83Carrier.lean`, the new
`mappedValues_order_monotone_of_lower` theorem in the concrete completion
bridge, and the focused
`BongTest/He2022ClassicEvenExtensionAudit.lean` passed Lean 4.32.1 source
checks with exit code zero against the existing v5 worktree's compiled
dependencies on 2026-09-17. The new carrier theorem's transitive axioms are
exactly `[propext, Classical.choice, Quot.sound]`; the focused audit also
printed the existing conditional Lemma 8.3 and Theorem 1.8 signatures. This
is useful development evidence only: the merged v6 source, complete package,
and fresh Review Kit have not yet passed an independent full build. No compiled
dependencies were copied into the v6 worktree. A single new generated `.olean`
for the carrier module was written into the old worktree's ignored build cache
solely to resolve the focused audit import; it is not release evidence.

A deliberately dirty **development-only** source kit was generated from the
uncommitted v6 worktree and passed structural verification of 2,026 checksummed
payload files. Its manifest names the v6 TeX hash and does not contain the
manuscript or its PDF. Its source-tree state is `dirty`, so this archive is
neither a release candidate nor a substitute for an exact-clean-commit kit,
full rebuild, or GitHub CI.

## Promotion gates

1. Update the manifest, entry module, source delta, theorem index, and audit
   comments to v6 without silently renaming historical v5 implementation
   constants or rewriting old verification receipts.
2. Construct the concrete ambient/scalar-extension basis transport and local
   Lemma 8.3 obstruction, or retain them as explicit prerequisites and Grade D.
   The abstract carrier-equality deduction is already kernel checked; do not
   infer its concrete basis-transport hypothesis from coefficient data alone.
3. Check the exact merged source in a clean build, run all manifest audit
   modules plus the enforcing paper axiom gate, perform the no-sorry scan and
   exact-dependency checks, and independently verify a source-only Review Kit.
4. Require exact-head GitHub CI before merging the v6 branch. Generate the
   release kit from the exact merge commit and publish only with accurate
   `NOT_COMPLETE` wording and remaining semantic boundaries.

Successful compilation will establish kernel acceptance of the encoded
statements; it will not by itself certify agreement with the v6 paper or the
unproved concrete arithmetic instances. Human mathematical sign-off remains
separate.
