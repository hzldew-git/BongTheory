# He Classic v6: the specified scalar-extension lattice

Status: `G_WORKTREE_DEVELOPMENT` / `TARGET_MODULES_BUILT` /
`GRADE_D_NOT_COMPLETE` / `NOT_RELEASE_EVIDENCE`.

The semantic authority remains the user-approved author-held
`classic_dyadic-n-uni-v6.tex`, SHA-256
`4D3903083188E2823CCA930477A43F82A1FC3C69AD96056ADB099D924B14EC5A`.
Neither its TeX nor its PDF is present in this repository or a Review Kit.
Report 44 fixes the v5-to-v6 statement map. This report records a new,
narrowly scoped formalization of the lattice-transport step in the proof of
v6 Lemma 8.3.

## What is now proved

| Source-facing question | Lean declaration | Exact scope |
| --- | --- | --- |
| What is the lattice obtained by extending a specified lower lattice? | `Bong.Lattice.scalarExtension` and `scalarExtension_toSubmodule_eq_span` | Its carrier is the upper valuation-ring span of the pure tensors of **all** lower-lattice vectors, provided the field embedding sends the lower valuation ring into the upper one. This also shows that the chosen-basis definition is independent of the basis. |
| What happens to a lower integral basis? | `Bong.Lattice.scalarExtension_basisLattice` | For every finite field basis `b` and the same ring-preservation premise, the scalar extension of `basisLattice b` is exactly `basisLattice (b.baseChange E)`. |
| Does the map between the selected number-field completions preserve integral elements? | `Bong.HeClassic2024NumberFieldScalarExtension.completionMap_preserves_integerRing` | Yes, for any pair of finite dyadic places `P` above `p`. The proof handles zero separately and uses the already proved ramification-index order formula for nonzero elements. It does **not** assume the extension is ramified. |
| Are the two lattice statements instantiated at actual finite completions? | `completionScalarExtension_toSubmodule_eq_span` and `completionScalarExtension_basisLattice` | Yes, for the algebra structure induced by the concrete `completionMap p P`. The scalar-extension ambient is the literal tensor product over the lower completion. |

These statements are mathematical lemmas about the **specified** tensor-
extension lattice. They are not merely equalities of diagonal coefficient
lists. Both new source modules compile in the G worktree with Lean 4.32.1;
the target build of
`Bong.Lattice.He2022ClassicCompletionLatticeScalarExtension` exited zero on
2026-09-18. The paper entry and all eight paper-manifest audit modules also
built from source with exit code zero. The focused enforcing axiom gate reported
`AXIOM_GATE_PASS: 63028 declarations checked`. The audit's `#print axioms`
output gives exactly `propext`, `Classical.choice`, and `Quot.sound` for each
new theorem (or a subset), with no custom or sorry axiom.

## Boundary that remains open

The v6 Lemma 8.1(iii) construction supplies an upper good-BONG lattice in a
standard diagonal ambient space with the mapped coefficients. The new lemmas
describe the literal scalar extension of the **lower** lattice and its
base-changed lower basis. The missing bridge is an explicit quadratic-space
isometry and lattice/basis identification between these two constructions.
The abstract carrier theorem in `He2022ClassicLemma83Carrier.lean` still
requires precisely that identification before it can be applied to the
separately realized upper good-BONG lattice. Equal coefficient values alone
must not be treated as this bridge.

Even after that bridge, the ramified local non-universality contradiction in
v6 Lemma 8.3, the global/local arithmetic instances of Section 8, and
independent human semantic sign-off remain open. The status is therefore
**Grade D / NOT_COMPLETE**, not whole-paper verification.

## Reproducibility and trust notes

Development used the clean G source worktree based on
`1f3d92e7419db481c0e1ac229c5b7c0b1fdc5dd7`, with nine separately
cloned, pinned, clean dependency source repositories and the official
mathlib cache. No compiled project artifacts were copied from another
worktree. Two earlier multi-job source attempts failed in older modules
with intermittent reads of existing mathlib `.olean.private` files; their
failed targets subsequently compiled when retried serially, and the
single-job new-module target build passed. Those environmental attempts
are not proof failures, but they remain part of the verification history.

The repository's comment-aware proof-token scan passed on all 2,814 tracked
Lean sources; the same scanner separately found no forbidden proof token in
either new, not-yet-tracked Lean file. The paper-entry and all eight audit-module
builds and focused enforcing axiom gate passed. The working tree is still
not an exact clean release commit. These checks do not replace the remaining
paper-fidelity audit, whole-project gate, exact-head CI, independent clean
Review Kit, or human sign-off. No v6 release is claimed here.
