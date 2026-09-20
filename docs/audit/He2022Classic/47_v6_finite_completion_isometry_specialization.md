# He Classic v6: finite-completion isometry specialization

Status: `G_WORKTREE_DEVELOPMENT` / `TARGET_MODULE_BUILT` /
`GRADE_D_NOT_COMPLETE` / `NOT_RELEASE_EVIDENCE`.

The semantic source is the user-approved author-held
`classic_dyadic-n-uni-v6.tex`, SHA-256
`4D3903083188E2823CCA930477A43F82A1FC3C69AD96056ADB099D924B14EC5A`.
The manuscript is not included in Git or Review Kits.

## Exact new theorem

`Bong.HeClassic2024NumberFieldScalarExtension.completionScalarExtension_isIsometric_diagonalRealization`
specializes Report 46's mapped-BONG quadratic-lattice isometry to the actual
continuous field embedding between the completions at a dyadic prime `p`
and a prime `P` lying above it. The existing theorem
`completionMap_preserves_integerRing` supplies the valuation-ring premise;
the field algebra structure is the one induced by `completionMap p P`, not
an arbitrary embedding. The result is an isometry from the literal tensor
scalar extension of the lower lattice to a mapped-value standard diagonal
BONG realization.

The theorem still has **two explicit mathematical premises**: the lower
lattice equals the span of the displayed lower BONG basis, and the upper
realization's BONG orders are monotone. Neither is silently inferred from
matching coefficient values. Report 46 separately proves that the corrected
even-rank Corollary 6.3 discharges the lower premise in a classic-universal
situation. The current theorem does not combine those facts into the full
source-facing v6 Lemma 8.3 endpoint.

The new module passed direct Lean source checking and an isolated G-source
Lake target build under Lean 4.32.1. The canonical paper entry, all eight
manifest audit modules, and `BongTest.AxiomGate` built in the same G worktree
at `LEAN_NUM_THREADS=1` and Lake jobs=1. The focused audit's `#print axioms`
reported only `propext`, `Classical.choice`, and `Quot.sound` for the new
theorem. The enforcing imported-closure check reported
`AXIOM_GATE_PASS: 63033 declarations checked`. These local checks are not
exact-head GitHub CI or an independent final Review Kit.

## Remaining boundary

The constructed upper lattice has not yet been identified **as the paper's
specified localized scalar-extension lattice** in a common ambient space.
The quadratic-lattice isometry under premises does not imply literal carrier
equality. The ramified local obstruction of Lemma 8.3, Section 8 concrete
arithmetic/global instances, and independent human semantic sign-off remain
open. The overall status is **Grade D / NOT_COMPLETE**.
