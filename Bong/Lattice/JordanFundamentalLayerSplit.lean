/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.JordanExtremeScaleTruncation
import Bong.Lattice.OmearaFundamentalInvariants
import Bong.Lattice.OmearaModularDecompositionTruncation
import Bong.Lattice.OrthogonalDecompositionPrefixSuffix
import Bong.Lattice.ScaleTruncationIsometry

/-!
# Orthogonal splitting of a noninitial fundamental layer

For a strict Jordan decomposition and a noninitial component `k`, the
fundamental lattice at the `k`th scale is integrally isometric to the
orthogonal product of the scalar-dualized exact prefix and the unchanged
exact suffix.  This is the precise geometric identity

`L^(s_k) = s_k (L_{<k})^# ⊥ L_{≥k}`

used in Beli's proof of Lemma 2.16(i).
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- The concrete product description of a noninitial fundamental layer. -/
noncomputable def fundamentalLayerSplitIsometry
    (J : JordanDecomposition q L t) {k n : Nat}
    (hkn : k + (n + 1) = t) (hk : 0 < k) :
    let D := J.toOrthogonalDecomposition
    let P := D.prefixQuadraticSublattice k
    let S := D.suffixQuadraticSublattice k
    let c := scaleTruncationUnit (K := K)
      (ordUnit K (J.scaleGenerator ⟨k, by omega⟩))
    Isometry (P.space.orthogonalSum S.space) q
      (product (rescale c (dualLattice P.space P.lattice)) S.lattice)
      (J.fundamentalLattice ⟨k, by omega⟩) := by
  let D := J.toOrthogonalDecomposition
  let P := D.prefixQuadraticSublattice k
  let S := D.suffixQuadraticSublattice k
  let r := ordUnit K (J.scaleGenerator ⟨k, by omega⟩)
  let c := scaleTruncationUnit (K := K) r
  let split := (D.prefixSuffixLatticeIsometry k).scaleTruncation r
  have hkcount : (k - 1) + 1 = k := by omega
  have hprefix := J.initialSegment_scaleTruncation_eq_rescale_dual hkn hk
  rw [hkcount] at hprefix
  have hsuffix := J.suffixSegment_scaleTruncation_eq_self hkn
  change scaleTruncation S.space S.lattice r = S.lattice at hsuffix
  change scaleTruncation P.space P.lattice r =
    rescale c (dualLattice P.space P.lattice) at hprefix
  change Isometry (P.space.orthogonalSum S.space) q
      (scaleTruncation (P.space.orthogonalSum S.space)
        (product P.lattice S.lattice) r)
      (scaleTruncation q L r) at split
  rw [scaleTruncation_orthogonalProduct, hprefix, hsuffix] at split
  simpa only [fundamentalLattice, fundamentalScaleOrder, r, c, D, P, S]
    using split

end Lattice.JordanDecomposition

end Bong
