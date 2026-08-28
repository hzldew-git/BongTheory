/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StabilizationPrefixes
import Bong.Lattice.ScaledHyperbolicChangeScale
import Bong.Lattice.Omeara9328TailConditions
import Bong.Bong.Representation

/-!
# Representations through paired hyperbolic stabilizations

A representation of two base quadratic spaces extends through paired
hyperbolic towers whose corresponding scale generators have equal valuation.
Applied to Jordan prefixes, this transports O'Meara's representation
conditions 93:28(ii) and (iii) through the rank stabilization used in 93:21.
-/

namespace Bong

open Dyadic Module

namespace QuadraticSpace

universe u v w z x

variable {K : Type u} [Field K]
  {U : Type v} [AddCommGroup U] [Module K U]
  {V : Type w} [AddCommGroup V] [Module K V]
  {W : Type z} [AddCommGroup W] [Module K W]
  {X : Type x} [AddCommGroup X] [Module K X]
  {q : QuadraticSpace K U} {q' : QuadraticSpace K V}
  {r : QuadraticSpace K W} {r' : QuadraticSpace K X}

/-- Represent orthogonal sums componentwise. -/
def Representation.orthogonalSum
    (f : Representation q q') (g : Representation r r') :
    Representation (q.orthogonalSum r) (q'.orthogonalSum r') where
  toLinearMap :=
    { toFun := fun x ↦ (f.toLinearMap x.1, g.toLinearMap x.2)
      map_add' := by
        intro x y
        ext <;> simp
      map_smul' := by
        intro c x
        ext <;> simp }
  injective := by
    intro x y hxy
    apply Prod.ext
    · exact f.injective (congrArg Prod.fst hxy)
    · exact g.injective (congrArg Prod.snd hxy)
  map_bilin := by
    intro x y
    change
      q'.bilin (f.toLinearMap x.1) (f.toLinearMap y.1) +
          r'.bilin (g.toLinearMap x.2) (g.toLinearMap y.2) =
        q.bilin x.1 y.1 + r.bilin x.2 y.2
    rw [f.map_bilin, g.map_bilin]

end QuadraticSpace

namespace Lattice

universe u v w z

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {U : Type v} [AddCommGroup U] [Module K U]
  {V : Type w} [AddCommGroup V] [Module K V]
  {Z : Type z} [AddCommGroup Z] [Module K Z]

/-- A base-space representation extends through paired hyperbolic towers.
The two towers may use different representatives for the same scale ideal. -/
noncomputable def pairedHyperbolicExtensionRepresentation
    {q : QuadraticSpace K U} {r : QuadraticSpace K V}
    {s : QuadraticSpace K Z}
    (L : Lattice K U) (M : Lattice K V)
    (f : QuadraticSpace.Representation q (r.orthogonalSum s)) :
    (t : Nat) → (sourceScale targetScale : Fin t → Kˣ) →
      (∀ i, ordUnit K (sourceScale i) = ordUnit K (targetScale i)) →
      QuadraticSpace.Representation
        (pairedHyperbolicExtensionForm q t sourceScale)
        ((pairedHyperbolicExtensionForm r t targetScale).orthogonalSum s)
  | 0, sourceScale, targetScale, _ => by
      let sourceBase :=
        (pairedHyperbolicExtensionBaseIsometry q L sourceScale)
          |>.toQuadraticSpaceIsometry
      let targetBase :=
        (pairedHyperbolicExtensionBaseIsometry r M targetScale)
          |>.toQuadraticSpaceIsometry
      exact
        (targetBase.symm.orthogonalSum
            (QuadraticSpace.Isometry.refl s)).toRepresentation.trans
          (f.trans sourceBase.toRepresentation)
  | t + 1, sourceScale, targetScale, hord => by
      let sourceHead := QuadraticSpace.hyperbolicPlane (sourceScale 0)
      let targetHead := QuadraticSpace.hyperbolicPlane (targetScale 0)
      let head : QuadraticSpace.Representation sourceHead targetHead :=
        (scaledHyperbolicChangeScaleIsometry
          (sourceScale 0) (targetScale 0) (hord 0))
            |>.toQuadraticSpaceIsometry.toRepresentation
      let tail := pairedHyperbolicExtensionRepresentation L M f t
        (Fin.tail sourceScale) (Fin.tail targetScale)
        (fun i ↦ hord i.succ)
      let assembled := head.orthogonalSum (head.orthogonalSum tail)
      let targetReframe : QuadraticSpace.Isometry
          (targetHead.orthogonalSum
            (targetHead.orthogonalSum
              ((pairedHyperbolicExtensionForm r t
                (Fin.tail targetScale)).orthogonalSum s)))
          ((targetHead.orthogonalSum
              (targetHead.orthogonalSum
                (pairedHyperbolicExtensionForm r t
                  (Fin.tail targetScale)))).orthogonalSum s) :=
        (QuadraticSpace.orthogonalSumAssoc targetHead targetHead
            ((pairedHyperbolicExtensionForm r t
              (Fin.tail targetScale)).orthogonalSum s)).symm |>.trans
          ((QuadraticSpace.orthogonalSumAssoc
            (targetHead.orthogonalSum targetHead)
            (pairedHyperbolicExtensionForm r t (Fin.tail targetScale)) s).symm |>.trans
            ((QuadraticSpace.orthogonalSumAssoc targetHead targetHead
                (pairedHyperbolicExtensionForm r t
                  (Fin.tail targetScale))).orthogonalSum
              (QuadraticSpace.Isometry.refl s)))
      exact targetReframe.toRepresentation.trans assembled

namespace JordanDecomposition

universe x y

variable {X : Type x} {Y : Type y}
  [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y]
  {q : QuadraticSpace K X} {r : QuadraticSpace K Y}
  {L : Lattice K X} {M : Lattice K Y} {N : Nat}

/-- Simultaneous stabilization preserves every prefix representation into an
orthogonal extension. -/
theorem saturationStablePrefix_embedsInto
    {J : JordanDecomposition q L (N + 2)}
    {H : JordanDecomposition r M (N + 2)}
    (F : SameFundamentalType J H)
    {m : Nat} (hk : m + 1 ≤ N + 2)
    (s : QuadraticSpace K Z)
    (h : QuadraticSublattice.EmbedsIntoOrthogonalSum
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1))
      (H.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1)) s) :
    QuadraticSublattice.EmbedsIntoOrthogonalSum
      (J.saturationStableJordan.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 1))
      (H.saturationStableJordan.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 1)) s := by
  rcases h with ⟨f⟩
  let sourceGather := J.saturationStablePrefixGatherIsometry hk
  let targetGather := H.saturationStablePrefixGatherIsometry hk
  have hscale : ∀ i,
      ordUnit K (J.prefixScaleGenerator hk i) =
        ordUnit K (H.prefixScaleGenerator hk i) := by
    intro i
    unfold prefixScaleGenerator
    have hidx := prefixIndexEquiv_component_eq
      J.toOrthogonalDecomposition H.toOrthogonalDecomposition hk i
    rw [← hidx]
    exact (F.scaleGenerator_order_eq_sameIndex _).symm
  let tower := pairedHyperbolicExtensionRepresentation
    (J.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1)).lattice
    (H.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1)).lattice
    f (m + 1) (J.prefixScaleGenerator hk) (H.prefixScaleGenerator hk)
    hscale
  let targetReframe :=
    (targetGather.symm.toQuadraticSpaceIsometry.orthogonalSum
      (QuadraticSpace.Isometry.refl s))
  exact ⟨targetReframe.toRepresentation.trans
    (tower.trans sourceGather.toQuadraticSpaceIsometry.toRepresentation)⟩

end JordanDecomposition
end Lattice

end Bong
