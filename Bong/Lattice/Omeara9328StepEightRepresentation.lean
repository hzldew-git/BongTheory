/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightThresholds
import Bong.Lattice.PairedHyperbolicRepresentation

/-!
# Prefix representations in O'Meara 93:28, Step 8

The inserted hyperbolic plane is a literal common left summand in every
prefix beyond the first new boundary.  Hence every representation of the
corresponding old prefixes extends through that plane.  At the two new
boundaries the displayed line `pi^2 a_0` is isometric to the old line
`a_0`, so conditions 93:28(ii) and (iii) can use the original first
condition-(iii) representation.
-/

namespace Bong

open Dyadic Module

namespace QuadraticSpace

universe u v w x y z t a

variable {K : Type u} [Field K]
  {U : Type v} [AddCommGroup U] [Module K U]
  {V : Type w} [AddCommGroup V] [Module K V]
  {W : Type x} [AddCommGroup W] [Module K W]
  {X : Type y} [AddCommGroup X] [Module K X]
  {Y : Type z} [AddCommGroup Y] [Module K Y]
  {Z : Type t} [AddCommGroup Z] [Module K Z]
  {T : Type a} [AddCommGroup T] [Module K T]

/-- Transport a representation into an orthogonal extension through
isometries of its source, target, and final line. -/
noncomputable def Representation.transportOrthogonalExtension
    {sourceNew : QuadraticSpace K U} {sourceOld : QuadraticSpace K V}
    {targetNew : QuadraticSpace K W} {targetOld : QuadraticSpace K X}
    {extraOld : QuadraticSpace K Y} {extraNew : QuadraticSpace K Z}
    (sourcePresentation : Isometry sourceNew sourceOld)
    (targetPresentation : Isometry targetNew targetOld)
    (extra : Isometry extraOld extraNew)
    (f : Representation sourceOld (targetOld.orthogonalSum extraOld)) :
    Representation sourceNew (targetNew.orthogonalSum extraNew) :=
  (targetPresentation.symm.orthogonalSum extra).toRepresentation.trans
    (f.trans sourcePresentation.toRepresentation)

/-- Transport a representation after adjoining the same common left
orthogonal summand to source and target. -/
noncomputable def Representation.transportThroughCommonLeft
    {common : QuadraticSpace K U}
    {sourceNew : QuadraticSpace K V} {sourceOld : QuadraticSpace K W}
    {targetNew : QuadraticSpace K X} {targetOld : QuadraticSpace K Y}
    {extraOld : QuadraticSpace K Z} {extraNew : QuadraticSpace K T}
    (sourcePresentation :
      Isometry sourceNew (common.orthogonalSum sourceOld))
    (targetPresentation :
      Isometry targetNew (common.orthogonalSum targetOld))
    (extra : Isometry extraOld extraNew)
    (f : Representation sourceOld (targetOld.orthogonalSum extraOld)) :
    Representation sourceNew (targetNew.orthogonalSum extraNew) := by
  let lifted := (Representation.refl common).orthogonalSum f
  let reassociate :=
    (orthogonalSumAssoc common targetOld extraOld).symm
  let targetChange := targetPresentation.symm.orthogonalSum extra
  exact targetChange.toRepresentation.trans <|
    reassociate.toRepresentation.trans <|
      lifted.trans sourcePresentation.toRepresentation

/-- Multiplication of the coordinate by `u` identifies the line with
coefficient `u^2 a` with the line with coefficient `a`. -/
noncomputable def scaledLineSquareIsometry (u a : Kˣ) :
    Isometry (scaledLine (u ^ 2 * a)) (scaledLine a) where
  toLinearEquiv :=
    { toFun := fun x ↦ (u : K) * x
      invFun := fun x ↦ ((u⁻¹ : Kˣ) : K) * x
      left_inv := by
        intro x
        simp only [Units.val_inv_eq_inv_val]
        field_simp [Units.ne_zero u]
      right_inv := by
        intro x
        simp only [Units.val_inv_eq_inv_val]
        field_simp [Units.ne_zero u]
      map_add' := by
        intro x y
        ring
      map_smul' := by
        intro c x
        simp only [smul_eq_mul, RingHom.id_apply]
        ring }
  map_bilin := by
    intro x y
    change (a : K) * ((u : K) * x) * ((u : K) * y) =
      ((u ^ 2 * a : Kˣ) : K) * x * y
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    ring

end QuadraticSpace

namespace Lattice.JordanDecomposition

universe u v w z x

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {Z : Type z} [AddCommGroup Z] [Module K Z]
  {X : Type x} [AddCommGroup X] [Module K X]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K Z} {s' : QuadraticSpace K X}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

/-- The line attached to the inserted norm generator is square-isometric
to the old first fundamental line. -/
noncomputable def stepEightRaisedLineIsometry
    (J : JordanDecomposition q L (n + 2))
    (A : FundamentalNormGeneratorChoice J) :
    QuadraticSpace.Isometry
      (QuadraticSpace.scaledLine (J.stepEightRaisedNormGeneratorWith A))
      (QuadraticSpace.scaledLine (A.value 0)) := by
  simpa only [stepEightRaisedNormGeneratorWith] using
    QuadraticSpace.scaledLineSquareIsometry
      (uniformizerUnit K) (A.value 0)

/-- A representation of the old first prefix transfers to the first
Step-8 prefix. -/
theorem SameFundamentalType.stepEightFirstPrefix_embedsInto
    (F : SameFundamentalType J H)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hgapH : 1 < ordUnit K (H.scaleGenerator 1) -
      ordUnit K (H.scaleGenerator 0))
    (extra : QuadraticSpace.Isometry s s')
    (h : QuadraticSublattice.EmbedsIntoOrthogonalSum
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1)
      (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1) s) :
    QuadraticSublattice.EmbedsIntoOrthogonalSum
      ((J.stepEightJordan hgap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice 1)
      ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice 1) s' := by
  rcases h with ⟨f⟩
  exact ⟨QuadraticSpace.Representation.transportOrthogonalExtension
    (J.stepEightFirstPrefixPresentation hgap).toQuadraticSpaceIsometry
    (F.targetStepEightFirstPrefixPresentation hgap hgapH).toQuadraticSpaceIsometry
    extra f⟩

/-- A representation of the old first prefix transfers to the prefix
formed by the old head and the inserted common plane. -/
theorem SameFundamentalType.stepEightFirstTwoPrefix_embedsInto
    (F : SameFundamentalType J H)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hgapH : 1 < ordUnit K (H.scaleGenerator 1) -
      ordUnit K (H.scaleGenerator 0))
    (extra : QuadraticSpace.Isometry s s')
    (h : QuadraticSublattice.EmbedsIntoOrthogonalSum
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1)
      (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1) s) :
    QuadraticSublattice.EmbedsIntoOrthogonalSum
      ((J.stepEightJordan hgap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice 2)
      ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice 2) s' := by
  rcases h with ⟨f⟩
  exact ⟨QuadraticSpace.Representation.transportThroughCommonLeft
    (J.stepEightFirstTwoPrefixPresentation hgap).toQuadraticSpaceIsometry
    (F.targetStepEightFirstTwoPrefixPresentation hgap hgapH).toQuadraticSpaceIsometry
    extra f⟩

/-- Every old representation after the first boundary transfers to the
corresponding later Step-8 prefix. -/
theorem SameFundamentalType.stepEightLaterPrefix_embedsInto
    (F : SameFundamentalType J H)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hgapH : 1 < ordUnit K (H.scaleGenerator 1) -
      ordUnit K (H.scaleGenerator 0))
    (i : Fin n)
    (extra : QuadraticSpace.Isometry s s')
    (h : QuadraticSublattice.EmbedsIntoOrthogonalSum
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 2))
      (H.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 2)) s) :
    QuadraticSublattice.EmbedsIntoOrthogonalSum
      ((J.stepEightJordan hgap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (i.val + 3))
      ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (i.val + 3)) s' := by
  rcases h with ⟨f⟩
  have hk : i.val + 1 ≤ n + 1 := by omega
  exact ⟨QuadraticSpace.Representation.transportThroughCommonLeft
    (J.stepEightLaterPrefixPresentation hgap i.val hk).toQuadraticSpaceIsometry
    (F.targetStepEightLaterPrefixPresentation hgap hgapH i.val hk).toQuadraticSpaceIsometry
    extra f⟩

end Lattice.JordanDecomposition

end Bong
