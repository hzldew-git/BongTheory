/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9318DeterminantOne
import Bong.Lattice.OmearaScaledHyperbolicTowerSpace
import Bong.Lattice.OmearaHyperbolicTransvection

/-!
# The hyperbolic model in O'Meara 93:18(vi)

When the discriminant error is zero, the first model in 93:18(vi) is
`A(a,0) ⊥ A(b,0)`.  Each factor is hyperbolic over the field.  This file
records an explicit isometry from that model to the standard two-plane
zero-coefficient tower.  It is the geometric fact that distinguishes the
first model from the discriminant-twisted model.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [laws : DyadicDiscriminantClassLaws K]

/-- A general plane `A(a,0)` is a standard zero-coefficient plane over the
field. -/
noncomputable def omearaGeneralPlaneZeroRightToZeroPlaneSpaceIsometry
    (a : K) :
    QuadraticSpace.Isometry
      (QuadraticSpace.omearaGeneralPlane a 0 (by simp))
      ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ)) := by
  have ha : a = 2 * (a / 2) := by
    field_simp
  let toOmeara := QuadraticSpace.omearaGeneralPlaneZeroRightIsometry a
  let toHyperbolic :=
    (hyperbolicToOmearaPlaneSpaceIsometry a (a / 2) ha).symm
  let toZeroPlane :=
    ((scaledZeroOmearaPlaneLatticeIsometry (K := K) (1 : Kˣ)).symm
      |>.toQuadraticSpaceIsometry)
  exact toOmeara.trans (toHyperbolic.trans toZeroPlane)

/-- Repackage a native product of two zero-coefficient planes as the
recursively parenthesized two-plane tower. -/
noncomputable def twoZeroPlaneProductToTowerTwoSpaceIsometry :
    QuadraticSpace.Isometry
      (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum
          ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ)))
      (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2) where
  toLinearEquiv :=
    { toFun := fun x ↦ (x.1, (x.2, 0))
      invFun := fun x ↦ (x.1, x.2.1)
      left_inv := by intro x; rfl
      right_inv := by
        intro x
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · rfl
          · funext i
            exact Fin.elim0 i
      map_add' := by
        intro x y
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · rfl
          · funext i
            exact Fin.elim0 i
      map_smul' := by
        intro c x
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · rfl
          · funext i
            exact Fin.elim0 i }
  map_bilin := by
    intro x y
    change
      ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ)).bilin
          x.1 y.1 +
        (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ)).bilin
          x.2 y.2 + 0) =
      ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ)).bilin
          x.1 y.1 +
        ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ)).bilin
          x.2 y.2
    simp

namespace Omeara9318RankFourModelParameters

/-- If `alpha = 0`, the first determinant-one quaternary model is the
standard two-plane hyperbolic tower over the field. -/
noncomputable def jSpaceToHyperbolicTowerIsometry
    (P : Omeara9318RankFourModelParameters K) (halpha : P.alpha = 0) :
    QuadraticSpace.Isometry P.jData.space
      (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2) := by
  let left : QuadraticSpace.Isometry P.jData.leftSpace
      ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ)) := by
    simpa only [OmearaOddQuaternaryModelData.leftSpace, jData,
      halpha, neg_zero, zero_mul] using
        omearaGeneralPlaneZeroRightToZeroPlaneSpaceIsometry
          (K := K) (P.a : K)
  let right : QuadraticSpace.Isometry P.jData.rightSpace
      ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ)) := by
    simpa only [OmearaOddQuaternaryModelData.rightSpace, jData] using
      omearaGeneralPlaneZeroRightToZeroPlaneSpaceIsometry
        (K := K) (P.b : K)
  let factors := left.orthogonalSum right
  simpa only [OmearaOddQuaternaryModelData.space] using
    factors.trans (twoZeroPlaneProductToTowerTwoSpaceIsometry (K := K))

end Omeara9318RankFourModelParameters

end Lattice

end Bong
