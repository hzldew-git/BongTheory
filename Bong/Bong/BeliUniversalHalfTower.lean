/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalSplitting
import Bong.Bong.GoodBONGScalarAgreementClassification
import Bong.Bong.AlternatingEndpointTowerNormalizationProof
import Bong.Bong.Beli2006SectionFourInvariants
import Bong.Bong.Beli2019PrefixChange
import Bong.Lattice.NormIdealOrthogonalProduct
import Bong.Lattice.OmearaScaledHyperbolicTowerInvariants

/-!
# The standard half-hyperbolic tower

This file packages the literal lattice
`2⁻¹ A(0,0)^k` and records the invariants needed in Beli's Lemmas
4.6--4.9.  The determinant assertions use the ordinary field square class,
as in the paper, even though the library also retains the finer unit square
class of an integral Gram determinant.
-/

namespace Bong

open Dyadic Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

noncomputable local instance universalSectionFourDiscriminant :
    DyadicDiscriminantClassLaws K :=
  dyadicDiscriminantClassLawsProved

namespace Lattice.QuadraticLatticeModel

/-- The unique zero-dimensional quadratic lattice, used as the residual of
a pure half-hyperbolic tower. -/
noncomputable def zeroModel : QuadraticLatticeModel (K := K) :=
  { Carrier := Fin 0 → K
    form := Lattice.zeroCoordinateQuadraticSpace (K := K)
    lattice := QuadraticSpace.zeroCoordinateBasisLattice (K := K) }

@[simp]
theorem zeroModel_rank : (zeroModel (K := K)).rank = 0 := by
  change finrank K (Fin 0 → K) = 0
  simp

/-- The standard integral model of `2⁻¹ A(0,0)^k`. -/
noncomputable def halfHyperbolicTower (k : Nat) :
    QuadraticLatticeModel (K := K) :=
  (zeroModel (K := K)).adjoinHalfHyperbolic k

@[simp]
theorem halfHyperbolicTower_rank (k : Nat) :
    (halfHyperbolicTower (K := K) k).rank = 2 * k := by
  rw [halfHyperbolicTower,
    QuadraticLatticeModel.rank_adjoinHalfHyperbolic, zeroModel_rank]
  omega

theorem zeroModel_isIntegral : by
    let T := zeroModel (K := K)
    letI : AddCommGroup T.Carrier := T.addCommGroup
    letI : Module K T.Carrier := T.module
    exact T.IsIntegral := by
  let T := zeroModel (K := K)
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  change Lattice.IsIntegral
    (Lattice.zeroCoordinateQuadraticSpace (K := K))
    (QuadraticSpace.zeroCoordinateBasisLattice (K := K))
  rw [Lattice.isIntegral_iff_forall]
  intro x _hx
  have hx : x = 0 := by
    funext i
    exact Fin.elim0 i
  subst x
  change Dyadic.IsIntegral K 0
  rw [Dyadic.IsIntegral, Dyadic.ord_zero]
  exact le_top

theorem halfHyperbolicTower_isIntegral (k : Nat) :
    (halfHyperbolicTower (K := K) k).IsIntegral := by
  exact zeroModel_isIntegral.adjoinHalfHyperbolic k

end Lattice.QuadraticLatticeModel

namespace BONG.GoodBONG

/-- A chosen good BONG on the standard half-hyperbolic tower, with its
length transported to the paper's literal index `2k`. -/
noncomputable def standardHalfHyperbolicTowerBONG (k : Nat) : by
    let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) k
    letI : AddCommGroup T.Carrier := T.addCommGroup
    letI : Module K T.Carrier := T.module
    exact GoodBONG T.form T.lattice (2 * k) := by
  let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) k
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  let raw := Classical.choice (Bong.exists_good_bong T.form T.lattice)
  exact raw.castLength (by
    change finrank K T.Carrier = 2 * k
    simpa only [Lattice.QuadraticLatticeModel.rank] using
      Lattice.QuadraticLatticeModel.halfHyperbolicTower_rank
        (K := K) k)

end BONG.GoodBONG

namespace Lattice

/-- The pure standard tower is half-modular. -/
theorem halfHyperbolicTower_isModular (k : Nat) : by
    let T := QuadraticLatticeModel.halfHyperbolicTower (K := K) k
    letI : AddCommGroup T.Carrier := T.addCommGroup
    letI : Module K T.Carrier := T.module
    exact IsModular T.form T.lattice (dyadicHalfUnit (K := K)) := by
  let T := QuadraticLatticeModel.halfHyperbolicTower (K := K) k
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  change IsModular
    (halfHyperbolicExtensionForm
      (Lattice.zeroCoordinateQuadraticSpace (K := K)) k)
    (halfHyperbolicExtensionLattice
      (QuadraticSpace.zeroCoordinateBasisLattice (K := K)) k)
    (dyadicHalfUnit (K := K))
  rw [halfHyperbolicExtensionForm_eq,
    halfHyperbolicExtensionLattice_eq,
    zeroOmearaExtensionForm_eq_scaled]
  exact scaledZeroOmearaTowerLattice_isModular
    (dyadicHalfUnit (K := K)) k

/-- Every nonempty pure standard tower has norm ideal `O`. -/
theorem halfHyperbolicTower_normIdeal (k : Nat) : by
    let T := QuadraticLatticeModel.halfHyperbolicTower (K := K) (k + 1)
    letI : AddCommGroup T.Carrier := T.addCommGroup
    letI : Module K T.Carrier := T.module
    exact normIdeal T.form T.lattice = unitIdeal (K := K) := by
  let T := QuadraticLatticeModel.halfHyperbolicTower (K := K) (k + 1)
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  change normIdeal
      (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
        (dyadicHalfUnit (K := K))).orthogonalSum
        (halfHyperbolicExtensionForm
          (Lattice.zeroCoordinateQuadraticSpace (K := K)) k))
      (product (hyperbolicPlaneLattice (K := K))
        (halfHyperbolicExtensionLattice
          (QuadraticSpace.zeroCoordinateBasisLattice (K := K)) k)) =
    unitIdeal (K := K)
  rw [normIdeal_orthogonalProduct]
  have hhalf : (2 : K) * (dyadicHalfUnit (K := K) : K) = 1 := by
    change (dyadicTwoUnit (K := K) : K) *
      (dyadicHalfUnit (K := K) : K) = 1
    rw [← Units.val_mul]
    simp [dyadicHalfUnit]
  have hhead : normIdeal
      ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
        (dyadicHalfUnit (K := K)))
      (hyperbolicPlaneLattice (K := K)) = unitIdeal (K := K) := by
    let f := scaledZeroOmearaPlaneLatticeIsometry
      (dyadicHalfUnit (K := K))
    have hmap := normIdeal_map_isometry f.toQuadraticSpaceIsometry
      (hyperbolicPlaneLattice (K := K))
    have hfmap : map f.toQuadraticSpaceIsometry.toLinearEquiv
        (hyperbolicPlaneLattice (K := K)) =
        hyperbolicPlaneLattice (K := K) := f.map_eq
    rw [hfmap, normIdeal_hyperbolicPlaneLattice, hhalf] at hmap
    exact hmap.symm
  rw [hhead]
  apply sup_eq_left.mpr
  exact (Lattice.isIntegral_iff_normIdeal_le _ _).1
    (QuadraticLatticeModel.halfHyperbolicTower_isIntegral
      (K := K) k)

/-- Intrinsic version of the two preceding standard-tower invariants. -/
theorem halfHyperbolicTower_isHalfModularWithUnitNorm
    {k : Nat} (hk : 1 ≤ k) : by
    let T := QuadraticLatticeModel.halfHyperbolicTower (K := K) k
    letI : AddCommGroup T.Carrier := T.addCommGroup
    letI : Module K T.Carrier := T.module
    exact IsHalfModularWithUnitNorm T.form T.lattice := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact ⟨by
      have hcomm : 1 + j = j + 1 := by omega
      rw [hcomm]
      exact halfHyperbolicTower_isModular (K := K) (j + 1),
    by
      have hcomm : 1 + j = j + 1 := by omega
      rw [hcomm]
      exact halfHyperbolicTower_normIdeal (K := K) j⟩

/-- The refined determinant class of the standard `k`-plane tower.  Its
ordinary square class is the paper's `(-1)^k`; the displayed power of
`1/2` is retained here because `determinantClass` is the integral
refinement. -/
theorem determinantClass_halfHyperbolicTower (k : Nat) : by
    let T := QuadraticLatticeModel.halfHyperbolicTower (K := K) k
    letI : AddCommGroup T.Carrier := T.addCommGroup
    letI : Module K T.Carrier := T.module
    exact determinantClass T.form T.lattice =
      unitSquareClass K (((-1 : Kˣ) ^ k) *
        (dyadicHalfUnit (K := K)) ^ (2 * k)) := by
  induction k with
  | zero =>
      let T := QuadraticLatticeModel.halfHyperbolicTower (K := K) 0
      letI : AddCommGroup T.Carrier := T.addCommGroup
      letI : Module K T.Carrier := T.module
      have hsub : Subsingleton (Fin 0 → K) := ⟨by
        intro x y
        funext i
        exact Fin.elim0 i⟩
      change determinantClass
          (zeroCoordinateQuadraticSpace (K := K))
          (QuadraticSpace.zeroCoordinateBasisLattice (K := K)) = _
      rw [determinantClass_eq_one_of_subsingleton _ _ hsub]
      simp [unitSquareClass_one]
  | succ k ih =>
      let T := QuadraticLatticeModel.halfHyperbolicTower (K := K) (k + 1)
      letI : AddCommGroup T.Carrier := T.addCommGroup
      letI : Module K T.Carrier := T.module
      have ih' : determinantClass
          (halfHyperbolicExtensionForm
            (zeroCoordinateQuadraticSpace (K := K)) k)
          (halfHyperbolicExtensionLattice
            (QuadraticSpace.zeroCoordinateBasisLattice (K := K)) k) =
          unitSquareClass K (((-1 : Kˣ) ^ k) *
            (dyadicHalfUnit (K := K)) ^ (2 * k)) := by
        dsimp only [QuadraticLatticeModel.halfHyperbolicTower,
          QuadraticLatticeModel.zeroModel,
          QuadraticLatticeModel.adjoinHalfHyperbolic] at ih
        exact ih
      change determinantClass
          (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
            (dyadicHalfUnit (K := K))).orthogonalSum
            (halfHyperbolicExtensionForm
              (zeroCoordinateQuadraticSpace (K := K)) k))
          (product (hyperbolicPlaneLattice (K := K))
            (halfHyperbolicExtensionLattice
              (QuadraticSpace.zeroCoordinateBasisLattice (K := K)) k)) = _
      rw [determinantClass_orthogonalProduct,
        determinantClass_eq_of_isometry
          (scaledZeroOmearaPlaneLatticeIsometry
            (dyadicHalfUnit (K := K))),
        determinantClass_hyperbolicPlaneLattice, ih',
        ← unitSquareClass_mul]
      apply congrArg (unitSquareClass K)
      have hneg : (-1 : Kˣ) ^ (k + 1) =
          (-1 : Kˣ) ^ k * (-1 : Kˣ) := pow_succ _ _
      have hhalf : (dyadicHalfUnit (K := K)) ^ (2 * (k + 1)) =
          (dyadicHalfUnit (K := K)) ^ (2 * k) *
            (dyadicHalfUnit (K := K)) ^ 2 := by
        rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
      rw [hneg, hhalf]
      ac_rfl

end Lattice

namespace BONG.GoodBONG

/-- The canonical good BONG on the standard tower has Beli's alternating
`0,-2e` order sequence. -/
theorem standardHalfHyperbolicTowerBONG_orderPattern
    {k : Nat} (hk : 1 ≤ k) : by
    let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) k
    letI : AddCommGroup T.Carrier := T.addCommGroup
    letI : Module K T.Carrier := T.module
    exact (standardHalfHyperbolicTowerBONG (K := K) k).HasHalfModularOrderPattern := by
  let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) k
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  apply (standardHalfHyperbolicTowerBONG (K := K) k).beliUniversalLemma46 hk |>.1
  exact Lattice.halfHyperbolicTower_isHalfModularWithUnitNorm
    (K := K) hk

/-- The ordinary signed determinant of the canonical tower BONG is a
square.  Equivalently, the determinant of its ambient space is `(-1)^k`
in `K×/(K×)^2`, exactly as in the first determinant clause of Beli's
Lemma 4.6. -/
theorem standardHalfHyperbolicTowerBONG_signedProduct_isSquare
    (k : Nat) : by
    let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) k
    letI : AddCommGroup T.Carrier := T.addCommGroup
    letI : Module K T.Carrier := T.module
    let b := standardHalfHyperbolicTowerBONG (K := K) k
    exact IsSquare (b.toBONG.signedEvenPrefixProduct k) := by
  let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) k
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  let b := standardHalfHyperbolicTowerBONG (K := K) k
  change IsSquare (b.toBONG.signedEvenPrefixProduct k)
  have hdet := Lattice.determinantClass_toSquareClass_eq_valueProduct b.toBONG
  rw [Lattice.determinantClass_halfHyperbolicTower (K := K) k,
    unitSquareClassToSquareClass_apply] at hdet
  let half := Lattice.dyadicHalfUnit (K := K)
  have hproduct : IsSquare
      (((-1 : Kˣ) ^ k * half ^ (2 * k)) * b.toBONG.valueProduct) :=
    isSquare_mul_of_squareClass_eq _ _ hdet
  have hhalf : IsSquare (half ^ (2 * k)) := by
    refine ⟨half ^ k, ?_⟩
    rw [← pow_add]
    congr 1
    omega
  have hsigned := hproduct.div hhalf
  have hcancel :
      ((((-1 : Kˣ) ^ k * half ^ (2 * k)) * b.toBONG.valueProduct) /
          half ^ (2 * k)) =
        (-1 : Kˣ) ^ k * b.toBONG.valueProduct := by
    calc
      (((-1 : Kˣ) ^ k * half ^ (2 * k)) * b.toBONG.valueProduct) /
          half ^ (2 * k) =
          (((-1 : Kˣ) ^ k * b.toBONG.valueProduct) *
            half ^ (2 * k)) / half ^ (2 * k) := by
            congr 1
            ac_rfl
      _ = (-1 : Kˣ) ^ k * b.toBONG.valueProduct :=
        mul_div_cancel_right _ _
  rw [hcancel] at hsigned
  unfold BONG.signedEvenPrefixProduct
  have hp := b.prefixProduct_eq_valueProduct_of_rank_le (2 * k) le_rfl
  change b.toBONG.prefixProduct (2 * k) = b.toBONG.valueProduct at hp
  rw [hp]
  exact hsigned

end BONG.GoodBONG

end Bong
