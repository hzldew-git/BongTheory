/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328EqualOrderConditionIIHyperbolic
import Bong.Lattice.WeightIdealRescale

/-!
# Absorbing the two rho-twists in O'Meara 93:28, Step 4

In the non-condition-(ii) branch, the equal-order inequality places both
negative rho-twists in the norm group of the normalized second component.
Two explicit applications of 93:19 then replace the twisted odd quaternary
model by the untwisted model while preserving a modular rank-four tail.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

variable [laws : DyadicDiscriminantClassLaws K]

/-- The coefficient `4 rho / a` in the twisted model of 93:18(vi),
bundled as a nonzero scalar. -/
noncomputable def scratch_omearaRhoTwistUnit (a : Kˣ) : Kˣ :=
  Units.mk0 ((4 : K) * laws.rho * (a : K)⁻¹) <| by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (ne_zero_of_isValuationUnit laws.rho_isValuationUnit))
      (inv_ne_zero (Units.ne_zero a))

@[simp]
theorem scratch_omearaRhoTwistUnit_coe (a : Kˣ) :
    (scratch_omearaRhoTwistUnit a : K) =
      (4 : K) * laws.rho * (a : K)⁻¹ :=
  rfl

theorem scratch_omearaRhoTwistUnit_order (a : Kˣ) :
    ordUnit K (scratch_omearaRhoTwistUnit a) =
      2 * (ramificationIndex K : Int) - ordUnit K a := by
  have hfour : ord K (4 : K) =
      (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) := by
    rw [show (4 : K) = 2 * 2 by norm_num, ord_mul,
      ← ramificationIndex_spec]
    norm_cast
    ring
  have hrho : ord K laws.rho = 0 := laws.rho_isValuationUnit
  apply WithTop.coe_injective
  rw [coe_ordUnit]
  simp only [scratch_omearaRhoTwistUnit_coe, ord_mul,
    hfour, hrho, AddValuation.map_inv,
    ← coe_ordUnit]
  norm_cast

theorem scratch_neg_omearaRhoTwistUnit_order (a : Kˣ) :
    ordUnit K (-scratch_omearaRhoTwistUnit a) =
      2 * (ramificationIndex K : Int) - ordUnit K a := by
  apply WithTop.coe_injective
  rw [coe_ordUnit, Units.val_neg, ord_neg, ← coe_ordUnit,
    scratch_omearaRhoTwistUnit_order]

namespace Omeara9319ExchangeSetup

universe w

variable {W : Type w} [AddCommGroup W] [Module K W]
  {r : QuadraticSpace K W} {M : Lattice K W} {s : Kˣ}

/-- If the binary exchange complement has values in the norm ideal of
the old modular tail, the final complement produced by 93:19 has the
same norm generator as that tail. -/
theorem coefficientShift_complement_normGenerator_of_exchangeComplement_le
    (E : Omeara9319ExchangeSetup r M s)
    (hM : IsModular r M s) (hrank : 3 ≤ finrank K W)
    (delta : Kˣ) (hdelta : IsNormGeneratorValue r M delta)
    (hle : normIdeal E.exchangeComplement
        (hyperbolicPlaneLattice (K := K)) ≤
      principalIdeal (K := K) (delta : K)) :
    let D := E.coefficientShift hM hrank
    IsNormGeneratorValue
      (D.splitting.decomposition.component 1).space
      (D.splitting.decomposition.component 1).lattice delta := by
  let D := E.coefficientShift hM hrank
  let ambient := E.exchangeComplement.orthogonalSum r
  let ambientLattice : Lattice K ((Fin 2 → K) × W) :=
    product (hyperbolicPlaneLattice (K := K)) M
  have hambientIdeal : normIdeal ambient ambientLattice =
      principalIdeal (K := K) (delta : K) := by
    change normIdeal (E.exchangeComplement.orthogonalSum r)
        (product (hyperbolicPlaneLattice (K := K)) M) = _
    rw [normIdeal_orthogonalProduct, hdelta.2]
    exact sup_eq_right.mpr hle
  have hdeltaAmbient : (delta : K) ∈
      normGroupSet ambient ambientLattice := by
    change (delta : K) ∈ normGroupSet
      (E.exchangeComplement.orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) M)
    rw [mem_normGroupSet_orthogonalProduct_iff]
    exact ⟨0, zero_mem_normGroupSet E.exchangeComplement
      (hyperbolicPlaneLattice (K := K)), (delta : K), hdelta.1, by simp⟩
  have hambientGenerator : IsNormGeneratorValue ambient ambientLattice delta :=
    ⟨hdeltaAmbient, hambientIdeal⟩
  letI : Module.Finite K W := M.moduleFinite
  have hcomplementRank :
      finrank K (D.splitting.decomposition.component 1).carrier =
        finrank K W := by
    rw [D.splitting.complement_finrank, Module.finrank_prod,
      Module.finrank_fin_fun]
    omega
  have hexists : ∃ a : Kˣ, IsNormGeneratorValue
      (D.splitting.decomposition.component 1).space
      (D.splitting.decomposition.component 1).lattice a := by
    rcases exists_isNormGenerator_of_finrank_pos
        (D.splitting.decomposition.component 1).space
        (D.splitting.decomposition.component 1).lattice
        (by rw [hcomplementRank]; omega) with ⟨x, hx, hne⟩
    exact ⟨Units.mk0
      ((D.splitting.decomposition.component 1).space.quadratic x) hne,
      hx.isNormGeneratorValue hne⟩
  exact JordanDecomposition.isNormGeneratorValue_of_normGroupSet_eq
    hambientGenerator
    (D.splitting.complement_normGroupSet_eq
      (by rw [hcomplementRank]; omega)).symm hexists

end Omeara9319ExchangeSetup

namespace Omeara9318RankFourModelParameters

universe w

variable {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K W} {L : Lattice K W} {s : Kˣ}

/-- First 93:19 exchange in Step 4: absorb the twist of the right binary
factor into the following rank-four component. -/
noncomputable def scratch_rightTwistSetup
    (P : Omeara9318RankFourModelParameters K)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :
    Omeara9319ExchangeSetup q L s := by
  apply Omeara9319ExchangeSetup.ofRepresentedScalar hL (by omega)
    P.kData.rightTail (P.b : K)
      ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K)
  · exact P.kData.rightTail_integral
  · exact P.b_integral
  · exact hs
  · simpa only [Omeara9318RankFourModelParameters.kData,
      mul_comm] using P.kData.right_determinant_unit
  · exact hright

@[simp]
theorem scratch_rightTwistSetup_alpha
    (P : Omeara9318RankFourModelParameters K)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :
    (P.scratch_rightTwistSetup hL hrank hs hright).alpha =
      P.kData.rightTail := rfl

@[simp]
theorem scratch_rightTwistSetup_beta
    (P : Omeara9318RankFourModelParameters K)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :
    (P.scratch_rightTwistSetup hL hrank hs hright).beta = (P.b : K) := rfl

@[simp]
theorem scratch_rightTwistSetup_newCoefficient
    (P : Omeara9318RankFourModelParameters K)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :
    let E := P.scratch_rightTwistSetup hL hrank hs hright
    E.alpha + (s : K) * E.gamma = 0 := by
  let E := P.scratch_rightTwistSetup hL hrank hs hright
  change E.alpha + (s : K) * E.gamma = 0
  rw [← E.delta_eq]
  change P.kData.rightTail +
      ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) = 0
  simp [Omeara9318RankFourModelParameters.kData,
    scratch_omearaRhoTwistUnit]

noncomputable def scratch_rightTwistData
    (P : Omeara9318RankFourModelParameters K)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :=
  (P.scratch_rightTwistSetup hL hrank hs hright).coefficientShift
    hL (by omega)

/-- Swap the displayed twisted right factor into the orientation expected
by the coefficient-shift construction. -/
noncomputable def scratch_kRightToRightOldPlaneIsometry
    (P : Omeara9318RankFourModelParameters K)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :
    let E := P.scratch_rightTwistSetup hL hrank hs hright
    Isometry P.kData.rightSpace E.oldPlane
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) := by
  let E := P.scratch_rightTwistSetup hL hrank hs hright
  change Isometry P.kData.rightSpace E.oldPlane
    (hyperbolicPlaneLattice (K := K))
    (hyperbolicPlaneLattice (K := K))
  dsimp only [E]
  let f := omearaGeneralPlaneSwapLatticeIsometry
    (P.b : K) P.kData.rightTail P.kData.right_nondegenerate
  simpa only [OmearaOddQuaternaryModelData.rightSpace,
    Omeara9318RankFourModelParameters.kData,
    Omeara9319ExchangeSetup.oldPlane,
    scratch_rightTwistSetup_alpha, scratch_rightTwistSetup_beta] using f

/-- After the exchange, swapping back identifies the new zero-left plane
with the untwisted right factor of `J`. -/
noncomputable def scratch_rightNewPlaneToJRightIsometry
    (P : Omeara9318RankFourModelParameters K)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :
    let E := P.scratch_rightTwistSetup hL hrank hs hright
    Isometry E.newPlane P.jData.rightSpace
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) := by
  let E := P.scratch_rightTwistSetup hL hrank hs hright
  change Isometry E.newPlane P.jData.rightSpace
    (hyperbolicPlaneLattice (K := K))
    (hyperbolicPlaneLattice (K := K))
  have hcoefficient : E.alpha + (s : K) * E.gamma = 0 :=
    P.scratch_rightTwistSetup_newCoefficient hL hrank hs hright
  dsimp only [E] at hcoefficient ⊢
  let f := omearaGeneralPlaneSwapLatticeIsometry
    (0 : K) (P.b : K) (by simp)
  simpa only [Omeara9319ExchangeSetup.newPlane,
    scratch_rightTwistSetup_beta,
    hcoefficient,
    OmearaOddQuaternaryModelData.rightSpace,
    Omeara9318RankFourModelParameters.jData] using f

/-- Complete right-factor twist absorption. -/
noncomputable def scratch_rightTwistIsometry
    (P : Omeara9318RankFourModelParameters K)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :
    let D := P.scratch_rightTwistData hL hrank hs hright
    Isometry (P.kData.rightSpace.orthogonalSum q)
      (P.jData.rightSpace.orthogonalSum
        (D.splitting.decomposition.component 1).space)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K))
        (D.splitting.decomposition.component 1).lattice) := by
  let E := P.scratch_rightTwistSetup hL hrank hs hright
  let D := P.scratch_rightTwistData hL hrank hs hright
  change Isometry (P.kData.rightSpace.orthogonalSum q)
    (P.jData.rightSpace.orthogonalSum
      (D.splitting.decomposition.component 1).space)
    (product (hyperbolicPlaneLattice (K := K)) L)
    (product (hyperbolicPlaneLattice (K := K))
      (D.splitting.decomposition.component 1).lattice)
  exact
    (Isometry.orthogonalProductBasic
      (P.scratch_kRightToRightOldPlaneIsometry hL hrank hs hright)
      (Isometry.refl q L)).trans <|
      D.shifted.trans <|
        Isometry.orthogonalProductBasic
          (P.scratch_rightNewPlaneToJRightIsometry hL hrank hs hright)
            (Isometry.refl
              (D.splitting.decomposition.component 1).space
              (D.splitting.decomposition.component 1).lattice)

theorem scratch_rightTwistComplement_finrank
    (P : Omeara9318RankFourModelParameters K)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :
    let D := P.scratch_rightTwistData hL hrank hs hright
    finrank K (D.splitting.decomposition.component 1).carrier = 4 := by
  let D := P.scratch_rightTwistData hL hrank hs hright
  change finrank K (D.splitting.decomposition.component 1).carrier = 4
  letI : Module.Finite K W := L.moduleFinite
  rw [D.splitting.complement_finrank, Module.finrank_prod,
    Module.finrank_fin_fun, hrank]

/-- Second 93:19 setup, now absorbing the twist in the left binary factor
into the complement produced by the first exchange. -/
noncomputable def scratch_leftTwistSetup
    (P : Omeara9318RankFourModelParameters K)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hleft : ((-scratch_omearaRhoTwistUnit P.a : Kˣ) : K) ∈
      normGroupSet q L)
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :
    let D := P.scratch_rightTwistData hL hrank hs hright
    Omeara9319ExchangeSetup
      (D.splitting.decomposition.component 1).space
      (D.splitting.decomposition.component 1).lattice s := by
  let D := P.scratch_rightTwistData hL hrank hs hright
  apply Omeara9319ExchangeSetup.ofRepresentedScalar
    D.splitting.complement_modular
      (by rw [P.scratch_rightTwistComplement_finrank hL hrank hs hright]; omega)
    P.kData.leftTail (P.a : K)
      ((-scratch_omearaRhoTwistUnit P.a : Kˣ) : K)
  · exact P.kData.leftTail_integral
  · exact P.a_integral
  · exact hs
  · simpa only [Omeara9318RankFourModelParameters.kData,
      mul_comm] using P.kData.left_determinant_unit
  · exact D.normGroup_subset hleft

@[simp]
theorem scratch_leftTwistSetup_alpha
    (P : Omeara9318RankFourModelParameters K)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hleft : ((-scratch_omearaRhoTwistUnit P.a : Kˣ) : K) ∈
      normGroupSet q L)
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :
    let E := P.scratch_leftTwistSetup hL hrank hs hleft hright
    E.alpha = P.kData.leftTail := rfl

@[simp]
theorem scratch_leftTwistSetup_beta
    (P : Omeara9318RankFourModelParameters K)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hleft : ((-scratch_omearaRhoTwistUnit P.a : Kˣ) : K) ∈
      normGroupSet q L)
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :
    let E := P.scratch_leftTwistSetup hL hrank hs hleft hright
    E.beta = (P.a : K) := rfl

@[simp]
theorem scratch_leftTwistSetup_newCoefficient
    (P : Omeara9318RankFourModelParameters K)
    (hAlpha : P.alpha = 0)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hleft : ((-scratch_omearaRhoTwistUnit P.a : Kˣ) : K) ∈
      normGroupSet q L)
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :
    let E := P.scratch_leftTwistSetup hL hrank hs hleft hright
    E.alpha + (s : K) * E.gamma = 0 := by
  let E := P.scratch_leftTwistSetup hL hrank hs hleft hright
  change E.alpha + (s : K) * E.gamma = 0
  rw [← E.delta_eq]
  change P.kData.leftTail +
      ((-scratch_omearaRhoTwistUnit P.a : Kˣ) : K) = 0
  simp [Omeara9318RankFourModelParameters.kData,
    scratch_omearaRhoTwistUnit, hAlpha]

noncomputable def scratch_leftTwistData
    (P : Omeara9318RankFourModelParameters K)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hleft : ((-scratch_omearaRhoTwistUnit P.a : Kˣ) : K) ∈
      normGroupSet q L)
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :=
  let R := P.scratch_rightTwistData hL hrank hs hright
  (P.scratch_leftTwistSetup hL hrank hs hleft hright).coefficientShift
    R.splitting.complement_modular
    (by rw [P.scratch_rightTwistComplement_finrank hL hrank hs hright]; omega)

noncomputable def scratch_kLeftToLeftOldPlaneIsometry
    (P : Omeara9318RankFourModelParameters K)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hleft : ((-scratch_omearaRhoTwistUnit P.a : Kˣ) : K) ∈
      normGroupSet q L)
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :
    let E := P.scratch_leftTwistSetup hL hrank hs hleft hright
    Isometry P.kData.leftSpace E.oldPlane
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) := by
  let E := P.scratch_leftTwistSetup hL hrank hs hleft hright
  change Isometry P.kData.leftSpace E.oldPlane
    (hyperbolicPlaneLattice (K := K))
    (hyperbolicPlaneLattice (K := K))
  dsimp only [E]
  let f := omearaGeneralPlaneSwapLatticeIsometry
    (P.a : K) P.kData.leftTail P.kData.left_nondegenerate
  simpa only [OmearaOddQuaternaryModelData.leftSpace,
    Omeara9318RankFourModelParameters.kData,
    Omeara9319ExchangeSetup.oldPlane,
    scratch_leftTwistSetup_alpha, scratch_leftTwistSetup_beta] using f

noncomputable def scratch_leftNewPlaneToJLeftIsometry
    (P : Omeara9318RankFourModelParameters K)
    (hAlpha : P.alpha = 0)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hleft : ((-scratch_omearaRhoTwistUnit P.a : Kˣ) : K) ∈
      normGroupSet q L)
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :
    let E := P.scratch_leftTwistSetup hL hrank hs hleft hright
    Isometry E.newPlane P.jData.leftSpace
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) := by
  let E := P.scratch_leftTwistSetup hL hrank hs hleft hright
  change Isometry E.newPlane P.jData.leftSpace
    (hyperbolicPlaneLattice (K := K))
    (hyperbolicPlaneLattice (K := K))
  have hcoefficient : E.alpha + (s : K) * E.gamma = 0 :=
    P.scratch_leftTwistSetup_newCoefficient hAlpha hL hrank hs hleft hright
  dsimp only [E] at hcoefficient ⊢
  let f := omearaGeneralPlaneSwapLatticeIsometry
    (0 : K) (P.a : K) (by simp)
  simpa only [Omeara9319ExchangeSetup.newPlane,
    scratch_leftTwistSetup_beta, hcoefficient,
    OmearaOddQuaternaryModelData.leftSpace,
    Omeara9318RankFourModelParameters.jData, hAlpha,
    neg_zero, zero_mul] using f

noncomputable def scratch_leftTwistIsometry
    (P : Omeara9318RankFourModelParameters K)
    (hAlpha : P.alpha = 0)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hleft : ((-scratch_omearaRhoTwistUnit P.a : Kˣ) : K) ∈
      normGroupSet q L)
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :
    let R := P.scratch_rightTwistData hL hrank hs hright
    let D := P.scratch_leftTwistData hL hrank hs hleft hright
    Isometry
      (P.kData.leftSpace.orthogonalSum
        (R.splitting.decomposition.component 1).space)
      (P.jData.leftSpace.orthogonalSum
        (D.splitting.decomposition.component 1).space)
      (product (hyperbolicPlaneLattice (K := K))
        (R.splitting.decomposition.component 1).lattice)
      (product (hyperbolicPlaneLattice (K := K))
        (D.splitting.decomposition.component 1).lattice) := by
  let R := P.scratch_rightTwistData hL hrank hs hright
  let E := P.scratch_leftTwistSetup hL hrank hs hleft hright
  let D := P.scratch_leftTwistData hL hrank hs hleft hright
  change Isometry
    (P.kData.leftSpace.orthogonalSum
      (R.splitting.decomposition.component 1).space)
    (P.jData.leftSpace.orthogonalSum
      (D.splitting.decomposition.component 1).space)
    (product (hyperbolicPlaneLattice (K := K))
      (R.splitting.decomposition.component 1).lattice)
    (product (hyperbolicPlaneLattice (K := K))
      (D.splitting.decomposition.component 1).lattice)
  exact
    (Isometry.orthogonalProductBasic
      (P.scratch_kLeftToLeftOldPlaneIsometry hL hrank hs hleft hright)
      (Isometry.refl (R.splitting.decomposition.component 1).space
        (R.splitting.decomposition.component 1).lattice)).trans <|
      D.shifted.trans <|
        Isometry.orthogonalProductBasic
          (P.scratch_leftNewPlaneToJLeftIsometry hAlpha hL hrank hs
            hleft hright)
          (Isometry.refl (D.splitting.decomposition.component 1).space
            (D.splitting.decomposition.component 1).lattice)

/-- The two coefficient exchanges remove both `rho`-twists from the
rank-four `K`-model, leaving the untwisted `J`-model and a new modular
rank-four complement. -/
noncomputable def scratch_twistAbsorptionIsometry
    (P : Omeara9318RankFourModelParameters K)
    (hAlpha : P.alpha = 0)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hleft : ((-scratch_omearaRhoTwistUnit P.a : Kˣ) : K) ∈
      normGroupSet q L)
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :
    let D := P.scratch_leftTwistData hL hrank hs hleft hright
    Isometry
      (P.kData.space.orthogonalSum q)
      (P.jData.space.orthogonalSum
        (D.splitting.decomposition.component 1).space)
      (product P.kData.lattice L)
      (product P.jData.lattice
        (D.splitting.decomposition.component 1).lattice) := by
  let R := P.scratch_rightTwistData hL hrank hs hright
  let D := P.scratch_leftTwistData hL hrank hs hleft hright
  let exposeRight : Isometry
      (P.kData.space.orthogonalSum q)
      (P.kData.leftSpace.orthogonalSum
        (P.kData.rightSpace.orthogonalSum q))
      (product P.kData.lattice L)
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K)) L)) :=
    orthogonalProductAssoc
  let shiftRight : Isometry
      (P.kData.leftSpace.orthogonalSum
        (P.kData.rightSpace.orthogonalSum q))
      (P.kData.leftSpace.orthogonalSum
        (P.jData.rightSpace.orthogonalSum
          (R.splitting.decomposition.component 1).space))
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K)) L))
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K))
          (R.splitting.decomposition.component 1).lattice)) :=
    Isometry.orthogonalProductBasic
      (Isometry.refl P.kData.leftSpace
        (hyperbolicPlaneLattice (K := K)))
      (P.scratch_rightTwistIsometry hL hrank hs hright)
  let rotateRight : Isometry
      (P.kData.leftSpace.orthogonalSum
        (P.jData.rightSpace.orthogonalSum
          (R.splitting.decomposition.component 1).space))
      ((P.jData.rightSpace.orthogonalSum P.kData.leftSpace)
        |>.orthogonalSum
          (R.splitting.decomposition.component 1).space)
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K))
          (R.splitting.decomposition.component 1).lattice))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (hyperbolicPlaneLattice (K := K)))
        (R.splitting.decomposition.component 1).lattice) :=
    orthogonalProductRotateLeft
  let hideRight : Isometry
      ((P.jData.rightSpace.orthogonalSum P.kData.leftSpace)
        |>.orthogonalSum
          (R.splitting.decomposition.component 1).space)
      (P.jData.rightSpace.orthogonalSum
        (P.kData.leftSpace.orthogonalSum
          (R.splitting.decomposition.component 1).space))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (hyperbolicPlaneLattice (K := K)))
        (R.splitting.decomposition.component 1).lattice)
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K))
          (R.splitting.decomposition.component 1).lattice)) :=
    orthogonalProductAssoc
  let shiftLeft : Isometry
      (P.jData.rightSpace.orthogonalSum
        (P.kData.leftSpace.orthogonalSum
          (R.splitting.decomposition.component 1).space))
      (P.jData.rightSpace.orthogonalSum
        (P.jData.leftSpace.orthogonalSum
          (D.splitting.decomposition.component 1).space))
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K))
          (R.splitting.decomposition.component 1).lattice))
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K))
          (D.splitting.decomposition.component 1).lattice)) :=
    Isometry.orthogonalProductBasic
      (Isometry.refl P.jData.rightSpace
        (hyperbolicPlaneLattice (K := K)))
      (P.scratch_leftTwistIsometry hAlpha hL hrank hs hleft hright)
  let restoreOrder : Isometry
      (P.jData.rightSpace.orthogonalSum
        (P.jData.leftSpace.orthogonalSum
          (D.splitting.decomposition.component 1).space))
      (P.jData.space.orthogonalSum
        (D.splitting.decomposition.component 1).space)
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K))
          (D.splitting.decomposition.component 1).lattice))
      (product P.jData.lattice
        (D.splitting.decomposition.component 1).lattice) :=
    orthogonalProductRotateLeft
  exact exposeRight.trans <| shiftRight.trans <| rotateRight.trans <|
    hideRight.trans <| shiftLeft.trans restoreOrder

theorem scratch_twistAbsorptionComplement_finrank
    (P : Omeara9318RankFourModelParameters K)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hleft : ((-scratch_omearaRhoTwistUnit P.a : Kˣ) : K) ∈
      normGroupSet q L)
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :
    let D := P.scratch_leftTwistData hL hrank hs hleft hright
    finrank K (D.splitting.decomposition.component 1).carrier = 4 := by
  let R := P.scratch_rightTwistData hL hrank hs hright
  let D := P.scratch_leftTwistData hL hrank hs hleft hright
  change finrank K (D.splitting.decomposition.component 1).carrier = 4
  letI : Module.Finite K W := L.moduleFinite
  rw [D.splitting.complement_finrank, Module.finrank_prod,
    Module.finrank_fin_fun, P.scratch_rightTwistComplement_finrank
      hL hrank hs hright]

theorem scratch_twistAbsorption_normGroup_subset
    (P : Omeara9318RankFourModelParameters K)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hleft : ((-scratch_omearaRhoTwistUnit P.a : Kˣ) : K) ∈
      normGroupSet q L)
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :
    let D := P.scratch_leftTwistData hL hrank hs hleft hright
    normGroupSet q L ⊆
      normGroupSet (D.splitting.decomposition.component 1).space
        (D.splitting.decomposition.component 1).lattice := by
  let R := P.scratch_rightTwistData hL hrank hs hright
  let D := P.scratch_leftTwistData hL hrank hs hleft hright
  exact R.normGroup_subset.trans D.normGroup_subset

/-- The first rho-twist exchange preserves a specified norm generator of
the modular tail, provided the three coefficients of the exchange
complement lie in its principal norm ideal. -/
theorem scratch_rightTwistComplement_normGenerator
    (P : Omeara9318RankFourModelParameters K)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L)
    (delta : Kˣ) (hdelta : IsNormGeneratorValue q L delta)
    (hrightTail : P.kData.rightTail ∈
      principalIdeal (K := K) (delta : K))
    (hrightScaleSq : (P.b : K) * (s : K) ^ 2 ∈
      principalIdeal (K := K) (delta : K)) :
    let R := P.scratch_rightTwistData hL hrank hs hright
    IsNormGeneratorValue
      (R.splitting.decomposition.component 1).space
      (R.splitting.decomposition.component 1).lattice delta := by
  let E := P.scratch_rightTwistSetup hL hrank hs hright
  let R := P.scratch_rightTwistData hL hrank hs hright
  change IsNormGeneratorValue
    (R.splitting.decomposition.component 1).space
    (R.splitting.decomposition.component 1).lattice delta
  apply E.coefficientShift_complement_normGenerator_of_exchangeComplement_le
    hL (by rw [hrank]; omega) delta hdelta
  apply E.exchangeComplement_normIdeal_le_of_newCoefficient_zero
    hL (by rw [hrank]; omega) delta hdelta
  · exact P.scratch_rightTwistSetup_newCoefficient hL hrank hs hright
  · simpa only [E, scratch_rightTwistSetup_alpha] using hrightTail
  · simpa only [E, scratch_rightTwistSetup_beta] using hrightScaleSq

/-- Both rho-twist exchanges preserve a specified norm generator of the
rank-four tail.  This is the norm-ideal invariant required in the
adjacent-norm-order case of 93:28, Step 6. -/
theorem scratch_twistAbsorption_tailNormGenerator
    (P : Omeara9318RankFourModelParameters K)
    (hAlpha : P.alpha = 0)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hleft : ((-scratch_omearaRhoTwistUnit P.a : Kˣ) : K) ∈
      normGroupSet q L)
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L)
    (delta : Kˣ) (hdelta : IsNormGeneratorValue q L delta)
    (hrightTail : P.kData.rightTail ∈
      principalIdeal (K := K) (delta : K))
    (hrightScaleSq : (P.b : K) * (s : K) ^ 2 ∈
      principalIdeal (K := K) (delta : K))
    (hleftTail : P.kData.leftTail ∈
      principalIdeal (K := K) (delta : K))
    (hleftScaleSq : (P.a : K) * (s : K) ^ 2 ∈
      principalIdeal (K := K) (delta : K)) :
    let D := P.scratch_leftTwistData hL hrank hs hleft hright
    IsNormGeneratorValue
      (D.splitting.decomposition.component 1).space
      (D.splitting.decomposition.component 1).lattice delta := by
  let R := P.scratch_rightTwistData hL hrank hs hright
  let E := P.scratch_leftTwistSetup hL hrank hs hleft hright
  let D := P.scratch_leftTwistData hL hrank hs hleft hright
  have hdeltaR : IsNormGeneratorValue
      (R.splitting.decomposition.component 1).space
      (R.splitting.decomposition.component 1).lattice delta :=
    P.scratch_rightTwistComplement_normGenerator hL hrank hs hright
      delta hdelta hrightTail hrightScaleSq
  change IsNormGeneratorValue
    (D.splitting.decomposition.component 1).space
    (D.splitting.decomposition.component 1).lattice delta
  apply E.coefficientShift_complement_normGenerator_of_exchangeComplement_le
    R.splitting.complement_modular
    (by rw [P.scratch_rightTwistComplement_finrank hL hrank hs hright]; omega)
    delta hdeltaR
  apply E.exchangeComplement_normIdeal_le_of_newCoefficient_zero
    R.splitting.complement_modular
    (by rw [P.scratch_rightTwistComplement_finrank hL hrank hs hright]; omega)
    delta hdeltaR
  · exact P.scratch_leftTwistSetup_newCoefficient
      hAlpha hL hrank hs hleft hright
  · simpa only [E, scratch_leftTwistSetup_alpha] using hleftTail
  · simpa only [E, scratch_leftTwistSetup_beta] using hleftScaleSq

/-- Universe-stable package for the result of the two coefficient
exchanges.  Bundling the final carrier and its algebraic instances keeps
the nested 93:18 complement opaque to later Jordan-replacement code. -/
structure RhoTwistAbsorptionData
    (P : Omeara9318RankFourModelParameters K)
    {W : Type w} [AddCommGroup W] [Module K W]
    (q : QuadraticSpace K W) (L : Lattice K W) (s : Kˣ) where
  Tail : Type (max u w)
  [tailAddCommGroup : AddCommGroup Tail]
  [tailModule : Module K Tail]
  tailSpace : QuadraticSpace K Tail
  tailLattice : Lattice K Tail
  pairIsometry : Isometry
    (P.kData.space.orthogonalSum q)
    (P.jData.space.orthogonalSum tailSpace)
    (product P.kData.lattice L)
    (product P.jData.lattice tailLattice)
  tailModular : IsModular tailSpace tailLattice s
  tailFinrank : finrank K Tail = 4
  normGroup_subset : normGroupSet q L ⊆
    normGroupSet tailSpace tailLattice
  tailNormGenerator_of : ∀ delta : Kˣ,
    IsNormGeneratorValue q L delta →
    P.kData.rightTail ∈ principalIdeal (K := K) (delta : K) →
    (P.b : K) * (s : K) ^ 2 ∈
      principalIdeal (K := K) (delta : K) →
    P.kData.leftTail ∈ principalIdeal (K := K) (delta : K) →
    (P.a : K) * (s : K) ^ 2 ∈
      principalIdeal (K := K) (delta : K) →
    IsNormGeneratorValue tailSpace tailLattice delta

attribute [instance] RhoTwistAbsorptionData.tailAddCommGroup
  RhoTwistAbsorptionData.tailModule

/-- Package the explicit double 93:19 calculation with a stable carrier
universe and all invariants needed by the first-pair Jordan replacement. -/
noncomputable def rhoTwistAbsorptionData
    (P : Omeara9318RankFourModelParameters K)
    (hAlpha : P.alpha = 0)
    (hL : IsModular q L s) (hrank : finrank K W = 4)
    (hs : IsInMaximalIdeal K (s : K))
    (hleft : ((-scratch_omearaRhoTwistUnit P.a : Kˣ) : K) ∈
      normGroupSet q L)
    (hright : ((-scratch_omearaRhoTwistUnit P.b : Kˣ) : K) ∈
      normGroupSet q L) :
    RhoTwistAbsorptionData P q L s := by
  let T := P.scratch_leftTwistData hL hrank hs hleft hright
  exact
    { Tail := (T.splitting.decomposition.component 1).carrier
      tailSpace := (T.splitting.decomposition.component 1).space
      tailLattice := (T.splitting.decomposition.component 1).lattice
      pairIsometry := P.scratch_twistAbsorptionIsometry
        hAlpha hL hrank hs hleft hright
      tailModular := T.splitting.complement_modular
      tailFinrank := P.scratch_twistAbsorptionComplement_finrank
        hL hrank hs hleft hright
      normGroup_subset := P.scratch_twistAbsorption_normGroup_subset
        hL hrank hs hleft hright
      tailNormGenerator_of := by
        intro delta hdelta hrightTail hrightScaleSq hleftTail hleftScaleSq
        exact P.scratch_twistAbsorption_tailNormGenerator hAlpha hL hrank hs
          hleft hright delta hdelta hrightTail hrightScaleSq
          hleftTail hleftScaleSq }

end Omeara9318RankFourModelParameters

end Lattice

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- A normalized scalar whose restored order reaches the second
fundamental weight belongs to the normalized second norm group. -/
theorem scratch_mem_targetSecondNormalized_of_weight_order_le
    (x : Kˣ)
    (hx : S.sourceJordan.fundamentalWeightOrder 1 ≤
      S.sourceJordan.fundamentalScaleOrder 0 + ordUnit K x) :
    (x : K) ∈ normGroupSet S.targetSecondNormalized
      (S.targetJordan.component 1).lattice := by
  rw [← S.secondNormalized_normGroupSet_eq,
    mem_normGroupSet_rescaleQuadraticUnit_iff]
  rw [S.sourceJordan_isSaturated 1]
  apply weightIdeal_subset_normGroupSet
    (S.sourceJordan.fundamentalNormGenerator 1)
    (S.sourceJordan.fundamentalNormGenerator_spec 1)
  change ((S.firstScale * x : Kˣ) : K) ∈
    S.sourceJordan.fundamentalWeightIdeal 1
  unfold fundamentalWeightIdeal
  rw [weightIdeal_eq_powerIdeal, mem_powerIdeal_iff,
    ← coe_ordUnit, ordUnit_mul]
  unfold fundamentalWeightOrder fundamentalScaleOrder at hx
  simp only [S.sourceJordan_scaleGenerator] at hx
  exact_mod_cast hx

theorem scratch_nontrigger_weight_order
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0)) :
    S.sourceJordan.fundamentalWeightOrder 1 ≤
      2 * (ramificationIndex K : Int) +
        2 * S.sourceJordan.fundamentalScaleOrder 0 -
          S.sourceJordan.fundamentalWeightOrder 0 := by
  rw [S.firstFundamentalIdeal_eq_rightNorm_mul_leftWeight_of_normalized_eq
    hgap] at hnontrigger
  unfold fourNormOverWeightIdealWith at hnontrigger
  rw [show boundaryRightIndex (0 : Fin (n + 1)) =
      (1 : Fin (n + 2)) by ext; rfl,
    fundamentalWeightIdeal, weightIdeal_eq_powerIdeal,
    scalarIdeal_powerIdeal_units, powerIdeal_lt_iff] at hnontrigger
  have hchoice : ordUnit K (A.value 1) =
      ordUnit K (S.sourceJordan.fundamentalNormGenerator 1) := by
    apply (principalIdeal_eq_iff_ordUnit_eq _ _).mp
    exact (A.spec 1).2.symm.trans
      (S.sourceJordan.fundamentalNormGenerator_spec 1).2
  rw [ordUnit_mul, ordUnit_inv,
    Omeara9328RankFourReductionSystem.secondNormalizedNormGenerator,
    ordUnit_mul, ordUnit_inv, hchoice] at hnontrigger
  unfold fundamentalWeightOrder at hnontrigger ⊢
  unfold fundamentalScaleOrder
  simp only [Omeara9328RankFourReductionSystem.firstScale,
    S.sourceJordan_scaleGenerator] at hnontrigger ⊢
  omega

/-- In the first-scale normalization, the weight order of the saturated
first component is the intrinsic fundamental weight order minus the first
scale order. -/
theorem scratch_firstNormalized_weightIdealOrder_eq :
    weightIdealOrder S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice =
      S.sourceJordan.fundamentalWeightOrder 0 -
        S.sourceJordan.fundamentalScaleOrder 0 := by
  have hcomponentWeight :
      weightIdeal (S.sourceJordan.component 0).space
          (S.sourceJordan.component 0).lattice =
        S.sourceJordan.fundamentalWeightIdeal 0 := by
    exact weightIdeal_eq_of_normGroupSet_eq_of_twoScaleIdeal_eq
      S.firstNormGenerator_source_unscaled
      ⟨S.firstScale * S.firstNormGenerator,
        S.firstNormGenerator_fundamental⟩
      (S.sourceJordan_isSaturated 0)
      (S.sourceJordan.componentTwoScaleIdeal_eq_fundamental 0)
  have hcomponentOrder :
      weightIdealOrder (S.sourceJordan.component 0).space
          (S.sourceJordan.component 0).lattice =
        S.sourceJordan.fundamentalWeightOrder 0 := by
    apply powerIdeal_order_eq_of_eq (K := K)
    calc
      powerIdeal (K := K)
          (weightIdealOrder (S.sourceJordan.component 0).space
            (S.sourceJordan.component 0).lattice) =
          weightIdeal (S.sourceJordan.component 0).space
            (S.sourceJordan.component 0).lattice :=
        (weightIdeal_eq_powerIdeal _ _).symm
      _ = S.sourceJordan.fundamentalWeightIdeal 0 := hcomponentWeight
      _ = powerIdeal (K := K)
          (S.sourceJordan.fundamentalWeightOrder 0) := by
        unfold fundamentalWeightIdeal fundamentalWeightOrder
        exact weightIdeal_eq_powerIdeal _ _
  have hrescale := weightIdealOrder_rescaleQuadraticUnit
    (S.firstScale * S.firstNormGenerator) S.firstScale⁻¹
      S.firstNormGenerator_source_unscaled
  change weightIdealOrder S.sourceFirstNormalized
      (S.sourceJordan.component 0).lattice = _
  rw [hrescale, ordUnit_inv, hcomponentOrder]
  unfold fundamentalScaleOrder
  simp only [S.sourceJordan_scaleGenerator,
    Omeara9328RankFourReductionSystem.firstScale]
  omega

/-- In the non-condition-(ii) half of Step 4, the negative twist attached
to any generator of the first normalized weight already belongs to the
normalized second norm group. -/
theorem scratch_neg_weightTwist_mem_targetSecondNormalized
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (b : Kˣ)
    (hb : ordUnit K b =
      weightIdealOrder S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice) :
    ((-scratch_omearaRhoTwistUnit b : Kˣ) : K) ∈
      normGroupSet S.targetSecondNormalized
        (S.targetJordan.component 1).lattice := by
  apply S.scratch_mem_targetSecondNormalized_of_weight_order_le
  have hnon := S.scratch_nontrigger_weight_order A hgap hnontrigger
  have hfirst := S.scratch_firstNormalized_weightIdealOrder_eq
  rw [scratch_neg_omearaRhoTwistUnit_order, hb, hfirst]
  omega

/-- The same nontrigger inequality also places the negative twist attached
to the first norm generator in the normalized second norm group. -/
theorem scratch_neg_normTwist_mem_targetSecondNormalized
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0)) :
    ((-scratch_omearaRhoTwistUnit S.firstNormGenerator : Kˣ) : K) ∈
      normGroupSet S.targetSecondNormalized
        (S.targetJordan.component 1).lattice := by
  apply S.scratch_mem_targetSecondNormalized_of_weight_order_le
  have hnon := S.scratch_nontrigger_weight_order A hgap hnontrigger
  have hfirst := S.scratch_firstNormalized_weightIdealOrder_eq
  have hnormLe := normGeneratorOrder_le_weightIdealOrder
    S.firstNormGenerator S.firstNormGenerator_source
  rw [scratch_neg_omearaRhoTwistUnit_order]
  rw [hfirst] at hnormLe
  omega

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- The left rho-twist of the `K`-model is represented by the corrected
normalized second component in the nontrigger branch. -/
theorem scratch_equalOrderKLeftTwist_mem
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.equalOrderErrorData A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
    ((-Lattice.scratch_omearaRhoTwistUnit N.parameters.a : Kˣ) : K) ∈
      normGroupSet D.newTail D.newTailLattice := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  change ((-Lattice.scratch_omearaRhoTwistUnit N.parameters.a : Kˣ) : K) ∈
    normGroupSet D.newTail D.newTailLattice
  apply D.tailShift.normGroup_subset
  rw [N.parameters_a]
  exact S.scratch_neg_normTwist_mem_targetSecondNormalized
    A hgap hnontrigger

/-- The right rho-twist is represented as well; its parameter is the
chosen generator of the first normalized weight ideal. -/
theorem scratch_equalOrderKRightTwist_mem
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.equalOrderErrorData A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
    ((-Lattice.scratch_omearaRhoTwistUnit N.parameters.b : Kˣ) : K) ∈
      normGroupSet D.newTail D.newTailLattice := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  change ((-Lattice.scratch_omearaRhoTwistUnit N.parameters.b : Kˣ) : K) ∈
    normGroupSet D.newTail D.newTailLattice
  apply D.tailShift.normGroup_subset
  apply S.scratch_neg_weightTwist_mem_targetSecondNormalized
    A hgap hnontrigger N.parameters.b
  rw [N.parameters_b, ordUnit_uniformizerPowerUnit,
    ← D.newHead_weightIdealOrder_eq_source]

/-
/-- In the twisted alternative of 93:18(vi), the determinant-corrected
normalized pair is integrally isometric to the untwisted `J`-head followed
by the twice-shifted tail. -/
noncomputable def scratch_equalOrderKNormalizedPairIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.equalOrderErrorData A conditions hgap
      let N := D.newHeadOddDeterminantOneData hodd
        (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
      IsIsometric D.newHead N.parameters.kData.space
        D.newHeadLattice N.parameters.kData.lattice) :
    let D := S.equalOrderErrorData A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
    let hleft := S.scratch_equalOrderKLeftTwist_mem A conditions hgap
      hnontrigger hodd
    let hright := S.scratch_equalOrderKRightTwist_mem A conditions hgap
      hnontrigger hodd
    let T := N.parameters.scratch_leftTwistData
      D.tailShift.splitting.complement_modular
      D.tailShift_complement_finrank
      S.relativeSecondScale_isInMaximalIdeal hleft hright
    Isometry
      (S.targetFirstNormalized.orthogonalSum S.targetSecondNormalized)
      (N.parameters.jData.space.orthogonalSum
        (T.splitting.decomposition.component 1).space)
      (product (S.targetJordan.component 0).lattice
        (S.targetJordan.component 1).lattice)
      (product N.parameters.jData.lattice
        (T.splitting.decomposition.component 1).lattice) := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  let hleft := S.scratch_equalOrderKLeftTwist_mem A conditions hgap
    hnontrigger hodd
  let hright := S.scratch_equalOrderKRightTwist_mem A conditions hgap
    hnontrigger hodd
  let T := N.parameters.scratch_leftTwistData
    D.tailShift.splitting.complement_modular
    D.tailShift_complement_finrank
    S.relativeSecondScale_isInMaximalIdeal hleft hright
  change Isometry
    (S.targetFirstNormalized.orthogonalSum S.targetSecondNormalized)
    (N.parameters.jData.space.orthogonalSum
      (T.splitting.decomposition.component 1).space)
    (product (S.targetJordan.component 0).lattice
      (S.targetJordan.component 1).lattice)
    (product N.parameters.jData.lattice
      (T.splitting.decomposition.component 1).lattice)
  let identifyK := (Classical.choice hk).orthogonalProductBasic
    (Isometry.refl D.newTail D.newTailLattice)
  let absorb := N.parameters.scratch_twistAbsorptionIsometry
    N.alpha_zero D.tailShift.splitting.complement_modular
    D.tailShift_complement_finrank
    S.relativeSecondScale_isInMaximalIdeal hleft hright
  exact D.normalizedPairIsometry.trans (identifyK.trans absorb)

theorem scratch_equalOrderKTwistComplement_finrank
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.equalOrderErrorData A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
    let hleft := S.scratch_equalOrderKLeftTwist_mem A conditions hgap
      hnontrigger hodd
    let hright := S.scratch_equalOrderKRightTwist_mem A conditions hgap
      hnontrigger hodd
    let T := N.parameters.scratch_leftTwistData
      D.tailShift.splitting.complement_modular
      D.tailShift_complement_finrank
      S.relativeSecondScale_isInMaximalIdeal hleft hright
    finrank K (T.splitting.decomposition.component 1).carrier = 4 := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  let hleft := S.scratch_equalOrderKLeftTwist_mem A conditions hgap
    hnontrigger hodd
  let hright := S.scratch_equalOrderKRightTwist_mem A conditions hgap
    hnontrigger hodd
  let T := N.parameters.scratch_leftTwistData
    D.tailShift.splitting.complement_modular
    D.tailShift_complement_finrank
    S.relativeSecondScale_isInMaximalIdeal hleft hright
  change finrank K (T.splitting.decomposition.component 1).carrier = 4
  exact N.parameters.scratch_twistAbsorptionComplement_finrank
    D.tailShift.splitting.complement_modular
    D.tailShift_complement_finrank
    S.relativeSecondScale_isInMaximalIdeal hleft hright

/-- The old corrected tail norm group embeds in the twice-shifted tail. -/
theorem scratch_equalOrderKTwist_normGroup_subset
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.equalOrderErrorData A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
    let hleft := S.scratch_equalOrderKLeftTwist_mem A conditions hgap
      hnontrigger hodd
    let hright := S.scratch_equalOrderKRightTwist_mem A conditions hgap
      hnontrigger hodd
    let T := N.parameters.scratch_leftTwistData
      D.tailShift.splitting.complement_modular
      D.tailShift_complement_finrank
      S.relativeSecondScale_isInMaximalIdeal hleft hright
    normGroupSet D.newTail D.newTailLattice ⊆
      normGroupSet (T.splitting.decomposition.component 1).space
        (T.splitting.decomposition.component 1).lattice := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  let hleft := S.scratch_equalOrderKLeftTwist_mem A conditions hgap
    hnontrigger hodd
  let hright := S.scratch_equalOrderKRightTwist_mem A conditions hgap
    hnontrigger hodd
  let T := N.parameters.scratch_leftTwistData
    D.tailShift.splitting.complement_modular
    D.tailShift_complement_finrank
    S.relativeSecondScale_isInMaximalIdeal hleft hright
  change normGroupSet D.newTail D.newTailLattice ⊆
    normGroupSet (T.splitting.decomposition.component 1).space
      (T.splitting.decomposition.component 1).lattice
  exact N.parameters.scratch_twistAbsorption_normGroup_subset
    D.tailShift.splitting.complement_modular
    D.tailShift_complement_finrank
    S.relativeSecondScale_isInMaximalIdeal hleft hright
-/

/-- Opaque result of the double rho-twist absorption in the nontrigger
odd branch of Step 4. -/
noncomputable def equalOrderKRhoTwistAbsorptionData
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.equalOrderErrorData A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
    Lattice.Omeara9318RankFourModelParameters.RhoTwistAbsorptionData
      N.parameters D.newTail D.newTailLattice S.relativeSecondScale := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  exact N.parameters.rhoTwistAbsorptionData N.alpha_zero
    D.tailShift.splitting.complement_modular
    D.tailShift_complement_finrank
    S.relativeSecondScale_isInMaximalIdeal
    (S.scratch_equalOrderKLeftTwist_mem A conditions hgap hnontrigger hodd)
    (S.scratch_equalOrderKRightTwist_mem A conditions hgap hnontrigger hodd)

/-- The determinant-corrected normalized target pair, in the twisted
93:18(vi) alternative, is replaced by the untwisted `J`-head and the
opaque twice-shifted tail. -/
noncomputable def equalOrderKNormalizedPairIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.equalOrderErrorData A conditions hgap
      let N := D.newHeadOddDeterminantOneData hodd
        (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
      IsIsometric D.newHead N.parameters.kData.space
        D.newHeadLattice N.parameters.kData.lattice) :
    let D := S.equalOrderErrorData A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
    let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
      hnontrigger hodd
    Isometry
      (S.targetFirstNormalized.orthogonalSum S.targetSecondNormalized)
      (N.parameters.jData.space.orthogonalSum B.tailSpace)
      (product (S.targetJordan.component 0).lattice
        (S.targetJordan.component 1).lattice)
      (product N.parameters.jData.lattice B.tailLattice) := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
    hnontrigger hodd
  change Isometry
    (S.targetFirstNormalized.orthogonalSum S.targetSecondNormalized)
    (N.parameters.jData.space.orthogonalSum B.tailSpace)
    (product (S.targetJordan.component 0).lattice
      (S.targetJordan.component 1).lattice)
    (product N.parameters.jData.lattice B.tailLattice)
  let identifyK := (Classical.choice hk).orthogonalProductBasic
    (Isometry.refl D.newTail D.newTailLattice)
  exact D.normalizedPairIsometry.trans (identifyK.trans B.pairIsometry)

/-- In the equal-order branch the corrected second generator and the
first normalized norm generator generate the same fractional ideal. -/
theorem equalOrder_secondGenerator_principalIdeal_eq_first
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator) :
    let D := S.equalOrderErrorData A conditions hgap
    principalIdeal (K := K) (D.secondGenerator : K) =
      principalIdeal (K := K) (S.firstNormGenerator : K) := by
  let D := S.equalOrderErrorData A conditions hgap
  apply (principalIdeal_eq_iff_ordUnit_eq D.secondGenerator
    S.firstNormGenerator).2
  change ordUnit K (S.secondNormalizedNormGeneratorWith A) =
    ordUnit K S.firstNormGenerator
  rw [S.secondNormalizedNormGeneratorWith_order_eq A, hgap]

/-- The normalized target first pair has norm ideal generated by the
first norm generator. -/
theorem equalOrder_normalizedTargetPair_normIdeal_eq_first
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator) :
    normIdeal
        (S.targetFirstNormalized.orthogonalSum S.targetSecondNormalized)
        (product (S.targetJordan.component 0).lattice
          (S.targetJordan.component 1).lattice) =
      principalIdeal (K := K) (S.firstNormGenerator : K) := by
  let D := S.equalOrderErrorData A conditions hgap
  rw [normIdeal_orthogonalProduct,
    S.firstNormGenerator_target.2,
    D.secondGenerator_targetSecond.2,
    S.equalOrder_secondGenerator_principalIdeal_eq_first
      A conditions hgap, sup_idem]

set_option maxHeartbeats 3000000 in
/-- Transporting the preceding equality through the twisted-pair
isometry determines the total norm ideal of the new displayed pair. -/
theorem equalOrderKNormalizedPair_normIdeal_eq_first
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.equalOrderErrorData A conditions hgap
      let N := D.newHeadOddDeterminantOneData hodd
        (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
      IsIsometric D.newHead N.parameters.kData.space
        D.newHeadLattice N.parameters.kData.lattice) :
    let D := S.equalOrderErrorData A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
    let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
      hnontrigger hodd
    normIdeal (N.parameters.jData.space.orthogonalSum B.tailSpace)
        (product N.parameters.jData.lattice B.tailLattice) =
      principalIdeal (K := K) (S.firstNormGenerator : K) := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
    hnontrigger hodd
  let f := S.equalOrderKNormalizedPairIsometry A conditions hgap
    hnontrigger hodd hk
  change normIdeal (N.parameters.jData.space.orthogonalSum B.tailSpace)
      (product N.parameters.jData.lattice B.tailLattice) = _
  calc
    normIdeal (N.parameters.jData.space.orthogonalSum B.tailSpace)
        (product N.parameters.jData.lattice B.tailLattice) =
        normIdeal (N.parameters.jData.space.orthogonalSum B.tailSpace)
          (map f.toLinearEquiv
            (product (S.targetJordan.component 0).lattice
              (S.targetJordan.component 1).lattice)) := by
      exact congrArg
        (normIdeal (N.parameters.jData.space.orthogonalSum B.tailSpace))
        f.map_eq.symm
    _ = normIdeal
        (S.targetFirstNormalized.orthogonalSum S.targetSecondNormalized)
        (product (S.targetJordan.component 0).lattice
          (S.targetJordan.component 1).lattice) :=
      normIdeal_map_isometry f.toQuadraticSpaceIsometry _
    _ = principalIdeal (K := K) (S.firstNormGenerator : K) :=
      S.equalOrder_normalizedTargetPair_normIdeal_eq_first
        A conditions hgap

set_option maxHeartbeats 3000000 in
/-- The twice-shifted tail still has the original second normalized norm
generator.  The upper bound follows from the total pair norm ideal, while
the lower bound is the explicit norm-group containment from the two
applications of 93:19. -/
theorem equalOrderKTail_normGenerator
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.equalOrderErrorData A conditions hgap
      let N := D.newHeadOddDeterminantOneData hodd
        (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
      IsIsometric D.newHead N.parameters.kData.space
        D.newHeadLattice N.parameters.kData.lattice) :
    let D := S.equalOrderErrorData A conditions hgap
    let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
      hnontrigger hodd
    IsNormGeneratorValue B.tailSpace B.tailLattice D.secondGenerator := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
    hnontrigger hodd
  change IsNormGeneratorValue B.tailSpace B.tailLattice D.secondGenerator
  have hmem : (D.secondGenerator : K) ∈
      normGroupSet B.tailSpace B.tailLattice :=
    B.normGroup_subset D.tailShift_complement_secondNormGenerator.1
  refine ⟨hmem, le_antisymm ?_ ?_⟩
  · calc
      normIdeal B.tailSpace B.tailLattice ≤
          normIdeal N.parameters.jData.space N.parameters.jData.lattice ⊔
            normIdeal B.tailSpace B.tailLattice := _root_.le_sup_right
      _ = normIdeal
          (N.parameters.jData.space.orthogonalSum B.tailSpace)
          (product N.parameters.jData.lattice B.tailLattice) :=
        normIdeal_orthogonalProduct.symm
      _ = principalIdeal (K := K) (S.firstNormGenerator : K) :=
        S.equalOrderKNormalizedPair_normIdeal_eq_first A conditions hgap
          hnontrigger hodd hk
      _ = principalIdeal (K := K) (D.secondGenerator : K) :=
        (S.equalOrder_secondGenerator_principalIdeal_eq_first
          A conditions hgap).symm
  · rw [principalIdeal, Submodule.span_singleton_le_iff_mem]
    exact normGroupSet_subset_normIdeal B.tailSpace B.tailLattice hmem

/-- Although the corrected head is the twisted `K`-model in this branch,
the untwisted `J`-model has exactly the source norm group.  The concrete
unimodular classification therefore gives an integral source-to-`J`
isometry. -/
noncomputable def equalOrderKSourceToJHeadIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.equalOrderErrorData A conditions hgap
      let N := D.newHeadOddDeterminantOneData hodd
        (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
      IsIsometric D.newHead N.parameters.kData.space
        D.newHeadLattice N.parameters.kData.lattice) :
    let D := S.equalOrderErrorData A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
    Isometry S.sourceFirstNormalized N.parameters.jData.space
      (S.sourceJordan.component 0).lattice
      N.parameters.jData.lattice := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  change Isometry S.sourceFirstNormalized N.parameters.jData.space
    (S.sourceJordan.component 0).lattice N.parameters.jData.lattice
  let kIso := Classical.choice hk
  have hgroup :
      normGroupSet S.sourceFirstNormalized
          (S.sourceJordan.component 0).lattice =
        normGroupSet N.parameters.jData.space
          N.parameters.jData.lattice := by
    calc
      normGroupSet S.sourceFirstNormalized
          (S.sourceJordan.component 0).lattice =
          normGroupSet D.newHead D.newHeadLattice :=
        D.newHead_normGroupSet_eq_source
      _ = normGroupSet N.parameters.kData.space
          N.parameters.kData.lattice :=
        normGroupSet_eq_of_latticeIsometry kIso.symm
      _ = integralSquareCoset (N.parameters.a : K)
          (principalIdeal (K := K) (N.parameters.b : K)) :=
        N.parameters.k_normGroupSet_eq
      _ = normGroupSet N.parameters.jData.space
          N.parameters.jData.lattice :=
        N.parameters.j_normGroupSet_eq.symm
  let fieldIso := S.sourceFirstNormalizedHyperbolicTowerIsometry.trans
    (N.parameters.jSpaceToHyperbolicTowerIsometry N.alpha_zero).symm
  exact latticeIsometryToUnimodularModel
    S.sourceFirstNormalized_unimodular N.parameters.jData.isModular
    fieldIso hgroup

/-- Untwisted head restored to the original first Jordan scale. -/
noncomputable abbrev equalOrderKHeadUnnormalized
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.equalOrderErrorData A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
    QuadraticSpace K ((Fin 2 → K) × (Fin 2 → K)) := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  exact N.parameters.jData.space.rescaleUnit S.firstScale

/-- Twice-shifted tail restored to the original second Jordan scale. -/
noncomputable abbrev equalOrderKTailUnnormalized
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity) :
    let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
      hnontrigger hodd
    QuadraticSpace K B.Tail := by
  let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
    hnontrigger hodd
  exact B.tailSpace.rescaleUnit S.firstScale

/-- Undo the common first-scale normalization on the complete pair after
the two rho-twists have been absorbed. -/
noncomputable def equalOrderKOriginalPairIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.equalOrderErrorData A conditions hgap
      let N := D.newHeadOddDeterminantOneData hodd
        (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
      IsIsometric D.newHead N.parameters.kData.space
        D.newHeadLattice N.parameters.kData.lattice) :
    let D := S.equalOrderErrorData A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
    let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
      hnontrigger hodd
    Isometry
      ((S.targetJordan.component 0).space.orthogonalSum
        (S.targetJordan.component 1).space)
      ((S.equalOrderKHeadUnnormalized A conditions hgap hodd).orthogonalSum
        (S.equalOrderKTailUnnormalized A conditions hgap
          hnontrigger hodd))
      (product (S.targetJordan.component 0).lattice
        (S.targetJordan.component 1).lattice)
      (product N.parameters.jData.lattice B.tailLattice) := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
    hnontrigger hodd
  let normalized := S.equalOrderKNormalizedPairIsometry A conditions hgap
    hnontrigger hodd hk
  let scaled := normalized.rescaleUnitBoth S.firstScale
  let distributeSource := rescaleUnitOrthogonalProductIsometry
    S.targetFirstNormalized S.targetSecondNormalized
    (S.targetJordan.component 0).lattice
    (S.targetJordan.component 1).lattice S.firstScale
  let undoFirst : Isometry
      (S.targetFirstNormalized.rescaleUnit S.firstScale)
      (S.targetJordan.component 0).space
      (S.targetJordan.component 0).lattice
      (S.targetJordan.component 0).lattice := by
    simpa only [targetFirstNormalized] using
      undoInverseRescaleLatticeIsometry
        (S.targetJordan.component 0).space
        (S.targetJordan.component 0).lattice S.firstScale
  let undoSecond : Isometry
      (S.targetSecondNormalized.rescaleUnit S.firstScale)
      (S.targetJordan.component 1).space
      (S.targetJordan.component 1).lattice
      (S.targetJordan.component 1).lattice := by
    simpa only [targetSecondNormalized] using
      undoInverseRescaleLatticeIsometry
        (S.targetJordan.component 1).space
        (S.targetJordan.component 1).lattice S.firstScale
  let undoSource := distributeSource.trans
    (undoFirst.orthogonalProductBasic undoSecond)
  let distributeTarget := rescaleUnitOrthogonalProductIsometry
    N.parameters.jData.space B.tailSpace
    N.parameters.jData.lattice B.tailLattice S.firstScale
  exact undoSource.symm.trans (scaled.trans distributeTarget)

theorem equalOrderKHeadUnnormalized_modular
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.equalOrderErrorData A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
    IsModular (S.equalOrderKHeadUnnormalized A conditions hgap hodd)
      N.parameters.jData.lattice (S.targetJordan.scaleGenerator 0) := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  have h := N.parameters.jData.isModular.rescaleQuadraticUnit S.firstScale
  simpa only [equalOrderKHeadUnnormalized,
    S.targetJordan_scaleGenerator,
    Omeara9328RankFourReductionSystem.firstScale, mul_one] using h

theorem equalOrderKTailUnnormalized_modular
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity) :
    let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
      hnontrigger hodd
    IsModular
      (S.equalOrderKTailUnnormalized A conditions hgap hnontrigger hodd)
      B.tailLattice (S.targetJordan.scaleGenerator 1) := by
  let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
    hnontrigger hodd
  have h := B.tailModular.rescaleQuadraticUnit S.firstScale
  simpa only [equalOrderKTailUnnormalized,
    EqualNormOrderErrorData.firstScale_mul_relativeSecondScale] using h

theorem equalOrderKHeadUnnormalized_scaleIdeal
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.equalOrderErrorData A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
    scaleIdeal (S.equalOrderKHeadUnnormalized A conditions hgap hodd)
        N.parameters.jData.lattice =
      principalIdeal (K := K) (S.targetJordan.scaleGenerator 0 : K) := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  exact (S.equalOrderKHeadUnnormalized_modular A conditions hgap hodd)
    |>.scaleIdeal_eq_principal (by
      simp only [Module.finrank_prod, Module.finrank_fin_fun]
      omega)

theorem equalOrderKTailUnnormalized_scaleIdeal
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity) :
    let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
      hnontrigger hodd
    scaleIdeal
        (S.equalOrderKTailUnnormalized A conditions hgap hnontrigger hodd)
        B.tailLattice =
      principalIdeal (K := K) (S.targetJordan.scaleGenerator 1 : K) := by
  let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
    hnontrigger hodd
  exact (S.equalOrderKTailUnnormalized_modular A conditions hgap
    hnontrigger hodd).scaleIdeal_eq_principal (by rw [B.tailFinrank]; omega)

theorem equalOrderKHeadUnnormalized_normGenerator
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.equalOrderErrorData A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
    IsNormGeneratorValue
      (S.equalOrderKHeadUnnormalized A conditions hgap hodd)
      N.parameters.jData.lattice
      (S.firstScale * S.firstNormGenerator) := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  change IsNormGeneratorValue
    (N.parameters.jData.space.rescaleUnit S.firstScale)
    N.parameters.jData.lattice (S.firstScale * S.firstNormGenerator)
  have h := N.parameters.jData.a_isNormGeneratorValue
    |>.rescaleQuadraticUnit S.firstScale
  simpa only [Omeara9318RankFourModelParameters.jData,
    N.parameters_a] using h

theorem equalOrderKTailUnnormalized_normGenerator
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.equalOrderErrorData A conditions hgap
      let N := D.newHeadOddDeterminantOneData hodd
        (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
      IsIsometric D.newHead N.parameters.kData.space
        D.newHeadLattice N.parameters.kData.lattice) :
    let D := S.equalOrderErrorData A conditions hgap
    let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
      hnontrigger hodd
    IsNormGeneratorValue
      (S.equalOrderKTailUnnormalized A conditions hgap hnontrigger hodd)
      B.tailLattice (S.firstScale * D.secondGenerator) := by
  let D := S.equalOrderErrorData A conditions hgap
  let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
    hnontrigger hodd
  have h := S.equalOrderKTail_normGenerator A conditions hgap hnontrigger
    hodd hk |>.rescaleQuadraticUnit S.firstScale
  simpa only [equalOrderKTailUnnormalized] using h

theorem equalOrderKHeadUnnormalized_normIdeal
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.equalOrderErrorData A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
    normIdeal (S.equalOrderKHeadUnnormalized A conditions hgap hodd)
        N.parameters.jData.lattice =
      principalIdeal (K := K) (S.targetJordan.normGenerator 0 : K) := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  have htarget : IsNormGeneratorValue
      (S.targetJordan.component 0).space
      (S.targetJordan.component 0).lattice
      (S.firstScale * S.firstNormGenerator) := by
    have h := S.firstNormGenerator_target.unscaleQuadraticUnit
    simpa only [targetFirstNormalized, inv_inv] using h
  calc
    normIdeal (S.equalOrderKHeadUnnormalized A conditions hgap hodd)
        N.parameters.jData.lattice =
        principalIdeal (K := K)
          ((S.firstScale * S.firstNormGenerator : Kˣ) : K) :=
      (S.equalOrderKHeadUnnormalized_normGenerator
        A conditions hgap hodd).2
    _ = normIdeal (S.targetJordan.component 0).space
        (S.targetJordan.component 0).lattice :=
      htarget.2.symm
    _ = principalIdeal (K := K) (S.targetJordan.normGenerator 0 : K) :=
      S.targetJordan.normIdeal_eq 0

theorem equalOrderKTailUnnormalized_normIdeal
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.equalOrderErrorData A conditions hgap
      let N := D.newHeadOddDeterminantOneData hodd
        (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
      IsIsometric D.newHead N.parameters.kData.space
        D.newHeadLattice N.parameters.kData.lattice) :
    let D := S.equalOrderErrorData A conditions hgap
    let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
      hnontrigger hodd
    normIdeal
        (S.equalOrderKTailUnnormalized A conditions hgap hnontrigger hodd)
        B.tailLattice =
      principalIdeal (K := K) (S.targetJordan.normGenerator 1 : K) := by
  let D := S.equalOrderErrorData A conditions hgap
  let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
    hnontrigger hodd
  calc
    normIdeal
        (S.equalOrderKTailUnnormalized A conditions hgap hnontrigger hodd)
        B.tailLattice =
        principalIdeal (K := K)
          ((S.firstScale * D.secondGenerator : Kˣ) : K) :=
      (S.equalOrderKTailUnnormalized_normGenerator A conditions hgap
        hnontrigger hodd hk).2
    _ = normIdeal (S.targetJordan.component 1).space
        (S.targetJordan.component 1).lattice :=
      D.targetSecond_unscaledNormGenerator.2.symm
    _ = principalIdeal (K := K) (S.targetJordan.normGenerator 1 : K) :=
      S.targetJordan.normIdeal_eq 1

/-- The untwisted restored head contains the complete old first-component
norm group. -/
theorem targetFirst_normGroupSet_subset_equalOrderKHeadUnnormalized
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.equalOrderErrorData A conditions hgap
      let N := D.newHeadOddDeterminantOneData hodd
        (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
      IsIsometric D.newHead N.parameters.kData.space
        D.newHeadLattice N.parameters.kData.lattice) :
    let D := S.equalOrderErrorData A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
    normGroupSet (S.targetJordan.component 0).space
        (S.targetJordan.component 0).lattice ⊆
      normGroupSet (S.equalOrderKHeadUnnormalized A conditions hgap hodd)
        N.parameters.jData.lattice := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  let sourceToJ := S.equalOrderKSourceToJHeadIsometry A conditions hgap hodd hk
  have hnormalized :
      normGroupSet S.targetFirstNormalized
          (S.targetJordan.component 0).lattice =
        normGroupSet N.parameters.jData.space
          N.parameters.jData.lattice :=
    S.firstNormalized_normGroupSet_eq.symm.trans
      (normGroupSet_eq_of_latticeIsometry sourceToJ).symm
  change normGroupSet (S.targetJordan.component 0).space
      (S.targetJordan.component 0).lattice ⊆
    normGroupSet (N.parameters.jData.space.rescaleUnit S.firstScale)
      N.parameters.jData.lattice
  intro z hz
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
  rw [← hnormalized]
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
  simpa only [Units.val_inv_eq_inv_val, inv_inv, ← mul_assoc,
    mul_inv_cancel₀ (Units.ne_zero S.firstScale), one_mul] using hz

/-- The restored twice-shifted tail contains the complete old second
component norm group. -/
theorem targetSecond_normGroupSet_subset_equalOrderKTailUnnormalized
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity) :
    let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
      hnontrigger hodd
    normGroupSet (S.targetJordan.component 1).space
        (S.targetJordan.component 1).lattice ⊆
      normGroupSet
        (S.equalOrderKTailUnnormalized A conditions hgap hnontrigger hodd)
        B.tailLattice := by
  let D := S.equalOrderErrorData A conditions hgap
  let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
    hnontrigger hodd
  change normGroupSet (S.targetJordan.component 1).space
      (S.targetJordan.component 1).lattice ⊆
    normGroupSet (B.tailSpace.rescaleUnit S.firstScale) B.tailLattice
  intro z hz
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
  apply B.normGroup_subset
  apply D.tailShift.normGroup_subset
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
  simpa only [Units.val_inv_eq_inv_val, inv_inv, ← mul_assoc,
    mul_inv_cancel₀ (Units.ne_zero S.firstScale), one_mul] using hz

/-- Regard the restored untwisted head and twice-shifted tail as a
decomposition of the original target first-pair sublattice. -/
noncomputable def equalOrderKFirstPairReplacementIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.equalOrderErrorData A conditions hgap
      let N := D.newHeadOddDeterminantOneData hodd
        (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
      IsIsometric D.newHead N.parameters.kData.space
        D.newHeadLattice N.parameters.kData.lattice) :
    let D := S.equalOrderErrorData A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
    let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
      hnontrigger hodd
    Isometry
      ((S.equalOrderKHeadUnnormalized A conditions hgap hodd).orthogonalSum
        (S.equalOrderKTailUnnormalized A conditions hgap hnontrigger hodd))
      S.targetJordan.firstPairSublattice.space
      (product N.parameters.jData.lattice B.tailLattice)
      S.targetJordan.firstPairSublattice.lattice :=
  (S.equalOrderKOriginalPairIsometry A conditions hgap hnontrigger hodd hk).symm
    |>.trans
      (S.targetJordan.toOrthogonalDecomposition
        |>.orthogonalSupLatticeIsometry firstIndex_ne_secondIndex)

set_option maxHeartbeats 3000000 in
/-- Install the nontrigger twisted-model correction as a saturated Jordan
splitting of the original target lattice. -/
noncomputable def equalOrderKJordanReplacement
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.equalOrderErrorData A conditions hgap
      let N := D.newHeadOddDeterminantOneData hodd
        (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
      IsIsometric D.newHead N.parameters.kData.space
        D.newHeadLattice N.parameters.kData.lattice) :
    Omeara9319JordanReplacement S.targetJordan := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
    hnontrigger hodd
  let f := S.equalOrderKFirstPairReplacementIsometry A conditions hgap
    hnontrigger hodd hk
  let hHeadMod := S.equalOrderKHeadUnnormalized_modular
    A conditions hgap hodd
  let hTailMod := S.equalOrderKTailUnnormalized_modular
    A conditions hgap hnontrigger hodd
  let hHeadScale := S.equalOrderKHeadUnnormalized_scaleIdeal
    A conditions hgap hodd
  let hTailScale := S.equalOrderKTailUnnormalized_scaleIdeal
    A conditions hgap hnontrigger hodd
  let hHeadNorm := S.equalOrderKHeadUnnormalized_normIdeal
    A conditions hgap hodd
  let hTailNorm := S.equalOrderKTailUnnormalized_normIdeal
    A conditions hgap hnontrigger hodd hk
  let T := S.targetJordan.replaceFirstPairOfIsometry f
    hHeadMod hTailMod hHeadScale hTailScale hHeadNorm hTailNorm
  exact
    { target := T
      fundamentalType :=
        S.targetJordan.replaceFirstPairOfIsometry_sameFundamentalType f
          hHeadMod hTailMod hHeadScale hTailScale hHeadNorm hTailNorm
      saturated :=
        S.targetJordan.replaceFirstPairOfIsometry_isSaturated f
          hHeadMod hTailMod hHeadScale hTailScale hHeadNorm hTailNorm
          S.targetJordan_isSaturated
          (S.targetFirst_normGroupSet_subset_equalOrderKHeadUnnormalized
            A conditions hgap hodd hk)
          (S.targetSecond_normGroupSet_subset_equalOrderKTailUnnormalized
            A conditions hgap hnontrigger hodd)
      laterPrefixIsometry := by
        intro k hk'
        exact S.targetJordan.toOrthogonalDecomposition
          |>.replacePair_first_prefixLatticeIsometry
            (S.targetJordan.firstPairDecompositionOfIsometry f) k hk' }

/-- The normalized source head, restored to the first Jordan scale, maps
integrally to the displayed untwisted head. -/
noncomputable def equalOrderKSourceToHeadUnnormalizedIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.equalOrderErrorData A conditions hgap
      let N := D.newHeadOddDeterminantOneData hodd
        (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
      IsIsometric D.newHead N.parameters.kData.space
        D.newHeadLattice N.parameters.kData.lattice) :
    let D := S.equalOrderErrorData A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
    Isometry (S.sourceJordan.component 0).space
      (S.equalOrderKHeadUnnormalized A conditions hgap hodd)
      (S.sourceJordan.component 0).lattice N.parameters.jData.lattice := by
  let normalized := S.equalOrderKSourceToJHeadIsometry
    A conditions hgap hodd hk
  let scaled := normalized.rescaleUnitBoth S.firstScale
  let undoSource := undoInverseRescaleLatticeIsometry
    (S.sourceJordan.component 0).space
    (S.sourceJordan.component 0).lattice S.firstScale
  exact undoSource.symm.trans scaled

set_option maxHeartbeats 3000000 in
/-- The displayed untwisted head maps onto the actual first component of
the installed Jordan replacement. -/
noncomputable def equalOrderKReplacementHeadIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.equalOrderErrorData A conditions hgap
      let N := D.newHeadOddDeterminantOneData hodd
        (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
      IsIsometric D.newHead N.parameters.kData.space
        D.newHeadLattice N.parameters.kData.lattice) :
    let D := S.equalOrderErrorData A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
    let R := S.equalOrderKJordanReplacement A conditions hgap
      hnontrigger hodd hk
    Isometry (S.equalOrderKHeadUnnormalized A conditions hgap hodd)
      (R.target.component 0).space N.parameters.jData.lattice
      (R.target.component 0).lattice := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  let B := S.equalOrderKRhoTwistAbsorptionData A conditions hgap
    hnontrigger hodd
  let f := S.equalOrderKFirstPairReplacementIsometry A conditions hgap
    hnontrigger hodd hk
  let hHeadMod := S.equalOrderKHeadUnnormalized_modular
    A conditions hgap hodd
  let hTailMod := S.equalOrderKTailUnnormalized_modular
    A conditions hgap hnontrigger hodd
  let hHeadScale := S.equalOrderKHeadUnnormalized_scaleIdeal
    A conditions hgap hodd
  let hTailScale := S.equalOrderKTailUnnormalized_scaleIdeal
    A conditions hgap hnontrigger hodd
  let hHeadNorm := S.equalOrderKHeadUnnormalized_normIdeal
    A conditions hgap hodd
  let hTailNorm := S.equalOrderKTailUnnormalized_normIdeal
    A conditions hgap hnontrigger hodd hk
  let R := S.equalOrderKJordanReplacement A conditions hgap
    hnontrigger hodd hk
  change Isometry (S.equalOrderKHeadUnnormalized A conditions hgap hodd)
    (R.target.component 0).space N.parameters.jData.lattice
    (R.target.component 0).lattice
  rw [show R.target = S.targetJordan.replaceFirstPairOfIsometry f
      hHeadMod hTailMod hHeadScale hTailScale hHeadNorm hTailNorm by rfl]
  exact S.targetJordan.replaceFirstPairOfIsometry_leftIsometry f
    hHeadMod hTailMod hHeadScale hTailScale hHeadNorm hTailNorm

/-- Source head aligned with the actual first component of the installed
nontrigger replacement. -/
noncomputable def equalOrderKSourceToReplacementHeadIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.equalOrderErrorData A conditions hgap
      let N := D.newHeadOddDeterminantOneData hodd
        (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
      IsIsometric D.newHead N.parameters.kData.space
        D.newHeadLattice N.parameters.kData.lattice) :
    let R := S.equalOrderKJordanReplacement A conditions hgap
      hnontrigger hodd hk
    Isometry (S.sourceJordan.component 0).space (R.target.component 0).space
      (S.sourceJordan.component 0).lattice (R.target.component 0).lattice :=
  (S.equalOrderKSourceToHeadUnnormalizedIsometry
    A conditions hgap hodd hk).trans
      (S.equalOrderKReplacementHeadIsometry A conditions hgap
        hnontrigger hodd hk)

/-- Complete Step-4 head-alignment object in the nontrigger twisted-model
branch. -/
noncomputable def equalOrderHeadAlignedReplacementOfNontriggerK
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0))
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.equalOrderErrorData A conditions hgap
      let N := D.newHeadOddDeterminantOneData hodd
        (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
      IsIsometric D.newHead N.parameters.kData.space
        D.newHeadLattice N.parameters.kData.lattice) :
    Omeara9328HeadAlignedReplacement S.sourceJordan S.targetJordan A := by
  let R := S.equalOrderKJordanReplacement A conditions hgap
    hnontrigger hodd hk
  let head := S.equalOrderKSourceToReplacementHeadIsometry
    A conditions hgap hnontrigger hodd hk
  let boundary := omeara9328BoundaryZeroConditionsWith_of_headIsometry
    S.sourceJordan R.target A head
  exact R.headAlignedReplacement S.residualFundamentalType A conditions
    boundary head

/-- Any integral alignment of the normalized source head with the
determinant-corrected head induces an alignment with the installed standard
equal-order replacement. -/
noncomputable def equalOrderSourceToReplacementHeadIsometryOfNormalizedHead
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (head : let D := S.equalOrderErrorData A conditions hgap
      Isometry S.sourceFirstNormalized D.newHead
        (S.sourceJordan.component 0).lattice D.newHeadLattice) :
    let R := S.equalOrderJordanReplacement A conditions hgap
    Isometry (S.sourceJordan.component 0).space (R.target.component 0).space
      (S.sourceJordan.component 0).lattice (R.target.component 0).lattice := by
  let R := S.equalOrderJordanReplacement A conditions hgap
  let normalized := head.trans
    (S.equalOrderNormalizedHeadIsometry A conditions hgap)
  let scaled := normalized.rescaleUnitBoth S.firstScale
  let undoSource := undoInverseRescaleLatticeIsometry
    (S.sourceJordan.component 0).space
    (S.sourceJordan.component 0).lattice S.firstScale
  let undoTarget := undoInverseRescaleLatticeIsometry
    (R.target.component 0).space (R.target.component 0).lattice S.firstScale
  exact undoSource.symm.trans (scaled.trans undoTarget)

/-- Package such a normalized-head alignment as the replacement consumed
by the saturated 93:28 induction. -/
noncomputable def equalOrderHeadAlignedReplacementOfNormalizedHead
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (headNormalized : let D := S.equalOrderErrorData A conditions hgap
      Isometry S.sourceFirstNormalized D.newHead
        (S.sourceJordan.component 0).lattice D.newHeadLattice) :
    Omeara9328HeadAlignedReplacement S.sourceJordan S.targetJordan A := by
  let R := S.equalOrderJordanReplacement A conditions hgap
  let head := S.equalOrderSourceToReplacementHeadIsometryOfNormalizedHead
    A conditions hgap headNormalized
  let boundary := omeara9328BoundaryZeroConditionsWith_of_headIsometry
    S.sourceJordan R.target A head
  exact R.headAlignedReplacement S.residualFundamentalType A conditions
    boundary head

/-- Nontrigger even-parity subcase of Step 4. -/
noncomputable def equalOrderHeadAlignedReplacementOfNontriggerEven
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (heven : Even S.firstNormWeightParity) :
    Omeara9328HeadAlignedReplacement S.sourceJordan S.targetJordan A := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  exact S.equalOrderHeadAlignedReplacementOfNormalizedHead
    A conditions hgap (D.sourceToNewHeadEvenIsometry heven hdet)

/-- Nontrigger odd-parity subcase when 93:18(vi) selects the untwisted
`J`-model directly. -/
noncomputable def equalOrderHeadAlignedReplacementOfNontriggerJ
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hodd : Odd S.firstNormWeightParity)
    (hj : let D := S.equalOrderErrorData A conditions hgap
      let N := D.newHeadOddDeterminantOneData hodd
        (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
      IsIsometric D.newHead N.parameters.jData.space
        D.newHeadLattice N.parameters.jData.lattice) :
    Omeara9328HeadAlignedReplacement S.sourceJordan S.targetJordan A := by
  let D := S.equalOrderErrorData A conditions hgap
  let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
  let N := D.newHeadOddDeterminantOneData hodd hdet
  let jIso := Classical.choice hj
  have htower : D.newHead.IsIsometric
      (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2) :=
    ⟨jIso.toQuadraticSpaceIsometry.trans
      (N.parameters.jSpaceToHyperbolicTowerIsometry N.alpha_zero)⟩
  exact S.equalOrderHeadAlignedReplacementOfNormalizedHead
    A conditions hgap (D.sourceToNewHeadIsometryOfHyperbolic htower)

/-- The non-condition-(ii) half of the equal-order case is now complete:
even heads are hyperbolic by 93:18(ii), and odd heads are handled by the
two alternatives of 93:18(vi), with the `K` alternative converted to `J`
by the two explicit 93:19 shifts. -/
noncomputable def equalOrderHeadAlignedReplacementOfNontrigger
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0)) :
    Omeara9328HeadAlignedReplacement S.sourceJordan S.targetJordan A := by
  by_cases hodd : Odd S.firstNormWeightParity
  · let D := S.equalOrderErrorData A conditions hgap
    let hdet := S.equalOrder_newHead_determinantClass_eq_one A conditions hgap
    let N := D.newHeadOddDeterminantOneData hodd hdet
    by_cases hj : IsIsometric D.newHead N.parameters.jData.space
        D.newHeadLattice N.parameters.jData.lattice
    · exact S.equalOrderHeadAlignedReplacementOfNontriggerJ
        A conditions hgap hodd hj
    · have hk := N.isometric_j_or_k.resolve_left hj
      exact S.equalOrderHeadAlignedReplacementOfNontriggerK
        A conditions hgap hnontrigger hodd hk
  · have heven : Even S.firstNormWeightParity :=
      Int.not_odd_iff_even.mp hodd
    exact S.equalOrderHeadAlignedReplacementOfNontriggerEven
      A conditions hgap heven

/-- Complete O'Meara 93:28 Step 4 in the equal normalized norm-order case,
with no residual local classification law. -/
noncomputable def equalOrderHeadAlignedReplacement
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator) :
    Omeara9328HeadAlignedReplacement S.sourceJordan S.targetJordan A := by
  by_cases htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A (boundaryRightIndex 0)
  · exact S.equalOrderHeadAlignedReplacementOfConditionII
      A conditions hgap htrigger
  · exact S.equalOrderHeadAlignedReplacementOfNontrigger
      A conditions hgap htrigger

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
