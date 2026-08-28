/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightProductPresentation
import Bong.Lattice.OmearaModularSingleTruncation
import Bong.Lattice.OmearaFundamentalIdeals
import Bong.Lattice.Omeara9325FundamentalMonotonicity

/-!
# Fundamental invariants in O'Meara 93:28, Step 8

The inserted plane is invisible at every old fundamental scale.  Its
truncated norm group lies in the doubled scale ideal of the old fundamental
lattice, hence is absorbed by that lattice's norm group.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- A norm-group summand already contained in the other summand does not
change the norm group of an orthogonal product. -/
theorem normGroupSet_orthogonalProduct_eq_right_of_subset
    (hsubset : normGroupSet q L ⊆ normGroupSet r M) :
    normGroupSet (q.orthogonalSum r) (product L M) =
      normGroupSet r M := by
  ext z
  rw [mem_normGroupSet_orthogonalProduct_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact add_mem_normGroupSet r M (hsubset ha) hb
  · intro hz
    exact ⟨0, zero_mem_normGroupSet q L, z, hz, by simp⟩

namespace JordanDecomposition

variable {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
  (J : JordanDecomposition q L (n + 2))

@[simp]
theorem stepEightScaleGenerator_zero :
    J.stepEightScaleGenerator 0 = J.scaleGenerator 0 := by
  have hidx : (0 : Fin (n + 3)) =
      (1 : Fin (n + 3)).succAbove (0 : Fin (n + 2)) := by
    apply Fin.ext
    simp
  rw [hidx, J.stepEightScaleGenerator_old]

@[simp]
theorem stepEightNormGeneratorAt_zero :
    J.stepEightNormGeneratorAt 0 = J.normGenerator 0 := by
  have hidx : (0 : Fin (n + 3)) =
      (1 : Fin (n + 3)).succAbove (0 : Fin (n + 2)) := by
    apply Fin.ext
    simp
  rw [hidx, J.stepEightNormGeneratorAt_old]

@[simp]
theorem stepEightScaleGenerator_succ_succ (i : Fin (n + 1)) :
    J.stepEightScaleGenerator i.succ.succ =
      J.scaleGenerator i.succ := by
  have hidx : (i.succ.succ : Fin (n + 3)) =
      (1 : Fin (n + 3)).succAbove (i.succ : Fin (n + 2)) := by
    apply Fin.ext
    simp
  rw [hidx, J.stepEightScaleGenerator_old]

@[simp]
theorem stepEightNormGeneratorAt_succ_succ (i : Fin (n + 1)) :
    J.stepEightNormGeneratorAt i.succ.succ =
      J.normGenerator i.succ := by
  have hidx : (i.succ.succ : Fin (n + 3)) =
      (1 : Fin (n + 3)).succAbove (i.succ : Fin (n + 2)) := by
    apply Fin.ext
    simp
  rw [hidx, J.stepEightNormGeneratorAt_old]

@[simp]
theorem stepEightNormGenerator_order :
    ordUnit K J.stepEightNormGenerator =
      (ramificationIndex K : Int) + ordUnit K J.stepEightScale := by
  let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
  have htwoOrder : ordUnit K two = (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    exact (ramificationIndex_spec K).symm
  have hunit : J.stepEightNormGenerator = two * J.stepEightScale := by
    apply Units.ext
    rfl
  rw [hunit, ordUnit_mul, htwoOrder]

/-- In a saturated splitting, the displayed component norm generator and
the intrinsic fundamental norm generator have the same order. -/
theorem IsSaturated.normGenerator_order_eq_fundamental
    (hJ : J.IsSaturated) (i : Fin (n + 2)) :
    ordUnit K (J.normGenerator i) =
      ordUnit K (J.fundamentalNormGenerator i) := by
  have hmem : (J.fundamentalNormGenerator i : K) ∈
      normGroupSet (J.component i).space (J.component i).lattice := by
    rw [hJ i]
    exact (J.fundamentalNormGenerator_spec i).1
  have hgenerator :=
    J.fundamentalNormGenerator_isComponentNormGenerator i hmem
  apply (principalIdeal_eq_iff_ordUnit_eq _ _).mp
  exact (J.normIdeal_eq i).symm.trans hgenerator.2

/-- Under the Step-8 norm gap, the original lattice truncated at the
inserted scale has norm order exactly two above the old first norm order. -/
theorem normIdeal_at_stepEightScale
    (hJ : J.IsSaturated)
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1)) :
    normIdeal q
        (scaleTruncation q L (ordUnit K J.stepEightScale)) =
      powerIdeal (K := K)
        (ordUnit K (J.fundamentalNormGenerator 0) + 2) := by
  rw [J.normIdeal_scaleTruncation_eq_powerIdeal 0]
  congr 1
  let scale : Fin (n + 2) → Int :=
    fun j => ordUnit K (J.scaleGenerator j)
  let norm : Fin (n + 2) → Int :=
    fun j => ordUnit K (J.normGenerator j)
  change JordanProfileOrder.effectiveAt scale norm 0
      (ordUnit K J.stepEightScale) =
    ordUnit K (J.fundamentalNormGenerator 0) + 2
  apply le_antisymm
  · calc
      JordanProfileOrder.effectiveAt scale norm 0
          (ordUnit K J.stepEightScale) ≤
          JordanProfileOrder.adjustedAt scale norm
            (ordUnit K J.stepEightScale) 0 :=
        JordanProfileOrder.effectiveAt_le scale norm 0 0 _
      _ = ordUnit K (J.fundamentalNormGenerator 0) + 2 := by
        unfold JordanProfileOrder.adjustedAt scale norm
        rw [if_pos]
        · rw [hJ.normGenerator_order_eq_fundamental,
            stepEightScale_order]
          omega
        · rw [stepEightScale_order]
          omega
  · apply JordanProfileOrder.le_effectiveAt
    intro j
    by_cases hj : j = 0
    · subst j
      unfold JordanProfileOrder.adjustedAt scale norm
      rw [if_pos]
      · rw [hJ.normGenerator_order_eq_fundamental,
          stepEightScale_order]
        omega
      · rw [stepEightScale_order]
        omega
    · have hOneLe : (1 : Fin (n + 2)) ≤ j := by
        apply Fin.le_iff_val_le_val.mpr
        have hval : j.val ≠ 0 := by
          intro hzero
          apply hj
          apply Fin.ext
          exact hzero
        exact Nat.one_le_iff_ne_zero.mpr hval
      have hscaleOne : ordUnit K J.stepEightScale ≤
          ordUnit K (J.scaleGenerator j) := by
        have hstrict := J.scaleOrder_strict
          (show (0 : Fin (n + 2)) < 1 by simp)
        have hmono : ordUnit K (J.scaleGenerator 1) ≤
            ordUnit K (J.scaleGenerator j) := by
          by_cases hEq : (1 : Fin (n + 2)) = j
          · subst j
            exact le_rfl
          · exact (J.scaleOrder_strict
              (lt_of_le_of_ne hOneLe hEq)).le
        rw [stepEightScale_order]
        omega
      have hnormOne : ordUnit K (J.fundamentalNormGenerator 1) ≤
          ordUnit K (J.fundamentalNormGenerator j) :=
        J.fundamentalNormGenerator_order_mono hOneLe
      unfold JordanProfileOrder.adjustedAt scale norm
      rw [if_neg (not_lt_of_ge hscaleOne)]
      rw [hJ.normGenerator_order_eq_fundamental]
      omega

/-- The inserted fundamental scale of the raw Step-8 splitting has norm
order `u₀ + 2`, as stated on O'Meara p. 275. -/
theorem stepEightJordan_effectiveNormOrder_inserted
    (hJ : J.IsSaturated)
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int)) :
    BONG.jordanEffectiveNormOrder (J.stepEightJordan hscaleGap) 1 =
      ordUnit K (J.fundamentalNormGenerator 0) + 2 := by
  let J₈ := J.stepEightJordan hscaleGap
  let scale : Fin (n + 3) → Int :=
    fun j => ordUnit K (J₈.scaleGenerator j)
  let norm : Fin (n + 3) → Int :=
    fun j => ordUnit K (J₈.normGenerator j)
  unfold BONG.jordanEffectiveNormOrder
    BONG.jordanEffectiveNormOrderAt
  change JordanProfileOrder.effectiveAt scale norm 1
      (ordUnit K J.stepEightScale) =
    ordUnit K (J.fundamentalNormGenerator 0) + 2
  apply le_antisymm
  · calc
      JordanProfileOrder.effectiveAt scale norm 1
          (ordUnit K J.stepEightScale) ≤
          JordanProfileOrder.adjustedAt scale norm
            (ordUnit K J.stepEightScale) 0 :=
        JordanProfileOrder.effectiveAt_le scale norm 1 0 _
      _ = ordUnit K (J.fundamentalNormGenerator 0) + 2 := by
        unfold JordanProfileOrder.adjustedAt
        dsimp only [scale, norm, J₈]
        rw [if_pos]
        · rw [J.stepEightJordan_scaleGenerator,
            J.stepEightScaleGenerator_zero,
            J.stepEightJordan_normGenerator,
            J.stepEightNormGeneratorAt_zero,
            hJ.normGenerator_order_eq_fundamental,
            stepEightScale_order]
          omega
        · rw [J.stepEightJordan_scaleGenerator,
            J.stepEightScaleGenerator_zero,
            stepEightScale_order]
          omega
  · apply JordanProfileOrder.le_effectiveAt
    intro j
    cases j using Fin.cases with
    | zero =>
        unfold JordanProfileOrder.adjustedAt
        dsimp only [scale, norm, J₈]
        rw [if_pos]
        · rw [J.stepEightJordan_scaleGenerator,
            J.stepEightScaleGenerator_zero,
            J.stepEightJordan_normGenerator,
            J.stepEightNormGeneratorAt_zero,
            hJ.normGenerator_order_eq_fundamental,
            stepEightScale_order]
          omega
        · rw [J.stepEightJordan_scaleGenerator,
            J.stepEightScaleGenerator_zero,
            stepEightScale_order]
          omega
    | succ j =>
        cases j using Fin.cases with
        | zero =>
            unfold JordanProfileOrder.adjustedAt
            dsimp only [scale, norm, J₈]
            rw [if_neg]
            · change ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
                ordUnit K ((J.stepEightJordan hscaleGap).normGenerator
                  (1 : Fin (n + 3)))
              rw [J.stepEightJordan_normGenerator,
                J.stepEightNormGeneratorAt_inserted,
                J.stepEightNormGenerator_order]
              unfold fundamentalScaleOrder at hfirst
              rw [stepEightScale_order]
              omega
            · change ¬ ordUnit K ((J.stepEightJordan hscaleGap).scaleGenerator
                  (1 : Fin (n + 3))) < ordUnit K J.stepEightScale
              rw [J.stepEightJordan_scaleGenerator,
                J.stepEightScaleGenerator_inserted]
              omega
        | succ j =>
            unfold JordanProfileOrder.adjustedAt
            dsimp only [scale, norm, J₈]
            rw [if_neg]
            · rw [J.stepEightJordan_normGenerator,
                J.stepEightNormGeneratorAt_succ_succ,
                hJ.normGenerator_order_eq_fundamental]
              have hOneLe : (1 : Fin (n + 2)) ≤ j.succ := by
                apply Fin.le_iff_val_le_val.mpr
                change 1 ≤ j.val + 1
                omega
              have hmono := J.fundamentalNormGenerator_order_mono
                (i := (1 : Fin (n + 2)))
                (j := j.succ) hOneLe
              omega
            · rw [J.stepEightJordan_scaleGenerator,
                J.stepEightScaleGenerator_succ_succ]
              have hscaleLater : ordUnit K (J.scaleGenerator 1) ≤
                  ordUnit K (J.scaleGenerator j.succ) := by
                have hOneLe : (1 : Fin (n + 2)) ≤ j.succ := by
                  apply Fin.le_iff_val_le_val.mpr
                  change 1 ≤ j.val + 1
                  omega
                have hstrict : StrictMono
                    (fun i : Fin (n + 2) =>
                      ordUnit K (J.scaleGenerator i)) := by
                  intro a b hab
                  exact J.scaleOrder_strict hab
                exact hstrict.monotone hOneLe
              rw [stepEightScale_order]
              omega

/-- The canonical fundamental norm generator at the inserted scale has the
order of O'Meara's displayed generator `pi² a₀`. -/
theorem stepEightJordan_fundamentalNormGenerator_order_inserted
    (hJ : J.IsSaturated)
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int)) :
    ordUnit K ((J.stepEightJordan hscaleGap).fundamentalNormGenerator 1) =
      ordUnit K (J.fundamentalNormGenerator 0) + 2 := by
  rw [(J.stepEightJordan hscaleGap).fundamentalNormGenerator_order_eq_effective]
  exact J.stepEightJordan_effectiveNormOrder_inserted hJ hscaleGap
    hnormGap hfirst

/-- O'Meara 93:25 gives `w₁ ⊆ w₀₋µ` for the old second scale
and the newly inserted Step-8 scale. -/
theorem stepEightJordan_secondWeightIdeal_le_inserted
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) :
    J.fundamentalWeightIdeal 1 ≤
      (J.stepEightJordan hscaleGap).fundamentalWeightIdeal 1 := by
  let J₈ := J.stepEightJordan hscaleGap
  let T := ordUnit K J.stepEightScale
  let q₈ := BONG.blockOrthogonalForm (n + 2)
    J.stepEightCarrier J.stepEightForm
  let L₈ := BONG.blockProductLattice (n + 2)
    J.stepEightCarrier J.stepEightLattice
  let qP := (QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum q
  let LP := product (hyperbolicPlaneLattice (K := K)) L
  have hscaleLe : T ≤ J.fundamentalScaleOrder 1 := by
    dsimp only [T]
    unfold fundamentalScaleOrder
    rw [stepEightScale_order]
    omega
  have hright : J.fundamentalLattice 1 ≤
      scaleTruncation q L T := by
    exact scaleTruncation_anti hscaleLe
  have hgroup : normGroupSet q (J.fundamentalLattice 1) ⊆
      normGroupSet qP (scaleTruncation qP LP T) := by
    intro z hz
    dsimp only [qP, LP]
    rw [scaleTruncation_orthogonalProduct,
      mem_normGroupSet_orthogonalProduct_iff]
    exact ⟨0, zero_mem_normGroupSet _ _, z,
      normGroupSet_mono hright hz, by simp⟩
  have htwo : twoScaleIdeal q (J.fundamentalLattice 1) ≤
      twoScaleIdeal qP (scaleTruncation qP LP T) := by
    dsimp only [qP, LP]
    rw [scaleTruncation_orthogonalProduct,
      twoScaleIdeal_orthogonalProduct]
    apply (twoScaleIdeal_mono hright).trans
    intro z hz
    exact Submodule.mem_sup_right hz
  let f := J.stepEightProductPresentation
  have hbProduct : IsNormGeneratorValue qP
      (scaleTruncation qP LP T) (J₈.fundamentalNormGenerator 1) := by
    have hmap := (J₈.fundamentalNormGenerator_spec 1).mapLatticeIsometry
      (f.scaleTruncation T)
    simpa only [J₈, q₈, L₈, qP, LP, fundamentalLattice,
      fundamentalScaleOrder, J.stepEightJordan_scaleGenerator,
      J.stepEightScaleGenerator_inserted] using hmap
  have hweight : weightIdeal q (J.fundamentalLattice 1) ≤
      weightIdeal qP (scaleTruncation qP LP T) :=
    weightIdeal_mono_of_normGroupSet_subset_of_twoScaleIdeal_le
      (J.fundamentalNormGenerator 1) (J₈.fundamentalNormGenerator 1)
      (J.fundamentalNormGenerator_spec 1) hbProduct htwo hgroup
  change weightIdeal q (J.fundamentalLattice 1) ≤
    weightIdeal q₈ (J₈.fundamentalLattice 1)
  calc
    weightIdeal q (J.fundamentalLattice 1) ≤
        weightIdeal qP (scaleTruncation qP LP T) := hweight
    _ = weightIdeal q₈ (J₈.fundamentalLattice 1) := by
      letI : Module.Finite K V := L.moduleFinite
      have hpos : 0 < finrank K ((Fin 2 → K) × V) := by
        rw [Module.finrank_prod]
        have hfun : finrank K (Fin 2 → K) = 2 := by simp
        rw [hfun]
        omega
      have heq := weightIdeal_scaleTruncation_eq_of_isometry
        f.symm T hpos
      symm
      simpa only [J₈, q₈, L₈, qP, LP, fundamentalLattice,
        fundamentalScaleOrder, J.stepEightJordan_scaleGenerator,
        J.stepEightScaleGenerator_inserted] using heq

@[simp]
theorem stepEightJordan_fundamentalScaleOrder_inserted
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) :
    (J.stepEightJordan hscaleGap).fundamentalScaleOrder 1 =
      J.fundamentalScaleOrder 0 + 1 := by
  unfold fundamentalScaleOrder
  rw [J.stepEightJordan_scaleGenerator,
    J.stepEightScaleGenerator_inserted, stepEightScale_order]

/-- Order form of `w₁ ⊆ w₀₋µ`. -/
theorem stepEightJordan_insertedWeightOrder_le_second
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) :
    (J.stepEightJordan hscaleGap).fundamentalWeightOrder 1 ≤
      J.fundamentalWeightOrder 1 := by
  have hweight := J.stepEightJordan_secondWeightIdeal_le_inserted hscaleGap
  unfold fundamentalWeightIdeal at hweight
  rw [weightIdeal_eq_powerIdeal, weightIdeal_eq_powerIdeal,
    powerIdeal_le_iff] at hweight
  exact hweight

/-- The first old fundamental norm group, multiplied by the square of the
uniformizer, lies in the newly inserted fundamental norm group.  This is the
first inclusion of O'Meara 93:25 in the precise form used at Step 8. -/
theorem stepEightJordan_sq_uniformizer_mem_insertedNormGroup
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) {z : K}
    (hz : z ∈ J.fundamentalNormGroup 0) :
    ((uniformizerUnit K ^ 2 : Kˣ) : K) * z ∈
      (J.stepEightJordan hscaleGap).fundamentalNormGroup 1 := by
  let c : Kˣ := uniformizerUnit K
  let T := ordUnit K J.stepEightScale
  have hscaleLe : J.fundamentalScaleOrder 0 ≤ T := by
    dsimp only [T]
    unfold fundamentalScaleOrder
    rw [stepEightScale_order]
    omega
  have hrescaled : (c ^ 2 : Kˣ) * z ∈
      normGroupSet q (rescale c (J.fundamentalLattice 0)) :=
    sq_mul_mem_normGroupSet_rescale c hz
  have hrescaleLe : rescale c (J.fundamentalLattice 0) ≤
      scaleTruncation q L T := by
    have hle := rescale_scaleTruncation_le (q := q) (L := L) hscaleLe
    simpa only [c, T, fundamentalLattice, fundamentalScaleOrder,
      stepEightScale_order, sub_self, add_sub_cancel_left,
      uniformizerPowerUnit, zpow_one] using hle
  have hright : (c ^ 2 : Kˣ) * z ∈
      normGroupSet q (scaleTruncation q L T) :=
    normGroupSet_mono hrescaleLe hrescaled
  have hproduct : (c ^ 2 : Kˣ) * z ∈
      normGroupSet
        ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum q)
        (scaleTruncation
          ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum q)
          (product (hyperbolicPlaneLattice (K := K)) L) T) := by
    rw [scaleTruncation_orthogonalProduct,
      mem_normGroupSet_orthogonalProduct_iff]
    exact ⟨0, zero_mem_normGroupSet _ _, (c ^ 2 : Kˣ) * z,
      hright, by simp⟩
  have heq := normGroupSet_scaleTruncation_eq_of_isometry
    J.stepEightProductPresentation T
  rw [heq] at hproduct
  unfold fundamentalNormGroup fundamentalLattice fundamentalScaleOrder
  rw [J.stepEightJordan_scaleGenerator,
    J.stepEightScaleGenerator_inserted]
  simpa only [c] using hproduct

/-- O'Meara's displayed Step-8 norm generator `pi² a₀`. -/
noncomputable def stepEightRaisedNormGenerator : Kˣ :=
  uniformizerUnit K ^ 2 * J.fundamentalNormGenerator 0

@[simp]
theorem stepEightRaisedNormGenerator_order :
    ordUnit K J.stepEightRaisedNormGenerator =
      ordUnit K (J.fundamentalNormGenerator 0) + 2 := by
  have hpi : ordUnit K (uniformizerUnit K) = 1 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, coe_uniformizerUnit, ord_uniformizer]
    norm_num
  rw [stepEightRaisedNormGenerator, ordUnit_mul, ordUnit_pow, hpi]
  omega

/-- The displayed scalar `pi² a₀` is genuinely a norm generator of the
new fundamental lattice, not merely a unit of the correct order. -/
theorem stepEightRaisedNormGenerator_spec
    (hJ : J.IsSaturated)
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int)) :
    IsNormGeneratorValue
      (BONG.blockOrthogonalForm (n + 2)
        J.stepEightCarrier J.stepEightForm)
      ((J.stepEightJordan hscaleGap).fundamentalLattice 1)
      J.stepEightRaisedNormGenerator := by
  constructor
  · exact J.stepEightJordan_sq_uniformizer_mem_insertedNormGroup
      hscaleGap (J.fundamentalNormGenerator_spec 0).1
  · have hcanonical :=
      J.stepEightJordan_fundamentalNormGenerator_order_inserted
        hJ hscaleGap hnormGap hfirst
    have hideal : principalIdeal (K := K)
          ((J.stepEightJordan hscaleGap).fundamentalNormGenerator 1 : K) =
        principalIdeal (K := K) (J.stepEightRaisedNormGenerator : K) := by
      apply (principalIdeal_eq_iff_ordUnit_eq _ _).2
      rw [hcanonical, J.stepEightRaisedNormGenerator_order]
    exact ((J.stepEightJordan hscaleGap).fundamentalNormGenerator_spec 1).2.trans
      hideal

/-- At an old fundamental scale, the inserted Step-8 plane is absorbed by
the old scale layer. -/
theorem stepEightHyperbolicNormGroup_subset_oldFundamental
    (i : Fin (n + 2)) :
    normGroupSet (QuadraticSpace.hyperbolicPlane J.stepEightScale)
        (scaleTruncation
          (QuadraticSpace.hyperbolicPlane J.stepEightScale)
          (hyperbolicPlaneLattice (K := K))
          (J.fundamentalScaleOrder i)) ⊆
      J.fundamentalNormGroup i := by
  intro z hz
  apply twoScaleIdeal_subset_normGroupSet q (J.fundamentalLattice i)
  rw [J.fundamentalTwoScaleIdeal_eq_powerIdeal]
  have hcontain :=
    normGroupSet_scaleTruncation_hyperbolicPlane_subset_powerIdeal
      J.stepEightScale (J.fundamentalScaleOrder i) hz
  simpa only [add_comm] using hcontain

/-- The actual enlarged lattice has exactly the old norm group at every old
fundamental scale. -/
theorem stepEightNormGroup_at_oldFundamentalScale
    (i : Fin (n + 2)) :
    normGroupSet
        (BONG.blockOrthogonalForm (n + 2)
          J.stepEightCarrier J.stepEightForm)
        (scaleTruncation
          (BONG.blockOrthogonalForm (n + 2)
            J.stepEightCarrier J.stepEightForm)
          (BONG.blockProductLattice (n + 2)
            J.stepEightCarrier J.stepEightLattice)
          (J.fundamentalScaleOrder i)) =
      J.fundamentalNormGroup i := by
  let f := J.stepEightProductPresentation
  calc
    normGroupSet
        (BONG.blockOrthogonalForm (n + 2)
          J.stepEightCarrier J.stepEightForm)
        (scaleTruncation
          (BONG.blockOrthogonalForm (n + 2)
            J.stepEightCarrier J.stepEightForm)
          (BONG.blockProductLattice (n + 2)
            J.stepEightCarrier J.stepEightLattice)
          (J.fundamentalScaleOrder i)) =
        normGroupSet
          ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum q)
          (scaleTruncation
            ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum q)
            (product (hyperbolicPlaneLattice (K := K)) L)
            (J.fundamentalScaleOrder i)) :=
      (normGroupSet_scaleTruncation_eq_of_isometry f
        (J.fundamentalScaleOrder i)).symm
    _ = normGroupSet
          ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum q)
          (product
            (scaleTruncation
              (QuadraticSpace.hyperbolicPlane J.stepEightScale)
              (hyperbolicPlaneLattice (K := K))
              (J.fundamentalScaleOrder i))
            (J.fundamentalLattice i)) := by
      rw [scaleTruncation_orthogonalProduct]
      rfl
    _ = J.fundamentalNormGroup i :=
      normGroupSet_orthogonalProduct_eq_right_of_subset
        (J.stepEightHyperbolicNormGroup_subset_oldFundamental i)

/-- The fundamental norm group at every raised old index is unchanged by
the raw Step-8 insertion. -/
theorem stepEightJordan_fundamentalNormGroup_old
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (i : Fin (n + 2)) :
    (J.stepEightJordan hgap).fundamentalNormGroup
        ((1 : Fin (n + 3)).succAbove i) =
      J.fundamentalNormGroup i := by
  unfold fundamentalNormGroup fundamentalLattice fundamentalScaleOrder
  rw [J.stepEightJordan_scaleGenerator,
    J.stepEightScaleGenerator_old]
  exact J.stepEightNormGroup_at_oldFundamentalScale i

/-- The doubled scale ideal at an old index is unchanged. -/
theorem stepEightJordan_fundamentalTwoScaleIdeal_old
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (i : Fin (n + 2)) :
    twoScaleIdeal
        (BONG.blockOrthogonalForm (n + 2)
          J.stepEightCarrier J.stepEightForm)
        ((J.stepEightJordan hgap).fundamentalLattice
          ((1 : Fin (n + 3)).succAbove i)) =
      twoScaleIdeal q (J.fundamentalLattice i) := by
  rw [(J.stepEightJordan hgap).fundamentalTwoScaleIdeal_eq_powerIdeal,
    J.fundamentalTwoScaleIdeal_eq_powerIdeal]
  congr 1
  unfold fundamentalScaleOrder
  rw [J.stepEightJordan_scaleGenerator,
    J.stepEightScaleGenerator_old]

/-- The old selected norm generator remains a norm generator of the
corresponding enlarged fundamental lattice. -/
theorem stepEightJordan_oldNormGenerator_spec
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (i : Fin (n + 2)) :
    IsNormGeneratorValue
        (BONG.blockOrthogonalForm (n + 2)
          J.stepEightCarrier J.stepEightForm)
        ((J.stepEightJordan hgap).fundamentalLattice
          ((1 : Fin (n + 3)).succAbove i))
        (J.fundamentalNormGenerator i) := by
  apply isNormGeneratorValue_of_normGroupSet_eq
    (J.fundamentalNormGenerator_spec i)
  · exact (J.stepEightJordan_fundamentalNormGroup_old hgap i).symm
  · exact ⟨(J.stepEightJordan hgap).fundamentalNormGenerator
      ((1 : Fin (n + 3)).succAbove i),
      (J.stepEightJordan hgap).fundamentalNormGenerator_spec _⟩

/-- Canonical fundamental norm-generator orders at old indices are
unchanged. -/
theorem stepEightJordan_fundamentalNormGenerator_order_old
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (i : Fin (n + 2)) :
    ordUnit K ((J.stepEightJordan hgap).fundamentalNormGenerator
        ((1 : Fin (n + 3)).succAbove i)) =
      ordUnit K (J.fundamentalNormGenerator i) := by
  apply (principalIdeal_eq_iff_ordUnit_eq _ _).mp
  calc
    principalIdeal (K := K)
        ((J.stepEightJordan hgap).fundamentalNormGenerator
          ((1 : Fin (n + 3)).succAbove i) : K) =
        normIdeal
          (BONG.blockOrthogonalForm (n + 2)
            J.stepEightCarrier J.stepEightForm)
          ((J.stepEightJordan hgap).fundamentalLattice
            ((1 : Fin (n + 3)).succAbove i)) :=
      ((J.stepEightJordan hgap).fundamentalNormGenerator_spec _).2.symm
    _ = principalIdeal (K := K)
        (J.fundamentalNormGenerator i : K) :=
      (J.stepEightJordan_oldNormGenerator_spec hgap i).2

/-- Fundamental weights at old indices are unchanged. -/
theorem stepEightJordan_fundamentalWeightIdeal_old
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (i : Fin (n + 2)) :
    (J.stepEightJordan hgap).fundamentalWeightIdeal
        ((1 : Fin (n + 3)).succAbove i) =
      J.fundamentalWeightIdeal i := by
  exact weightIdeal_eq_of_normGroupSet_eq_of_twoScaleIdeal_eq
    ((J.stepEightJordan hgap).fundamentalNormGenerator_spec _)
    ⟨J.fundamentalNormGenerator i, J.fundamentalNormGenerator_spec i⟩
    (J.stepEightJordan_fundamentalNormGroup_old hgap i)
    (J.stepEightJordan_fundamentalTwoScaleIdeal_old hgap i)

/-- Fundamental weight orders at old indices are unchanged. -/
theorem stepEightJordan_fundamentalWeightOrder_old
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (i : Fin (n + 2)) :
    (J.stepEightJordan hgap).fundamentalWeightOrder
        ((1 : Fin (n + 3)).succAbove i) =
      J.fundamentalWeightOrder i := by
  unfold fundamentalWeightOrder
  apply powerIdeal_order_eq_of_eq (K := K)
  rw [← weightIdeal_eq_powerIdeal, ← weightIdeal_eq_powerIdeal]
  exact J.stepEightJordan_fundamentalWeightIdeal_old hgap i

/-- Every old boundary strictly after the first one is unchanged by the
insertion.  The first old boundary is split into two new boundaries and is
handled separately in Step 8. -/
theorem stepEightJordan_fundamentalIdeal_later
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (i : Fin n) :
    (J.stepEightJordan hgap).fundamentalIdeal i.succ.succ =
      J.fundamentalIdeal i.succ := by
  let J₈ := J.stepEightJordan hgap
  let oldBoundary : Fin (n + 1) := i.succ
  let newBoundary : Fin (n + 2) := i.succ.succ
  have hleft : boundaryLeftIndex newBoundary =
      (1 : Fin (n + 3)).succAbove (boundaryLeftIndex oldBoundary) := by
    apply Fin.ext
    simp [oldBoundary, newBoundary, boundaryLeftIndex]
  have hright : boundaryRightIndex newBoundary =
      (1 : Fin (n + 3)).succAbove (boundaryRightIndex oldBoundary) := by
    apply Fin.ext
    simp [oldBoundary, newBoundary, boundaryRightIndex]
  have hsum : J₈.boundaryNormOrderSum newBoundary =
      J.boundaryNormOrderSum oldBoundary := by
    unfold boundaryNormOrderSum
    rw [hleft, hright,
      J.stepEightJordan_fundamentalNormGenerator_order_old hgap,
      J.stepEightJordan_fundamentalNormGenerator_order_old hgap]
  have hdefect : J₈.boundaryProductDefectSum newBoundary =
      J.boundaryProductDefectSum oldBoundary := by
    unfold boundaryProductDefectSum
    rw [hleft, hright,
      J.stepEightJordan_fundamentalNormGroup_old hgap,
      J.stepEightJordan_fundamentalNormGroup_old hgap]
  have hscale : J₈.fundamentalScaleOrder
        (boundaryLeftIndex newBoundary) =
      J.fundamentalScaleOrder (boundaryLeftIndex oldBoundary) := by
    unfold fundamentalScaleOrder
    rw [hleft, J.stepEightJordan_scaleGenerator,
      J.stepEightScaleGenerator_old]
  have hparity : J₈.boundaryParityIdeal newBoundary =
      J.boundaryParityIdeal oldBoundary := by
    unfold boundaryParityIdeal
    rw [hsum, hscale]
  have hscaled : J₈.scaledFundamentalIdeal newBoundary =
      J.scaledFundamentalIdeal oldBoundary := by
    unfold scaledFundamentalIdeal
    rw [hsum, hdefect, hparity]
  change J₈.fundamentalIdeal newBoundary =
    J.fundamentalIdeal oldBoundary
  unfold fundamentalIdeal
  rw [hscaled]
  apply scalarIdeal_units_eq_of_ordUnit_eq
  rw [ordUnit_pow, ordUnit_inv, ordUnit_pow, ordUnit_inv]
  have hscaleGenerator : ordUnit K
        (J₈.scaleGenerator (boundaryLeftIndex newBoundary)) =
      ordUnit K
        (J.scaleGenerator (boundaryLeftIndex oldBoundary)) := by
    simpa only [fundamentalScaleOrder] using hscale
  rw [hscaleGenerator]

end JordanDecomposition

end Lattice

end Bong
