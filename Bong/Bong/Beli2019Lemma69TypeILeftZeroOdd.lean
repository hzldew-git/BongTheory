/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIBetaPreviousValue
import Bong.Bong.Beli2019CappedDefectSharp

/-!
# Beli (2019), Lemma 6.9(ii): the zero-left first odd boundary

If the canonical left switch is zero, the first central boundary is `i = 1`.
Definition 4 has no secondary candidate there.  The half-gap estimate is the
usual type-I weight calculation; the primary defect reduces to the source
adjacent defect because the target prefix is empty.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

set_option maxHeartbeats 2000000 in
-- The empty-prefix normalization is combined with two finite-to-WithTop shifts.
/-- At `i = 1`, the representation invariant equals the first target alpha
under the type-I endpoint weight equality. -/
theorem lemma69_typeI_beta_eq_one_of_leftSwitch_zero
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hleftZero : C.leftSwitch = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2)) (hiOne : i.val = 1)
    (hrightPos : 0 < C.rightSwitch)
    (hweight : a.alphaLeftEndpoint ⟨0, by
        have hi := i.lt_large
        omega⟩ =
      b.alphaLeftEndpoint ⟨0, by
        have hi := i.lt_large
        omega⟩) :
    a.representationAlpha b i =
      (b.alphaValue ⟨0, by
        have hi := i.lt_large
        omega⟩ : WithTop ℚ) := by
  have hiPrevious : i.val - 1 < n + 2 := by
    have hi := i.lt_large
    omega
  have hiAlpha : i.val - 1 < n + 1 := by
    have hi := i.lt_large
    omega
  let p : Fin (n + 1) := ⟨i.val - 1, hiAlpha⟩
  have hpEven : Even p.val := by
    refine ⟨0, ?_⟩
    simp only [p, hiOne]
  have hgapEntries := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst p.val hpEven (by
      simp only [p, hiOne, hleftZero]
      omega)
      (by simp only [p, hiOne]; omega)
  have hpCast : p.castSucc =
      (⟨i.val - 1, hiPrevious⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hpSucc : p.succ =
      (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have htargetPrevious : b.order p.castSucc =
      a.order p.castSucc + 2 := by
    rw [hpCast]
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    simpa only [p] using hgapEntries
  have hbetaSource : b.alphaValue p = a.alphaValue p - 2 := by
    have hweightP : a.alphaLeftEndpoint p = b.alphaLeftEndpoint p := by
      simpa only [p, hiOne] using hweight
    unfold alphaLeftEndpoint at hweightP
    change (a.order p.castSucc : ℚ) + a.alphaValue p =
      (b.order p.castSucc : ℚ) + b.alphaValue p at hweightP
    rw [htargetPrevious] at hweightP
    push_cast at hweightP ⊢
    linarith
  have halphaHalf := a.alphaValue_le_halfGapValue p
  unfold halfGapValue orderGap at halphaHalf
  rw [hpSucc] at halphaHalf
  have hhalfFinite : b.alphaValue p ≤
      ((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) := by
    rw [← hpCast, htargetPrevious]
    push_cast at halphaHalf ⊢
    linarith [hbetaSource]
  have hhalf : (b.alphaValue p : WithTop ℚ) ≤
      a.representationHalfGap b i := by
    unfold representationHalfGap
    exact_mod_cast hhalfFinite
  let shift : ℚ :=
    ((a.order p.succ - a.order p.castSucc : Int) : ℚ)
  let sourceDefect := a.truncatedPrefixDefect a (-1)
    p.val (p.val + 2)
  let crossDefect := a.truncatedPrefixDefect b (-1)
    (i.val + 1) (i.val - 1)
  have hcrossEq : crossDefect = sourceDefect := by
    calc
      crossDefect = a.truncatedPrefixDefect b (-1) (i.val + 1) 0 := by
        simp only [crossDefect, hiOne]
      _ = a.truncatedPrefixDefect a (-1) (i.val + 1) 0 :=
        a.truncatedPrefixDefect_zero_right_eq_self b (-1) (i.val + 1)
      _ = a.truncatedPrefixDefect a (-1) 0 (i.val + 1) :=
        a.truncatedPrefixDefect_comm a (-1) (i.val + 1) 0
      _ = sourceDefect := by
        simp only [sourceDefect, p, hiOne]
  have halphaRaw := a.alpha_le_orderGap_add_cappedAdjacent p
  have hsourceBound : (a.alphaValue p : WithTop ℚ) ≤
      (shift : WithTop ℚ) + crossDefect := by
    rw [hcrossEq]
    simpa only [shift, sourceDefect] using halphaRaw
  have htranslated := add_le_add_right hsourceBound
    ((-2 : ℚ) : WithTop ℚ)
  have hcoefficient :
      ((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) =
      shift - 2 := by
    rw [← hpSucc, ← hpCast, htargetPrevious]
    dsimp only [shift]
    push_cast
    ring
  have hleftTranslate :
      (a.alphaValue p : WithTop ℚ) + ((-2 : ℚ) : WithTop ℚ) =
        (b.alphaValue p : WithTop ℚ) := by
    exact_mod_cast (show a.alphaValue p + (-2 : ℚ) =
      b.alphaValue p by linarith [hbetaSource])
  have hrightTranslate :
      ((shift : WithTop ℚ) + crossDefect) +
          ((-2 : ℚ) : WithTop ℚ) =
        ((shift - 2 : ℚ) : WithTop ℚ) + crossDefect := by
    rw [sub_eq_add_neg, WithTop.coe_add]
    ac_rfl
  have htranslated' :
      (a.alphaValue p : WithTop ℚ) + ((-2 : ℚ) : WithTop ℚ) ≤
        ((shift : WithTop ℚ) + crossDefect) +
          ((-2 : ℚ) : WithTop ℚ) := by
    simpa only [add_comm] using htranslated
  rw [hleftTranslate, hrightTranslate] at htranslated'
  have hprimary : (b.alphaValue p : WithTop ℚ) ≤
      a.representationPrimaryDefect b i := by
    unfold representationPrimaryDefect
    rw [hcoefficient]
    simpa only [crossDefect] using htranslated'
  have hnotInterior : ¬(1 < i.val ∧ i.val + 1 < n + 2) := by omega
  have hlower : (b.alphaValue p : WithTop ℚ) ≤
      a.representationAlpha b i := by
    rw [a.representationAlpha_eq_min_halfGap_prime b i,
      a.representationAlphaPrime_eq_primary_of_not_interior b i hnotInterior]
    exact le_min hhalf hprimary
  have hupper := a.representationAlpha_le_rightAlpha b hdefect i
  simpa only [p, hiOne] using le_antisymm hupper hlower

end BONG.GoodBONG

end Bong
