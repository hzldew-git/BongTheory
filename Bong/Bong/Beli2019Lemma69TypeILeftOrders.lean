/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeILeft
import Bong.Bong.Beli2009TwoAdic

/-!
# Beli (2019), Lemma 6.9(ii): the normalized type-I left profile

Before the first canonical type-I switch, every even source entry is
constant.  The corresponding target entries differ by `+1,-1`; this is the
order pattern used in the source-alpha branch of Lemma 6.9(ii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Order identities at an even boundary in the type-I left profile. -/
theorem lemma69_typeI_left_boundary_orders
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : Nat) (hiTwo : 2 ≤ i) (hiLeft : i ≤ C.leftSwitch)
    (hiEven : Even i) :
    a.orderSequence.entryOrZero i =
        a.orderSequence.entryOrZero (i - 2) ∧
      b.orderSequence.entryOrZero (i - 2) =
        a.orderSequence.entryOrZero (i - 2) + 1 ∧
      b.orderSequence.entryOrZero (i - 1) =
        a.orderSequence.entryOrZero (i - 1) - 1 := by
  have hpreviousEven : Even (i - 2) := by
    rcases hiEven with ⟨m, hm⟩
    exact ⟨m - 1, by omega⟩
  have hsourceCurrent := C.source_to_anchor i
    (hiLeft.trans C.left_le_anchor) hiEven
  have hsourcePrevious := C.source_to_anchor (i - 2)
    ((Nat.sub_le i 2).trans hiLeft |>.trans C.left_le_anchor)
    hpreviousEven
  have hsourceEq := hsourceCurrent.trans hsourcePrevious.symm
  have htargetPrevious := C.target_before_left (i - 2)
    (by omega) hpreviousEven
  have htargetPreviousGap : b.orderSequence.entryOrZero (i - 2) =
      a.orderSequence.entryOrZero (i - 2) + 1 := by
    rw [hsourcePrevious]
    exact htargetPrevious
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hpairParity : Even (D.anchor - (i - 2)) := by
    rcases hanchorEven with ⟨m, hm⟩
    rcases hiEven with ⟨r, hr⟩
    have hiAnchor : i ≤ D.anchor := hiLeft.trans C.left_le_anchor
    exact ⟨m - r + 1, by omega⟩
  have hpair := D.profile.leftPairEq (i - 2) (by
      have hleftAnchor := C.left_le_anchor
      omega) hpairParity
  rw [show i - 2 + 1 = i - 1 by omega] at hpair
  have htargetCurrent : b.orderSequence.entryOrZero (i - 1) =
      a.orderSequence.entryOrZero (i - 1) - 1 := by
    omega
  exact ⟨hsourceEq, htargetPreviousGap, htargetCurrent⟩

/-- A source alpha bounded by one is exactly one when the target adjacent
gap is the source adjacent gap minus two. -/
theorem alpha_eq_one_of_le_one_of_targetGap_sub_two
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (p : Fin (n + 1)) (halphaLe : a.alphaValue p ≤ 1)
    (hgap : b.orderGap p = a.orderGap p - 2) :
    a.alphaValue p = 1 := by
  have htargetLower := b.orderGap_ge_neg_two_mul_e p
  have hsourceGapStrict :
      -(2 * (ramificationIndex K : Int)) < a.orderGap p := by
    omega
  have halphaNe : a.alphaValue p ≠ 0 := by
    intro hzero
    have hsourceBottom := (a.alpha_p2 p).2.mp hzero
    exact (ne_of_gt hsourceGapStrict) hsourceBottom
  have halphaNonnegative := (a.alpha_p2 p).1
  have halphaIntegral : IsRationalInteger (a.alphaValue p) := by
    rcases a.beli2009Corollary28_iii p with hsmall | hlarge
    · exact hsmall.2.2
    · have honeTwoE : (1 : ℚ) ≤ 2 * (ramificationIndex K : ℚ) := by
        have hePos := ramificationIndex_pos (K := K)
        exact_mod_cast (show (1 : Int) ≤
          2 * (ramificationIndex K : Int) by omega)
      have hleTwoE : a.alphaValue p ≤
          2 * (ramificationIndex K : ℚ) := halphaLe.trans honeTwoE
      exact (not_lt_of_ge hleTwoE hlarge.1).elim
  rcases halphaIntegral with ⟨z, hz⟩
  have hzNonnegative : (0 : Int) ≤ z := by
    exact_mod_cast (show (0 : ℚ) ≤ (z : ℚ) by
      simpa only [← hz] using halphaNonnegative)
  have hzLe : z ≤ (1 : Int) := by
    exact_mod_cast (show (z : ℚ) ≤ 1 by
      simpa only [← hz] using halphaLe)
  have hzNe : z ≠ 0 := by
    intro hzZero
    apply halphaNe
    rw [hz, hzZero]
    norm_num
  have hzOne : z = 1 := by omega
  rw [hz, hzOne]
  norm_num

/-- The alpha immediately before any even boundary in the type-I left
profile is one. -/
theorem lemma69_typeI_left_previousAlpha_eq_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (hdefect : a.RepresentationDefectCondition b)
    (i : Nat) (hiTwo : 2 ≤ i) (hiLeft : i ≤ C.leftSwitch)
    (hiEven : Even i) :
    a.alphaValue ⟨i - 2, by
      have hbound := C.left_le_anchor.trans_lt D.anchor_bound
      omega⟩ = 1 := by
  have horders := lemma69_typeI_left_boundary_orders
    a b D C hfirst i hiTwo hiLeft hiEven
  let p : Fin (n + 1) := ⟨i - 2, by
    have hbound := C.left_le_anchor.trans_lt D.anchor_bound
    omega⟩
  have halphaLe : a.alphaValue p ≤ 1 := by
    simpa only [p] using beli2019Lemma69_i_typeI_sourceLeftTail
      a b D C hfirst hleftPos hdefect (i - 2) (by omega) (by
        rcases hiEven with ⟨m, hm⟩
        exact ⟨m - 1, by omega⟩)
  have hpCast : p.castSucc =
      (⟨i - 2, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hpSucc : p.succ =
      (⟨i - 1, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have htargetPrevious : b.order p.castSucc =
      a.order p.castSucc + 1 := by
    rw [hpCast, ← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact horders.2.1
  have htargetCurrent : b.order p.succ = a.order p.succ - 1 := by
    rw [hpSucc, ← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact horders.2.2
  have hgap : b.orderGap p = a.orderGap p - 2 := by
    unfold orderGap
    rw [htargetPrevious, htargetCurrent]
    ring
  simpa only [p] using alpha_eq_one_of_le_one_of_targetGap_sub_two
    a b p halphaLe hgap

end BONG.GoodBONG

end Bong
