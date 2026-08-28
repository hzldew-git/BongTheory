/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma720Defect
import Bong.Bong.Beli2019Lemma716CentralComplete

/-!
# Beli (2019), Section 7 after Lemma 7.19: central condition

This file proves revised condition 2.1(iii') for all three replacement
normal forms. Type I and II have one non-tail stopping boundary; the proof
compares the source and target alpha caps before transporting the capped
defect trigger. Type III has no exceptional central boundary. Every later
index transports along the common suffix supplied by Lemma 7.19.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

variable [Beli2006AlphaLaws.{u, v} K]
variable [Beli2009AlphaParityLaws.{u, v} K]
variable [laws : DyadicDiscriminantClassLaws K]

private theorem centralRepresentationIndex_eq_of_val_eq720
    {m k : Nat} {i j : CentralRepresentationIndex m k} (h : i.val = j.val) :
    i = j := by
  cases i
  cases j
  simp_all

/-- At a type-I/II endpoint above `R`, the source alpha at the stopping
boundary attains its half-gap candidate. -/
theorem alphaValue_eq_halfGap_at_lemma717EndpointAbove
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData a R s)
    (habove : Lemma717EndpointAbove a R s)
    (hsInterior : s < n + 3) :
    a.alphaValue ⟨s - 1, by omega⟩ =
      a.halfGapValue ⟨s - 1, by omega⟩ := by
  let boundary : Fin (n + 2) := ⟨s - 1, by omega⟩
  let left : Fin (n + 3) := ⟨s - 1, by omega⟩
  let right : Fin (n + 3) := ⟨s, hsInterior⟩
  have hleft : a.order left = R - 2 * (ramificationIndex K : Int) := by
    have hindex : left = (⟨s - 1, by omega⟩ : Fin (n + 3)) := rfl
    rw [hindex]
    exact D.terminal
  have hright : R + 1 ≤ a.order right := by
    rcases habove with hfull | ⟨hs, hstrict⟩
    · omega
    · have hindex : right = (⟨s, hs⟩ : Fin (n + 3)) := by
        apply Fin.ext
        rfl
      rw [hindex]
      omega
  have hgap : 2 * (ramificationIndex K : Int) ≤ a.orderGap boundary := by
    unfold orderGap
    have hcast : boundary.castSucc = left := by
      apply Fin.ext
      rfl
    have hsucc : boundary.succ = right := by
      apply Fin.ext
      simp only [boundary, right, Fin.val_succ]
      have := D.two_le
      omega
    rw [hcast, hsucc, hleft]
    omega
  simpa only [boundary] using a.beli2009Lemma27_ii boundary hgap

theorem Lemma718TypeINormalForm.stoppingBoundaryAlpha_le_source
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s)
    (hsInterior : s < n + 3) :
    b.alphaValue ⟨s - 1, by omega⟩ ≤
      a.alphaValue ⟨s - 1, by omega⟩ := by
  let boundary : Fin (n + 2) := ⟨s - 1, by omega⟩
  let left : Fin (n + 3) := ⟨s - 1, by omega⟩
  let right : Fin (n + 3) := ⟨s, hsInterior⟩
  have ha := alphaValue_eq_halfGap_at_lemma717EndpointAbove
    a R s D.stopping D.typeI.1 hsInterior
  have hb := D.stoppingBoundaryAttainsHalfGap a b R s hsInterior
  have hright := D.tailOrder a b R s right le_rfl
  rcases D.stopping.even with ⟨d, hd⟩
  have hodd : Odd left.val := by
    exact ⟨d - 1, by
      dsimp only [left]
      have := D.stopping.two_le
      omega⟩
  have haLeft := D.sourceOrder_odd a b R s left (by
    dsimp only [left]
    have := D.stopping.two_le
    omega) hodd
  have hbLeft := D.targetOrder_odd a b R s left (by
    dsimp only [left]
    have := D.stopping.two_le
    omega) hodd
  rw [ha, hb]
  unfold halfGapValue orderGap
  have hcast : boundary.castSucc = left := by
    apply Fin.ext
    rfl
  have hsucc : boundary.succ = right := by
    apply Fin.ext
    simp only [boundary, right, Fin.val_succ]
    have := D.stopping.two_le
    omega
  rw [hcast, hsucc, ← hright, haLeft, hbLeft]
  norm_num
  linarith

theorem Lemma718TypeIINormalForm.stoppingBoundaryAlpha_le_source
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s)
    (hsInterior : s < n + 3) :
    b.alphaValue ⟨s - 1, by omega⟩ ≤
      a.alphaValue ⟨s - 1, by omega⟩ := by
  by_cases hsTwo : s = 2
  · have hvalues : ∀ i, a.valueUnit i = b.valueUnit i := by
      intro i
      rw [D.targetValues]
      unfold lemma718TypeIITargetValues
      split_ifs with h
      · omega
      · rfl
    exact le_of_eq
      (a.alphaValue_eq_of_valueUnits_eq b hvalues ⟨s - 1, by omega⟩).symm
  · let boundary : Fin (n + 2) := ⟨s - 1, by omega⟩
    let left : Fin (n + 3) := ⟨s - 1, by omega⟩
    let right : Fin (n + 3) := ⟨s, hsInterior⟩
    have ha := alphaValue_eq_halfGap_at_lemma717EndpointAbove
      a R s D.stopping D.typeII.1 hsInterior
    have hb := D.stoppingBoundaryAttainsHalfGap a b R s hsInterior
    have hright := D.tailOrder a b R s right le_rfl
    rcases D.stopping.even with ⟨d, hd⟩
    have hodd : Odd left.val := by
      exact ⟨d - 1, by
        dsimp only [left]
        have := D.stopping.two_le
        omega⟩
    have haLeft := D.sourceOrder_odd a b R s left (by
      dsimp only [left]
      have := D.stopping.two_le
      omega) hodd
    have hbLeft := D.targetOrder_odd a b R s left (by
      dsimp only [left]
      have := D.stopping.two_le
      omega) hodd
    have hleftTwo : ¬ left.val < 2 := by
      dsimp only [left]
      rcases D.stopping.even with ⟨d', hd'⟩
      have := D.stopping.two_le
      omega
    rw [if_neg hleftTwo] at hbLeft
    rw [ha, hb]
    unfold halfGapValue orderGap
    have hcast : boundary.castSucc = left := by
      apply Fin.ext
      rfl
    have hsucc : boundary.succ = right := by
      apply Fin.ext
      simp only [boundary, right, Fin.val_succ]
      have := D.stopping.two_le
      omega
    rw [hcast, hsucc, ← hright, haLeft, hbLeft]
    norm_num
    linarith

/-- A prefix isometry and a weak inequality of its alpha cap transport the
capped mixed defect in the direction needed at the stopping boundary. -/
theorem truncatedPrefixDefect_le_of_prefix_isometric_of_cap_le
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (epsilon : Kˣ)
    (k j : Nat) (hk : k ≤ n + 3)
    (hcap : b.prefixAlphaCap k ≤ a.prefixAlphaCap k)
    (hprefix : (a.prefixDiagonalSpace k hk).IsIsometric
      (b.prefixDiagonalSpace k hk)) :
    b.truncatedPrefixDefect c epsilon k j ≤
      a.truncatedPrefixDefect c epsilon k j := by
  have hraw := a.defectOrder_mixedPrefix_eq_of_prefix_isometric
    b c epsilon k j hk hprefix
  unfold truncatedPrefixDefect
  rw [hraw]
  exact min_le_min le_rfl (min_le_min hcap le_rfl)

theorem centralDefectTrigger_of_order_eq_of_defects_mono
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (i : CentralRepresentationIndex (n + 3) (n + 3))
    (horder : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩)
    (hprevious : b.centralPreviousDefect c i ≤
      a.centralPreviousDefect c i)
    (hcurrent : b.centralCurrentDefect c i =
      a.centralCurrentDefect c i)
    (htrigger : b.centralDefectTrigger c i) :
    a.centralDefectTrigger c i := by
  unfold centralDefectTrigger at htrigger ⊢
  constructor
  · rw [horder]
    exact htrigger.1
  · rw [horder]
    exact htrigger.2.trans_le
      (add_le_add hprevious (le_of_eq hcurrent))

theorem centralDefectTrigger_false_of_not_essential720
    (b : GoodBONG q M (n + 3)) (c : GoodBONG q N (n + 3))
    (horder : b.RepresentationOrderCondition c le_rfl)
    (hdefect : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 3) (n + 3))
    (hnot : ¬ b.IsEssentialFor c ⟨i.val - 1, by
      have := i.lt_large
      omega⟩) :
    ¬ b.centralDefectTrigger c i := by
  intro htrigger
  have halpha : b.centralAlphaTrigger c i :=
    ((b.beli2019Lemma216 c le_rfl horder hdefect) i).mpr htrigger
  exact hnot (b.isEssentialFor_of_centralAlphaTrigger c i halpha)

theorem prefixAlphaCap_le_of_internal_alphaValue_le
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (s : Nat) (hsPos : 0 < s) (hsInterior : s < n + 3)
    (hAlpha : b.alphaValue ⟨s - 1, by omega⟩ ≤
      a.alphaValue ⟨s - 1, by omega⟩) :
    b.prefixAlphaCap s ≤ a.prefixAlphaCap s := by
  rw [b.prefixAlphaCap_of_internal (n := n + 2) hsPos hsInterior,
    a.prefixAlphaCap_of_internal (n := n + 2) hsPos hsInterior]
  exact_mod_cast hAlpha

/-- The single non-tail instance of condition (iii') for type I/II. -/
theorem centralRepresentationAt_at_lemma718Stopping
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (Dstop : Lemma717StoppingData a R s)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (h719 : Beli2019Lemma719Conclusion a b R s)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (i : CentralRepresentationIndex (n + 3) (n + 3))
    (hi : i.val = s)
    (hcap : b.prefixAlphaCap s ≤ a.prefixAlphaCap s)
    (htrigger : b.centralDefectTrigger c i) :
    DiagonalRepresents
      (c.prefixValues (i.val - 1) (by
        have := i.le_small_succ
        omega))
      (b.prefixValues i.val (by
        have := i.lt_large
        omega)) := by
  subst s
  have hsInterior : i.val < n + 3 := i.lt_large
  have hprevious :
      centralPreviousDefect (m := n + 2) (n := n + 2) b c i ≤
        centralPreviousDefect (m := n + 2) (n := n + 2) a c i := by
    unfold centralPreviousDefect
    exact truncatedPrefixDefect_le_of_prefix_isometric_of_cap_le
      a b c (-1) i.val (i.val - 2) Dstop.le_rank hcap
        (h719.prefixIsometric_of_even a b R i.val i.val Dstop.even Dstop.le_rank)
  have hcurrent :
      centralCurrentDefect (m := n + 2) (n := n + 2) b c i =
        centralCurrentDefect (m := n + 2) (n := n + 2) a c i := by
    unfold centralCurrentDefect
    symm
    exact a.lemma716_tail_truncatedPrefixDefect_eq b c i.val
      (fun j hsj ↦ h719.alphaValue_eq_of_s_le a b R i.val j hsj)
      (fun k hsk hk ↦ h719.prefixIsometric_of_s_le a b R i.val k (by omega) hk)
      (-1) (i.val + 1) (i.val - 1) (by omega) hsInterior
  have horder : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩ :=
    horders ⟨i.val, i.lt_large⟩ le_rfl
  have hsourceTrigger :
      centralDefectTrigger (m := n + 2) (n := n + 2) a c i :=
    centralDefectTrigger_of_order_eq_of_defects_mono
      a b c i horder hprevious hcurrent htrigger
  have hsource := hac.centralRepresentations i hsourceTrigger
  have hiEven : Even i.val := Dstop.even
  have htransport := diagonalRepresents_prefixValues_of_prefix_isometric
    a b i.val i.lt_large.le
      (h719.prefixIsometric_of_even a b R i.val i.val hiEven i.lt_large.le)
  exact hsource.trans htransport

theorem Lemma718TypeINormalForm.centralRepresentationConditionsPrime
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s)
    (hac : RepresentationConditions a c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.CentralRepresentationConditionsPrime c := by
  have htriggers := a.beli2019Lemma216 c le_rfl
    hac.orderCondition hac.defectCondition
  have hacPrime : RepresentationConditionsPrime a c le_rfl :=
    (representationConditions_iff_prime a c le_rfl htriggers).mp hac
  have horderBC := D.representationOrderCondition a b c R s
    hac.orderCondition hnorm
  have hdefectBC := D.representationDefectCondition a b c R s hac hnorm
  have h719 := a.beli2019Lemma719_of_normalForm b R s
    (Beli2019Lemma718NormalForm.typeI D)
  intro i htrigger
  by_cases hiEarly : i.val < s
  · have hnot : ¬ b.IsEssentialFor c ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ := D.notEssential_prefix (n := n) a b c R s hnorm
      ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ (by
      change 0 < i.val - 1
      exact Nat.sub_pos_of_lt i.one_lt) (by
      change (i.val - 1) + 1 < s
      rw [Nat.sub_add_cancel i.one_lt.le]
      exact hiEarly)
    exact (centralDefectTrigger_false_of_not_essential720
      b c horderBC hdefectBC i hnot htrigger).elim
  · by_cases hiS : i.val = s
    · subst s
      have hsInterior : i.val < n + 3 := i.lt_large
      have hAlpha := D.stoppingBoundaryAlpha_le_source
        a b R i.val hsInterior
      have hiPos : 0 < i.val := Nat.zero_lt_of_lt i.one_lt
      have hcap := prefixAlphaCap_le_of_internal_alphaValue_le
        a b i.val hiPos hsInterior hAlpha
      exact centralRepresentationAt_at_lemma718Stopping
        a b c R i.val D.stopping hacPrime h719
          (fun j hsj ↦ D.tailOrder a b R i.val j hsj)
            i rfl hcap htrigger
    · have htail : s + 1 ≤ i.val := by omega
      exact a.lemma716_tail_centralRepresentationAt (n := n) b c s hacPrime
        (fun j hsj ↦ D.tailOrder a b R s j hsj)
        (fun j hsj ↦ h719.alphaValue_eq_of_s_le a b R s j hsj)
        (fun k hsk hk ↦ h719.prefixIsometric_of_s_le a b R s k (by omega) hk)
        i htail htrigger

theorem Lemma718TypeIINormalForm.centralRepresentationConditionsPrime
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s)
    (hac : RepresentationConditions a c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.CentralRepresentationConditionsPrime c := by
  have htriggers := a.beli2019Lemma216 c le_rfl
    hac.orderCondition hac.defectCondition
  have hacPrime : RepresentationConditionsPrime a c le_rfl :=
    (representationConditions_iff_prime a c le_rfl htriggers).mp hac
  have horderBC := D.representationOrderCondition a b c R s
    hac.orderCondition hnorm
  have hdefectBC := D.representationDefectCondition a b c R s hac hnorm
  have h719 := a.beli2019Lemma719_of_normalForm b R s
    (Beli2019Lemma718NormalForm.typeII D)
  intro i htrigger
  by_cases hiEarly : i.val < s
  · have hnot : ¬ b.IsEssentialFor c ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ := D.notEssential_prefix (n := n) a b c R s hnorm
      ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ (by
      change 0 < i.val - 1
      exact Nat.sub_pos_of_lt i.one_lt) (by
      change (i.val - 1) + 1 < s
      rw [Nat.sub_add_cancel i.one_lt.le]
      exact hiEarly)
    exact (centralDefectTrigger_false_of_not_essential720
      b c horderBC hdefectBC i hnot htrigger).elim
  · by_cases hiS : i.val = s
    · subst s
      have hsInterior : i.val < n + 3 := i.lt_large
      have hAlpha := D.stoppingBoundaryAlpha_le_source
        a b R i.val hsInterior
      have hiPos : 0 < i.val := Nat.zero_lt_of_lt i.one_lt
      have hcap := prefixAlphaCap_le_of_internal_alphaValue_le
        a b i.val hiPos hsInterior hAlpha
      exact centralRepresentationAt_at_lemma718Stopping
        a b c R i.val D.stopping hacPrime h719
          (fun j hsj ↦ D.tailOrder a b R i.val j hsj)
            i rfl hcap htrigger
    · have htail : s + 1 ≤ i.val := by omega
      exact a.lemma716_tail_centralRepresentationAt (n := n) b c s hacPrime
        (fun j hsj ↦ D.tailOrder a b R s j hsj)
        (fun j hsj ↦ h719.alphaValue_eq_of_s_le a b R s j hsj)
        (fun k hsk hk ↦ h719.prefixIsometric_of_s_le a b R s k (by omega) hk)
        i htail htrigger

theorem Lemma718TypeIIINormalForm.centralRepresentationConditionsPrime
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIIINormalForm a b R s)
    (hac : RepresentationConditions a c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.CentralRepresentationConditionsPrime c := by
  have htriggers := a.beli2019Lemma216 c le_rfl
    hac.orderCondition hac.defectCondition
  have hacPrime : RepresentationConditionsPrime a c le_rfl :=
    (representationConditions_iff_prime a c le_rfl htriggers).mp hac
  have horderBC := D.representationOrderCondition a b c R s
    hac.orderCondition hnorm
  have hdefectBC := D.representationDefectCondition a b c R s hac hnorm
  have h719 := a.beli2019Lemma719_of_normalForm b R s
    (Beli2019Lemma718NormalForm.typeIII D)
  intro i htrigger
  by_cases hiEarly : i.val ≤ s
  · have hpredLt : i.val - 1 < i.val :=
      Nat.sub_lt (Nat.zero_lt_of_lt i.one_lt) Nat.one_pos
    have hnot : ¬ b.IsEssentialFor c ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ := D.notEssential_prefix (n := n) a b c R s hnorm
      ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ (by
      change 0 < i.val - 1
      exact Nat.sub_pos_of_lt i.one_lt) (by
      change i.val - 1 < s
      exact hpredLt.trans_le hiEarly)
    exact (centralDefectTrigger_false_of_not_essential720
      b c horderBC hdefectBC i hnot htrigger).elim
  · have htail : s + 1 ≤ i.val :=
      Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hiEarly)
    exact a.lemma716_tail_centralRepresentationAt (n := n) b c s hacPrime
      (fun j hsj ↦ D.tailOrder a b R s j hsj)
      (fun j hsj ↦ h719.alphaValue_eq_of_s_le a b R s j hsj)
      (fun k hsk hk ↦ h719.prefixIsometric_of_s_le a b R s k (by omega) hk)
      i htail htrigger

/-- Condition 2.1(iii') survives every normal form of Lemma 7.18. -/
theorem Beli2019Lemma718NormalForm.centralRepresentationConditionsPrime
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Beli2019Lemma718NormalForm a b R s)
    (hac : RepresentationConditions a c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.CentralRepresentationConditionsPrime c := by
  cases D with
  | typeI data =>
      exact data.centralRepresentationConditionsPrime a b c R s hac hnorm
  | typeII data =>
      exact data.centralRepresentationConditionsPrime a b c R s hac hnorm
  | typeIII data =>
      exact data.centralRepresentationConditionsPrime a b c R s hac hnorm

end BONG.GoodBONG

end Bong
