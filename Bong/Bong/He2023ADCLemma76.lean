/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma710
import Bong.Bong.He2023ADCOddMaximalStructure
import Bong.Bong.He2023ADCEvenPenultimateObstruction
import Bong.Bong.Beli2019CappedDefectSharp

/-!
# He (2025), Lemma 7.6

The five capped-defect calculations are exposed separately.  Paper indices
are one-based; the source has rank `n+2=2*k+5` and every maximal target has
rank `n=2*k+3`.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V W : Type u} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- He (2025), Lemma 7.6(i), at the paper prefix `i=2*p`. -/
theorem heADC2025Lemma76i (k p : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 3))
    (hInitial : a.HeHuI1E (2 * k + 2) (by omega))
    (hM : Lattice.IsOMaximal r M)
    (hp : p ≤ k) :
    ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 (2 * p) (2 * p) := by
  have hsource := a.heADCExtremalPairs_prefixDefect p (by omega) (fun t ht ↦ ?_)
  · let C := b.heADC2025Proposition413 k hM
    have htarget := b.heADCExtremalPairs_prefixDefect p (by omega) (fun t ht ↦ ?_)
    · have hdom := a.truncatedPrefixDefect_selfPrefixes_domination b
        ((-1) ^ p) ((-1) ^ p) (2 * p) (2 * p)
      have hsign : (-1 : Kˣ) ^ p * (-1) ^ p = 1 := by
        rw [← pow_add]
        exact (show Even (p + p) from ⟨p, rfl⟩).neg_one_pow
      simpa only [hsign] using (le_min hsource htarget).trans hdom
    · let left : Fin (2 * k + 3) := ⟨2 * t, by omega⟩
      let right : Fin (2 * k + 3) := ⟨2 * t + 1, by omega⟩
      have hleft := C.initialOrders left (by dsimp only [left]; omega)
      have hright := C.initialOrders right (by dsimp only [right]; omega)
      have heven : Even (2 * t) := ⟨t, by omega⟩
      have hodd : ¬ Even (2 * t + 1) := by
        rintro ⟨s, hs⟩
        omega
      simp only [left, if_pos heven] at hleft
      simp only [right, if_neg hodd] at hright
      change b.order ⟨2 * t + 1, by omega⟩ -
          b.order ⟨2 * t, by omega⟩ = _
      rw [hleft, hright, sub_zero]
  · have hleft : a.order ⟨2 * t, by omega⟩ = 0 := by
      apply hInitial.oddOrder ⟨2 * t, by omega⟩
      simpa only [Fin.val_mk] using (show Odd (2 * t + 1) from ⟨t, by omega⟩)
    have hright : a.order ⟨2 * t + 1, by omega⟩ =
        -(2 * (ramificationIndex K : Int)) := by
      apply hInitial.evenOrder ⟨2 * t + 1, by omega⟩
      simpa only [Fin.val_mk] using (show Even (2 * t + 2) from ⟨t + 1, by omega⟩)
    change a.order ⟨2 * t + 1, by omega⟩ -
        a.order ⟨2 * t, by omega⟩ = _
    rw [hleft, hright, sub_zero]

/-- The full alternating source prefix used in Lemma 7.6(ii). -/
private theorem heADC2025Lemma76_sourcePrefix (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hInitial : a.HeHuI1E (2 * k + 2) (by omega)) :
    ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect a ((-1) ^ (k + 1)) 0 (2 * k + 2) := by
  have h := a.heADCExtremalPairs_prefixDefect (k + 1) (by omega) (fun t ht ↦ ?_)
  · simpa only [show 2 * (k + 1) = 2 * k + 2 by omega] using h
  · have hleft : a.order ⟨2 * t, by omega⟩ = 0 := by
      apply hInitial.oddOrder ⟨2 * t, by omega⟩
      simpa only [Fin.val_mk] using (show Odd (2 * t + 1) from ⟨t, by omega⟩)
    have hright : a.order ⟨2 * t + 1, by omega⟩ =
        -(2 * (ramificationIndex K : Int)) := by
      apply hInitial.evenOrder ⟨2 * t + 1, by omega⟩
      simpa only [Fin.val_mk] using (show Even (2 * t + 2) from ⟨t + 1, by omega⟩)
    change a.order ⟨2 * t + 1, by omega⟩ -
        a.order ⟨2 * t, by omega⟩ = _
    rw [hleft, hright, sub_zero]

/-- The standard-tail target prefix in Lemma 7.6(ii). -/
private theorem heADC2025Lemma76_targetStandardPrefix (k : Nat)
    (b : GoodBONG r M (2 * k + 3))
    (hM : Lattice.IsOMaximal r M)
    (hPenultimate : b.order ⟨2 * k + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int))) :
    ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      b.truncatedPrefixDefect b ((-1) ^ (k + 1)) 0 (2 * k + 2) := by
  let C := b.heADC2025Proposition413 k hM
  have h := b.heADCExtremalPairs_prefixDefect (k + 1) (by omega) (fun t ht ↦ ?_)
  · simpa only [show 2 * (k + 1) = 2 * k + 2 by omega] using h
  · let left : Fin (2 * k + 3) := ⟨2 * t, by omega⟩
    have hleft := C.initialOrders left (by dsimp only [left]; omega)
    have hright : b.order ⟨2 * t + 1, by omega⟩ =
        -(2 * (ramificationIndex K : Int)) := by
      by_cases htk : t = k
      · subst t
        exact hPenultimate
      · let right : Fin (2 * k + 3) := ⟨2 * t + 1, by omega⟩
        have h := C.initialOrders right (by dsimp only [right]; omega)
        have hodd : ¬ Even (2 * t + 1) := by
          rintro ⟨s, hs⟩
          omega
        simpa only [right, if_neg hodd] using h
    have heven : Even (2 * t) := ⟨t, by omega⟩
    simp only [left, if_pos heven] at hleft
    change b.order ⟨2 * t + 1, by omega⟩ -
        b.order ⟨2 * t, by omega⟩ = _
    rw [hleft, hright, sub_zero]

/-- The raised-tail target prefix has the exact lower bound needed in
Lemma 7.6(ii). -/
private theorem heADC2025Lemma76_targetRaisedPrefix (k : Nat)
    (b : GoodBONG r M (2 * k + 3))
    (hM : Lattice.IsOMaximal r M)
    (hPenultimate : b.order ⟨2 * k + 1, by omega⟩ =
      2 - 2 * (ramificationIndex K : Int)) :
    ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) ≤
      b.truncatedPrefixDefect b ((-1) ^ (k + 1)) 0 (2 * k + 2) := by
  let C := b.heADC2025Proposition413 k hM
  have h := b.truncatedPrefixDefect_alternating_ge 0 k (by omega)
      ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) (fun t ht ↦ ?_)
  · simpa only [zero_add, show 2 * (k + 1) = 2 * k + 2 by omega] using h
  · by_cases htk : t = k
    · subst t
      simpa only [zero_add, heADCAdjacentCappedDefect,
        heHuAdjacentCappedDefect] using (C.raisedTail hPenultimate).2.2.1.ge
    · let gap : Fin (2 * k + 2) := ⟨2 * t, by omega⟩
      let left : Fin (2 * k + 3) := ⟨2 * t, by omega⟩
      let right : Fin (2 * k + 3) := ⟨2 * t + 1, by omega⟩
      have hleft := C.initialOrders left (by dsimp only [left]; omega)
      have hright := C.initialOrders right (by dsimp only [right]; omega)
      have heven : Even (2 * t) := ⟨t, by omega⟩
      have hodd : ¬ Even (2 * t + 1) := by
        rintro ⟨s, hs⟩
        omega
      simp only [left, if_pos heven] at hleft
      simp only [right, if_neg hodd] at hright
      have hgap : b.orderGap gap = -(2 * (ramificationIndex K : Int)) := by
        unfold orderGap
        change b.order right - b.order left = _
        rw [hleft, hright, sub_zero]
      have hlocal := (b.heADC2025Proposition34 gap).alphaZeroDefect
        ((b.heADC2025Proposition34 gap).alphaZero.mpr hgap)
      have he : (1 : ℚ) ≤ ramificationIndex K := by
        exact_mod_cast ramificationIndex_pos (K := K)
      have hlower : ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) ≤
          ((2 * ramificationIndex K : ℚ) : WithTop ℚ) := by
        apply WithTop.coe_le_coe.mpr
        linarith
      exact hlower.trans (by
        simpa only [gap, heADCAdjacentCappedDefect, heHuAdjacentCappedDefect,
          zero_add] using hlocal)

/-- He (2025), Lemma 7.6(ii), in the two alternatives for `S_(n-1)`. -/
theorem heADC2025Lemma76ii (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 3))
    (hInitial : a.HeHuI1E (2 * k + 2) (by omega))
    (hM : Lattice.IsOMaximal r M) :
    (b.order ⟨2 * k + 1, by omega⟩ =
        -(2 * (ramificationIndex K : Int)) →
      ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
        a.truncatedPrefixDefect b 1 (2 * k + 2) (2 * k + 2)) ∧
    (b.order ⟨2 * k + 1, by omega⟩ =
        2 - 2 * (ramificationIndex K : Int) →
      a.truncatedPrefixDefect b 1 (2 * k + 2) (2 * k + 2) =
        ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ)) := by
  have hsource := a.heADC2025Lemma76_sourcePrefix k hInitial
  constructor
  · intro hPenultimate
    have htarget := b.heADC2025Lemma76_targetStandardPrefix k hM hPenultimate
    have hdom := a.truncatedPrefixDefect_selfPrefixes_domination b
      ((-1) ^ (k + 1)) ((-1) ^ (k + 1)) (2 * k + 2) (2 * k + 2)
    have hsign : (-1 : Kˣ) ^ (k + 1) * (-1) ^ (k + 1) = 1 := by
      rw [← pow_add]
      exact (show Even ((k + 1) + (k + 1)) from ⟨k + 1, rfl⟩).neg_one_pow
    rw [hsign] at hdom
    exact (le_min hsource htarget).trans hdom
  · intro hPenultimate
    have htarget := b.heADC2025Lemma76_targetRaisedPrefix k hM hPenultimate
    have hdom := a.truncatedPrefixDefect_selfPrefixes_domination b
      ((-1) ^ (k + 1)) ((-1) ^ (k + 1)) (2 * k + 2) (2 * k + 2)
    have hsign : (-1 : Kˣ) ^ (k + 1) * (-1) ^ (k + 1) = 1 := by
      rw [← pow_add]
      exact (show Even ((k + 1) + (k + 1)) from ⟨k + 1, rfl⟩).neg_one_pow
    rw [hsign] at hdom
    have hlower : ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) ≤
        a.truncatedPrefixDefect b 1 (2 * k + 2) (2 * k + 2) := by
      have htwoE : ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) ≤
          ((2 * ramificationIndex K : ℚ) : WithTop ℚ) := by
        apply WithTop.coe_le_coe.mpr
        linarith
      exact (le_min (htwoE.trans hsource) htarget).trans hdom
    have hupper := a.truncatedPrefixDefect_le_rightCap b 1
      (2 * k + 2) (2 * k + 2)
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hupper
    have htail := (b.heADC2025Proposition413 k hM).raisedTail hPenultimate
    have hupper' : a.truncatedPrefixDefect b 1 (2 * k + 2) (2 * k + 2) ≤
        (b.alphaValue ⟨2 * k + 1, by omega⟩ : WithTop ℚ) := by
      simpa only [show 2 * k + 2 - 1 = 2 * k + 1 by omega] using hupper
    rw [htail.2.2.2] at hupper'
    exact le_antisymm hupper' hlower

/-- He (2025), Lemma 7.6(iii).  The right-hand side is the paper's
`1-S_n`; Proposition 4.13 proves that `S_n` is zero or one. -/
theorem heADC2025Lemma76iii (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 3))
    (hInitial : a.HeHuI1E (2 * k + 2) (by omega))
    (hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1)
    (hM : Lattice.IsOMaximal r M) :
    a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) =
      ((((1 : Int) - b.order ⟨2 * k + 2, by omega⟩ : Int) : ℚ) :
        WithTop ℚ) := by
  letI : Beli2006AlphaLaws.{u, u} K := beliUniversalAlphaLaws
  let C := b.heADC2025Proposition413 k hM
  have hSourceEntries (t : Nat) (ht : t < 2 * k + 3) :
      Even (a.orderSequence.entryOrZero t) := by
    let i : Fin (2 * k + 5) := ⟨t, by omega⟩
    rw [a.orderSequence_entryOrZero_eq_order i]
    rcases Nat.even_or_odd t with htEven | htOdd
    · have horder : a.order i = 0 := by
        apply hInitial.oddOrder ⟨t, ht⟩
        simpa only [i, Fin.val_mk] using htEven.add_one
      rw [horder]
      exact Even.zero
    · have horder : a.order i = -(2 * (ramificationIndex K : Int)) := by
        have htBound : t < 2 * k + 2 := by
          rcases htOdd with ⟨d, hd⟩
          omega
        apply hInitial.evenOrder ⟨t, htBound⟩
        simpa only [i, Fin.val_mk] using htOdd.add_one
      rw [horder]
      exact ⟨-(ramificationIndex K : Int), by ring⟩
  have hSourceEven : Even (a.orderSequence.prefixSum (2 * k + 3)) :=
    a.orderSequence.prefixSum_even_of_entries_even (2 * k + 3) hSourceEntries
  have hTargetHeadEntries (t : Nat) (ht : t < 2 * k + 2) :
      Even (b.orderSequence.entryOrZero t) := by
    let i : Fin (2 * k + 3) := ⟨t, by omega⟩
    rw [b.orderSequence_entryOrZero_eq_order i]
    by_cases hInitialIndex : t ≤ 2 * k
    · have horder := C.initialOrders i (by simpa only [i, Fin.val_mk])
      rcases Nat.even_or_odd t with htEven | htOdd
      · simp only [i, if_pos htEven] at horder
        rw [horder]
        exact Even.zero
      · have htNotEven : ¬ Even t := by
          rintro ⟨d, hd⟩
          rcases htOdd with ⟨s, hs⟩
          omega
        simp only [i, if_neg htNotEven] at horder
        rw [horder]
        exact ⟨-(ramificationIndex K : Int), by ring⟩
    · have htLast : t = 2 * k + 1 := by omega
      rcases C.penultimate with hstandard | hraised
      · rw [show i = (⟨2 * k + 1, by omega⟩ : Fin (2 * k + 3)) by
          apply Fin.ext
          exact htLast, hstandard]
        exact ⟨-(ramificationIndex K : Int), by ring⟩
      · rw [show i = (⟨2 * k + 1, by omega⟩ : Fin (2 * k + 3)) by
          apply Fin.ext
          exact htLast, hraised]
        exact ⟨1 - (ramificationIndex K : Int), by ring⟩
  have hTargetHeadEven : Even (b.orderSequence.prefixSum (2 * k + 2)) :=
    b.orderSequence.prefixSum_even_of_entries_even (2 * k + 2) hTargetHeadEntries
  have hLast : b.order ⟨2 * k + 2, by omega⟩ = 0 ∨
      b.order ⟨2 * k + 2, by omega⟩ = 1 := by
    rcases C.penultimate with hstandard | hraised
    · exact (C.standardTail hstandard).1
    · exact Or.inl (C.raisedTail hraised).1
  rcases hLast with hzero | hone
  · have hTargetEven : Even (b.orderSequence.prefixSum (2 * k + 3)) := by
      rw [b.orderSequence.prefixSum_succ,
        b.orderSequence_entryOrZero_eq_order
          (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 3)), hzero]
      exact hTargetHeadEven.add Even.zero
    have hrawEven : Even (ordUnit K
        (a.prefixProduct (2 * k + 3) * b.prefixProduct (2 * k + 3))) := by
      rw [ordUnit_mul,
        a.ordUnit_prefixProduct_eq_orderSequence_prefixSum (2 * k + 3) (by omega),
        b.ordUnit_prefixProduct_eq_orderSequence_prefixSum (2 * k + 3) le_rfl]
      exact hSourceEven.add hTargetEven
    have hraw : (1 : WithTop ℚ) ≤ defectOrder (K := K)
        (a.prefixProduct (2 * k + 3) * b.prefixProduct (2 * k + 3)) :=
      defectOrder_one_le_of_even _ hrawEven
    have hsourceCap : a.prefixAlphaCap (2 * k + 3) = 1 := by
      rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
      have h := congrArg (fun z : ℚ ↦ (z : WithTop ℚ)) hAlpha
      convert h using 1 <;> norm_num
    have htargetCap : b.prefixAlphaCap (2 * k + 3) = ⊤ :=
      b.prefixAlphaCap_last
    unfold truncatedPrefixDefect
    simp only [one_mul, hsourceCap, htargetCap]
    rw [min_eq_left le_top, min_eq_right hraw, hzero]
    norm_num
  · have hTargetOdd : Odd (b.orderSequence.prefixSum (2 * k + 3)) := by
      rw [b.orderSequence.prefixSum_succ,
        b.orderSequence_entryOrZero_eq_order
          (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 3)), hone]
      exact hTargetHeadEven.add_odd odd_one
    have hrawOdd : Odd (ordUnit K
        (a.prefixProduct (2 * k + 3) * b.prefixProduct (2 * k + 3))) := by
      rw [ordUnit_mul,
        a.ordUnit_prefixProduct_eq_orderSequence_prefixSum (2 * k + 3) (by omega),
        b.ordUnit_prefixProduct_eq_orderSequence_prefixSum (2 * k + 3) le_rfl]
      exact hSourceEven.add_odd hTargetOdd
    rw [a.truncatedPrefixDefect_eq_zero_of_odd_order b (2 * k + 3) hrawOdd, hone]
    norm_num

/-- He (2025), Lemma 7.6(iv), in the two alternatives for `S_(n-1)`. -/
theorem heADC2025Lemma76iv (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 3))
    (hM : Lattice.IsOMaximal r M) :
    (b.order ⟨2 * k + 1, by omega⟩ =
        -(2 * (ramificationIndex K : Int)) →
      a.truncatedPrefixDefect b (-1) (2 * k + 3) (2 * k + 1) = 0) ∧
    (b.order ⟨2 * k + 1, by omega⟩ =
        2 - 2 * (ramificationIndex K : Int) →
      a.truncatedPrefixDefect b (-1) (2 * k + 3) (2 * k + 1) ≤ 1) := by
  letI : Beli2006AlphaLaws.{u, u} K := beliUniversalAlphaLaws
  have hcap := a.truncatedPrefixDefect_le_rightCap b (-1)
    (2 * k + 3) (2 * k + 1)
  rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
  have hcap' : a.truncatedPrefixDefect b (-1) (2 * k + 3) (2 * k + 1) ≤
      (b.alphaValue ⟨2 * k, by omega⟩ : WithTop ℚ) := by
    simpa only [show 2 * k + 1 - 1 = 2 * k by omega] using hcap
  have hnonnegative : (0 : WithTop ℚ) ≤
      a.truncatedPrefixDefect b (-1) (2 * k + 3) (2 * k + 1) :=
    a.truncatedPrefixDefect_nonneg b (-1) (2 * k + 3) (2 * k + 1)
  let C := b.heADC2025Proposition413 k hM
  constructor
  · intro hstandard
    have halpha := (C.standardTail hstandard).2.1
    rw [halpha] at hcap'
    exact le_antisymm (by simpa using hcap') hnonnegative
  · intro hraised
    have halpha := (C.raisedTail hraised).2.1
    rw [halpha] at hcap'
    simpa using hcap'

/-- He (2025), Lemma 7.6(v).  The hypotheses spell out the second
alternative in Lemma 7.5(ii), namely
`alpha_n=R_(n+1)+d[-a_n a_(n+1)]=1`. -/
theorem heADC2025Lemma76v (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 3))
    (hInitial : a.HeHuI1E (2 * k + 2) (by omega))
    (hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1)
    (hAdjacent : a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩ =
      (((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ))
    (hM : Lattice.IsOMaximal r M) :
    a.truncatedPrefixDefect b (-1) (2 * k + 4) (2 * k + 2) =
      (((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) := by
  let boundary : Fin (2 * k + 4) := ⟨2 * k + 2, by omega⟩
  have hBefore : a.order boundary.castSucc = 0 := by
    have h : a.order ⟨2 * k + 2, by omega⟩ = 0 := by
      apply hInitial.oddOrder (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 3))
      simpa only [Fin.val_mk] using
        (show Odd (2 * k + 3) from ⟨k + 1, by omega⟩)
    have hindex : boundary.castSucc =
        (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 5)) := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact h
  have hgap : a.orderGap boundary = a.order ⟨2 * k + 3, by omega⟩ := by
    unfold orderGap
    rw [hBefore]
    simp only [boundary, Fin.succ_mk, sub_zero]
  have hshape := (a.heADC2025Proposition34 boundary).alphaOne.mp (by
    simpa only [boundary] using hAlpha)
  rw [hgap] at hshape
  have hRLower : 2 - 2 * (ramificationIndex K : Int) ≤
      a.order ⟨2 * k + 3, by omega⟩ := by
    have hePos := ramificationIndex_pos (K := K)
    rcases hshape with (hendpoint | hone) | hmiddle
    · omega
    · omega
    · omega
  have hlocal : a.truncatedPrefixDefect a (-1) (2 * k + 4) (2 * k + 2) =
      (((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) := by
    rw [a.truncatedPrefixDefect_comm a (-1) (2 * k + 4) (2 * k + 2)]
    simpa only [heADCAdjacentCappedDefect, heHuAdjacentCappedDefect, boundary]
      using hAdjacent
  let C := b.heADC2025Proposition413 k hM
  rcases C.penultimate with hstandard | hraised
  · have hmixed := (a.heADC2025Lemma76ii k b hInitial hM).1 hstandard
    have hthresholdLt :
        (((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
          ((2 * (ramificationIndex K : ℚ)) : WithTop ℚ) := by
      apply WithTop.coe_lt_coe.mpr
      have hRLowerQ : (2 : ℚ) - 2 * (ramificationIndex K : ℚ) ≤
          (a.order ⟨2 * k + 3, by omega⟩ : ℚ) := by
        exact_mod_cast hRLower
      calc
        (1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) ≤
            2 * (ramificationIndex K : ℚ) - 1 := by linarith
        _ < 2 * (ramificationIndex K : ℚ) := by linarith
    have hlt : a.truncatedPrefixDefect a (-1) (2 * k + 4) (2 * k + 2) <
        a.truncatedPrefixDefect b 1 (2 * k + 2) (2 * k + 2) := by
      rw [hlocal]
      exact hthresholdLt.trans_le hmixed
    have hsharp := a.truncatedPrefixDefect_mul_eq_left_of_lt_right a b
      (-1) 1 (2 * k + 4) (2 * k + 2) (2 * k + 2) hlt
    simpa only [mul_one] using hsharp.trans hlocal
  · have hmixed := (a.heADC2025Lemma76ii k b hInitial hM).2 hraised
    by_cases hendpoint : a.order ⟨2 * k + 3, by omega⟩ =
        2 - 2 * (ramificationIndex K : Int)
    · have hthresholdEq :
          (((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) =
            ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) := by
        apply congrArg (fun z : ℚ ↦ (z : WithTop ℚ))
        rw [hendpoint]
        push_cast
        ring
      have hmixedThreshold :
          a.truncatedPrefixDefect b 1 (2 * k + 2) (2 * k + 2) =
            (((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) :=
        hmixed.trans hthresholdEq.symm
      have hdom := a.truncatedPrefixDefect_domination a b (-1) 1
        (2 * k + 4) (2 * k + 2) (2 * k + 2)
      have hlower :
          (((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) ≤
            a.truncatedPrefixDefect b (-1) (2 * k + 4) (2 * k + 2) := by
        rw [hlocal, hmixedThreshold, min_self] at hdom
        simpa only [mul_one] using hdom
      have hcap := a.truncatedPrefixDefect_le_rightCap b (-1)
        (2 * k + 4) (2 * k + 2)
      rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
      have hcap' : a.truncatedPrefixDefect b (-1) (2 * k + 4) (2 * k + 2) ≤
          (b.alphaValue ⟨2 * k + 1, by omega⟩ : WithTop ℚ) := by
        simpa only [show 2 * k + 2 - 1 = 2 * k + 1 by omega] using hcap
      rw [(C.raisedTail hraised).2.2.2] at hcap'
      rw [hthresholdEq]
      exact le_antisymm hcap' (by simpa only [hthresholdEq] using hlower)
    · have hRStrict : 2 - 2 * (ramificationIndex K : Int) <
          a.order ⟨2 * k + 3, by omega⟩ := lt_of_le_of_ne hRLower (Ne.symm hendpoint)
      have hthresholdLt :
          (((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
            ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) := by
        apply WithTop.coe_lt_coe.mpr
        have hRStrictQ : (2 : ℚ) - 2 * (ramificationIndex K : ℚ) <
            (a.order ⟨2 * k + 3, by omega⟩ : ℚ) := by
          exact_mod_cast hRStrict
        linarith
      have hlt : a.truncatedPrefixDefect a (-1) (2 * k + 4) (2 * k + 2) <
          a.truncatedPrefixDefect b 1 (2 * k + 2) (2 * k + 2) := by
        rw [hlocal, hmixed]
        exact hthresholdLt
      have hsharp := a.truncatedPrefixDefect_mul_eq_left_of_lt_right a b
        (-1) 1 (2 * k + 4) (2 * k + 2) (2 * k + 2) hlt
      simpa only [mul_one] using hsharp.trans hlocal

end BONG.GoodBONG

end Bong
