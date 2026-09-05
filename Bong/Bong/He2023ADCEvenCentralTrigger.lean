/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCPublishedRepresentation
import Bong.Bong.He2023ADCEvenPenultimateObstruction
import Bong.Bong.He2023ADCEvenSecondTests

/-!
# The capped-defect trigger in He (2025), Lemma 6.6

These support lemmas establish the literal published condition-(iii) trigger
from the alternating source head and raised target pair. They do not assume
that the next source order is zero or that either lattice represents the other.
The separate prefix non-representation is needed to complete Lemma 6.6.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The two full even prefixes in Lemma 6.6 have mixed capped defect at least 2e. -/
theorem heADCEvenCentral_fullMixedDefect (k : Nat)
    (a : GoodBONG q L (2 * k + 4)) (b : GoodBONG r M (2 * k + 2))
    (hhead : ∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hTarget : ∀ i : Fin (2 * k + 2), b.order i = heADCMaximalOrderProfile (K := K) k
      ![1, 1 - 2 * (ramificationIndex K : Int)] ⟨i.val, by omega⟩) :
    ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 (2 * k + 2) (2 * k + 2) := by
  have hsource := a.heADCExtremalPairs_prefixDefect (k + 1) (by omega) (fun t ht ↦ ?_)
  · have htarget := b.heADCExtremalPairs_prefixDefect (k + 1) (by omega) (fun t ht ↦ ?_)
    · have hdom := a.truncatedPrefixDefect_selfPrefixes_domination b
        ((-1) ^ (k + 1)) ((-1) ^ (k + 1)) (2 * (k + 1)) (2 * (k + 1))
      have hsign : (-1 : Kˣ) ^ (k + 1) * (-1) ^ (k + 1) = 1 := by
        rw [← pow_add]
        exact (show Even (k + 1 + (k + 1)) from ⟨k + 1, rfl⟩).neg_one_pow
      simpa only [hsign, show 2 * (k + 1) = 2 * k + 2 by omega] using
        (le_min hsource htarget).trans hdom
    · have hleft := hTarget ⟨2 * t, by omega⟩
      have hright := hTarget ⟨2 * t + 1, by omega⟩
      change b.order ⟨2 * t + 1, by omega⟩ - b.order ⟨2 * t, by omega⟩ = _
      by_cases htk : t = k
      · subst t
        simp [heADCMaximalOrderProfile, show ¬ 2 * k + 1 < 2 * k by omega,
          show 2 * k + 1 - 2 * k = 1 by omega] at hleft hright
        rw [hleft, hright]
        omega
      · have heven : Even (2 * t) := ⟨t, by omega⟩
        have hodd : ¬ Even (2 * t + 1) := by rintro ⟨s, hs⟩; omega
        simp only [heADCMaximalOrderProfile, dif_pos (show 2 * t < 2 * k by omega),
          if_pos heven] at hleft
        simp only [heADCMaximalOrderProfile, dif_pos (show 2 * t + 1 < 2 * k by omega),
          if_neg hodd] at hright
        rw [hleft, hright, sub_zero]
  · have heven : Even (2 * t) := ⟨t, by omega⟩
    have hodd : ¬ Even (2 * t + 1) := by rintro ⟨s, hs⟩; omega
    have hleft := hhead ⟨2 * t, by omega⟩
    have hright := hhead ⟨2 * t + 1, by omega⟩
    simp only [if_pos heven] at hleft
    simp only [if_neg hodd] at hright
    change a.order ⟨2 * t + 1, by omega⟩ - a.order ⟨2 * t, by omega⟩ = _
    rw [hleft, hright, sub_zero]

/-- The current central defect exceeds the exact threshold in Lemma 6.6. -/
theorem heADCEvenCentral_currentDefect_gt (k : Nat)
    (a : GoodBONG q L (2 * k + 4)) (b : GoodBONG r M (2 * k + 2))
    (hhead : ∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hTarget : ∀ i : Fin (2 * k + 2), b.order i = heADCMaximalOrderProfile (K := K) k
      ![1, 1 - 2 * (ramificationIndex K : Int)] ⟨i.val, by omega⟩)
    (hR : 2 - 2 * (ramificationIndex K : Int) ≤ a.order ⟨2 * k + 3, by omega⟩)
    (hAdjacent : ((1 - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
      a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩) :
    ((1 - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
      a.centralCurrentDefect b (heHuLemma43CentralIndex k le_rfl) := by
  let threshold : WithTop ℚ := (1 - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ)
  have hsmall : threshold < ((2 * ramificationIndex K : ℚ) : WithTop ℚ) := by
    apply WithTop.coe_lt_coe.mpr
    have hRQ : (2 : ℚ) - 2 * (ramificationIndex K : ℚ) ≤
        (a.order ⟨2 * k + 3, by omega⟩ : ℚ) := by exact_mod_cast hR
    linarith
  have hfull := hsmall.trans_le (a.heADCEvenCentral_fullMixedDefect k b hhead hTarget)
  have hadj : threshold < a.truncatedPrefixDefect a (-1) (2 * k + 4) (2 * k + 2) := by
    rw [a.truncatedPrefixDefect_comm a]
    exact hAdjacent
  have hdom := a.truncatedPrefixDefect_domination a b (-1) 1
    (2 * k + 4) (2 * k + 2) (2 * k + 2)
  have hout := (lt_min hadj hfull).trans_le hdom
  simpa only [centralCurrentDefect, heHuLemma43CentralIndex, mul_one,
    show 2 * k + 3 + 1 = 2 * k + 4 by omega,
    show 2 * k + 3 - 1 = 2 * k + 2 by omega] using hout

/-- The literal published condition-(iii) trigger at i=n+1 in Lemma 6.6. -/
theorem heADCEvenCentral_defectTrigger (k : Nat)
    (a : GoodBONG q L (2 * k + 4)) (b : GoodBONG r M (2 * k + 2))
    (hhead : ∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hTarget : ∀ i : Fin (2 * k + 2), b.order i = heADCMaximalOrderProfile (K := K) k
      ![1, 1 - 2 * (ramificationIndex K : Int)] ⟨i.val, by omega⟩)
    (hR : 2 - 2 * (ramificationIndex K : Int) ≤ a.order ⟨2 * k + 3, by omega⟩)
    (hAdjacent : ((1 - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
      a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩) :
    a.centralDefectTrigger b (heHuLemma43CentralIndex k le_rfl) := by
  let i := heHuLemma43CentralIndex k le_rfl
  have hlast : b.order ⟨2 * k + 1, by omega⟩ = 1 - 2 * (ramificationIndex K : Int) := by
    simpa [heADCMaximalOrderProfile, show ¬ 2 * k + 1 < 2 * k by omega,
      show 2 * k + 1 - 2 * k = 1 by omega] using hTarget ⟨2 * k + 1, by omega⟩
  have hindex : (⟨i.val - 2, by dsimp [i, heHuLemma43CentralIndex]; omega⟩ :
      Fin (2 * k + 2)) = ⟨2 * k + 1, by omega⟩ := by
    apply Fin.ext
    dsimp [i, heHuLemma43CentralIndex]
    omega
  change b.order ⟨i.val - 2, _⟩ < a.order ⟨i.val, _⟩ ∧ _
  constructor
  · rw [hindex, hlast]
    change 1 - 2 * (ramificationIndex K : Int) < a.order ⟨2 * k + 3, by omega⟩
    omega
  · have hcurrent := a.heADCEvenCentral_currentDefect_gt k b hhead hTarget hR hAdjacent
    have hprevious : (0 : WithTop ℚ) ≤ a.centralPreviousDefect b i :=
      a.truncatedPrefixDefect_nonneg b (-1) i.val (i.val - 2)
    have hsum := add_le_add hprevious
      (le_rfl : a.centralCurrentDefect b i ≤ a.centralCurrentDefect b i)
    rw [zero_add] at hsum
    change ((2 * (ramificationIndex K : ℚ) + (b.order ⟨i.val - 2, _⟩ : ℚ) -
      (a.order ⟨i.val, _⟩ : ℚ) : ℚ) : WithTop ℚ) < _
    rw [hindex, hlast]
    have hid : 2 * (ramificationIndex K : ℚ) +
        ((1 - 2 * (ramificationIndex K : Int) : Int) : ℚ) -
        (a.order ⟨2 * k + 3, by omega⟩ : ℚ) =
        1 - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) := by
      push_cast
      ring
    change ((2 * (ramificationIndex K : ℚ) +
      ((1 - 2 * (ramificationIndex K : Int) : Int) : ℚ) -
      (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) < _
    rw [hid]
    exact hcurrent.trans_le hsum

end BONG.GoodBONG

end Bong
