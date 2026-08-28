/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma216Caps

/-!
# Beli (2019), Lemma 2.16: the auxiliary invariants

This file proves the ordinary-index part of Lemma 2.16 for Definition 5's
auxiliary invariants `A'_i`.  Under the revised defect inequality, the primary
candidate realizes both adjacent auxiliary invariants.  The two endpoint cases
are handled separately, where Definition 5 has no secondary candidate.
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
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- Under the revised defect inequality, the primary candidate realizes
`A'_(i-1)` at a non-endpoint index. -/
theorem representationAlphaPrime_previous_eq_primary_of_defectSum
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hi : 2 < i.val)
    (hcross : b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ < a.order ⟨i.val, by have := i.lt_large; omega⟩)
    (hsum :
      ((2 * (ramificationIndex K : ℚ) +
          (b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : ℚ) -
          (a.order ⟨i.val, by have := i.lt_large; omega⟩ : ℚ) : ℚ) :
            WithTop ℚ) <
        a.centralPreviousDefect b i + a.centralCurrentDefect b i) :
    a.representationAlphaPrime b i.previous =
      a.representationPrimaryDefect b i.previous := by
  have hprev : 1 < i.previous.val ∧ i.previous.val + 1 < m + 1 := by
    constructor
    · change 1 < i.val - 1
      omega
    · change i.val - 1 + 1 < m + 1
      have := i.lt_large
      omega
  have hcrossPrev :
      b.order ⟨i.previous.val - 1, by
        have := i.previous.le_small
        omega⟩ ≤
        a.order ⟨i.previous.val + 1, hprev.2⟩ := by
    have hbIndex : (⟨i.previous.val - 1, by
        have := i.previous.le_small
        omega⟩ : Fin (n + 1)) =
        ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ := by
      apply Fin.ext
      change (i.val - 1) - 1 = i.val - 2
      omega
    have haIndex : (⟨i.previous.val + 1, hprev.2⟩ : Fin (m + 1)) =
        ⟨i.val, by have := i.lt_large; omega⟩ := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    rw [hbIndex, haIndex]
    exact hcross.le
  have hnormal := a.representationAlphaPrime_eq_min_primary_current
    b i.previous hprev hcrossPrev
  rw [hnormal]
  apply min_eq_left
  apply le_of_lt
  rw [a.representationPrimaryDefect_previous_eq b i]
  let p : Fin n := ⟨i.val - 3, by
    have := i.le_small_succ
    omega⟩
  let c : ℚ := ((a.order ⟨i.val, by have := i.lt_large; omega⟩ -
    b.order ⟨i.val - 3, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ : Int) : ℚ)
  let d : ℚ := 2 * (ramificationIndex K : ℚ) +
    (b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ : ℚ) -
    (a.order ⟨i.val, by have := i.lt_large; omega⟩ : ℚ)
  have hpSucc : p.succ = ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have hpCast : p.castSucc = ⟨i.val - 3, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ := by
    apply Fin.ext
    rfl
  have hcore : a.centralPreviousDefect b i <
      (c : WithTop ℚ) + a.centralCurrentDefect b i := by
    apply withTop_lt_shift_add_of_affine_sum (d := d)
      (p := b.halfGapValue p)
    · simpa only [p] using a.centralPreviousDefect_le_halfGap b i hi
    · rw [halfGapValue, orderGap, hpSucc, hpCast]
      dsimp only [c, d]
      push_cast
      ring_nf
      exact le_rfl
    · simpa only [d] using hsum
  unfold representationSecondaryCurrentDefect
  let x : WithTop ℚ := (((a.order ⟨i.val - 1, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ - b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ : Int) : ℚ) : WithTop ℚ)
  let y : WithTop ℚ :=
    (((a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ + a.order ⟨i.val, by have := i.lt_large; omega⟩ -
      b.order ⟨i.val - 3, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ - b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ : Int) : ℚ) : WithTop ℚ)
  have hshift : x + (c : WithTop ℚ) = y := by
    dsimp only [x, c, y]
    norm_cast
    ring
  have hadd := WithTop.add_lt_add_left (x := x) (by simp [x]) hcore
  rw [← add_assoc] at hadd
  rw [hshift] at hadd
  simpa only [centralCurrentDefect, CentralRepresentationIndex.previous,
    Nat.sub_add_cancel i.one_lt.le, Nat.sub_sub, one_add_one_eq_two,
    show i.val - 1 + 2 = i.val + 1 by omega, x, y] using hadd

/-- Under the revised defect inequality, the primary candidate realizes
`A'_i` at a non-endpoint ordinary index. -/
theorem representationAlphaPrime_current_eq_primary_of_defectSum
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hi : i.val ≤ n + 1) (hinner : i.val + 1 < m + 1)
    (hcross : b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ < a.order ⟨i.val, by have := i.lt_large; omega⟩)
    (hsum :
      ((2 * (ramificationIndex K : ℚ) +
          (b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : ℚ) -
          (a.order ⟨i.val, by have := i.lt_large; omega⟩ : ℚ) : ℚ) :
            WithTop ℚ) <
        a.centralPreviousDefect b i + a.centralCurrentDefect b i) :
    a.representationAlphaPrime b (i.current hi) =
      a.representationPrimaryDefect b (i.current hi) := by
  have hcurrent : 1 < (i.current hi).val ∧
      (i.current hi).val + 1 < m + 1 := by
    constructor
    · change 1 < i.val
      exact i.one_lt
    · change i.val + 1 < m + 1
      exact hinner
  have hnormal := a.representationAlphaPrime_eq_min_primary_previous
    b (i.current hi) hcurrent hcross.le
  rw [hnormal]
  apply min_eq_left
  apply le_of_lt
  rw [a.representationPrimaryDefect_current_eq b i hi]
  let p : Fin m := ⟨i.val, by omega⟩
  let c : ℚ := ((a.order ⟨i.val + 1, hinner⟩ -
    b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ : Int) : ℚ)
  let d : ℚ := 2 * (ramificationIndex K : ℚ) +
    (b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ : ℚ) -
    (a.order ⟨i.val, by have := i.lt_large; omega⟩ : ℚ)
  have hpSucc : p.succ = ⟨i.val + 1, hinner⟩ := by
    apply Fin.ext
    rfl
  have hpCast : p.castSucc = ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    rfl
  have hcore : a.centralCurrentDefect b i <
      (c : WithTop ℚ) + a.centralPreviousDefect b i := by
    apply withTop_lt_shift_add_of_affine_sum (d := d)
      (p := a.halfGapValue p)
    · simpa only [p] using a.centralCurrentDefect_le_halfGap b i hinner
    · rw [halfGapValue, orderGap, hpSucc, hpCast]
      dsimp only [c, d]
      push_cast
      ring_nf
      exact le_rfl
    · simpa only [d, add_comm] using hsum
  unfold representationSecondaryPreviousDefect
  let x : WithTop ℚ := (((a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 1, by
      have := i.one_lt
      have := hi
      omega⟩ : Int) : ℚ) : WithTop ℚ)
  let y : WithTop ℚ :=
    (((a.order ⟨i.val, i.lt_large⟩ +
      a.order ⟨i.val + 1, hinner⟩ -
      b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ - b.order ⟨i.val - 1, by
        have := i.one_lt
        have := hi
        omega⟩ : Int) : ℚ) : WithTop ℚ)
  have hshift : x + (c : WithTop ℚ) = y := by
    dsimp only [x, c, y]
    norm_cast
    ring
  have hadd := WithTop.add_lt_add_left (x := x) (by simp [x]) hcore
  rw [← add_assoc] at hadd
  rw [hshift] at hadd
  simpa only [centralPreviousDefect, CentralRepresentationIndex.current,
    Nat.add_comm, x, y] using hadd

/-- The first adjacent auxiliary invariant is primary whenever the revised
defect inequality holds.  At `i = 2` this follows directly from the endpoint
clause of Definition 5. -/
theorem representationAlphaPrime_previous_eq_primary
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hcross : b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ < a.order ⟨i.val, by have := i.lt_large; omega⟩)
    (hsum :
      ((2 * (ramificationIndex K : ℚ) +
          (b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : ℚ) -
          (a.order ⟨i.val, by have := i.lt_large; omega⟩ : ℚ) : ℚ) :
            WithTop ℚ) <
        a.centralPreviousDefect b i + a.centralCurrentDefect b i) :
    a.representationAlphaPrime b i.previous =
      a.representationPrimaryDefect b i.previous := by
  by_cases hi : 2 < i.val
  · exact a.representationAlphaPrime_previous_eq_primary_of_defectSum
      b i hi hcross hsum
  · apply a.representationAlphaPrime_eq_primary_of_not_interior
    simp only [CentralRepresentationIndex.previous]
    omega

/-- The second adjacent auxiliary invariant is primary whenever the revised
defect inequality holds.  At the final source boundary this is again the
endpoint clause of Definition 5. -/
theorem representationAlphaPrime_current_eq_primary
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hi : i.val ≤ n + 1)
    (hcross : b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ < a.order ⟨i.val, by have := i.lt_large; omega⟩)
    (hsum :
      ((2 * (ramificationIndex K : ℚ) +
          (b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : ℚ) -
          (a.order ⟨i.val, by have := i.lt_large; omega⟩ : ℚ) : ℚ) :
            WithTop ℚ) <
        a.centralPreviousDefect b i + a.centralCurrentDefect b i) :
    a.representationAlphaPrime b (i.current hi) =
      a.representationPrimaryDefect b (i.current hi) := by
  by_cases hinner : i.val + 1 < m + 1
  · exact a.representationAlphaPrime_current_eq_primary_of_defectSum
      b i hi hinner hcross hsum
  · apply a.representationAlphaPrime_eq_primary_of_not_interior
    simp only [CentralRepresentationIndex.current]
    omega

/-- Lemma 2.16 for the ordinary-index auxiliary invariants `A'_(i-1)` and
`A'_i`, assuming the strict order comparison common to both triggers. -/
theorem centralAlphaPrimeTrigger_iff_defectSum
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hi : i.val ≤ n + 1)
    (hcross : b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ < a.order ⟨i.val, by have := i.lt_large; omega⟩) :
    (((2 * (ramificationIndex K : ℚ) +
        (a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
        a.representationAlphaPrime b i.previous +
          (((b.order ⟨i.val - 1, by
            have := i.one_lt
            have := hi
            omega⟩ : Int) : ℚ) : WithTop ℚ) +
            a.representationAlphaPrime b (i.current hi)) ↔
      ((2 * (ramificationIndex K : ℚ) +
          (b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : ℚ) -
          (a.order ⟨i.val, by have := i.lt_large; omega⟩ : ℚ) : ℚ) :
            WithTop ℚ) <
        a.centralPreviousDefect b i + a.centralCurrentDefect b i := by
  constructor
  · intro h
    apply (a.centralPrimaryTrigger_iff_defectTrigger b i hi).mp
    exact h.trans_le (add_le_add
      (add_le_add
        (a.representationAlphaPrime_le_primaryDefect b i.previous) le_rfl)
      (a.representationAlphaPrime_le_primaryDefect b (i.current hi)))
  · intro h
    have hprevious : a.representationAlphaPrime b i.previous =
        a.representationPrimaryDefect b i.previous := by
      letI : Beli2006AlphaLaws.{u, w} K := targetLaws
      exact a.representationAlphaPrime_previous_eq_primary b i hcross h
    have hcurrent : a.representationAlphaPrime b (i.current hi) =
        a.representationPrimaryDefect b (i.current hi) := by
      letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
      exact a.representationAlphaPrime_current_eq_primary b i hi hcross h
    rw [hprevious, hcurrent]
    exact (a.centralPrimaryTrigger_iff_defectTrigger b i hi).mpr h

end BONG.GoodBONG

end Bong
