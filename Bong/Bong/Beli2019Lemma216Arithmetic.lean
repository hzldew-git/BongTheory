/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AuxiliaryAlphaBounds

/-!
# Beli (2019), Lemma 2.16: arithmetic core

After the two auxiliary minima have selected their primary candidates, the
equivalence in Lemma 2.16 is a cancellation identity.  This file proves that
identity over `WithTop ℚ`, including the cases in which a quadratic defect is
infinite, and specializes it to the two defects in condition (iii').
-/

namespace Bong

open Dyadic

universe u v w

/-- The affine cancellation at the heart of Lemma 2.16.  The proof treats
`⊤` explicitly, so square prefix products need no separate hypothesis. -/
theorem withTop_centralShift_lt_iff
    (e : ℚ) (rCurrent sCurrent sPrevious rNext : Int)
    (dPrevious dCurrent : WithTop ℚ) :
    ((2 * e + rCurrent : ℚ) : WithTop ℚ) <
        ((((rCurrent - sPrevious : Int) : ℚ) : WithTop ℚ) + dPrevious) +
          ((((sCurrent : Int) : ℚ) : WithTop ℚ) +
            ((((rNext - sCurrent : Int) : ℚ) : WithTop ℚ) + dCurrent)) ↔
      ((2 * e + sPrevious - rNext : ℚ) : WithTop ℚ) <
        dPrevious + dCurrent := by
  by_cases hPrevious : dPrevious = ⊤
  · subst dPrevious
    simp only [top_add, add_top]
    exact ⟨fun _ ↦ WithTop.coe_lt_top _, fun _ ↦ WithTop.coe_lt_top _⟩
  by_cases hCurrent : dCurrent = ⊤
  · subst dCurrent
    simp only [add_top]
    exact ⟨fun _ ↦ WithTop.coe_lt_top _, fun _ ↦ WithTop.coe_lt_top _⟩
  rw [← WithTop.coe_untop dPrevious hPrevious,
    ← WithTop.coe_untop dCurrent hCurrent]
  norm_cast
  push_cast
  constructor <;> intro h <;> linarith

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- The previous primary candidate in Lemma 2.16, written with the central
index's first v2 defect. -/
theorem representationPrimaryDefect_previous_eq
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1)) :
    a.representationPrimaryDefect b i.previous =
      (((a.order ⟨i.val - 1, by have := i.one_lt; have := i.lt_large; omega⟩ -
        b.order ⟨i.val - 2, by have := i.one_lt; have := i.le_small_succ; omega⟩ :
          Int) : ℚ) : WithTop ℚ) + a.centralPreviousDefect b i := by
  unfold representationPrimaryDefect centralPreviousDefect
    CentralRepresentationIndex.previous
  simp only [Nat.sub_add_cancel i.one_lt.le, Nat.sub_sub, one_add_one_eq_two]

/-- The current primary candidate in Lemma 2.16, written with the central
index's second v2 defect. -/
theorem representationPrimaryDefect_current_eq
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1)) (hi : i.val ≤ n + 1) :
    a.representationPrimaryDefect b (i.current hi) =
      (((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by have := i.one_lt; have := hi; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + a.centralCurrentDefect b i := by
  unfold representationPrimaryDefect centralCurrentDefect
    CentralRepresentationIndex.current
  rfl

/-- Lemma 2.16 after replacing `A_(i-1)` and `A_i` by their primary
candidates.  This is the exact affine identity used in both directions of
the paper's proof. -/
theorem centralPrimaryTrigger_iff_defectTrigger
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1)) (hi : i.val ≤ n + 1) :
    ((2 * (ramificationIndex K : ℚ) +
        (a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
        a.representationPrimaryDefect b i.previous +
          (((b.order ⟨i.val - 1, by
            have := i.one_lt
            have := hi
            omega⟩ : Int) : ℚ) : WithTop ℚ) +
            a.representationPrimaryDefect b (i.current hi) ↔
      ((2 * (ramificationIndex K : ℚ) +
          (b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : ℚ) -
          (a.order ⟨i.val, by have := i.lt_large; omega⟩ : ℚ) : ℚ) :
            WithTop ℚ) <
        a.centralPreviousDefect b i + a.centralCurrentDefect b i := by
  rw [a.representationPrimaryDefect_previous_eq b i,
    a.representationPrimaryDefect_current_eq b i hi]
  simpa only [Int.cast_sub, add_assoc] using withTop_centralShift_lt_iff
    (ramificationIndex K : ℚ)
    (a.order ⟨i.val - 1, by have := i.one_lt; have := i.lt_large; omega⟩)
    (b.order ⟨i.val - 1, by have := i.one_lt; have := hi; omega⟩)
    (b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩)
    (a.order ⟨i.val, by have := i.lt_large; omega⟩)
    (a.centralPreviousDefect b i) (a.centralCurrentDefect b i)

end BONG.GoodBONG

end Bong
