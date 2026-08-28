/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019CappedDominationOrderBound
import Bong.Bong.Beli2019Lemma79EvenTargetDomination

/-!
# Beli (2019), Lemma 7.9(ii), case 3: capped target domination

This is the square-bracket version of the first case-3 split.  If the
selected target order reaches the next intermediate order, the primary
candidate proves the bound against the complete capped target prefix.
Otherwise we retain the strict low-order witness for the type-I analysis.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- The easy capped-domination branch in case 3. -/
theorem lemma79_even_targetCapped_of_sourceNext_le
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (j : Fin (n + 1))
    (hsourceNext : b.order ⟨i.val, i.lt_large⟩ ≤
      c.order j.castSucc)
    (hdomination :
      (((((c.order j.castSucc -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ)) :
        WithTop ℚ) ≤
          c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val := by
  calc
    (b.representationAlphaValue c i : WithTop ℚ) ≤
        (((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) :
          WithTop ℚ) + c.prefixAlphaCap (i.val - 1) :=
      lemma79_representationAlphaValue_le_primaryRightCap b c i
    _ = (((((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ)) :
        WithTop ℚ) :=
      evenTarget_primaryRightCap_eq b c i hiTwo
    _ ≤ (((((c.order j.castSucc -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ)) :
        WithTop ℚ) :=
      evenTarget_coefficient_le_of_sourceNext_le b c i j hsourceNext
    _ ≤ c.truncatedPrefixDefect c
        ((-1) ^ (i.val / 2)) 0 i.val := hdomination

/-- Capped case 3 after its first domination split. -/
theorem lemma79_even_targetCapped_or_exists_lowWitness
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
        c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val ∨
      ∃ j : Fin (n + 1), Even j.val ∧ j.val + 1 < i.val ∧
        c.truncatedPrefixDefect c (-1) j.val (j.val + 2) ≤
          c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val ∧
        c.order j.castSucc < b.order ⟨i.val, i.lt_large⟩ ∧
        (((((c.order j.castSucc -
            c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
            c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ)) :
          WithTop ℚ) ≤
            c.truncatedPrefixDefect c
              ((-1) ^ (i.val / 2)) 0 i.val := by
  rcases c.exists_even_capped_domination_order_bound
      i.val i.pos i.lt_large.le hiEven with
    ⟨j, hjEven, hjlt, hjDefect, hdomination⟩
  have hdomination' :
      (((((c.order j.castSucc -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ)) :
        WithTop ℚ) ≤
          c.truncatedPrefixDefect c
            ((-1) ^ (i.val / 2)) 0 i.val := by
    have hpreviousIndex :
        (⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : Fin (n + 2)) = evenTargetPreviousIndex i := by
      apply Fin.ext
      rfl
    have hAlphaIndex :
        (⟨i.val - 2, by
          have hiPos := i.pos
          have hiLarge := i.lt_large
          omega⟩ : Fin (n + 1)) = evenTargetPreviousAlphaIndex i := by
      apply Fin.ext
      rfl
    rw [hpreviousIndex, hAlphaIndex] at hdomination
    exact hdomination
  by_cases hsourceNext : b.order ⟨i.val, i.lt_large⟩ ≤
      c.order j.castSucc
  · exact Or.inl (lemma79_even_targetCapped_of_sourceNext_le
      b c i hiTwo j hsourceNext hdomination')
  · exact Or.inr ⟨j, hjEven, hjlt, hjDefect,
      lt_of_not_ge hsourceNext,
      hdomination'⟩

end BONG.GoodBONG

end Bong
