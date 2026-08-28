/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019DominationOrderBound
import Bong.Bong.Beli2019AuxiliaryAlphaBounds
import Bong.Bong.Beli2006SectionFourInvariants

/-!
# Beli (2019), Lemma 7.9(ii), case 3: target domination

At an even boundary, domination selects an earlier adjacent target pair.
If its first order is at least the next intermediate order, the primary
candidate and the target alpha cap immediately prove the required defect
bound. Otherwise the same argument returns the strict low-order witness
used by the remaining type-I analysis in the paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- The target entry immediately before a representation boundary. -/
def evenTargetPreviousIndex
    (i : RepresentationIndex (n + 2) (n + 2)) : Fin (n + 2) :=
  ⟨i.val - 1, (Nat.sub_le i.val 1).trans_lt i.lt_large⟩

/-- The target alpha index immediately before `evenTargetPreviousIndex`. -/
def evenTargetPreviousAlphaIndex
    (i : RepresentationIndex (n + 2) (n + 2)) : Fin (n + 1) :=
  ⟨i.val - 2, by
    have hiPos := i.pos
    have hiLarge := i.lt_large
    omega⟩

/-- Addition by a rational preserves an inequality after embedding in
`WithTop ℚ`; keeping this coercion lemma abstract prevents unwanted
unfolding of alpha values in later proofs. -/
theorem withTopRat_coe_add_le_coe_add_right {x y z : ℚ} (h : x ≤ y) :
    ((x + z : ℚ) : WithTop ℚ) ≤ ((y + z : ℚ) : WithTop ℚ) :=
  WithTop.coe_le_coe.mpr (add_le_add_left h z)

/-- The internal cap at an even target boundary is its preceding alpha. -/
theorem evenTarget_prefixAlphaCap
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) :
    c.prefixAlphaCap (i.val - 1) =
      (c.alphaValue (evenTargetPreviousAlphaIndex i) : WithTop ℚ) := by
  rw [c.prefixAlphaCap_of_internal (i := i.val - 1) (by omega)
    ((Nat.sub_le i.val 1).trans_lt i.lt_large)]
  apply congrArg (fun k : Fin (n + 1) =>
    (c.alphaValue k : WithTop ℚ))
  apply Fin.ext
  simp only [evenTargetPreviousAlphaIndex]
  omega

/-- The auxiliary-primary estimate with `representationAlphaValue` on the
left; this avoids unfolding the finite minimum defining the alpha. -/
theorem lemma79_representationAlphaValue_le_primaryRightCap
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      (((b.order ⟨i.val, i.lt_large⟩ -
        c.order (evenTargetPreviousIndex i) : Int) : ℚ) : WithTop ℚ) +
        c.prefixAlphaCap (i.val - 1) := by
  have hprime := b.representationAlphaPrime_le_primaryRightCap c i
  have hindex :
      (⟨i.val - 1, by
        have := i.le_small
        omega⟩ : Fin (n + 2)) = evenTargetPreviousIndex i := by
    apply Fin.ext
    rfl
  rw [hindex] at hprime
  rw [b.coe_representationAlphaValue c i]
  exact (b.representationAlpha_le_prime c i).trans hprime

/-- Replacing the internal target cap by its alpha produces the rational
coefficient used in the domination estimate. -/
theorem evenTarget_primaryRightCap_eq
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) :
    (((b.order ⟨i.val, i.lt_large⟩ -
        c.order (evenTargetPreviousIndex i) : Int) : ℚ) : WithTop ℚ) +
        c.prefixAlphaCap (i.val - 1) =
      (((((b.order ⟨i.val, i.lt_large⟩ -
        c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ)) : WithTop ℚ) := by
  rw [evenTarget_prefixAlphaCap c i hiTwo]
  exact (WithTop.coe_add _ _).symm

/-- Increasing the source order to the selected target order increases the
domination coefficient. -/
theorem evenTarget_coefficient_le_of_sourceNext_le
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2)) (j : Fin (n + 1))
    (hsourceNext : b.order ⟨i.val, i.lt_large⟩ ≤
      c.order j.castSucc) :
    (((((b.order ⟨i.val, i.lt_large⟩ -
        c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ)) : WithTop ℚ) ≤
      (((((c.order j.castSucc -
        c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ)) : WithTop ℚ) := by
  have horderDiff :
      b.order ⟨i.val, i.lt_large⟩ - c.order (evenTargetPreviousIndex i) ≤
        c.order j.castSucc - c.order (evenTargetPreviousIndex i) :=
    sub_le_sub_right hsourceNext _
  have horderDiffQ :
      ((b.order ⟨i.val, i.lt_large⟩ -
        c.order (evenTargetPreviousIndex i) : Int) : ℚ) ≤
        ((c.order j.castSucc -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) := by
    exact Int.cast_le.mpr horderDiff
  exact withTopRat_coe_add_le_coe_add_right horderDiffQ

/-- The easy domination branch in case 3. -/
theorem lemma79_even_targetDefect_of_sourceNext_le
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (j : Fin (n + 1))
    (hsourceNext : b.order ⟨i.val, i.lt_large⟩ ≤
      c.order j.castSucc)
    (hdomination :
      (((((c.order j.castSucc -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ)) :
        WithTop ℚ) ≤ c.alternatingPrefixDefect i.val) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      c.alternatingPrefixDefect i.val := by
  calc
    (b.representationAlphaValue c i : WithTop ℚ) ≤
        (((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) : WithTop ℚ) +
          c.prefixAlphaCap (i.val - 1) :=
      lemma79_representationAlphaValue_le_primaryRightCap b c i
    _ = (((((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ)) : WithTop ℚ) :=
      evenTarget_primaryRightCap_eq b c i hiTwo
    _ ≤ (((((c.order j.castSucc -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ)) : WithTop ℚ) :=
      evenTarget_coefficient_le_of_sourceNext_le b c i j hsourceNext
    _ ≤ c.alternatingPrefixDefect i.val := hdomination

/-- Case 3 after the first domination split: either condition 2.1(ii)
already holds against the target self-prefix, or there is an earlier even
pair whose first target order is strictly below the next intermediate
order and which retains the full domination estimate. -/
theorem lemma79_even_targetDefect_or_exists_lowWitness
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
        c.alternatingPrefixDefect i.val ∨
      ∃ j : Fin (n + 1), Even j.val ∧ j.val + 1 < i.val ∧
        c.order j.castSucc < b.order ⟨i.val, i.lt_large⟩ ∧
        (((((c.order j.castSucc -
            c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
            c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ)) :
          WithTop ℚ) ≤ c.alternatingPrefixDefect i.val := by
  rcases c.exists_even_domination_order_bound i.val i.pos
      i.lt_large.le hiEven with ⟨j, hjEven, hjlt, hdomination⟩
  have hdomination' :
      (((((c.order j.castSucc -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ)) :
        WithTop ℚ) ≤ c.alternatingPrefixDefect i.val := by
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
  · exact Or.inl (lemma79_even_targetDefect_of_sourceNext_le
      b c i hiTwo j hsourceNext hdomination')
  · exact Or.inr ⟨j, hjEven, hjlt, lt_of_not_ge hsourceNext,
      hdomination'⟩

end BONG.GoodBONG

end Bong
