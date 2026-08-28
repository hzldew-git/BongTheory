/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailLastGap
import Bong.Bong.Beli2019Lemma79RightTailStrictData

/-!
# Beli (2019), Lemma 7.9(ii), case 8: the gap-one branch

Assume that the target order at the first changed coordinate is one above
the source order, while the following orders agree.  In the strict beta
branch, the target gap cannot be even: otherwise the source gap is the next
odd integer and Lemma 2.7(iii) contradicts the strict source-alpha bound.
Consequently the first beta equals its order gap, and every later beta is
the explicit order difference displayed in the paper.
-/

namespace Bong

open Dyadic

universe u v

/-- An odd rational integer lying above an even integer lies at least one
integer step above it. -/
theorem intCast_add_one_le_of_even_of_oddRationalInteger
    (x : Int) (y : Rat) (hx : Even x)
    (hy : IsOddRationalInteger y) (hxy : (x : Rat) ≤ y) :
    ((x + 1 : Int) : Rat) ≤ y := by
  rcases hy with ⟨z, hzOdd, rfl⟩
  have hxz : x ≤ z := by
    exact_mod_cast hxy
  have hxzNext : x + 1 ≤ z := by
    rcases hx with ⟨p, hp⟩
    rcases hzOdd with ⟨q, hq⟩
    omega
  exact_mod_cast hxzNext

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- In the gap-one branch of case 8, the first target order gap is odd. -/
theorem CaseEightStrictBetaTailConsequences.firstGap_odd_of_target_eq_source_add_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {first last : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b first last)
    (hfirstLast : first ≤ last)
    (hcurrent : b.order first.castSucc = a.order first.castSucc + 1)
    (hnext : b.order first.succ = a.order first.succ)
    (hstrict : b.alphaValue first < a.alphaValue first) :
    Odd (b.orderGap first) := by
  have htargetGapLt :
      b.orderGap first < 2 * (ramificationIndex K : Int) :=
    (b.beli2009Corollary28_ii first).1.mp
      (H.alpha_lt_twoE first le_rfl hfirstLast)
  have hsourceGap : a.orderGap first = b.orderGap first + 1 := by
    unfold orderGap
    omega
  rcases Int.even_or_odd (b.orderGap first) with htargetEven | htargetOdd
  · have hsourceGapLe :
        a.orderGap first ≤ 2 * (ramificationIndex K : Int) := by
      rw [hsourceGap]
      omega
    have hsourceOdd : Odd (a.orderGap first) := by
      rcases htargetEven with ⟨d, hd⟩
      refine ⟨d, ?_⟩
      omega
    have hsourceAlpha :
        a.alphaValue first = (a.orderGap first : Rat) :=
      (a.beli2009Lemma27_iii first hsourceGapLe).2.mpr
        (Or.inr hsourceOdd)
    have htargetGapLe :
        b.orderGap first ≤ 2 * (ramificationIndex K : Int) :=
      htargetGapLt.le
    have htargetLower :
        (b.orderGap first : Rat) ≤ b.alphaValue first :=
      (b.beli2009Lemma27_iii first htargetGapLe).1
    have htargetNextLower :
        ((b.orderGap first + 1 : Int) : Rat) ≤ b.alphaValue first :=
      intCast_add_one_le_of_even_of_oddRationalInteger
        (b.orderGap first) (b.alphaValue first) htargetEven
        (H.alpha_odd first le_rfl hfirstLast) htargetLower
    rw [hsourceAlpha, hsourceGap] at hstrict
    exfalso
    exact (not_lt_of_ge htargetNextLower) hstrict
  · exact htargetOdd

/-- The odd first gap makes the first beta equal that gap. -/
theorem CaseEightStrictBetaTailConsequences.firstAlpha_eq_gap_of_target_eq_source_add_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {first last : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b first last)
    (hfirstLast : first ≤ last)
    (hcurrent : b.order first.castSucc = a.order first.castSucc + 1)
    (hnext : b.order first.succ = a.order first.succ)
    (hstrict : b.alphaValue first < a.alphaValue first) :
    b.alphaValue first = (b.orderGap first : Rat) := by
  have hodd := H.firstGap_odd_of_target_eq_source_add_one
    hfirstLast hcurrent hnext hstrict
  have hgapLe : b.orderGap first ≤
      2 * (ramificationIndex K : Int) :=
    (b.beli2009Corollary28_ii first).1.mp
      (H.alpha_lt_twoE first le_rfl hfirstLast) |>.le
  exact (b.beli2009Lemma27_iii first hgapLe).2.mpr (Or.inr hodd)

/-- Every beta on the gap-one tail is the difference between its right
target order and the target order at the changed coordinate. -/
theorem CaseEightStrictBetaTailConsequences.alphaValue_eq_order_sub_first
    {b : GoodBONG q M (n + 2)} {first last : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b first last)
    (hfirstAlpha : b.alphaValue first = (b.orderGap first : Rat))
    (j : Fin (n + 1)) (hfirst : first ≤ j) (hlast : j ≤ last) :
    b.alphaValue j =
      ((b.order j.succ - b.order first.castSucc : Int) : Rat) := by
  have hvalue := H.value_eq j hfirst hlast
  unfold orderGap at hfirstAlpha
  push_cast at hvalue hfirstAlpha ⊢
  linarith

namespace CaseEightStrictBetaTailConsequences

/-- Combined form of the explicit beta formula used after the gap-one
split in case 8. -/
theorem alphaValue_eq_order_sub_first_of_target_eq_source_add_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {first last : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b first last)
    (hfirstLast : first ≤ last)
    (hcurrent : b.order first.castSucc = a.order first.castSucc + 1)
    (hnext : b.order first.succ = a.order first.succ)
    (hstrict : b.alphaValue first < a.alphaValue first)
    (j : Fin (n + 1)) (hfirst : first ≤ j) (hlast : j ≤ last) :
    b.alphaValue j =
      ((b.order j.succ - b.order first.castSucc : Int) : Rat) := by
  apply H.alphaValue_eq_order_sub_first
    (H.firstAlpha_eq_gap_of_target_eq_source_add_one
      hfirstLast hcurrent hnext hstrict)
    j hfirst hlast

end CaseEightStrictBetaTailConsequences

end BONG.GoodBONG

end Bong
