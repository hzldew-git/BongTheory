/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoEvenPrimaryOdd
import Bong.Bong.Beli2019Lemma79RightTailGapOnePrefix

/-!
# Beli (2019), Lemma 7.9(ii), case 8: exceptional even prefix parity

When failure of the desired beta bound forces the preceding comparison
order back to the norm floor, the target prefix of length `i + 1` and the
comparison prefix of length `i - 1` have the two complementary congruences
displayed in the paper.  Their signed product consequently has odd order.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The order equalities forced by failure in the nonintegral even branch
give odd valuation of the signed primary product. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_even_primaryProduct_odd
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last + 1 <= i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.profile.last hlast) (caseEightLastAlphaIndex i))
    (hiEven : Even i.val) (hiTwo : 2 <= i.val)
    (hfloor : b.order (Fin.mk D.profile.last hlast).castSucc =
      c.order (0 : Fin (n + 2)) + 1)
    (hboundary : b.alphaValue (Fin.mk D.profile.last hlast) =
      (b.orderGap (Fin.mk D.profile.last hlast) : Rat))
    (hprevious : c.order (evenTargetPreviousAlphaIndex i).castSucc =
      c.order (0 : Fin (n + 2))) :
    Odd (ordUnit K
      ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
        c.prefixProduct (i.val - 1))) := by
  rcases beli2019Lemma79_typeI_caseEight_gapTwo_initialData
    a b D hfirst hgapTwo with ⟨I⟩
  let first : Fin (n + 1) := Fin.mk D.profile.last hlast
  let reference : Int := c.order (0 : Fin (n + 2))
  have hfirstLast : first <= caseEightLastAlphaIndex i := by
    change D.profile.last <= i.val - 1
    omega
  have htargetOrder : b.order first.castSucc =
      a.orderSequence.entryOrZero D.anchor + 2 := by
    rw [<- b.orderSequence_entryOrZero_eq_order first.castSucc]
    change b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.anchor + 2
    exact I.target_last
  have hreference : reference =
      a.orderSequence.entryOrZero D.anchor + 1 := by
    simp only [reference] at ⊢
    simp only [first] at hfloor htargetOrder
    omega
  have hbase : b.order first.castSucc = reference + 1 := by
    simpa only [first, reference] using hfloor
  have hformula (j : Fin (n + 1)) (hjFirst : first <= j)
      (hjLast : j <= caseEightLastAlphaIndex i) :
      b.alphaValue j =
        ((b.order j.succ - b.order first.castSucc : Int) : Rat) := by
    have hvalue := H.value_eq j hjFirst hjLast
    have hgap : b.orderGap first =
        b.order first.succ - b.order first.castSucc := by
      rfl
    rw [hboundary, hgap] at hvalue
    push_cast at hvalue ⊢
    linarith
  have hprefix : Int.ModEq 2
      (b.orderSequence.prefixSum (first.val + 1))
      (((first.val + 1 : Nat) : Int) * reference + 1) := by
    simpa only [first, hreference] using I.target_prefix_last
  have hbRaw := H.targetPrefix_modEq_of_gapOne reference hbase hformula
    hprefix (i.val + 1) (by
      simp only [first]
      omega) (by
        simp only [caseEightLastAlphaIndex_val]
        omega)
  have hiEvenForProduct := hiEven
  have htargetReference : Int.ModEq 2
      (((i.val + 1 : Nat) : Int) * reference + 1)
      (((i.val + 1 : Nat) : Int) * (reference + 1)) := by
    rcases hiEven with ⟨d, hd⟩
    rw [Int.modEq_iff_dvd]
    refine ⟨(d : Int), ?_⟩
    have hdInt : (i.val : Int) = (d : Int) + (d : Int) := by
      exact_mod_cast hd
    push_cast
    rw [hdInt]
    ring
  have hb : Int.ModEq 2
      (b.orderSequence.prefixSum (i.val + 1))
      (((i.val + 1 : Nat) : Int) * (reference + 1)) :=
    hbRaw.trans htargetReference
  let p : Fin (n + 1) := evenTargetPreviousAlphaIndex i
  have hpBound : p.val < n + 2 := p.castSucc.isLt
  have hfirstComparison : reference <=
      c.orderSequence.entryOrZero 0 := by
    have hrefEntry : reference = c.orderSequence.entryOrZero 0 := by
      calc
        reference = c.order (0 : Fin (n + 2)) := by rfl
        _ = c.orderSequence.entryOrZero 0 := by
          symm
          simpa using c.orderSequence_entryOrZero_eq_order
            (0 : Fin (n + 2))
    exact hrefEntry.le
  have hcurrentComparison : c.orderSequence.entryOrZero p.val <=
      reference := by
    calc
      c.orderSequence.entryOrZero p.val = c.order p.castSucc := by
        simpa using c.orderSequence_entryOrZero_eq_order p.castSucc
      _ <= reference := by
        simpa only [p, reference] using hprevious.le
  have hcRaw := c.prefixSum_modEq_mul_of_current_le_reference_le_first
    reference p.val hpBound hfirstComparison hcurrentComparison
  have hpLength : p.val + 1 = i.val - 1 := by
    simp only [p, evenTargetPreviousAlphaIndex]
    omega
  have hc : Int.ModEq 2
      (c.orderSequence.prefixSum (i.val - 1))
      (((i.val - 1 : Nat) : Int) * reference) := by
    simpa only [hpLength] using hcRaw
  have hiPrefixBound : i.val + 1 <= n + 2 := by
    have hi := i.lt_large
    omega
  exact lemma79_typeI_even_primaryProduct_odd_of_modEq
    b c i.val hiEvenForProduct hiTwo hiPrefixBound reference hb hc

end BONG.GoodBONG

end Bong
