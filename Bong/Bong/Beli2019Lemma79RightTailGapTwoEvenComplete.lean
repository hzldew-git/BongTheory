/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoEvenEquality
import Bong.Bong.Beli2019Lemma79RightTailGapTwoEvenIntegral

/-!
# Beli (2019), Lemma 7.9(ii), case 8: complete even gap-two beta bound

Capped domination either proves the beta bound immediately or supplies a
low witness.  For that witness a strict coefficient is handled by integral
rounding or the nonintegral contradiction, while equality is handled by
Lemma 7.3(ii) and prefix parity.  This completes lines 5902--5946.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 4000000 in
/-- The complete beta estimate at an even coordinate after a type-I
gap-two endpoint. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_even_beta_bound
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last + 1 <= i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.profile.last hlast) (caseEightLastAlphaIndex i))
    (hiEven : Even i.val) (hiTwo : 2 <= i.val)
    (hself : c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val =
      ((((b.order (Fin.mk D.profile.last hlast).castSucc -
          b.order (Fin.mk D.profile.last hlast).succ : Int) : Rat) +
        b.alphaValue (Fin.mk D.profile.last hlast) : Rat) : WithTop Rat))
    (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val)) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) := by
  let first : Fin (n + 1) := Fin.mk D.profile.last hlast
  have hfirstLast : first <= caseEightLastAlphaIndex i := by
    change D.profile.last <= i.val - 1
    omega
  rcases caseEight_gapTwo_even_beta_bound_or_exists_lowWitness
      b c i first hfirstLast H hiEven hiTwo (by
        simpa only [first] using hself) with
    hdone | ⟨j, hjEven, hjBefore, hlow, hjPair, hjCoefficient⟩
  · exact hdone
  · rcases beli2019Lemma79_typeI_caseEight_gapTwo_lowWitness_orders
        a b c D hfirst hgapTwo hlast hnorm j hjEven (by
          simpa only [first] using hlow) with
      ⟨hzero, hjOrder, htarget, _⟩
    have hsource : b.order first.castSucc = c.order j.castSucc + 1 := by
      simp only [first] at htarget ⊢
      omega
    have hfloor : b.order first.castSucc =
        c.order (0 : Fin (n + 2)) + 1 := by
      simp only [first] at hzero htarget ⊢
      omega
    by_cases hstrict :
        ((((c.order j.castSucc -
            c.order (evenTargetPreviousIndex i) : Int) : Rat) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) : Rat) :
            WithTop Rat) <
        ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
          b.alphaValue first : Rat) : WithTop Rat)
    · by_cases hintegral : IsRationalInteger
          (c.alphaValue (evenTargetPreviousAlphaIndex i))
      · exact caseEight_gapTwo_even_beta_bound_of_strict_lowWitness_integral
          b c i first hfirstLast H hiTwo j hsource hstrict hintegral
      · by_contra hnotBound
        have hfailureTop :
            (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) <
              (b.representationAlphaValue c i : WithTop Rat) :=
          lt_of_not_ge hnotBound
        have hfailure : b.alphaValue (caseEightLastAlphaIndex i) <
            b.representationAlphaValue c i := by
          exact_mod_cast hfailureTop
        have hbound :=
          beli2019Lemma79_typeI_caseEight_gapTwo_even_beta_bound_of_nonintegral_failure
            a b c D hfirst hgapTwo hlast i hafter H hiEven hiTwo (by
              simpa only [first] using hfloor) hfailure hintegral
        exact (not_lt_of_ge hbound) hfailureTop
    · have heq :
          ((((c.order j.castSucc -
              c.order (evenTargetPreviousIndex i) : Int) : Rat) +
            c.alphaValue (evenTargetPreviousAlphaIndex i) : Rat) :
              WithTop Rat) =
          ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
            b.alphaValue first : Rat) : WithTop Rat) :=
        le_antisymm hjCoefficient (le_of_not_gt hstrict)
      exact
        beli2019Lemma79_typeI_caseEight_gapTwo_even_beta_bound_of_domination_equality
          a b c D hfirst hgapTwo hlast hnorm i hafter H hiEven hiTwo
            hself hprefix j hjEven hjBefore hlow hjPair (by
              simpa only [first] using heq)

end BONG.GoodBONG

end Bong
