/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoEvenEqualityAlpha

/-!
# Beli (2019), Lemma 7.9(ii), case 8: complete even equality branch

This assembles the low-witness order identities, Lemma 7.3(ii) parity,
the exclusion of a zero preceding alpha, and the final numerical primary
bound.  It closes the equality alternative in lines 5931--5946.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The equality alternative selected by capped domination satisfies the
desired even beta bound. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_even_beta_bound_of_domination_equality
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
      (c.orderSequence.prefixSum i.val))
    (j : Fin (n + 1)) (hjEven : Even j.val)
    (hjBefore : j.val + 1 < i.val)
    (hlow : c.order j.castSucc <
      b.order (Fin.mk D.profile.last hlast).castSucc)
    (hjPair : c.truncatedPrefixDefect c (-1) j.val (j.val + 2) <=
      ((((b.order (Fin.mk D.profile.last hlast).castSucc -
          b.order (Fin.mk D.profile.last hlast).succ : Int) : Rat) +
        b.alphaValue (Fin.mk D.profile.last hlast) : Rat) : WithTop Rat))
    (hcoefficient :
      ((((c.order j.castSucc -
          c.order (evenTargetPreviousIndex i) : Int) : Rat) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) : Rat) :
          WithTop Rat) =
      ((((b.order (Fin.mk D.profile.last hlast).castSucc -
          b.order (Fin.mk D.profile.last hlast).succ : Int) : Rat) +
        b.alphaValue (Fin.mk D.profile.last hlast) : Rat) : WithTop Rat)) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) := by
  let first : Fin (n + 1) := Fin.mk D.profile.last hlast
  have hfirstLast : first <= caseEightLastAlphaIndex i := by
    change D.profile.last <= i.val - 1
    omega
  rcases beli2019Lemma79_typeI_caseEight_gapTwo_lowWitness_orders
      a b c D hfirst hgapTwo hlast hnorm j hjEven (by
        simpa only [first] using hlow) with
    ⟨_, hjOrder, htarget, _⟩
  have hsource : b.order first.castSucc = c.order j.castSucc + 1 := by
    simp only [first] at htarget ⊢
    omega
  have hodd :=
    beli2019Lemma79_typeI_caseEight_gapTwo_even_equality_primaryProduct_odd
      a b c D hfirst hgapTwo hlast hnorm i hafter H hiEven hiTwo hself
        j hjEven hjBefore hlow hjPair hcoefficient
  have halphaNe := caseEight_gapTwo_even_equality_previousAlpha_ne_zero
    b c i first hfirstLast H j hsource (by
      simpa only [first] using hcoefficient) hprefix hodd
  exact
    caseEight_gapTwo_even_beta_bound_of_equality_primaryProduct_odd_of_alpha_ne_zero
      b c i first hfirstLast H j hsource (by
        simpa only [first] using hcoefficient) hodd halphaNe

end BONG.GoodBONG

end Bong
