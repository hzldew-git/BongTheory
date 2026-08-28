/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenTypeIBoundarySecondary
import Bong.Bong.Beli2019Lemma79EvenTypeIInterior

/-!
# Beli (2019), Lemma 7.9(ii), case 3: first type-I switch assembly

This is the remaining early type-I boundary `i + 2 = leftSwitch`.  The
large-gap branch is unchanged; the small-gap branch uses the special
secondary-candidate theorem at the switch.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 3000000 in
-- This is the scalar beta estimate at `leftSwitch - 2`.
/-- The representation alpha is bounded by the preceding target alpha at
the last even coordinate before the first type-I switch. -/
theorem beli2019Lemma79_typeI_even_leftBoundary_beta
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hboundary : i.val + 2 = C.leftSwitch) :
    b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by omega⟩ := by
  have hiTwo : 2 ≤ i.val := by omega
  have hbefore : i.val < C.leftSwitch := by omega
  have horders := lemma79_typeI_even_left_shiftedTwoStep
    a b D C hfirst i hiTwo hiEven hbefore
  have hsourceLe := b.orderGap_previous_le_twoE_of_twoStep
    i hiTwo horders.2.1
  have hcross :=
    crossGap_le_twoE_of_representationOrder_of_sourceGap_le_twoE
      b c horderBC i hsourceLe
  by_cases hlarge : 2 * (ramificationIndex K : Int) ≤
      b.orderGap ⟨i.val - 1, by omega⟩
  · exact lemma79_even_beta_bound_of_large_sourceGap
      b c i hcross hlarge
  · have hsmall : b.orderGap ⟨i.val - 1, by omega⟩ <
        2 * (ramificationIndex K : Int) := lt_of_not_ge hlarge
    have halpha := beli2019Lemma79_typeI_even_left_alphaShift
      a b D C hfirst hdefectAB i hiTwo hiEven hbefore hsmall
    have hhalf := lemma79_typeI_even_left_halfGap_le_add_two
      a b c D C i hiEven hbefore
    have hprimary := lemma79_typeI_even_left_primary_le_add_two
      a b c D C hfirst i hi.2 hiEven hbefore
    have hsecondary : ∀
        (hi' : 1 < i.val ∧ i.val + 1 < n + 2),
        b.representationSecondaryDefect c i hi' ≤
          a.representationSecondaryDefect c i hi' +
            ((2 : ℚ) : WithTop ℚ) := by
      intro hi'
      exact beli2019Lemma79_typeI_even_leftBoundary_secondary
        a b c D C hfirst hdefectAB i hi' hiEven hboundary
    exact lemma79_even_beta_bound_of_candidate_shifts
      a b c hdefectAC i halpha hhalf hprimary hsecondary

/-- Lemma 7.9(ii), case 3, at the final even coordinate before the first
canonical type-I switch. -/
theorem beli2019Lemma79_ii_typeI_even_leftBoundary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hboundary : i.val + 2 = C.leftSwitch) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hbeta := beli2019Lemma79_typeI_even_leftBoundary_beta
    a b c D C hfirst hdefectAB hdefectAC horderBC
      i hi hiEven hboundary
  exact beli2019Lemma79_ii_typeI_even_left_of_beta
    a b c D C hnorm i (by omega) hi.2 hiEven (by omega) hbeta

end BONG.GoodBONG

end Bong
