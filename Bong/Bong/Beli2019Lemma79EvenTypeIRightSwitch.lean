/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma76TypeICentralComplete
import Bong.Bong.Beli2019Lemma79EvenAssembly
import Bong.Bong.Beli2019Lemma79EvenTypeILeftSwitch
import Bong.Bong.Beli2019Lemma79EvenTypeIRightSwitchCandidates
import Bong.Bong.Beli2019Lemma79EvenTypeITargetCentral

/-!
# Beli (2019), Lemma 7.9(ii), case 3: the right type-I switch

This closes the exceptional even coordinate `i = t' - 1`.  A large source
gap gives the scalar beta estimate directly.  In the small-gap branch, the
right-switch candidate comparisons give `B_i ≤ C_i + 2`; the alpha shift is
the central formula when the switches are distinct and the first-switch
formula when they coincide.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 5000000 in
-- The small-gap branch compares all three representation candidates.
/-- The scalar beta estimate at the canonical right type-I switch. -/
theorem beli2019Lemma79_typeI_rightSwitch_even_beta
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val) (hrightEq : i.val = C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by omega⟩ := by
  let previous : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  by_cases hlarge : 2 * (ramificationIndex K : Int) ≤
      b.orderGap previous
  · exact lemma79_even_beta_bound_of_large_sourceGap
      b c i hcross (by simpa only [previous] using hlarge)
  · have hsmall : b.orderGap previous <
        2 * (ramificationIndex K : Int) := lt_of_not_ge hlarge
    have hiLeft : C.leftSwitch ≤ i.val := by
      rw [hrightEq]
      exact C.left_le_anchor.trans C.anchor_le_right
    have halpha : b.alphaValue ⟨i.val - 1, by omega⟩ =
        a.alphaValue ⟨i.val - 1, by omega⟩ + 2 := by
      by_cases hswitch : C.leftSwitch < C.rightSwitch
      · have hleftAlpha : C.leftSwitch ≤ i.val - 1 := by
          rcases C.left_even with ⟨d, hd⟩
          rcases C.right_even with ⟨e, he⟩
          omega
        exact beli2019Lemma79_typeI_central_even_alphaShift
          a b D C hfirst hrightLast horderAB hdefectAB i hiEven
            hleftAlpha (by omega)
      · have hleftRight : C.leftSwitch ≤ C.rightSwitch :=
          C.left_le_anchor.trans C.anchor_le_right
        have hswitchEq : C.leftSwitch = C.rightSwitch := by omega
        have hleftEq : i.val = C.leftSwitch :=
          hrightEq.trans hswitchEq.symm
        have hraw :=
          beli2019Lemma79_typeI_leftSwitch_alphaShift_of_gap_lt_twoE
            a b D C hfirst hdefectAB (by omega) (by
              simpa only [previous, hleftEq] using hsmall)
        simpa only [hleftEq] using hraw
    have hhalf := lemma79_typeI_central_even_halfGap_le_add_two
      a b c D C hfirst i hiEven hiLeft hrightEq.le
    have hprimary := beli2019Lemma79_typeI_rightSwitch_even_primary
      a b c D C hfirst hrightLast hdefectAB i hi.2 hiEven hrightEq
    have hsecondary : ∀
        (hi' : 1 < i.val ∧ i.val + 1 < n + 2),
        b.representationSecondaryDefect c i hi' ≤
          a.representationSecondaryDefect c i hi' +
            ((2 : ℚ) : WithTop ℚ) := by
      intro hi'
      exact beli2019Lemma79_typeI_rightSwitch_even_secondary
        a b c D C hfirst hrightLast hdefectAB i hi' hiEven hrightEq
    exact lemma79_even_beta_bound_of_candidate_shifts
      a b c hdefectAC i halpha hhalf hprimary hsecondary

set_option maxHeartbeats 5000000 in
-- The positive-length and coincident-switch prefix proofs are distinct.
/-- The source self-prefix bound at the canonical right type-I switch. -/
theorem beli2019Lemma79_typeI_rightSwitch_even_sourceCapped
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val) (hrightEq : i.val = C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect b ((-1) ^ (i.val / 2)) 0 i.val := by
  have hbeta := beli2019Lemma79_typeI_rightSwitch_even_beta
    a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
      i hi hiEven hrightEq hcross
  have hiLeft : C.leftSwitch ≤ i.val := by
    rw [hrightEq]
    exact C.left_le_anchor.trans C.anchor_le_right
  by_cases hstrict : C.leftSwitch < i.val
  · exact beli2019Lemma76_typeI_central_sourceCapped_complete
      a b c D C hfirst i hi.2 hiEven hstrict hrightEq.le hcross hbeta
  · have hleftEq : i.val = C.leftSwitch := by omega
    have hbetaTop : (b.representationAlphaValue c i : WithTop ℚ) ≤
        (b.alphaValue ⟨C.leftSwitch - 1, by
          have hbound := C.left_le_anchor.trans_lt D.anchor_bound
          omega⟩ : WithTop ℚ) := by
      exact_mod_cast (by simpa only [hleftEq] using hbeta)
    have htwoE := representationAlphaValue_le_twoE_of_crossGap_le
      b c i hcross
    have hboundary := beli2019Lemma76_typeI_boundary_lower
      a b D C hfirst (by omega)
        (b.representationAlphaValue c i : WithTop ℚ) hbetaTop htwoE
    simpa only [hleftEq] using hboundary

/-- Lemma 7.9(ii), case 3, at the canonical right even type-I switch. -/
theorem beli2019Lemma79_ii_typeI_even_rightSwitch
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val) (hrightEq : i.val = C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hsource := beli2019Lemma79_typeI_rightSwitch_even_sourceCapped
    a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
      i hi hiEven hrightEq hcross
  have hiLeft : C.leftSwitch ≤ i.val := by
    rw [hrightEq]
    exact C.left_le_anchor.trans C.anchor_le_right
  have htarget := beli2019Lemma79_typeI_central_even_target
    a b c D C hfirst hnorm i (by omega) hiEven hiLeft hrightEq.le hcross
  exact lemma79_ii_of_even_selfCapped_bounds b c i hsource htarget

end BONG.GoodBONG

end Bong
