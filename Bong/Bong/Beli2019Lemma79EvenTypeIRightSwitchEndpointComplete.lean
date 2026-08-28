/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma76TypeICentralEndpointComplete
import Bong.Bong.Beli2019Lemma79EvenTypeIRightSwitchTerminal

/-!
# Beli (2019), Lemma 7.9(ii): endpoint-complete type-I right switch

At the final internal representation coordinate the primary mixed prefix is a
full left prefix, so its comparison follows directly from invariance under a
change of BONG.  The secondary candidate is absent at that coordinate.  These
observations remove the artificial successor-coordinate hypothesis from the
canonical right-switch argument.
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
-- The final-coordinate branch is exactly the full-left change identity.
/-- Primary-candidate comparison at a terminal canonical right switch,
including the final internal representation coordinate. -/
theorem beli2019Lemma79_typeI_rightSwitch_even_primary_terminal_endpointComplete
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch = D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiEven : Even i.val) (hrightEq : i.val = C.rightSwitch) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i +
        ((2 : ℚ) : WithTop ℚ) := by
  by_cases hiNext : i.val + 1 < n + 2
  · exact beli2019Lemma79_typeI_rightSwitch_even_primary_terminal
      a b c D C hfirst hrightLast hdefect i hiNext hiEven hrightEq
  · have hfull : i.val + 1 = n + 2 := by
      have hiBound : i.val < n + 2 := i.lt_large
      omega
    have hiLeft : C.leftSwitch ≤ i.val := by
      rw [hrightEq]
      exact C.left_le_anchor.trans C.anchor_le_right
    have hentry := lemma69_v_typeI_even_entry_gap_two
      a b D C hfirst i.val hiEven hiLeft hrightEq.le
    have horderShift : b.order ⟨i.val, i.lt_large⟩ =
        a.order ⟨i.val, i.lt_large⟩ + 2 := by
      rw [← a.orderSequence_entryOrZero_eq_order,
        ← b.orderSequence_entryOrZero_eq_order]
      exact hentry
    have hprefix : b.truncatedPrefixDefect c (-1) (i.val + 1)
        (i.val - 1) ≤
        a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
      simpa only [hfull] using
        (truncatedPrefixDefect_fullLeft_change
          a b c (-1) (i.val - 1)).le
    exact representationPrimaryDefect_le_add_two_of_order_eq_add_two
      a b c i horderShift hprefix

set_option maxHeartbeats 5000000 in
-- At the endpoint the secondary callback is vacuous by its own index bound.
/-- Scalar beta estimate at a terminal canonical right switch, with no
successor-coordinate hypothesis. -/
theorem beli2019Lemma79_typeI_rightSwitch_even_beta_terminal_endpointComplete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch = D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiEven : Even i.val) (hrightEq : i.val = C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by
          have hiBound : i.val < n + 2 := i.lt_large
          omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by
        have hiBound : i.val < n + 2 := i.lt_large
        omega⟩ := by
  let previous : Fin (n + 1) := ⟨i.val - 1, by
    have hiBound : i.val < n + 2 := i.lt_large
    omega⟩
  have hiTwo : 2 ≤ i.val := by
    rcases hiEven with ⟨d, hd⟩
    have hiPos := i.pos
    omega
  by_cases hlarge : 2 * (ramificationIndex K : Int) ≤
      b.orderGap previous
  · exact lemma79_even_beta_bound_of_large_sourceGap
      b c i hcross (by simpa only [previous] using hlarge)
  · have hsmall : b.orderGap previous <
        2 * (ramificationIndex K : Int) := lt_of_not_ge hlarge
    have hiLeft : C.leftSwitch ≤ i.val := by
      rw [hrightEq]
      exact C.left_le_anchor.trans C.anchor_le_right
    have halpha : b.alphaValue ⟨i.val - 1, by
          have hiBound : i.val < n + 2 := i.lt_large
          omega⟩ =
        a.alphaValue ⟨i.val - 1, by
          have hiBound : i.val < n + 2 := i.lt_large
          omega⟩ + 2 := by
      by_cases hswitch : C.leftSwitch < C.rightSwitch
      · have hleftAlpha : C.leftSwitch ≤ i.val - 1 := by
          rcases C.left_even with ⟨d, hd⟩
          rcases C.right_even with ⟨e, he⟩
          omega
        exact beli2019Lemma79_typeI_central_even_alphaShift_complete
          a b D C hfirst horderAB hdefectAB i hiEven hleftAlpha
            (by omega)
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
    have hprimary :=
      beli2019Lemma79_typeI_rightSwitch_even_primary_terminal_endpointComplete
        a b c D C hfirst hrightLast hdefectAB i hiEven hrightEq
    have hsecondary : ∀
        (hi' : 1 < i.val ∧ i.val + 1 < n + 2),
        b.representationSecondaryDefect c i hi' ≤
          a.representationSecondaryDefect c i hi' +
            ((2 : ℚ) : WithTop ℚ) := by
      intro hi'
      exact beli2019Lemma79_typeI_rightSwitch_even_secondary_terminal
        a b c D C hfirst hrightLast hdefectAB i hi' hiEven hrightEq
    exact lemma79_even_beta_bound_of_candidate_shifts
      a b c hdefectAC i halpha hhalf hprimary hsecondary

set_option maxHeartbeats 5000000 in
-- The source bound expands the endpoint-complete central concatenation.
/-- Source self-prefix estimate at a terminal canonical right switch,
including the final internal representation coordinate. -/
theorem beli2019Lemma79_typeI_rightSwitch_even_sourceCapped_terminal_endpointComplete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch = D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiEven : Even i.val) (hrightEq : i.val = C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by
          have hiBound : i.val < n + 2 := i.lt_large
          omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect b ((-1) ^ (i.val / 2)) 0 i.val := by
  have hbeta :=
    beli2019Lemma79_typeI_rightSwitch_even_beta_terminal_endpointComplete
      a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
        i hiEven hrightEq hcross
  have hiLeft : C.leftSwitch ≤ i.val := by
    rw [hrightEq]
    exact C.left_le_anchor.trans C.anchor_le_right
  by_cases hstrict : C.leftSwitch < i.val
  · exact beli2019Lemma76_typeI_central_sourceCapped_endpointComplete
      a b c D C hfirst i hiEven hstrict hrightEq.le hcross hbeta
  · have hleftEq : i.val = C.leftSwitch := by omega
    have hbetaTop : (b.representationAlphaValue c i : WithTop ℚ) ≤
        (b.alphaValue ⟨C.leftSwitch - 1, by
          have hbound := C.left_le_anchor.trans_lt D.anchor_bound
          omega⟩ : WithTop ℚ) := by
      exact_mod_cast (by simpa only [hleftEq] using hbeta)
    have htwoE := representationAlphaValue_le_twoE_of_crossGap_le
      b c i hcross
    have hboundary := beli2019Lemma76_typeI_boundary_lower
      a b D C hfirst (by
        rcases hiEven with ⟨d, hd⟩
        have hiPos := i.pos
        omega)
        (b.representationAlphaValue c i : WithTop ℚ) hbetaTop htwoE
    simpa only [hleftEq] using hboundary

/-- Lemma 7.9(ii) at a terminal canonical right switch, including the final
internal representation coordinate. -/
theorem beli2019Lemma79_ii_typeI_even_rightSwitch_terminal_endpointComplete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch = D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiEven : Even i.val) (hrightEq : i.val = C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by
          have hiBound : i.val < n + 2 := i.lt_large
          omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hiTwo : 2 ≤ i.val := by
    rcases hiEven with ⟨d, hd⟩
    have hiPos := i.pos
    omega
  have hsource :=
    beli2019Lemma79_typeI_rightSwitch_even_sourceCapped_terminal_endpointComplete
      a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
        i hiEven hrightEq hcross
  have hiLeft : C.leftSwitch ≤ i.val := by
    rw [hrightEq]
    exact C.left_le_anchor.trans C.anchor_le_right
  have htarget := beli2019Lemma79_typeI_central_even_target
    a b c D C hfirst hnorm i hiTwo hiEven hiLeft hrightEq.le hcross
  exact lemma79_ii_of_even_selfCapped_bounds b c i hsource htarget

/-- Lemma 7.9(ii) at the canonical right switch with no successor-coordinate
hypothesis, dispatching between proper and terminal type-I profiles. -/
theorem beli2019Lemma79_ii_typeI_even_rightSwitch_endpointComplete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiEven : Even i.val) (hrightEq : i.val = C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by
          have hiBound : i.val < n + 2 := i.lt_large
          omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hiTwo : 2 ≤ i.val := by
    rcases hiEven with ⟨d, hd⟩
    have hiPos := i.pos
    omega
  rcases C.right_le_last.lt_or_eq with hrightLast | hrightLast
  · have hiNext : i.val + 1 < n + 2 := by
      have hlastBound := D.profile.lastDifference.bound
      omega
    exact beli2019Lemma79_ii_typeI_even_rightSwitch
      a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
        hnorm i ⟨by omega, hiNext⟩ hiEven hrightEq hcross
  · exact
      beli2019Lemma79_ii_typeI_even_rightSwitch_terminal_endpointComplete
        a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
          hnorm i hiEven hrightEq hcross

end BONG.GoodBONG

end Bong
