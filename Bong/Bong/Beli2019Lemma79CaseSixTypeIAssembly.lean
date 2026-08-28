/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixTypeICandidates
import Bong.Bong.Beli2019Lemma79OrderTypeIRight
import Bong.Bong.Beli2019RepresentationTargetHalfGap
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityCurrent
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityJumpBound
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityJumpWitness

/-!
# Beli (2019), Lemma 7.9(ii), case 6: the type-I right-even interval

This file closes the even type-I interval strictly after the canonical right
switch and before the last unequal coordinate.  The first comparison parity
uses the one-unit candidate shift.  In the second parity, equal current parity
uses the primary bound, while opposite current parity produces an odd adjacent
pair in the third BONG.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The positive-third-alpha subcase of the first comparison parity. -/
theorem beli2019Lemma79_typeI_caseSix_firstParity_of_gamma_ge_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hbeforeLast : i.val < D.profile.last) (hiEven : Even i.val)
    (hgamma : (1 : ℚ) ≤ c.alphaValue ⟨i.val - 1, by
      have hiBound := i.lt_large
      omega⟩)
    (hbcEven : Even
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (hacOdd : Odd
      (ordUnit K (a.prefixProduct i.val * c.prefixProduct i.val))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hshift := beli2019Lemma79_typeI_caseSix_alpha_le_add_one
    a b c D C hfirst hrightLast hdefectAB i hright hbeforeLast hiEven
  have hrightEven := C.right_even
  have hpreviousRight : C.rightSwitch < i.val - 1 := by
    rcases hiEven with ⟨d, hd⟩
    rcases hrightEven with ⟨e, he⟩
    omega
  have hpreviousOdd : Odd (i.val - 1) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hbeta := beli2019Remark613_typeI_targetRightAlpha_eq_one
    a b D C hfirst hrightLast hdefectAB (i.val - 1)
      hpreviousRight (by omega) hpreviousOdd
  exact lemma79_caseSix_of_alphaShift_even_and_sourceOdd
    a b c hdefectAC i hshift hbeta hgamma hbcEven hacOdd

/-- The zero-third-alpha subcase of the first comparison parity. -/
theorem beli2019Lemma79_typeI_caseSix_firstParity_of_gamma_eq_zero
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hlast : D.profile.last = n + 1)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hbeforeLast : i.val < D.profile.last) (hiEven : Even i.val)
    (hgamma : c.alphaValue ⟨i.val - 1, by omega⟩ = 0) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hlastEven := lemma79_typeI_last_even
    a b D C hfirst hrightLast
  have hiTwoLast : i.val + 2 ≤ D.profile.last := by
    rcases hiEven with ⟨d, hd⟩
    rcases hlastEven with ⟨e, he⟩
    omega
  have hiTwo : i.val + 2 < n + 2 := by
    rw [hlast] at hiTwoLast
    omega
  have hiNext : i.val + 1 < n + 2 := by omega
  have hleft : C.leftSwitch ≤ i.val := by
    have hleftRight := C.left_le_anchor.trans C.anchor_le_right
    omega
  have hcompare := beli2019Lemma79_i_typeI_rightEven
    a b c D C hfirst hrightLast hdefectAB hdefectAC hinitial hnorm
      i.val i.lt_large hiNext hiTwo hiEven hleft hright.le hbeforeLast
  exact lemma79_caseSix_of_gamma_eq_zero_and_compare
    b c i hiNext hcompare hgamma

/-- The complete first comparison parity on the type-I case-6 interval. -/
theorem beli2019Lemma79_typeI_caseSix_firstParity
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hlast : D.profile.last = n + 1)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hbeforeLast : i.val < D.profile.last) (hiEven : Even i.val)
    (hbcEven : Even
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (hacOdd : Odd
      (ordUnit K (a.prefixProduct i.val * c.prefixProduct i.val))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let previous : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  by_cases hgamma : (1 : ℚ) ≤ c.alphaValue previous
  · exact beli2019Lemma79_typeI_caseSix_firstParity_of_gamma_ge_one
      a b c D C hfirst hrightLast hdefectAB hdefectAC i hright
        hbeforeLast hiEven (by simpa only [previous] using hgamma)
          hbcEven hacOdd
  · have hgammaZero : c.alphaValue previous = 0 := by
      by_contra hne
      exact hgamma (c.one_le_alphaValue_of_ne_zero previous hne)
    exact beli2019Lemma79_typeI_caseSix_firstParity_of_gamma_eq_zero
      a b c D C hfirst hrightLast hlast hdefectAB hdefectAC hinitial
        hnorm i hright hbeforeLast hiEven
          (by simpa only [previous] using hgammaZero)

/-- The same-current-parity subcase of the second comparison parity. -/
theorem beli2019Lemma79_typeI_caseSix_secondParity_sameCurrentParity
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hthroughLast : i.val ≤ D.profile.last) (hiEven : Even i.val)
    (hcomparison : Odd
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hcurrent := lemma79_typeI_caseSix_current_eq_reference_add_one
    a b D C hfirst i hright hthroughLast hiEven
  have hreference := beli2019Lemma79_typeI_caseSix_reference_le_thirdFirst
    a b c D C hfirst hnorm
  have hupper : b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero 0 + 1 := by omega
  have htarget := beli2019Lemma79_typeI_caseSix_targetPrefix_even
    a b D C hfirst i hright hthroughLast hiEven
  exact lemma79_caseSix_secondParity_of_prefix_odd_target_even_orders_modEq
    b c i hcomparison htarget hupper horders

/-- The opposite-current-parity subcase of the second comparison parity. -/
theorem beli2019Lemma79_typeI_caseSix_secondParity_oppositeCurrentParity
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hthroughLast : i.val ≤ D.profile.last) (hiEven : Even i.val)
    (hcomparison : Odd
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1) + 1)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let T := a.orderSequence.entryOrZero D.anchor + 1
  have hcurrentEntry := lemma79_typeI_caseSix_current_eq_reference_add_one
    a b D C hfirst i hright hthroughLast hiEven
  have hcurrent : b.order ⟨i.val, i.lt_large⟩ = T + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order]
    simpa only [T] using hcurrentEntry
  have htarget := beli2019Lemma79_typeI_caseSix_targetPrefix_even
    a b D C hfirst i hright hthroughLast hiEven
  have hthirdPrefix :=
    caseSix_thirdPrefix_odd_of_comparison_odd_and_target_even
      b c i hcomparison htarget
  have hfirstLower := beli2019Lemma79_typeI_caseSix_reference_le_thirdFirst
    a b c D C hfirst hnorm
  have hone : Int.ModEq 2 (1 : Int) 1 := Int.ModEq.refl 1
  have hshifted := horders.sub hone
  have hfinalMod : Int.ModEq 2
      (c.orderSequence.entryOrZero (i.val - 1)) T := by
    simpa only [hcurrentEntry, T, add_sub_cancel_right] using hshifted.symm
  have hfinalBound : i.val - 1 < n + 2 :=
    (Nat.sub_le i.val 1).trans_lt i.lt_large
  rcases c.exists_odd_entryPair_above_reference_of_even_prefix_odd
      i.val (i.val - 1) T i.pos i.lt_large.le hiEven hthirdPrefix
      hfinalBound le_rfl (by simpa only [T] using hfirstLower)
      hfinalMod with ⟨k, hkFinal, hkOdd, hkAbove⟩
  have hiLarge := i.lt_large
  have hkBound : k < n + 1 := by omega
  let j : Fin (n + 1) := ⟨k, hkBound⟩
  have hsumOdd : Odd (c.order j.castSucc + c.order j.succ) := by
    rw [← c.orderSequence_entryOrZero_eq_order j.castSucc,
      ← c.orderSequence_entryOrZero_eq_order j.succ]
    simpa only [j, Fin.val_castSucc, Fin.val_succ] using hkOdd
  have hreference : T < c.order j.castSucc := by
    rw [← c.orderSequence_entryOrZero_eq_order j.castSucc]
    simpa only [j, Fin.val_castSucc] using hkAbove
  have hjlt : j.val + 1 < i.val := by
    change k + 1 < i.val
    omega
  exact lemma79_caseSix_secondParity_of_odd_pair_above_reference
    b c i T j hcurrent hjlt hsumOdd hreference

/-- The complete second comparison parity on the type-I case-6 interval. -/
theorem beli2019Lemma79_typeI_caseSix_secondParity
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hthroughLast : i.val ≤ D.profile.last) (hiEven : Even i.val)
    (hcomparison : Odd
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  rcases modEq_two_or_add_one
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1)) with hsame | hopposite
  · exact beli2019Lemma79_typeI_caseSix_secondParity_sameCurrentParity
      a b c D C hfirst hnorm i hright hthroughLast hiEven
        hcomparison hsame
  · exact beli2019Lemma79_typeI_caseSix_secondParity_oppositeCurrentParity
      a b c D C hfirst hnorm i hright hthroughLast hiEven
        hcomparison hopposite

set_option maxHeartbeats 6000000 in
-- Both comparison-prefix parity branches are closed above.
/-- Lemma 7.9(ii), case 6, on the even type-I right interval. -/
theorem beli2019Lemma79_ii_typeI_caseSix
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hlast : D.profile.last = n + 1)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hbeforeLast : i.val < D.profile.last) (hiEven : Even i.val) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hprefix := beli2019Lemma79_typeI_caseSix_prefix_opposite
    a b D C hfirst i hright hbeforeLast.le hiEven
  rcases caseSix_comparisonPrefix_parity_dichotomy a b c i hprefix with
      hfirstParity | hsecondParity
  · exact beli2019Lemma79_typeI_caseSix_firstParity
      a b c D C hfirst hrightLast hlast hdefectAB hdefectAC hinitial
        hnorm i hright hbeforeLast hiEven hfirstParity.1 hfirstParity.2
  · exact beli2019Lemma79_typeI_caseSix_secondParity
      a b c D C hfirst hnorm i hright hbeforeLast.le hiEven hsecondParity.1

end BONG.GoodBONG

end Bong
