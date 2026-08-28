/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityTypeIIAssembly
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIIOverlap
import Bong.Bong.Beli2019Lemma72TypeIIIOverlap

/-!
# Beli (2019), Lemma 7.9(ii), overlapping case 6: second parity

The central-gap-one type-III profile has the type-II current value and prefix
congruences.  Its case-6 indices are odd, so only the odd-index jump-witness
branch remains after the common same-current-parity argument.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The target current value is one above the common overlap reference. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_targetCurrent_eq_reference_add_one
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    b.orderSequence.entryOrZero i.val =
      b.orderSequence.entryOrZero D.outer.transition.lastZero + 1 := by
  have hcurrentBoundary := D.outer.target_rightEven_eq_boundary
    i.val hright hthroughLast heven
  have hlastBoundary := D.outer.target_rightEven_eq_boundary
    D.outer.last D.outer.right_le_last le_rfl D.outer.right_even_distance
  calc
    b.orderSequence.entryOrZero i.val =
        b.orderSequence.entryOrZero (D.outer.transition.firstTwo - 1) :=
      hcurrentBoundary
    _ = b.orderSequence.entryOrZero D.outer.last := hlastBoundary.symm
    _ = b.orderSequence.entryOrZero D.outer.transition.lastZero + 1 :=
      beli2019Lemma79_typeIII_overlap_lastTarget_eq_left_add_one
        a b D hoverlap

/-- The overlap reference bounds every current value in the case-6 parity
class by one above the third first order. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_targetCurrent_le_thirdFirst_add_one
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero 0 + 1 := by
  have hreference :=
    beli2019Lemma79_typeIII_overlap_reference_le_thirdFirst
      a b c D hfirst hnorm
  have hcurrent :=
    beli2019Lemma79_typeIII_overlap_caseSix_targetCurrent_eq_reference_add_one
      a b D hoverlap i hright hthroughLast heven
  omega

/-- The same-current-parity subcase of overlapping type-III case 6. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_secondParity_sameCurrentParity
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hcomparison : Odd
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hupper :=
    beli2019Lemma79_typeIII_overlap_caseSix_targetCurrent_le_thirdFirst_add_one
      a b c D hfirst hoverlap hnorm i hright hthroughLast heven
  by_cases hcurrent : b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero (i.val - 1)
  · exact lemma79_caseSix_secondParity_of_prefix_odd_orders_modEq_current_le
      b c i hcomparison horders hcurrent
  · have hstrict : c.orderSequence.entryOrZero (i.val - 1) <
        b.orderSequence.entryOrZero i.val := lt_of_not_ge hcurrent
    have hiEven := caseSix_index_even_of_current_lt_and_orders_modEq
      b c i hupper horders hstrict
    have hiOdd := beli2019Lemma79_typeIII_caseSix_index_odd
      a b D hfirst i hright heven
    rcases hiEven with ⟨e, he⟩
    rcases hiOdd with ⟨o, ho⟩
    omega

/-- Opposite current parity identifies the third preceding order modulo two
with the overlap reference. -/
theorem caseSix_thirdPrevious_modEq_typeIII_overlap_reference
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1) + 1)) :
    Int.ModEq 2 (c.orderSequence.entryOrZero (i.val - 1))
      (b.orderSequence.entryOrZero D.outer.transition.lastZero) := by
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  have hcurrent :=
    beli2019Lemma79_typeIII_overlap_caseSix_targetCurrent_eq_reference_add_one
      a b D hoverlap i hright hthroughLast heven
  have hone : Int.ModEq 2 (1 : Int) 1 := Int.ModEq.refl 1
  have hshifted := horders.sub hone
  simpa only [hcurrent, T, add_sub_cancel_right] using hshifted.symm

/-- At an odd overlap case-6 index, the target prefix of length `i + 1`
has odd order. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_targetPrefix_succ_odd
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    Odd (b.orderSequence.prefixSum (i.val + 1)) := by
  let base := D.outer.transition.firstTwo - 1
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  let P := a.beli2019Lemma72_ii_typeIII_overlap b D hfirst hoverlap
  have hiOdd := beli2019Lemma79_typeIII_caseSix_index_odd
    a b D hfirst i hright heven
  rcases hiOdd with ⟨d, hd⟩
  rcases heven with ⟨e, he⟩
  have hbaseOdd : Odd base := ⟨d - e, by
    simp only [base]
    omega⟩
  rcases hbaseOdd with ⟨f, hf⟩
  have hiSuccInt : ((i.val + 1 : Nat) : Int) =
      (d + 1 : Int) + (d + 1 : Int) := by
    exact_mod_cast (show i.val + 1 = (d + 1) + (d + 1) by omega)
  have hbaseInt' : (base : Int) = 2 * (f : Int) + 1 := by
    exact_mod_cast hf
  have hbaseInt : (base : Int) = (f : Int) + (f : Int) + 1 := by
    omega
  have hmod := P.target_after (i.val + 1) (by omega) (by omega)
  apply caseSix_odd_of_modEq_two_of_odd
    (by simpa only [T, base] using hmod)
  refine ⟨(d + 1 : Int) * (T + 1) + (f : Int), ?_⟩
  rw [hiSuccInt, hbaseInt]
  ring

/-- An earlier odd pair above the overlap reference closes condition
2.1(ii). -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_secondParity_of_oddPair
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (j : Fin (n + 1)) (hjlt : j.val + 1 < i.val)
    (hsumOdd : Odd (c.order j.castSucc + c.order j.succ))
    (hreference :
      b.orderSequence.entryOrZero D.outer.transition.lastZero <
        c.order j.castSucc) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  have hcurrentEntry :=
    beli2019Lemma79_typeIII_overlap_caseSix_targetCurrent_eq_reference_add_one
      a b D hoverlap i hright hthroughLast heven
  have hcurrent : b.order ⟨i.val, i.lt_large⟩ = T + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order]
    simpa only [T] using hcurrentEntry
  exact lemma79_caseSix_secondParity_of_odd_pair_above_reference
    b c i T j hcurrent hjlt hsumOdd (by simpa only [T] using hreference)

set_option maxHeartbeats 5000000 in
-- The odd-prefix witness construction introduces several dependent indices.
/-- The opposite-current-parity subcase of overlapping type-III case 6. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_secondParity_oppositeCurrentParity
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hcomparison : Odd
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1) + 1)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  have htargetOdd :=
    beli2019Lemma79_typeIII_overlap_caseSix_targetPrefix_succ_odd
      a b D hfirst hoverlap i hright hthroughLast heven
  have hshifted :=
    caseSix_shiftedPrefix_modEq_of_comparison_odd_and_current_opposite
      b c i hcomparison horders
  have hthirdPrefix : Odd
      (c.orderSequence.prefixSum (i.val - 1)) :=
    caseSix_odd_of_modEq_two_of_odd hshifted.symm htargetOdd
  have hiOdd := beli2019Lemma79_typeIII_caseSix_index_odd
    a b D hfirst i hright heven
  rcases hiOdd with ⟨d, hd⟩
  have hlengthEven : Even (i.val - 1) := ⟨d, by omega⟩
  have hlengthPos : 0 < i.val - 1 := by
    by_contra hnot
    have hzero : i.val - 1 = 0 := by omega
    rw [hzero, BeliOrderSequence.prefixSum_zero] at hthirdPrefix
    rcases hthirdPrefix with ⟨z, hz⟩
    omega
  have hfirstLower :=
    beli2019Lemma79_typeIII_overlap_reference_le_thirdFirst
      a b c D hfirst hnorm
  have hfinalMod := caseSix_thirdPrevious_modEq_typeIII_overlap_reference
    a b c D hoverlap i hright hthroughLast heven horders
  have hlengthBound : i.val - 1 ≤ n + 2 :=
    (Nat.sub_le i.val 1).trans i.lt_large.le
  have hfinalBound : i.val - 1 < n + 2 :=
    (Nat.sub_le i.val 1).trans_lt i.lt_large
  have hlengthFinal : i.val - 1 - 1 ≤ i.val - 1 := Nat.sub_le _ _
  rcases c.exists_odd_entryPair_above_reference_of_even_prefix_odd
      (i.val - 1) (i.val - 1) T hlengthPos hlengthBound hlengthEven
      hthirdPrefix hfinalBound hlengthFinal
      (by simpa only [T] using hfirstLower)
      (by simpa only [T] using hfinalMod) with
    ⟨k, hkFinal, hkOdd, hkAbove⟩
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
    have hiPos := i.pos
    omega
  exact beli2019Lemma79_typeIII_overlap_caseSix_secondParity_of_oddPair
    a b c D hoverlap i hright hthroughLast heven
      j hjlt hsumOdd hreference

/-- The complete second comparison-prefix parity branch in overlapping
type-III case 6. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_secondParity
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hcomparison : Odd
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  rcases modEq_two_or_add_one
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1)) with hsame | hopposite
  · exact
      beli2019Lemma79_typeIII_overlap_caseSix_secondParity_sameCurrentParity
        a b c D hfirst hoverlap hnorm i hright hthroughLast heven
          hcomparison hsame
  · exact
      beli2019Lemma79_typeIII_overlap_caseSix_secondParity_oppositeCurrentParity
        a b c D hfirst hoverlap hnorm i hright hthroughLast heven
          hcomparison hopposite

end BONG.GoodBONG

end Bong
