/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeILeftValueLocal
import Bong.Bong.Beli2019Lemma79EvenSecondaryInterior
import Bong.Bong.Beli2019Lemma79EvenTypeIAlphaShift

/-!
# Beli (2019), Lemma 7.9(ii), case 3: early type-I candidates

The canonical type-I order profile gives the `+2` comparison for each of
the three candidates defining the representation alpha.  The secondary
comparison uses the local form of Lemma 6.9(ii) at boundary `i + 2`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The half-gap candidate comparison before the first type-I switch. -/
theorem lemma79_typeI_even_left_halfGap_le_add_two
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiEven : Even i.val) (hbefore : i.val < C.leftSwitch) :
    b.representationHalfGap c i ≤
      a.representationHalfGap c i + ((2 : ℚ) : WithTop ℚ) := by
  have hsource := C.source_to_anchor i.val
    (hbefore.le.trans C.left_le_anchor) hiEven
  have htarget := C.target_before_left i.val hbefore hiEven
  apply representationHalfGap_le_add_two_of_order_le_add_four a b c i
  rw [← a.orderSequence_entryOrZero_eq_order,
    ← b.orderSequence_entryOrZero_eq_order]
  change b.orderSequence.entryOrZero i.val ≤
    a.orderSequence.entryOrZero i.val + 4
  omega

/-- The primary candidate comparison before the first type-I switch. -/
theorem lemma79_typeI_even_left_primary_le_add_two
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (hiEven : Even i.val) (hbefore : i.val < C.leftSwitch) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i +
        ((2 : ℚ) : WithTop ℚ) := by
  have hleftPos : 0 < C.leftSwitch := by omega
  have hsource := C.source_to_anchor i.val
    (hbefore.le.trans C.left_le_anchor) hiEven
  have htarget := C.target_before_left i.val hbefore hiEven
  apply representationPrimaryDefect_le_add_two_of_order_eq_add_one
    a b c i hiNext
  · rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    change b.orderSequence.entryOrZero i.val =
      a.orderSequence.entryOrZero i.val + 1
    omega
  · exact beli2019Lemma69_i_typeI_targetLeftTail
      a b D C hfirst hleftPos i.val hbefore hiEven

set_option maxHeartbeats 3000000 in
-- Lemma 6.9(ii) and Remark 6.16 transport dependent prefix indices.
/-- The secondary candidate comparison strictly before the first type-I
switch boundary. -/
theorem beli2019Lemma79_typeI_even_left_secondary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hfarBefore : i.val + 2 < C.leftSwitch) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((2 : ℚ) : WithTop ℚ) := by
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  have hfarBound : i.val + 2 < n + 2 := by omega
  let farIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 2, by omega, hfarBound, hfarBound.le⟩
  have hfarEven : Even farIdx.val := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d + 1, by simp only [farIdx]; omega⟩
  have hfarNext : farIdx.val + 1 < n + 2 := by
    simp only [farIdx]
    omega
  have hAlpha : a.representationAlpha b farIdx =
      (a.alphaValue ⟨farIdx.val - 1, by omega⟩ : WithTop ℚ) :=
    beli2019Lemma69_ii_typeI_sourceLeftValue_of_next
      a b D C hfirst hdefect farIdx (by simp only [farIdx]; omega)
        (by simp only [farIdx]; omega) hfarEven hfarNext
  have hAlphaValue : a.representationAlphaValue b farIdx =
      a.alphaValue ⟨farIdx.val - 1, by omega⟩ := by
    apply WithTop.coe_injective
    rw [a.coe_representationAlphaValue b farIdx]
    exact hAlpha
  have hclose := beli2019Lemma79_typeI_even_left_alphaClose
    a b D C hfirst hdefect farIdx (by simp only [farIdx]; omega)
      hfarEven (by simpa only [farIdx] using hfarBefore)
  have hprefix := lemma79_even_secondaryPrefix_le_add_two_of_leftAlpha
    a b c hdefect i hfarBound
      (by simpa only [farIdx,
        show i.val + 2 - 1 = i.val + 1 by omega] using hAlphaValue)
      (by simpa only [farIdx,
        show i.val + 2 - 1 = i.val + 1 by omega] using hclose)
  have horders := lemma69_typeI_left_boundary_orders
    a b D C hfirst (i.val + 2) (by omega) hfarBefore.le
      (by rcases hiEven with ⟨d, hd⟩; exact ⟨d + 1, by omega⟩)
  have htargetCurrent : b.orderSequence.entryOrZero i.val =
      a.orderSequence.entryOrZero i.val + 1 := by
    simpa only [show i.val + 2 - 2 = i.val by omega] using horders.2.1
  have htargetNext : b.orderSequence.entryOrZero (i.val + 1) =
      a.orderSequence.entryOrZero (i.val + 1) - 1 := by
    simpa only [show i.val + 2 - 1 = i.val + 1 by omega] using horders.2.2
  apply representationSecondaryDefect_le_add_two_of_orderSum_eq
    a b c i hi
  · rw [← a.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    change b.orderSequence.entryOrZero i.val +
        b.orderSequence.entryOrZero (i.val + 1) =
      a.orderSequence.entryOrZero i.val +
        a.orderSequence.entryOrZero (i.val + 1)
    rw [htargetCurrent, htargetNext]
    omega
  · exact hprefix

end BONG.GoodBONG

end Bong
