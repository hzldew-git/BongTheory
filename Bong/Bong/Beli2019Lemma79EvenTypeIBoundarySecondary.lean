/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenSecondaryInterior
import Bong.Bong.Beli2019Lemma79EvenTypeIBoundaryAlpha

/-!
# Beli (2019), Lemma 7.9(ii), case 3: type-I boundary secondary candidate

When `i + 2` is the first canonical switch, the adjacent order shifts are
still `+1,-1`, so their sum is unchanged.  The complete left value theorem
and the switch-alpha estimate feed Remark 6.16 and close the last candidate.
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
-- The switch coordinate may be terminal, hence the complete local value.
/-- The shifted secondary-candidate comparison immediately before the first
canonical type-I switch. -/
theorem beli2019Lemma79_typeI_even_leftBoundary_secondary
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
    (hboundary : i.val + 2 = C.leftSwitch) :
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
  have hAlpha : a.representationAlpha b farIdx =
      (a.alphaValue ⟨farIdx.val - 1, by
        have hf := farIdx.lt_large
        omega⟩ : WithTop ℚ) :=
    beli2019Lemma69_ii_typeI_sourceLeftValue_complete
      a b D C hfirst hdefect farIdx (by simp only [farIdx]; omega)
        (by simp only [farIdx]; omega) hfarEven
  have hAlphaValue : a.representationAlphaValue b farIdx =
      a.alphaValue ⟨farIdx.val - 1, by
        have hf := farIdx.lt_large
        omega⟩ := by
    apply WithTop.coe_injective
    rw [a.coe_representationAlphaValue b farIdx]
    exact hAlpha
  have hswitchClose := beli2019Lemma79_typeI_leftSwitch_alphaClose
    a b D C hfirst hdefect (by omega)
  have hclose : b.alphaValue ⟨i.val + 1, by omega⟩ ≤
      a.alphaValue ⟨i.val + 1, by omega⟩ + 2 := by
    simpa only [← hboundary,
      show i.val + 2 - 1 = i.val + 1 by omega] using hswitchClose
  have hprefix := lemma79_even_secondaryPrefix_le_add_two_of_leftAlpha
    a b c hdefect i hfarBound
      (by simpa only [farIdx,
        show i.val + 2 - 1 = i.val + 1 by omega] using hAlphaValue)
      hclose
  have horders := lemma69_typeI_left_boundary_orders
    a b D C hfirst (i.val + 2) (by omega) (by omega)
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
