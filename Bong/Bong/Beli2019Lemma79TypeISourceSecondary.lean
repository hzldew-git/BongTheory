/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeISourcePrimary
import Bong.Bong.Beli2019Remark616RightMixedGeneral

/-!
# Beli (2019), Lemma 7.9(ii): the type-I secondary source candidate

Away from the right transition, the adjacent source and target order sums
agree.  Remark 6.16 at boundary `i + 2` then compares the remaining mixed
prefixes, proving the secondary-candidate comparison in case 4.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 2000000 in
-- The secondary candidate contains four dependent order indices.
/-- The comparison secondary candidate is no larger than the source
secondary candidate whenever `i + 2` remains in the central interval. -/
theorem lemma79_typeI_secondary_le_sourceSecondary_of_next_lt_right
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hodd : Odd i.val)
    (hleft : C.leftSwitch ≤ i.val - 1)
    (hnextRight : i.val + 1 < C.rightSwitch) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi := by
  rcases hodd with ⟨d, hd⟩
  have hfarBound : i.val + 2 < n + 2 := by
    have hr := C.right_le_last
    have hb := D.profile.lastDifference.bound
    omega
  let farIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 2, by omega, hfarBound, by omega⟩
  have hfarOdd : Odd farIdx.val := by
    exact ⟨d + 1, by simp only [farIdx]; omega⟩
  have hAlpha := beli2019Lemma69_ii_typeI_targetValue_from_conditions
    a b D C hfirst hrightLast horder hdefect farIdx hfarOdd
      (by simp only [farIdx]; omega)
      (by simp only [farIdx]; omega)
  have hformula := beli2019Remark616_rightMixedPrefix_at
    a b c hdefect farIdx hAlpha 1 (i.val - 2)
  have hprefix :
      b.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) ≤
        a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) := by
    calc
      b.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) =
          min (a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2))
            (b.alphaValue ⟨i.val + 1, by omega⟩ : WithTop ℚ) := by
        simpa only [farIdx, show i.val + 2 - 1 = i.val + 1 by omega]
          using hformula
      _ ≤ a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) :=
        min_le_left _ _
  have hsumEntries := lemma69_v_typeI_adjacent_entry_sum_eq
    a b D C hfirst i.val (by omega) (by omega)
  have hsumOrders :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ =
        b.order ⟨i.val, i.lt_large⟩ + b.order ⟨i.val + 1, hi.2⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hsumEntries
  have hcoefficientInt :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
            c.order ⟨i.val - 1, by omega⟩ =
        b.order ⟨i.val, i.lt_large⟩ + b.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
            c.order ⟨i.val - 1, by omega⟩ := by
    omega
  have hcoefficient :
      (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        c.order ⟨i.val - 2, by omega⟩ -
          c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) =
        (((b.order ⟨i.val, i.lt_large⟩ + b.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
            c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) := by
    exact_mod_cast hcoefficientInt
  unfold representationSecondaryDefect
  rw [hcoefficient]
  exact add_le_add_right hprefix _

end BONG.GoodBONG

end Bong
