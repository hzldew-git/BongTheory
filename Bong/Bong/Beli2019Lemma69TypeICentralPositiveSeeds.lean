/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIBetaPreviousValue
import Bong.Bong.Beli2019Lemma69TypeICentralFromConditions
import Bong.Bong.Beli2019Lemma69TypeILeftValue

/-!
# Beli (2019), Lemma 6.9(ii): positive-left type-I seeds

When the canonical left switch is positive, the completed left-branch
induction supplies the value immediately before the central interval.  The
Lemma 2.7 odd step gives the first central value, and the established even
step gives the second.  Thus the former two-seed interface is derived from
the representation conditions in this branch.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

set_option maxHeartbeats 3000000 in
-- The two dependent seed indices are transported through the left-switch equality.
/-- Conditions 2.1(i),(ii) determine both central seeds when the normalized
type-I left switch is positive. -/
theorem lemma69_typeI_centralSeedData_of_leftSwitch_pos_from_conditions
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hleftPos : 0 < C.leftSwitch)
    (hstrict : C.leftSwitch < C.rightSwitch)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b) :
    Lemma69TypeICentralSeedData a b D C := by
  have hrightBound : C.rightSwitch < n + 2 :=
    C.right_le_last.trans_lt D.profile.lastDifference.bound
  have hleftNext : C.leftSwitch + 1 < n + 2 := by omega
  have hleftValue := beli2019Lemma69_ii_typeI_leftSwitchValue
    a b D C hfirst hleftPos hleftNext hdefect
  have hoddSeed : ∀ j : RepresentationIndex (n + 2) (n + 2),
      j.val = C.leftSwitch + 1 →
        a.representationAlpha b j =
          (b.alphaValue ⟨j.val - 1, by
            have hl := j.lt_large
            omega⟩ : WithTop ℚ) := by
    intro j hj
    have hjOdd : Odd j.val := by
      rcases C.left_even with ⟨d, hd⟩
      exact ⟨d, by omega⟩
    have hjTwo : 1 < j.val := by
      rcases C.left_even with ⟨d, hd⟩
      omega
    have hjLeft : C.leftSwitch ≤ j.val - 1 := by omega
    have hjRight : j.val - 1 < C.rightSwitch := by omega
    have hweight := beli2019Lemma69_v_typeI_of_rightSwitch_lt_last
      a b D C hfirst hrightLast horder hdefect (j.val - 1)
        hjLeft hjRight
    have hprevious : a.representationAlpha b
        (⟨j.val - 1, by omega, by omega, by omega⟩ :
          RepresentationIndex (n + 2) (n + 2)) =
      (a.alphaValue ⟨j.val - 2, by omega⟩ : WithTop ℚ) := by
      simpa only [hj, show C.leftSwitch + 1 - 1 = C.leftSwitch by omega,
        show C.leftSwitch + 1 - 2 = C.leftSwitch - 1 by omega]
        using hleftValue
    apply lemma69_typeI_beta_eq_of_previous_normal
      a b D C hfirst hdefect j hjOdd hjTwo hjLeft hjRight
    · simpa only using hweight
    · exact hprevious
  have hevenSeed : ∀ j : RepresentationIndex (n + 2) (n + 2),
      j.val = C.leftSwitch + 2 →
        a.representationAlpha b j =
          (a.alphaValue ⟨j.val - 1, by
            have hl := j.lt_large
            omega⟩ : WithTop ℚ) := by
    intro j hj
    have hjEven : Even j.val := by
      rcases C.left_even with ⟨d, hd⟩
      exact ⟨d + 1, by omega⟩
    have hjThree : 2 < j.val := by
      rcases C.left_even with ⟨d, hd⟩
      omega
    have hjLeft : C.leftSwitch ≤ j.val - 2 := by omega
    have hjRight : j.val - 1 < C.rightSwitch := by
      rcases C.left_even with ⟨d, hd⟩
      rcases C.right_even with ⟨e, he⟩
      omega
    have hjInterior : 1 < j.val ∧ j.val + 1 < n + 2 := by
      constructor
      · omega
      · have hb := D.profile.lastDifference.bound
        omega
    have hweight := beli2019Lemma69_v_typeI_of_rightSwitch_lt_last
      a b D C hfirst hrightLast horder hdefect (j.val - 2)
        (by omega) (by omega)
    let previousIdx : RepresentationIndex (n + 2) (n + 2) :=
      ⟨j.val - 1, by omega, by omega, by omega⟩
    have hpreviousRaw := hoddSeed previousIdx (by
      simp only [previousIdx]
      omega)
    have hprevious : a.representationAlpha b
        (⟨j.val - 1, by omega, by omega, by omega⟩ :
          RepresentationIndex (n + 2) (n + 2)) =
      (b.alphaValue ⟨j.val - 2, by omega⟩ : WithTop ℚ) := by
      simpa only [previousIdx,
        show j.val - 1 - 1 = j.val - 2 by omega] using hpreviousRaw
    have hearlier : a.representationAlpha b
        (⟨j.val - 2, by omega, by omega, by omega⟩ :
          RepresentationIndex (n + 2) (n + 2)) =
      (a.alphaValue ⟨j.val - 3, by omega⟩ : WithTop ℚ) := by
      simpa only [hj, show C.leftSwitch + 2 - 2 = C.leftSwitch by omega,
        show C.leftSwitch + 2 - 3 = C.leftSwitch - 1 by omega]
        using hleftValue
    exact lemma69_typeI_alpha_eq_of_previous
      a b D C hfirst hdefect j hjEven hjThree hjLeft hjRight
        hjInterior (by simpa only using hweight) hprevious hearlier
  exact ⟨hoddSeed, hevenSeed⟩

/-- All central type-I values follow directly from conditions in the
positive-left branch. -/
theorem lemma69_typeI_central_values_of_leftSwitch_pos_from_conditions
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hleftPos : 0 < C.leftSwitch)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiLeft : C.leftSwitch ≤ i.val - 1)
    (hiRight : i.val - 1 < C.rightSwitch) :
    (Odd i.val → a.representationAlpha b i =
      (b.alphaValue ⟨i.val - 1, by
        have hl := i.lt_large
        omega⟩ : WithTop ℚ)) ∧
    (Even i.val → a.representationAlpha b i =
      (a.alphaValue ⟨i.val - 1, by
        have hl := i.lt_large
        omega⟩ : WithTop ℚ)) := by
  have hstrict : C.leftSwitch < C.rightSwitch := hiLeft.trans_lt hiRight
  have S := lemma69_typeI_centralSeedData_of_leftSwitch_pos_from_conditions
    a b D C hfirst hleftPos hstrict hrightLast horder hdefect
  exact lemma69_typeI_central_values_of_seeds_from_conditions
    a b D C hfirst hrightLast horder hdefect S i hiLeft hiRight

/-- The finite target-beta value in the positive-left central branch, with
the seed interface fully eliminated. -/
theorem beli2019Lemma69_ii_typeI_targetValue_of_leftSwitch_pos
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hleftPos : 0 < C.leftSwitch)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val)
    (hiLeft : C.leftSwitch ≤ i.val - 1)
    (hiRight : i.val - 1 < C.rightSwitch) :
    a.representationAlphaValue b i =
      b.alphaValue ⟨i.val - 1, by
        have hl := i.lt_large
        omega⟩ := by
  have hvalue :=
    (lemma69_typeI_central_values_of_leftSwitch_pos_from_conditions
      a b D C hfirst hleftPos hrightLast horder hdefect i
        hiLeft hiRight).1 hodd
  apply WithTop.coe_injective
  rw [a.coe_representationAlphaValue b i]
  exact hvalue

end BONG.GoodBONG

end Bong
