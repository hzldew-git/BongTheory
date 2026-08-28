/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIAlphaFirstValue
import Bong.Bong.Beli2019Lemma69TypeICentralPositiveSeeds

/-!
# Beli (2019), Lemma 6.9(ii): complete type-I central seeds

The zero-left endpoint uses the explicit `i = 1` calculation and the empty
diagonal-prefix `i = 2` calculation.  Together with the positive-left branch,
this derives the former central seed package in all cases and removes it from
the public conditions-level statement.
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
-- Both endpoint indices are dependent on the rank and canonical switches.
/-- Conditions 2.1(i),(ii) determine both central seeds when the normalized
type-I left switch is zero. -/
theorem lemma69_typeI_centralSeedData_of_leftSwitch_zero_from_conditions
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hleftZero : C.leftSwitch = 0)
    (hstrict : C.leftSwitch < C.rightSwitch)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b) :
    Lemma69TypeICentralSeedData a b D C := by
  have hrightPos : 0 < C.rightSwitch := by omega
  have hrightBound : C.rightSwitch < n + 2 :=
    C.right_le_last.trans_lt D.profile.lastDifference.bound
  have hoddSeed : ∀ j : RepresentationIndex (n + 2) (n + 2),
      j.val = C.leftSwitch + 1 →
        a.representationAlpha b j =
          (b.alphaValue ⟨j.val - 1, by
            have hl := j.lt_large
            omega⟩ : WithTop ℚ) := by
    intro j hj
    have hjOne : j.val = 1 := by omega
    have hweight := beli2019Lemma69_v_typeI_of_rightSwitch_lt_last
      a b D C hfirst hrightLast horder hdefect 0 (by omega) hrightPos
    have hbeta := lemma69_typeI_beta_eq_one_of_leftSwitch_zero
      a b D C hfirst hleftZero hdefect j hjOne hrightPos (by
        simpa only using hweight)
    simpa only [hjOne] using hbeta
  have hevenSeed : ∀ j : RepresentationIndex (n + 2) (n + 2),
      j.val = C.leftSwitch + 2 →
        a.representationAlpha b j =
          (a.alphaValue ⟨j.val - 1, by
            have hl := j.lt_large
            omega⟩ : WithTop ℚ) := by
    intro j hj
    have hjTwoValue : j.val = 2 := by omega
    have hjEven : Even j.val := ⟨1, by omega⟩
    have hjTwo : 1 < j.val := by omega
    have hjLeft : C.leftSwitch ≤ j.val - 2 := by omega
    have hjRight : j.val - 1 < C.rightSwitch := by
      rcases C.right_even with ⟨e, he⟩
      omega
    have hjInterior : 1 < j.val ∧ j.val + 1 < n + 2 := by
      constructor
      · omega
      · have hb := D.profile.lastDifference.bound
        omega
    have hweight := beli2019Lemma69_v_typeI_of_rightSwitch_lt_last
      a b D C hfirst hrightLast horder hdefect 0 (by omega) hrightPos
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
    apply lemma69_typeI_alpha_eq_of_previous_or_first
      a b D C hfirst hdefect j hjEven hjTwo hjLeft hjRight
        hjInterior (by simpa only [hjTwoValue] using hweight) hprevious
    intro hthree
    omega
  exact ⟨hoddSeed, hevenSeed⟩

/-- The former two-seed interface follows from conditions in every
nonempty canonical type-I central interval. -/
theorem lemma69_typeI_centralSeedData_from_conditions
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hstrict : C.leftSwitch < C.rightSwitch)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b) :
    Lemma69TypeICentralSeedData a b D C := by
  by_cases hzero : C.leftSwitch = 0
  · exact lemma69_typeI_centralSeedData_of_leftSwitch_zero_from_conditions
      a b D C hfirst hzero hstrict hrightLast horder hdefect
  · exact lemma69_typeI_centralSeedData_of_leftSwitch_pos_from_conditions
      a b D C hfirst (Nat.pos_of_ne_zero hzero) hstrict hrightLast
        horder hdefect

/-- Conditions 2.1(i),(ii) determine all central type-I values, with no
external seed package. -/
theorem lemma69_typeI_central_values_from_conditions
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
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
  have S := lemma69_typeI_centralSeedData_from_conditions
    a b D C hfirst hstrict hrightLast horder hdefect
  exact lemma69_typeI_central_values_of_seeds_from_conditions
    a b D C hfirst hrightLast horder hdefect S i hiLeft hiRight

/-- Lemma 6.9(ii)'s finite target-beta value on the complete nonterminal
central type-I interval, with all seed assumptions eliminated. -/
theorem beli2019Lemma69_ii_typeI_targetValue_from_conditions
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
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
  have hvalue := (lemma69_typeI_central_values_from_conditions
    a b D C hfirst hrightLast horder hdefect i hiLeft hiRight).1 hodd
  apply WithTop.coe_injective
  rw [a.coe_representationAlphaValue b i]
  exact hvalue

end BONG.GoodBONG

end Bong
