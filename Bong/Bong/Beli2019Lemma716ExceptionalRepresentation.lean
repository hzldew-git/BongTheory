/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716TypeIIDefect

/-!
# Beli (2019), Lemma 7.16: representations forced by an exceptional profile

Corollary 2.17 produces the original condition-(iii) alpha trigger.  Lemma
2.16 converts it to the revised v2 condition-(iii') defect trigger, after
which the assumed representation conditions give the required prefix
representation.  In type II the endpoint case is independent of condition
(iii'): the target prefix is the whole ambient space, so ordinary prefix
inclusion followed by a change of complete BONG suffices.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L N : Lattice K V} {n : Nat}

variable [Beli2006AlphaLaws.{u, v} K]

/-- In the type-I exceptional profile, revised condition (iii') supplies
`[c₁, ..., cₛ₋₁] → [a₁, ..., aₛ]`. -/
theorem lemma716_typeI_failureProfile_prefixRepresents
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hI : Lemma714IsTypeI a R s) (hsInterior : s < n + 3)
    (P : Beli2019Lemma716TypeIFailureProfile c R s D.two_le D.le_rank) :
    DiagonalRepresents
      (c.prefixValues (s - 1) (by omega))
      (a.prefixValues s D.le_rank) := by
  let i : CentralRepresentationIndex (n + 3) (n + 3) :=
    { val := s
      one_lt := by have := D.two_le; omega
      lt_large := hsInterior
      le_small_succ := by omega }
  have halpha : a.centralAlphaTrigger c i := by
    simpa only [i] using
      a.lemma716_typeI_failureProfile_alphaTrigger c R s D hfirst
        hsecond hthird hac.orderCondition hac.defectCondition hI hsInterior P
  have hdefect : a.centralDefectTrigger c i :=
    (a.beli2019Lemma216 c le_rfl hac.orderCondition hac.defectCondition i).mp
      halpha
  simpa [i] using hac.centralRepresentations i hdefect

/-- The type-I exceptional profile always gives the required prefix
representation.  At the terminal endpoint it comes from the common ambient
quadratic space, exactly as in the type-II endpoint case below. -/
theorem lemma716_typeI_failureProfile_prefixRepresents_all
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hI : Lemma714IsTypeI a R s)
    (P : Beli2019Lemma716TypeIFailureProfile c R s D.two_le D.le_rank) :
    DiagonalRepresents
      (c.prefixValues (s - 1) (by
        have := D.le_rank
        omega))
      (a.prefixValues s D.le_rank) := by
  by_cases hsInterior : s < n + 3
  · exact a.lemma716_typeI_failureProfile_prefixRepresents c R s D
      hfirst hsecond hthird hac hI hsInterior P
  · have hsFull : s = n + 3 := by
      have := D.le_rank
      omega
    have hprefix := c.prefixValues_represents_of_le
      (s - 1) (n + 3) (by omega) le_rfl
    have hrepresented := hprefix.trans (c.fullPrefix_represents a)
    exact prefixRepresents_cast c a rfl hsFull.symm hrepresented

/-- In the proper-prefix type-II branch, revised condition (iii') supplies
`[c₁, ..., cₛ] → [a₁, ..., aₛ₊₁]`. -/
theorem lemma716_typeII_failureProfile_prefixRepresents_of_next
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hII : Lemma714IsTypeII a R s) (hsNext : s + 2 ≤ n + 3)
    (P : Beli2019Lemma716TypeIIFailureProfile c R s D.two_le
      (Classical.choose hII)) :
    DiagonalRepresents
      (c.prefixValues s (Nat.le_of_lt (Classical.choose hII)))
      (a.prefixValues (s + 1) (by
        have := Classical.choose hII
        omega)) := by
  let i : CentralRepresentationIndex (n + 3) (n + 3) :=
    { val := s + 1
      one_lt := by have := D.two_le; omega
      lt_large := by omega
      le_small_succ := by omega }
  have halpha : a.centralAlphaTrigger c i := by
    simpa only [i] using
      a.lemma716_typeII_failureProfile_alphaTrigger c R s D hfirst
        hsecond hthird hac.orderCondition hac.defectCondition hII hsNext P
  have hdefect : a.centralDefectTrigger c i :=
    (a.beli2019Lemma216 c le_rfl hac.orderCondition hac.defectCondition i).mp
      halpha
  simpa [i] using hac.centralRepresentations i hdefect

/-- The type-II exceptional profile always gives the required prefix
representation.  At the final coordinate this follows from the common
ambient quadratic space rather than from condition (iii'). -/
theorem lemma716_typeII_failureProfile_prefixRepresents
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hII : Lemma714IsTypeII a R s)
    (P : Beli2019Lemma716TypeIIFailureProfile c R s D.two_le
      (Classical.choose hII)) :
    DiagonalRepresents
      (c.prefixValues s (Nat.le_of_lt (Classical.choose hII)))
      (a.prefixValues (s + 1) (by
        have := Classical.choose hII
        omega)) := by
  by_cases hsNext : s + 2 ≤ n + 3
  · exact a.lemma716_typeII_failureProfile_prefixRepresents_of_next c R s D
      hfirst hsecond hthird hac hII hsNext P
  · have hsFull : s + 1 = n + 3 := by
      have hsInterior := Classical.choose hII
      omega
    have hprefix := c.prefixValues_represents_of_le
      s (n + 3) (Nat.le_of_lt (Classical.choose hII)) le_rfl
    have hrepresented := hprefix.trans (c.fullPrefix_represents a)
    exact prefixRepresents_cast c a rfl hsFull.symm hrepresented

end BONG.GoodBONG

end Bong
