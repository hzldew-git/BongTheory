/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIReduction

/-!
# Beli (2019), Lemma 9.12: the ternary type-I endpoint

The general type-I proof compares the mixed defect at the third boundary by
using the next representation index, and therefore assumes that a fourth
coefficient is present.  In rank three the third boundary is the full-rank
boundary.  Full value products of two good BONGs of the same quadratic space
differ by a square, so the required mixed defects are equal directly.  This
file supplies that endpoint argument and packages the resulting literal
index-uniformizer reduction.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG.Beli2019Lemma910Data

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {M : Lattice K V} {P : Lattice K W} {Q : Lattice K U}

/-- At ternary rank, the first mixed target-defect inequality is equivalent
to the scalar inequality at the complete source prefix. -/
theorem firstMixedDefect_iff_sourceFull_rankThree
    [Beli2006AlphaLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + 0))
    (c : GoodBONG s Q (0 + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data (N := 0) a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd 0 i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + 0 = 0 + 3)
    (hdefect : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength)) :
    ((β₁ : ℚ) : WithTop ℚ) ≤
        (E.bong.castLength hlength).truncatedPrefixDefect c 1 1 1 ↔
      ((β₁ : ℚ) : WithTop ℚ) ≤
        (a.castLength hlength).truncatedPrefixDefect c (-1) 3 1 := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  let p : Fin (0 + 1) := ⟨0, by omega⟩
  have houter := E.firstThirdOrder_eq a D hlength
  have hremark := target.beli2019Remark87 p (by
    simpa only [target, p, remark87PreviousValue, remark87NextValue]
      using houter)
  have hprevious : remark87PreviousAlpha p = (0 : Fin (0 + 2)) := by
    apply Fin.ext
    simp [p, remark87PreviousAlpha]
  have hself : target.truncatedPrefixDefect target (-1) 1 3 =
      ((β₁ : ℚ) : WithTop ℚ) := by
    have h := hremark.currentCappedDefect_eq
    rw [hprevious, E.firstAlpha] at h
    simpa only [p] using h
  have hselfReverse : target.truncatedPrefixDefect target (-1) 3 1 =
      ((β₁ : ℚ) : WithTop ℚ) := by
    rw [target.truncatedPrefixDefect_comm target (-1) 3 1]
    exact hself
  have hforward : ((β₁ : ℚ) : WithTop ℚ) ≤
      target.truncatedPrefixDefect c 1 1 1 →
      ((β₁ : ℚ) : WithTop ℚ) ≤
        target.truncatedPrefixDefect c (-1) 3 1 := by
    intro hshort
    have hdom := target.truncatedPrefixDefect_domination
      target c (-1) 1 3 1 1
    have hdom' : min (target.truncatedPrefixDefect target (-1) 3 1)
        (target.truncatedPrefixDefect c 1 1 1) ≤
          target.truncatedPrefixDefect c (-1) 3 1 := by
      simpa using hdom
    exact (le_min (le_of_eq hselfReverse.symm) hshort).trans hdom'
  have hreverse : ((β₁ : ℚ) : WithTop ℚ) ≤
      target.truncatedPrefixDefect c (-1) 3 1 →
      ((β₁ : ℚ) : WithTop ℚ) ≤
        target.truncatedPrefixDefect c 1 1 1 := by
    intro hfull
    have hdom := target.truncatedPrefixDefect_domination
      target c (-1) (-1) 1 3 1
    have h := (le_min (le_of_eq hself.symm) hfull).trans hdom
    simpa using h
  have hfull : target.truncatedPrefixDefect c (-1) 3 1 =
      source.truncatedPrefixDefect c (-1) 3 1 := by
    exact source.truncatedPrefixDefect_fullLeft_invariant target c (-1) 1
  constructor
  · intro hshort
    rw [← hfull]
    exact hforward hshort
  · intro hsource
    apply hreverse
    rw [hfull]
    exact hsource

/-- Ternary endpoint form of the first ordinary defect condition. -/
theorem representationDefectAt_first_iff_sourceFull_rankThree
    [Beli2006AlphaLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + 0))
    (c : GoodBONG s Q (0 + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data (N := 0) a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd 0 i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + 0 = 0 + 3)
    (hdefect : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength))
    (hfirst : (a.castLength hlength).order
        (⟨0, by omega⟩ : Fin (0 + 3)) =
      c.order (⟨0, by omega⟩ : Fin (0 + 3))) :
    let first := firstRepresentationIndex (0 + 1) (0 + 2)
    ((E.bong.castLength hlength).representationAlphaValue c first :
          WithTop ℚ) ≤
        (E.bong.castLength hlength).truncatedPrefixDefect
          c 1 first.val first.val ↔
      ((β₁ : ℚ) : WithTop ℚ) ≤
        (a.castLength hlength).truncatedPrefixDefect c (-1) 3 1 := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  let zero : Fin 3 := ⟨0, by omega⟩
  have htargetZero : target.order (⟨0, by omega⟩ : Fin (0 + 3)) = R₁ := by
    have h := E.order_castLength_prefix a D hlength zero
    have hzero : zero = (0 : Fin 3) := by
      apply Fin.ext
      rfl
    rw [hzero, D.order_zero] at h
    simpa [target, zero] using h
  have hsourceZero : source.order (⟨0, by omega⟩ : Fin (0 + 3)) = R₁ := by
    rw [GoodBONG.order_castLength]
    have hindex : (⟨0, by omega⟩ : Fin (3 + 0)) =
        Fin.castAdd 0 zero := by
      apply Fin.ext
      rfl
    rw [hindex, horders zero]
    rfl
  have htargetFirst : target.order (⟨0, by omega⟩ : Fin (0 + 3)) =
      c.order (⟨0, by omega⟩ : Fin (0 + 3)) :=
    htargetZero.trans (hsourceZero.symm.trans hfirst)
  let first := firstRepresentationIndex (0 + 1) (0 + 2)
  have halpha : target.representationAlpha c first =
      (target.alphaValue (0 : Fin (0 + 2)) : WithTop ℚ) := by
    exact target.beli2019Lemma812_i c htargetFirst
  change (target.representationAlphaValue c first : WithTop ℚ) ≤
      target.truncatedPrefixDefect c 1 first.val first.val ↔ _
  rw [target.coe_representationAlphaValue, halpha, E.firstAlpha]
  simpa only [first, firstRepresentationIndex, source, target] using
    E.firstMixedDefect_iff_sourceFull_rankThree
      a c D horders hlength hdefect

private theorem representationIndex_eq_of_val_eq_rankThree
    (i j : RepresentationIndex 3 3) (h : i.val = j.val) : i = j := by
  cases i
  cases j
  cases h
  rfl

/-- In ternary rank, condition (ii) is equivalent to the same two scalar
conditions as in the general type-I claim. -/
theorem representationDefectCondition_iff_scalar_rankThree
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + 0))
    (c : GoodBONG s Q (0 + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data (N := 0) a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd 0 i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + 0 = 0 + 3)
    (hdefect : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength))
    (hac : (a.castLength hlength).RepresentationDefectCondition c)
    (hfirst : (a.castLength hlength).order
        (⟨0, by omega⟩ : Fin (0 + 3)) =
      c.order (⟨0, by omega⟩ : Fin (0 + 3))) :
    (E.bong.castLength hlength).RepresentationDefectCondition c ↔
      ((β₁ : ℚ) : WithTop ℚ) ≤
          (a.castLength hlength).truncatedPrefixDefect c (-1) 3 1 ∧
        ∀ i : RepresentationIndex (0 + 3) (0 + 3), 2 ≤ i.val →
          ((E.bong.castLength hlength).representationAlphaValue c i :
              WithTop ℚ) ≤
            (((((E.bong.castLength hlength).order
                  ⟨i.val, i.lt_large⟩ -
                (E.bong.castLength hlength).order
                  (⟨1, by omega⟩ : Fin (0 + 3)) : Int) : ℚ) +
              (β₁ : ℚ) : ℚ) : WithTop ℚ) := by
  let first := firstRepresentationIndex (0 + 1) (0 + 2)
  constructor
  · intro hbc
    refine ⟨?_, ?_⟩
    · apply (E.representationDefectAt_first_iff_sourceFull_rankThree
        a c D horders hlength hdefect hfirst).mp
      exact hbc first
    · intro i hi
      apply (E.representationDefectAt_iff_shift
        a c D horders hlength hdefect hac i hi).mp
      exact hbc i
  · rintro ⟨hfirstScalar, hlater⟩ i
    by_cases hiFirst : i.val = 1
    · have hieq : i = first := by
        apply representationIndex_eq_of_val_eq_rankThree
        simpa only [first, firstRepresentationIndex] using hiFirst
      subst i
      apply (E.representationDefectAt_first_iff_sourceFull_rankThree
        a c D horders hlength hdefect hfirst).mpr
      exact hfirstScalar
    · have hiTwo : 2 ≤ i.val := by
        have := i.pos
        omega
      apply (E.representationDefectAt_iff_shift
        a c D horders hlength hdefect hac i hiTwo).mpr
      exact hlater i hiTwo

/-- Ternary specialization of the type-I scalar characterization for the v2
four-condition package. -/
theorem representationConditionsPrime_iff_typeIScalarConditions_rankThree
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + 0))
    (c : GoodBONG s Q (0 + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data (N := 0) a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd 0 i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + 0 = 0 + 3)
    (hdefectSourceTarget :
      (a.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength))
    (hsource : RepresentationConditions (a.castLength hlength) c le_rfl)
    (hfirst : (a.castLength hlength).order
        (⟨0, by omega⟩ : Fin (0 + 3)) =
      c.order (⟨0, by omega⟩ : Fin (0 + 3)))
    (horderTarget :
      (E.bong.castLength hlength).RepresentationOrderCondition c le_rfl) :
    RepresentationConditionsPrime (E.bong.castLength hlength) c le_rfl ↔
      E.TypeIScalarConditions a c D hlength := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  let target := E.bong.castLength hlength
  have hdefectEquiv := E.representationDefectCondition_iff_scalar_rankThree
    a c D horders hlength hdefectSourceTarget hsource.defectCondition hfirst
  constructor
  · intro conditions
    exact hdefectEquiv.mp conditions.defectCondition
  · intro hscalar
    have hdefectTarget := hdefectEquiv.mpr hscalar
    refine {
      orderCondition := horderTarget
      defectCondition := hdefectTarget
      centralRepresentations := ?_
      longRepresentations := ?_ }
    · exact E.centralRepresentationConditionsPrime
        (sourceLaws := sourceLaws) (targetLaws := targetLaws)
        a c D horders hlength hdefectSourceTarget hfirst horderTarget
          hdefectTarget hsource.centralRepresentations
    · exact E.longRepresentationConditions
        a c D horders hlength hsource.longRepresentations

/-- Ternary specialization for the original condition (iii). -/
theorem representationConditions_iff_typeIScalarConditions_rankThree
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + 0))
    (c : GoodBONG s Q (0 + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data (N := 0) a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd 0 i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + 0 = 0 + 3)
    (hdefectSourceTarget :
      (a.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength))
    (hsource : RepresentationConditions (a.castLength hlength) c le_rfl)
    (hfirst : (a.castLength hlength).order
        (⟨0, by omega⟩ : Fin (0 + 3)) =
      c.order (⟨0, by omega⟩ : Fin (0 + 3)))
    (horderTarget :
      (E.bong.castLength hlength).RepresentationOrderCondition c le_rfl) :
    RepresentationConditions (E.bong.castLength hlength) c le_rfl ↔
      E.TypeIScalarConditions a c D hlength := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  let target := E.bong.castLength hlength
  have hprime := E.representationConditionsPrime_iff_typeIScalarConditions_rankThree
    (sourceLaws := sourceLaws) (targetLaws := targetLaws)
    a c D horders hlength hdefectSourceTarget hsource hfirst horderTarget
  constructor
  · intro conditions
    have htriggers := target.beli2019Lemma216
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      c le_rfl conditions.orderCondition conditions.defectCondition
    apply hprime.mp
    exact (representationConditions_iff_prime
      target c le_rfl htriggers).mp conditions
  · intro hscalar
    have conditionsPrime := hprime.mpr hscalar
    have htriggers := target.beli2019Lemma216
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      c le_rfl conditionsPrime.orderCondition
        conditionsPrime.defectCondition
    exact (representationConditions_iff_prime
      target c le_rfl htriggers).mpr conditionsPrime

/-- A ternary type-I scalar package produces the literal index-uniformizer
reduction used by Section 9 descent. -/
noncomputable def indexPReduction_of_typeIScalarConditions_rankThree
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + 0))
    (c : GoodBONG s Q (0 + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data (N := 0) a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd 0 i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + 0 = 0 + 3)
    (hdefectSourceTarget :
      (a.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength))
    (hsource : RepresentationConditions (a.castLength hlength) c le_rfl)
    (hfirst : (a.castLength hlength).order
        (⟨0, by omega⟩ : Fin (0 + 3)) =
      c.order (⟨0, by omega⟩ : Fin (0 + 3)))
    (horderTarget :
      (E.bong.castLength hlength).RepresentationOrderCondition c le_rfl)
    (ambient : q.Represents s)
    (hscalar : E.TypeIScalarConditions a c D hlength) :
    let problem := Beli2019RepresentationProblem.ofData
      (a.castLength hlength) c le_rfl ambient hsource
    Beli2019RepresentationProblem.IndexPReduction problem := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  have htarget : RepresentationConditions target c le_rfl :=
    (E.representationConditions_iff_typeIScalarConditions_rankThree
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      a c D horders hlength hdefectSourceTarget hsource hfirst
        horderTarget).mpr hscalar
  let problem := Beli2019RepresentationProblem.ofData
    source c le_rfl ambient hsource
  change Beli2019RepresentationProblem.IndexPReduction problem
  exact {
    index_eq := rfl
    lattice := E.lattice
    inclusion := E.inclusion
    targetBONG := target
    conditions := htarget }

end BONG.GoodBONG.Beli2019Lemma910Data

end Bong
