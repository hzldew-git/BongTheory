/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIBeta
import Bong.Bong.DiagonalTailCancellation
import Bong.Bong.Beli2019Lemma216Complete

/-!
# Beli (2019), Lemma 9.12: the complete type-I claim

The Lemma 9.10 construction changes only its ternary prefix.  Common-tail
cancellation identifies every old and new prefix of length at least three.
Together with the comparison inequalities from the preceding files, this
proves conditions (iii') and (iv) and packages the full v2 claim as an
if-and-only-if with the two scalar inequalities displayed in the paper.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {M : Lattice K V} {P : Lattice K W} {Q : Lattice K U}
  {N : Nat}

namespace Beli2019Lemma910Data

/-- Every coefficient from the fourth onward is unchanged by the type-I
replacement. -/
theorem valueUnit_castLength_eq_source_of_three_le
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (hlength : 3 + N = N + 3) (i : Fin (N + 3)) (hi : 3 ≤ i.val) :
    (E.bong.castLength hlength).valueUnit i =
      (a.castLength hlength).valueUnit i := by
  rw [valueUnit_castLength, valueUnit_castLength, E.values]
  let j : Fin (3 + N) := ⟨i.val, by omega⟩
  change beli2019Lemma910Values D a j = a.valueUnit j
  let k : Fin N := ⟨i.val - 3, by omega⟩
  have hj : j = Fin.natAdd 3 k := by
    apply Fin.ext
    simp only [j, k, Fin.val_mk, Fin.natAdd_mk]
    omega
  rw [hj, beli2019Lemma910Values_right]

/-- The replacement preserves the first order, even though it changes the
first coefficient. -/
theorem firstOrder_castLength_eq_source
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3) :
    (E.bong.castLength hlength).order
        (⟨0, by omega⟩ : Fin (N + 3)) =
      (a.castLength hlength).order
        (⟨0, by omega⟩ : Fin (N + 3)) := by
  let zero : Fin 3 := 0
  rw [show (⟨0, by omega⟩ : Fin (N + 3)) =
        ⟨zero.val, by omega⟩ by
      apply Fin.ext
      rfl,
    E.order_castLength_prefix a D hlength, D.order_zero,
    GoodBONG.order_castLength]
  have hindex : (⟨zero.val, by omega⟩ : Fin (3 + N)) =
      Fin.castAdd N zero := by
    apply Fin.ext
    rfl
  rw [hindex, horders zero]
  rfl

/-- Full ambient isometry and equality of the unchanged tail identify every
new and old prefix of length at least three. -/
theorem sourcePrefix_represents_targetPrefix
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (hlength : 3 + N = N + 3)
    (k : Nat) (hkThree : 3 ≤ k) (hk : k ≤ N + 3) :
    DiagonalRepresents
      ((a.castLength hlength).prefixValues k hk)
      ((E.bong.castLength hlength).prefixValues k hk) := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  have hfull : DiagonalRepresents source.toBONG.value target.toBONG.value :=
    source.toBONG.diagonalRepresents_values target.toBONG
  have htail : ∀ i, k ≤ i.val → source.toBONG.value i =
      target.toBONG.value i := by
    intro i hi
    have hiThree : 3 ≤ i.val := hkThree.trans hi
    have hu := E.valueUnit_castLength_eq_source_of_three_le
      a D hlength i hiThree
    have hv := congrArg Units.val hu
    simpa only [source, target, GoodBONG.coe_valueUnit,
      GoodBONG.value] using hv.symm
  have hcancelled := DiagonalRepresents.cancel_common_suffix
    source.toBONG.value target.toBONG.value hk
    source.toBONG.value_ne_zero target.toBONG.value_ne_zero htail hfull
  change DiagonalRepresents
    (fun i : Fin k => source.toBONG.value ⟨i.val, i.isLt.trans_le hk⟩)
    (fun i : Fin k => target.toBONG.value ⟨i.val, i.isLt.trans_le hk⟩)
  exact hcancelled

/-- An active central trigger cannot occur at the first possible boundary;
there the two compared orders are equal. -/
theorem three_le_of_centralAlphaTrigger_target
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hfirst : (a.castLength hlength).order
        (⟨0, by omega⟩ : Fin (N + 3)) =
      c.order (⟨0, by omega⟩ : Fin (N + 3)))
    (i : CentralRepresentationIndex (N + 3) (N + 3))
    (htrigger : (E.bong.castLength hlength).centralAlphaTrigger c i) :
    3 ≤ i.val := by
  by_contra hi
  have hiTwo : i.val = 2 := by
    have := i.one_lt
    omega
  have hsmall :
      (⟨i.val - 2, by have := i.one_lt; omega⟩ : Fin (N + 3)) =
        (⟨0, by omega⟩ : Fin (N + 3)) := by
    apply Fin.ext
    change i.val - 2 = 0
    omega
  have hlarge :
      (⟨i.val, i.lt_large⟩ : Fin (N + 3)) =
        (⟨2, by omega⟩ : Fin (N + 3)) := by
    apply Fin.ext
    exact hiTwo
  have houter := E.firstThirdOrder_eq a D hlength
  have hzero := E.firstOrder_castLength_eq_source
    a D horders hlength
  have heq :
      (E.bong.castLength hlength).order
          (⟨2, by omega⟩ : Fin (N + 3)) =
        c.order (⟨0, by omega⟩ : Fin (N + 3)) := by
    exact houter.symm.trans (hzero.trans hfirst)
  have hlt := htrigger.1
  rw [hsmall, hlarge] at hlt
  exact lt_irrefl _ (hlt.trans_eq heq)

/-- Every active central trigger for the type-I output, except for the
impossible first boundary, is already active for the source BONG. -/
theorem centralAlphaTrigger_source_of_target
    [Beli2006AlphaLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefect : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength))
    (hfirst : (a.castLength hlength).order
        (⟨0, by omega⟩ : Fin (N + 3)) =
      c.order (⟨0, by omega⟩ : Fin (N + 3)))
    (i : CentralRepresentationIndex (N + 3) (N + 3))
    (htrigger : (E.bong.castLength hlength).centralAlphaTrigger c i) :
    (a.castLength hlength).centralAlphaTrigger c i := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  have hiThree := E.three_le_of_centralAlphaTrigger_target
    a c D horders hlength hfirst i htrigger
  have hiCurrent : i.val ≤ N + 3 := by
    have := i.lt_large
    omega
  have horderCurrent : target.order
        (⟨i.val, i.lt_large⟩ : Fin (N + 3)) =
      source.order (⟨i.val, i.lt_large⟩ : Fin (N + 3)) :=
      E.order_castLength_eq_source_of_two_le
        a D horders hlength
          (⟨i.val, i.lt_large⟩ : Fin (N + 3)) (by
            change 2 ≤ i.val
            omega)
  have horderPrevious : target.order
        (⟨i.val - 1, by have := i.one_lt; have := i.lt_large; omega⟩ :
          Fin (N + 3)) =
      source.order
        (⟨i.val - 1, by have := i.one_lt; have := i.lt_large; omega⟩ :
          Fin (N + 3)) :=
      E.order_castLength_eq_source_of_two_le
        a D horders hlength
          (⟨i.val - 1, by
            have := i.one_lt
            have := i.lt_large
            omega⟩ : Fin (N + 3)) (by
              change 2 ≤ i.val - 1
              omega)
  have hprevious := E.representationAlphaValue_le_source
      a c D horders hlength hdefect i.previous (by
        simp only [CentralRepresentationIndex.previous]
        omega)
  have hcurrent := E.representationAlphaValue_le_source
      a c D horders hlength hdefect (i.current hiCurrent) (by
        simp only [CentralRepresentationIndex.current]
        omega)
  have hpreviousTop :
        ((target.representationAlphaValue c i.previous : ℚ) : WithTop ℚ) ≤
          ((source.representationAlphaValue c i.previous : ℚ) : WithTop ℚ) := by
      exact_mod_cast hprevious
  have hcurrentTop :
        (target.representationAlphaValue c (i.current hiCurrent) :
            WithTop ℚ) ≤
          (source.representationAlphaValue c (i.current hiCurrent) :
            WithTop ℚ) := by
      exact_mod_cast hcurrent
  have hadjusted : target.centralAdjustedAlpha c i ≤
        source.centralAdjustedAlpha c i := by
      unfold centralAdjustedAlpha
      rw [dif_pos hiCurrent, dif_pos hiCurrent]
      exact add_le_add (le_refl _) hcurrentTop
  have hright :
        ((target.representationAlphaValue c i.previous : ℚ) : WithTop ℚ) +
            target.centralAdjustedAlpha c i ≤
          ((source.representationAlphaValue c i.previous : ℚ) : WithTop ℚ) +
            source.centralAdjustedAlpha c i :=
      add_le_add hpreviousTop hadjusted
  unfold centralAlphaTrigger at htrigger ⊢
  refine ⟨htrigger.1.trans_eq horderCurrent, ?_⟩
  rw [horderPrevious] at htrigger
  exact htrigger.2.trans_le hright

/-- Condition (iii) transfers from the source BONG to the type-I output. -/
theorem centralRepresentationConditions
    [Beli2006AlphaLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefect : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength))
    (hfirst : (a.castLength hlength).order
        (⟨0, by omega⟩ : Fin (N + 3)) =
      c.order (⟨0, by omega⟩ : Fin (N + 3)))
    (hcentral : (a.castLength hlength).CentralRepresentationConditions c) :
    (E.bong.castLength hlength).CentralRepresentationConditions c := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  rw [target.centralRepresentationConditions_iff_forall_alphaTrigger c]
  intro i htrigger
  have hiThree := E.three_le_of_centralAlphaTrigger_target
    a c D horders hlength hfirst i htrigger
  have hsourceTrigger := E.centralAlphaTrigger_source_of_target
    a c D horders hlength hdefect hfirst i htrigger
  have hsourceRepresentation :=
    (source.centralRepresentationConditions_iff_forall_alphaTrigger c).mp
      hcentral i hsourceTrigger
  have hprefix := E.sourcePrefix_represents_targetPrefix
    a D hlength i.val hiThree (by
      have := i.lt_large
      omega)
  exact hsourceRepresentation.trans hprefix

/-- The v2 condition (iii') transfers to the type-I output by Lemma 2.16. -/
theorem centralRepresentationConditionsPrime
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefectSourceTarget :
      (a.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength))
    (hfirst : (a.castLength hlength).order
        (⟨0, by omega⟩ : Fin (N + 3)) =
      c.order (⟨0, by omega⟩ : Fin (N + 3)))
    (horderTarget : (E.bong.castLength hlength).RepresentationOrderCondition
      c le_rfl)
    (hdefectTarget :
      (E.bong.castLength hlength).RepresentationDefectCondition c)
    (hcentralSource :
      (a.castLength hlength).CentralRepresentationConditions c) :
    (E.bong.castLength hlength).CentralRepresentationConditionsPrime c := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  let target := E.bong.castLength hlength
  have hcentralTarget : target.CentralRepresentationConditions c :=
    E.centralRepresentationConditions (K := K) (V := V) (U := U)
      a c D horders hlength hdefectSourceTarget hfirst hcentralSource
  have htriggers := target.beli2019Lemma216
    (sourceLaws := sourceLaws) (targetLaws := targetLaws)
    c le_rfl horderTarget hdefectTarget
  exact (target.centralRepresentationConditions_iff_prime c htriggers).mp
    hcentralTarget

/-- The numerical trigger in condition (iv) for the type-I output implies
the same trigger for the source BONG. -/
theorem longRepresentationTrigger_source_of_target
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (i : LongRepresentationIndex (N + 3) (N + 3))
    (htrigger :
      (E.bong.castLength hlength).longRepresentationTrigger c i) :
    (a.castLength hlength).longRepresentationTrigger c i := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  have hcurrent : target.order
      (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin (N + 3)) =
    source.order
      (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin (N + 3)) :=
    E.order_castLength_eq_source_of_two_le
      a D horders hlength
        (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin (N + 3)) (by
          change 2 ≤ i.val
          have := i.one_lt
          omega)
  have hnext : target.order
      (⟨i.val + 1, i.succ_lt_large⟩ : Fin (N + 3)) =
    source.order (⟨i.val + 1, i.succ_lt_large⟩ : Fin (N + 3)) :=
    E.order_castLength_eq_source_of_two_le
      a D horders hlength
        (⟨i.val + 1, i.succ_lt_large⟩ : Fin (N + 3)) (by
          change 2 ≤ i.val + 1
          have := i.one_lt
          omega)
  unfold longRepresentationTrigger at htrigger ⊢
  rw [hcurrent, hnext] at htrigger
  exact htrigger

/-- Condition (iv) transfers from the source BONG to the type-I output. -/
theorem longRepresentationConditions
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hlong : (a.castLength hlength).LongRepresentationConditions c) :
    (E.bong.castLength hlength).LongRepresentationConditions c := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  rw [target.longRepresentationConditions_iff_forall_generalTrigger c]
  intro i htrigger
  have hsourceTrigger := E.longRepresentationTrigger_source_of_target
    a c D horders hlength i htrigger
  have hsourceRepresentation :=
    (source.longRepresentationConditions_iff_forall_generalTrigger c).mp
      hlong i hsourceTrigger
  have hprefix := E.sourcePrefix_represents_targetPrefix
    a D hlength (i.val + 1) (by
      have := i.one_lt
      omega) (by
        have := i.succ_lt_large
        omega)
  exact hsourceRepresentation.trans hprefix

/-- The two scalar inequalities in the type-I claim of Lemma 9.12. -/
noncomputable def TypeIScalarConditions
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (hlength : 3 + N = N + 3) : Prop :=
  ((β₁ : ℚ) : WithTop ℚ) ≤
      (a.castLength hlength).truncatedPrefixDefect c (-1) 3 1 ∧
    ∀ i : RepresentationIndex (N + 3) (N + 3), 2 ≤ i.val →
      ((E.bong.castLength hlength).representationAlphaValue c i :
          WithTop ℚ) ≤
        (((((E.bong.castLength hlength).order
              ⟨i.val, i.lt_large⟩ -
            (E.bong.castLength hlength).order
              (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
          (β₁ : ℚ) : ℚ) : WithTop ℚ)

/-- The Type-I scalar conditions are exactly condition (ii). -/
theorem representationDefectCondition_iff_typeIScalarConditions
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefectSourceTarget :
      (a.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength))
    (hdefectSource :
      (a.castLength hlength).RepresentationDefectCondition c)
    (hfirst : (a.castLength hlength).order
        (⟨0, by omega⟩ : Fin (N + 3)) =
      c.order (⟨0, by omega⟩ : Fin (N + 3)))
    (hN : 0 < N) :
    (E.bong.castLength hlength).RepresentationDefectCondition c ↔
      E.TypeIScalarConditions a c D hlength := by
  simpa only [TypeIScalarConditions] using
    E.representationDefectCondition_iff_scalar
      a c D horders hlength hdefectSourceTarget hdefectSource
        hfirst hN

/-- The complete type-I claim: conditions (i), (iii'), and (iv) are
unconditional, while all four v2 conditions are equivalent to the two
displayed scalar inequalities. -/
theorem representationConditionsPrime_iff_typeIScalarConditions
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefectSourceTarget :
      (a.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength))
    (hsource : RepresentationConditions (a.castLength hlength) c le_rfl)
    (hfirst : (a.castLength hlength).order
        (⟨0, by omega⟩ : Fin (N + 3)) =
      c.order (⟨0, by omega⟩ : Fin (N + 3)))
    (horderTarget :
      (E.bong.castLength hlength).RepresentationOrderCondition c le_rfl)
    (hN : 0 < N) :
    RepresentationConditionsPrime (E.bong.castLength hlength) c le_rfl ↔
      E.TypeIScalarConditions a c D hlength := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  let target := E.bong.castLength hlength
  have hdefectEquiv := E.representationDefectCondition_iff_typeIScalarConditions
    a c D horders hlength hdefectSourceTarget hsource.defectCondition
      hfirst hN
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

end Beli2019Lemma910Data

end BONG.GoodBONG

end Bong
