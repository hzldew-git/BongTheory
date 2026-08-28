/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714
import Bong.Bong.Beli2019Lemma714SpecialLattice

/-!
# Beli (2019), Lemma 7.14 in the equal-first-gap branch

This is the Section-7 form of Lemma 7.14.  Its target is the explicit image
of `pi J perp T`, so the theorem has exactly the hypotheses used in the
paper and does not assume the strict scale bound belonging to Lemma 7.1.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Type-I realization on the unconditional special lattice. -/
theorem exists_lemma714_typeI_specialGoodBONG
    [BeliCorollary44Laws.{u, v} K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hfirst : b.order ⟨0, by omega⟩ = R)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hI : Lemma714IsTypeI b R s)
    (S : TwoBlockSplitWitness b.toBONG 2 (by omega)) :
    ∃ result : GoodBONG q S.lemma714SpecialLattice (n + 3),
      ∀ i, result.valueUnit i =
        lemma714TypeITargetValues b s D.two_le D.le_rank i := by
  rcases b.exists_lemma714_typeI_productGoodBONG R s D hfirst hsecond
      hthird hI S with ⟨productBONG, hproductValues⟩
  let result := productBONG.mapLatticeIsometry
    S.rescaledLeftProductToLemma714SpecialLattice
  refine ⟨result, ?_⟩
  intro i
  calc
    result.valueUnit i = productBONG.valueUnit i := by
      simpa only [result] using
        (GoodBONG.valueUnit_mapLatticeIsometry
          S.rescaledLeftProductToLemma714SpecialLattice productBONG i)
    _ = lemma714TypeITargetValues b s D.two_le D.le_rank i :=
      hproductValues i

/-- Type-II realization on the unconditional special lattice. -/
theorem exists_lemma714_typeII_specialGoodBONG
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [Beli2006AlphaLaws.{u, u} K]
    [modelLemma43 : BeliLemma43ConstructionLaws.{u, u} K]
    [modelSectionTwo : Beli2006SectionTwoLaws.{u, u} K]
    [GoodBONGClassificationLaws.{u, u, u} K]
    [ambientLemma43 : BeliLemma43ConstructionLaws.{u, v} K]
    [ambientSectionTwo : Beli2006SectionTwoLaws.{u, v} K]
    [BONGReverseDualLaws.{u, v} K]
    [BeliCorollary44Laws.{u, v} K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hfirst : b.order ⟨0, by omega⟩ = R)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hII : Lemma714IsTypeII b R s)
    (S : TwoBlockSplitWitness b.toBONG 2 (by omega))
    (hdiscriminant : b.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hεDefect : defectOrder (K := K) ε = (1 : WithTop ℚ))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ))
    (hhilbert : hilbertSymbol K ε η = -1) :
    ∃ result : GoodBONG q S.lemma714SpecialLattice (n + 3),
      ∀ i, result.valueUnit i =
        lemma714TypeIITargetValues b s D.two_le
          (Classical.choose hII) ε η i := by
  have hsFour : s = 2 ∨ 4 ≤ s := by
    have htwo : 2 ≤ s := D.two_le
    rcases D.even with ⟨d, hd⟩
    omega
  let hsCurrent : s < n + 3 := Classical.choose hII
  have hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1 :=
    Classical.choose_spec hII
  rcases b.exists_lemma714_typeII_selectedTailSplit R s D hthird hII S
      hsFour with ⟨U⟩
  rcases exists_lemma714_typeII_targetGoodBONG
      (modelLemma43 := modelLemma43)
      (modelSectionTwo := modelSectionTwo)
      (ambientLemma43 := ambientLemma43)
      (ambientSectionTwo := ambientSectionTwo)
      b R s D hfirst hthird hII S hdiscriminant ε η hεUnit hηUnit
        hεDefect hηDefect hhilbert with
    ⟨N, target, block, hblockValues, htargetValues, htargetVectors⟩
  let productBONG := b.lemma714TypeIIRescaledProductGoodBONG R s D hfirst
    hsecond hthird hsCurrent hcurrent S hsFour U block target htargetVectors
  let result := productBONG.mapLatticeIsometry
    S.rescaledLeftProductToLemma714SpecialLattice
  refine ⟨result, ?_⟩
  intro i
  calc
    result.valueUnit i = productBONG.valueUnit i := by
      simpa only [result] using
        (GoodBONG.valueUnit_mapLatticeIsometry
          S.rescaledLeftProductToLemma714SpecialLattice productBONG i)
    _ = target.valueUnit i := by
      apply Units.ext
      change productBONG.toBONG.value i = target.toBONG.value i
      simpa only [productBONG, lemma714TypeIIRescaledProductGoodBONG,
        GoodBONG.mapLatticeIsometry] using
        BONG.value_mapLatticeIsometry
          (b.lemma714TypeIITargetToRescaledProductIsometry R s D hfirst
            hsecond hthird hsCurrent hcurrent S hsFour U block target
            htargetVectors) target.toBONG i
    _ = lemma714TypeIITargetValues b s D.two_le
        (Classical.choose hII) ε η i := htargetValues i

/-- The two mutually exclusive realizations in the scale-free Section-7
form of Lemma 7.14. -/
inductive Beli2019Lemma714SpecialRealization
    [DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (S : TwoBlockSplitWitness b.toBONG 2 (by omega))
    (ε η : Kˣ) : Prop where
  | typeI
      (hI : Lemma714IsTypeI b R s)
      (result : GoodBONG q S.lemma714SpecialLattice (n + 3))
      (values : ∀ i, result.valueUnit i =
        lemma714TypeITargetValues b s D.two_le D.le_rank i) :
      Beli2019Lemma714SpecialRealization b R s D S ε η
  | typeII
      (hII : Lemma714IsTypeII b R s)
      (result : GoodBONG q S.lemma714SpecialLattice (n + 3))
      (values : ∀ i, result.valueUnit i =
        lemma714TypeIITargetValues b s D.two_le
          (Classical.choose hII) ε η i) :
      Beli2019Lemma714SpecialRealization b R s D S ε η

/-- Complete scale-free conclusion of Lemma 7.14 for Section 7. -/
structure Beli2019Lemma714SpecialConclusion
    [DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (S : TwoBlockSplitWitness b.toBONG 2 (by omega))
    (ε η : Kˣ) : Prop where
  plateau : 4 ≤ s → Lemma714PlateauConsequences b R s D.le_rank
  realization : Beli2019Lemma714SpecialRealization b R s D S ε η

variable [laws : DyadicDiscriminantClassLaws K]
variable [QuadraticDefectLaws K]
variable [DyadicUnramifiedNormLaws K]
variable [HilbertSymbolLaws K]
variable [DyadicDiagonalClassificationLaws K]
variable [BONGStructuralLaws.{u, u} K]
variable [Beli2009WeightIdealData.{u, u} K]
variable [Beli2019UnaryBinaryJordanLaws.{u} K]
variable [Beli2009JordanWeightOrderLaws.{u, u} K]
variable [modelAlpha : Beli2006AlphaLaws.{u, u} K]
variable [modelLemma43 : BeliLemma43ConstructionLaws.{u, u} K]
variable [modelSectionTwo : Beli2006SectionTwoLaws.{u, u} K]
variable [GoodBONGClassificationLaws.{u, u, u} K]
variable [ambientLemma43 : BeliLemma43ConstructionLaws.{u, v} K]
variable [ambientSectionTwo : Beli2006SectionTwoLaws.{u, v} K]
variable [BONGReverseDualLaws.{u, v} K]
variable [BeliCorollary44Laws.{u, v} K]

/-- Beli (2019), Lemma 7.14 with the exact assumptions of the
equal-first-gap branch. -/
theorem beli2019Lemma714Special
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hfirst : b.order ⟨0, by omega⟩ = R)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (S : TwoBlockSplitWitness b.toBONG 2 (by omega))
    (hdiscriminant : b.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hεDefect : defectOrder (K := K) ε = (1 : WithTop ℚ))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ))
    (hhilbert : hilbertSymbol K ε η = -1) :
    Beli2019Lemma714SpecialConclusion b R s D S ε η := by
  refine ⟨?_, ?_⟩
  · intro hsFour
    exact b.beli2019Lemma714_i R s D.toLemma714MinimalityData hsFour hthird
  · rcases b.beli2019Lemma714_type_dichotomy R s
        D.toLemma714MinimalityData hthird with hI | hII
    · rcases b.exists_lemma714_typeI_specialGoodBONG R s D hfirst hsecond
          hthird hI S with ⟨result, hvalues⟩
      exact Beli2019Lemma714SpecialRealization.typeI hI result hvalues
    · rcases b.exists_lemma714_typeII_specialGoodBONG
          (modelLemma43 := modelLemma43)
          (modelSectionTwo := modelSectionTwo)
          (ambientLemma43 := ambientLemma43)
          (ambientSectionTwo := ambientSectionTwo)
          R s D hfirst hsecond
          hthird hII S hdiscriminant ε η hεUnit hηUnit hεDefect hηDefect
            hhilbert with ⟨result, hvalues⟩
      exact Beli2019Lemma714SpecialRealization.typeII hII result hvalues

end BONG.GoodBONG

end Bong
