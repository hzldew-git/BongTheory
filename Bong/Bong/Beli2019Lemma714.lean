/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714TypeIIClosure

/-!
# Beli (2019), Lemma 7.14

This module is the paper-facing closure of Lemma 7.14.  Part (i) records the
alternating order plateau whenever `s ≥ 4`.  Part (ii) uses the exhaustive and
disjoint type-I/type-II split and realizes the corresponding displayed value
sequence on the literal lattice of non-norm generators.  Both realizations
include the boundary `s = 2`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The two mutually exclusive realizations in Lemma 7.14(ii). -/
inductive Beli2019Lemma714Realization
    [DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hnorm : Lattice.normIdeal q L = Lattice.powerIdeal (K := K) R)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.powerIdeal (K := K)
        (R - ramificationIndex K + 1))
    (ε η : Kˣ) : Prop where
  | typeI
      (hI : Lemma714IsTypeI b R s)
      (result : GoodBONG q
        (Lattice.nonNormGeneratorLattice R hnorm hscale) (n + 3))
      (values : ∀ i, result.valueUnit i =
        lemma714TypeITargetValues b s D.two_le D.le_rank i) :
      Beli2019Lemma714Realization b R s D hnorm hscale ε η
  | typeII
      (hII : Lemma714IsTypeII b R s)
      (result : GoodBONG q
        (Lattice.nonNormGeneratorLattice R hnorm hscale) (n + 3))
      (values : ∀ i, result.valueUnit i =
        lemma714TypeIITargetValues b s D.two_le
          (Classical.choose hII) ε η i) :
      Beli2019Lemma714Realization b R s D hnorm hscale ε η

/-- The complete paper-facing conclusion of Lemma 7.14. -/
structure Beli2019Lemma714Conclusion
    [DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hnorm : Lattice.normIdeal q L = Lattice.powerIdeal (K := K) R)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.powerIdeal (K := K)
        (R - ramificationIndex K + 1))
    (ε η : Kˣ) : Prop where
  plateau : 4 ≤ s →
    Lemma714PlateauConsequences b R s D.le_rank
  realization :
    Beli2019Lemma714Realization b R s D hnorm hscale ε η

variable [laws : DyadicDiscriminantClassLaws K]
variable [QuadraticDefectLaws K]
variable [DyadicUnramifiedNormLaws K]
variable [HilbertSymbolLaws K]
variable [DyadicDiagonalClassificationLaws K]
variable [BONGStructuralLaws.{u, u} K]
variable [Beli2009WeightIdealData.{u, u} K]
variable [Beli2019UnaryBinaryJordanLaws.{u} K]
variable [Beli2009JordanWeightOrderLaws.{u, u} K]
variable [Beli2006AlphaLaws.{u, u} K]
variable [modelLemma43 : BeliLemma43ConstructionLaws.{u, u} K]
variable [modelSectionTwo : Beli2006SectionTwoLaws.{u, u} K]
variable [GoodBONGClassificationLaws.{u, u, u} K]
variable [ambientLemma43 : BeliLemma43ConstructionLaws.{u, v} K]
variable [ambientSectionTwo : Beli2006SectionTwoLaws.{u, v} K]
variable [BONGReverseDualLaws.{u, v} K]
variable [BeliCorollary44Laws.{u, v} K]

/-- Beli (2019), Lemma 7.14, including both alternatives of part (ii). -/
theorem beli2019Lemma714
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hfirst : b.order ⟨0, by omega⟩ = R)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (S : TwoBlockSplitWitness b.toBONG 2 (by omega))
    (hnorm : Lattice.normIdeal q L = Lattice.powerIdeal (K := K) R)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.powerIdeal (K := K)
        (R - ramificationIndex K + 1))
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
    Beli2019Lemma714Conclusion b R s D hnorm hscale ε η := by
  refine {
    plateau := ?_
    realization := ?_ }
  · intro hsFour
    exact b.beli2019Lemma714_i R s D.toLemma714MinimalityData hsFour hthird
  · rcases b.beli2019Lemma714_type_dichotomy R s
        D.toLemma714MinimalityData hthird with hI | hII
    · have hdiscriminantI : b.toBONG.adjacentUnitSquareClass
          (0 : Fin (n + 3)) (by simp) = unitSquareClass K
            (negativeQuarterUnit K * laws.discriminantUnit) := by
        simpa only [lemma712DiscriminantParameter] using hdiscriminant
      rcases b.exists_lemma714_typeI_nonNormGoodBONG R s D hfirst hsecond
          hthird hI S hnorm hscale hdiscriminantI with ⟨result, hvalues⟩
      exact Beli2019Lemma714Realization.typeI hI result hvalues
    · rcases b.exists_lemma714_typeII_nonNormGoodBONG
          (modelLemma43 := modelLemma43)
          (modelSectionTwo := modelSectionTwo)
          (ambientLemma43 := ambientLemma43)
          (ambientSectionTwo := ambientSectionTwo)
          R s D hfirst hsecond hthird hII S hnorm hscale hdiscriminant ε η
            hεUnit hηUnit hεDefect hηDefect hhilbert with ⟨result, hvalues⟩
      exact Beli2019Lemma714Realization.typeII hII result hvalues

end BONG.GoodBONG

end Bong
