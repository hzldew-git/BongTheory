/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma718TypeIRealization
import Bong.Bong.Beli2019Lemma718TypeIIRealization
import Bong.Bong.Beli2019Lemma718TypeIIIRealization

/-!
# Beli (2019), Lemma 7.18: assembly of the three realizations

The paper first changes the good BONG of the source lattice into one of the
three displayed normal forms and only then constructs the replacement
lattice.  This file assembles the already constructive replacement theorems
without conflating those two steps.

`Lemma718PreparedSource` is deliberately not a typeclass and has no default
inhabitant.  Its constructive existence from Lemma 7.17 is proved separately
in `Beli2019Lemma718Preparation`; keeping the predicate explicit prevents the
normalization step from being hidden by instance search.  Once it is supplied,
`exists_lemma718Realization` returns a literal sublattice and a good BONG in
the appropriate one of the three normal forms.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- A source BONG after the explicit change of BONG made at the beginning of
the proof of Lemma 7.18.  Each constructor contains exactly one of the three
displayed coefficient lists, together with the corresponding case of Lemma
7.17. -/
inductive Lemma718PreparedSource
    [DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat) : Prop
  | typeI
      (stopping : Lemma717StoppingData a R s)
      (caseProof : Lemma717IsTypeI a R s)
      (sourcePair : ∀ (j : Nat) (hj : 2 * j + 1 < s),
        a.valueUnit ⟨2 * j, by
          have hs := stopping.le_rank
          omega⟩ = lemma718CanonicalHigh (K := K) R ∧
        a.valueUnit ⟨2 * j + 1, by
          have hs := stopping.le_rank
          omega⟩ = lemma718CanonicalLow (K := K) R) :
      Lemma718PreparedSource a R s
  | typeII
      (stopping : Lemma717StoppingData a R s)
      (caseProof : Lemma717IsTypeII a R s)
      (initialFirst : a.valueUnit ⟨0, by omega⟩ =
        lemma718CanonicalHigh (K := K) R)
      (initialSecond : a.valueUnit ⟨1, by omega⟩ =
        -(DyadicDiscriminantClassLaws.discriminantUnit (K := K) *
          uniformizerPowerUnit K
            (R - 2 * (ramificationIndex K : Int))))
      (sourcePair : ∀ (j : Nat) (hjOne : 1 ≤ j)
          (hj : 2 * j + 1 < s),
        a.valueUnit ⟨2 * j, by
          have hs := stopping.le_rank
          omega⟩ = lemma718CanonicalHigh (K := K) R ∧
        a.valueUnit ⟨2 * j + 1, by
          have hs := stopping.le_rank
          omega⟩ = lemma718CanonicalLow (K := K) R) :
      Lemma718PreparedSource a R s
  | typeIII
      (stopping : Lemma717StoppingData a R s)
      (caseProof : Lemma717IsTypeIII a R s)
      (sourcePair : ∀ (j : Nat) (hj : 2 * j + 1 < s),
        a.valueUnit ⟨2 * j, by
          have hs := stopping.le_rank
          omega⟩ = lemma718CanonicalHigh (K := K) R ∧
        a.valueUnit ⟨2 * j + 1, by
          have hs := stopping.le_rank
          omega⟩ = lemma718CanonicalLow (K := K) R) :
      Lemma718PreparedSource a R s

/-- The three possible constructive outputs of Lemma 7.18. -/
inductive Lemma718Realization
    [DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat) :
    Type (max (u + 1) (v + 1))
  | typeI (data : Lemma718TypeIRealization a R s) :
      Lemma718Realization a R s
  | typeII (data : Lemma718TypeIIRealization a R s) :
      Lemma718Realization a R s
  | typeIII (data : Lemma718TypeIIIRealization a R s) :
      Lemma718Realization a R s

/-- Assemble the three constructive branches of Lemma 7.18. -/
theorem exists_lemma718Realization
    [corollary44V : BeliCorollary44Laws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [defect : QuadraticDefectLaws K]
    [hilbert : HilbertSymbolLaws K]
    [diagonal : DyadicDiagonalClassificationLaws K]
    [perfect : PerfectResidueFieldLaws K]
    [structural : BONGStructuralLaws.{u, u} K]
    [weight : Beli2009WeightIdealData.{u, u} K]
    [unaryBinary : Beli2019UnaryBinaryJordanLaws.{u} K]
    [jordanOrder : Beli2009JordanWeightOrderLaws.{u, u} K]
    [alphaBase : Beli2006AlphaLaws.{u, u} K]
    [constructionBase : BeliLemma43ConstructionLaws.{u, u} K]
    [sectionTwoBase : Beli2006SectionTwoLaws.{u, u} K]
    [classification : GoodBONGClassificationLaws.{u, u, u} K]
    [sectionFourV : BONGReverseDualLaws.{u, v} K]
    [constructionV : BeliLemma43ConstructionLaws.{u, v} K]
    [sectionTwoV : Beli2006SectionTwoLaws.{u, v} K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (prepared : Lemma718PreparedSource a R s) :
    Nonempty (Lemma718Realization a R s) := by
  cases prepared with
  | typeI stopping caseProof sourcePair =>
      rcases exists_lemma718TypeIRealization
          a R s stopping caseProof sourcePair with ⟨D⟩
      exact ⟨Lemma718Realization.typeI D⟩
  | typeII stopping caseProof initialFirst initialSecond sourcePair =>
      rcases exists_lemma718TypeIIRealization
          a R s stopping caseProof initialFirst initialSecond sourcePair with ⟨D⟩
      exact ⟨Lemma718Realization.typeII D⟩
  | typeIII stopping caseProof sourcePair =>
      rcases (@exists_lemma718TypeIIIRealization.{u, v}
          K _ _ _ _ _ V _ _ q L n
          corollary44V defect hilbert diagonal perfect structural weight
          unaryBinary jordanOrder alphaBase constructionBase sectionTwoBase
          classification sectionFourV constructionV sectionTwoV
          a R s stopping caseProof sourcePair) with ⟨D⟩
      exact ⟨Lemma718Realization.typeIII D⟩

end BONG.GoodBONG

end Bong
