/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicPublishedTestingSet
import Bong.Bong.He2022ClassicSectionFour

/-!
# He (2024), the published testing lattices as representation conditions

This file is the semantic bridge needed in Section 7.  The entries of the
finite table in Definition 2.6 are actual bundled lattices, while Sections 4
and 5 use Beli's good-BONG representation conditions.  We attach the exact
good BONG to every table entry and prove that an integral representation of
that entry implies the revised conditions of Theorem 2.5.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {L : Lattice K V}
  {r : QuadraticSpace K W} {M : Lattice K W}

namespace BONG.GoodBONG

/-- An actual integral representation implies the revised four BONG
conditions.  This is the forward half of Theorem 2.5 followed by Beli's
Lemma 2.16; unlike a condition-only test, it retains the ambient-space
representation supplied by the lattice map. -/
theorem representationConditionsPrime_of_represents
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (hRank : n <= m)
    (hrep : Lattice.Represents q r L M) :
    RepresentationConditionsPrime a b hRank := by
  have horiginal :=
    (a.he2022ClassicTheorem25 hRank hrep.ambient b).1 hrep
  let sourceLaws : Beli2006AlphaLaws.{u, v} K :=
    beliUniversalAlphaLaws
  let targetLaws : Beli2006AlphaLaws.{u, w} K :=
    beliUniversalAlphaLaws
  have htrigger := a.beli2019Lemma216
    (sourceLaws := sourceLaws) (targetLaws := targetLaws)
    b hRank horiginal.orderCondition horiginal.defectCondition
  exact (representationConditions_iff_prime a b hRank htrigger).1
    horiginal

end BONG.GoodBONG

namespace HeClassicPublishedEvenTestingIndex

private theorem unitRepresentative_order_zero {I : Type u} [Fintype I]
    (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) (i : I) :
    ordUnit K (U i) = 0 :=
  (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i)

private theorem unitUniformizerParameter_order_one
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) (i : I) :
    ordUnit K (U i * uniformizerPowerUnit K (1 : Int)) = 1 := by
  rw [ordUnit_mul, unitRepresentative_order_zero U hU i,
    ordUnit_uniformizerPowerUnit]
  norm_num

/-- The exact good BONG on an even-rank entry of `C_e^n`. -/
noncomputable def goodBONG {I : Type u} [Fintype I]
    (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat)
    (i : HeClassicPublishedEvenTestingIndex (K := K) U
      (ramificationIndex K)) :
    let X := model (K := K) U hU pairs i
    @BONG.GoodBONG K _ _ _ _ _ X.Carrier X.addCommGroup X.module
      X.form X.lattice (2 * pairs + 2) := by
  rcases i with h | j
  · exact heClassicEvenHGoodBONG (K := K) pairs
      (HeClassicExceptionalIndex.parameter (K := K) h)
      (HeClassicExceptionalIndex.parameter_class (K := K) h)
      (HeClassicExceptionalIndex.parameter_order (K := K) h)
  · rcases j with j | i
    · rcases j with ⟨j, column⟩
      cases column
      · exact heClassicEvenC1GoodBONG (K := K) pairs (U j)
          (by
            rw [unitRepresentative_order_zero U hU j])
      · exact heClassicEvenC2GoodBONG (K := K) pairs (U j)
          (heClassicDefectOneSharp (K := K) (U j) j.property)
          (by
            rw [unitRepresentative_order_zero U hU j])
          (heClassicDefectOneSharp_order (U j) j.property)
    · rcases i with ⟨i, column⟩
      let c := U i * uniformizerPowerUnit K (1 : Int)
      let delta :=
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
      have hc : 0 <= ordUnit K c := by
        rw [show ordUnit K c = 1 from
          unitUniformizerParameter_order_one U hU i]
        omega
      have hdelta : ordUnit K delta = 0 :=
        (isValuationUnit_iff_ordUnit_eq_zero K _).1
          ((inferInstance : DyadicDiscriminantClassLaws K).discriminant_isValuationUnit)
      cases column
      · exact heClassicEvenC1GoodBONG (K := K) pairs c hc
      · exact heClassicEvenC2GoodBONG (K := K) pairs c delta hc hdelta

/-- A represented even table entry satisfies all four revised conditions
with its literal good BONG. -/
theorem primeConditions_of_represents_model
    {I : Type u} [Fintype I]
    (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat)
    (i : HeClassicPublishedEvenTestingIndex (K := K) U
      (ramificationIndex K))
    {m : Nat} (a : BONG.GoodBONG q L (m + 1))
    (hRank : 2 * pairs + 1 <= m)
    (hrep :
      let X := model (K := K) U hU pairs i
      @Lattice.Represents K _ _ _ _ _ V _ _ X.Carrier X.addCommGroup
        X.module q X.form L X.lattice) :
    let X := model (K := K) U hU pairs i
    let b := goodBONG (K := K) U hU pairs i
    @RepresentationConditionsPrime K _ _ _ _ _ V _ _ X.Carrier
      X.addCommGroup X.module q X.form L X.lattice m (2 * pairs + 1)
      a b hRank := by
  let X := model (K := K) U hU pairs i
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  change RepresentationConditionsPrime a
    (goodBONG (K := K) U hU pairs i) hRank
  exact a.representationConditionsPrime_of_represents
    (goodBONG (K := K) U hU pairs i) hRank hrep

end HeClassicPublishedEvenTestingIndex

namespace HeClassicPublishedOddTestingIndex

private theorem unitRepresentative_order_zero {I : Type u} [Fintype I]
    (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) (i : I) :
    ordUnit K (U i) = 0 :=
  (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i)

private theorem unitUniformizerParameter_order_one
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) (i : I) :
    ordUnit K (U i * uniformizerPowerUnit K (1 : Int)) = 1 := by
  rw [ordUnit_mul, unitRepresentative_order_zero U hU i,
    ordUnit_uniformizerPowerUnit]
  norm_num

/-- The exact good BONG on an odd-rank entry of `C_e^n`. -/
noncomputable def goodBONG {I : Type u} [Fintype I]
    (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) (pairs : Nat)
    (i : HeClassicPublishedOddTestingIndex I) :
    let X := model (K := K) U hU omegaData pairs i
    @BONG.GoodBONG K _ _ _ _ _ X.Carrier X.addCommGroup X.module
      X.form X.lattice (2 * pairs + 3) := by
  rcases i with ⟨⟨i, parity⟩, column⟩
  cases parity <;> cases column
  · exact heClassicOddC1GoodBONG (K := K) pairs (U i)
      (by
        rw [unitRepresentative_order_zero U hU i])
  · exact heClassicOddC2EvenGoodBONG (K := K) pairs (U i)
      omegaData.omega omegaData.omegaSharp
      (unitRepresentative_order_zero U hU i)
      omegaData.omega_order omegaData.omegaSharp_order
  · let c := U i * uniformizerPowerUnit K (1 : Int)
    exact heClassicOddC1GoodBONG (K := K) pairs c
      (by
        rw [show ordUnit K c = 1 from
          unitUniformizerParameter_order_one U hU i]
        omega)
  · let c := U i * uniformizerPowerUnit K (1 : Int)
    exact heClassicOddC2OddGoodBONG (K := K) pairs c
      (by
        rw [show ordUnit K c = 1 from
          unitUniformizerParameter_order_one U hU i]
        omega)

/-- A represented odd table entry satisfies all four revised conditions
with its literal good BONG. -/
theorem primeConditions_of_represents_model
    {I : Type u} [Fintype I]
    (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) (pairs : Nat)
    (i : HeClassicPublishedOddTestingIndex I)
    {m : Nat} (a : BONG.GoodBONG q L (m + 1))
    (hRank : 2 * pairs + 2 <= m)
    (hrep :
      let X := model (K := K) U hU omegaData pairs i
      @Lattice.Represents K _ _ _ _ _ V _ _ X.Carrier X.addCommGroup
        X.module q X.form L X.lattice) :
    let X := model (K := K) U hU omegaData pairs i
    let b := goodBONG (K := K) U hU omegaData pairs i
    @RepresentationConditionsPrime K _ _ _ _ _ V _ _ X.Carrier
      X.addCommGroup X.module q X.form L X.lattice m (2 * pairs + 2)
      a b hRank := by
  let X := model (K := K) U hU omegaData pairs i
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  change RepresentationConditionsPrime a
    (goodBONG (K := K) U hU omegaData pairs i) hRank
  exact a.representationConditionsPrime_of_represents
    (goodBONG (K := K) U hU omegaData pairs i) hRank hrep

end HeClassicPublishedOddTestingIndex

end Bong
