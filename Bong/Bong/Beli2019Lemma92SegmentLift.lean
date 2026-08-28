/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma92BaseEquality
import Bong.Bong.BeliLemmas48To410

/-!
# Beli (2019), Lemma 9.2: lifting the rank-four and rank-five changes

The proof first changes only the initial four or five coefficients.  Beli
(2003), Lemma 4.9(ii), then replaces that good initial segment inside the
original good BONG.  This file implements that reduction, so the remaining
local construction can be carried out at exactly rank four or rank five.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- The initial quaternary segment used in the early alternatives of
Lemma 9.2. -/
noncomputable def lemma92InitialFourSegment
    (a : GoodBONG q L (N + 4)) :
    BONG.SegmentWitness a.toBONG 0 4 (by omega) :=
  a.toBONG.segmentWitness 0 4 (by omega)

/-- The initial quaternary segment as a good BONG of its integral segment
lattice. -/
noncomputable def lemma92InitialFour
    (a : GoodBONG q L (N + 4)) :
    GoodBONG
      (q.restrict a.lemma92InitialFourSegment.carrier
        a.lemma92InitialFourSegment.nondegenerate)
      a.lemma92InitialFourSegment.lattice 4 :=
  a.lemma92InitialFourSegment.toGoodBONG a.good

/-- Local values in the initial quaternary segment are the first four
ambient values. -/
theorem lemma92InitialFour_valueUnit_eq
    (a : GoodBONG q L (N + 4)) (i : Fin 4) :
    a.lemma92InitialFour.valueUnit i =
      a.valueUnit ⟨i.1, by omega⟩ := by
  let w := a.lemma92InitialFourSegment
  change w.bong.valueUnit i = a.toBONG.valueUnit ⟨i.1, by omega⟩
  calc
    w.bong.valueUnit i = a.toBONG.valueUnit (w.sourceIndex i) :=
      w.valueUnit_eq i
    _ = a.toBONG.valueUnit ⟨i.1, by omega⟩ := by
      congr 1
      apply Fin.ext
      simp only [BONG.SegmentWitness.sourceIndex_val]
      omega

/-- The initial quinary segment used in the complementary branch of
Lemma 9.2. -/
noncomputable def lemma92InitialFiveSegment
    (a : GoodBONG q L (N + 5)) :
    BONG.SegmentWitness a.toBONG 0 5 (by omega) :=
  a.toBONG.segmentWitness 0 5 (by omega)

/-- The initial quinary segment as a good BONG. -/
noncomputable def lemma92InitialFive
    (a : GoodBONG q L (N + 5)) :
    GoodBONG
      (q.restrict a.lemma92InitialFiveSegment.carrier
        a.lemma92InitialFiveSegment.nondegenerate)
      a.lemma92InitialFiveSegment.lattice 5 :=
  a.lemma92InitialFiveSegment.toGoodBONG a.good

/-- Local values in the initial quinary segment are the first five ambient
values. -/
theorem lemma92InitialFive_valueUnit_eq
    (a : GoodBONG q L (N + 5)) (i : Fin 5) :
    a.lemma92InitialFive.valueUnit i =
      a.valueUnit ⟨i.1, by omega⟩ := by
  let w := a.lemma92InitialFiveSegment
  change w.bong.valueUnit i = a.toBONG.valueUnit ⟨i.1, by omega⟩
  calc
    w.bong.valueUnit i = a.toBONG.valueUnit (w.sourceIndex i) :=
      w.valueUnit_eq i
    _ = a.toBONG.valueUnit ⟨i.1, by omega⟩ := by
      congr 1
      apply Fin.ext
      simp only [BONG.SegmentWitness.sourceIndex_val]
      omega

namespace Lemma92EarlyScalingData

/-- A successful rank-four change can be inserted into a good BONG of any
larger rank without changing the surrounding lattice. -/
theorem liftInitialFour
    [BeliLemma49Laws.{u, v} K]
    {a : GoodBONG q L (N + 4)} {ε η : Kˣ}
    (D : Lemma92EarlyScalingData a.lemma92InitialFour ε η) :
    Nonempty (Lemma92EarlyScalingData a ε η) := by
  rcases a.toBONG.beliLemma49_ii a.good a.lemma92InitialFourSegment
      D.transformed.toBONG D.transformed.good with ⟨replacement⟩
  let transformed : GoodBONG q L (N + 4) :=
    ⟨replacement.bong, replacement.good⟩
  have hvalue (i : Fin 4) :
      transformed.valueUnit ⟨i.1, by omega⟩ =
        D.transformed.valueUnit i := by
    apply Units.ext
    change replacement.bong.value ⟨i.1, by omega⟩ =
      D.transformed.toBONG.value i
    rw [← replacement.bong.quadratic_ambientVector,
      ← D.transformed.toBONG.quadratic_ambientVector]
    have hinside := replacement.inside_eq i
    have hindex :
        (⟨0 + i.1, by omega⟩ : Fin (N + 4)) =
          ⟨i.1, by omega⟩ := Fin.ext (by simp)
    rw [hindex] at hinside
    exact congrArg q.quadratic hinside
  refine ⟨{
    transformed := transformed
    firstValue_eq := ?_
    secondValue_eq := ?_
    thirdValue_eq := ?_
    fourthValue_eq := ?_
  }⟩
  · exact (hvalue (0 : Fin 4)).trans <|
      D.firstValue_eq.trans (a.lemma92InitialFour_valueUnit_eq 0)
  · exact (hvalue (1 : Fin 4)).trans <|
      D.secondValue_eq.trans <|
        congrArg (ε * ·) (a.lemma92InitialFour_valueUnit_eq 1)
  · exact (hvalue (2 : Fin 4)).trans <|
      D.thirdValue_eq.trans <|
        congrArg (ε * η * ·) (a.lemma92InitialFour_valueUnit_eq 2)
  · exact (hvalue (3 : Fin 4)).trans <|
      D.fourthValue_eq.trans <|
        congrArg (η * ·) (a.lemma92InitialFour_valueUnit_eq 3)

end Lemma92EarlyScalingData

namespace Lemma92LaterScalingData

/-- A successful rank-five change can likewise be inserted into every
higher-rank good BONG. -/
theorem liftInitialFive
    [BeliLemma49Laws.{u, v} K]
    {a : GoodBONG q L (N + 5)} {ε η : Kˣ}
    (D : Lemma92LaterScalingData a.lemma92InitialFive ε η) :
    Nonempty (Lemma92LaterScalingData a ε η) := by
  rcases a.toBONG.beliLemma49_ii a.good a.lemma92InitialFiveSegment
      D.transformed.toBONG D.transformed.good with ⟨replacement⟩
  let transformed : GoodBONG q L (N + 5) :=
    ⟨replacement.bong, replacement.good⟩
  have hvalue (i : Fin 5) :
      transformed.valueUnit ⟨i.1, by omega⟩ =
        D.transformed.valueUnit i := by
    apply Units.ext
    change replacement.bong.value ⟨i.1, by omega⟩ =
      D.transformed.toBONG.value i
    rw [← replacement.bong.quadratic_ambientVector,
      ← D.transformed.toBONG.quadratic_ambientVector]
    have hinside := replacement.inside_eq i
    have hindex :
        (⟨0 + i.1, by omega⟩ : Fin (N + 5)) =
          ⟨i.1, by omega⟩ := Fin.ext (by simp)
    rw [hindex] at hinside
    exact congrArg q.quadratic hinside
  refine ⟨{
    transformed := transformed
    firstValue_eq := ?_
    secondValue_eq := ?_
    thirdValue_eq := ?_
    fourthValue_eq := ?_
    fifthValue_eq := ?_
  }⟩
  · exact (hvalue (0 : Fin 5)).trans <|
      D.firstValue_eq.trans (a.lemma92InitialFive_valueUnit_eq 0)
  · exact (hvalue (1 : Fin 5)).trans <|
      D.secondValue_eq.trans (a.lemma92InitialFive_valueUnit_eq 1)
  · exact (hvalue (2 : Fin 5)).trans <|
      D.thirdValue_eq.trans <|
        congrArg (ε * ·) (a.lemma92InitialFive_valueUnit_eq 2)
  · exact (hvalue (3 : Fin 5)).trans <|
      D.fourthValue_eq.trans <|
        congrArg (ε * η * ·) (a.lemma92InitialFive_valueUnit_eq 3)
  · exact (hvalue (4 : Fin 5)).trans <|
      D.fifthValue_eq.trans <|
        congrArg (η * ·) (a.lemma92InitialFive_valueUnit_eq 4)

end Lemma92LaterScalingData

end BONG.GoodBONG

end Bong
