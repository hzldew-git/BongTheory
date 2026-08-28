/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliTheoremOneProof
import Bong.Bong.BeliTheoremThreeProof

/-!
# Beli (2003), Theorem 3, unconditional entry point

This file assembles the proved local packages used by the necessity and
sufficiency arguments and exposes Theorem 3 without project-specific law
parameters.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {m : Nat}

namespace BONG

/-- Beli (2003), Theorem 3, with exactly the mathematical hypotheses of the
paper-level good-BONG statement. -/
theorem beliTheoremThree_proved (b : BONG V q L m) (hgood : b.IsGood) :
    Lattice.SpinorNormIsUnitBounded q L ↔
      b.SatisfiesTheoremThreeConditions := by
  letI : BONGStructuralLaws.{u, v} K := bongStructuralLawsProved K
  letI : BeliLemma47Laws.{u, v} K := beliLemma47LawsProved K
  letI : BONGReverseDualLaws.{u, v} K :=
    BONGStructuralLaws.toBONGReverseDualLaws
  letI : BeliLemma49Laws.{u, v} K := beliLemma49LawsOfReverseDual
  letI : BinarySpinorLocalLaws.{u, v} K := binarySpinorLocalLawsProved
  letI : BeliLemma66Laws.{u, v} K := beliLemma66LawsProved
  letI : BeliLemma67Laws.{u, v} K := beliLemma67LawsProved
  letI : BeliLemma411Laws.{u, v} K := beliLemma411LawsProved
  letI : BeliTheoremOneTernaryLaws.{u, v} K :=
    beliTheoremOneTernaryLawsProved
  letI : BeliLemma71Laws.{u, v} K := beliLemma71LawsProved
  letI : BeliLemma72Laws K := beliLemma72LawsProved
  letI : BeliLemma73Laws.{u, v} K := beliLemma73LawsOfProof
  letI : BeliTheoremThreeLaws.{u, v} K := beliTheoremThreeLawsProved
  exact b.beliTheoremThree hgood

end BONG

end Bong
