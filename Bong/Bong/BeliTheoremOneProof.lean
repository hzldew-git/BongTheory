/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliTheoremOneTernaryProof
import Bong.Bong.BeliLemma66Proof
import Bong.Bong.BeliTheoremOneReverse

/-!
# Beli (2003), Theorem 1, unconditional entry point

The forward ternary calculation and the Section 6 reverse induction are
proved in separate modules.  This file assembles their concrete law packages
and exposes the paper theorem without any project-specific law parameter.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG

/-- Beli (2003), Theorem 1, in subgroup form, with exactly the mathematical
hypotheses of the paper-level BONG statement. -/
theorem beliTheoremOne_proved (b : BONG V q L (n + 3))
    (hA : b.HasPropertyA) :
    Lattice.spinorNormImageSubgroup (q := q) (L := L) =
      b.theoremOneRHS := by
  letI : BONGStructuralLaws.{u, v} K := bongStructuralLawsProved K
  letI : BeliLemma47Laws.{u, v} K := beliLemma47LawsProved K
  letI : BONGReverseDualLaws.{u, v} K :=
    BONGStructuralLaws.toBONGReverseDualLaws
  letI : BeliLemma49Laws.{u, v} K :=
    BONG.beliLemma49LawsOfReverseDual
  letI : BinarySpinorLocalLaws.{u, v} K :=
    binarySpinorLocalLawsProved
  letI : BeliLemma66Laws.{u, v} K := beliLemma66LawsProved
  letI : BeliLemma67Laws.{u, v} K := beliLemma67LawsProved
  letI : BeliLemma411Laws.{u, v} K := beliLemma411LawsProved
  letI : BeliTheoremOneTernaryLaws.{u, v} K :=
    beliTheoremOneTernaryLawsProved
  exact b.beliTheoremOne hA

/-- Beli (2003), Theorem 1, in the paper's set-valued notation, without law
parameters. -/
theorem beliTheoremOne_set_proved (b : BONG V q L (n + 3))
    (hA : b.HasPropertyA) :
    Lattice.spinorNormImage (q := q) (L := L) =
      (b.theoremOneRHS : Set (SquareClass K)) := by
  rw [← Lattice.coe_spinorNormImageSubgroup, b.beliTheoremOne_proved hA]

end BONG

end Bong
