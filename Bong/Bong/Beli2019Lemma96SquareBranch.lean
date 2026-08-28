/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma219
import Bong.Bong.DiagonalTernaryRepresentationObstruction

/-!
# Beli (2019), Lemma 9.6: reduction of the ordinary square branch

If `-a_(1,3)b_1` is a square, Lemma 2.19 rules out the strict inequality
`R_4 > R_1 + 2e`: the represented source line together with the signed
determinant square class would make the first ternary target prefix
isotropic.  Consequently the lower bound already obtained from P5 is an
equality.  This is the boundary case in which the paper performs its
rank-four `Delta` scaling.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

/-- In the ordinary square-class branch of Lemma 9.6, the fourth target
order is forced to be the dyadic endpoint `R_1 + 2e`. -/
theorem beli2019Lemma96_fourthOrder_eq_of_rawSquare
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hconditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (hfirstThirdSource :
      a.order (0 : Fin (N + 4)) = a.order (2 : Fin (N + 4)) ∧
      a.order (0 : Fin (N + 4)) = b.order (0 : Fin (N + 4)))
    (hdefect : a.Beli2019Lemma96DefectBound b)
    (hanisotropic : a.Lemma814FirstThreeAnisotropic)
    (hrawSquare :
      IsSquare ((-1) * a.prefixProduct 3 * b.prefixProduct 1)) :
    a.order (3 : Fin (N + 4)) =
      a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) := by
  have hinitial := a.beli2019Lemma96_initialOrderConsequences
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    b (by omega) hfirstThirdSource hdefect
  apply le_antisymm
  · by_contra hnot
    have hstrict :
        b.order (0 : Fin (N + 4)) +
              2 * (ramificationIndex K : Int) <
          a.order (3 : Fin (N + 4)) := by
      rw [← hfirstThirdSource.2]
      exact lt_of_not_ge hnot
    have hrep := a.beli2019Lemma219_unaryTernary
      (sourceLaws := targetLaws) (targetLaws := sourceLaws)
      b hconditions
      (hfirstThirdSource.1.symm.trans hfirstThirdSource.2)
      hstrict hdefect
    let head : Fin 3 → Kˣ := a.prefixValueUnits 3 (by omega)
    let source : Kˣ := b.valueUnit (0 : Fin (N + 4))
    have hbValues : b.prefixValues 1 (by omega) =
        (fun _ : Fin 1 ↦ (source : K)) := by
      funext i
      rw [Fin.eq_zero i]
      rfl
    have haValues : a.prefixValues 3 (by omega) =
        diagonalUnitCoefficients head := by
      exact (a.diagonalUnitCoefficients_prefixValueUnits 3 (by omega)).symm
    have hrep' : DiagonalRepresents
        (fun _ : Fin 1 ↦ (source : K))
        (diagonalUnitCoefficients head) := by
      simpa only [← hbValues, ← haValues] using hrep
    have hheadDeterminant : diagonalUnitDeterminant head =
        a.prefixProduct 3 := by
      exact a.diagonalUnitDeterminant_prefixValueUnits 3 (by omega)
    have hbProduct : b.prefixProduct 1 = source := by
      change b.toBONG.prefixProduct 1 = b.toBONG.valueUnit 0
      rw [b.toBONG.prefixProduct_succ 0 (by omega),
        b.toBONG.prefixProduct_zero, one_mul]
      congr 1
    have hsquare : IsSquare
        ((-1 : Kˣ) * diagonalUnitDeterminant head * source) := by
      rw [hheadDeterminant, ← hbProduct]
      exact hrawSquare
    have hisotropic : DiagonalIsotropic
        (diagonalUnitCoefficients head) :=
      DyadicTernaryRepresentationObstructionLaws.isotropic_of_represents_and_signedDeterminantSquare
        (K := K) head source hrep' hsquare
    have hisotropic' : DiagonalIsotropic
        (a.prefixValues 3 (by omega)) := by
      rwa [haValues]
    rcases hisotropic' with ⟨x, hx, hzero⟩
    exact hx (hanisotropic x hzero)
  · exact hinitial.targetFourthOrder_ge

end BONG.GoodBONG

end Bong
