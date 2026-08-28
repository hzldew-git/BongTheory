/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma219GapOne
import Bong.Bong.Beli2019CanonicalApproximation

/-!
# Beli (2019), Lemma 2.19: the complete gap-one case

The earlier internal form starts two places from the left endpoint.  Section
4(iv) also uses the conclusion for prefixes of length one and two.  The unary
case has an empty codimension-one prefix; all larger prefixes use Corollary
2.10 and Lemma 2.14 exactly as in the internal proof.
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
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Lemma 2.19 for `l - j = 1`, including the left endpoint. -/
theorem beli2019Lemma219_gapOne_complete
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    [QuadraticDefectLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hconditions : RepresentationConditions a b le_rfl)
    (p : RepresentationIndex (n + 1) (n + 1))
    (hstrict :
      b.order ⟨p.val - 1, by
        have := p.le_small
        omega⟩ + 2 * (ramificationIndex K : Int) <
        a.order ⟨p.val, p.lt_large⟩) :
    DiagonalRepresents
      (b.prefixValues p.val p.le_small)
      (a.prefixValues p.val p.lt_large.le) := by
  have hsquareRaw : IsSquare
      (a.prefixProduct p.val * b.prefixProduct p.val) := by
    by_cases hpOne : p.val = 1
    · exact a.beli2019Corollary210_of_not_interior
        (sourceLaws := sourceLaws) (targetLaws := targetLaws)
        b hconditions.defectCondition p (by omega) hstrict
    · exact a.beli2019Corollary210_complete
        (sourceLaws := sourceLaws) (targetLaws := targetLaws)
        b hconditions.orderCondition hconditions.defectCondition
        p (by have := p.pos; omega) hstrict
  have hprefixRaw : DiagonalRepresents
      (b.prefixValues (p.val - 1) (by
        have := p.le_small
        omega))
      (a.prefixValues p.val p.lt_large.le) := by
    by_cases hpOne : p.val = 1
    · exact DiagonalRepresents.of_source_length_eq_zero
        (b.prefixValues (p.val - 1) (by
          have := p.le_small
          omega))
        (a.prefixValues p.val p.lt_large.le) (by omega)
    · let j : CentralRepresentationIndex (n + 1) (n + 1) :=
        { val := p.val
          one_lt := by
            have := p.pos
            omega
          lt_large := p.lt_large
          le_small_succ := by
            have := p.le_small
            omega }
      have hne := a.beli2019Corollary210_alpha_ne_prime_complete
        (sourceLaws := sourceLaws) (targetLaws := targetLaws)
        b hconditions.orderCondition hconditions.defectCondition
        p (by have := p.pos; omega) hstrict
      have hjSmall : j.val ≤ n + 1 := by
        dsimp only [j]
        exact p.le_small
      have hne' :
          a.representationAlpha b (j.current hjSmall) ≠
            a.representationAlphaPrime b (j.current hjSmall) := by
        simpa only [j, CentralRepresentationIndex.current] using hne
      have htrigger := a.centralAlphaTrigger_of_current_alpha_ne_prime
        b le_rfl hconditions.orderCondition hconditions.defectCondition
        j hjSmall hne'
      simpa only [j] using hconditions.centralRepresentations j htrigger
  let k := p.val - 1
  have hk : k + 1 = p.val := by
    dsimp only [k]
    have := p.pos
    omega
  let source := b.prefixValueUnits (k + 1) (by
    rw [hk]
    exact p.le_small)
  let base := a.prefixValueUnits (k + 1) (by
    rw [hk]
    exact p.lt_large.le)
  have hsourcePrefix : diagonalUnitPrefix source =
      b.prefixValueUnits k (by
        dsimp only [k]
        have := p.le_small
        omega) := by
    simpa only [source] using
      b.diagonalUnitPrefix_prefixValueUnits k (by
        rw [hk]
        exact p.le_small)
  have hprefix : DiagonalRepresents
      (diagonalUnitCoefficients (diagonalUnitPrefix source))
      (diagonalUnitCoefficients base) := by
    rw [hsourcePrefix]
    have hprefixRaw' : DiagonalRepresents
        (b.prefixValues k (by
          dsimp only [k]
          have := p.le_small
          omega))
        (a.prefixValues (k + 1) (by
          rw [hk]
          exact p.lt_large.le)) :=
      prefixRepresents_cast
        (sourceBound' := by
          dsimp only [k]
          have := p.le_small
          omega)
        (targetBound' := by
          rw [hk]
          exact p.lt_large.le)
        b a rfl hk.symm hprefixRaw
    simpa only [base, k,
      diagonalUnitCoefficients_prefixValueUnits] using hprefixRaw'
  have hsquare : IsSquare
      (diagonalUnitDeterminant source * diagonalUnitDeterminant base) := by
    simpa only [source, base, hk,
      diagonalUnitDeterminant_prefixValueUnits, mul_comm] using hsquareRaw
  have hcompleted := diagonalRepresents_of_prefix_of_determinant_square
    source base hprefix hsquare
  have hcompletedRaw : DiagonalRepresents
      (b.prefixValues (k + 1) (by
        rw [hk]
        exact p.le_small))
      (a.prefixValues (k + 1) (by
        rw [hk]
        exact p.lt_large.le)) := by
    simpa only [source, base,
      diagonalUnitCoefficients_prefixValueUnits] using hcompleted
  exact prefixRepresents_cast
    (sourceBound' := p.le_small)
    (targetBound' := p.lt_large.le)
    b a hk hk hcompletedRaw

end BONG.GoodBONG

end Bong
