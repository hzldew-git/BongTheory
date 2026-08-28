/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Corollary210
import Bong.Bong.Beli2019Lemma214Current
import Bong.Bong.DiagonalDeterminantExtension
import Bong.Bong.GoodBONGPrefixValues

/-!
# Beli (2019), Lemma 2.19: the gap-one case

This is the `l - j = 1` case of Lemma 2.19.  Corollary 2.10 first shows that
the two prefixes of length `i + 1` have the same determinant square class and
that `A_(i+1) ≠ A'_(i+1)`.  Lemma 2.14 then activates condition (iii), which
represents the source prefix of length `i` by the target prefix of length
`i + 1`.  The determinant line uniquely completes that representation.
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

/-- Beli (2019), Lemma 2.19 in the same-length, gap-one form used in
Section 7. -/
theorem beli2019Lemma219_gapOne
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [QuadraticDefectLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hconditions : RepresentationConditions a b le_rfl)
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (hstrict :
      b.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩ +
          2 * (ramificationIndex K : Int) <
        a.order ⟨i.val + 1, i.succ_lt_large⟩) :
    DiagonalRepresents
      (b.prefixValues (i.val + 1) (by
        have := i.succ_lt_large
        omega))
      (a.prefixValues (i.val + 1) (by
        have := i.succ_lt_large
        omega)) := by
  let p : RepresentationIndex (n + 1) (n + 1) :=
    { val := i.val + 1
      pos := by omega
      lt_large := i.succ_lt_large
      le_small := by
        have := i.succ_lt_large
        omega }
  let j : CentralRepresentationIndex (n + 1) (n + 1) :=
    { val := i.val + 1
      one_lt := by
        have := i.one_lt
        omega
      lt_large := i.succ_lt_large
      le_small_succ := by
        have := i.succ_lt_large
        omega }
  have hpOne : 1 < p.val := by
    dsimp only [p]
    have := i.one_lt
    omega
  have hstrictP :
      b.order ⟨p.val - 1, by have := p.le_small; omega⟩ +
          2 * (ramificationIndex K : Int) <
        a.order ⟨p.val, p.lt_large⟩ := by
    simpa only [p, Nat.add_sub_cancel] using hstrict
  have hsquareRaw := a.beli2019Corollary210_complete
    (sourceLaws := alphaV) (targetLaws := alphaW)
    b hconditions.orderCondition hconditions.defectCondition
    p hpOne hstrictP
  have hneRaw := a.beli2019Corollary210_alpha_ne_prime_complete
    (sourceLaws := alphaV) (targetLaws := alphaW)
    b hconditions.orderCondition hconditions.defectCondition
    p hpOne hstrictP
  have hjSmall : j.val ≤ n + 1 := by
    dsimp only [j]
    have := i.succ_lt_large
    omega
  have hne :
      a.representationAlpha b (j.current hjSmall) ≠
        a.representationAlphaPrime b (j.current hjSmall) := by
    simpa only [p, j, CentralRepresentationIndex.current] using hneRaw
  have htrigger := a.centralAlphaTrigger_of_current_alpha_ne_prime
    (b := b) le_rfl hconditions.orderCondition hconditions.defectCondition
    j hjSmall hne
  have hcentral := hconditions.centralRepresentations j htrigger
  have hcentral' : DiagonalRepresents
      (b.prefixValues i.val (by
        have := i.succ_lt_large
        omega))
      (a.prefixValues (i.val + 1) (by
        have := i.succ_lt_large
        omega)) := by
    simpa [j] using hcentral
  let source := b.prefixValueUnits (i.val + 1) (by
    have := i.succ_lt_large
    omega)
  let base := a.prefixValueUnits (i.val + 1) (by
    have := i.succ_lt_large
    omega)
  have hsourcePrefix : diagonalUnitPrefix source =
      b.prefixValueUnits i.val (by
        have := i.succ_lt_large
        omega) := by
    simpa only [source] using
      b.diagonalUnitPrefix_prefixValueUnits i.val (by
        have := i.succ_lt_large
        omega)
  have hprefix : DiagonalRepresents
      (diagonalUnitCoefficients (diagonalUnitPrefix source))
      (diagonalUnitCoefficients base) := by
    rw [hsourcePrefix]
    simpa only [base, diagonalUnitCoefficients_prefixValueUnits] using
      hcentral'
  have hsquare : IsSquare
      (diagonalUnitDeterminant source * diagonalUnitDeterminant base) := by
    simpa only [source, base, p,
      diagonalUnitDeterminant_prefixValueUnits, mul_comm] using hsquareRaw
  have hcompleted := diagonalRepresents_of_prefix_of_determinant_square
    source base hprefix hsquare
  simpa only [source, base,
    diagonalUnitCoefficients_prefixValueUnits] using hcompleted

end BONG.GoodBONG

end Bong
