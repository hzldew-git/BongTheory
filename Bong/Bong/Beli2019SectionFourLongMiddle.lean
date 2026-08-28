/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Corollary217
import Bong.Bong.Beli2019RepresentationTransitivity
import Bong.Bong.DiagonalCodimensionTwoRepresentation

/-!
# Beli (2019), Section 4(iv): the middle branch

This file isolates the geometric assembly in the remaining branch of
condition (iv).  Once the two strict mixed-defect estimates in Beli's proof
are available, Corollary 2.17 gives the two adjacent central representations,
which compose through the middle prefix of length `i`.

The complementary nonsquare determinant class is independent of the case
analysis and follows directly from the local codimension-two theorem.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  {L M N : Lattice K V} {n : Nat}

/-- Outside the exceptional negative-square determinant class, the desired
codimension-two representation is automatic. -/
theorem sectionFourLongCertificate_of_not_negative_determinant_square
    [DyadicDiagonalCodimensionTwoLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (hnonsquare : ¬ IsSquare
      (-a.prefixProduct (i.val + 1) * c.prefixProduct (i.val - 1))) :
    LongRepresentationCertificate a b c i := by
  let source := c.prefixValueUnits (i.val - 1) (by
    have := i.succ_lt_large
    omega)
  let target := a.prefixValueUnits (i.val + 1) (by
    have := i.succ_lt_large
    omega)
  have hdet : ¬ IsSquare
      (-diagonalUnitDeterminant target *
        diagonalUnitDeterminant source) := by
    simpa only [source, target,
      diagonalUnitDeterminant_prefixValueUnits] using hnonsquare
  have hrep := diagonalRepresents_of_not_negative_determinant_square
    source target (show i.val + 1 = (i.val - 1) + 2 by
      have := i.one_lt
      omega) hdet
  exact LongRepresentationCertificate.direct (by
    simpa only [source, target,
      diagonalUnitCoefficients_prefixValueUnits] using hrep)

/-- Section 4(iv), middle branch after the two strict defect estimates have
been established.  The first estimate activates `(a,b)` at `i+1`; the second
activates `(b,c)` at `i`; the resulting representations compose through the
middle prefix of length `i`. -/
theorem sectionFourLongCertificate_throughCurrent_of_defectBounds
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (hleft : b.order ⟨i.val - 1, by
        have := i.succ_lt_large
        omega⟩ < a.order ⟨i.val + 1, i.succ_lt_large⟩)
    (hright : c.order ⟨i.val - 2, by
        have := i.succ_lt_large
        omega⟩ < b.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩)
    (hdefectAB :
      (((2 * (ramificationIndex K : ℚ) +
          (b.order ⟨i.val - 1, by
            have := i.succ_lt_large
            omega⟩ : ℚ) -
          (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ) : ℚ)) :
          WithTop ℚ) <
        a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1))
    (hdefectBC :
      (((2 * (ramificationIndex K : ℚ) +
          (c.order ⟨i.val - 2, by
            have := i.succ_lt_large
            omega⟩ : ℚ) -
          (b.order ⟨i.val, by
            have := i.succ_lt_large
            omega⟩ : ℚ) : ℚ)) :
          WithTop ℚ) <
        b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1)) :
    LongRepresentationCertificate a b c i := by
  let j : CentralRepresentationIndex (n + 1) (n + 1) :=
    { val := i.val + 1
      one_lt := by
        have := i.one_lt
        omega
      lt_large := i.succ_lt_large
      le_small_succ := by
        have := i.succ_lt_large
        omega }
  have hpreviousIndex : i.val + 1 - 2 = i.val - 1 := by
    have := i.one_lt
    omega
  have htriggerAB := a.beli2019Corollary217_of_previousDefect
    (sourceLaws := inferInstance) (targetLaws := inferInstance)
    b le_rfl hab.orderCondition hab.defectCondition j
      (by
        simpa only [j, hpreviousIndex] using hleft)
      (by
        change (((2 * (ramificationIndex K : ℚ) +
            (b.order ⟨j.val - 2, by
              have := j.one_lt
              have := j.le_small_succ
              omega⟩ : ℚ) -
            (a.order ⟨j.val, j.lt_large⟩ : ℚ) : ℚ)) : WithTop ℚ) <
          a.truncatedPrefixDefect b (-1) j.val (j.val - 2)
        simpa only [j, hpreviousIndex] using hdefectAB)
  have hmiddleToTarget := hab.centralRepresentations j htriggerAB
  have htriggerBC := b.beli2019Corollary217_of_currentDefect
    (sourceLaws := inferInstance) (targetLaws := inferInstance)
    c le_rfl hbc.orderCondition hbc.defectCondition
      { val := i.val
        one_lt := i.one_lt
        lt_large := by
          have := i.succ_lt_large
          omega
        le_small_succ := i.le_small_succ }
      hright (by simpa only [centralCurrentDefect] using hdefectBC)
  have hsourceToMiddle := hbc.centralRepresentations
    { val := i.val
      one_lt := i.one_lt
      lt_large := by
        have := i.succ_lt_large
        omega
      le_small_succ := i.le_small_succ }
    htriggerBC
  exact LongRepresentationCertificate.throughCurrent
    (by simpa using hsourceToMiddle)
    (prefixRepresents_cast b a (by
      dsimp only [j]
      omega) rfl hmiddleToTarget)

end BONG.GoodBONG

end Bong
