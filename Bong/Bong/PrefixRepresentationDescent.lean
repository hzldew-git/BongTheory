/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Reflexivity
import Bong.Bong.Beli2019CanonicalApproximation
import Bong.Bong.DiagonalRepresentationParity

/-!
# Descent for codimension-one prefix representations

The second parity cycle in the diagonal form of Witt's theorem turns a
representation of one prefix in the next longer prefix into the preceding
prefix representation. The required fourth parity statement follows from
the usual dyadic defect-sum criterion for the Hilbert symbol.

The result is independent of the later Beli arguments and packages the
descending step used in the anisotropic branch of Lemma 9.12.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K] [HilbertSymbolLaws K]
  [DiagonalRepresentationParityLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- One descending step for codimension-one prefix representations.

In paper notation, from
`[c₁,...,cⱼ] rep [a₁,...,aⱼ₊₁]` and the defect sum making the relevant
Hilbert symbol equal to one, this proves
`[c₁,...,cⱼ₋₁] rep [a₁,...,aⱼ]`. -/
theorem prefixRepresentation_descend
    (a : GoodBONG q L (n + 1)) (c : GoodBONG r M (n + 1))
    (j : Nat) (hjTwo : 2 ≤ j) (hjNext : j + 1 ≤ n + 1)
    (hrep : DiagonalRepresents
      (c.prefixValues j (by omega))
      (a.prefixValues (j + 1) hjNext))
    (hdefect :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        defectOrder (K := K)
            (a.prefixProduct j * c.prefixProduct j) +
          defectOrder (K := K)
            (-a.prefixProduct (j + 1) * c.prefixProduct (j - 1))) :
    DiagonalRepresents
      (c.prefixValues (j - 1) (by omega))
      (a.prefixValues j (by omega)) := by
  let au := a.prefixValueUnits (j + 1) hjNext
  let cu := c.prefixValueUnits j (by omega)
  let cp := c.prefixValueUnits (j - 1) (by omega)
  have hrepUnits : DiagonalRepresents
      (diagonalUnitCoefficients cu)
      (diagonalUnitCoefficients au) := by
    simpa only [au, cu, diagonalUnitCoefficients_prefixValueUnits] using hrep
  have hprefix : DiagonalRepresents
      (diagonalUnitCoefficients cp)
      (diagonalUnitCoefficients cu) := by
    have h := c.prefixValues_represents_of_le
      (j - 1) j (by omega) (by omega)
    simpa only [cp, cu, diagonalUnitCoefficients_prefixValueUnits] using h
  have hhilbert : hilbertSymbol K
      (diagonalUnitDeterminant
          (diagonalUnitTake au j (by omega)) *
        diagonalUnitDeterminant cu)
      (-diagonalUnitDeterminant au * diagonalUnitDeterminant cp) = 1 := by
    apply hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
    simpa only [au, cu, cp, diagonalUnitTake_prefixValueUnits,
      diagonalUnitDeterminant_prefixValueUnits] using hdefect
  have hcycle := DiagonalRepresentationParityLaws.caseII
    au cu cp rfl (by omega)
  have hiff := EvenTruthParity.second_iff_third_of_first_fourth
    hcycle hrepUnits hhilbert
  have hresult := hiff.mp hprefix
  simpa only [au, cp, diagonalUnitTake_prefixValueUnits,
    diagonalUnitCoefficients_prefixValueUnits] using hresult

/-- Iterate `prefixRepresentation_descend` from an arbitrary prefix down to
the binary prefix.  The family `hdefect` is exactly the pair of strict
defect-sum inequalities used in the descending induction at the end of
Beli (2019), Lemma 9.12. -/
theorem prefixRepresentation_descend_to_two
    (a : GoodBONG q L (n + 1)) (c : GoodBONG r M (n + 1))
    (j : Nat) (hjTwo : 2 ≤ j) (hjNext : j + 1 ≤ n + 1)
    (hrep : DiagonalRepresents
      (c.prefixValues j (by omega))
      (a.prefixValues (j + 1) hjNext))
    (hdefect : ∀ k : Nat, 2 < k → k ≤ j →
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        defectOrder (K := K)
            (a.prefixProduct k * c.prefixProduct k) +
          defectOrder (K := K)
            (-a.prefixProduct (k + 1) * c.prefixProduct (k - 1))) :
    DiagonalRepresents
      (c.prefixValues 2 (by omega))
      (a.prefixValues 3 (by omega)) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
      by_cases hj : j = 2
      · subst j
        simpa using hrep
      · have hjThree : 3 ≤ j := by omega
        have hstep := a.prefixRepresentation_descend c j hjTwo hjNext hrep
          (hdefect j (by omega) le_rfl)
        have hstep' : DiagonalRepresents
            (c.prefixValues (j - 1) (by omega))
            (a.prefixValues ((j - 1) + 1) (by omega)) := by
          have hindex : (j - 1) + 1 = j := by omega
          exact targetPrefixRepresents_cast
            (c.prefixValues (j - 1) (by omega)) a hindex.symm hstep
        exact ih (j - 1) (by omega) (by omega) (by omega) hstep'
          (fun k hk hkj ↦ hdefect k hk (by omega))

end BONG.GoodBONG

end Bong
