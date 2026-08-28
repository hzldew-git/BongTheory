/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009TwoAdic
import Bong.Bong.DiscriminantClassProof
import Bong.Bong.MaximalDefectClassProof
import Bong.Dyadic.ValuationUnitDefect

/-!
# The 2-adic endpoint square classes in Beli (2009), Section 4

When the ramification index is one, the general dyadic endpoint `2e` is the
integer `2`.  The already proved maximal-defect dichotomy therefore says
that a class of defect at least two is either a square or the distinguished
discriminant class times a square.  Even valuation supplies the lower bound
one used in the remaining branch of Theorem 4.2.
-/

namespace Bong

open Dyadic

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

theorem defectOrder_two_le_iff_square_or_discriminant
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicMaximalDefectClassLaws K]
    (x : Kˣ) (htwoAdic : ramificationIndex K = 1)
    (_heven : Even (ordUnit K x)) :
    (2 : WithTop ℚ) ≤ defectOrder (K := K) x ↔
      IsSquareOrDistinguishedSquare laws.discriminantUnit x := by
  constructor
  · intro hdefect
    have htwoE :
        ((((2 * ramificationIndex K : Nat) : Nat) : ℚ) : WithTop ℚ) ≤
          defectOrder (K := K) x := by
      have heq :
          ((((2 * ramificationIndex K : Nat) : Nat) : ℚ) : WithTop ℚ) = 2 := by
        norm_num [htwoAdic]
      rw [heq]
      exact hdefect
    have hraw : ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
        quadraticDefect K x :=
      (natCast_le_defectOrder_iff x (2 * ramificationIndex K)).1 htwoE
    exact isSquare_or_isSquare_div_discriminant_of_defect_ge_twoE x hraw
  · rintro (hsquare | hdistinguished)
    · rw [defectOrder_eq_top_of_isSquare hsquare]
      exact le_top
    · rcases hdistinguished with ⟨y, hy⟩
      have hx : x = laws.discriminantUnit * y ^ 2 := by
        calc
          x = laws.discriminantUnit * (x / laws.discriminantUnit) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
          _ = laws.discriminantUnit * (y * y) := by rw [hy]
          _ = laws.discriminantUnit * y ^ 2 := by rw [pow_two]
      have hrawEq : quadraticDefect K x =
          ((2 * ramificationIndex K : Nat) : ℕ∞) := by
        calc
          quadraticDefect K x =
              quadraticDefect K (laws.discriminantUnit * y ^ 2) :=
            congrArg (quadraticDefect K) hx
          _ = quadraticDefect K laws.discriminantUnit :=
            quadraticDefect_mul_square K laws.discriminantUnit y
          _ = ((2 * ramificationIndex K : Nat) : ℕ∞) :=
            laws.discriminant_defect
      have htwoE :
          ((((2 * ramificationIndex K : Nat) : Nat) : ℚ) : WithTop ℚ) ≤
            defectOrder (K := K) x :=
        (natCast_le_defectOrder_iff x (2 * ramificationIndex K)).2
          (by rw [hrawEq])
      have heq :
          ((((2 * ramificationIndex K : Nat) : Nat) : ℚ) : WithTop ℚ) = 2 := by
        norm_num [htwoAdic]
      rw [heq] at htwoE
      exact htwoE

end BONG.GoodBONG

/-- Beli's 2-adic defect-class interface follows from the general dyadic
discriminant-class theorem once its explicit `e = 1` hypothesis is used. -/
noncomputable instance beli2009TwoAdicDefectClassLawsProved
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] :
    Beli2009TwoAdicDefectClassLaws K where
  distinguishedUnit := DyadicDiscriminantClassLaws.discriminantUnit
  defectOrder_one_le_of_even x _htwoAdic heven :=
    BONG.GoodBONG.defectOrder_one_le_of_even x heven
  defectOrder_two_le_iff x htwoAdic heven :=
    BONG.GoodBONG.defectOrder_two_le_iff_square_or_discriminant
      x htwoAdic heven

end Bong
