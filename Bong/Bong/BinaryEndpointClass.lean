/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinarySpinorGroupFormula
import Bong.Bong.BinaryAdmissibility

/-!
# The endpoint classes of an improper modular binary lattice

At relative order `-2e`, an admissible binary parameter has one of two
valuation-unit square classes: `-1/4` or `-Δ/4`.  This file isolates that
local-field classification independently of any result from Beli (2019).
-/

namespace Bong

open Dyadic

universe u v

/-- Foundational discriminant-class data for a dyadic local field.  The
classification field is the standard endpoint statement for admissible
binary parameters; it is deliberately independent of the 2019 paper. -/
class DyadicDiscriminantClassLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] where
  discriminantUnit : Kˣ
  discriminant_isValuationUnit :
    IsValuationUnit K (discriminantUnit : K)
  rho : K
  rho_isValuationUnit : IsValuationUnit K rho
  discriminant_eq_one_sub_four_mul_rho :
    (discriminantUnit : K) = 1 - 4 * rho
  discriminant_defect :
    quadraticDefect K discriminantUnit =
      ((2 * ramificationIndex K : Nat) : ℕ∞)
  endpoint_parameter_class (a : Kˣ)
      (hadmissible : BONG.IsBinaryParameterAdmissible a)
      (horder : ordUnit K a =
        -(2 * (ramificationIndex K : Int))) :
    unitSquareClass K a = unitSquareClass K (negativeQuarterUnit K) ∨
      unitSquareClass K a = unitSquareClass K
        (negativeQuarterUnit K * discriminantUnit)

/-- The maximal quadratic-defect square-class theorem for a dyadic local
field.  A class of defect at least `2e` is either trivial or the unique
discriminant class.  This is field arithmetic, independent of any lattice
or of Beli's 2019 representation theorem, and therefore is kept as a
separate local-field interface with no default instance. -/
class DyadicMaximalDefectClassLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [DyadicDiscriminantClassLaws K] : Prop where
  square_or_discriminantSquare_of_defect_ge_twoE
      (x : Kˣ)
      (hdefect : ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
        quadraticDefect K x) :
      IsSquare x ∨
        IsSquare (x / DyadicDiscriminantClassLaws.discriminantUnit)

/-- Public form of the maximal-defect square-class dichotomy. -/
theorem isSquare_or_isSquare_div_discriminant_of_defect_ge_twoE
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [DyadicDiscriminantClassLaws K]
    [DyadicMaximalDefectClassLaws K]
    (x : Kˣ)
    (hdefect : ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
      quadraticDefect K x) :
    IsSquare x ∨
      IsSquare (x / DyadicDiscriminantClassLaws.discriminantUnit) :=
  DyadicMaximalDefectClassLaws.square_or_discriminantSquare_of_defect_ge_twoE
    x hdefect

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Adjacent BONG parameters at the minimal possible order have one of the
two binary endpoint classes. -/
theorem adjacentUnitSquareClass_endpoint_cases
    [laws : DyadicDiscriminantClassLaws K]
    (b : BONG V q L n) (i : Fin n) (hi : i.val + 1 < n)
    (hgap : b.order ⟨i.val + 1, hi⟩ - b.order i =
      -(2 * (ramificationIndex K : Int))) :
    b.adjacentUnitSquareClass i hi =
        unitSquareClass K (negativeQuarterUnit K) ∨
      b.adjacentUnitSquareClass i hi = unitSquareClass K
        (negativeQuarterUnit K * laws.discriminantUnit) := by
  apply laws.endpoint_parameter_class
  · exact b.adjacentParameter_isBinaryParameterAdmissible i hi
  · rw [b.ordUnit_adjacentParameter i hi]
    exact hgap

end BONG

end Bong
