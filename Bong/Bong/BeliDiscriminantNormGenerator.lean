/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.UnramifiedNorm
import Bong.Dyadic.BeliGroups
import Bong.Dyadic.UnitDefectClassification
import Bong.Bong.DefectArithmetic

/-!
# The discriminant class at the boundary of Beli's norm-generator group

If a binary parameter has order exactly `2e`, Beli (2003), Definition 6,
places the distinguished discriminant unit in its norm-generator group.
This is the local-field calculation used in Beli (2019), Lemma 7.17, type
III, before applying paragraph 3.12.

The low-defect branch uses the standard fact that the norm group of the
unramified quadratic extension consists of the even-order elements.  That
fact remains visible through the independent `DyadicUnramifiedNormLaws`
interface.
-/

namespace Bong.Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [laws : DyadicDiscriminantClassLaws K]

/-- The distinguished discriminant unit, bundled as a valuation unit. -/
noncomputable def discriminantValuationUnit : valuationUnitSubgroup K :=
  ⟨laws.discriminantUnit, laws.discriminant_isValuationUnit⟩

/-- The distinguished discriminant valuation unit is genuinely nonsquare. -/
theorem discriminantValuationUnit_not_isSquare :
    ¬IsSquare (discriminantValuationUnit (K := K) : Kˣ) := by
  intro hsquare
  have htop := quadraticDefect_eq_top_of_isSquare (K := K) hsquare
  change quadraticDefect K laws.discriminantUnit = ⊤ at htop
  rw [laws.discriminant_defect] at htop
  exact ENat.coe_ne_top (2 * ramificationIndex K) htop

/-- The equation `Delta = 1 - 4 rho` puts the discriminant unit in the
principal-unit group of depth `2e`. -/
theorem discriminantUnit_mem_principalUnitSubgroup_twoE :
    laws.discriminantUnit ∈
      principalUnitSubgroup K (2 * ramificationIndex K) := by
  rw [mem_principalUnitSubgroup_iff]
  refine ⟨laws.discriminant_isValuationUnit, ?_⟩
  rw [Lattice.mem_powerIdeal_iff]
  rw [laws.discriminant_eq_one_sub_four_mul_rho]
  have herror : (1 - 4 * laws.rho : K) - 1 = -(4 * laws.rho) := by
    ring
  rw [herror, ord_neg]
  have hfour : (4 : K) = 2 * 2 := by norm_num
  rw [hfour, ord_mul, ord_mul, laws.rho_isValuationUnit,
    ← ramificationIndex_spec]
  norm_cast
  omega

/-- Unit-square-class form of the depth-`2e` congruence. -/
theorem
    discriminantUnitClass_mem_principalUnitValuationClassSubgroup_twoE :
    valuationUnitClassHom K (discriminantValuationUnit (K := K)) ∈
      principalUnitValuationClassSubgroup K (2 * ramificationIndex K) := by
  refine ⟨discriminantValuationUnit (K := K), ?_, rfl⟩
  exact discriminantUnit_mem_principalUnitSubgroup_twoE (K := K)

variable [DyadicUnramifiedNormLaws K]

/-- The discriminant unit is a norm from every even-order parameter. -/
theorem discriminantUnit_isQuadraticNorm_of_even_order
    (a : Kˣ) (ha : Even (ordUnit K a)) :
    IsQuadraticNorm K a laws.discriminantUnit := by
  exact (IsQuadraticNorm.symm K)
    ((isQuadraticNorm_discriminant_iff_even_order a).2 ha)

/-- Unit-square-class form of the preceding norm statement. -/
theorem
    discriminantUnitClass_mem_quadraticNormValuationClassSubgroup_of_even_order
    (a : Kˣ) (ha : Even (ordUnit K a)) :
    valuationUnitClassHom K (discriminantValuationUnit (K := K)) ∈
      quadraticNormValuationClassSubgroup K a := by
  refine ⟨discriminantValuationUnit (K := K), ?_, rfl⟩
  exact discriminantUnit_isQuadraticNorm_of_even_order a ha

/-- Beli (2003), Definition 6, at the boundary `ord(a) = 2e`: the
distinguished discriminant unit belongs to `g(a)`. -/
theorem discriminantUnitClass_mem_beliNormGeneratorGroup_of_order_eq_twoE
    (a : Kˣ)
    (horder : ordUnit K a = 2 * (ramificationIndex K : Int)) :
    valuationUnitClassHom K (discriminantValuationUnit (K := K)) ∈
      beliNormGeneratorGroup K a := by
  have hnotAbove : ¬ 2 * (ramificationIndex K : Int) < ordUnit K a := by
    omega
  by_cases hlow : 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞)
  · rw [beliNormGeneratorGroup_of_low_defect K a hnotAbove hlow]
    have hcutoff : beliDefectCutoff K a = 0 := by
      simp [beliDefectCutoff, horder]
    rw [hcutoff] at hlow
    have hdefect : beliParameterDefect K a = 0 := by
      simpa using hlow
    have hdefectNat : beliParameterDefectNat K a = 0 := by
      simp [beliParameterDefectNat, hdefect]
    have hexponent : beliLowDefectExponent K a =
        2 * ramificationIndex K := by
      rw [beliLowDefectExponent, horder, hdefectNat]
      have hcast : 2 * (ramificationIndex K : Int) =
          (2 * ramificationIndex K : Nat) := by norm_cast
      rw [hcast]
      simp
      rw [Int.toNat_mul (by norm_num) (by positivity)]
      simp
    rw [hexponent]
    refine ⟨
      discriminantUnitClass_mem_principalUnitValuationClassSubgroup_twoE
        (K := K), ?_⟩
    apply
      discriminantUnitClass_mem_quadraticNormValuationClassSubgroup_of_even_order
    rw [show ordUnit K (-a) = ordUnit K a by
      apply WithTop.coe_injective
      simp]
    rw [horder]
    exact ⟨ramificationIndex K, by omega⟩
  · rw [beliNormGeneratorGroup_of_high_defect K a hnotAbove hlow]
    have hexponent : beliHighDefectExponent K a =
        2 * ramificationIndex K := by
      rw [beliHighDefectExponent, horder]
      have hinside :
          (ramificationIndex K : Int) +
              (2 * (ramificationIndex K : Int)) / 2 =
            2 * (ramificationIndex K : Int) := by omega
      rw [hinside]
      have hcast : 2 * (ramificationIndex K : Int) =
          (2 * ramificationIndex K : Nat) := by norm_cast
      rw [hcast, Int.toNat_natCast]
    rw [hexponent]
    exact
      discriminantUnitClass_mem_principalUnitValuationClassSubgroup_twoE
        (K := K)

/-- For every even-order parameter in the range `ord(a) <= 2e`, the
distinguished discriminant unit belongs to Beli's norm-generator group.

This is the form of the observation following Beli (2003), Definition 6 that
is needed in Lemma 4.11.  The low-defect inequality bounds `R + d(-a)` by
`2e`; in the high-defect branch the exponent `e + R / 2` has the same bound.
-/
theorem discriminantUnitClass_mem_beliNormGeneratorGroup_of_even_order_le_twoE
    (a : Kˣ) (heven : Even (ordUnit K a))
    (horder : ordUnit K a ≤ 2 * (ramificationIndex K : Int)) :
    valuationUnitClassHom K (discriminantValuationUnit (K := K)) ∈
      beliNormGeneratorGroup K a := by
  have hnotAbove : ¬2 * (ramificationIndex K : Int) < ordUnit K a :=
    not_lt.mpr horder
  by_cases hlow : 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞)
  · rw [beliNormGeneratorGroup_of_low_defect K a hnotAbove hlow]
    have hfinite : beliParameterDefect K a ≠ ⊤ := by
      intro htop
      rw [htop] at hlow
      simp at hlow
    have hdefectEq : beliParameterDefect K a =
        (beliParameterDefectNat K a : ℕ∞) := by
      simpa [beliParameterDefectNat] using
        (ENat.coe_toNat hfinite).symm
    have hdefectNat : 2 * beliParameterDefectNat K a ≤
        beliDefectCutoff K a := by
      rw [hdefectEq] at hlow
      exact_mod_cast hlow
    have hcutoff : (beliDefectCutoff K a : Int) =
        2 * (ramificationIndex K : Int) - ordUnit K a := by
      unfold beliDefectCutoff
      rw [Int.toNat_of_nonneg]
      omega
    have hexponent : beliLowDefectExponent K a ≤
        2 * ramificationIndex K := by
      unfold beliLowDefectExponent
      have hdefectInt :
          2 * (beliParameterDefectNat K a : Int) ≤
            (beliDefectCutoff K a : Int) := by
        exact_mod_cast hdefectNat
      rw [hcutoff] at hdefectInt
      omega
    refine ⟨principalUnitValuationClassSubgroup_anti K hexponent
        (discriminantUnitClass_mem_principalUnitValuationClassSubgroup_twoE
          (K := K)), ?_⟩
    apply
      discriminantUnitClass_mem_quadraticNormValuationClassSubgroup_of_even_order
    simpa using heven
  · rw [beliNormGeneratorGroup_of_high_defect K a hnotAbove hlow]
    have hexponent : beliHighDefectExponent K a ≤
        2 * ramificationIndex K := by
      unfold beliHighDefectExponent
      rcases heven with ⟨r, hr⟩
      omega
    exact principalUnitValuationClassSubgroup_anti K hexponent
      (discriminantUnitClass_mem_principalUnitValuationClassSubgroup_twoE
        (K := K))

variable [HilbertSymbolLaws K]

/-- For an admissible odd order in the range `0 < ord(a) < 2e`, Beli's group
`g(a)` contains a nonsquare unit class.

Choose a unit of quadratic defect `ord(a)`.  If it is not a norm from
`K(sqrt(-a))`, multiply it by the distinguished discriminant unit.  Because
`ord(a)` is odd, the discriminant has Hilbert symbol `-1` against `-a`, so
this multiplication switches the norm coset while preserving the smaller
quadratic defect.
-/
theorem exists_nonsquare_mem_beliNormGeneratorGroup_of_odd_order_le_twoE
    (a : Kˣ) (hodd : Odd (ordUnit K a))
    (hnonneg : 0 ≤ ordUnit K a)
    (horder : ordUnit K a ≤ 2 * (ramificationIndex K : Int)) :
    ∃ z : valuationUnitSubgroup K,
      valuationUnitClassHom K z ∈ beliNormGeneratorGroup K a ∧
        ¬IsSquare (z : Kˣ) := by
  let d : Nat := Int.toNat (ordUnit K a)
  have hdCast : (d : Int) = ordUnit K a := by
    exact Int.toNat_of_nonneg hnonneg
  have hdOdd : Odd d := by
    rw [← hdCast] at hodd
    exact_mod_cast hodd
  have hdPos : 0 < d := by
    rcases hdOdd with ⟨r, hr⟩
    omega
  have hdLt : d < 2 * ramificationIndex K := by
    have hevenTwoE : Even (2 * (ramificationIndex K : Int)) :=
      ⟨ramificationIndex K, by omega⟩
    have hstrict : ordUnit K a < 2 * (ramificationIndex K : Int) := by
      apply lt_of_le_of_ne horder
      intro heq
      apply Int.not_even_iff_odd.mpr hodd
      rwa [heq]
    rw [← hdCast] at hstrict
    exact_mod_cast hstrict
  rcases exists_unit_quadraticDefect_eq_odd
      (K := K) d hdPos hdOdd hdLt with ⟨u, huUnit, huDefect⟩
  let uUnit : valuationUnitSubgroup K := ⟨u, huUnit⟩
  have hparameterDefect : beliParameterDefect K a = 0 := by
    apply quadraticDefect_eq_zero_of_odd_ordUnit
    simpa using hodd
  have hnotAbove : ¬2 * (ramificationIndex K : Int) < ordUnit K a :=
    not_lt.mpr horder
  have hlow : 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞) := by
    rw [hparameterDefect]
    simp
  have hexponent : beliLowDefectExponent K a = d := by
    unfold beliLowDefectExponent beliParameterDefectNat
    rw [hparameterDefect]
    simpa [d]
  rw [beliNormGeneratorGroup_of_low_defect K a hnotAbove hlow,
    hexponent]
  have huPrincipal : valuationUnitClassHom K uUnit ∈
      principalUnitValuationClassSubgroup K d := by
    apply valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
    rw [huDefect]
  have huNotSquare : ¬IsSquare u := by
    intro hsquare
    have htop := quadraticDefect_eq_top_of_isSquare (K := K) hsquare
    rw [huDefect] at htop
    exact ENat.coe_ne_top d htop
  by_cases huNorm : IsQuadraticNorm K (-a) u
  · exact ⟨uUnit, ⟨huPrincipal, ⟨uUnit, huNorm, rfl⟩⟩, huNotSquare⟩
  · let delta := discriminantValuationUnit (K := K)
    let z : valuationUnitSubgroup K := delta * uUnit
    have hdeltaDefect : quadraticDefect K (delta : Kˣ) =
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
      exact laws.discriminant_defect
    have huDefectLt : quadraticDefect K (uUnit : Kˣ) <
        quadraticDefect K (delta : Kˣ) := by
      rw [huDefect, hdeltaDefect]
      exact_mod_cast hdLt
    have hzDefect : quadraticDefect K (z : Kˣ) = (d : ℕ∞) := by
      change quadraticDefect K ((delta : Kˣ) * (uUnit : Kˣ)) = (d : ℕ∞)
      rw [quadraticDefect_mul_eq_right_of_lt_left (K := K) huDefectLt,
        huDefect]
    have hzPrincipal : valuationUnitClassHom K z ∈
        principalUnitValuationClassSubgroup K d := by
      apply valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
      rw [hzDefect]
    have huHilbert : hilbertSymbol K (-a) u = -1 :=
      (hilbertSymbol_eq_neg_one_iff K (-a) u).2 huNorm
    have hdeltaNeOne : hilbertSymbol K (-a) (delta : Kˣ) ≠ 1 := by
      rw [hilbertSymbol_comm]
      apply hilbertSymbol_discriminant_ne_one_of_odd_order
      simpa using hodd
    have hdeltaHilbert : hilbertSymbol K (-a) (delta : Kˣ) = -1 :=
      (Int.units_eq_one_or _).resolve_left hdeltaNeOne
    have hzNorm : IsQuadraticNorm K (-a) (z : Kˣ) := by
      rw [← hilbertSymbol_eq_one_iff]
      change hilbertSymbol K (-a) ((delta : Kˣ) * u) = 1
      rw [hilbertSymbol_mul_right, hdeltaHilbert, huHilbert]
      norm_num
    have hzNotSquare : ¬IsSquare (z : Kˣ) := by
      intro hsquare
      have htop := quadraticDefect_eq_top_of_isSquare (K := K) hsquare
      rw [hzDefect] at htop
      exact ENat.coe_ne_top d htop
    exact ⟨z, ⟨hzPrincipal, ⟨z, hzNorm, rfl⟩⟩, hzNotSquare⟩

/-- Every admissible binary parameter of order at most `2e` has a genuinely
nontrivial norm-generator class. -/
theorem exists_nonsquare_mem_beliNormGeneratorGroup_of_admissible_order_le_twoE
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (horder : ordUnit K a ≤ 2 * (ramificationIndex K : Int)) :
    ∃ z : valuationUnitSubgroup K,
      valuationUnitClassHom K z ∈ beliNormGeneratorGroup K a ∧
        ¬IsSquare (z : Kˣ) := by
  rcases Int.even_or_odd (ordUnit K a) with heven | hodd
  · exact ⟨discriminantValuationUnit (K := K),
      discriminantUnitClass_mem_beliNormGeneratorGroup_of_even_order_le_twoE
        (K := K) a heven horder,
      discriminantValuationUnit_not_isSquare (K := K)⟩
  · exact exists_nonsquare_mem_beliNormGeneratorGroup_of_odd_order_le_twoE
      (K := K) a hodd (ha.ordUnit_nonneg_of_odd hodd) horder

end Bong.Dyadic
