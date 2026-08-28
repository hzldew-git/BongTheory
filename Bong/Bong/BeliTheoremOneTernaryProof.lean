/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliTheoremOneForward
import Bong.Bong.BeliLemma411Proof
import Bong.Bong.BeliCorollary315
import Bong.Bong.HilbertDefectChoiceProof
import Bong.Bong.Beli2019Lemma82Unit
import Bong.Bong.BeliDiscriminantNormGenerator
import Bong.Bong.DiscriminantClassProof
import Bong.Bong.BeliLemma47Proof
import Bong.Bong.BeliLemma49Proof
import Bong.Bong.BinaryNormGeneratorLocalProof
import Bong.Bong.BinarySpinorLocalProof
import Bong.Bong.StructuralProof
import Bong.Dyadic.UnramifiedNormProof
import Bong.Dyadic.UnramifiedNormDirectProof
import Bong.Dyadic.QuadraticDefectHensel
import Bong.Dyadic.UnitDefectClassification

/-!
# Beli (2003), Theorem 1: the ternary calculation

This file proves the rank-three calculation in Section 5.  Together with
consecutive-segment transport, this is the only rank-specific input in the
forward inclusion of Theorem 1.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Dyadic

/-- Every principal unit whose depth is strictly greater than `2e` has
trivial field square class. -/
theorem principalUnitSquareClassSubgroup_eq_bot_of_two_mul_e_lt
    (n : Nat) (hdeep : 2 * ramificationIndex K < n) :
    principalUnitSquareClassSubgroup K n = ⊥ := by
  apply le_antisymm
  · intro c hc
    rcases hc with ⟨u, hu, rfl⟩
    change squareClass K u = 1
    apply (QuotientGroup.eq_one_iff u).2
    apply isSquare_of_ord_sub_one_gt_two_mul_e K u
    change IsValuationUnit K (u : K) ∧
      (u : K) - 1 ∈ Lattice.powerIdeal (K := K) (n : Int) at hu
    rw [Lattice.mem_powerIdeal_iff] at hu
    have hcast :
        (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) <
          ((n : Int) : WithTop Int) := by
      exact_mod_cast hdeep
    exact hcast.trans_le hu.2
  · exact bot_le

/-- The distinguished discriminant class belongs to every admissible binary
spinor group of even order in the middle range `2e < R ≤ 4e`. -/
theorem discriminantSquareClass_mem_beliSpinorGroup_of_even_middle
    [DyadicDiscriminantClassLaws K] [DyadicUnramifiedNormLaws K]
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (heven : Even (ordUnit K a))
    (hRlow : 2 * (ramificationIndex K : Int) < ordUnit K a)
    (hRhigh : ordUnit K a ≤ 4 * (ramificationIndex K : Int)) :
    squareClass K
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit ∈
      beliSpinorGroupRepresentative K a := by
  let delta : Kˣ :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  have hquarter := unitSquareClass_ne_negativeQuarter_of_two_e_lt
    (K := K) a hRlow
  have hdeltaTwoE : squareClass K delta ∈
      principalUnitSquareClassSubgroup K (2 * ramificationIndex K) := by
    refine ⟨delta, ?_, rfl⟩
    exact discriminantUnit_mem_principalUnitSubgroup_twoE (K := K)
  by_cases hd : 2 * beliParameterDefect K a ≤
      (beliSpinorCaseIICutoff K a : ℕ∞)
  · rw [beliSpinorGroupRepresentative_caseII_low K a ha hquarter
      hRlow hRhigh hd]
    apply (show
      principalUnitSquareClassSubgroup K
            (beliSpinorCaseIILowExponent K a) ⊓
          quadraticNormSquareClassSubgroup K (-a) ≤
        cyclicSquareClassSubgroup K a ⊔
          (principalUnitSquareClassSubgroup K
              (beliSpinorCaseIILowExponent K a) ⊓
            quadraticNormSquareClassSubgroup K (-a)) from le_sup_right)
    constructor
    · apply principalUnitSquareClassSubgroup_anti K
        (m := beliSpinorCaseIILowExponent K a)
        (n := 2 * ramificationIndex K)
      · have hfinite : beliParameterDefect K a ≠ ⊤ := by
          intro htop
          rw [htop] at hd
          simp at hd
        have hdefectEq : beliParameterDefect K a =
            (beliParameterDefectNat K a : ℕ∞) := by
          simpa [beliParameterDefectNat] using
            (ENat.coe_toNat hfinite).symm
        have hdNat : 2 * beliParameterDefectNat K a ≤
            beliSpinorCaseIICutoff K a := by
          rw [hdefectEq] at hd
          exact_mod_cast hd
        unfold beliSpinorCaseIICutoff at hdNat
        have hcutNonneg : 0 ≤
            4 * (ramificationIndex K : Int) - ordUnit K a := by omega
        have hdInt : 2 * (beliParameterDefectNat K a : Int) ≤
            (Int.toNat
              (4 * (ramificationIndex K : Int) - ordUnit K a) : Int) := by
          exact_mod_cast hdNat
        rw [Int.toNat_of_nonneg hcutNonneg] at hdInt
        unfold beliSpinorCaseIILowExponent
        omega
      · exact hdeltaTwoE
    · refine ⟨delta, ?_, rfl⟩
      change IsQuadraticNorm K (-a) delta
      simpa only [delta] using
        (discriminantUnit_isQuadraticNorm_of_even_order
          (K := K) (-a) (by simpa using heven))
  · rw [beliSpinorGroupRepresentative_caseII_high K a ha hquarter
      hRlow hRhigh hd]
    apply (show principalUnitSquareClassSubgroup K
          (beliSpinorCaseIIHighExponent K a) ≤
        cyclicSquareClassSubgroup K a ⊔
          principalUnitSquareClassSubgroup K
            (beliSpinorCaseIIHighExponent K a) from le_sup_right)
    apply principalUnitSquareClassSubgroup_anti K
      (m := beliSpinorCaseIIHighExponent K a)
      (n := 2 * ramificationIndex K)
    · unfold beliSpinorCaseIIHighExponent
      omega
    · exact hdeltaTwoE

/-- An odd-order parameter does not norm the distinguished discriminant
class.  This is the codimension-one separation used in Section 5(i)(b). -/
theorem theoremOneDiscriminant_not_mem_quadraticNorm_of_odd
    [DyadicDiscriminantClassLaws K]
    (a : Kˣ) (hodd : Odd (ordUnit K a)) :
    squareClass K
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit ∉
      quadraticNormSquareClassSubgroup K (-a) := by
  let delta : Kˣ :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  have hoddNeg : Odd (ordUnit K (-a)) := by simpa using hodd
  have hne := hilbertSymbol_discriminant_ne_one_of_odd_order
    (K := K) (-a) hoddNeg
  rw [quadraticNormSquareClassSubgroup_eq_ker]
  intro hmem
  change squareClassHilbertCharacter K (-a) (squareClass K delta) = 1
    at hmem
  rw [squareClassHilbertCharacter_apply] at hmem
  apply hne
  rw [hilbertSymbol_comm]
  simpa only [delta] using hmem

/-- For an admissible odd parameter in the middle range, its binary spinor
group together with the discriminant class fills the principal layer at
depth `ord(a)-2e`. -/
theorem theoremOnePrincipalUnit_order_sub_twoE_le_of_odd_spinor_and_discriminant
    [DyadicDiscriminantClassLaws K]
    (a : Kˣ) (H : Subgroup (SquareClass K))
    (ha : BONG.IsBinaryParameterAdmissible a)
    (hodd : Odd (ordUnit K a))
    (hRlow : 2 * (ramificationIndex K : Int) < ordUnit K a)
    (hRhigh : ordUnit K a ≤ 4 * (ramificationIndex K : Int))
    (hspinor : beliSpinorGroupRepresentative K a ≤ H)
    (hdelta : squareClass K
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit ∈ H) :
    principalUnitSquareClassSubgroup K
        (Int.toNat
          (ordUnit K a - 2 * (ramificationIndex K : Int))) ≤ H := by
  let delta : Kˣ :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let m : Nat := Int.toNat
    (ordUnit K a - 2 * (ramificationIndex K : Int))
  have hdefect : beliParameterDefect K a = 0 := by
    unfold beliParameterDefect
    exact quadraticDefect_eq_zero_of_odd_ordUnit (-a) (by simpa using hodd)
  have hdefectNat : beliParameterDefectNat K a = 0 := by
    simp [beliParameterDefectNat, hdefect]
  have hcut : 2 * beliParameterDefect K a ≤
      (beliSpinorCaseIICutoff K a : ℕ∞) := by
    rw [hdefect]
    simp
  have hexponent : beliSpinorCaseIILowExponent K a = m := by
    unfold beliSpinorCaseIILowExponent
    rw [hdefectNat]
    simp only [Nat.cast_zero, add_zero]
    rfl
  have hauxFormula := beliAuxiliarySpinorGroup_caseII_low
    (K := K) a hRlow hRhigh hcut
  rw [hexponent] at hauxFormula
  have hquarter := unitSquareClass_ne_negativeQuarter_of_two_e_lt
    (K := K) a hRlow
  have hfullFormula :=
    beliSpinorGroupRepresentative_eq_cyclic_sup_auxiliary
      K a ha hquarter hRlow
  have hauxLeH : beliAuxiliarySpinorGroup K a hRlow ≤ H := by
    apply (show beliAuxiliarySpinorGroup K a hRlow ≤
      beliSpinorGroupRepresentative K a by
        rw [hfullFormula]
        exact le_sup_right) |>.trans
    exact hspinor
  have hinfLeH : principalUnitSquareClassSubgroup K m ⊓
      quadraticNormSquareClassSubgroup K (-a) ≤ H := by
    rw [← hauxFormula]
    exact hauxLeH
  have hmLe : m ≤ 2 * ramificationIndex K := by
    dsimp only [m]
    have hnonneg : 0 ≤
        ordUnit K a - 2 * (ramificationIndex K : Int) := by omega
    have hmCast : (m : Int) =
        ordUnit K a - 2 * (ramificationIndex K : Int) := by
      rw [Int.toNat_of_nonneg hnonneg]
    exact_mod_cast (show (m : Int) ≤
      2 * (ramificationIndex K : Int) by omega)
  have hdeltaLayer : squareClass K delta ∈
      principalUnitSquareClassSubgroup K m := by
    apply principalUnitSquareClassSubgroup_anti K hmLe
    refine ⟨delta, ?_, rfl⟩
    exact discriminantUnit_mem_principalUnitSubgroup_twoE (K := K)
  have hdeltaNotNorm : squareClass K delta ∉
      quadraticNormSquareClassSubgroup K (-a) := by
    simpa only [delta] using
      theoremOneDiscriminant_not_mem_quadraticNorm_of_odd
        (K := K) a hodd
  have hcyclicLayer : cyclicSquareClassSubgroup K delta ≤
      principalUnitSquareClassSubgroup K m :=
    (Subgroup.zpowers_le).2 hdeltaLayer
  have hcyclicNotNorm : ¬cyclicSquareClassSubgroup K delta ≤
      quadraticNormSquareClassSubgroup K (-a) := by
    intro hle
    exact hdeltaNotNorm (hle (Subgroup.mem_zpowers (squareClass K delta)))
  have hfill := inf_ker_sup_eq_of_le_of_not_le
    (squareClassHilbertCharacter K (-a))
    (principalUnitSquareClassSubgroup K m)
    (cyclicSquareClassSubgroup K delta) hcyclicLayer (by
      rw [← quadraticNormSquareClassSubgroup_eq_ker K (-a)]
      exact hcyclicNotNorm)
  rw [← quadraticNormSquareClassSubgroup_eq_ker K (-a)] at hfill
  rw [← hfill]
  apply sup_le hinfLeH
  exact (Subgroup.zpowers_le).2 (by simpa only [delta] using hdelta)

/-- The valuation-unit square-class subgroup has index two.  Hence any
larger subgroup containing an odd-valuation class is the whole group. -/
theorem theoremOneSquareClassSubgroup_eq_top_of_valuationUnit_le_of_not_le
    (H : Subgroup (SquareClass K))
    (hunit : valuationUnitSquareClassSubgroup K ≤ H)
    (hnot : ¬H ≤ valuationUnitSquareClassSubgroup K) :
    H = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro aClass
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective (Subgroup.square Kˣ) aClass
  change ¬∀ x, x ∈ H →
    x ∈ valuationUnitSquareClassSubgroup K at hnot
  push Not at hnot
  obtain ⟨bClass, hbH, hbNotUnit⟩ := hnot
  obtain ⟨b, hbClass⟩ :=
    QuotientGroup.mk'_surjective (Subgroup.square Kˣ) bClass
  have hbH' : squareClass K b ∈ H := by
    change (QuotientGroup.mk' (Subgroup.square Kˣ)) b ∈ H
    rw [hbClass]
    exact hbH
  have hbNotUnit' : squareClass K b ∉
      valuationUnitSquareClassSubgroup K := by
    change (QuotientGroup.mk' (Subgroup.square Kˣ)) b ∉
      valuationUnitSquareClassSubgroup K
    rw [hbClass]
    exact hbNotUnit
  have hbOdd : Odd (ordUnit K b) := by
    apply Int.not_even_iff_odd.mp
    intro hbEven
    exact hbNotUnit'
      ((squareClass_mem_valuationUnitSquareClassSubgroup_iff_even b).2
        hbEven)
  rcases Int.even_or_odd (ordUnit K a) with haEven | haOdd
  · exact hunit
      ((squareClass_mem_valuationUnitSquareClassSubgroup_iff_even a).2
        haEven)
  · have habEven : Even (ordUnit K (a / b)) := by
      rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv]
      exact haOdd.sub_odd hbOdd
    have habH : squareClass K (a / b) ∈ H :=
      hunit
        ((squareClass_mem_valuationUnitSquareClassSubgroup_iff_even
          (a / b)).2 habEven)
    have hmul := H.mul_mem habH hbH'
    change squareClass K (a / b) * squareClass K b ∈ H at hmul
    change (squareClassHom K) a ∈ H
    have hmul' : (squareClassHom K) (a / b * b) ∈ H := by
      simpa only [← squareClassHom_apply, ← map_mul] using hmul
    simpa [div_eq_mul_inv] using hmul'

/-- A quadratic norm hyperplane together with one square class outside it
generates the full square-class group. -/
theorem quadraticNorm_sup_cyclic_eq_top_of_not_mem
    (a z : Kˣ)
    (hz : squareClass K z ∉ quadraticNormSquareClassSubgroup K a) :
    quadraticNormSquareClassSubgroup K a ⊔
        cyclicSquareClassSubgroup K z = ⊤ := by
  have hnot : ¬cyclicSquareClassSubgroup K z ≤
      (squareClassHilbertCharacter K a).ker := by
    rw [← quadraticNormSquareClassSubgroup_eq_ker K a]
    intro hle
    exact hz (hle (Subgroup.mem_zpowers (squareClass K z)))
  rw [quadraticNormSquareClassSubgroup_eq_ker]
  simpa using inf_ker_sup_eq_of_le_of_not_le
    (squareClassHilbertCharacter K a) ⊤
      (cyclicSquareClassSubgroup K z) le_top hnot

/-- A quadratic norm hyperplane and a principal-unit layer generate all
square classes when the layer depth plus the parameter defect is at most
`2e`. -/
theorem quadraticNorm_sup_principalUnit_eq_top_of_defect_add_le
    (a : Kˣ) (alpha d : Nat) (halpha : 0 < alpha)
    (hdefect : quadraticDefect K a = (d : ℕ∞))
    (hbound : alpha + d ≤ 2 * ramificationIndex K) :
    quadraticNormSquareClassSubgroup K a ⊔
        principalUnitSquareClassSubgroup K alpha = ⊤ := by
  have hnot : ¬principalUnitSquareClassSubgroup K alpha ≤
      quadraticNormSquareClassSubgroup K a := by
    rw [principalUnitSquareClassSubgroup_le_quadraticNorm_iff
      K a alpha halpha, hdefect]
    norm_cast
    omega
  rw [quadraticNormSquareClassSubgroup_eq_ker] at hnot ⊢
  simpa using inf_ker_sup_eq_of_le_of_not_le
    (squareClassHilbertCharacter K a) ⊤
      (principalUnitSquareClassSubgroup K alpha) le_top hnot

/-- A chosen valuation unit of exact defect `m` and Hilbert sign `+1`
belongs to the low norm-generator group of an odd parameter of order `m`.
-/
theorem valuationUnitClass_mem_beliNormGeneratorGroup_of_odd_exact
    (a : Kˣ) (zeta : valuationUnitSubgroup K) (m : Nat)
    (haOrder : ordUnit K a = (m : Int))
    (haOdd : Odd (ordUnit K a))
    (haUpper : ordUnit K a ≤ 2 * (ramificationIndex K : Int))
    (hzetaDefect : quadraticDefect K (zeta : Kˣ) = (m : ℕ∞))
    (hzetaHilbert : hilbertSymbol K (-a) (zeta : Kˣ) = 1) :
    valuationUnitClassHom K zeta ∈ beliNormGeneratorGroup K a := by
  have hnotAbove : ¬2 * (ramificationIndex K : Int) < ordUnit K a := by
    omega
  have hoddNeg : Odd (ordUnit K (-a)) := by simpa using haOdd
  have hdefect : beliParameterDefect K a = 0 := by
    unfold beliParameterDefect
    exact quadraticDefect_eq_zero_of_odd_ordUnit (-a) hoddNeg
  have hlow : 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞) := by
    rw [hdefect]
    simp
  rw [beliNormGeneratorGroup_of_low_defect K a hnotAbove hlow]
  have hdefectNat : beliParameterDefectNat K a = 0 := by
    simp [beliParameterDefectNat, hdefect]
  have hexponent : beliLowDefectExponent K a = m := by
    unfold beliLowDefectExponent
    rw [hdefectNat, haOrder]
    simp
  rw [hexponent]
  constructor
  · apply
      valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
    rw [hzetaDefect]
  · refine ⟨zeta, ?_, rfl⟩
    change IsQuadraticNorm K (-a) (zeta : Kˣ)
    exact (hilbertSymbol_eq_one_iff K (-a) (zeta : Kˣ)).1
      hzetaHilbert

/-- The easy high-defect branch of Section 5(iii): if an even parameter has
order at most `2e` and its neighbor has order greater than `2e`, the binary
spinor group already contains the principal layer at half the total order.
-/
theorem principalUnit_half_sum_le_beliSpinorGroup_of_even_high
    (R T : Int) (epsilon : Kˣ)
    (hepsilon : IsValuationUnit K (epsilon : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * epsilon))
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hREven : Even R)
    (hdHigh : ¬2 * quadraticDefect K (-epsilon) ≤
      (Int.toNat
        (2 * (ramificationIndex K : Int) - R) : ℕ∞))
    (hTlow : 2 * (ramificationIndex K : Int) < T) :
    principalUnitSquareClassSubgroup K (Int.toNat ((R + T) / 2)) ≤
      beliSpinorGroupRepresentative K
        (uniformizerPowerUnit K R * epsilon) := by
  have hbase := principalUnitSquareClassSubgroup_halfOrder_add_e_le_spinor
    (K := K) R epsilon hepsilon ha hRupper hREven hdHigh
  apply (principalUnitSquareClassSubgroup_anti K ?_).trans hbase
  apply Int.toNat_le_toNat
  omega

/-- A positive odd defect strictly complementary to `a` can be represented
by a valuation unit with Hilbert sign `+1` against `a`.  This is the exact
unit-valued choice used in the multiplier branches of Section 5. -/
theorem exists_valuationUnit_defect_eq_odd_hilbert_one_of_sum_lt
    (a : Kˣ) (m : Nat) (hmPos : 0 < m) (hmOdd : Odd m)
    (hmLt : m < 2 * ramificationIndex K)
    (hsum : quadraticDefect K a + (m : ℕ∞) <
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    ∃ z : valuationUnitSubgroup K,
      quadraticDefect K (z : Kˣ) = (m : ℕ∞) ∧
        hilbertSymbol K a (z : Kˣ) = 1 := by
  rcases exists_unit_quadraticDefect_eq_odd
      (K := K) m hmPos hmOdd hmLt with ⟨reference, hrefUnit, hrefDefect⟩
  have hsumRef : quadraticDefect K a + quadraticDefect K reference <
      ((2 * ramificationIndex K : Nat) : ℕ∞) := by
    rwa [hrefDefect]
  by_cases hres : BONG.HasResidueFieldMoreThanTwoElements (K := K)
  · have hnot : ¬BONG.IsZeroTwoEDefectPair (K := K) a reference := by
      intro hzero
      rcases hzero with hzero | hzero
      · rw [hzero.1, hzero.2] at hsumRef
        simpa using hsumRef
      · rw [hzero.1] at hsumRef
        exact (not_lt_of_ge (self_le_add_right _ _)) hsumRef
    rcases BONG.beli2019Lemma82_ii_unit hres a reference hrefUnit hnot with
      ⟨u, hu, huDefect, huHilbert⟩
    exact ⟨⟨u, hu⟩, huDefect.trans hrefDefect, huHilbert⟩
  · have hne : quadraticDefect K a + quadraticDefect K reference ≠
        ((2 * ramificationIndex K : Nat) : ℕ∞) :=
      ne_of_lt hsumRef
    rcases BONG.beli2019Lemma82_iii_unit hres a reference hrefUnit hne with
      ⟨u, hu, huDefect, huHilbert⟩
    exact ⟨⟨u, hu⟩, huDefect.trans hrefDefect, huHilbert⟩

/-- Corollary 3.15(i) for a parameter and its valuation-unit twist.  The
product of the two normalized unit parts differs from the twisting unit by a
square, so its defect is exactly the prescribed defect of the twist. -/
theorem principalUnit_order_sub_twoE_add_defect_le_spinor_sup_twist
    (p : Kˣ) (zeta : valuationUnitSubgroup K) (m : Nat)
    (hpAdmissible : BONG.IsBinaryParameterAdmissible p)
    (htwistAdmissible : BONG.IsBinaryParameterAdmissible
      ((zeta : Kˣ) * p))
    (hTlow : 2 * (ramificationIndex K : Int) < ordUnit K p)
    (hThigh : ordUnit K p ≤ 4 * (ramificationIndex K : Int))
    (hzetaDefect : quadraticDefect K (zeta : Kˣ) = (m : ℕ∞)) :
    principalUnitSquareClassSubgroup K
        (Int.toNat
          (ordUnit K p - 2 * (ramificationIndex K : Int) + (m : Int))) ≤
      beliSpinorGroupRepresentative K p ⊔
        beliSpinorGroupRepresentative K ((zeta : Kˣ) * p) := by
  let T : Int := ordUnit K p
  let epsilon : Kˣ := normalizedUnitPart K p
  let eta : Kˣ := (zeta : Kˣ) * epsilon
  have hepsilon : IsValuationUnit K (epsilon : K) :=
    normalizedUnitPart_isValuationUnit K p
  have heta : IsValuationUnit K (eta : K) := by
    change ord K (((zeta : Kˣ) : K) * (epsilon : K)) = 0
    rw [ord_mul, zeta.property, hepsilon]
    simp
  have hbase : uniformizerPowerUnit K T * epsilon = p := by
    simpa only [T, epsilon] using uniformizerPower_mul_normalizedUnitPart K p
  have htwist : uniformizerPowerUnit K T * eta = (zeta : Kˣ) * p := by
    dsimp only [eta]
    rw [← hbase]
    ac_rfl
  have hproduct : epsilon * eta = (zeta : Kˣ) * epsilon ^ 2 := by
    dsimp only [eta]
    simp only [pow_two]
    ac_rfl
  have hproductDefect : quadraticDefect K (epsilon * eta) = (m : ℕ∞) := by
    rw [hproduct, quadraticDefect_mul_square, hzetaDefect]
  have hcor := beliSpinorGroupRepresentative_sup_of_two_e_lt
    (K := K) T epsilon eta hepsilon heta
      (hbase.symm ▸ hpAdmissible) (htwist.symm ▸ htwistAdmissible)
      (by simpa only [T] using hTlow) (by simpa only [T] using hThigh)
  rw [hbase, htwist, hproductDefect] at hcor
  have hmFinite : (m : ℕ∞) ≠ ⊤ := ENat.coe_ne_top m
  have hfactor : beliLemma314CongruenceFactor (K := K)
        (T - 2 * (ramificationIndex K : Int)) (m : ℕ∞) =
      principalUnitSquareClassSubgroup K
        (Int.toNat
          (T - 2 * (ramificationIndex K : Int) + (m : Int))) := by
    rw [beliLemma314CongruenceFactor_of_ne_top
      (K := K) _ _ hmFinite]
    simp
  have hle : beliLemma314CongruenceFactor (K := K)
        (T - 2 * (ramificationIndex K : Int)) (m : ℕ∞) ≤
      cyclicSquareClassSubgroup K (epsilon * eta) ⊔
          beliLemma314CongruenceFactor (K := K)
            (T - 2 * (ramificationIndex K : Int)) (m : ℕ∞) ⊔
        beliSpinorGroupRepresentative K p :=
    (le_sup_right : _ ≤
      cyclicSquareClassSubgroup K (epsilon * eta) ⊔
        beliLemma314CongruenceFactor (K := K)
          (T - 2 * (ramificationIndex K : Int)) (m : ℕ∞)) |>.trans
      le_sup_left
  rw [← hcor] at hle
  simpa only [T, hfactor] using hle

/-- Corollary 3.15(ii) for an even-order parameter and a valuation-unit
twist.  The product of normalized unit parts has the prescribed defect, so
the printed factor has depth `T/2 + m - e`. -/
theorem principalUnit_halfOrder_add_defect_sub_e_le_spinor_sup_twist
    (p : Kˣ) (zeta : valuationUnitSubgroup K) (m : Nat)
    (hpAdmissible : BONG.IsBinaryParameterAdmissible p)
    (htwistAdmissible : BONG.IsBinaryParameterAdmissible
      ((zeta : Kˣ) * p))
    (hTupper : ordUnit K p ≤ 2 * (ramificationIndex K : Int))
    (hTEven : Even (ordUnit K p))
    (hpHigh : ¬2 * beliParameterDefect K p ≤
      (beliDefectCutoff K p : ℕ∞))
    (htwistHigh : ¬2 * beliParameterDefect K ((zeta : Kˣ) * p) ≤
      (beliDefectCutoff K ((zeta : Kˣ) * p) : ℕ∞))
    (hzetaDefect : quadraticDefect K (zeta : Kˣ) = (m : ℕ∞)) :
    principalUnitSquareClassSubgroup K
        (Int.toNat
          (ordUnit K p / 2 + (m : Int) -
            (ramificationIndex K : Int))) ≤
      beliSpinorGroupRepresentative K p ⊔
        beliSpinorGroupRepresentative K ((zeta : Kˣ) * p) := by
  let T : Int := ordUnit K p
  let epsilon : Kˣ := normalizedUnitPart K p
  let eta : Kˣ := (zeta : Kˣ) * epsilon
  have hepsilon : IsValuationUnit K (epsilon : K) :=
    normalizedUnitPart_isValuationUnit K p
  have heta : IsValuationUnit K (eta : K) := by
    change ord K (((zeta : Kˣ) : K) * (epsilon : K)) = 0
    rw [ord_mul, zeta.property, hepsilon]
    simp
  have hbase : uniformizerPowerUnit K T * epsilon = p := by
    simpa only [T, epsilon] using uniformizerPower_mul_normalizedUnitPart K p
  have htwist : uniformizerPowerUnit K T * eta = (zeta : Kˣ) * p := by
    dsimp only [eta]
    rw [← hbase]
    ac_rfl
  have htwistOrder : ordUnit K ((zeta : Kˣ) * p) = T := by
    rw [ordUnit_mul, (isValuationUnit_iff_ordUnit_eq_zero K
      (zeta : Kˣ)).1 zeta.property]
    simp only [zero_add, T]
  have hpDefect : beliParameterDefect K p =
      quadraticDefect K (-epsilon) := by
    have h := beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
      (K := K) T epsilon hepsilon (by simpa only [T] using hTEven)
    rwa [hbase] at h
  have htwistEven : Even (ordUnit K ((zeta : Kˣ) * p)) := by
    rwa [htwistOrder]
  have htwistDefect : beliParameterDefect K ((zeta : Kˣ) * p) =
      quadraticDefect K (-eta) := by
    have h := beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
      (K := K) T eta heta (by simpa only [T] using hTEven)
    rwa [htwist] at h
  have hdEpsilon : ¬2 * quadraticDefect K (-epsilon) ≤
      (Int.toNat
        (2 * (ramificationIndex K : Int) - T) : ℕ∞) := by
    intro hle
    apply hpHigh
    rw [hpDefect]
    unfold beliDefectCutoff
    simpa only [T] using hle
  have hdEta : ¬2 * quadraticDefect K (-eta) ≤
      (Int.toNat
        (2 * (ramificationIndex K : Int) - T) : ℕ∞) := by
    intro hle
    apply htwistHigh
    rw [htwistDefect]
    unfold beliDefectCutoff
    rw [htwistOrder]
    exact hle
  have hproduct : epsilon * eta = (zeta : Kˣ) * epsilon ^ 2 := by
    dsimp only [eta]
    simp only [pow_two]
    ac_rfl
  have hproductDefect : quadraticDefect K (epsilon * eta) = (m : ℕ∞) := by
    rw [hproduct, quadraticDefect_mul_square, hzetaDefect]
  have hcor := beliSpinorGroupRepresentative_sup_of_even_order
    (K := K) T epsilon eta hepsilon heta
      (hbase.symm ▸ hpAdmissible) (htwist.symm ▸ htwistAdmissible)
      (by simpa only [T] using hTupper) (by simpa only [T] using hTEven)
      hdEpsilon hdEta
  rw [hbase, htwist, hproductDefect] at hcor
  have hmFinite : (m : ℕ∞) ≠ ⊤ := ENat.coe_ne_top m
  have hfactor : beliCorollary315EvenCongruenceFactor (K := K) T (m : ℕ∞) =
      principalUnitSquareClassSubgroup K
        (Int.toNat (T / 2 + (m : Int) -
          (ramificationIndex K : Int))) := by
    rw [beliCorollary315EvenCongruenceFactor_of_ne_top
      (K := K) T (m : ℕ∞) hmFinite]
    simp
  have hle : beliCorollary315EvenCongruenceFactor (K := K) T (m : ℕ∞) ≤
      beliCorollary315EvenCongruenceFactor (K := K) T (m : ℕ∞) ⊔
        beliSpinorGroupRepresentative K p := le_sup_left
  rw [← hcor] at hle
  simpa only [T, hfactor] using hle

end Dyadic

namespace BONG

/-- Adjacent parameters are preserved, with the adjacent index reversed,
by a reverse-dual BONG. -/
theorem theoremOne_reverseDual_adjacentParameter
    {n : Nat} (b : BONG V q L (n + 1))
    (d : BONG V q (Lattice.dualLattice q L) (n + 1))
    (hvalues : ∀ j, d.value j = ((b.valueUnit (Fin.rev j))⁻¹ : K))
    (j : Fin n) :
    d.adjacentParameter j.castSucc (by simpa using j.isLt) =
      b.adjacentParameter (Fin.rev j).castSucc
        (by simpa using (Fin.rev j).isLt) := by
  have hvalueUnit : ∀ k,
      d.valueUnit k = (b.valueUnit (Fin.rev k))⁻¹ := by
    intro k
    apply Units.ext
    exact hvalues k
  have hrevSucc : Fin.rev j.succ = (Fin.rev j).castSucc := by
    apply Fin.ext
    simp [Fin.rev]
  have hrevCast : Fin.rev j.castSucc = (Fin.rev j).succ := by
    apply Fin.ext
    simp [Fin.rev]
    omega
  unfold adjacentParameter
  change d.valueUnit j.succ / d.valueUnit j.castSucc =
    b.valueUnit (Fin.rev j).succ / b.valueUnit (Fin.rev j).castSucc
  rw [hvalueUnit j.succ, hvalueUnit j.castSucc, hrevSucc, hrevCast]
  simp [div_eq_mul_inv, mul_comm]

/-- Adjacent order gaps are preserved with reversed adjacent index under
reverse duality. -/
theorem theoremOne_reverseDual_orderGap
    {n : Nat} (b : BONG V q L (n + 1))
    (d : BONG V q (Lattice.dualLattice q L) (n + 1))
    (horders : ∀ j, d.order j = -b.order (Fin.rev j))
    (j : Fin n) :
    d.order j.succ - d.order j.castSucc =
      b.order (Fin.rev j).succ - b.order (Fin.rev j).castSucc := by
  have hrevSucc : Fin.rev j.succ = (Fin.rev j).castSucc := by
    apply Fin.ext
    simp [Fin.rev]
  have hrevCast : Fin.rev j.castSucc = (Fin.rev j).succ := by
    apply Fin.ext
    simp [Fin.rev]
    omega
  rw [horders j.succ, horders j.castSucc, hrevSucc, hrevCast]
  ring

/-- In the even branch, the normalized adjacent defect used by Property B
is preserved under reverse duality. -/
theorem theoremOne_reverseDual_normalizedAdjacentDefectOrder
    {n : Nat} (b : BONG V q L (n + 1))
    (d : BONG V q (Lattice.dualLattice q L) (n + 1))
    (hvalues : ∀ j, d.value j = ((b.valueUnit (Fin.rev j))⁻¹ : K))
    (horders : ∀ j, d.order j = -b.order (Fin.rev j))
    (j : Fin n)
    (heven : Even (d.order j.succ - d.order j.castSucc)) :
    d.normalizedAdjacentDefectOrder j =
      b.normalizedAdjacentDefectOrder (Fin.rev j) := by
  have hgap := b.theoremOne_reverseDual_orderGap d horders j
  have hevenB : Even
      (b.order (Fin.rev j).succ - b.order (Fin.rev j).castSucc) := by
    rwa [← hgap]
  have hparameter := b.theoremOne_reverseDual_adjacentParameter d hvalues j
  have hd :=
    d.quadraticDefect_negative_adjacentParameter_eq_normalizedProduct_of_even
      j heven
  have hb :=
    b.quadraticDefect_negative_adjacentParameter_eq_normalizedProduct_of_even
      (Fin.rev j) hevenB
  unfold normalizedAdjacentDefectOrder
  congr 1
  calc
    quadraticDefect K (d.normalizedAdjacentProduct j) =
        quadraticDefect K
          (-(d.adjacentParameter j.castSucc (by simpa using j.isLt))) :=
      hd.symm
    _ = quadraticDefect K
          (-(b.adjacentParameter (Fin.rev j).castSucc
            (by simpa using (Fin.rev j).isLt))) := by rw [hparameter]
    _ = quadraticDefect K (b.normalizedAdjacentProduct (Fin.rev j)) := hb

/-- Property B is invariant under reversal and lattice duality in rank
three.  Endpoint quantifiers are checked explicitly at the two adjacent
indices. -/
theorem theoremOne_reverseDual_hasPropertyB
    (b : BONG V q L 3) (hB : b.HasPropertyB)
    (d : BONG V q (Lattice.dualLattice q L) 3)
    (hvalues : ∀ j, d.value j = ((b.valueUnit (Fin.rev j))⁻¹ : K))
    (horders : ∀ j, d.order j = -b.order (Fin.rev j)) :
    d.HasPropertyB := by
  constructor
  · intro i hi
    have hiZero : i = (0 : Fin 3) := by
      apply Fin.ext
      change i.val = 0
      omega
    subst i
    have hbA := hB.hasPropertyA (0 : Fin 3) (by norm_num)
    have hbA' : b.order (0 : Fin 3) < b.order (2 : Fin 3) := by
      simpa using hbA
    have hd0 : d.order (0 : Fin 3) = -b.order (2 : Fin 3) := by
      simpa [Fin.rev] using horders (0 : Fin 3)
    have hd2 : d.order (2 : Fin 3) = -b.order (0 : Fin 3) := by
      simpa [Fin.rev] using horders (2 : Fin 3)
    simpa using (show d.order (0 : Fin 3) < d.order (2 : Fin 3) by omega)
  · intro i htriggerD
    have hgap := b.theoremOne_reverseDual_orderGap d horders i
    have htriggerB : b.propertyBTrigger (Fin.rev i) := by
      unfold propertyBTrigger at htriggerD ⊢
      rcases htriggerD with hodd | heven
      · left
        constructor
        · simpa only [hgap] using hodd.1
        · simpa only [hgap] using hodd.2
      · right
        have hdefect :=
          b.theoremOne_reverseDual_normalizedAdjacentDefectOrder
            d hvalues horders i heven.1
        constructor
        · simpa only [hgap] using heven.1
        · simpa only [hgap, hdefect] using heven.2
    fin_cases i
    · have htriggerOne : b.propertyBTrigger (1 : Fin 2) := by
        simpa [Fin.rev] using htriggerB
      have hbNeighbors := hB.2 (1 : Fin 2) htriggerOne
      constructor
      · intro j hj
        norm_num at hj
      · intro k hk
        have hkTwo : k = (2 : Fin 3) := by
          apply Fin.ext
          change k.val = 2
          omega
        subst k
        have hbDeep := hbNeighbors.1 (0 : Fin 3) (by norm_num)
        have hbDeep' : 2 * (ramificationIndex K : Int) + 1 ≤
            b.order (1 : Fin 3) - b.order (0 : Fin 3) := by
          simpa using hbDeep
        have hd1 : d.order (1 : Fin 3) = -b.order (1 : Fin 3) := by
          simpa [Fin.rev] using horders (1 : Fin 3)
        have hd2 : d.order (2 : Fin 3) = -b.order (0 : Fin 3) := by
          simpa [Fin.rev] using horders (2 : Fin 3)
        simpa using (show 2 * (ramificationIndex K : Int) + 1 ≤
            d.order (2 : Fin 3) - d.order (1 : Fin 3) by omega)
    · have htriggerZero : b.propertyBTrigger (0 : Fin 2) := by
        simpa [Fin.rev] using htriggerB
      have hbNeighbors := hB.2 (0 : Fin 2) htriggerZero
      constructor
      · intro j hj
        have hjZero : j = (0 : Fin 3) := by
          apply Fin.ext
          change j.val = 0
          omega
        subst j
        have hbDeep := hbNeighbors.2 (2 : Fin 3) (by norm_num)
        have hbDeep' : 2 * (ramificationIndex K : Int) + 1 ≤
            b.order (2 : Fin 3) - b.order (1 : Fin 3) := by
          simpa using hbDeep
        have hd0 : d.order (0 : Fin 3) = -b.order (2 : Fin 3) := by
          simpa [Fin.rev] using horders (0 : Fin 3)
        have hd1 : d.order (1 : Fin 3) = -b.order (1 : Fin 3) := by
          simpa [Fin.rev] using horders (1 : Fin 3)
        simpa using (show 2 * (ramificationIndex K : Int) + 1 ≤
            d.order (1 : Fin 3) - d.order (0 : Fin 3) by omega)
      · intro k hk
        norm_num at hk
        have hklt := k.isLt
        omega

/-- The target two-step depth is unchanged by reverse duality in rank
three. -/
theorem theoremOne_reverseDual_twoStepDepth
    (b : BONG V q L 3)
    (d : BONG V q (Lattice.dualLattice q L) 3)
    (horders : ∀ j, d.order j = -b.order (Fin.rev j)) :
    d.theoremOneTwoStepDepth 0 = b.theoremOneTwoStepDepth 0 := by
  unfold theoremOneTwoStepDepth
  change Int.toNat ((d.order (2 : Fin 3) - d.order (0 : Fin 3)) / 2) =
    Int.toNat ((b.order (2 : Fin 3) - b.order (0 : Fin 3)) / 2)
  have hd0 : d.order (0 : Fin 3) = -b.order (2 : Fin 3) := by
    simpa [Fin.rev] using horders (0 : Fin 3)
  have hd2 : d.order (2 : Fin 3) = -b.order (0 : Fin 3) := by
    simpa [Fin.rev] using horders (2 : Fin 3)
  rw [hd0, hd2]
  congr 1
  ring_nf

/-- The first adjacent gap of a ternary reverse dual is the second gap of the
original BONG. -/
theorem theoremOne_reverseDual_leftGap
    (b : BONG V q L 3)
    (d : BONG V q (Lattice.dualLattice q L) 3)
    (horders : ∀ j, d.order j = -b.order (Fin.rev j)) :
    d.order (1 : Fin 3) - d.order (0 : Fin 3) =
      b.order (2 : Fin 3) - b.order (1 : Fin 3) := by
  simpa [Fin.rev] using
    b.theoremOne_reverseDual_orderGap d horders (0 : Fin 2)

/-- The second adjacent gap of a ternary reverse dual is the first gap of the
original BONG. -/
theorem theoremOne_reverseDual_rightGap
    (b : BONG V q L 3)
    (d : BONG V q (Lattice.dualLattice q L) 3)
    (horders : ∀ j, d.order j = -b.order (Fin.rev j)) :
    d.order (2 : Fin 3) - d.order (1 : Fin 3) =
      b.order (1 : Fin 3) - b.order (0 : Fin 3) := by
  simpa [Fin.rev] using
    b.theoremOne_reverseDual_orderGap d horders (1 : Fin 2)

/-- The first adjacent parameter of a ternary reverse dual is the second
parameter of the original BONG. -/
theorem theoremOne_reverseDual_leftParameter
    (b : BONG V q L 3)
    (d : BONG V q (Lattice.dualLattice q L) 3)
    (hvalues : ∀ j, d.value j = ((b.valueUnit (Fin.rev j))⁻¹ : K)) :
    d.adjacentParameter (0 : Fin 3) (by norm_num) =
      b.adjacentParameter (1 : Fin 3) (by norm_num) := by
  simpa [Fin.rev] using
    b.theoremOne_reverseDual_adjacentParameter d hvalues (0 : Fin 2)

/-- The second adjacent parameter of a ternary reverse dual is the first
parameter of the original BONG. -/
theorem theoremOne_reverseDual_rightParameter
    (b : BONG V q L 3)
    (d : BONG V q (Lattice.dualLattice q L) 3)
    (hvalues : ∀ j, d.value j = ((b.valueUnit (Fin.rev j))⁻¹ : K)) :
    d.adjacentParameter (1 : Fin 3) (by norm_num) =
      b.adjacentParameter (0 : Fin 3) (by norm_num) := by
  simpa [Fin.rev] using
    b.theoremOne_reverseDual_adjacentParameter d hvalues (1 : Fin 2)

/-- A congruence inclusion proved on a reverse-dual ternary BONG transports
back to the original lattice, since integral dual lattices have the same
spinor-norm image. -/
theorem theoremOne_congruence_le_of_reverseDual
    (b : BONG V q L 3)
    (d : BONG V q (Lattice.dualLattice q L) 3)
    (hdepth : d.theoremOneTwoStepDepth 0 = b.theoremOneTwoStepDepth 0)
    (hdual : beliCongruenceSquareClassSubgroup K
        (d.theoremOneTwoStepDepth 0) ≤
      Lattice.spinorNormImageSubgroup
        (q := q) (L := Lattice.dualLattice q L)) :
    beliCongruenceSquareClassSubgroup K (b.theoremOneTwoStepDepth 0) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
  rw [← hdepth]
  intro z hz
  have hzDual := hdual hz
  change z ∈ Lattice.spinorNormImage
      (q := q) (L := Lattice.dualLattice q L) at hzDual
  change z ∈ Lattice.spinorNormImage (q := q) (L := L)
  rwa [Lattice.spinorNormImage_dualLattice] at hzDual

/-- It is enough to prove the ternary congruence inclusion on one of the
explicit reverse-dual BONGs.  This packages the Section 4 construction so the
right-oriented cases in Section 5 can reuse the left-oriented calculation. -/
theorem theoremOne_congruence_le_via_reverseDual
    [BONGStructuralLaws.{u, v} K]
    (b : BONG V q L 3) (hB : b.HasPropertyB)
    (hdual : ∀
      (d : BONG V q (Lattice.dualLattice q L) 3)
      (hvalues : ∀ j,
        d.value j = ((b.valueUnit (Fin.rev j))⁻¹ : K))
      (horders : ∀ j, d.order j = -b.order (Fin.rev j)),
        d.HasPropertyB →
          beliCongruenceSquareClassSubgroup K
              (d.theoremOneTwoStepDepth 0) ≤
            Lattice.spinorNormImageSubgroup
              (q := q) (L := Lattice.dualLattice q L)) :
    beliCongruenceSquareClassSubgroup K (b.theoremOneTwoStepDepth 0) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
  let source : BONG.GoodBONG q L 3 := ⟨b, hB.isGood⟩
  rcases source.exists_reverseDual_with_values with
    ⟨dual, _hvectors, hvalues, horders⟩
  let d : BONG V q (Lattice.dualLattice q L) 3 := dual.toBONG
  have hdB : d.HasPropertyB :=
    b.theoremOne_reverseDual_hasPropertyB hB d hvalues horders
  have hdepth : d.theoremOneTwoStepDepth 0 =
      b.theoremOneTwoStepDepth 0 :=
    b.theoremOne_reverseDual_twoStepDepth d horders
  exact b.theoremOne_congruence_le_of_reverseDual d hdepth
    (hdual d hvalues horders hdB)

/-- The even low-defect alternative in Definition 6 is exactly the even
branch of Property B's trigger.  This conversion is kept explicit because
the former uses the doubled natural cutoff `2e-R`, while the latter uses the
rational cutoff `e-R/2`. -/
theorem propertyBTrigger_of_even_low
    {n : Nat} (b : BONG V q L (n + 1)) (i : Fin n)
    (heven : Even (b.order i.succ - b.order i.castSucc))
    (hupper : b.order i.succ - b.order i.castSucc ≤
      2 * (ramificationIndex K : Int))
    (hlow : 2 * beliParameterDefect K
        (b.adjacentParameter i.castSucc (by simpa using i.isLt)) ≤
      (beliDefectCutoff K
        (b.adjacentParameter i.castSucc (by simpa using i.isLt)) : ℕ∞)) :
    b.propertyBTrigger i := by
  let gap : Int := b.order i.succ - b.order i.castSucc
  let a : Kˣ := b.adjacentParameter i.castSucc (by simpa using i.isLt)
  have haOrder : ordUnit K a = gap := by
    dsimp only [a, gap]
    rw [b.ordUnit_adjacentParameter]
    congr 2
  have hfinite : beliParameterDefect K a ≠ ⊤ := by
    intro htop
    have h : 2 * beliParameterDefect K a ≤
        (beliDefectCutoff K a : ℕ∞) := by
      simpa only [a] using hlow
    rw [htop] at h
    simp at h
  let d : Nat := (beliParameterDefect K a).toNat
  have hdefect : beliParameterDefect K a = (d : ℕ∞) := by
    simpa only [d] using (ENat.coe_toNat hfinite).symm
  have hcutNonneg : 0 ≤
      2 * (ramificationIndex K : Int) - gap := by
    simpa only [gap] using sub_nonneg.mpr hupper
  have hcutCast : (beliDefectCutoff K a : Int) =
      2 * (ramificationIndex K : Int) - gap := by
    unfold beliDefectCutoff
    rw [haOrder, Int.toNat_of_nonneg hcutNonneg]
  have hlowNat : 2 * d ≤ beliDefectCutoff K a := by
    have hENat : (2 : ℕ∞) * (d : ℕ∞) ≤
        (beliDefectCutoff K a : ℕ∞) := by
      have h : 2 * beliParameterDefect K a ≤
          (beliDefectCutoff K a : ℕ∞) := by
        simpa only [a] using hlow
      rwa [hdefect] at h
    exact_mod_cast hENat
  have hlowInt : 2 * (d : Int) ≤
      2 * (ramificationIndex K : Int) - gap := by
    have hcast : (2 * d : Int) ≤ (beliDefectCutoff K a : Int) := by
      exact_mod_cast hlowNat
    rwa [hcutCast] at hcast
  have hnormalizedDefect : quadraticDefect K
        (b.normalizedAdjacentProduct i) = (d : ℕ∞) := by
    have hraw :=
      b.quadraticDefect_negative_adjacentParameter_eq_normalizedProduct_of_even
        i heven
    unfold beliParameterDefect at hdefect
    rw [← hraw]
    simpa only [a] using hdefect
  unfold propertyBTrigger
  right
  constructor
  · simpa only [gap] using heven
  · unfold normalizedAdjacentDefectOrder
    rw [hnormalizedDefect]
    change (((d : ℚ) : WithTop ℚ)) ≤
      ((((ramificationIndex K : ℚ) -
        ((gap : Int) : ℚ) / 2) : ℚ) : WithTop ℚ)
    have hq : (d : ℚ) ≤
        (ramificationIndex K : ℚ) - (gap : ℚ) / 2 := by
      have hevenGap : Even gap := by exact heven
      rcases hevenGap with ⟨r, hr⟩
      rw [hr] at hlowInt ⊢
      norm_num at hlowInt ⊢
      have hz : (d : Int) ≤ (ramificationIndex K : Int) - r := by
        omega
      exact_mod_cast hz
    exact_mod_cast hq

/-- Property B makes the ternary two-step depth positive, so Beli's
depth-zero convention is not active in the nontrivial branch. -/
theorem theoremOneTwoStepDepth_pos_of_propertyB
    (b : BONG V q L 3) (hB : b.HasPropertyB) :
    0 < b.theoremOneTwoStepDepth 0 := by
  have htwo := hB.twoStep_add_two_le (0 : Fin 3) (by norm_num)
  unfold theoremOneTwoStepDepth
  change 0 < Int.toNat
    ((b.order (2 : Fin 3) - b.order (0 : Fin 3)) / 2)
  have htwo' : b.order (0 : Fin 3) + 2 ≤ b.order (2 : Fin 3) := by
    simpa using htwo
  have hgap : 2 ≤ b.order (2 : Fin 3) - b.order (0 : Fin 3) := by
    omega
  have hdiv : 1 ≤
      (b.order (2 : Fin 3) - b.order (0 : Fin 3)) / 2 := by
    omega
  have hnonneg : 0 ≤
      (b.order (2 : Fin 3) - b.order (0 : Fin 3)) / 2 := by
    omega
  have hnat : 1 ≤ Int.toNat
      ((b.order (2 : Fin 3) - b.order (0 : Fin 3)) / 2) := by
    exact_mod_cast (show (1 : Int) ≤
        (Int.toNat
          ((b.order (2 : Fin 3) - b.order (0 : Fin 3)) / 2) : Int) by
      rw [Int.toNat_of_nonneg hnonneg]
      exact hdiv)
  exact hnat

/-- The rank-three congruence inclusion is immediate when property B fails,
because Lemma 4.11 makes the integral spinor image the whole square-class
group. -/
theorem congruence_le_spinorNormImage_of_not_propertyB
    (b : BONG V q L 3) (hA : b.HasPropertyA)
    (hnotB : ¬b.HasPropertyB) :
    beliCongruenceSquareClassSubgroup K (b.theoremOneTwoStepDepth 0) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
  letI : BeliLemma411Laws.{u, v} K := beliLemma411LawsProved
  have himage : Lattice.spinorNormImage (q := q) (L := L) = Set.univ :=
    b.beliLemma411 hA hnotB
  intro c _hc
  change c ∈ Lattice.spinorNormImage (q := q) (L := L)
  rw [himage]
  trivial

/-- In the property-B branch, the desired group is the ordinary principal
unit square-class layer. -/
theorem congruence_eq_principalUnit_of_propertyB
    (b : BONG V q L 3) (hB : b.HasPropertyB) :
    beliCongruenceSquareClassSubgroup K (b.theoremOneTwoStepDepth 0) =
      principalUnitSquareClassSubgroup K (b.theoremOneTwoStepDepth 0) :=
  beliCongruenceSquareClassSubgroup_of_pos K
    (b.theoremOneTwoStepDepth_pos_of_propertyB hB)

/-- Integer form of the ternary depth.  Property B supplies the positivity
needed to remove `Int.toNat`. -/
theorem theoremOneTwoStepDepth_cast_of_propertyB
    (b : BONG V q L 3) (hB : b.HasPropertyB) :
    (b.theoremOneTwoStepDepth 0 : Int) =
      (b.order (2 : Fin 3) - b.order (0 : Fin 3)) / 2 := by
  have htwo := hB.twoStep_add_two_le (0 : Fin 3) (by norm_num)
  have htwo' : b.order (0 : Fin 3) + 2 ≤ b.order (2 : Fin 3) := by
    simpa using htwo
  unfold theoremOneTwoStepDepth
  change (Int.toNat
      ((b.order (2 : Fin 3) - b.order (0 : Fin 3)) / 2) : Int) = _
  rw [Int.toNat_of_nonneg]
  omega

/-- The spinor group of either adjacent binary segment is contained in the
integral spinor image of the ternary lattice. -/
theorem adjacentSpinorGroup_le_spinorNormImage
    [BeliLemma49Laws.{u, v} K]
    [BinarySpinorLocalLaws.{u, v} K]
    (b : BONG V q L 3) (hgood : b.IsGood)
    (i : Fin 3) (hi : i.val + 1 < 3) :
    beliSpinorGroupRepresentative K (b.adjacentParameter i hi) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
  intro c hc
  change c ∈ Lattice.spinorNormImage (q := q) (L := L)
  apply b.beliCorollary410_ii hgood i hi
  unfold adjacentUnitSquareClass
  rwa [beliSpinorGroup_unitSquareClass]

/-- A unit class from the first binary norm-generator group may twist the
second adjacent parameter.  Corollary 3.15(i) then places the corresponding
principal layer in the ternary spinor image. -/
theorem principalUnit_rightTwist_le_spinorNormImage
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BinarySpinorLocalLaws.{u, v} K]
    (b : BONG V q L 3) (hgood : b.IsGood)
    (zeta : valuationUnitSubgroup K) (m : Nat)
    (hzeta : valuationUnitClassHom K zeta ∈
      beliNormGeneratorGroup K
        (b.adjacentParameter (0 : Fin 3) (by norm_num)))
    (hzetaDefect : quadraticDefect K (zeta : Kˣ) = (m : ℕ∞))
    (hTlow : 2 * (ramificationIndex K : Int) <
      b.order (2 : Fin 3) - b.order (1 : Fin 3))
    (hThigh : b.order (2 : Fin 3) - b.order (1 : Fin 3) ≤
      4 * (ramificationIndex K : Int)) :
    principalUnitSquareClassSubgroup K
        (Int.toNat
          (b.order (2 : Fin 3) - b.order (1 : Fin 3) -
            2 * (ramificationIndex K : Int) + (m : Int))) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
  let c : Kˣ := b.adjacentParameter (1 : Fin 3) (by norm_num)
  have hzetaNeighbor :
      ((∃ hleft : 1 ≤ (1 : Fin 3).val,
          valuationUnitClassHom K zeta ∈ beliNormGeneratorGroup K
            (b.valueUnit (1 : Fin 3) /
              b.valueUnit ⟨(1 : Fin 3).val - 1, by omega⟩)) ∨
        (∃ hright : (1 : Fin 3).val + 2 < 3,
          valuationUnitClassHom K zeta ∈ beliNormGeneratorGroup K
            (b.valueUnit ⟨(1 : Fin 3).val + 2, hright⟩ /
              b.valueUnit ⟨(1 : Fin 3).val + 1, by norm_num⟩))) := by
    left
    refine ⟨by norm_num, ?_⟩
    have hparameter :
        b.valueUnit (1 : Fin 3) /
            b.valueUnit ⟨(1 : Fin 3).val - 1, by omega⟩ =
          b.adjacentParameter (0 : Fin 3) (by norm_num) := by
      unfold adjacentParameter
      congr 2
    rw [hparameter]
    exact hzeta
  have hcAdmissible : IsBinaryParameterAdmissible c := by
    simpa only [c] using b.adjacentParameter_isBinaryParameterAdmissible
      (1 : Fin 3) (by norm_num)
  have htwistAdmissible : IsBinaryParameterAdmissible
      ((zeta : Kˣ) * c) := by
    simpa only [c] using
      b.isBinaryParameterAdmissible_mul_adjacentParameter_of_adjacentMultiplier
        hgood (1 : Fin 3) (by norm_num) zeta hzetaNeighbor
  have hcOrder : ordUnit K c =
      b.order (2 : Fin 3) - b.order (1 : Fin 3) := by
    dsimp only [c]
    rw [b.ordUnit_adjacentParameter]
    congr 2
  have hcor := principalUnit_order_sub_twoE_add_defect_le_spinor_sup_twist
    (K := K) c zeta m hcAdmissible htwistAdmissible
      (by rwa [hcOrder]) (by rwa [hcOrder]) hzetaDefect
  rw [hcOrder] at hcor
  have hcLe : beliSpinorGroupRepresentative K c ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
    simpa only [c] using b.adjacentSpinorGroup_le_spinorNormImage
      hgood (1 : Fin 3) (by norm_num)
  have htwistLe : beliSpinorGroupRepresentative K ((zeta : Kˣ) * c) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
    intro x hx
    change x ∈ Lattice.spinorNormImage (q := q) (L := L)
    apply b.twistedAdjacentSpinorGroup_subset_of_adjacentMultiplier
      hgood (1 : Fin 3) (by norm_num) zeta hzetaNeighbor
    rw [beliSpinorGroup_unitSquareClass]
    change x ∈ (beliSpinorGroupRepresentative K
      ((zeta : Kˣ) * c) : Set (SquareClass K))
    exact hx
  exact hcor.trans (sup_le hcLe htwistLe)

/-- Section 5(iv)(a): if both adjacent gaps are beyond `2e`, the target
depth is beyond `2e`, hence its principal-unit square-class factor is
trivial. -/
theorem congruence_le_spinorNormImage_of_propertyB_of_both_two_e_lt
    (b : BONG V q L 3) (hB : b.HasPropertyB)
    (hleft : 2 * (ramificationIndex K : Int) <
      b.order (1 : Fin 3) - b.order (0 : Fin 3))
    (hright : 2 * (ramificationIndex K : Int) <
      b.order (2 : Fin 3) - b.order (1 : Fin 3)) :
    beliCongruenceSquareClassSubgroup K (b.theoremOneTwoStepDepth 0) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
  rw [b.congruence_eq_principalUnit_of_propertyB hB]
  have hdepth : 2 * ramificationIndex K <
      b.theoremOneTwoStepDepth 0 := by
    have hcast := b.theoremOneTwoStepDepth_cast_of_propertyB hB
    exact_mod_cast (show
      (2 * ramificationIndex K : Int) <
          (b.theoremOneTwoStepDepth 0 : Int) by
        rw [hcast]
        omega)
  rw [principalUnitSquareClassSubgroup_eq_bot_of_two_mul_e_lt
    (K := K) (b.theoremOneTwoStepDepth 0) hdepth]
  exact bot_le

/-- Section 5(ii), even neighboring gap: the discriminant class belongs to
the even neighboring binary spinor group but not to the odd quadratic norm
hyperplane.  Hence the ternary spinor image is the full square-class group.
-/
theorem congruence_le_spinorNormImage_of_propertyB_of_left_odd_right_even
    [BeliLemma49Laws.{u, v} K]
    [BinarySpinorLocalLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K] [DyadicUnramifiedNormLaws K]
    (b : BONG V q L 3) (hB : b.HasPropertyB)
    (hleftOdd : Odd
      (b.order (1 : Fin 3) - b.order (0 : Fin 3)))
    (hleftUpper : b.order (1 : Fin 3) - b.order (0 : Fin 3) ≤
      2 * (ramificationIndex K : Int))
    (hrightEven : Even
      (b.order (2 : Fin 3) - b.order (1 : Fin 3))) :
    beliCongruenceSquareClassSubgroup K (b.theoremOneTwoStepDepth 0) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
  by_cases hdepth : 2 * ramificationIndex K <
      b.theoremOneTwoStepDepth 0
  · rw [b.congruence_eq_principalUnit_of_propertyB hB,
      principalUnitSquareClassSubgroup_eq_bot_of_two_mul_e_lt
        (K := K) (b.theoremOneTwoStepDepth 0) hdepth]
    exact bot_le
  · have hdepthUpper : b.theoremOneTwoStepDepth 0 ≤
        2 * ramificationIndex K := by omega
    have hleftPos : 0 <
        b.order (1 : Fin 3) - b.order (0 : Fin 3) := by
      exact b.adjacentOrderGap_pos_of_odd (0 : Fin 3) (by norm_num)
        hleftOdd
    have htrigger : b.propertyBTrigger (0 : Fin 2) := by
      unfold propertyBTrigger
      left
      constructor
      · simpa using (show
          b.order (1 : Fin 3) - b.order (0 : Fin 3) ≤
            2 * (ramificationIndex K : Int) + 1 by omega)
      · simpa using hleftOdd
    have hrightLower : 2 * (ramificationIndex K : Int) + 1 ≤
        b.order (2 : Fin 3) - b.order (1 : Fin 3) := by
      have h := (hB.2 (0 : Fin 2) htrigger).2 (2 : Fin 3) (by norm_num)
      simpa using h
    have htotalOdd : Odd
        (b.order (2 : Fin 3) - b.order (0 : Fin 3)) := by
      have hsum : b.order (2 : Fin 3) - b.order (0 : Fin 3) =
          (b.order (1 : Fin 3) - b.order (0 : Fin 3)) +
            (b.order (2 : Fin 3) - b.order (1 : Fin 3)) := by omega
      rw [hsum]
      exact hleftOdd.add_even hrightEven
    have htotalUpper : b.order (2 : Fin 3) - b.order (0 : Fin 3) ≤
        4 * (ramificationIndex K : Int) + 1 := by
      have hcast := b.theoremOneTwoStepDepth_cast_of_propertyB hB
      have hdepthUpperInt :
          (b.theoremOneTwoStepDepth 0 : Int) ≤
            2 * (ramificationIndex K : Int) := by exact_mod_cast hdepthUpper
      rw [hcast] at hdepthUpperInt
      rcases htotalOdd with ⟨m, hm⟩
      omega
    have hrightUpper :
        b.order (2 : Fin 3) - b.order (1 : Fin 3) ≤
          4 * (ramificationIndex K : Int) := by omega
    let a : Kˣ := b.adjacentParameter (0 : Fin 3) (by norm_num)
    let c : Kˣ := b.adjacentParameter (1 : Fin 3) (by norm_num)
    have haAdmissible : IsBinaryParameterAdmissible a :=
      b.adjacentParameter_isBinaryParameterAdmissible
        (0 : Fin 3) (by norm_num)
    have hcAdmissible : IsBinaryParameterAdmissible c :=
      b.adjacentParameter_isBinaryParameterAdmissible
        (1 : Fin 3) (by norm_num)
    have haOrder : ordUnit K a =
        b.order (1 : Fin 3) - b.order (0 : Fin 3) := by
      dsimp only [a]
      rw [b.ordUnit_adjacentParameter]
      congr 2
    have hcOrder : ordUnit K c =
        b.order (2 : Fin 3) - b.order (1 : Fin 3) := by
      dsimp only [c]
      rw [b.ordUnit_adjacentParameter]
      congr 2
    have haGroup : beliSpinorGroupRepresentative K a =
        quadraticNormSquareClassSubgroup K (-a) := by
      apply beliSpinorGroupRepresentative_eq_norm_of_odd_trigger
        (K := K) a haAdmissible
      · rwa [haOrder]
      · rw [haOrder]
        omega
    have haLe : beliSpinorGroupRepresentative K a ≤
        Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
      simpa only [a] using b.adjacentSpinorGroup_le_spinorNormImage
        hB.isGood (0 : Fin 3) (by norm_num)
    have hcLe : beliSpinorGroupRepresentative K c ≤
        Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
      simpa only [c] using b.adjacentSpinorGroup_le_spinorNormImage
        hB.isGood (1 : Fin 3) (by norm_num)
    let delta : Kˣ :=
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    have hdeltaC : squareClass K delta ∈
        beliSpinorGroupRepresentative K c := by
      apply discriminantSquareClass_mem_beliSpinorGroup_of_even_middle
        (K := K) c hcAdmissible
      · rwa [hcOrder]
      · rw [hcOrder]
        exact hrightLower
      · rw [hcOrder]
        exact hrightUpper
    have hdeltaNotA : squareClass K delta ∉
        quadraticNormSquareClassSubgroup K (-a) := by
      have hoddNeg : Odd (ordUnit K (-a)) := by
        simpa [haOrder] using hleftOdd
      have hne := hilbertSymbol_discriminant_ne_one_of_odd_order
        (K := K) (-a) hoddNeg
      rw [quadraticNormSquareClassSubgroup_eq_ker]
      intro hmem
      change squareClassHilbertCharacter K (-a) (squareClass K delta) = 1
        at hmem
      rw [squareClassHilbertCharacter_apply] at hmem
      apply hne
      rw [hilbertSymbol_comm]
      simpa only [delta] using hmem
    have htopGen : quadraticNormSquareClassSubgroup K (-a) ⊔
        cyclicSquareClassSubgroup K delta = ⊤ :=
      quadraticNorm_sup_cyclic_eq_top_of_not_mem
        (K := K) (-a) delta hdeltaNotA
    have hnormLe : quadraticNormSquareClassSubgroup K (-a) ≤
        Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
      rw [← haGroup]
      exact haLe
    have hdeltaGlobal : squareClass K delta ∈
        Lattice.spinorNormImageSubgroup (q := q) (L := L) :=
      hcLe hdeltaC
    have hcyclicLe : cyclicSquareClassSubgroup K delta ≤
        Lattice.spinorNormImageSubgroup (q := q) (L := L) :=
      (Subgroup.zpowers_le).2 hdeltaGlobal
    have htop : Lattice.spinorNormImageSubgroup (q := q) (L := L) = ⊤ := by
      apply top_unique
      rw [← htopGen]
      exact sup_le hnormLe hcyclicLe
    rw [htop]
    exact le_top

/-- Section 5(iii)(a), oriented from the left: an even high-defect first
parameter and a right gap beyond `2e` already supply the target layer. -/
theorem congruence_le_spinorNormImage_of_propertyB_of_left_even_high_right_deep
    [BeliLemma49Laws.{u, v} K]
    [BinarySpinorLocalLaws.{u, v} K]
    (b : BONG V q L 3) (hB : b.HasPropertyB)
    (hleftEven : Even
      (b.order (1 : Fin 3) - b.order (0 : Fin 3)))
    (hleftUpper : b.order (1 : Fin 3) - b.order (0 : Fin 3) ≤
      2 * (ramificationIndex K : Int))
    (hleftHigh : ¬2 * beliParameterDefect K
        (b.adjacentParameter (0 : Fin 3) (by norm_num)) ≤
      (beliDefectCutoff K
        (b.adjacentParameter (0 : Fin 3) (by norm_num)) : ℕ∞))
    (hrightDeep : 2 * (ramificationIndex K : Int) <
      b.order (2 : Fin 3) - b.order (1 : Fin 3)) :
    beliCongruenceSquareClassSubgroup K (b.theoremOneTwoStepDepth 0) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
  rw [b.congruence_eq_principalUnit_of_propertyB hB]
  let a : Kˣ := b.adjacentParameter (0 : Fin 3) (by norm_num)
  let R : Int := b.order (1 : Fin 3) - b.order (0 : Fin 3)
  let T : Int := b.order (2 : Fin 3) - b.order (1 : Fin 3)
  let epsilon : Kˣ := normalizedUnitPart K a
  have haOrder : ordUnit K a = R := by
    dsimp only [a, R]
    rw [b.ordUnit_adjacentParameter]
    congr 2
  have hepsilon : IsValuationUnit K (epsilon : K) :=
    normalizedUnitPart_isValuationUnit K a
  have hfactor : uniformizerPowerUnit K R * epsilon = a := by
    rw [← haOrder]
    exact uniformizerPower_mul_normalizedUnitPart K a
  have haAdmissible : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * epsilon) := by
    rw [hfactor]
    exact b.adjacentParameter_isBinaryParameterAdmissible
      (0 : Fin 3) (by norm_num)
  have hREven : Even R := by simpa only [R] using hleftEven
  have hRupper : R ≤ 2 * (ramificationIndex K : Int) := by
    simpa only [R] using hleftUpper
  have hTdeep : 2 * (ramificationIndex K : Int) < T := by
    simpa only [T] using hrightDeep
  have hdefectEq : beliParameterDefect K a =
      quadraticDefect K (-epsilon) := by
    unfold beliParameterDefect
    simpa only [epsilon] using
      (beliParameterDefect_eq_normalizedUnitPart_of_even
        (K := K) a (haOrder.symm ▸ hREven))
  have hdHigh : ¬2 * quadraticDefect K (-epsilon) ≤
      (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞) := by
    intro hd
    apply hleftHigh
    rw [hdefectEq]
    unfold beliDefectCutoff
    rw [haOrder]
    exact hd
  have hlocal := principalUnit_half_sum_le_beliSpinorGroup_of_even_high
    (K := K) R T epsilon hepsilon haAdmissible hRupper hREven hdHigh hTdeep
  rw [hfactor] at hlocal
  have hdepth : b.theoremOneTwoStepDepth 0 =
      Int.toNat ((R + T) / 2) := by
    unfold theoremOneTwoStepDepth
    change Int.toNat
        ((b.order (2 : Fin 3) - b.order (0 : Fin 3)) / 2) = _
    congr 2
    dsimp only [R, T]
    omega
  rw [hdepth]
  exact hlocal.trans
    (by
      simpa only [a] using b.adjacentSpinorGroup_le_spinorNormImage
        hB.isGood (0 : Fin 3) (by norm_num))

/-- Section 5(ii), odd neighboring gap: choose a norm multiplier of exact
defect equal to the first odd order, twist the second binary parameter, and
apply Corollary 3.15(i).  The resulting principal layer and the first
quadratic norm hyperplane generate all square classes. -/
theorem congruence_le_spinorNormImage_of_propertyB_of_left_odd_right_odd
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BinarySpinorLocalLaws.{u, v} K]
    (b : BONG V q L 3) (hB : b.HasPropertyB)
    (hleftOdd : Odd
      (b.order (1 : Fin 3) - b.order (0 : Fin 3)))
    (hleftUpper : b.order (1 : Fin 3) - b.order (0 : Fin 3) ≤
      2 * (ramificationIndex K : Int))
    (hrightOdd : Odd
      (b.order (2 : Fin 3) - b.order (1 : Fin 3))) :
    beliCongruenceSquareClassSubgroup K (b.theoremOneTwoStepDepth 0) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
  by_cases hdepth : 2 * ramificationIndex K <
      b.theoremOneTwoStepDepth 0
  · rw [b.congruence_eq_principalUnit_of_propertyB hB,
      principalUnitSquareClassSubgroup_eq_bot_of_two_mul_e_lt
        (K := K) (b.theoremOneTwoStepDepth 0) hdepth]
    exact bot_le
  · have hdepthUpper : b.theoremOneTwoStepDepth 0 ≤
        2 * ramificationIndex K := by omega
    let R : Int := b.order (1 : Fin 3) - b.order (0 : Fin 3)
    let T : Int := b.order (2 : Fin 3) - b.order (1 : Fin 3)
    have hRPos : 0 < R := by
      have h := b.adjacentOrderGap_pos_of_odd
        (0 : Fin 3) (by norm_num) hleftOdd
      have hindex : (⟨(0 : Fin 3).val + 1, by norm_num⟩ : Fin 3) =
          (1 : Fin 3) := by ext; norm_num
      rw [hindex] at h
      simpa only [R] using h
    have hcast0 : (Fin.castSucc (0 : Fin 2) : Fin 3) = (0 : Fin 3) := by
      ext
      norm_num
    have hsucc0 : (Fin.succ (0 : Fin 2) : Fin 3) = (1 : Fin 3) := by
      ext
      norm_num
    have htrigger : b.propertyBTrigger (0 : Fin 2) := by
      unfold propertyBTrigger
      rw [hcast0, hsucc0]
      left
      constructor
      · omega
      · exact hleftOdd
    have hTlower : 2 * (ramificationIndex K : Int) + 1 ≤ T := by
      have h := (hB.2 (0 : Fin 2) htrigger).2 (2 : Fin 3) (by norm_num)
      rw [hsucc0] at h
      simpa only [T] using h
    have htotalEven : Even (R + T) := by
      have hROdd : Odd R := by simpa only [R] using hleftOdd
      have hTOdd : Odd T := by simpa only [T] using hrightOdd
      exact hROdd.add_odd hTOdd
    have htotalUpper : R + T ≤
        4 * (ramificationIndex K : Int) := by
      have hcast := b.theoremOneTwoStepDepth_cast_of_propertyB hB
      have hdepthUpperInt :
          (b.theoremOneTwoStepDepth 0 : Int) ≤
            2 * (ramificationIndex K : Int) := by exact_mod_cast hdepthUpper
      have htotal : b.order (2 : Fin 3) - b.order (0 : Fin 3) =
          R + T := by
        dsimp only [R, T]
        omega
      rw [hcast, htotal] at hdepthUpperInt
      rcases htotalEven with ⟨s, hs⟩
      omega
    have hTupper : T ≤ 4 * (ramificationIndex K : Int) := by omega
    let m : Nat := Int.toNat R
    have hmCast : (m : Int) = R := by
      dsimp only [m]
      rw [Int.toNat_of_nonneg hRPos.le]
    have hmPos : 0 < m := by omega
    have hmOdd : Odd m := by
      rcases hleftOdd with ⟨r, hr⟩
      have hrNonneg : 0 ≤ r := by
        dsimp only [R] at hRPos
        omega
      refine ⟨Int.toNat r, ?_⟩
      have hrCast : (Int.toNat r : Int) = r := by
        rw [Int.toNat_of_nonneg hrNonneg]
      exact_mod_cast (show (m : Int) =
          2 * (Int.toNat r : Int) + 1 by
        rw [hmCast, hrCast]
        simpa only [R] using hr)
    have hmLt : m < 2 * ramificationIndex K := by
      have hRlt : R < 2 * (ramificationIndex K : Int) := by
        have hoddR : Odd R := by simpa only [R] using hleftOdd
        have hRupper : R ≤ 2 * (ramificationIndex K : Int) := by
          simpa only [R] using hleftUpper
        rcases hoddR with ⟨r, hr⟩
        omega
      have hmLtInt : (m : Int) < 2 * (ramificationIndex K : Int) := by
        rw [hmCast]
        exact hRlt
      exact_mod_cast hmLtInt
    let a : Kˣ := b.adjacentParameter (0 : Fin 3) (by norm_num)
    let c : Kˣ := b.adjacentParameter (1 : Fin 3) (by norm_num)
    have haOrder : ordUnit K a = R := by
      dsimp only [a, R]
      rw [b.ordUnit_adjacentParameter]
      congr 2
    have hcOrder : ordUnit K c = T := by
      dsimp only [c, T]
      rw [b.ordUnit_adjacentParameter]
      congr 2
    have haOdd : Odd (ordUnit K a) := by rwa [haOrder]
    have haDefect : quadraticDefect K (-a) = 0 :=
      quadraticDefect_eq_zero_of_odd_ordUnit (-a) (by simpa using haOdd)
    have hchoiceSum : quadraticDefect K (-a) + (m : ℕ∞) <
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
      rw [haDefect]
      simp only [zero_add]
      exact_mod_cast hmLt
    rcases exists_valuationUnit_defect_eq_odd_hilbert_one_of_sum_lt
        (K := K) (-a) m hmPos hmOdd hmLt hchoiceSum with
      ⟨zeta, hzetaDefect, hzetaHilbert⟩
    have hzetaGroup : valuationUnitClassHom K zeta ∈
        beliNormGeneratorGroup K a := by
      apply valuationUnitClass_mem_beliNormGeneratorGroup_of_odd_exact
        (K := K) a zeta m
      · rw [haOrder, hmCast]
      · exact haOdd
      · rw [haOrder]
        simpa only [R] using hleftUpper
      · exact hzetaDefect
      · exact hzetaHilbert
    have hzetaNeighbor :
        ((∃ hleft : 1 ≤ (1 : Fin 3).val,
            valuationUnitClassHom K zeta ∈ beliNormGeneratorGroup K
              (b.valueUnit (1 : Fin 3) /
                b.valueUnit ⟨(1 : Fin 3).val - 1, by omega⟩)) ∨
          (∃ hright : (1 : Fin 3).val + 2 < 3,
            valuationUnitClassHom K zeta ∈ beliNormGeneratorGroup K
              (b.valueUnit ⟨(1 : Fin 3).val + 2, hright⟩ /
                b.valueUnit ⟨(1 : Fin 3).val + 1, by norm_num⟩))) := by
      left
      refine ⟨by norm_num, ?_⟩
      have hparameter :
          b.valueUnit (1 : Fin 3) /
              b.valueUnit ⟨(1 : Fin 3).val - 1, by omega⟩ = a := by
        dsimp only [a, adjacentParameter]
        congr 2
      rw [hparameter]
      exact hzetaGroup
    have hcAdmissible : IsBinaryParameterAdmissible c := by
      simpa only [c] using b.adjacentParameter_isBinaryParameterAdmissible
        (1 : Fin 3) (by norm_num)
    have htwistAdmissible : IsBinaryParameterAdmissible
        ((zeta : Kˣ) * c) := by
      simpa only [c] using
        b.isBinaryParameterAdmissible_mul_adjacentParameter_of_adjacentMultiplier
          hB.isGood (1 : Fin 3) (by norm_num) zeta hzetaNeighbor
    have hcor := principalUnit_order_sub_twoE_add_defect_le_spinor_sup_twist
      (K := K) c zeta m hcAdmissible htwistAdmissible
        (by rw [hcOrder]; omega) (by rw [hcOrder]; exact hTupper)
        hzetaDefect
    let beta : Nat := Int.toNat
      (T - 2 * (ramificationIndex K : Int) + (m : Int))
    have hcorBeta : principalUnitSquareClassSubgroup K beta ≤
        beliSpinorGroupRepresentative K c ⊔
          beliSpinorGroupRepresentative K ((zeta : Kˣ) * c) := by
      simpa only [beta, hcOrder] using hcor
    have hcLe : beliSpinorGroupRepresentative K c ≤
        Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
      simpa only [c] using b.adjacentSpinorGroup_le_spinorNormImage
        hB.isGood (1 : Fin 3) (by norm_num)
    have htwistLe : beliSpinorGroupRepresentative K ((zeta : Kˣ) * c) ≤
        Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
      intro x hx
      change x ∈ Lattice.spinorNormImage (q := q) (L := L)
      apply b.twistedAdjacentSpinorGroup_subset_of_adjacentMultiplier
        hB.isGood (1 : Fin 3) (by norm_num) zeta hzetaNeighbor
      rw [beliSpinorGroup_unitSquareClass]
      change x ∈ (beliSpinorGroupRepresentative K
        ((zeta : Kˣ) * c) : Set (SquareClass K))
      exact hx
    have hbetaLe : principalUnitSquareClassSubgroup K beta ≤
        Lattice.spinorNormImageSubgroup (q := q) (L := L) :=
      hcorBeta.trans (sup_le hcLe htwistLe)
    have haAdmissible : IsBinaryParameterAdmissible a := by
      simpa only [a] using b.adjacentParameter_isBinaryParameterAdmissible
        (0 : Fin 3) (by norm_num)
    have haGroup : beliSpinorGroupRepresentative K a =
        quadraticNormSquareClassSubgroup K (-a) := by
      apply beliSpinorGroupRepresentative_eq_norm_of_odd_trigger
        (K := K) a haAdmissible haOdd
      rw [haOrder]
      dsimp only [R]
      omega
    have haLe : beliSpinorGroupRepresentative K a ≤
        Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
      simpa only [a] using b.adjacentSpinorGroup_le_spinorNormImage
        hB.isGood (0 : Fin 3) (by norm_num)
    have hnormLe : quadraticNormSquareClassSubgroup K (-a) ≤
        Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
      rw [← haGroup]
      exact haLe
    have hbetaPos : 0 < beta := by
      dsimp only [beta]
      omega
    have hbetaUpper : beta ≤ 2 * ramificationIndex K := by
      dsimp only [beta]
      omega
    have htopGen : quadraticNormSquareClassSubgroup K (-a) ⊔
        principalUnitSquareClassSubgroup K beta = ⊤ :=
      quadraticNorm_sup_principalUnit_eq_top_of_defect_add_le
        (K := K) (-a) beta 0 hbetaPos haDefect (by simpa using hbetaUpper)
    have htop : Lattice.spinorNormImageSubgroup (q := q) (L := L) = ⊤ := by
      apply top_unique
      rw [← htopGen]
      exact sup_le hnormLe hbetaLe
    rw [htop]
    exact le_top

/-- Section 5(i)(a): for an even low-defect first parameter and an even
neighboring gap beyond `2e`, either the target principal layer is already in
the first quadratic norm group, or an exact low-defect multiplier and
Corollary 3.15(i) produce a second principal layer which, together with that
norm group, generates all square classes. -/
theorem congruence_le_spinorNormImage_of_propertyB_of_left_even_low_right_even
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BinarySpinorLocalLaws.{u, v} K]
    (b : BONG V q L 3) (hB : b.HasPropertyB)
    (hleftEven : Even
      (b.order (1 : Fin 3) - b.order (0 : Fin 3)))
    (hleftUpper : b.order (1 : Fin 3) - b.order (0 : Fin 3) ≤
      2 * (ramificationIndex K : Int))
    (hleftLow : 2 * beliParameterDefect K
        (b.adjacentParameter (0 : Fin 3) (by norm_num)) ≤
      (beliDefectCutoff K
        (b.adjacentParameter (0 : Fin 3) (by norm_num)) : ℕ∞))
    (hrightEven : Even
      (b.order (2 : Fin 3) - b.order (1 : Fin 3)))
    (hrightDeep : 2 * (ramificationIndex K : Int) <
      b.order (2 : Fin 3) - b.order (1 : Fin 3)) :
    beliCongruenceSquareClassSubgroup K (b.theoremOneTwoStepDepth 0) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
  let alpha : Nat := b.theoremOneTwoStepDepth 0
  let R : Int := b.order (1 : Fin 3) - b.order (0 : Fin 3)
  let T : Int := b.order (2 : Fin 3) - b.order (1 : Fin 3)
  let a : Kˣ := b.adjacentParameter (0 : Fin 3) (by norm_num)
  have haOrder : ordUnit K a = R := by
    dsimp only [a, R]
    rw [b.ordUnit_adjacentParameter]
    congr 2
  have haAdmissible : IsBinaryParameterAdmissible a := by
    simpa only [a] using b.adjacentParameter_isBinaryParameterAdmissible
      (0 : Fin 3) (by norm_num)
  have hREven : Even (ordUnit K a) := by
    rw [haOrder]
    simpa only [R] using hleftEven
  have hRnotAbove : ¬2 * (ramificationIndex K : Int) < ordUnit K a := by
    rw [haOrder]
    simpa only [R] using (not_lt.mpr hleftUpper)
  have hlow : 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞) := by
    simpa only [a] using hleftLow
  have hfinite : beliParameterDefect K a ≠ ⊤ := by
    intro htop
    rw [htop] at hlow
    simp at hlow
  let d : Nat := beliParameterDefectNat K a
  have hdefectEq : beliParameterDefect K a = (d : ℕ∞) := by
    simpa only [d, beliParameterDefectNat] using
      (ENat.coe_toNat hfinite).symm
  have haDefect : quadraticDefect K (-a) = (d : ℕ∞) := by
    simpa only [beliParameterDefect] using hdefectEq
  have haGroup : beliSpinorGroupRepresentative K a =
      quadraticNormSquareClassSubgroup K (-a) := by
    apply beliSpinorGroupRepresentative_eq_norm_of_low_defect
      (K := K) a haAdmissible
    · rw [haOrder]
      simpa only [R] using hleftUpper
    · simpa [beliSpinorCaseIIILowerCutoff, beliDefectCutoff] using hlow
    · exact hfinite
  have haLe : beliSpinorGroupRepresentative K a ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
    simpa only [a] using b.adjacentSpinorGroup_le_spinorNormImage
      hB.isGood (0 : Fin 3) (by norm_num)
  have hnormLe : quadraticNormSquareClassSubgroup K (-a) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
    rw [← haGroup]
    exact haLe
  by_cases htargetNorm : principalUnitSquareClassSubgroup K alpha ≤
      quadraticNormSquareClassSubgroup K (-a)
  · rw [b.congruence_eq_principalUnit_of_propertyB hB]
    simpa only [alpha] using htargetNorm.trans hnormLe
  · have halphaPos : 0 < alpha := by
      simpa only [alpha] using b.theoremOneTwoStepDepth_pos_of_propertyB hB
    have hsumNot : ¬((2 * ramificationIndex K : Nat) : ℕ∞) <
        quadraticDefect K (-a) + (alpha : ℕ∞) := by
      rw [← principalUnitSquareClassSubgroup_le_quadraticNorm_iff
        K (-a) alpha halphaPos]
      exact htargetNorm
    have hsumLeENat : (d : ℕ∞) + (alpha : ℕ∞) ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
      rw [← haDefect]
      exact le_of_not_gt hsumNot
    have hsumLe : d + alpha ≤ 2 * ramificationIndex K := by
      exact_mod_cast hsumLeENat
    have habsolute : 0 ≤ R + (d : Int) := by
      have h := beli2009_order_add_parameterDefect_nonneg
        (K := K) haAdmissible hfinite
      rw [haOrder] at h
      simpa only [d, beliParameterDefectNat] using h
    have hnotEndpoint : ordUnit K a ≠
        -(2 * (ramificationIndex K : Int)) := by
      intro hend
      have hRend : R = -(2 * (ramificationIndex K : Int)) := by
        rwa [haOrder] at hend
      have hdLowerInt : 2 * (ramificationIndex K : Int) ≤ (d : Int) := by
        omega
      have hdLower : 2 * ramificationIndex K ≤ d := by
        exact_mod_cast hdLowerInt
      omega
    let m : Nat := beliLowDefectExponent K a
    have harith := scratch_beliLowBranch_arithmetic
      (K := K) a haAdmissible hRnotAbove hlow hREven hnotEndpoint
    have hmPos : 0 < m := by simpa only [m] using harith.1
    have hmOdd : Odd m := by simpa only [m] using harith.2.1
    have hmLt : m < 2 * ramificationIndex K := by
      simpa only [m] using harith.2.2.1
    have hmCast : (m : Int) = R + (d : Int) := by
      have h := scratch_beliLowDefectExponent_cast
        (K := K) a haAdmissible hfinite
      rw [haOrder] at h
      simpa only [m, d] using h
    have htotal : b.order (2 : Fin 3) - b.order (0 : Fin 3) =
        R + T := by
      dsimp only [R, T]
      omega
    have halphaCast : (alpha : Int) = (R + T) / 2 := by
      have h := b.theoremOneTwoStepDepth_cast_of_propertyB hB
      rw [htotal] at h
      simpa only [alpha] using h
    have hTEven : Even T := by simpa only [T] using hrightEven
    have hTdeep : 2 * (ramificationIndex K : Int) < T := by
      simpa only [T] using hrightDeep
    have hTlower : 2 * (ramificationIndex K : Int) + 2 ≤ T := by
      rcases hTEven with ⟨t, ht⟩
      omega
    have hsumLeInt : (d : Int) + (alpha : Int) ≤
        2 * (ramificationIndex K : Int) := by exact_mod_cast hsumLe
    have hchoiceNat : d + m < 2 * ramificationIndex K := by
      have hchoiceInt : (d : Int) + (m : Int) <
          2 * (ramificationIndex K : Int) := by
        rw [hmCast]
        rw [halphaCast] at hsumLeInt
        rcases hTEven with ⟨t, ht⟩
        rcases hleftEven with ⟨r, hr⟩
        omega
      exact_mod_cast hchoiceInt
    have hchoiceSum : quadraticDefect K (-a) + (m : ℕ∞) <
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
      rw [haDefect]
      exact_mod_cast hchoiceNat
    rcases exists_valuationUnit_defect_eq_odd_hilbert_one_of_sum_lt
        (K := K) (-a) m hmPos hmOdd hmLt hchoiceSum with
      ⟨zeta, hzetaDefect, hzetaHilbert⟩
    have hzetaGroup : valuationUnitClassHom K zeta ∈
        beliNormGeneratorGroup K a := by
      rw [beliNormGeneratorGroup_of_low_defect K a hRnotAbove hlow]
      change valuationUnitClassHom K zeta ∈
          principalUnitValuationClassSubgroup K m ⊓
            quadraticNormValuationClassSubgroup K (-a)
      constructor
      · apply
          valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
        rw [hzetaDefect]
      · refine ⟨zeta, ?_, rfl⟩
        change IsQuadraticNorm K (-a) (zeta : Kˣ)
        exact (hilbertSymbol_eq_one_iff K (-a) (zeta : Kˣ)).1
          hzetaHilbert
    have hTupper : T ≤ 4 * (ramificationIndex K : Int) := by
      rw [halphaCast] at hsumLeInt
      rcases hTEven with ⟨t, ht⟩
      rcases hleftEven with ⟨r, hr⟩
      omega
    have htwist := b.principalUnit_rightTwist_le_spinorNormImage
      hB.isGood zeta m (by simpa only [a] using hzetaGroup)
        hzetaDefect (by simpa only [T] using hTdeep)
        (by simpa only [T] using hTupper)
    let beta : Nat := Int.toNat
      (T - 2 * (ramificationIndex K : Int) + (m : Int))
    have hbetaLe : principalUnitSquareClassSubgroup K beta ≤
        Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
      simpa only [beta, T] using htwist
    have hbetaPos : 0 < beta := by
      dsimp only [beta]
      omega
    have hbetaBound : beta + d ≤ 2 * ramificationIndex K := by
      have hbetaInt :
          (Int.toNat
            (T - 2 * (ramificationIndex K : Int) + (m : Int)) : Int) =
          T - 2 * (ramificationIndex K : Int) + (m : Int) := by
        rw [Int.toNat_of_nonneg]
        omega
      have hboundInt : (beta : Int) + (d : Int) ≤
          2 * (ramificationIndex K : Int) := by
        dsimp only [beta]
        rw [hbetaInt, hmCast]
        rw [halphaCast] at hsumLeInt
        rcases hTEven with ⟨t, ht⟩
        rcases hleftEven with ⟨r, hr⟩
        omega
      exact_mod_cast hboundInt
    have htopGen : quadraticNormSquareClassSubgroup K (-a) ⊔
        principalUnitSquareClassSubgroup K beta = ⊤ :=
      quadraticNorm_sup_principalUnit_eq_top_of_defect_add_le
        (K := K) (-a) beta d hbetaPos haDefect hbetaBound
    have htop : Lattice.spinorNormImageSubgroup (q := q) (L := L) = ⊤ := by
      apply top_unique
      rw [← htopGen]
      exact sup_le hnormLe hbetaLe
    rw [htop]
    exact le_top

/-- Section 5(i)(b): for an even low-defect first parameter and an odd
neighboring gap beyond `2e`, the neighboring spinor group and the
discriminant class fill `U_(T-2e)`.  Either that layer escapes the first
norm hyperplane, or the arithmetic forces the finite endpoint
`-Delta/4`, whose binary group is the full valuation-unit subgroup. -/
theorem congruence_le_spinorNormImage_of_propertyB_of_left_even_low_right_odd
    [BeliLemma49Laws.{u, v} K]
    [BinarySpinorLocalLaws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    (b : BONG V q L 3) (hB : b.HasPropertyB)
    (hleftEven : Even
      (b.order (1 : Fin 3) - b.order (0 : Fin 3)))
    (hleftUpper : b.order (1 : Fin 3) - b.order (0 : Fin 3) ≤
      2 * (ramificationIndex K : Int))
    (hleftLow : 2 * beliParameterDefect K
        (b.adjacentParameter (0 : Fin 3) (by norm_num)) ≤
      (beliDefectCutoff K
        (b.adjacentParameter (0 : Fin 3) (by norm_num)) : ℕ∞))
    (hrightOdd : Odd
      (b.order (2 : Fin 3) - b.order (1 : Fin 3)))
    (hrightDeep : 2 * (ramificationIndex K : Int) <
      b.order (2 : Fin 3) - b.order (1 : Fin 3)) :
    beliCongruenceSquareClassSubgroup K (b.theoremOneTwoStepDepth 0) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
  let alpha : Nat := b.theoremOneTwoStepDepth 0
  let R : Int := b.order (1 : Fin 3) - b.order (0 : Fin 3)
  let T : Int := b.order (2 : Fin 3) - b.order (1 : Fin 3)
  let a : Kˣ := b.adjacentParameter (0 : Fin 3) (by norm_num)
  let c : Kˣ := b.adjacentParameter (1 : Fin 3) (by norm_num)
  have haOrder : ordUnit K a = R := by
    dsimp only [a, R]
    rw [b.ordUnit_adjacentParameter]
    congr 2
  have hcOrder : ordUnit K c = T := by
    dsimp only [c, T]
    rw [b.ordUnit_adjacentParameter]
    congr 2
  have haAdmissible : IsBinaryParameterAdmissible a := by
    simpa only [a] using b.adjacentParameter_isBinaryParameterAdmissible
      (0 : Fin 3) (by norm_num)
  have hcAdmissible : IsBinaryParameterAdmissible c := by
    simpa only [c] using b.adjacentParameter_isBinaryParameterAdmissible
      (1 : Fin 3) (by norm_num)
  have hREven : Even (ordUnit K a) := by
    rw [haOrder]
    simpa only [R] using hleftEven
  have hRnotAbove : ¬2 * (ramificationIndex K : Int) < ordUnit K a := by
    rw [haOrder]
    simpa only [R] using (not_lt.mpr hleftUpper)
  have hlow : 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞) := by
    simpa only [a] using hleftLow
  have hfinite : beliParameterDefect K a ≠ ⊤ := by
    intro htop
    rw [htop] at hlow
    simp at hlow
  let d : Nat := beliParameterDefectNat K a
  have hdefectEq : beliParameterDefect K a = (d : ℕ∞) := by
    simpa only [d, beliParameterDefectNat] using
      (ENat.coe_toNat hfinite).symm
  have haDefect : quadraticDefect K (-a) = (d : ℕ∞) := by
    simpa only [beliParameterDefect] using hdefectEq
  have hdPos : 0 < d := by
    by_contra hnot
    have hdZero : d = 0 := Nat.eq_zero_of_not_pos hnot
    have hdefectZero : quadraticDefect K (-a) = 0 := by
      rw [haDefect, hdZero]
      simp
    have hodd := odd_ordUnit_of_quadraticDefect_eq_zero (-a) hdefectZero
    have heven : Even (ordUnit K (-a)) := by simpa using hREven
    exact (Int.not_even_iff_odd.mpr hodd) heven
  have haGroup : beliSpinorGroupRepresentative K a =
      quadraticNormSquareClassSubgroup K (-a) := by
    apply beliSpinorGroupRepresentative_eq_norm_of_low_defect
      (K := K) a haAdmissible
    · rw [haOrder]
      simpa only [R] using hleftUpper
    · simpa [beliSpinorCaseIIILowerCutoff, beliDefectCutoff] using hlow
    · exact hfinite
  have haLe : beliSpinorGroupRepresentative K a ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
    simpa only [a] using b.adjacentSpinorGroup_le_spinorNormImage
      hB.isGood (0 : Fin 3) (by norm_num)
  have hnormLe : quadraticNormSquareClassSubgroup K (-a) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
    rw [← haGroup]
    exact haLe
  by_cases htargetNorm : principalUnitSquareClassSubgroup K alpha ≤
      quadraticNormSquareClassSubgroup K (-a)
  · rw [b.congruence_eq_principalUnit_of_propertyB hB]
    simpa only [alpha] using htargetNorm.trans hnormLe
  · have halphaPos : 0 < alpha := by
      simpa only [alpha] using b.theoremOneTwoStepDepth_pos_of_propertyB hB
    have hsumNot : ¬((2 * ramificationIndex K : Nat) : ℕ∞) <
        quadraticDefect K (-a) + (alpha : ℕ∞) := by
      rw [← principalUnitSquareClassSubgroup_le_quadraticNorm_iff
        K (-a) alpha halphaPos]
      exact htargetNorm
    have hsumLeENat : (d : ℕ∞) + (alpha : ℕ∞) ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
      rw [← haDefect]
      exact le_of_not_gt hsumNot
    have hsumLe : d + alpha ≤ 2 * ramificationIndex K := by
      exact_mod_cast hsumLeENat
    have hsumLeInt : (d : Int) + (alpha : Int) ≤
        2 * (ramificationIndex K : Int) := by exact_mod_cast hsumLe
    have habsolute : 0 ≤ R + (d : Int) := by
      have h := beli2009_order_add_parameterDefect_nonneg
        (K := K) haAdmissible hfinite
      rw [haOrder] at h
      simpa only [d, beliParameterDefectNat] using h
    have htotal : b.order (2 : Fin 3) - b.order (0 : Fin 3) =
        R + T := by
      dsimp only [R, T]
      omega
    have halphaCast : (alpha : Int) = (R + T) / 2 := by
      have h := b.theoremOneTwoStepDepth_cast_of_propertyB hB
      rw [htotal] at h
      simpa only [alpha] using h
    have hROriginalEven : Even R := by simpa only [R] using hleftEven
    have hTOdd : Odd T := by simpa only [T] using hrightOdd
    have htotalOdd : Odd (R + T) := hROriginalEven.add_odd hTOdd
    have hTdeep : 2 * (ramificationIndex K : Int) < T := by
      simpa only [T] using hrightDeep
    have hTupper : T ≤ 4 * (ramificationIndex K : Int) := by
      rw [halphaCast] at hsumLeInt
      rcases htotalOdd with ⟨s, hs⟩
      omega
    have hcLe : beliSpinorGroupRepresentative K c ≤
        Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
      simpa only [c] using b.adjacentSpinorGroup_le_spinorNormImage
        hB.isGood (1 : Fin 3) (by norm_num)
    let delta : Kˣ := laws.discriminantUnit
    have hdeltaNormA : squareClass K delta ∈
        quadraticNormSquareClassSubgroup K (-a) := by
      refine ⟨delta, ?_, rfl⟩
      change IsQuadraticNorm K (-a) delta
      simpa only [delta] using
        (discriminantUnit_isQuadraticNorm_of_even_order
          (K := K) (-a) (by simpa using hREven))
    have hdeltaGlobal : squareClass K delta ∈
        Lattice.spinorNormImageSubgroup (q := q) (L := L) :=
      hnormLe hdeltaNormA
    let beta : Nat := Int.toNat
      (T - 2 * (ramificationIndex K : Int))
    have hbetaLe : principalUnitSquareClassSubgroup K beta ≤
        Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
      have hfill :=
        theoremOnePrincipalUnit_order_sub_twoE_le_of_odd_spinor_and_discriminant
          (K := K) c
          (Lattice.spinorNormImageSubgroup (q := q) (L := L))
          hcAdmissible (by rwa [hcOrder]) (by rwa [hcOrder])
          (by rwa [hcOrder]) hcLe (by simpa only [delta] using hdeltaGlobal)
      simpa only [beta, hcOrder] using hfill
    have hbetaCast : (beta : Int) =
        T - 2 * (ramificationIndex K : Int) := by
      dsimp only [beta]
      rw [Int.toNat_of_nonneg]
      omega
    have hbetaPos : 0 < beta := by
      exact_mod_cast (show (0 : Int) < (beta : Int) by
        rw [hbetaCast]
        omega)
    by_cases hbetaNorm : principalUnitSquareClassSubgroup K beta ≤
        quadraticNormSquareClassSubgroup K (-a)
    · have hbetaCriterion :
          ((2 * ramificationIndex K : Nat) : ℕ∞) <
            quadraticDefect K (-a) + (beta : ℕ∞) := by
        rw [← principalUnitSquareClassSubgroup_le_quadraticNorm_iff
          K (-a) beta hbetaPos]
        exact hbetaNorm
      have hbetaSum : 2 * ramificationIndex K < d + beta := by
        rw [haDefect] at hbetaCriterion
        exact_mod_cast hbetaCriterion
      have hbetaSumInt : 2 * (ramificationIndex K : Int) <
          (d : Int) + (beta : Int) := by exact_mod_cast hbetaSum
      have hREq : R = -(d : Int) := by
        rw [hbetaCast] at hbetaSumInt
        rw [halphaCast] at hsumLeInt
        rcases htotalOdd with ⟨s, hs⟩
        omega
      have hdEven : Even d := by
        rcases hROriginalEven with ⟨r, hr⟩
        refine ⟨Int.toNat (-r), ?_⟩
        have hrNonneg : 0 ≤ -r := by
          rw [hREq] at hr
          omega
        have hrCast : (Int.toNat (-r) : Int) = -r := by
          rw [Int.toNat_of_nonneg hrNonneg]
        have hdDouble : d = 2 * Int.toNat (-r) := by
          exact_mod_cast (show (d : Int) =
              2 * (Int.toNat (-r) : Int) by
            rw [hrCast]
            omega)
        simpa [two_mul] using hdDouble
      have hdUpper : d ≤ 2 * ramificationIndex K := by omega
      have hdEq : d = 2 * ramificationIndex K := by
        by_contra hne
        have hdLt : d < 2 * ramificationIndex K := by omega
        have hdefectLt : quadraticDefect K (-a) <
            ((2 * ramificationIndex K : Nat) : ℕ∞) := by
          rw [haDefect]
          exact_mod_cast hdLt
        have hdOdd :=
          quadraticDefect_toNat_odd_of_even_ordUnit_of_lt_two_mul_e
            (K := K) (-a) (by simpa using hREven) hdefectLt
        rw [haDefect] at hdOdd
        simp only [ENat.toNat_coe] at hdOdd
        exact (Nat.not_even_iff_odd.mpr hdOdd) hdEven
      have hREndpoint : ordUnit K a =
          -(2 * (ramificationIndex K : Int)) := by
        rw [haOrder, hREq, hdEq]
        push_cast
        rfl
      have hclasses := laws.endpoint_parameter_class a haAdmissible hREndpoint
      have hdeltaClass : unitSquareClass K a =
          unitSquareClass K (negativeQuarterUnit K * delta) := by
        rcases hclasses with hquarter | hdeltaClass
        · have hdefectClass :=
            beliParameterDefect_eq_of_unitSquareClass_eq (K := K) hquarter
          rw [beliParameterDefect_negativeQuarterUnit] at hdefectClass
          exact (hfinite hdefectClass).elim
        · simpa only [delta] using hdeltaClass
      have hsquare : IsSquare (-a * delta) := by
        simpa only [delta] using
          (isSquare_neg_mul_discriminant_of_endpointClass
            (K := K) hdeltaClass)
      rcases hsquare with ⟨s, hs⟩
      have hfactor : -a = delta * (s * delta⁻¹) ^ 2 := by
        calc
          -a = (-a * delta) * delta⁻¹ := by simp
          _ = (s * s) * delta⁻¹ := by rw [hs]
          _ = delta * (s * delta⁻¹) ^ 2 := by
            simp only [pow_two]
            calc
              s * s * delta⁻¹ =
                  (delta * delta⁻¹) * (s * s) * delta⁻¹ := by simp
              _ = delta * s * delta⁻¹ * s * delta⁻¹ := by ac_rfl
              _ = delta * (s * delta⁻¹ * (s * delta⁻¹)) := by group
      have hnormUnit : quadraticNormSquareClassSubgroup K (-a) =
          valuationUnitSquareClassSubgroup K := by
        rw [hfactor, quadraticNormSquareClassSubgroup_mul_square]
        exact quadraticNormSquareClassSubgroup_discriminant_eq_valuationUnit
          (K := K)
      have hunitLe : valuationUnitSquareClassSubgroup K ≤
          Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
        rw [← hnormUnit]
        exact hnormLe
      have hquarterC := unitSquareClass_ne_negativeQuarter_of_two_e_lt
        (K := K) c (by rwa [hcOrder])
      have hcFormula :=
        beliSpinorGroupRepresentative_eq_cyclic_sup_auxiliary
          K c hcAdmissible hquarterC (by rwa [hcOrder])
      have hcyclicC : cyclicSquareClassSubgroup K c ≤
          Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
        apply (show cyclicSquareClassSubgroup K c ≤
          beliSpinorGroupRepresentative K c by
            rw [hcFormula]
            exact le_sup_left) |>.trans
        exact hcLe
      have hcClassGlobal : squareClass K c ∈
          Lattice.spinorNormImageSubgroup (q := q) (L := L) :=
        hcyclicC (Subgroup.mem_zpowers (squareClass K c))
      have hcNotUnit : squareClass K c ∉
          valuationUnitSquareClassSubgroup K := by
        intro hcUnit
        have hcEven :=
          (squareClass_mem_valuationUnitSquareClassSubgroup_iff_even c).1
            hcUnit
        apply Int.not_even_iff_odd.mpr
          (show Odd (ordUnit K c) by rwa [hcOrder])
        exact hcEven
      have hnotGlobal : ¬Lattice.spinorNormImageSubgroup (q := q) (L := L) ≤
          valuationUnitSquareClassSubgroup K := by
        intro hle
        exact hcNotUnit (hle hcClassGlobal)
      have htop :=
        theoremOneSquareClassSubgroup_eq_top_of_valuationUnit_le_of_not_le
          (K := K) (Lattice.spinorNormImageSubgroup (q := q) (L := L))
          hunitLe hnotGlobal
      rw [htop]
      exact le_top
    · have hbetaCriterion : ¬
          ((2 * ramificationIndex K : Nat) : ℕ∞) <
            quadraticDefect K (-a) + (beta : ℕ∞) := by
        rw [← principalUnitSquareClassSubgroup_le_quadraticNorm_iff
          K (-a) beta hbetaPos]
        exact hbetaNorm
      have hbetaBoundENat : (d : ℕ∞) + (beta : ℕ∞) ≤
          ((2 * ramificationIndex K : Nat) : ℕ∞) := by
        rw [← haDefect]
        exact le_of_not_gt hbetaCriterion
      have hbetaBound : beta + d ≤ 2 * ramificationIndex K := by
        have : d + beta ≤ 2 * ramificationIndex K := by
          exact_mod_cast hbetaBoundENat
        simpa [Nat.add_comm] using this
      have htopGen : quadraticNormSquareClassSubgroup K (-a) ⊔
          principalUnitSquareClassSubgroup K beta = ⊤ :=
        quadraticNorm_sup_principalUnit_eq_top_of_defect_add_le
          (K := K) (-a) beta d hbetaPos haDefect hbetaBound
      have htop : Lattice.spinorNormImageSubgroup (q := q) (L := L) = ⊤ := by
        apply top_unique
        rw [← htopGen]
        exact sup_le hnormLe hbetaLe
      rw [htop]
      exact le_top

/-- Section 5(iii)(c), in the parity orientation used in the paper.  Both
adjacent gaps are even and in the high-defect range.  A multiplier of defect
`R/2+e` (or the next odd defect) and Corollary 3.15(ii) produce the target
layer.  In the successor case the dyadic filtration is constant because the
target depth is even. -/
theorem congruence_le_spinorNormImage_of_propertyB_of_both_even_high_oriented
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BinarySpinorLocalLaws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    (b : BONG V q L 3) (hB : b.HasPropertyB)
    (hleftEven : Even
      (b.order (1 : Fin 3) - b.order (0 : Fin 3)))
    (hleftUpper : b.order (1 : Fin 3) - b.order (0 : Fin 3) ≤
      2 * (ramificationIndex K : Int))
    (hleftHigh : ¬2 * beliParameterDefect K
        (b.adjacentParameter (0 : Fin 3) (by norm_num)) ≤
      (beliDefectCutoff K
        (b.adjacentParameter (0 : Fin 3) (by norm_num)) : ℕ∞))
    (hrightEven : Even
      (b.order (2 : Fin 3) - b.order (1 : Fin 3)))
    (hrightUpper : b.order (2 : Fin 3) - b.order (1 : Fin 3) ≤
      2 * (ramificationIndex K : Int))
    (hrightHigh : ¬2 * beliParameterDefect K
        (b.adjacentParameter (1 : Fin 3) (by norm_num)) ≤
      (beliDefectCutoff K
        (b.adjacentParameter (1 : Fin 3) (by norm_num)) : ℕ∞))
    (hparity :
      Odd ((b.order (1 : Fin 3) - b.order (0 : Fin 3)) / 2 +
        (ramificationIndex K : Int)) ∨
      (b.order (1 : Fin 3) - b.order (0 : Fin 3)) / 2 +
          (ramificationIndex K : Int) =
        2 * (ramificationIndex K : Int) ∨
      Even ((b.order (2 : Fin 3) - b.order (1 : Fin 3)) / 2 +
        (ramificationIndex K : Int))) :
    beliCongruenceSquareClassSubgroup K (b.theoremOneTwoStepDepth 0) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
  rw [b.congruence_eq_principalUnit_of_propertyB hB]
  let alpha : Nat := b.theoremOneTwoStepDepth 0
  let R : Int := b.order (1 : Fin 3) - b.order (0 : Fin 3)
  let T : Int := b.order (2 : Fin 3) - b.order (1 : Fin 3)
  let x : Int := R / 2 + (ramificationIndex K : Int)
  let y : Int := T / 2 + (ramificationIndex K : Int)
  let k : Nat := Int.toNat x
  let a : Kˣ := b.adjacentParameter (0 : Fin 3) (by norm_num)
  let c : Kˣ := b.adjacentParameter (1 : Fin 3) (by norm_num)
  have haOrder : ordUnit K a = R := by
    dsimp only [a, R]
    rw [b.ordUnit_adjacentParameter]
    congr 2
  have hcOrder : ordUnit K c = T := by
    dsimp only [c, T]
    rw [b.ordUnit_adjacentParameter]
    congr 2
  have haAdmissible : IsBinaryParameterAdmissible a := by
    simpa only [a] using b.adjacentParameter_isBinaryParameterAdmissible
      (0 : Fin 3) (by norm_num)
  have hcAdmissible : IsBinaryParameterAdmissible c := by
    simpa only [c] using b.adjacentParameter_isBinaryParameterAdmissible
      (1 : Fin 3) (by norm_num)
  have hREven : Even R := by simpa only [R] using hleftEven
  have hTEven : Even T := by simpa only [T] using hrightEven
  have hRupper : R ≤ 2 * (ramificationIndex K : Int) := by
    simpa only [R] using hleftUpper
  have hTupper : T ≤ 2 * (ramificationIndex K : Int) := by
    simpa only [T] using hrightUpper
  have htotalPos : 0 < R + T := by
    have hA := hB.hasPropertyA (0 : Fin 3) (by norm_num)
    have hA' : b.order (0 : Fin 3) < b.order (2 : Fin 3) := by
      simpa using hA
    dsimp only [R, T]
    omega
  have hxPos : 0 < x := by
    rcases hREven with ⟨r, hr⟩
    rcases hTEven with ⟨t, ht⟩
    dsimp only [x]
    omega
  have hxUpper : x ≤ 2 * (ramificationIndex K : Int) := by
    rcases hREven with ⟨r, hr⟩
    dsimp only [x]
    omega
  have hkCast : (k : Int) = x := by
    dsimp only [k]
    rw [Int.toNat_of_nonneg hxPos.le]
  have hkPos : 0 < k := by
    have : (0 : Int) < (k : Int) := by rwa [hkCast]
    exact_mod_cast this
  have hkUpper : k ≤ 2 * ramificationIndex K := by
    have : (k : Int) ≤ 2 * (ramificationIndex K : Int) := by
      rwa [hkCast]
    exact_mod_cast this
  have halphaCast : (alpha : Int) = (R + T) / 2 := by
    have h := b.theoremOneTwoStepDepth_cast_of_propertyB hB
    have htotal : b.order (2 : Fin 3) - b.order (0 : Fin 3) =
        R + T := by
      dsimp only [R, T]
      omega
    rw [htotal] at h
    simpa only [alpha] using h
  have halphaPos : 0 < alpha := by
    simpa only [alpha] using b.theoremOneTwoStepDepth_pos_of_propertyB hB
  obtain ⟨m, zeta, hzetaDefect, hkm, hmUpper,
      hmShape⟩ : ∃ (m : Nat) (zeta : valuationUnitSubgroup K),
      quadraticDefect K (zeta : Kˣ) = (m : ℕ∞) ∧
        k ≤ m ∧ m ≤ 2 * ramificationIndex K ∧
        (m = k ∨
          (m = k + 1 ∧ Even alpha ∧
            alpha < 2 * ramificationIndex K)) := by
    by_cases hxMax : x = 2 * (ramificationIndex K : Int)
    · let zeta : valuationUnitSubgroup K :=
        ⟨laws.discriminantUnit, laws.discriminant_isValuationUnit⟩
      refine ⟨k, zeta, ?_, le_rfl, ?_, Or.inl rfl⟩
      · have hkEq : k = 2 * ramificationIndex K := by
          have : (k : Int) = 2 * (ramificationIndex K : Int) := by
            rw [hkCast, hxMax]
          exact_mod_cast this
        simpa only [zeta, hkEq] using laws.discriminant_defect
      · exact hkUpper
    · by_cases hxOdd : Odd x
      · have hkOddInt : Odd (k : Int) := by rwa [hkCast]
        have hkOdd : Odd k := by exact_mod_cast hkOddInt
        have hkLt : k < 2 * ramificationIndex K := by
          have : (k : Int) < 2 * (ramificationIndex K : Int) := by
            rw [hkCast]
            omega
          exact_mod_cast this
        rcases exists_unit_quadraticDefect_eq_odd
            (K := K) k hkPos hkOdd hkLt with
          ⟨z, hzUnit, hzDefect⟩
        exact ⟨k, ⟨z, hzUnit⟩, hzDefect, le_rfl, hkUpper, Or.inl rfl⟩
      · have hxEven : Even x := Int.not_odd_iff_even.mp hxOdd
        have hkEvenInt : Even (k : Int) := by rwa [hkCast]
        have hkEven : Even k := by exact_mod_cast hkEvenInt
        have hkLt : k < 2 * ramificationIndex K := by
          have : (k : Int) < 2 * (ramificationIndex K : Int) := by
            rw [hkCast]
            omega
          exact_mod_cast this
        have hmPos : 0 < k + 1 := by omega
        have hmOdd : Odd (k + 1) := hkEven.add_one
        have hmLt : k + 1 < 2 * ramificationIndex K := by
          rcases hkEven with ⟨r, hr⟩
          omega
        rcases exists_unit_quadraticDefect_eq_odd
            (K := K) (k + 1) hmPos hmOdd hmLt with
          ⟨z, hzUnit, hzDefect⟩
        have hyEven : Even y := by
          rcases hparity with h | h | h
          · exact (hxOdd h).elim
          · exact (hxMax (by simpa only [x, R] using h)).elim
          · simpa only [y, T] using h
        have halphaEven : Even alpha := by
          rcases hxEven with ⟨r, hr⟩
          rcases hyEven with ⟨t, ht⟩
          have htarget : Even (alpha : Int) := by
            refine ⟨r + t - ramificationIndex K, ?_⟩
            rw [halphaCast]
            rcases hREven with ⟨rR, hrR⟩
            rcases hTEven with ⟨rT, hrT⟩
            dsimp only [x] at hr
            dsimp only [y] at ht
            omega
          exact_mod_cast htarget
        have halphaLt : alpha < 2 * ramificationIndex K := by
          have hRlt : R < 2 * (ramificationIndex K : Int) := by
            dsimp only [x] at hxMax
            rcases hREven with ⟨r, hr⟩
            omega
          have halphaLtInt : (alpha : Int) <
              2 * (ramificationIndex K : Int) := by
            rw [halphaCast]
            rcases hREven with ⟨r, hr⟩
            rcases hTEven with ⟨t, ht⟩
            omega
          exact_mod_cast halphaLtInt
        exact ⟨k + 1, ⟨z, hzUnit⟩, hzDefect, by omega,
          by omega, Or.inr ⟨rfl, halphaEven, halphaLt⟩⟩
  have hRnotAbove : ¬2 * (ramificationIndex K : Int) < ordUnit K a := by
    rw [haOrder]
    omega
  have haHigh : ¬2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞) := by
    simpa only [a] using hleftHigh
  have hzetaGroup : valuationUnitClassHom K zeta ∈
      beliNormGeneratorGroup K a := by
    rw [beliNormGeneratorGroup_of_high_defect K a hRnotAbove haHigh]
    have hexponent : beliHighDefectExponent K a = k := by
      unfold beliHighDefectExponent
      rw [haOrder]
      simpa only [k, x, add_comm] using rfl
    rw [hexponent]
    apply
      valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
    rw [hzetaDefect]
    exact_mod_cast hkm
  have hzetaNeighbor :
      ((∃ hleft : 1 ≤ (1 : Fin 3).val,
          valuationUnitClassHom K zeta ∈ beliNormGeneratorGroup K
            (b.valueUnit (1 : Fin 3) /
              b.valueUnit ⟨(1 : Fin 3).val - 1, by omega⟩)) ∨
        (∃ hright : (1 : Fin 3).val + 2 < 3,
          valuationUnitClassHom K zeta ∈ beliNormGeneratorGroup K
            (b.valueUnit ⟨(1 : Fin 3).val + 2, hright⟩ /
              b.valueUnit ⟨(1 : Fin 3).val + 1, by norm_num⟩))) := by
    left
    refine ⟨by norm_num, ?_⟩
    have hparameter :
        b.valueUnit (1 : Fin 3) /
            b.valueUnit ⟨(1 : Fin 3).val - 1, by omega⟩ = a := by
      dsimp only [a, adjacentParameter]
      congr 2
    rw [hparameter]
    exact hzetaGroup
  have htwistAdmissible : IsBinaryParameterAdmissible
      ((zeta : Kˣ) * c) := by
    simpa only [c] using
      b.isBinaryParameterAdmissible_mul_adjacentParameter_of_adjacentMultiplier
        hB.isGood (1 : Fin 3) (by norm_num) zeta hzetaNeighbor
  have htwistOrder : ordUnit K ((zeta : Kˣ) * c) = T := by
    rw [ordUnit_mul, (isValuationUnit_iff_ordUnit_eq_zero K
      (zeta : Kˣ)).1 zeta.property, hcOrder]
    simp
  have hcutEq : beliDefectCutoff K ((zeta : Kˣ) * c) =
      beliDefectCutoff K c := by
    unfold beliDefectCutoff
    rw [htwistOrder, hcOrder]
  have hzetaAboveCutoff : ¬2 * quadraticDefect K (zeta : Kˣ) ≤
      (beliDefectCutoff K c : ℕ∞) := by
    rw [hzetaDefect]
    have hcutCast : (beliDefectCutoff K c : Int) =
        2 * (ramificationIndex K : Int) - T := by
      unfold beliDefectCutoff
      rw [hcOrder, Int.toNat_of_nonneg]
      omega
    have hstrict : beliDefectCutoff K c < 2 * m := by
      have hstrictInt : (beliDefectCutoff K c : Int) < 2 * (m : Int) := by
        rw [hcutCast]
        have hmk : (k : Int) ≤ (m : Int) := by exact_mod_cast hkm
        rw [hkCast] at hmk
        rcases hREven with ⟨r, hr⟩
        omega
      exact_mod_cast hstrictInt
    exact_mod_cast (not_le_of_gt hstrict)
  have htwistHigh : ¬2 * beliParameterDefect K ((zeta : Kˣ) * c) ≤
      (beliDefectCutoff K ((zeta : Kˣ) * c) : ℕ∞) := by
    intro htwistLow
    rw [hcutEq] at htwistLow
    let epsilon : Kˣ := normalizedUnitPart K c
    let eta : Kˣ := (zeta : Kˣ) * epsilon
    have hepsilon : IsValuationUnit K (epsilon : K) :=
      normalizedUnitPart_isValuationUnit K c
    have hcFactor : uniformizerPowerUnit K T * epsilon = c := by
      rw [← hcOrder]
      exact uniformizerPower_mul_normalizedUnitPart K c
    have heta : IsValuationUnit K (eta : K) := by
      change ord K (((zeta : Kˣ) : K) * (epsilon : K)) = 0
      rw [ord_mul, zeta.property, hepsilon]
      simp
    have htwistFactor : uniformizerPowerUnit K T * eta =
        (zeta : Kˣ) * c := by
      dsimp only [eta]
      rw [← hcFactor]
      ac_rfl
    have hcDefect : beliParameterDefect K c =
        quadraticDefect K (-epsilon) := by
      have h := beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
        (K := K) T epsilon hepsilon hTEven
      rwa [hcFactor] at h
    have htwistDefect : beliParameterDefect K ((zeta : Kˣ) * c) =
        quadraticDefect K (-eta) := by
      have h := beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
        (K := K) T eta heta hTEven
      rwa [htwistFactor] at h
    have hlowerRaw := quadraticDefect_mul_ge_min K (-epsilon) (zeta : Kˣ)
    have hnegEta : (-epsilon) * (zeta : Kˣ) = -eta := by
      dsimp only [eta]
      apply Units.ext
      simp only [Units.val_neg, Units.val_mul]
      ring
    have hlower : min (beliParameterDefect K c)
          (quadraticDefect K (zeta : Kˣ)) ≤
        beliParameterDefect K ((zeta : Kˣ) * c) := by
      rw [hcDefect, htwistDefect]
      rwa [hnegEta] at hlowerRaw
    have htwice := mul_le_mul_left' hlower 2
    have hminLow : 2 * min (beliParameterDefect K c)
          (quadraticDefect K (zeta : Kˣ)) ≤
        (beliDefectCutoff K c : ℕ∞) :=
      htwice.trans htwistLow
    rcases le_total (beliParameterDefect K c)
        (quadraticDefect K (zeta : Kˣ)) with hle | hle
    · apply (by simpa only [c] using hrightHigh)
      simpa [min_eq_left hle] using hminLow
    · exact hzetaAboveCutoff
        (by simpa [min_eq_right hle] using hminLow)
  have hcor := principalUnit_halfOrder_add_defect_sub_e_le_spinor_sup_twist
    (K := K) c zeta m hcAdmissible htwistAdmissible
      (by rw [hcOrder]; exact hTupper) (by rwa [hcOrder])
      (by simpa only [c] using hrightHigh) htwistHigh hzetaDefect
  let gamma : Nat := Int.toNat
    (T / 2 + (m : Int) - (ramificationIndex K : Int))
  have hgammaLocal : principalUnitSquareClassSubgroup K gamma ≤
      beliSpinorGroupRepresentative K c ⊔
        beliSpinorGroupRepresentative K ((zeta : Kˣ) * c) := by
    simpa only [gamma, hcOrder] using hcor
  have hcLe : beliSpinorGroupRepresentative K c ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
    simpa only [c] using b.adjacentSpinorGroup_le_spinorNormImage
      hB.isGood (1 : Fin 3) (by norm_num)
  have htwistLe : beliSpinorGroupRepresentative K ((zeta : Kˣ) * c) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
    intro z hz
    change z ∈ Lattice.spinorNormImage (q := q) (L := L)
    apply b.twistedAdjacentSpinorGroup_subset_of_adjacentMultiplier
      hB.isGood (1 : Fin 3) (by norm_num) zeta hzetaNeighbor
    rw [beliSpinorGroup_unitSquareClass]
    change z ∈ (beliSpinorGroupRepresentative K
      ((zeta : Kˣ) * c) : Set (SquareClass K))
    exact hz
  have hgammaLe : principalUnitSquareClassSubgroup K gamma ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) :=
    hgammaLocal.trans (sup_le hcLe htwistLe)
  rcases hmShape with hmEq | ⟨hmEq, halphaEven, halphaLt⟩
  · have hgammaEq : gamma = alpha := by
      dsimp only [gamma]
      have hmCast : (m : Int) = x := by
        rw [hmEq, hkCast]
      rw [hmCast]
      have hinside : T / 2 + x - (ramificationIndex K : Int) =
          (alpha : Int) := by
        rw [halphaCast]
        rcases hREven with ⟨r, hr⟩
        rcases hTEven with ⟨t, ht⟩
        dsimp only [x]
        omega
      rw [hinside]
      simp
    rw [hgammaEq] at hgammaLe
    simpa only [alpha] using hgammaLe
  · have hgammaEq : gamma = alpha + 1 := by
      dsimp only [gamma]
      have hmCast : (m : Int) = x + 1 := by
        rw [hmEq]
        push_cast
        rw [hkCast]
      rw [hmCast]
      have hinside : T / 2 + (x + 1) -
          (ramificationIndex K : Int) = (alpha : Int) + 1 := by
        rw [halphaCast]
        rcases hREven with ⟨r, hr⟩
        rcases hTEven with ⟨t, ht⟩
        dsimp only [x]
        omega
      rw [hinside]
      simp
    have hfiltration := principalUnitSquareClassSubgroup_eq_succ_of_even
      K alpha halphaPos halphaLt halphaEven
    rw [hgammaEq, ← hfiltration] at hgammaLe
    simpa only [alpha] using hgammaLe

/-!
The preceding lemmas are the individual cases of Section 5.  The next theorem
is the exhaustive case split.  Notice that the only use of reverse duality is
to orient a case so that the bounded adjacent gap is on the left; no additional
local arithmetic assertion is introduced here.
-/

/-- Beli (2003), Theorem 1, ternary calculation, assembled from all Section 5
cases under the already isolated proved local interfaces. -/
theorem congruence_le_spinorNormImage_of_local_laws
    [BONGStructuralLaws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BinarySpinorLocalLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    (b : BONG V q L 3) (hA : b.HasPropertyA) :
    beliCongruenceSquareClassSubgroup K (b.theoremOneTwoStepDepth 0) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
  by_cases hB : b.HasPropertyB
  · let R : Int := b.order (1 : Fin 3) - b.order (0 : Fin 3)
    let T : Int := b.order (2 : Fin 3) - b.order (1 : Fin 3)
    by_cases hRDeep : 2 * (ramificationIndex K : Int) < R
    · by_cases hTDeep : 2 * (ramificationIndex K : Int) < T
      · exact b.congruence_le_spinorNormImage_of_propertyB_of_both_two_e_lt
          hB (by simpa only [R] using hRDeep)
            (by simpa only [T] using hTDeep)
      · have hTUpper : T ≤ 2 * (ramificationIndex K : Int) :=
          le_of_not_gt hTDeep
        refine b.theoremOne_congruence_le_via_reverseDual hB ?_
        intro d hvalues horders hdB
        have hleftGap := b.theoremOne_reverseDual_leftGap d horders
        have hrightGap := b.theoremOne_reverseDual_rightGap d horders
        have hdLeftUpper : d.order (1 : Fin 3) - d.order (0 : Fin 3) ≤
            2 * (ramificationIndex K : Int) := by
          simpa only [hleftGap, T] using hTUpper
        have hdRightDeep : 2 * (ramificationIndex K : Int) <
            d.order (2 : Fin 3) - d.order (1 : Fin 3) := by
          simpa only [hrightGap, R] using hRDeep
        rcases Int.even_or_odd
            (d.order (1 : Fin 3) - d.order (0 : Fin 3)) with
          hdLeftEven | hdLeftOdd
        · by_cases hdLeftLow : 2 * beliParameterDefect K
              (d.adjacentParameter (0 : Fin 3) (by norm_num)) ≤
            (beliDefectCutoff K
              (d.adjacentParameter (0 : Fin 3) (by norm_num)) : ℕ∞)
          · rcases Int.even_or_odd
                (d.order (2 : Fin 3) - d.order (1 : Fin 3)) with
              hdRightEven | hdRightOdd
            · exact
                d.congruence_le_spinorNormImage_of_propertyB_of_left_even_low_right_even
                  hdB hdLeftEven hdLeftUpper hdLeftLow hdRightEven hdRightDeep
            · exact
                d.congruence_le_spinorNormImage_of_propertyB_of_left_even_low_right_odd
                  hdB hdLeftEven hdLeftUpper hdLeftLow hdRightOdd hdRightDeep
          · exact
              d.congruence_le_spinorNormImage_of_propertyB_of_left_even_high_right_deep
                hdB hdLeftEven hdLeftUpper hdLeftLow hdRightDeep
        · rcases Int.even_or_odd
              (d.order (2 : Fin 3) - d.order (1 : Fin 3)) with
            hdRightEven | hdRightOdd
          · exact
              d.congruence_le_spinorNormImage_of_propertyB_of_left_odd_right_even
                hdB hdLeftOdd hdLeftUpper hdRightEven
          · exact
              d.congruence_le_spinorNormImage_of_propertyB_of_left_odd_right_odd
                hdB hdLeftOdd hdLeftUpper hdRightOdd
    · have hRUpper : R ≤ 2 * (ramificationIndex K : Int) :=
        le_of_not_gt hRDeep
      rcases Int.even_or_odd R with hREven | hROdd
      · by_cases hRLow : 2 * beliParameterDefect K
              (b.adjacentParameter (0 : Fin 3) (by norm_num)) ≤
            (beliDefectCutoff K
              (b.adjacentParameter (0 : Fin 3) (by norm_num)) : ℕ∞)
        · have htrigger : b.propertyBTrigger (0 : Fin 2) :=
            b.propertyBTrigger_of_even_low (0 : Fin 2)
              (by simpa [R] using hREven)
              (by simpa [R] using hRUpper) hRLow
          have hneighbors := hB.2 (0 : Fin 2) htrigger
          have hTBound := hneighbors.2 (2 : Fin 3) (by norm_num)
          have hTDeep : 2 * (ramificationIndex K : Int) < T := by
            have hTBound' : 2 * (ramificationIndex K : Int) + 1 ≤ T := by
              simpa [T] using hTBound
            omega
          rcases Int.even_or_odd T with hTEven | hTOdd
          · exact
              b.congruence_le_spinorNormImage_of_propertyB_of_left_even_low_right_even
                hB (by simpa only [R] using hREven)
                  (by simpa only [R] using hRUpper) hRLow
                  (by simpa only [T] using hTEven)
                  (by simpa only [T] using hTDeep)
          · exact
              b.congruence_le_spinorNormImage_of_propertyB_of_left_even_low_right_odd
                hB (by simpa only [R] using hREven)
                  (by simpa only [R] using hRUpper) hRLow
                  (by simpa only [T] using hTOdd)
                  (by simpa only [T] using hTDeep)
        · by_cases hTDeep : 2 * (ramificationIndex K : Int) < T
          · exact
              b.congruence_le_spinorNormImage_of_propertyB_of_left_even_high_right_deep
                hB (by simpa only [R] using hREven)
                  (by simpa only [R] using hRUpper) hRLow
                  (by simpa only [T] using hTDeep)
          · have hTUpper : T ≤ 2 * (ramificationIndex K : Int) :=
              le_of_not_gt hTDeep
            rcases Int.even_or_odd T with hTEven | hTOdd
            · by_cases hTLow : 2 * beliParameterDefect K
                    (b.adjacentParameter (1 : Fin 3) (by norm_num)) ≤
                  (beliDefectCutoff K
                    (b.adjacentParameter (1 : Fin 3) (by norm_num)) : ℕ∞)
              · have htrigger : b.propertyBTrigger (1 : Fin 2) :=
                  b.propertyBTrigger_of_even_low (1 : Fin 2)
                    (by simpa [T] using hTEven)
                    (by simpa [T] using hTUpper) hTLow
                have hneighbors := hB.2 (1 : Fin 2) htrigger
                have hRBound := hneighbors.1 (0 : Fin 3) (by norm_num)
                have hRBound' : 2 * (ramificationIndex K : Int) + 1 ≤ R := by
                  simpa [R] using hRBound
                exfalso
                omega
              · let x : Int := R / 2 + (ramificationIndex K : Int)
                let y : Int := T / 2 + (ramificationIndex K : Int)
                by_cases hparity : Odd x ∨
                    x = 2 * (ramificationIndex K : Int) ∨ Even y
                · exact
                    b.congruence_le_spinorNormImage_of_propertyB_of_both_even_high_oriented
                      hB (by simpa only [R] using hREven)
                        (by simpa only [R] using hRUpper) hRLow
                        (by simpa only [T] using hTEven)
                        (by simpa only [T] using hTUpper) hTLow
                        (by simpa only [x, y, R, T] using hparity)
                · have hyNotEven : ¬Even y := by
                    intro hy
                    exact hparity (Or.inr (Or.inr hy))
                  have hyOdd : Odd y := Int.not_even_iff_odd.mp hyNotEven
                  refine b.theoremOne_congruence_le_via_reverseDual hB ?_
                  intro d hvalues horders hdB
                  have hleftGap := b.theoremOne_reverseDual_leftGap d horders
                  have hrightGap := b.theoremOne_reverseDual_rightGap d horders
                  have hleftParameter :=
                    b.theoremOne_reverseDual_leftParameter d hvalues
                  have hrightParameter :=
                    b.theoremOne_reverseDual_rightParameter d hvalues
                  have hdLeftEven : Even
                      (d.order (1 : Fin 3) - d.order (0 : Fin 3)) := by
                    simpa only [hleftGap, T] using hTEven
                  have hdLeftUpper :
                      d.order (1 : Fin 3) - d.order (0 : Fin 3) ≤
                        2 * (ramificationIndex K : Int) := by
                    simpa only [hleftGap, T] using hTUpper
                  have hdLeftHigh : ¬2 * beliParameterDefect K
                        (d.adjacentParameter (0 : Fin 3) (by norm_num)) ≤
                      (beliDefectCutoff K
                        (d.adjacentParameter (0 : Fin 3) (by norm_num)) : ℕ∞) := by
                    simpa only [hleftParameter] using hTLow
                  have hdRightEven : Even
                      (d.order (2 : Fin 3) - d.order (1 : Fin 3)) := by
                    simpa only [hrightGap, R] using hREven
                  have hdRightUpper :
                      d.order (2 : Fin 3) - d.order (1 : Fin 3) ≤
                        2 * (ramificationIndex K : Int) := by
                    simpa only [hrightGap, R] using hRUpper
                  have hdRightHigh : ¬2 * beliParameterDefect K
                        (d.adjacentParameter (1 : Fin 3) (by norm_num)) ≤
                      (beliDefectCutoff K
                        (d.adjacentParameter (1 : Fin 3) (by norm_num)) : ℕ∞) := by
                    simpa only [hrightParameter] using hRLow
                  apply
                    d.congruence_le_spinorNormImage_of_propertyB_of_both_even_high_oriented
                      hdB hdLeftEven hdLeftUpper hdLeftHigh
                        hdRightEven hdRightUpper hdRightHigh
                  left
                  simpa only [hleftGap, y, T] using hyOdd
            · have htrigger : b.propertyBTrigger (1 : Fin 2) := by
                unfold propertyBTrigger
                left
                constructor
                · simpa [T] using
                    (show T ≤ 2 * (ramificationIndex K : Int) + 1 by omega)
                · simpa [T] using hTOdd
              have hneighbors := hB.2 (1 : Fin 2) htrigger
              have hRBound := hneighbors.1 (0 : Fin 3) (by norm_num)
              have hRBound' : 2 * (ramificationIndex K : Int) + 1 ≤ R := by
                simpa [R] using hRBound
              exfalso
              omega
      · rcases Int.even_or_odd T with hTEven | hTOdd
        · exact
            b.congruence_le_spinorNormImage_of_propertyB_of_left_odd_right_even
              hB (by simpa only [R] using hROdd)
                (by simpa only [R] using hRUpper)
                (by simpa only [T] using hTEven)
        · exact
            b.congruence_le_spinorNormImage_of_propertyB_of_left_odd_right_odd
              hB (by simpa only [R] using hROdd)
                (by simpa only [R] using hRUpper)
                (by simpa only [T] using hTOdd)
  · exact b.congruence_le_spinorNormImage_of_not_propertyB hA hB

end BONG

/-- The Section 5 ternary law package is now a theorem, not a mathematical
assumption.  Every formerly abstract dependency is instantiated by its proved
dyadic or Section 4 implementation before the exhaustive calculation is used. -/
noncomputable instance beliTheoremOneTernaryLawsProved :
    BeliTheoremOneTernaryLaws.{u, v} K where
  congruence_le_spinorNormImage b hA := by
    letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
    letI : UnitQuadraticDefectParityLaws K :=
      unitQuadraticDefectParityLawsProved
    letI : DyadicDiscriminantClassLaws K :=
      Dyadic.dyadicDiscriminantClassLawsProved
    letI : DyadicUnramifiedNormLaws K :=
      Dyadic.dyadicUnramifiedNormLawsProvedDirect
    letI : BONGStructuralLaws.{u, v} K := bongStructuralLawsProved K
    letI : BeliLemma47Laws.{u, v} K := beliLemma47LawsProved K
    letI : BONGReverseDualLaws.{u, v} K :=
      BONGStructuralLaws.toBONGReverseDualLaws
    letI : BeliLemma49Laws.{u, v} K :=
      BONG.beliLemma49LawsOfReverseDual
    letI : BinarySpinorLocalLaws.{u, v} K :=
      binarySpinorLocalLawsProved
    letI : BinaryNormGeneratorLocalLaws.{u, v} K :=
      binaryNormGeneratorLocalLawsProved
    exact BONG.congruence_le_spinorNormImage_of_local_laws b hA

end Bong
