/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryScaledShearSpinor
import Bong.Bong.BeliCorollary315

/-!
# The even shifted-model inclusion in the low binary range

For an even parameter order `0 ≤ R ≤ 2e` outside the low-defect branch,
Beli's shift

`T = -2 ⌊(2e-R)/4⌋`

is admissible.  A defect-adapted shear at order `T` satisfies exactly the
five integrality inequalities required by the scaled-shear spinor theorem.
This proves the difficult reverse containment in Xu (1993), Proposition 2.3
without assuming `BinarySpinorLocalLaws`.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A field unit of nonnegative order belongs to the valuation ring. -/
theorem unit_mem_integerRing_of_ordUnit_nonneg (a : Kˣ)
    (ha : 0 ≤ ordUnit K a) : (a : K) ∈ IntegerRing K := by
  apply (mem_integerRing_iff K).2
  change (0 : WithTop Int) ≤ ord K (a : K)
  rw [← coe_ordUnit]
  exact_mod_cast ha

/-- The reverse containment supplied by the even shifted model, written for
the normalized representative `πᴿε`. -/
theorem evenShiftedNormGeneratorGroup_le_spinorNormImage_binaryDiagonal
    (R : Int) (ε : Kˣ)
    (hε : IsValuationUnit K (ε : K))
    (ha : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hRnonneg : 0 ≤ R)
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hEven : Even R)
    (hdLower : ¬2 * quadraticDefect K (-ε) ≤
      (Int.toNat
        (2 * (ramificationIndex K : Int) - R) : ℕ∞)) :
    beliNormGeneratorSquareClassGroup K
        (uniformizerPowerUnit K
          (beliLemma313EvenShift (K := K) R) * ε) ≤
      Lattice.spinorNormImageSubgroup
        (q := QuadraticSpace.binaryModel
          (uniformizerPowerUnit K R * ε) 0)
        (L := binaryModelLattice (K := K)) := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  rcases hEven with ⟨r, hr⟩
  let j : Int :=
    (2 * (ramificationIndex K : Int) - R) / 4
  let T : Int := beliLemma313EvenShift (K := K) R
  let s : Int := R / 2 + j
  let source : Kˣ := uniformizerPowerUnit K R * ε
  let shifted : Kˣ := uniformizerPowerUnit K T * ε
  let t : Kˣ := uniformizerPowerUnit K s
  have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
  have hRhalf : R / 2 = r := by omega
  have hnumeratorNonneg :
      0 ≤ 2 * (ramificationIndex K : Int) - R := by omega
  have hjNonneg : 0 ≤ j := by
    exact Int.ediv_nonneg hnumeratorNonneg (by omega)
  have hdivisionLower :=
    Int.ediv_mul_le (2 * (ramificationIndex K : Int) - R)
      (by norm_num : (4 : Int) ≠ 0)
  have hjBound :
      2 * j ≤ (ramificationIndex K : Int) - R / 2 := by
    dsimp only [j]
    omega
  have hT : T = -2 * j := by rfl
  have hEvenT : Even T := by
    refine ⟨-j, ?_⟩
    omega
  have hsNonneg : 0 ≤ s := by
    dsimp only [s]
    omega
  have hsLeE : s ≤ (ramificationIndex K : Int) := by
    dsimp only [s]
    omega
  have hsLeEsubJ :
      s ≤ (ramificationIndex K : Int) - j := by
    dsimp only [s]
    omega
  have htwoJLeE : 2 * j ≤ (ramificationIndex K : Int) := by
    omega
  have hsourceOrder : ordUnit K source = R := by
    dsimp only [source]
    exact ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have hshiftedOrder : ordUnit K shifted = T := by
    dsimp only [shifted]
    exact ordUnit_uniformizerPower_mul_valuationUnit ε hε T
  have htOrder : ordUnit K t = s := by
    exact ordUnit_uniformizerPowerUnit (K := K) s
  have hshiftedAdmissible : IsBinaryParameterAdmissible shifted := by
    dsimp only [shifted, T]
    exact beliLemma313EvenShift_isBinaryParameterAdmissible
      (K := K) R ε hε ha hRupper hdLower
  rcases exists_defectAdaptedShear shifted hshiftedAdmissible
      (by rw [hshiftedOrder]; exact hEvenT) with
    ⟨c, htwo, hdiag, hcross, _hsecond⟩
  have hc0 : c ≠ 0 := by
    intro hc
    rw [hc, mul_zero, ord_zero] at hcross
    have : (⊤ : WithTop Int) =
        (((ramificationIndex K : Int) + ordUnit K shifted / 2 : Int) :
          WithTop Int) := hcross
    exact WithTop.top_ne_coe this
  let cU : Kˣ := Units.mk0 c hc0
  have hcOrder : ordUnit K cU = -j := by
    apply WithTop.coe_injective
    have hcross' := hcross
    rw [ord_mul, ← ramificationIndex_spec] at hcross'
    have hcOrd : ord K c = (ordUnit K cU : WithTop Int) := by
      simpa [cU] using (coe_ordUnit K cU).symm
    rw [hcOrd, hshiftedOrder, hT] at hcross'
    norm_cast at hcross' ⊢
    omega
  have hfactor : shifted * t ^ 2 = source := by
    have hpower :
        uniformizerPowerUnit K T * uniformizerPowerUnit K s ^ 2 =
          uniformizerPowerUnit K R := by
      unfold uniformizerPowerUnit
      rw [pow_two, ← zpow_add, ← zpow_add]
      congr 1
      dsimp only [s]
      omega
    dsimp only [shifted, t, source]
    calc
      (uniformizerPowerUnit K T * ε) *
            uniformizerPowerUnit K s ^ 2 =
          (uniformizerPowerUnit K T *
            uniformizerPowerUnit K s ^ 2) * ε := by ac_rfl
      _ = uniformizerPowerUnit K R * ε := by rw [hpower]
  have hsourceIntegral : (source : K) ∈ IntegerRing K :=
    unit_mem_integerRing_of_ordUnit_nonneg source
      (by rw [hsourceOrder]; exact hRnonneg)
  have htIntegral : (t : K) ∈ IntegerRing K :=
    unit_mem_integerRing_of_ordUnit_nonneg t
      (by rw [htOrder]; exact hsNonneg)
  have htcOrder : ordUnit K (t * cU) = R / 2 := by
    simp only [ordUnit_mul, htOrder, hcOrder]
    dsimp only [s]
    omega
  have htcIntegral : (t : K) * c ∈ IntegerRing K := by
    have hmem := unit_mem_integerRing_of_ordUnit_nonneg (t * cU)
      (by rw [htcOrder]; omega)
    simpa [cU] using hmem
  let twoU : Kˣ := Units.mk0 (2 : K) (by norm_num)
  have htwoOrder : ordUnit K twoU = (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, ramificationIndex_spec]
    rfl
  have htwoDivTOrder : ordUnit K (twoU * t⁻¹) =
      (ramificationIndex K : Int) - s := by
    simp only [ordUnit_mul, ordUnit_inv, htwoOrder, htOrder]
    omega
  have htwoDivT : (2 : K) / (t : K) ∈ IntegerRing K := by
    have hmem := unit_mem_integerRing_of_ordUnit_nonneg (twoU * t⁻¹)
      (by rw [htwoDivTOrder]; omega)
    simpa [twoU, div_eq_mul_inv] using hmem
  have htwoCDivTOrder : ordUnit K (twoU * cU * t⁻¹) =
      (ramificationIndex K : Int) - j - s := by
    simp only [ordUnit_mul, ordUnit_inv, htwoOrder, hcOrder, htOrder]
    omega
  have htwoCDivT : (2 : K) * c / (t : K) ∈ IntegerRing K := by
    have hmem :=
      unit_mem_integerRing_of_ordUnit_nonneg (twoU * cU * t⁻¹)
        (by rw [htwoCDivTOrder]; exact sub_nonneg.mpr hsLeEsubJ)
    simpa [twoU, cU, div_eq_mul_inv, mul_assoc] using hmem
  have htwoADivTSqOrder :
      ordUnit K (twoU * source * (t ^ 2)⁻¹) =
        (ramificationIndex K : Int) + R - 2 * s := by
    simp only [ordUnit_mul, ordUnit_inv, ordUnit_pow,
      htwoOrder, hsourceOrder, htOrder]
    omega
  have htwoADivTSq :
      (2 : K) * (source : K) / (t : K) ^ 2 ∈ IntegerRing K := by
    have hmem := unit_mem_integerRing_of_ordUnit_nonneg
      (twoU * source * (t ^ 2)⁻¹) (by
        rw [htwoADivTSqOrder]
        dsimp only [s]
        omega)
    simpa [twoU, div_eq_mul_inv, mul_assoc] using hmem
  exact
    beliNormGeneratorSquareClassGroup_le_spinorNormImage_binaryDiagonal_of_scaledShear
      source shifted t c htwo hdiag hsourceIntegral hfactor htIntegral
        htcIntegral htwoDivT htwoCDivT htwoADivTSq

end BONG

end Bong
