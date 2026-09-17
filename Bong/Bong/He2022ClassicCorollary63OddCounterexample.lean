/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicCorollary63
import Bong.Bong.He2022ClassicProfiles
import Bong.Bong.BeliLemma43ConstructionProof
import Bong.Bong.Beli2009JordanAlphaTransport

/-!
# The odd-rank obstruction to He (2024), Corollary 6.3

The author-corrected v5 statement of Corollary 6.3 is unrestricted in parity,
but its proof treats only even `n`.  This file gives a counterexample to the
odd statement.  Over every dyadic context with absolute ramification index
two, the exact coefficient profile

`[1, -1, 1, -u, u * π², -u]`, with `d(u)=1`,

is realized by a classic integral good BONG.  The odd clause of Theorem 1.1
proves that the resulting rank-six lattice is classic `3`-universal, while
the last BONG orders are `2, 0`.

For the isometry-level conclusion, the same six coefficients are reordered
as `[1, -1, 1, -u, -u, u * π²]`.  They have nondecreasing orders and hence
give an actual integral orthogonal basis lattice.  Beli's invariance of the
orders of good BONGs under integral isometry then separates the two lattices
at the fifth entry.  Thus the source lattice is not isometric to the diagonal
lattice with the same coefficients.  No manuscript source is embedded here.
-/

namespace Bong

open Dyadic Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG

/-- The six coefficients of the ramification-two odd counterexample. -/
noncomputable def heClassicCorollary63OddCoefficients (u : Kˣ) :
    Fin 6 → Kˣ :=
  ![1, -1, 1, -u,
    u * uniformizerPowerUnit K 2, -u]

/-- The same six coefficients, reordered into nondecreasing valuation order. -/
noncomputable def heClassicCorollary63OddSortedCoefficients (u : Kˣ) :
    Fin 6 → Kˣ :=
  ![1, -1, 1, -u, -u,
    u * uniformizerPowerUnit K 2]

private theorem heClassicCorollary63Odd_prefixProduct_four
    (u : Kˣ)
    (R : DiagonalBONGRealization
      (heClassicCorollary63OddCoefficients (K := K) u)) :
    R.bong.prefixProduct 4 = u := by
  rw [R.bong.prefixProduct_succ 3 (by norm_num),
    R.bong.prefixProduct_succ 2 (by norm_num),
    R.bong.prefixProduct_succ 1 (by norm_num),
    R.bong.prefixProduct_succ 0 (by norm_num),
    R.bong.prefixProduct_zero,
    R.valueUnit_eq, R.valueUnit_eq, R.valueUnit_eq, R.valueUnit_eq]
  simp [heClassicCorollary63OddCoefficients]

private theorem isBinaryParameterAdmissible_neg_uniformizerPower_neg_two
    (he : ramificationIndex K = 2) :
    IsBinaryParameterAdmissible
      (-(uniformizerPowerUnit K (-2))) := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  apply (isBinaryParameterAdmissible_iff_beli _).2
  apply Or.inr
  constructor
  · simpa only [neg_neg] using
      (GoodBONG.isSquare_uniformizerPowerUnit_of_even (K := K) (-2)
        ⟨-1, by norm_num⟩)
  · rw [ordUnit_neg, ordUnit_uniformizerPowerUnit, he]
    norm_num

/-- The coefficient list satisfies every adjacent binary realizability
condition in Beli's Lemma 4.3. -/
private theorem heClassicCorollary63OddCoefficients_adjacent
    (u : Kˣ) (hu : IsValuationUnit K (u : K))
    (he : ramificationIndex K = 2) :
    CoefficientAdjacentAdmissible
      (heClassicCorollary63OddCoefficients (K := K) u) := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  intro i hi
  have huOrder : ordUnit K u = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K u).1 hu
  have hiCases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨
      i.val = 3 ∨ i.val = 4 := by omega
  rcases hiCases with hi0 | hi1 | hi2 | hi3 | hi4
  · have : i = (0 : Fin 6) := Fin.ext hi0
    subst i
    simpa [heClassicCorollary63OddCoefficients] using
      (isBinaryParameterAdmissible_neg_one (K := K))
  · have : i = (1 : Fin 6) := Fin.ext hi1
    subst i
    simpa [heClassicCorollary63OddCoefficients] using
      (isBinaryParameterAdmissible_neg_one (K := K))
  · have : i = (2 : Fin 6) := Fin.ext hi2
    subst i
    simpa [heClassicCorollary63OddCoefficients] using
      (isBinaryParameterAdmissible_neg_of_ordUnit_nonneg
        (K := K) u (by omega))
  · have : i = (3 : Fin 6) := Fin.ext hi3
    subst i
    have hpNonnegative :
        0 ≤ ordUnit K (uniformizerPowerUnit K 2) := by
      rw [ordUnit_uniformizerPowerUnit]
      norm_num
    simpa [heClassicCorollary63OddCoefficients, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using
      (isBinaryParameterAdmissible_neg_of_ordUnit_nonneg
        (K := K) (uniformizerPowerUnit K 2) hpNonnegative)
  · have : i = (4 : Fin 6) := Fin.ext hi4
    subst i
    simpa [heClassicCorollary63OddCoefficients, div_eq_mul_inv,
      uniformizerPowerUnit, zpow_neg, mul_comm, mul_left_comm, mul_assoc] using
      (isBinaryParameterAdmissible_neg_uniformizerPower_neg_two
        (K := K) he)

/-- The prescribed orders are weakly increasing two steps at a time, as
required for a good BONG. -/
private theorem heClassicCorollary63OddCoefficients_twoStep
    (u : Kˣ) (hu : IsValuationUnit K (u : K)) :
    CoefficientWeakTwoStep (K := K)
      (heClassicCorollary63OddCoefficients (K := K) u) := by
  intro i hi
  have huOrder : ordUnit K u = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K u).1 hu
  have honeOrder : ordUnit K (1 : Kˣ) = 0 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    simp
  have hiCases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨
      i.val = 3 := by omega
  rcases hiCases with hi0 | hi1 | hi2 | hi3
  all_goals
    first
    | have : i = (0 : Fin 6) := Fin.ext hi0; subst i
    | have : i = (1 : Fin 6) := Fin.ext hi1; subst i
    | have : i = (2 : Fin 6) := Fin.ext hi2; subst i
    | have : i = (3 : Fin 6) := Fin.ext hi3; subst i
  all_goals
    simp [heClassicCorollary63OddCoefficients, ordUnit_neg,
      ordUnit_mul, ordUnit_uniformizerPowerUnit, huOrder, honeOrder]

/-- The reordered diagonal coefficients satisfy every adjacent binary
realizability condition. -/
private theorem heClassicCorollary63OddSortedCoefficients_adjacent
    (u : Kˣ) (hu : IsValuationUnit K (u : K)) :
    CoefficientAdjacentAdmissible
      (heClassicCorollary63OddSortedCoefficients (K := K) u) := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  intro i hi
  have huOrder : ordUnit K u = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K u).1 hu
  have hiCases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨
      i.val = 3 ∨ i.val = 4 := by omega
  rcases hiCases with hi0 | hi1 | hi2 | hi3 | hi4
  · have : i = (0 : Fin 6) := Fin.ext hi0
    subst i
    simpa [heClassicCorollary63OddSortedCoefficients] using
      (isBinaryParameterAdmissible_neg_one (K := K))
  · have : i = (1 : Fin 6) := Fin.ext hi1
    subst i
    simpa [heClassicCorollary63OddSortedCoefficients] using
      (isBinaryParameterAdmissible_neg_one (K := K))
  · have : i = (2 : Fin 6) := Fin.ext hi2
    subst i
    simpa [heClassicCorollary63OddSortedCoefficients] using
      (isBinaryParameterAdmissible_neg_of_ordUnit_nonneg
        (K := K) u (by omega))
  · have : i = (3 : Fin 6) := Fin.ext hi3
    subst i
    have hnegOne : 0 ≤ ordUnit K (-1 : Kˣ) := by
      rw [ordUnit_neg]
      have hone : ordUnit K (1 : Kˣ) = 0 := by
        apply WithTop.coe_injective
        rw [coe_ordUnit]
        simp
      omega
    simpa [heClassicCorollary63OddSortedCoefficients] using
      (isBinaryParameterAdmissible_neg_of_ordUnit_nonneg
        (K := K) (-1 : Kˣ) hnegOne)
  · have : i = (4 : Fin 6) := Fin.ext hi4
    subst i
    have hpNonnegative :
        0 ≤ ordUnit K (uniformizerPowerUnit K 2) := by
      rw [ordUnit_uniformizerPowerUnit]
      norm_num
    simpa [heClassicCorollary63OddSortedCoefficients, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using
      (isBinaryParameterAdmissible_neg_of_ordUnit_nonneg
        (K := K) (uniformizerPowerUnit K 2) hpNonnegative)

/-- The reordered diagonal coefficients satisfy weak two-step monotonicity. -/
private theorem heClassicCorollary63OddSortedCoefficients_twoStep
    (u : Kˣ) (hu : IsValuationUnit K (u : K)) :
    CoefficientWeakTwoStep (K := K)
      (heClassicCorollary63OddSortedCoefficients (K := K) u) := by
  intro i hi
  have huOrder : ordUnit K u = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K u).1 hu
  have honeOrder : ordUnit K (1 : Kˣ) = 0 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    simp
  have hiCases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨
      i.val = 3 := by omega
  rcases hiCases with hi0 | hi1 | hi2 | hi3
  all_goals
    first
    | have : i = (0 : Fin 6) := Fin.ext hi0; subst i
    | have : i = (1 : Fin 6) := Fin.ext hi1; subst i
    | have : i = (2 : Fin 6) := Fin.ext hi2; subst i
    | have : i = (3 : Fin 6) := Fin.ext hi3; subst i
  all_goals
    simp [heClassicCorollary63OddSortedCoefficients, ordUnit_neg,
      ordUnit_mul, ordUnit_uniformizerPowerUnit, huOrder, honeOrder]

/-- Counterexample to the unrestricted odd clause of v5 Corollary 6.3.  The
second lattice is an integral orthogonal basis lattice with exactly the same
six coefficients, reordered by swapping the last two entries.  The two
lattices are not integrally isometric. -/
theorem exists_he2022ClassicCorollary63_odd_counterexample
    (he : ramificationIndex K = 2) :
    ∃ (u : Kˣ)
      (L : Lattice K (Fin 6 → K))
      (a : GoodBONG
          (coefficientDiagonalSpace
            (heClassicCorollary63OddCoefficients (K := K) u)) L 6)
      (D : Lattice K (Fin 6 → K))
      (d : GoodBONG
          (coefficientDiagonalSpace
            (heClassicCorollary63OddSortedCoefficients (K := K) u)) D 6),
      Lattice.IsClassicIntegral
          (coefficientDiagonalSpace
            (heClassicCorollary63OddCoefficients (K := K) u)) L ∧
        Lattice.IsClassicNUniversal.{u, u, u}
          (coefficientDiagonalSpace
            (heClassicCorollary63OddCoefficients (K := K) u)) L 3 ∧
        (∀ i, a.order i = ![0, 0, 0, 0, 2, 0] i) ∧
        D = Lattice.basisLattice d.toBONG.basis ∧
        (∀ i, d.valueUnit i =
          heClassicCorollary63OddSortedCoefficients (K := K) u i) ∧
        ¬ Lattice.IsIsometric
          (coefficientDiagonalSpace
            (heClassicCorollary63OddCoefficients (K := K) u))
          (coefficientDiagonalSpace
            (heClassicCorollary63OddSortedCoefficients (K := K) u))
          L D := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  letI : HilbertSymbolLaws K := hilbertSymbolLawsProved
  letI : DyadicDiscriminantClassLaws K :=
    dyadicDiscriminantClassLawsProved
  obtain ⟨u, hu, huDefect⟩ :=
    exists_unit_quadraticDefect_eq_odd (K := K) 1 (by norm_num)
      odd_one (by rw [he]; norm_num)
  let c := heClassicCorollary63OddCoefficients (K := K) u
  have hadjacent : CoefficientAdjacentAdmissible c :=
    heClassicCorollary63OddCoefficients_adjacent u hu he
  have htwoStep : CoefficientWeakTwoStep (K := K) c :=
    heClassicCorollary63OddCoefficients_twoStep u hu
  let R := diagonalBONGRealizationOfCriteria c hadjacent htwoStep
  let a : GoodBONG (coefficientDiagonalSpace c) R.lattice 6 :=
    ⟨R.bong, R.isGood htwoStep⟩
  have huOrder : ordUnit K u = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K u).1 hu
  have honeOrder : ordUnit K (1 : Kˣ) = 0 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    simp
  have horders : ∀ i : Fin 6,
      a.order i = ![0, 0, 0, 0, 2, 0] i := by
    intro i
    change R.bong.order i = _
    rw [R.order_eq]
    fin_cases i <;>
      simp [c, heClassicCorollary63OddCoefficients, ordUnit_neg,
        ordUnit_mul, ordUnit_uniformizerPowerUnit, huOrder, honeOrder]
  have hClassic :
      Lattice.IsClassicIntegral (coefficientDiagonalSpace c) R.lattice := by
    apply (a.isClassicIntegral_iff_firstOrders).2
    constructor
    · rw [horders 0]
      norm_num
    · rw [horders 0, horders 1]
      norm_num
  have hPrefix :
      a.heClassicSignedPrefixDefect 2 4 = (1 : ℚ) := by
    have hproduct : a.toBONG.prefixProduct 4 = u := by
      change R.bong.prefixProduct 4 = u
      exact heClassicCorollary63Odd_prefixProduct_four u R
    change GoodBONG.defectOrder (K := K)
      ((-1 : Kˣ) ^ 2 * a.toBONG.prefixProduct 4) = (1 : ℚ)
    rw [hproduct]
    norm_num
    unfold GoodBONG.defectOrder
    rw [huDefect]
    exact WithTop.map_coe (fun m : Nat ↦ (m : ℚ)) 1
  have hOrder3 : a.order (⟨3, by omega⟩ : Fin 6) = 0 := by
    simpa using horders 3
  have hOrder4 : a.order (⟨3 + 1, by omega⟩ : Fin 6) = 2 := by
    simpa using horders 4
  have hOrder5 : a.order (⟨3 + 2, by omega⟩ : Fin 6) = 0 := by
    simpa using horders 5
  have hConditions : a.HeClassicTheorem11Conditions 3 := by
    refine
      { rank_bound := by norm_num
        initial_orders := ?_
        parity_branch := Or.inr ?_ }
    · intro i
      fin_cases i
      · simpa using horders 0
      · simpa using horders 1
      · simpa using horders 2
    · refine
        { parity := by norm_num
          order_n1 := Or.inl ?_
          zero_branch := ?_
          upper_branch := ?_
          last_gap := ?_ }
      · exact hOrder3
      · intro _hzero
        constructor
        · exact Or.inl hPrefix
        · rintro ⟨_heLarge, _h3, h4, _hPrefixLarge⟩
          rw [hOrder4] at h4
          norm_num at h4
      · intro _htrigger
        constructor
        · intro _heven
          apply Or.inl
          rw [hOrder3, hOrder4, hOrder5, he]
          norm_num
        · intro hodd
          have hnotOdd : ¬ Odd
              (a.order (⟨3 + 1, by omega⟩ : Fin 6) -
                a.order (⟨3, by omega⟩ : Fin 6)) := by
            rw [hOrder3, hOrder4]
            norm_num
          exact (hnotOdd hodd).elim
      · rw [hOrder4, hOrder5, he]
        norm_num
  have hUniversal :
      Lattice.IsClassicNUniversal.{u, u, u}
        (coefficientDiagonalSpace c) R.lattice 3 :=
    (a.he2022ClassicTheorem11 (by norm_num) hClassic).2 hConditions
  let s := heClassicCorollary63OddSortedCoefficients (K := K) u
  have hsAdjacent : CoefficientAdjacentAdmissible s :=
    heClassicCorollary63OddSortedCoefficients_adjacent u hu
  have hsTwoStep : CoefficientWeakTwoStep (K := K) s :=
    heClassicCorollary63OddSortedCoefficients_twoStep u hu
  let S := diagonalBONGRealizationOfCriteria s hsAdjacent hsTwoStep
  let d : GoodBONG (coefficientDiagonalSpace s) S.lattice 6 :=
    ⟨S.bong, S.isGood hsTwoStep⟩
  have hsOrders : ∀ i : Fin 6,
      d.order i = ![0, 0, 0, 0, 0, 2] i := by
    intro i
    change S.bong.order i = _
    rw [S.order_eq]
    fin_cases i <;>
      simp [s, heClassicCorollary63OddSortedCoefficients, ordUnit_neg,
        ordUnit_mul, ordUnit_uniformizerPowerUnit, huOrder, honeOrder]
  have hsMonotone : Monotone (fun i : Fin 6 ↦ d.order i) := by
    rw [Fin.monotone_iff_le_succ]
    intro i
    fin_cases i <;> simp [hsOrders]
  have hsBasis : S.lattice = Lattice.basisLattice d.toBONG.basis :=
    d.toBONG.lattice_eq_basisLattice_of_order_monotone
      (fun i j hij ↦ hsMonotone hij)
  have hsValues : ∀ i, d.valueUnit i =
      heClassicCorollary63OddSortedCoefficients (K := K) u i := by
    intro i
    exact S.valueUnit_eq i
  have hNotIsometric : ¬ Lattice.IsIsometric
      (coefficientDiagonalSpace c) (coefficientDiagonalSpace s)
      R.lattice S.lattice := by
    rintro ⟨f⟩
    have hsame := a.sameOrders_of_latticeIsometry d f
    have hfour := hsame (4 : Fin 6)
    rw [horders 4, hsOrders 4] at hfour
    simp at hfour
  exact ⟨u, R.lattice, a, S.lattice, d, hClassic, hUniversal,
    horders, hsBasis, hsValues, hNotIsometric⟩

end BONG

end Bong
