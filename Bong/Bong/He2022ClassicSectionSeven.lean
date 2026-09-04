/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicPublishedRepresentation
import Bong.Bong.He2022ClassicLemma58
import Bong.Bong.HeHu2022Theorem12

/-!
# He (2024), Section 7: the explicit classic testing family

This file fixes the exact bundled meaning of Theorem 1.3 and proves its
necessity half for the literal finite table `C_e^n`.  In particular, the
family contains actual classic integral lattices, rather than condition-only
surrogates, and deletion minimality is stated for literal table entries.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Lattice.QuadraticLatticeModel

/-- Integral isometry of bundled quadratic lattices. -/
def IsIntegrallyIsometric (X Y : QuadraticLatticeModel (K := K)) : Prop := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup Y.Carrier := Y.addCommGroup
  letI : Module K Y.Carrier := Y.module
  exact Lattice.IsIsometric X.form Y.form X.lattice Y.lattice

/-- The diagonal change of basis between square-equivalent even `C₁`
rows is trivial except at the final coefficient. -/
def heClassicEvenC1SquareScale (pairs : Nat) (s : Kˣ) :
    Fin (2 * pairs + 2) → Kˣ := fun i =>
  if i.val = 2 * pairs + 1 then s else 1

theorem heClassicEvenC1_coefficients_mul_square
    (pairs : Nat) (c d s : Kˣ) (h : c = d * s ^ 2) (i : Fin (2 * pairs + 2)) :
    heClassicEvenC1 (K := K) pairs c i =
      heClassicEvenC1 (K := K) pairs d i *
        heClassicEvenC1SquareScale pairs s i ^ 2 := by
  by_cases hlast : i.val = 2 * pairs + 1
  · have hi : i = Fin.natAdd (2 * pairs) (1 : Fin 2) := by
      apply Fin.ext
      simpa using hlast
    rw [hi, heClassicEvenC1_tail, heClassicEvenC1_tail]
    simp [heClassicEvenC1SquareScale, h]
  · by_cases hhead : i.val < 2 * pairs
    · let j : Fin (2 * pairs) := ⟨i.val, hhead⟩
      have hi : i = Fin.castAdd 2 j := Fin.ext rfl
      rw [hi, heClassicEvenC1_head, heClassicEvenC1_head]
      have hjNotLast : j.val ≠ 2 * pairs + 1 := by omega
      simp [heClassicEvenC1SquareScale, hjNotLast]
    · have hmiddle : i.val = 2 * pairs := by omega
      have hi : i = Fin.natAdd (2 * pairs) (0 : Fin 2) := by
        apply Fin.ext
        simpa using hmiddle
      rw [hi, heClassicEvenC1_tail, heClassicEvenC1_tail]
      simp [heClassicEvenC1SquareScale]

/-- Square-equivalent unit parameters give isometric literal `C₁` lattices,
not merely isometric ambient spaces. -/
theorem heClassicEvenC1Model_isIsometric_of_mul_square
    (pairs : Nat) (c d s : Kˣ)
    (hc : ordUnit K c = 0) (hd : ordUnit K d = 0)
    (hsUnit : IsValuationUnit K (s : K))
    (h : c = d * s ^ 2) :
    (heClassicEvenC1Model (K := K) pairs c (by omega)).IsIntegrallyIsometric
      (heClassicEvenC1Model (K := K) pairs d (by omega)) := by
  let source := heClassicEvenC1 (K := K) pairs c
  let target := heClassicEvenC1 (K := K) pairs d
  let scale := heClassicEvenC1SquareScale pairs s
  have hsourceMono : ∀ i j, i ≤ j →
      ordUnit K (source i) ≤ ordUnit K (source j) := by
    intro i j _hij
    rw [show ordUnit K (source i) = 0 by
      simp only [source, heClassicEvenC1_order, hc]
      split <;> rfl,
      show ordUnit K (source j) = 0 by
        simp only [source, heClassicEvenC1_order, hc]
        split <;> rfl]
  have htargetMono : ∀ i j, i ≤ j →
      ordUnit K (target i) ≤ ordUnit K (target j) := by
    intro i j _hij
    rw [show ordUnit K (target i) = 0 by
      simp only [target, heClassicEvenC1_order, hd]
      split <;> rfl,
      show ordUnit K (target j) = 0 by
        simp only [target, heClassicEvenC1_order, hd]
        split <;> rfl]
  have hscaleUnit : ∀ i, IsValuationUnit K (scale i : K) := by
    intro i
    unfold scale heClassicEvenC1SquareScale
    split
    · exact hsUnit
    · simp [IsValuationUnit]
  have hcoeff : ∀ i, source i = target i * scale i ^ 2 := by
    intro i
    exact heClassicEvenC1_coefficients_mul_square pairs c d s h i
  unfold IsIntegrallyIsometric
  change Lattice.IsIsometric
    (BONG.coefficientDiagonalSpace source)
    (BONG.coefficientDiagonalSpace target)
    (heHuExactRealization source
      (heClassicEvenC1_adjacentAdmissible pairs c (by omega))
      (heClassicEvenC1_weakTwoStep pairs c (by omega))).lattice
    (heHuExactRealization target
      (heClassicEvenC1_adjacentAdmissible pairs d (by omega))
      (heClassicEvenC1_weakTwoStep pairs d (by omega))).lattice
  exact heHuExactModel_isIsometric_of_pointwise_unit_square
    source target scale
    (heClassicEvenC1_adjacentAdmissible pairs c (by omega))
    (heClassicEvenC1_weakTwoStep pairs c (by omega))
    (heClassicEvenC1_adjacentAdmissible pairs d (by omega))
    (heClassicEvenC1_weakTwoStep pairs d (by omega))
    hsourceMono htargetMono hscaleUnit hcoeff

/-- The diagonal change of basis between square-equivalent odd `C₁`
rows is trivial except at the final coefficient. -/
def heClassicOddC1SquareScale (pairs : Nat) (s : Kˣ) :
    Fin (2 * pairs + 3) → Kˣ := fun i =>
  if i.val = 2 * pairs + 2 then s else 1

theorem heClassicOddC1_coefficients_mul_square
    (pairs : Nat) (c d s : Kˣ) (h : c = d * s ^ 2)
    (i : Fin (2 * pairs + 3)) :
    heClassicOddC1 (K := K) pairs c i =
      heClassicOddC1 (K := K) pairs d i *
        heClassicOddC1SquareScale pairs s i ^ 2 := by
  by_cases hlast : i.val = 2 * pairs + 2
  · have hi : i = Fin.last (2 * pairs + 2) := Fin.ext hlast
    rw [hi, heClassicOddC1_last, heClassicOddC1_last]
    simp [heClassicOddC1SquareScale, h]
  · have hhead : i.val < 2 * (pairs + 1) := by omega
    let j : Fin (2 * (pairs + 1)) := ⟨i.val, hhead⟩
    have hi : i = j.castSucc := Fin.ext rfl
    rw [hi, heClassicOddC1_head, heClassicOddC1_head]
    have hj : j.val ≠ 2 * pairs + 2 := by omega
    simp [heClassicOddC1SquareScale, hj]

/-- Square-equivalent unit parameters give isometric literal odd `C₁`
lattices.  This is the integral, rather than merely ambient, transport
needed to recover the paper's distinguished `C₁(omega)` test. -/
theorem heClassicOddC1Model_isIsometric_of_mul_square
    (pairs : Nat) (c d s : Kˣ)
    (hc : ordUnit K c = 0) (hd : ordUnit K d = 0)
    (hsUnit : IsValuationUnit K (s : K))
    (h : c = d * s ^ 2) :
    (heClassicOddC1Model (K := K) pairs c (by omega)).IsIntegrallyIsometric
      (heClassicOddC1Model (K := K) pairs d (by omega)) := by
  let source := heClassicOddC1 (K := K) pairs c
  let target := heClassicOddC1 (K := K) pairs d
  let scale := heClassicOddC1SquareScale pairs s
  have hsourceMono : ∀ i j, i ≤ j →
      ordUnit K (source i) ≤ ordUnit K (source j) := by
    intro i j _hij
    rw [show ordUnit K (source i) = 0 by
      simp only [source, heClassicOddC1_order, hc]
      split <;> rfl,
      show ordUnit K (source j) = 0 by
        simp only [source, heClassicOddC1_order, hc]
        split <;> rfl]
  have htargetMono : ∀ i j, i ≤ j →
      ordUnit K (target i) ≤ ordUnit K (target j) := by
    intro i j _hij
    rw [show ordUnit K (target i) = 0 by
      simp only [target, heClassicOddC1_order, hd]
      split <;> rfl,
      show ordUnit K (target j) = 0 by
        simp only [target, heClassicOddC1_order, hd]
        split <;> rfl]
  have hscaleUnit : ∀ i, IsValuationUnit K (scale i : K) := by
    intro i
    unfold scale heClassicOddC1SquareScale
    split
    · exact hsUnit
    · simp [IsValuationUnit]
  have hcoeff : ∀ i, source i = target i * scale i ^ 2 := by
    intro i
    exact heClassicOddC1_coefficients_mul_square pairs c d s h i
  unfold IsIntegrallyIsometric
  change Lattice.IsIsometric
    (BONG.coefficientDiagonalSpace source)
    (BONG.coefficientDiagonalSpace target)
    (heHuExactRealization source
      (heClassicOddC1_adjacentAdmissible pairs c (by omega))
      (heClassicOddC1_weakTwoStep pairs c (by omega))).lattice
    (heHuExactRealization target
      (heClassicOddC1_adjacentAdmissible pairs d (by omega))
      (heClassicOddC1_weakTwoStep pairs d (by omega))).lattice
  exact heHuExactModel_isIsometric_of_pointwise_unit_square
    source target scale
    (heClassicOddC1_adjacentAdmissible pairs c (by omega))
    (heClassicOddC1_weakTwoStep pairs c (by omega))
    (heClassicOddC1_adjacentAdmissible pairs d (by omega))
    (heClassicOddC1_weakTwoStep pairs d (by omega))
    hsourceMono htargetMono hscaleUnit hcoeff

/-- Match the two-column He--Hu odd table with the parity/column layout of
the literal classic table. -/
def classicOddIndexOfHeHu {I : Type u} :
    HeHuPublishedOddTestingIndex I -> HeClassicPublishedOddTestingIndex I
  | .inl p => (p, false)
  | .inr p => (p, true)

/-- The exact good-BONG lattice and the canonical maximal lattice have
isometric ambient spaces whenever their displayed diagonal rows do. -/
theorem exactModel_isAmbientlyIsometric_omaximalModel
    {n : Nat} (source target : Fin n -> Kˣ)
    (hadj : BONG.CoefficientAdjacentAdmissible source)
    (hweak : BONG.CoefficientWeakTwoStep (K := K) source)
    (hrep : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients source)
      (BONG.GoodBONG.diagonalUnitCoefficients target)) :
    (heHuExactModel source hadj hweak).IsAmbientlyIsometric
      (heHuOMaximalModel target) := by
  change (BONG.coefficientDiagonalSpace source).IsIsometric
    (BONG.coefficientDiagonalSpace target)
  have hspace :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      source target).2 hrep
  rcases hspace with ⟨f⟩
  exact ⟨f.toIsometryOfFinrankEq (by simp)⟩

/-- Convert a representation of a displayed finite diagonal space into
diagonal coordinates on an arbitrary target space. -/
theorem diagonalRepresents_of_represents_coefficientDiagonal
    {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {q : QuadraticSpace K V}
    {n : Nat} (a : Fin n -> Kˣ)
    (h : q.Represents (BONG.coefficientDiagonalSpace a)) :
    DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients a)
      (BONG.GoodBONG.diagonalUnitCoefficients q.diagonalUnits) := by
  have hdiag : q.diagonalModel.Represents
      (QuadraticSpace.finiteDiagonal
        (BONG.GoodBONG.diagonalUnitCoefficients a)
        (fun i => Units.ne_zero (a i))) := by
    change q.diagonalModel.Represents (BONG.coefficientDiagonalSpace a)
    exact ⟨q.diagonalizationIsometry.toRepresentation.trans
      (Classical.choice h)⟩
  exact (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
    a q.diagonalUnits).mp hdiag

/-- Express an ambient representation in the orthogonal coordinates of a
chosen good BONG.  This keeps the determinant calculation in the same BONG
coordinates used by Lemma 4.4. -/
theorem diagonalRepresents_goodBONG_of_represents_coefficientDiagonal
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    {m n : Nat} (a : BONG.GoodBONG q L n) (source : Fin m -> Kˣ)
    (h : q.Represents (BONG.coefficientDiagonalSpace source)) :
    DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients source)
      (BONG.GoodBONG.diagonalUnitCoefficients a.valueUnit) := by
  rcases h with ⟨f⟩
  let g : (Fin m -> K) →ₗ[K] (Fin n -> K) :=
    a.toBONG.basis.equivFun.toLinearMap.comp f.toLinearMap
  refine ⟨g, a.toBONG.basis.equivFun.injective.comp f.injective, ?_⟩
  intro x
  change diagonalQuadratic (fun i => (a.valueUnit i : K)) (g x) =
    diagonalQuadratic (fun i => (source i : K)) x
  change diagonalQuadratic a.toBONG.value (g x) =
    diagonalQuadratic (fun i => (source i : K)) x
  rw [a.toBONG.diagonalQuadratic_value_eq]
  simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  simpa only [BONG.coefficientDiagonalSpace,
    QuadraticSpace.finiteDiagonal_quadratic_apply] using f.map_quadratic x

/-! ## The published Lemma 7.1 obstruction

The publisher proof applies Lemma 3.14 with the wrong parity.  The next
calculation shows that this cannot be repaired by a harmless reindexing:
when the ramification index is greater than one, the terminal condition
of Theorem 2.5 already excludes the exceptional even lattice `H_e` from
every odd source whose last order is zero and whose preceding alpha is one.
-/

/-- At ramification index greater than one, the terminal defect condition
prevents a rank-`2p+3` source with terminal order zero and preceding alpha
one from representing the exceptional rank-`2p+2` lattice `H_e(1)`.

This is the exact numerical obstruction hidden by the parity mismatch in
the published proof of Lemma 7.1. -/
theorem zeroTerminalAlphaOne_not_represents_heClassicEvenH
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (pairs : Nat) (a : BONG.GoodBONG q L (2 * pairs + 3))
    (hLast : a.order ⟨2 * pairs + 2, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨2 * pairs + 1, by omega⟩ = 1)
    (heLarge : 1 < ramificationIndex K) :
    ¬ Lattice.Represents q
        (BONG.coefficientDiagonalSpace
          (heClassicEvenH (K := K) pairs 1))
        L
        (heHuExactRealization
          (heClassicEvenH (K := K) pairs 1)
          (heClassicEvenH_adjacentAdmissible pairs 1 (Or.inl rfl))
          (heClassicEvenH_weakTwoStep pairs 1 (by
            have h := ordUnit_mul K (1 : Kˣ) 1
            simp only [mul_one] at h
            omega))).lattice := by
  let oneOrder : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  let b := heClassicEvenHGoodBONG (K := K) pairs 1
    (Or.inl rfl) oneOrder
  let i : RepresentationIndex (2 * pairs + 3) (2 * pairs + 2) :=
    { val := 2 * pairs + 2
      pos := by omega
      lt_large := by omega
      le_small := by omega }
  have hTargetLast :
      b.order ⟨2 * pairs + 1, by omega⟩ =
        -(ramificationIndex K : Int) := by
    simp only [b, heClassicEvenHGoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenH_order pairs 1 oneOrder]
    simp only [Nat.not_even_two_mul_add_one, ↓reduceIte]
  have hHalf : (1 : WithTop ℚ) < a.representationHalfGap b i := by
    unfold BONG.GoodBONG.representationHalfGap
    dsimp only [i]
    have hTargetIndex :
        (⟨2 * pairs + 2 - 1, by omega⟩ : Fin (2 * pairs + 2)) =
          ⟨2 * pairs + 1, by omega⟩ := by
      apply Fin.ext
      dsimp
    rw [hLast, hTargetIndex, hTargetLast]
    have heQ : (1 : ℚ) < (ramificationIndex K : ℚ) := by
      exact_mod_cast heLarge
    norm_cast
    simp only [Rat.divInt_eq_div]
    push_cast
    linarith
  have hMixedNonnegative : (0 : WithTop ℚ) <=
      a.truncatedPrefixDefect b (-1) (2 * pairs + 3)
        (2 * pairs + 1) := by
    exact a.truncatedPrefixDefect_nonneg b (-1)
      (2 * pairs + 3) (2 * pairs + 1)
  have hPrimary :
      (1 : WithTop ℚ) < a.representationPrimaryDefect b i := by
    unfold BONG.GoodBONG.representationPrimaryDefect
    dsimp only [i]
    have hTargetIndex :
        (⟨2 * pairs + 2 - 1, by omega⟩ : Fin (2 * pairs + 2)) =
          ⟨2 * pairs + 1, by omega⟩ := by
      apply Fin.ext
      dsimp
    rw [hLast, hTargetIndex, hTargetLast]
    have hPlus : 2 * pairs + 2 + 1 = 2 * pairs + 3 := by omega
    have hMinus : 2 * pairs + 2 - 1 = 2 * pairs + 1 := by omega
    rw [hPlus, hMinus]
    have heTop : (1 : WithTop ℚ) <
        ((((ramificationIndex K : Int) : ℚ) : WithTop ℚ)) := by
      exact_mod_cast heLarge
    have hbase :
        ((((ramificationIndex K : Int) : ℚ) : WithTop ℚ)) <=
          ((((0 - -(ramificationIndex K : Int) : Int) : ℚ) : WithTop ℚ) +
            a.truncatedPrefixDefect b (-1) (2 * pairs + 3)
              (2 * pairs + 1)) := by
      simpa using (le_add_of_nonneg_right hMixedNonnegative)
    exact heTop.trans_le hbase
  have hRepresentationAlpha :
      (1 : WithTop ℚ) < a.representationAlpha b i := by
    rw [a.representationAlpha_eq_min_halfGap_prime b i,
      a.representationAlphaPrime_eq_primary_of_not_interior b i (by
        dsimp only [i]
        omega)]
    exact lt_min hHalf hPrimary
  have hComparisonCap :
      a.truncatedPrefixDefect b 1 i.val i.val <= (1 : WithTop ℚ) := by
    calc
      a.truncatedPrefixDefect b 1 i.val i.val <= a.prefixAlphaCap i.val :=
        a.truncatedPrefixDefect_le_leftCap b 1 i.val i.val
      _ = (1 : WithTop ℚ) := by
        rw [a.prefixAlphaCap_of_internal (by dsimp only [i]; omega)
          (by dsimp only [i]; omega)]
        have hIndex :
            (⟨i.val - 1, by dsimp only [i]; omega⟩ :
              Fin (2 * pairs + 2)) =
              ⟨2 * pairs + 1, by omega⟩ := Fin.ext rfl
        rw [hIndex, hAlpha]
        norm_num
  intro hrep
  have hConditions := a.representationConditionsPrime_of_represents
    b (by omega) hrep
  have hDefect := hConditions.defectCondition i
  rw [← a.coe_representationAlphaValue b i] at hRepresentationAlpha
  exact (not_lt_of_ge (hDefect.trans hComparisonCap)) hRepresentationAlpha

/-- Consequently, for `e>1` the literal first odd row `C₁(omega)` does
not represent `H_e(1)`. -/
theorem heClassicOddC1Omega_not_represents_evenH_of_ramification_gt_one
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    (pairs : Nat) (heLarge : 1 < ramificationIndex K) :
    ¬ (heClassicOddC1Model (K := K) pairs (heClassicOmega (K := K))
          (by rw [heClassicOmega_order (K := K)])).Represents
        (heClassicEvenHModel (K := K) pairs 1 (Or.inl rfl)
          (by
            have h := ordUnit_mul K (1 : Kˣ) 1
            simp only [mul_one] at h
            omega)) := by
  let c := heClassicOmega (K := K)
  let hc : 0 <= ordUnit K c := by
    rw [heClassicOmega_order (K := K)]
  let a := heClassicOddC1GoodBONG (K := K) pairs c hc
  have hLast : a.order ⟨2 * pairs + 2, by omega⟩ = 0 := by
    simp only [a, heClassicOddC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicOddC1_order, if_pos rfl,
      heClassicOmega_order (K := K)]
  have hAlpha : a.alphaValue ⟨2 * pairs + 1, by omega⟩ = 1 := by
    have hAll := heClassicOddC1_alpha_eq_one (K := K) pairs c 1 hc
      (Or.inr rfl)
      (by dsimp only [c]; rw [heClassicOmega_order (K := K)]; norm_num)
      (by dsimp only [c]; rw [heClassicOmega_defect (K := K)]; norm_num)
    exact hAll _
  exact zeroTerminalAlphaOne_not_represents_heClassicEvenH
    pairs a hLast hAlpha heLarge

/-- The literal second odd row `C₂(omega)`, with the formula-defined
`omega#`, has the same terminal obstruction to representing `H_e(1)`. -/
theorem heClassicOddC2Omega_not_represents_evenH_of_ramification_gt_one
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    (pairs : Nat) (heLarge : 1 < ramificationIndex K) :
    ¬ (heClassicOddC2EvenModel (K := K) pairs
          (heClassicOmega (K := K)) (heClassicOmega (K := K))
          (heClassicOmegaSharp (K := K))
          (heClassicOmega_order (K := K))
          (heClassicOmega_order (K := K))
          (heClassicOmegaSharp_order (K := K))).Represents
        (heClassicEvenHModel (K := K) pairs 1 (Or.inl rfl)
          (by
            have h := ordUnit_mul K (1 : Kˣ) 1
            simp only [mul_one] at h
            omega)) := by
  let c := heClassicOmega (K := K)
  let omegaUnit := heClassicOmega (K := K)
  let omegaSharp := heClassicOmegaSharp (K := K)
  let hc : ordUnit K c = 0 := heClassicOmega_order (K := K)
  let homega : ordUnit K omegaUnit = 0 := heClassicOmega_order (K := K)
  let homegaSharp : ordUnit K omegaSharp = 0 :=
    heClassicOmegaSharp_order (K := K)
  let a := heClassicOddC2EvenGoodBONG (K := K) pairs c omegaUnit
    omegaSharp hc homega homegaSharp
  have hLast : a.order ⟨2 * pairs + 2, by omega⟩ = 0 := by
    simp only [a, heClassicOddC2EvenGoodBONG, heHuExactGoodBONG_order]
    exact heClassicOddC2Even_order_zero pairs c omegaUnit omegaSharp hc
      homega homegaSharp _
  have hAlpha : a.alphaValue ⟨2 * pairs + 1, by omega⟩ = 1 := by
    have hAll := heClassicOddC2Even_alpha_eq_one (K := K) pairs c
      omegaUnit omegaSharp hc homega homegaSharp (by
        dsimp only [omegaUnit]
        exact heClassicOmega_defect (K := K))
    exact hAll _
  exact zeroTerminalAlphaOne_not_represents_heClassicEvenH
    pairs a hLast hAlpha heLarge

/-- Formal counterexample certificate for the literal conclusion of the
published Lemma 7.1(ii): for `e>1`, neither displayed odd test lattice with
parameter `omega` represents the classic integral lattice `H_e(1)`. -/
theorem he2022ClassicLemma71ii_literal_disjunction_fails
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    (pairs : Nat) (heLarge : 1 < ramificationIndex K) :
    ¬ ((heClassicOddC1Model (K := K) pairs (heClassicOmega (K := K))
            (by rw [heClassicOmega_order (K := K)])).Represents
          (heClassicEvenHModel (K := K) pairs 1 (Or.inl rfl)
            (by
              have h := ordUnit_mul K (1 : Kˣ) 1
              simp only [mul_one] at h
              omega)) ∨
        (heClassicOddC2EvenModel (K := K) pairs
            (heClassicOmega (K := K)) (heClassicOmega (K := K))
            (heClassicOmegaSharp (K := K))
            (heClassicOmega_order (K := K))
            (heClassicOmega_order (K := K))
            (heClassicOmegaSharp_order (K := K))).Represents
          (heClassicEvenHModel (K := K) pairs 1 (Or.inl rfl)
            (by
              have h := ordUnit_mul K (1 : Kˣ) 1
              simp only [mul_one] at h
              omega))) := by
  rintro (h | h)
  · exact heClassicOddC1Omega_not_represents_evenH_of_ramification_gt_one
      pairs heLarge h
  · exact heClassicOddC2Omega_not_represents_evenH_of_ramification_gt_one
      pairs heLarge h

/-- For an odd-order determinant parameter, the literal discriminant-unit
second column is the other member of the common determinant square class. -/
theorem heClassicEvenC_oddOrder_literalPairProperties
    [HilbertSymbolLaws K] [DyadicDiscriminantClassLaws K]
    (pairs : Nat) (c : Kˣ) (hodd : Odd (ordUnit K c)) :
    HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) pairs c)
      (heClassicEvenC2 (K := K) pairs c
        (Dyadic.dyadicDiscriminantClassLawsProved
          (K := K)).discriminantUnit) := by
  let delta :=
    (Dyadic.dyadicDiscriminantClassLawsProved
      (K := K)).discriminantUnit
  have hnegative : hilbertSymbol K delta c = -1 := by
    simpa only [delta] using
      (hilbertSymbol_discriminant_eq_neg_one_of_odd_order c hodd)
  have hclassification :=
    heHuBinaryTwist_classification c delta hnegative
  have hbinary : HeHuSpacePairProperties
      (heHuBinaryFirst c) (heHuBinaryTwist c delta) := by
    apply HeHuSpacePairProperties.of_det_not
    · exact hclassification.1
    · exact hclassification.2.1
  have hpair := hbinary.append
    (AlternatingEndpointTower.standardHyperbolicEndpointTower
      (K := K) pairs)
  simpa only [delta, heClassicEvenC1, heClassicEvenC2,
    heClassicScaledHyperbolicTower_zero, heHuBinaryFirst,
    heHuBinaryTwist] using hpair

/-- The determinant calculation at the heart of the even branch of Lemma
7.3.  If the signed determinant of a rank-`n+2` good BONG is square
equivalent to the parameter of a published `C₁/C₂` pair, that pair
cannot both be represented by the ambient source space. -/
theorem heClassicEvenPair_not_both_goodBONG_of_signedPrefix_factor
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (pairs : Nat) (a : BONG.GoodBONG q L (2 * pairs + 4))
    (c s : Kˣ) (second : Fin (2 * pairs + 2) -> Kˣ)
    (pair : HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) pairs c) second)
    (hcNonnegative : 0 <= ordUnit K c)
    (hfactor : ((-1 : Kˣ) ^ (pairs + 2)) *
      a.prefixProduct (2 * pairs + 4) = c * s ^ 2)
    (hfirst : q.Represents
      (BONG.coefficientDiagonalSpace
        (heClassicEvenC1 (K := K) pairs c)))
    (hsecond : q.Represents (BONG.coefficientDiagonalSpace second)) : False := by
  have hFirstDiagonal :=
    diagonalRepresents_goodBONG_of_represents_coefficientDiagonal
      a (heClassicEvenC1 (K := K) pairs c) hfirst
  have hSecondDiagonal :=
    diagonalRepresents_goodBONG_of_represents_coefficientDiagonal
      a second hsecond
  let bFirst := heClassicEvenC1GoodBONG (K := K) pairs c hcNonnegative
  have hFirstDet :
      BONG.GoodBONG.diagonalUnitDeterminant
          (heClassicEvenC1 (K := K) pairs c) =
        (-1 : Kˣ) ^ (pairs + 1) * c := by
    calc
      BONG.GoodBONG.diagonalUnitDeterminant
          (heClassicEvenC1 (K := K) pairs c) =
          BONG.GoodBONG.diagonalUnitDeterminant
            (bFirst.prefixValueUnits (2 * pairs + 2) le_rfl) := by
        rw [BONG.GoodBONG.heClassicEvenC1_fullPrefixValueUnits
          pairs c hcNonnegative]
      _ = bFirst.prefixProduct (2 * pairs + 2) :=
        bFirst.diagonalUnitDeterminant_prefixValueUnits
          (2 * pairs + 2) le_rfl
      _ = (-1 : Kˣ) ^ (pairs + 1) * c :=
        BONG.GoodBONG.heClassicEvenC1_prefixProduct_full
          (K := K) pairs c hcNonnegative
  have hTargetDet :
      BONG.GoodBONG.diagonalUnitDeterminant a.valueUnit =
        a.prefixProduct (2 * pairs + 4) := by
    have hvalues : a.prefixValueUnits (2 * pairs + 4) le_rfl =
        a.valueUnit := by
      funext i
      rfl
    rw [← hvalues]
    exact a.diagonalUnitDeterminant_prefixValueUnits
      (2 * pairs + 4) le_rfl
  have hSquare : IsSquare
      (((( (-1 : Kˣ) ^ (pairs + 2)) *
          a.prefixProduct (2 * pairs + 4)) * c)) := by
    refine ⟨c * s, ?_⟩
    rw [hfactor]
    simp only [pow_two]
    ac_rfl
  have hdet : IsSquare
      (-BONG.GoodBONG.diagonalUnitDeterminant a.valueUnit *
        BONG.GoodBONG.diagonalUnitDeterminant
          (heClassicEvenC1 (K := K) pairs c)) := by
    rw [hTargetDet, hFirstDet]
    have hsign :
        -a.prefixProduct (2 * pairs + 4) *
            ((-1 : Kˣ) ^ (pairs + 1) * c) =
          (((-1 : Kˣ) ^ (pairs + 2)) *
            a.prefixProduct (2 * pairs + 4)) * c := by
      have hneg : -a.prefixProduct (2 * pairs + 4) =
          (-1 : Kˣ) * a.prefixProduct (2 * pairs + 4) := by
        simp
      rw [hneg,
        show (-1 : Kˣ) ^ (pairs + 2) =
          (-1 : Kˣ) ^ (pairs + 1) * (-1 : Kˣ) by
            rw [show pairs + 2 = (pairs + 1) + 1 by omega, pow_succ]]
      ac_rfl
    rw [hsign]
    exact hSquare
  have hExactlyOne := heHu2022Lemma313CodimensionTwo
    (heClassicEvenC1 (K := K) pairs c) second pair a.valueUnit (by
      simpa only [show (2 * pairs + 2) + 2 = 2 * pairs + 4 by omega]
        using hdet)
  rcases hExactlyOne with hFirst | hSecond
  · exact hFirst.2 hSecondDiagonal
  · exact hSecond.1 hFirstDiagonal

/-- In equal dimension, one space cannot represent both members of a
nonisometric determinant-class pair. -/
theorem pair_not_both_represents_of_rank_eq
    {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {q : QuadraticSpace K V}
    {n : Nat} (first second : Fin n -> Kˣ)
    (pair : HeHuSpacePairProperties first second)
    (hrank : Module.finrank K V = n)
    (hfirst : q.Represents (BONG.coefficientDiagonalSpace first))
    (hsecond : q.Represents (BONG.coefficientDiagonalSpace second)) : False := by
  let e : Fin n ≃ Fin (Module.finrank K V) := finCongr hrank.symm
  let target : Fin n -> Kˣ := fun i => q.diagonalUnits (e i)
  have hqToTarget : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients q.diagonalUnits)
      (BONG.GoodBONG.diagonalUnitCoefficients target) := by
    have h := BONG.GoodBONG.DiagonalRepresents.reindexEquiv
      (BONG.GoodBONG.diagonalUnitCoefficients target) e.symm
    have hsource :
        (BONG.GoodBONG.diagonalUnitCoefficients target ∘ e.symm) =
          BONG.GoodBONG.diagonalUnitCoefficients q.diagonalUnits := by
      funext i
      simp only [Function.comp_apply, target,
        BONG.GoodBONG.diagonalUnitCoefficients, Equiv.apply_symm_apply]
    rw [hsource] at h
    exact h
  have hf :=
    (diagonalRepresents_of_represents_coefficientDiagonal first hfirst).trans
      hqToTarget
  have hs :=
    (diagonalRepresents_of_represents_coefficientDiagonal second hsecond).trans
      hqToTarget
  exact pair.nonisometric (hs.trans hf.symm_of_sameRank)

/-- Lemma 3.13 supplies the same exclusion in codimension one. -/
theorem pair_not_both_represents_of_rank_eq_add_one
    {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {q : QuadraticSpace K V}
    {n : Nat} (first second : Fin n -> Kˣ)
    (pair : HeHuSpacePairProperties first second)
    (hrank : Module.finrank K V = n + 1)
    (hfirst : q.Represents (BONG.coefficientDiagonalSpace first))
    (hsecond : q.Represents (BONG.coefficientDiagonalSpace second)) : False := by
  let e : Fin (n + 1) ≃ Fin (Module.finrank K V) := finCongr hrank.symm
  let target : Fin (n + 1) -> Kˣ := fun i => q.diagonalUnits (e i)
  have hqToTarget : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients q.diagonalUnits)
      (BONG.GoodBONG.diagonalUnitCoefficients target) := by
    have h := BONG.GoodBONG.DiagonalRepresents.reindexEquiv
      (BONG.GoodBONG.diagonalUnitCoefficients target) e.symm
    have hsource :
        (BONG.GoodBONG.diagonalUnitCoefficients target ∘ e.symm) =
          BONG.GoodBONG.diagonalUnitCoefficients q.diagonalUnits := by
      funext i
      simp only [Function.comp_apply, target,
        BONG.GoodBONG.diagonalUnitCoefficients, Equiv.apply_symm_apply]
    rw [hsource] at h
    exact h
  have hf :=
    (diagonalRepresents_of_represents_coefficientDiagonal first hfirst).trans
      hqToTarget
  have hs :=
    (diagonalRepresents_of_represents_coefficientDiagonal second hsecond).trans
      hqToTarget
  rcases heHu2022Lemma313CodimensionOne first second pair target with
    hexact | hexact
  · exact hexact.2 hs
  · exact hexact.1 hf

/-- Every odd He--Hu row has the same ambient quadratic space as the
corresponding literal classic row.  This is the space-level bridge used in
Lemma 7.3; it does not identify their generally different lattices. -/
theorem classicOddModel_isAmbientlyIsometric_heHuModel
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) (pairs : Nat)
    (j : HeHuPublishedOddTestingIndex I) :
    IsAmbientlyIsometric
      (HeClassicPublishedOddTestingIndex.model
        (K := K) U hU omegaData pairs (classicOddIndexOfHeHu j))
      (HeHuPublishedOddTestingIndex.model
        (K := K) (U := U) (pairs := pairs) j) := by
  have homega : omegaData.omega = heClassicOmega (K := K) :=
    omegaData.omega_eq
  have homegaSharp : omegaData.omegaSharp =
      heClassicOmegaSharp (K := K) := omegaData.omegaSharp_eq
  rcases j with p | p
  · rcases p with ⟨i, parity⟩
    cases parity
    · have hdiag : DiagonalRepresents
          (BONG.GoodBONG.diagonalUnitCoefficients
            (heClassicOddC1 (K := K) pairs (U i)))
          (BONG.GoodBONG.diagonalUnitCoefficients
            (heHuOddFirst pairs (U i))) := by
        rw [heClassicOddC1_eq_heHuOddFirst]
        exact diagonalRepresents_refl _
      simpa only [classicOddIndexOfHeHu,
        HeClassicPublishedOddTestingIndex.model,
        HeHuPublishedOddTestingIndex.model,
        HeHuPublishedOddTestingIndex.toGeneral,
        HeHuOddTestingIndex.model, HeHuOddTestingIndex.coefficients,
        HeHuPublishedSquareClassIndex.parameter_unit,
        heClassicOddC1Model] using
          (exactModel_isAmbientlyIsometric_omaximalModel
            (K := K)
            (heClassicOddC1 (K := K) pairs (U i))
            (heHuOddFirst pairs (U i))
            (heClassicOddC1_adjacentAdmissible pairs (U i) (by
              exact (isValuationUnit_iff_ordUnit_eq_zero K _).1
                (hU.isUnit i) ▸ le_rfl))
            (heClassicOddC1_weakTwoStep pairs (U i) (by
              exact (isValuationUnit_iff_ordUnit_eq_zero K _).1
                (hU.isUnit i) ▸ le_rfl)) hdiag)
    · let c := U i * uniformizerPowerUnit K (1 : Int)
      have hc : ordUnit K c = 1 := by
        rw [ordUnit_mul,
          (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i),
          ordUnit_uniformizerPowerUnit]
        norm_num
      have hdiag : DiagonalRepresents
          (BONG.GoodBONG.diagonalUnitCoefficients
            (heClassicOddC1 (K := K) pairs c))
          (BONG.GoodBONG.diagonalUnitCoefficients
            (heHuOddFirst pairs c)) := by
        rw [heClassicOddC1_eq_heHuOddFirst]
        exact diagonalRepresents_refl _
      simpa only [classicOddIndexOfHeHu,
        HeClassicPublishedOddTestingIndex.model,
        HeHuPublishedOddTestingIndex.model,
        HeHuPublishedOddTestingIndex.toGeneral,
        HeHuOddTestingIndex.model, HeHuOddTestingIndex.coefficients,
        HeHuPublishedSquareClassIndex.parameter_uniformizer,
        heClassicOddC1Model, c] using
          (exactModel_isAmbientlyIsometric_omaximalModel
            (K := K) (heClassicOddC1 (K := K) pairs c)
            (heHuOddFirst pairs c)
            (heClassicOddC1_adjacentAdmissible pairs c (by omega))
            (heClassicOddC1_weakTwoStep pairs c (by omega)) hdiag)
  · rcases p with ⟨i, parity⟩
    cases parity
    · have hnegative : hilbertSymbol K omegaData.omegaSharp
          omegaData.omega = -1 := by
        rw [homega, homegaSharp]
        exact BONG.GoodBONG.heClassicOmegaSharp_hilbert_neg (K := K)
      have hfirst : DiagonalRepresents
          (BONG.GoodBONG.diagonalUnitCoefficients
            (heClassicOddC1 (K := K) pairs (U i)))
          (BONG.GoodBONG.diagonalUnitCoefficients
            (heHuOddFirst pairs (U i))) := by
        rw [heClassicOddC1_eq_heHuOddFirst]
        exact diagonalRepresents_refl _
      have hdiag := HeHuSpacePairProperties.second_represents_second
        (heClassicOddC_evenOrder_pairProperties (K := K) pairs (U i)
          omegaData.omega omegaData.omegaSharp hnegative)
        (heHu2022Definition34Proposition35Odd pairs (U i)) hfirst
      have hc : ordUnit K (U i) = 0 :=
        (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i)
      simpa only [classicOddIndexOfHeHu,
        HeClassicPublishedOddTestingIndex.model,
        HeHuPublishedOddTestingIndex.model,
        HeHuPublishedOddTestingIndex.toGeneral,
        HeHuOddTestingIndex.model, HeHuOddTestingIndex.coefficients,
        HeHuPublishedSquareClassIndex.parameter_unit,
        heClassicOddC2EvenModel] using
          (exactModel_isAmbientlyIsometric_omaximalModel
            (K := K)
            (heClassicOddC2Even (K := K) pairs (U i)
              omegaData.omega omegaData.omegaSharp)
            (heHuOddSecond pairs (U i))
            (heClassicOddC2Even_adjacentAdmissible pairs (U i)
              omegaData.omega omegaData.omegaSharp hc
              omegaData.omega_order omegaData.omegaSharp_order)
            (heClassicOddC2Even_weakTwoStep pairs (U i)
              omegaData.omega omegaData.omegaSharp hc
              omegaData.omega_order omegaData.omegaSharp_order) hdiag)
    · let c := U i * uniformizerPowerUnit K (1 : Int)
      have hc : ordUnit K c = 1 := by
        rw [ordUnit_mul,
          (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i),
          ordUnit_uniformizerPowerUnit]
        norm_num
      have hodd : Odd (ordUnit K c) := by rw [hc]; exact odd_one
      have hdiag : DiagonalRepresents
          (BONG.GoodBONG.diagonalUnitCoefficients
            (heClassicOddC2Odd (K := K) pairs c))
          (BONG.GoodBONG.diagonalUnitCoefficients
            (heHuOddSecond pairs c)) := by
        rw [heClassicOddC2Odd_eq_heHuOddSecond_of_odd pairs c hodd]
        exact diagonalRepresents_refl _
      simpa only [classicOddIndexOfHeHu,
        HeClassicPublishedOddTestingIndex.model,
        HeHuPublishedOddTestingIndex.model,
        HeHuPublishedOddTestingIndex.toGeneral,
        HeHuOddTestingIndex.model, HeHuOddTestingIndex.coefficients,
        HeHuPublishedSquareClassIndex.parameter_uniformizer,
        heClassicOddC2OddModel, c] using
          (exactModel_isAmbientlyIsometric_omaximalModel
            (K := K) (heClassicOddC2Odd (K := K) pairs c)
            (heHuOddSecond pairs c)
            (heClassicOddC2Odd_adjacentAdmissible pairs c (by omega))
            (heClassicOddC2Odd_weakTwoStep pairs c (by omega)) hdiag)

/-- Classic `n`-universality of a bundled local quadratic lattice. -/
def IsClassicNUniversal (X : QuadraticLatticeModel (K := K))
    (n : Nat) : Prop := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : Module.Finite K X.Carrier := X.lattice.moduleFinite
  exact Lattice.IsClassicNUniversal.{u, u, u} X.form X.lattice n

/-- Ambient rank-`n` universality of a bundled local quadratic lattice. -/
def IsAmbientlyNUniversal (X : QuadraticLatticeModel (K := K))
    (n : Nat) : Prop := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  exact Lattice.AmbientlyNUniversal.{u, u, u} X.form n

/-- The finite even table contains the literal exceptional row
`H_e^(2p+2)(1)`. -/
theorem represents_literalEvenHOne_of_all
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hAll : forall i : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model
          (K := K) U hU pairs i)) :
    X.Represents
      (heClassicEvenHModel (K := K) pairs 1 (Or.inl rfl)
        (by
          have h := ordUnit_mul K (1 : Kˣ) 1
          simp only [mul_one] at h
          omega)) := by
  let i : HeClassicPublishedEvenTestingIndex
      (K := K) U (ramificationIndex K) :=
    .inl ⟨false, Or.inl rfl⟩
  simpa [i, HeClassicPublishedEvenTestingIndex.model,
    HeClassicExceptionalIndex.parameter] using hAll i

/-- When `e=1`, the finite even table also contains the literal
`H_1^(2p+2)(Delta)` row. -/
theorem represents_literalEvenHDelta_of_all
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (heOne : ramificationIndex K = 1)
    (hAll : forall i : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model
          (K := K) U hU pairs i)) :
    let delta :=
      (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminantUnit
    let deltaOrder : ordUnit K delta = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K delta).1
        (Dyadic.dyadicDiscriminantClassLawsProved
          (K := K)).discriminant_isValuationUnit
    X.Represents
      (heClassicEvenHModel (K := K) pairs delta
        (Or.inr (show delta =
          (Dyadic.dyadicDiscriminantClassLawsProved
            (K := K)).discriminantUnit
          from rfl))
        deltaOrder) := by
  let delta :=
    (Dyadic.dyadicDiscriminantClassLawsProved
      (K := K)).discriminantUnit
  let deltaOrder : ordUnit K delta = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K delta).1
      (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminant_isValuationUnit
  let i : HeClassicPublishedEvenTestingIndex
      (K := K) U (ramificationIndex K) :=
    .inl ⟨true, Or.inr heOne⟩
  simpa [i, delta, deltaOrder,
    HeClassicPublishedEvenTestingIndex.model,
    HeClassicExceptionalIndex.parameter] using hAll i

/-- Completeness of the unit square-class representatives and the integral
unit-square transport above recover the literal `C₁(omega)` row from the
finite even table. -/
theorem represents_literalEvenC1Omega_of_all
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hAll : forall i : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model
          (K := K) U hU pairs i)) :
    X.Represents
      (heClassicEvenC1Model (K := K) pairs
        (heClassicOmega (K := K)) (by
          rw [heClassicOmega_order (K := K)])) := by
  have homegaUnit : IsValuationUnit K ((heClassicOmega (K := K) : K)) :=
    (isValuationUnit_iff_ordUnit_eq_zero K _).2
      (heClassicOmega_order (K := K))
  obtain ⟨i, s, hsUnit, hfactor⟩ :=
    hU.complete (heClassicOmega (K := K)) homegaUnit
  have hdefect : BONG.GoodBONG.defectOrder (K := K) (U i) =
      (1 : WithTop ℚ) := by
    have h := heClassicOmega_defect (K := K)
    rw [hfactor, BONG.GoodBONG.defectOrder_mul_square] at h
    exact h
  let di : HeClassicDefectOneIndex (K := K) U := ⟨i, hdefect⟩
  let idx : HeClassicPublishedEvenTestingIndex
      (K := K) U (ramificationIndex K) := .inr (.inl (di, false))
  let C := heClassicEvenC1Model (K := K) pairs
    (heClassicOmega (K := K)) (by
      rw [heClassicOmega_order (K := K)])
  let D := heClassicEvenC1Model (K := K) pairs (U i) (by
    exact (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i) ▸ le_rfl)
  have hXD : X.Represents D := by
    simpa [D, idx, di, HeClassicPublishedEvenTestingIndex.model] using hAll idx
  have hCD : C.IsIntegrallyIsometric D := by
    simpa [C, D] using
      (heClassicEvenC1Model_isIsometric_of_mul_square
        (K := K) pairs (heClassicOmega (K := K)) (U i) s
        (heClassicOmega_order (K := K))
        ((isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i))
        hsUnit hfactor)
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup C.Carrier := C.addCommGroup
  letI : Module K C.Carrier := C.module
  letI : AddCommGroup D.Carrier := D.addCommGroup
  letI : Module K D.Carrier := D.module
  change Lattice.Represents X.form C.form X.lattice C.lattice
  change Lattice.Represents X.form D.form X.lattice D.lattice at hXD
  change Lattice.IsIsometric C.form D.form C.lattice D.lattice at hCD
  rcases hXD with ⟨f⟩
  rcases hCD with ⟨g⟩
  exact ⟨f.trans g.toRepresentation⟩

/-- Completeness of the unit square-class representatives also recovers
the literal odd-rank `C₁(omega)` row. -/
theorem represents_literalOddC1Omega_of_all
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K))
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hAll : forall i : HeClassicPublishedOddTestingIndex I,
      X.Represents
        (HeClassicPublishedOddTestingIndex.model
          (K := K) U hU omegaData pairs i)) :
    X.Represents
      (heClassicOddC1Model (K := K) pairs
        (heClassicOmega (K := K)) (by
          rw [heClassicOmega_order (K := K)])) := by
  have homegaUnit : IsValuationUnit K ((heClassicOmega (K := K) : K)) :=
    (isValuationUnit_iff_ordUnit_eq_zero K _).2
      (heClassicOmega_order (K := K))
  obtain ⟨i, s, hsUnit, hfactor⟩ :=
    hU.complete (heClassicOmega (K := K)) homegaUnit
  let idx : HeClassicPublishedOddTestingIndex I := ((i, false), false)
  let C := heClassicOddC1Model (K := K) pairs
    (heClassicOmega (K := K)) (by
      rw [heClassicOmega_order (K := K)])
  let D := heClassicOddC1Model (K := K) pairs (U i) (by
    exact (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i) ▸ le_rfl)
  have hXD : X.Represents D := by
    simpa [D, idx, HeClassicPublishedOddTestingIndex.model] using hAll idx
  have hCD : C.IsIntegrallyIsometric D := by
    simpa [C, D] using
      (heClassicOddC1Model_isIsometric_of_mul_square
        (K := K) pairs (heClassicOmega (K := K)) (U i) s
        (heClassicOmega_order (K := K))
        ((isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i))
        hsUnit hfactor)
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup C.Carrier := C.addCommGroup
  letI : Module K C.Carrier := C.module
  letI : AddCommGroup D.Carrier := D.addCommGroup
  letI : Module K D.Carrier := D.module
  change Lattice.Represents X.form C.form X.lattice C.lattice
  change Lattice.Represents X.form D.form X.lattice D.lattice at hXD
  change Lattice.IsIsometric C.form D.form C.lattice D.lattice at hCD
  rcases hXD with ⟨f⟩
  rcases hCD with ⟨g⟩
  exact ⟨f.trans g.toRepresentation⟩

/-- The represented literal odd `C₁(omega)` row supplies the exact
condition-level premise of Lemma 5.4. -/
theorem literalLemma54Test_of_all_publishedOdd
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K))
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    {m : Nat}
    (a : @BONG.GoodBONG K _ _ _ _ _ X.Carrier X.addCommGroup X.module
      X.form X.lattice (m + 5))
    (hSource : 2 * pairs + 5 <= m + 5)
    (hAll : forall i : HeClassicPublishedOddTestingIndex I,
      X.Represents
        (HeClassicPublishedOddTestingIndex.model
          (K := K) U hU omegaData pairs i)) :
    (by
      letI : AddCommGroup X.Carrier := X.addCommGroup (K := K)
      letI : Module K X.Carrier := X.module (K := K)
      exact a.HeClassicLemma54PublishedTest pairs (by omega)) := by
  let C := heClassicOddC1Model (K := K) pairs
    (heClassicOmega (K := K)) (by
      rw [heClassicOmega_order (K := K)])
  have hXC : X.Represents C := by
    simpa only [C] using
      represents_literalOddC1Omega_of_all U hU omegaData pairs X hAll
  letI : AddCommGroup X.Carrier := X.addCommGroup (K := K)
  letI : Module K X.Carrier := X.module (K := K)
  letI : AddCommGroup C.Carrier := C.addCommGroup
  letI : Module K C.Carrier := C.module
  let b := heClassicOddC1GoodBONG (K := K) pairs
    (heClassicOmega (K := K)) (by
      rw [heClassicOmega_order (K := K)])
  have hrep : Lattice.Represents X.form C.form X.lattice C.lattice := hXC
  have hconditions := a.representationConditionsPrime_of_represents
    b (by omega) hrep
  unfold BONG.GoodBONG.HeClassicLemma54PublishedTest
  dsimp only
  exact ⟨hconditions.orderCondition, hconditions.defectCondition⟩

/-- Actual representation of the finite even table supplies the two literal
condition-level tests used in Lemma 4.2. -/
theorem literalLemma42Tests_of_all
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    {m : Nat}
    (a : @BONG.GoodBONG K _ _ _ _ _ X.Carrier X.addCommGroup X.module
      X.form X.lattice (m + 3))
    (hSource : 2 * pairs + 4 <= m + 3)
    (hAll : forall i : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model
          (K := K) U hU pairs i)) :
    (by
      letI : AddCommGroup X.Carrier := X.addCommGroup (K := K)
      letI : Module K X.Carrier := X.module (K := K)
      exact a.HeClassicLemma42PublishedTests pairs (by omega)) := by
  let oneOrder : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  let omega := heClassicOmega (K := K)
  let omegaOrder : ordUnit K omega = 0 := heClassicOmega_order (K := K)
  let C := heClassicEvenC1Model (K := K) pairs omega (by omega)
  let H := heClassicEvenHModel (K := K) pairs 1 (Or.inl rfl) oneOrder
  have hXC : X.Represents C := by
    simpa only [C, omega, omegaOrder] using
      represents_literalEvenC1Omega_of_all U hU pairs X hAll
  have hXH : X.Represents H := by
    simpa only [H, oneOrder] using
      represents_literalEvenHOne_of_all U hU pairs X hAll
  letI : AddCommGroup X.Carrier := X.addCommGroup (K := K)
  letI : Module K X.Carrier := X.module (K := K)
  letI : AddCommGroup C.Carrier := C.addCommGroup
  letI : Module K C.Carrier := C.module
  letI : AddCommGroup H.Carrier := H.addCommGroup
  letI : Module K H.Carrier := H.module
  let bC := heClassicEvenC1GoodBONG (K := K) pairs omega (by omega)
  let bH := heClassicEvenHGoodBONG (K := K) pairs 1 (Or.inl rfl) oneOrder
  have hrepC : Lattice.Represents X.form C.form X.lattice C.lattice := by
    exact hXC
  have hrepH : Lattice.Represents X.form H.form X.lattice H.lattice := by
    exact hXH
  have hconditionsC := a.representationConditionsPrime_of_represents
    bC (by omega) hrepC
  have hconditionsH := a.representationConditionsPrime_of_represents
    bH (by omega) hrepH
  unfold BONG.GoodBONG.HeClassicLemma42PublishedTests
  dsimp only
  exact ⟨⟨hconditionsC.orderCondition, hconditionsC.defectCondition⟩,
    ⟨hconditionsH.orderCondition, hconditionsH.defectCondition⟩⟩

/-- The codimension-one exclusion in Lemma 4.3(ii) depends only on the
two displayed rows forming the two ambient isometry classes with their
common determinant square class.  This parameterized version permits the
square-class representative actually occurring in the finite table. -/
theorem heClassicEvenC_notBothRepresents_of_pair
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    {m : Nat} (pairs : Nat) (a : BONG.GoodBONG q L (m + 3))
    (hExtra : 2 * pairs + 5 <= m + 3)
    (c cSharp : Kˣ) (hc : ordUnit K c = 0)
    (hcSharp : ordUnit K cSharp = 0)
    (pair : HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) pairs c)
      (heClassicEvenC2 (K := K) pairs c cSharp)) :
    let bC1 := heClassicEvenC1GoodBONG (K := K) pairs c (by omega)
    let bC2 := heClassicEvenC2GoodBONG (K := K) pairs c cSharp
      (by omega) hcSharp
    let i := BONG.GoodBONG.he2022ClassicLemma43Index
      (m := m) pairs (by omega)
    ¬ (DiagonalRepresents
        (bC1.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega))
        (a.prefixValues i.val (by
          have := i.lt_large
          omega)) ∧
      DiagonalRepresents
        (bC2.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega))
        (a.prefixValues i.val (by
          have := i.lt_large
          omega))) := by
  dsimp only
  let hnonnegative : 0 <= ordUnit K c := by omega
  let bC1 := heClassicEvenC1GoodBONG (K := K) pairs c hnonnegative
  let bC2 := heClassicEvenC2GoodBONG (K := K) pairs c cSharp
    hnonnegative hcSharp
  let i := BONG.GoodBONG.he2022ClassicLemma43Index pairs (by omega :
    2 * pairs + 4 <= m + 3)
  rintro ⟨hC1, hC2⟩
  let hs : i.val - 1 = 2 * pairs + 2 := by
    dsimp only [i, BONG.GoodBONG.he2022ClassicLemma43Index]
    omega
  let ht : i.val = 2 * pairs + 3 := by rfl
  have hC1Cast := BONG.GoodBONG.heHuLemma43_diagonalRepresents_castLengths
    hs ht hC1
  have hC2Cast := BONG.GoodBONG.heHuLemma43_diagonalRepresents_castLengths
    hs ht hC2
  have hC1TargetEq :
      (fun j : Fin (2 * pairs + 2) =>
        bC1.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega) (Fin.cast hs.symm j)) =
        bC1.prefixValues (2 * pairs + 2) le_rfl := by
    funext j
    unfold BONG.GoodBONG.prefixValues
    congr 1
  have hC2TargetEq :
      (fun j : Fin (2 * pairs + 2) =>
        bC2.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega) (Fin.cast hs.symm j)) =
        bC2.prefixValues (2 * pairs + 2) le_rfl := by
    funext j
    unfold BONG.GoodBONG.prefixValues
    congr 1
  have hsourceEq :
      (fun j : Fin (2 * pairs + 3) =>
        a.prefixValues i.val (by
          have := i.lt_large
          omega) (Fin.cast ht.symm j)) =
        a.prefixValues (2 * pairs + 3) (by omega) := by
    funext j
    unfold BONG.GoodBONG.prefixValues
    congr 1
  have hC1' : DiagonalRepresents
      (bC1.prefixValues (2 * pairs + 2) le_rfl)
      (a.prefixValues (2 * pairs + 3) (by omega)) := by
    rw [hC1TargetEq, hsourceEq] at hC1Cast
    exact hC1Cast
  have hC2' : DiagonalRepresents
      (bC2.prefixValues (2 * pairs + 2) le_rfl)
      (a.prefixValues (2 * pairs + 3) (by omega)) := by
    rw [hC2TargetEq, hsourceEq] at hC2Cast
    exact hC2Cast
  let source := a.prefixValueUnits (2 * pairs + 3) (by omega)
  have hC1Units : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients
        (heClassicEvenC1 (K := K) pairs c))
      (BONG.GoodBONG.diagonalUnitCoefficients source) := by
    change DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients
        (bC1.prefixValueUnits (2 * pairs + 2) le_rfl))
      (BONG.GoodBONG.diagonalUnitCoefficients source) at hC1'
    rw [BONG.GoodBONG.heClassicEvenC1_fullPrefixValueUnits
      pairs c hnonnegative] at hC1'
    exact hC1'
  have hC2Units : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients
        (heClassicEvenC2 (K := K) pairs c cSharp))
      (BONG.GoodBONG.diagonalUnitCoefficients source) := by
    change DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients
        (bC2.prefixValueUnits (2 * pairs + 2) le_rfl))
      (BONG.GoodBONG.diagonalUnitCoefficients source) at hC2'
    rw [BONG.GoodBONG.heClassicEvenC2_fullPrefixValueUnits
      pairs c cSharp hnonnegative hcSharp] at hC2'
    exact hC2'
  have hexact := heHu2022Lemma313CodimensionOne
    (heClassicEvenC1 (K := K) pairs c)
    (heClassicEvenC2 (K := K) pairs c cSharp)
    pair source
  rcases hexact with hfirst | hsecond
  · exact hfirst.2 hC2Units
  · exact hsecond.1 hC1Units

/-- The Lemma 4.3(ii) failure alternative for an arbitrary defect-one
unit representative and its canonical sharp partner.  The published
`omega` statement is a specialization; Section 7 needs this invariant
form because its finite table is indexed by an arbitrary complete system
of unit square-class representatives. -/
theorem he2022ClassicLemma43ii_representative
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    {m : Nat} (pairs : Nat) (a : BONG.GoodBONG q L (m + 3))
    (hExtra : 2 * pairs + 5 <= m + 3)
    (hJ1 : a.HeClassicJ1EPrime (2 * pairs + 2) (by omega))
    (heOne : ramificationIndex K = 1)
    (_hSum :
      (1 : WithTop ℚ) <
        ((((a.order ⟨2 * pairs + 3, by omega⟩ : Int) : ℚ) :
            WithTop ℚ)) +
          a.truncatedPrefixDefect a ((-1) ^ (pairs + 2))
            0 (2 * pairs + 4))
    (hDAlpha :
      a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
          (2 * pairs + 4) =
        (a.alphaValue
          (⟨2 * pairs + 3, by omega⟩ : Fin (m + 2)) : WithTop ℚ))
    (hR : 1 <= a.order ⟨2 * pairs + 3, by omega⟩)
    (c : Kˣ) (hc : ordUnit K c = 0)
    (hcDefect : BONG.GoodBONG.defectOrder (K := K) c = 1) :
    let cSharp := heClassicDefectOneSharp (K := K) c hcDefect
    let hcSharp := heClassicDefectOneSharp_order c hcDefect
    let bC1 := heClassicEvenC1GoodBONG (K := K) pairs c (by omega)
    let bC2 := heClassicEvenC2GoodBONG (K := K) pairs c cSharp
      (by omega) hcSharp
    let i := BONG.GoodBONG.he2022ClassicLemma43Index pairs (by omega)
    ¬ a.HeClassicPublishedCentralConditionAt bC1 i ∨
      ¬ a.HeClassicPublishedCentralConditionAt bC2 i := by
  dsimp only
  let cSharp := heClassicDefectOneSharp (K := K) c hcDefect
  let hcSharp := heClassicDefectOneSharp_order c hcDefect
  let hnonnegative : 0 <= ordUnit K c := by omega
  let bC1 := heClassicEvenC1GoodBONG (K := K) pairs c hnonnegative
  let bC2 := heClassicEvenC2GoodBONG (K := K) pairs c cSharp
    hnonnegative hcSharp
  let i := BONG.GoodBONG.he2022ClassicLemma43Index pairs (by omega :
    2 * pairs + 4 <= m + 3)
  have hC1Order : ∀ j : Fin (2 * pairs + 2), bC1.order j = 0 := by
    intro j
    simp only [bC1, heClassicEvenC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC1_order]
    split
    · simpa only using hc
    · rfl
  have hC2Order : ∀ j : Fin (2 * pairs + 2), bC2.order j = 0 := by
    intro j
    simp only [bC2, heClassicEvenC2GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC2_order pairs c cSharp hcSharp]
    split
    · simpa only using hc
    · rfl
  have hC1Alpha : bC1.alphaValue
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 1)) = 1 := by
    have hall := heClassicEvenC1_alpha_eq_one (K := K) pairs c 1
      hnonnegative (Or.inr rfl) (by rw [hc]; norm_num)
      (by simpa using hcDefect)
    exact hall _
  have hC2Alpha : bC2.alphaValue
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 1)) = 1 := by
    have hall := heClassicEvenC2_alpha_eq_one (K := K) pairs c cSharp 1
      hnonnegative hcSharp (Or.inr rfl) (by rw [hc]; norm_num)
      (by simpa using hcDefect)
    exact hall _
  have hC1Self := BONG.GoodBONG.heClassicEvenC1_fullSelfDefect
    (K := K) pairs c hnonnegative
  have hC2Self := BONG.GoodBONG.heClassicEvenC2_fullSelfDefect
    (K := K) pairs c cSharp hnonnegative hcSharp
  have hC1Current : min
      (a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
        (2 * pairs + 4)) (1 : WithTop ℚ) <=
      a.centralCurrentDefect bC1 i := by
    have h := a.heClassicLemma43_C_centralCurrentDefect_lower_of_self
      pairs (by omega) bC1 c hC1Self
    rw [hcDefect] at h
    simpa only [i] using h
  have hC2Current : min
      (a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
        (2 * pairs + 4)) (1 : WithTop ℚ) <=
      a.centralCurrentDefect bC2 i := by
    have h := a.heClassicLemma43_C_centralCurrentDefect_lower_of_self
      pairs (by omega) bC2 c hC2Self
    rw [hcDefect] at h
    simpa only [i] using h
  have hC1Trigger : a.centralDefectTrigger bC1 i := by
    exact a.he2022ClassicLemma43_C_trigger pairs hExtra hJ1 heOne bC1
      hC1Order hC1Alpha hDAlpha hR hC1Current
  have hC2Trigger : a.centralDefectTrigger bC2 i := by
    exact a.he2022ClassicLemma43_C_trigger pairs hExtra hJ1 heOne bC2
      hC2Order hC2Alpha hDAlpha hR hC2Current
  have hpair := BONG.GoodBONG.heClassicEvenC_pairProperties
    (K := K) pairs c hcDefect
  have hnot := heClassicEvenC_notBothRepresents_of_pair
    (K := K) pairs a hExtra c cSharp hc hcSharp hpair
  exact BONG.GoodBONG.not_both_heClassicPublishedCentralConditionAt_of_triggers
    (m := m + 1) (n₁ := 2 * pairs) (n₂ := 2 * pairs)
    a bC1 bC2 i i hC1Trigger hC2Trigger hnot

/-- Representation of the actual finite even table forces the signed-prefix
upper bound used in Lemmas 4.4 and 4.5 at every admissible source rank.
For `e>1` this is `J2'_E`; for `e=1` the two exceptional `H` rows and a
defect-one representative pair exclude all remaining branches. -/
theorem signedPrefix_upper_of_all
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    {m : Nat}
    (a : @BONG.GoodBONG K _ _ _ _ _ X.Carrier X.addCommGroup X.module
      X.form X.lattice (m + 4))
    (hSource : 2 * pairs + 4 <= m + 4)
    (hXClassic : X.IsClassicIntegral)
    (hAll : forall i : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model
          (K := K) U hU pairs i)) :
    (by
      letI : AddCommGroup X.Carrier := X.addCommGroup
      letI : Module K X.Carrier := X.module
      exact
        (((a.order ⟨2 * pairs + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
            a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
              (2 * pairs + 4) <= 1) := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  have hClassic : Lattice.IsClassicIntegral X.form X.lattice := by
    exact hXClassic
  have hTests := literalLemma42Tests_of_all U hU pairs X a hSource hAll
  have hJ1 := a.he2022ClassicLemma42_j1Prime_of_publishedTests pairs
    hSource hClassic hTests
  by_cases heLarge : 1 < ramificationIndex K
  · have hJ2 := a.he2022ClassicLemma42_j2Prime_of_publishedTests pairs
      hSource hClassic hTests
    have hbound := hJ2 heLarge
    simpa only [show (2 * pairs + 2 + 2) / 2 = pairs + 2 by omega,
      show 2 * pairs + 2 + 1 = 2 * pairs + 3 by omega,
      show 2 * pairs + 2 + 2 = 2 * pairs + 4 by omega] using hbound
  · have hePositive : 0 < ramificationIndex K :=
      ramificationIndex_pos (K := K)
    have heOne : ramificationIndex K = 1 := by omega
    let oneOrder : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    let delta := (Dyadic.dyadicDiscriminantClassLawsProved
      (K := K)).discriminantUnit
    let deltaOrder : ordUnit K delta = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K delta).1
        (Dyadic.dyadicDiscriminantClassLawsProved
          (K := K)).discriminant_isValuationUnit
    let HOne := heClassicEvenHModel (K := K) pairs 1
      (Or.inl rfl) oneOrder
    let HDelta := heClassicEvenHModel (K := K) pairs delta
      (Or.inr (show delta =
        (Dyadic.dyadicDiscriminantClassLawsProved
          (K := K)).discriminantUnit from rfl)) deltaOrder
    have hXOne : X.Represents HOne := by
      simpa only [HOne, oneOrder] using
        represents_literalEvenHOne_of_all U hU pairs X hAll
    have hXDelta : X.Represents HDelta := by
      simpa only [HDelta, delta, deltaOrder] using
        represents_literalEvenHDelta_of_all U hU pairs X heOne hAll
    letI : AddCommGroup HOne.Carrier := HOne.addCommGroup
    letI : Module K HOne.Carrier := HOne.module
    letI : AddCommGroup HDelta.Carrier := HDelta.addCommGroup
    letI : Module K HDelta.Carrier := HDelta.module
    let bOne := heClassicEvenHGoodBONG (K := K) pairs 1
      (Or.inl rfl) oneOrder
    let bDelta := heClassicEvenHGoodBONG (K := K) pairs delta
      (Or.inr (show delta =
        (Dyadic.dyadicDiscriminantClassLawsProved
          (K := K)).discriminantUnit from rfl)) deltaOrder
    have hrepOne : Lattice.Represents X.form HOne.form
        X.lattice HOne.lattice := hXOne
    have hrepDelta : Lattice.Represents X.form HDelta.form
        X.lattice HDelta.lattice := hXDelta
    have hOneConditions := a.representationConditionsPrime_of_represents
      bOne (by omega) hrepOne
    have hDeltaConditions := a.representationConditionsPrime_of_represents
      bDelta (by omega) hrepDelta
    have hOneCentral := hOneConditions.centralRepresentations
    have hDeltaCentral := hDeltaConditions.centralRepresentations
    let D : WithTop ℚ :=
      a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
        (2 * pairs + 4)
    let R : Int := a.order ⟨2 * pairs + 3, by omega⟩
    let raw : WithTop ℚ := BONG.GoodBONG.defectOrder (K := K)
      (((-1 : Kˣ) ^ (pairs + 2)) * a.prefixProduct (2 * pairs + 4))
    let twoE : WithTop ℚ :=
      ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)
    by_contra hupper
    have hsum : (1 : WithTop ℚ) <
        (((R : Int) : ℚ) : WithTop ℚ) + D := by
      exact lt_of_not_ge (by simpa only [R, D] using hupper)
    by_cases hRawLt : raw < twoE
    · have hfailure := a.he2022ClassicLemma43i pairs hSource
          hJ1 heOne (by simpa only [R, D] using hsum)
          (Or.inl (by simpa only [raw, twoE] using hRawLt))
      dsimp only at hfailure
      let i : CentralRepresentationIndex
          (m + 4) (2 * pairs + 2) :=
        BONG.GoodBONG.he2022ClassicLemma43Index pairs hSource
      rcases hfailure with hOneFails | hDeltaFails
      · exact hOneFails
          ((a.heClassicPublishedCentralConditions_iff_forall_at bOne).mp
            hOneCentral i)
      · exact hDeltaFails
          ((a.heClassicPublishedCentralConditions_iff_forall_at bDelta).mp
            hDeltaCentral i)
    · have hRawGe : twoE <= raw := le_of_not_gt hRawLt
      by_cases hTwoELeD : twoE <= D
      · have hfailure := a.he2022ClassicLemma43i pairs hSource
            hJ1 heOne (by simpa only [R, D] using hsum)
            (Or.inr (by simpa only [D, twoE] using hTwoELeD))
        dsimp only at hfailure
        let i : CentralRepresentationIndex
            (m + 4) (2 * pairs + 2) :=
          BONG.GoodBONG.he2022ClassicLemma43Index pairs hSource
        rcases hfailure with hOneFails | hDeltaFails
        · exact hOneFails
            ((a.heClassicPublishedCentralConditions_iff_forall_at bOne).mp
              hOneCentral i)
        · exact hDeltaFails
            ((a.heClassicPublishedCentralConditions_iff_forall_at bDelta).mp
              hDeltaCentral i)
      · have hDLtTwoE : D < twoE := lt_of_not_ge hTwoELeD
        by_cases hExtra : 2 * pairs + 5 <= m + 4
        · let gap : Fin (m + 3) := ⟨2 * pairs + 3, by omega⟩
          have hDFormula : D =
              min raw (a.alphaValue gap : WithTop ℚ) := by
            dsimp only [D, raw, gap]
            unfold BONG.GoodBONG.truncatedPrefixDefect
            rw [a.prefixAlphaCap_zero,
              a.prefixAlphaCap_of_internal (by omega) (by omega)]
            simp [BONG.GoodBONG.prefixProduct]
          have hDAlpha : D = (a.alphaValue gap : WithTop ℚ) := by
            by_cases hRawLeAlpha : raw <=
                (a.alphaValue gap : WithTop ℚ)
            · rw [min_eq_left hRawLeAlpha] at hDFormula
              have : raw < twoE := by
                simpa only [hDFormula] using hDLtTwoE
              exact (not_lt_of_ge hRawGe this).elim
            · have hAlphaLeRaw : (a.alphaValue gap : WithTop ℚ) <= raw :=
                le_of_not_ge hRawLeAlpha
              simpa only [min_eq_right hAlphaLeRaw] using hDFormula
          have hfirst : a.order (0 : Fin (m + 4)) = 0 := by
            let first : Fin (2 * pairs + 3) := ⟨0, by omega⟩
            have h := hJ1.1 first
            have hindex : (⟨first.val, by omega⟩ : Fin (m + 4)) = 0 :=
              Fin.ext rfl
            rw [hindex] at h
            exact h
          have hRNonnegative : 0 <= R := by
            exact (a.he2022ClassicProposition24 hClassic).nonnegativeOfFirstZero
              hfirst ⟨2 * pairs + 3, by omega⟩
          have hc : ordUnit K (heClassicOmega (K := K)) = 0 :=
            heClassicOmega_order (K := K)
          have hcUnit : IsValuationUnit K
              ((heClassicOmega (K := K) : K)) :=
            (isValuationUnit_iff_ordUnit_eq_zero K _).2 hc
          obtain ⟨ri, s, _hsUnit, hfactor⟩ :=
            hU.complete (heClassicOmega (K := K)) hcUnit
          have hcRep : ordUnit K (U ri) = 0 :=
            (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit ri)
          have hcDefect : BONG.GoodBONG.defectOrder (K := K) (U ri) = 1 := by
            have homega := heClassicOmega_defect (K := K)
            rw [hfactor, BONG.GoodBONG.defectOrder_mul_square] at homega
            exact homega
          let di : HeClassicDefectOneIndex (K := K) U := ⟨ri, hcDefect⟩
          let idxFirst : HeClassicPublishedEvenTestingIndex
              (K := K) U (ramificationIndex K) :=
            .inr (.inl (di, false))
          let idxSecond : HeClassicPublishedEvenTestingIndex
              (K := K) U (ramificationIndex K) :=
            .inr (.inl (di, true))
          let cSharp := heClassicDefectOneSharp (K := K) (U ri) hcDefect
          let hcSharp := heClassicDefectOneSharp_order (U ri) hcDefect
          let bC1 := heClassicEvenC1GoodBONG (K := K) pairs (U ri)
            (by omega)
          let bC2 := heClassicEvenC2GoodBONG (K := K) pairs (U ri)
            cSharp (by omega) hcSharp
          have hFirstConditions :=
            HeClassicPublishedEvenTestingIndex.primeConditions_of_represents_model
              U hU pairs idxFirst a (by omega) (hAll idxFirst)
          have hSecondConditions :=
            HeClassicPublishedEvenTestingIndex.primeConditions_of_represents_model
              U hU pairs idxSecond a (by omega) (hAll idxSecond)
          change RepresentationConditionsPrime a bC1
            (by omega) at hFirstConditions
          change RepresentationConditionsPrime a bC2
            (by omega) at hSecondConditions
          have hRZero : R = 0 := by
            by_contra hRNe
            have hROne : 1 <= R := by omega
            have hfailure := he2022ClassicLemma43ii_representative
              (K := K) pairs a hExtra hJ1 heOne
              (by simpa only [D, R] using hsum)
              (by simpa only [D, gap] using hDAlpha)
              (by simpa only [R] using hROne)
              (U ri) hcRep hcDefect
            dsimp only at hfailure
            let i := BONG.GoodBONG.he2022ClassicLemma43Index pairs
              (by omega : 2 * pairs + 4 <= m + 4)
            rcases hfailure with hC1Fails | hC2Fails
            · exact hC1Fails
                ((a.heClassicPublishedCentralConditions_iff_forall_at bC1).mp
                  hFirstConditions.centralRepresentations i)
            · exact hC2Fails
                ((a.heClassicPublishedCentralConditions_iff_forall_at bC2).mp
                  hSecondConditions.centralRepresentations i)
          have hAlphaOneLt : (1 : ℚ) < a.alphaValue gap := by
            have hsum' := hsum
            rw [hRZero, Int.cast_zero, WithTop.coe_zero, zero_add,
              hDAlpha] at hsum'
            exact_mod_cast hsum'
          have hAlphaLtTwo : a.alphaValue gap < (2 : ℚ) := by
            have hlt := hDLtTwoE
            rw [hDAlpha] at hlt
            dsimp only [twoE] at hlt
            rw [heOne] at hlt
            norm_num at hlt
            rw [← a.coe_alphaValue gap] at hlt
            exact WithTop.coe_lt_coe.mp hlt
          have hAlphaIntegral : IsRationalInteger (a.alphaValue gap) := by
            rcases (a.he2022ClassicProposition23 gap).arithmeticShape with
              hsmall | hlarge
            · exact hsmall.2.2
            · rw [heOne] at hlarge
              norm_num at hlarge
              linarith
          rcases hAlphaIntegral with ⟨z, hz⟩
          have hzOne : (1 : Int) < z := by
            rw [hz] at hAlphaOneLt
            exact_mod_cast hAlphaOneLt
          have hzTwo : z < (2 : Int) := by
            rw [hz] at hAlphaLtTwo
            exact_mod_cast hAlphaLtTwo
          omega
        · have hlast : 2 * pairs + 4 = m + 4 := by omega
          have hDraw : D = raw := by
            dsimp only [D, raw]
            unfold BONG.GoodBONG.truncatedPrefixDefect
            have hcapLast : a.prefixAlphaCap (2 * pairs + 4) = ⊤ := by
              rw [hlast]
              exact a.prefixAlphaCap_last
            rw [a.prefixAlphaCap_zero, hcapLast]
            simp [BONG.GoodBONG.prefixProduct]
          rw [hDraw] at hDLtTwoE
          exact (not_lt_of_ge hRawGe) hDLtTwoE

/-- The four literal rows used in Lemma 4.5 may be replaced by the
square-class representatives actually present in the published finite
table.  The preceding invariant argument supplies the only upper bound
needed in the proof, while the remainder is exactly Lemma 4.5's alpha,
lower-bound, and binary-rank argument. -/
theorem heClassicEvenJ2_of_all_published
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    {m : Nat}
    (a : @BONG.GoodBONG K _ _ _ _ _ X.Carrier X.addCommGroup X.module
      X.form X.lattice (m + 4))
    (hSource : 2 * pairs + 4 <= m + 4)
    (hXClassic : X.IsClassicIntegral)
    (hAmbient : X.IsAmbientlyNUniversal (2 * pairs + 2))
    (hAll : forall i : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model
          (K := K) U hU pairs i)) :
    (by
      letI : AddCommGroup X.Carrier := X.addCommGroup
      letI : Module K X.Carrier := X.module
      exact a.HeClassicJ2E (2 * pairs + 2) (by omega)) := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  have hClassic : Lattice.IsClassicIntegral X.form X.lattice := hXClassic
  have hAmbient' : Lattice.AmbientlyNUniversal.{u, u, u}
      X.form (2 * pairs + 2) := hAmbient
  have hTests := literalLemma42Tests_of_all U hU pairs X a hSource hAll
  have hJ1 := a.he2022ClassicLemma42_j1Prime_of_publishedTests pairs
    hSource hClassic hTests
  have hUpperAdd := signedPrefix_upper_of_all
    U hU pairs X a hSource hXClassic hAll
  have hNextAlpha := a.he2022ClassicLemma45_nextAlpha pairs hSource
    hJ1 (by simpa only [show (2 * pairs + 4) / 2 = pairs + 2 by omega]
      using hUpperAdd)
  let R : Int := a.order ⟨2 * pairs + 3, by omega⟩
  let D : WithTop ℚ :=
    a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
      (2 * pairs + 4)
  have hfirst : a.order (0 : Fin (m + 4)) = 0 := by
    let first : Fin (2 * pairs + 3) := ⟨0, by omega⟩
    have h := hJ1.1 first
    have hindex : (⟨first.val, by omega⟩ : Fin (m + 4)) = 0 :=
      Fin.ext rfl
    rw [hindex] at h
    exact h
  have hRNonnegative : 0 <= R := by
    exact (a.he2022ClassicProposition24 hClassic).nonnegativeOfFirstZero
      hfirst ⟨2 * pairs + 3, by omega⟩
  have hLower : ((((1 - R : Int) : ℚ) : WithTop ℚ)) <= D := by
    simpa only [D, R] using
      a.he2022ClassicLemma45_signedPrefix_lower pairs hSource hJ1
        hNextAlpha (by simpa only [R] using hRNonnegative)
  have hUpper : D <= ((((1 - R : Int) : ℚ) : WithTop ℚ)) := by
    apply (WithTop.add_le_add_iff_left WithTop.coe_ne_top).mp
    calc
      (((R : Int) : ℚ) : WithTop ℚ) + D <= 1 := by
        simpa only [R, D] using hUpperAdd
      _ = (((R : Int) : ℚ) : WithTop ℚ) +
          ((((1 - R : Int) : ℚ) : WithTop ℚ)) := by
        norm_cast
        ring
  have hDEq : D = ((((1 - R : Int) : ℚ) : WithTop ℚ)) :=
    le_antisymm hUpper hLower
  have hEquality :
      (((a.order ⟨2 * pairs + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
          (2 * pairs + 4) = 1 := by
    rw [show a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
        (2 * pairs + 4) = D by rfl, hDEq]
    change (((R : Int) : ℚ) : WithTop ℚ) +
      ((((1 - R : Int) : ℚ) : WithTop ℚ)) = 1
    norm_cast
    ring
  unfold BONG.GoodBONG.HeClassicJ2E
  refine ⟨hNextAlpha, ?_, ?_⟩
  · simpa only [show 2 * pairs + 2 + 1 = 2 * pairs + 3 by omega,
      show (2 * pairs + 2 + 2) / 2 = pairs + 2 by omega,
      show 2 * pairs + 2 + 2 = 2 * pairs + 4 by omega] using hEquality
  · exact a.he2022ClassicLemma45_binaryRank_of_ambient_and_equality
      pairs hAmbient' hSource hEquality

/-- The terminal argument of Lemma 4.6 only needs a normalized pair from
the published table whose parameter is square-equivalent to the signed
source prefix.  This formulation separates that invariant argument from
the choice of square-class representatives in Definition 2.6. -/
theorem heClassicEvenJ3_of_published_pair
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    {m : Nat} (pairs : Nat) (a : BONG.GoodBONG q L (m + 4))
    (hSource : 2 * pairs + 4 <= m + 4)
    (c s cSharp : Kˣ) (hcNonnegative : 0 <= ordUnit K c)
    (hcSharpOrder : ordUnit K cSharp = 0)
    (hOrder : ordUnit K c = a.order ⟨2 * pairs + 3, by omega⟩)
    (hfactor : ((-1 : Kˣ) ^ (pairs + 2)) *
      a.prefixProduct (2 * pairs + 4) = c * s ^ 2)
    (hPair : HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) pairs c)
      (heClassicEvenC2 (K := K) pairs c cSharp))
    (hLongC1 : a.LongRepresentationConditions
      (heClassicEvenC1GoodBONG (K := K) pairs c hcNonnegative))
    (hLongC2 : a.LongRepresentationConditions
      (heClassicEvenC2GoodBONG (K := K) pairs c cSharp
        hcNonnegative hcSharpOrder)) :
    a.HeClassicJ3E (2 * pairs + 2) (by omega) := by
  let bC1 := heClassicEvenC1GoodBONG (K := K) pairs c hcNonnegative
  let bC2 := heClassicEvenC2GoodBONG (K := K) pairs c cSharp
    hcNonnegative hcSharpOrder
  unfold BONG.GoodBONG.HeClassicJ3E
  intro hExtraRaw
  have hExtra : 2 * pairs + 5 <= m + 4 := by omega
  by_contra hNotBound
  have hNotBound' : ¬ (a.order ⟨2 * pairs + 4, by omega⟩ -
      a.order ⟨2 * pairs + 3, by omega⟩ <=
        2 * (ramificationIndex K : Int)) := by
    simpa only [show 2 * pairs + 2 + 1 = 2 * pairs + 3 by omega,
      show 2 * pairs + 2 + 2 = 2 * pairs + 4 by omega] using hNotBound
  have hLargeGap : 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * pairs + 4, by omega⟩ -
        a.order ⟨2 * pairs + 3, by omega⟩ := by
    omega
  have hC1Last : bC1.order ⟨2 * pairs + 1, by omega⟩ =
      a.order ⟨2 * pairs + 3, by omega⟩ := by
    calc
      bC1.order ⟨2 * pairs + 1, by omega⟩ = ordUnit K c := by
        simp only [bC1, heClassicEvenC1GoodBONG,
          heHuExactGoodBONG_order, heClassicEvenC1_order]
        simp
      _ = a.order ⟨2 * pairs + 3, by omega⟩ := hOrder
  have hC2Last : bC2.order ⟨2 * pairs + 1, by omega⟩ =
      a.order ⟨2 * pairs + 3, by omega⟩ := by
    calc
      bC2.order ⟨2 * pairs + 1, by omega⟩ = ordUnit K c := by
        simp only [bC2, heClassicEvenC2GoodBONG,
          heHuExactGoodBONG_order]
        rw [heClassicEvenC2_order pairs c cSharp hcSharpOrder]
        simp
      _ = a.order ⟨2 * pairs + 3, by omega⟩ := hOrder
  have hRepC1 := a.he2022ClassicLemma46_terminalRepresentation pairs bC1
    hExtra hLargeGap hC1Last hLongC1
  have hRepC2 := a.he2022ClassicLemma46_terminalRepresentation pairs bC2
    hExtra hLargeGap hC2Last hLongC2
  let source := a.prefixValueUnits (2 * pairs + 4) (by omega)
  have hRepC1Units : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients
        (heClassicEvenC1 (K := K) pairs c))
      (BONG.GoodBONG.diagonalUnitCoefficients source) := by
    change DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients
        (bC1.prefixValueUnits (2 * pairs + 2) le_rfl))
      (BONG.GoodBONG.diagonalUnitCoefficients source) at hRepC1
    rw [BONG.GoodBONG.heClassicEvenC1_fullPrefixValueUnits
      pairs c hcNonnegative] at hRepC1
    exact hRepC1
  have hRepC2Units : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients
        (heClassicEvenC2 (K := K) pairs c cSharp))
      (BONG.GoodBONG.diagonalUnitCoefficients source) := by
    change DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients
        (bC2.prefixValueUnits (2 * pairs + 2) le_rfl))
      (BONG.GoodBONG.diagonalUnitCoefficients source) at hRepC2
    rw [BONG.GoodBONG.heClassicEvenC2_fullPrefixValueUnits
      pairs c cSharp hcNonnegative hcSharpOrder] at hRepC2
    exact hRepC2
  have hSourceDet : BONG.GoodBONG.diagonalUnitDeterminant source =
      a.prefixProduct (2 * pairs + 4) := by
    simpa only [source] using
      a.diagonalUnitDeterminant_prefixValueUnits (2 * pairs + 4) (by omega)
  have hC1Det :
      BONG.GoodBONG.diagonalUnitDeterminant
          (heClassicEvenC1 (K := K) pairs c) =
        (-1 : Kˣ) ^ (pairs + 1) * c := by
    calc
      BONG.GoodBONG.diagonalUnitDeterminant
          (heClassicEvenC1 (K := K) pairs c) =
          BONG.GoodBONG.diagonalUnitDeterminant
            (bC1.prefixValueUnits (2 * pairs + 2) le_rfl) := by
        rw [BONG.GoodBONG.heClassicEvenC1_fullPrefixValueUnits
          pairs c hcNonnegative]
      _ = bC1.prefixProduct (2 * pairs + 2) :=
        bC1.diagonalUnitDeterminant_prefixValueUnits
          (2 * pairs + 2) le_rfl
      _ = (-1 : Kˣ) ^ (pairs + 1) * c :=
        BONG.GoodBONG.heClassicEvenC1_prefixProduct_full
          (K := K) pairs c hcNonnegative
  have hSquare : IsSquare
      ((((-1 : Kˣ) ^ (pairs + 2)) *
        a.prefixProduct (2 * pairs + 4)) * c) := by
    refine ⟨c * s, ?_⟩
    rw [hfactor]
    simp only [pow_two]
    ac_rfl
  have hDet : IsSquare
      (-BONG.GoodBONG.diagonalUnitDeterminant source *
        BONG.GoodBONG.diagonalUnitDeterminant
          (heClassicEvenC1 (K := K) pairs c)) := by
    rw [hSourceDet, hC1Det]
    have hsign :
        -a.prefixProduct (2 * pairs + 4) *
            ((-1 : Kˣ) ^ (pairs + 1) * c) =
          (((-1 : Kˣ) ^ (pairs + 2)) *
            a.prefixProduct (2 * pairs + 4)) * c := by
      have hneg : -a.prefixProduct (2 * pairs + 4) =
          (-1 : Kˣ) * a.prefixProduct (2 * pairs + 4) := by
        simp
      rw [hneg,
        show (-1 : Kˣ) ^ (pairs + 2) =
          (-1 : Kˣ) ^ (pairs + 1) * (-1 : Kˣ) by
            rw [show pairs + 2 = (pairs + 1) + 1 by omega, pow_succ]]
      ac_rfl
    rw [hsign]
    exact hSquare
  have hExactlyOne := heHu2022Lemma313CodimensionTwo
    (heClassicEvenC1 (K := K) pairs c)
    (heClassicEvenC2 (K := K) pairs c cSharp)
    hPair source hDet
  rcases hExactlyOne with hFirst | hSecond
  · exact hFirst.2 hRepC2Units
  · exact hSecond.1 hRepC1Units

/-- A signed determinant parameter with the two low-order and low-defect
possibilities singled out by Lemma 4.4 is square-equivalent to one of the
literal pairs in the finite even table, and both members of that pair are
represented by the source. -/
theorem exists_represented_publishedEven_pair_of_low_signed_parameter
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hAll : forall i : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model
          (K := K) U hU pairs i))
    (c0 : Kˣ)
    (hOrder : ordUnit K c0 = 0 ∨ ordUnit K c0 = 1)
    (hDefect : BONG.GoodBONG.defectOrder (K := K) c0 = 0 ∨
      BONG.GoodBONG.defectOrder (K := K) c0 = 1) :
    (by
      letI : AddCommGroup X.Carrier := X.addCommGroup
      letI : Module K X.Carrier := X.module
      exact ∃ (c s : Kˣ) (second : Fin (2 * pairs + 2) -> Kˣ),
        HeHuSpacePairProperties
            (heClassicEvenC1 (K := K) pairs c) second ∧
          0 <= ordUnit K c ∧ c0 = c * s ^ 2 ∧
          X.form.Represents
            (BONG.coefficientDiagonalSpace
              (heClassicEvenC1 (K := K) pairs c)) ∧
          X.form.Represents (BONG.coefficientDiagonalSpace second)) := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  rcases hOrder with hOrderZero | hOrderOne
  · have hc0Unit : IsValuationUnit K (c0 : K) :=
      (isValuationUnit_iff_ordUnit_eq_zero K c0).2 hOrderZero
    have hc0Even : Even (ordUnit K c0) := by
      rw [hOrderZero]
      exact Even.zero
    have hDefectOne : BONG.GoodBONG.defectOrder (K := K) c0 = 1 := by
      rcases hDefect with hzero | hone
      · have hlower := BONG.GoodBONG.defectOrder_one_le_of_even
          c0 hc0Even
        rw [hzero] at hlower
        exact (not_le_of_gt (show (0 : WithTop ℚ) < 1 by norm_num)
          hlower).elim
      · exact hone
    obtain ⟨i, s, _hsUnit, hfactor⟩ := hU.complete c0 hc0Unit
    have hUiDefect : BONG.GoodBONG.defectOrder (K := K) (U i) = 1 := by
      rw [hfactor, BONG.GoodBONG.defectOrder_mul_square] at hDefectOne
      exact hDefectOne
    let di : HeClassicDefectOneIndex (K := K) U := ⟨i, hUiDefect⟩
    let iFirst : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K) := .inr (.inl (di, false))
    let iSecond : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K) := .inr (.inl (di, true))
    have hXFirst := hAll iFirst
    have hXSecond := hAll iSecond
    dsimp [iFirst, di,
      HeClassicPublishedEvenTestingIndex.model,
      heClassicEvenC1Model, heHuExactModel] at hXFirst
    dsimp [iSecond, di,
      HeClassicPublishedEvenTestingIndex.model,
      heClassicEvenC2Model, heHuExactModel] at hXSecond
    let cSharp := heClassicDefectOneSharp (K := K) (U i) hUiDefect
    refine ⟨U i, s,
      heClassicEvenC2 (K := K) pairs (U i) cSharp, ?_, ?_,
      hfactor, ?_, ?_⟩
    · simpa only [cSharp] using
        (BONG.GoodBONG.heClassicEvenC_pairProperties
          (K := K) pairs (U i) hUiDefect)
    · rw [(isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i)]
    · exact hXFirst.ambient
    · simpa only [cSharp] using hXSecond.ambient
  · have hc0Odd : Odd (ordUnit K c0) := by
      rw [hOrderOne]
      exact odd_one
    have hDefectZero : BONG.GoodBONG.defectOrder (K := K) c0 = 0 := by
      unfold BONG.GoodBONG.defectOrder
      rw [quadraticDefect_eq_zero_of_odd_ordUnit c0 hc0Odd]
      rfl
    let pi : Kˣ := uniformizerPowerUnit K (1 : Int)
    let unitPart : Kˣ := c0 / pi
    have hUnitPartOrder : ordUnit K unitPart = 0 := by
      dsimp only [unitPart, pi]
      rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
        ordUnit_uniformizerPowerUnit, hOrderOne]
      norm_num
    have hUnitPart : IsValuationUnit K (unitPart : K) :=
      (isValuationUnit_iff_ordUnit_eq_zero K unitPart).2 hUnitPartOrder
    obtain ⟨i, s, _hsUnit, hunitFactor⟩ :=
      hU.complete unitPart hUnitPart
    let c : Kˣ := U i * pi
    have hcOrder : ordUnit K c = 1 := by
      dsimp only [c, pi]
      rw [ordUnit_mul,
        (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i),
        ordUnit_uniformizerPowerUnit]
      norm_num
    have hcOdd : Odd (ordUnit K c) := by
      rw [hcOrder]
      exact odd_one
    have hfactor : c0 = c * s ^ 2 := by
      calc
        c0 = unitPart * pi := by simp [unitPart]
        _ = (U i * s ^ 2) * pi := by rw [hunitFactor]
        _ = c * s ^ 2 := by
          dsimp only [c]
          ac_rfl
    have hcDefect : BONG.GoodBONG.defectOrder (K := K) c = 0 := by
      rw [hfactor, BONG.GoodBONG.defectOrder_mul_square] at hDefectZero
      exact hDefectZero
    let delta :=
      (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminantUnit
    let iFirst : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K) := .inr (.inr (i, false))
    let iSecond : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K) := .inr (.inr (i, true))
    have hXFirst := hAll iFirst
    have hXSecond := hAll iSecond
    dsimp [iFirst, c, pi,
      HeClassicPublishedEvenTestingIndex.model,
      heClassicEvenC1Model, heHuExactModel] at hXFirst
    dsimp [iSecond, c, pi, delta,
      HeClassicPublishedEvenTestingIndex.model,
      heClassicEvenC2Model, heHuExactModel] at hXSecond
    refine ⟨c, s, heClassicEvenC2 (K := K) pairs c delta,
      ?_, by omega, hfactor, ?_, ?_⟩
    · simpa only [delta] using
        (heClassicEvenC_oddOrder_literalPairProperties
          (K := K) pairs c hcOdd)
    · simpa only [c, pi] using hXFirst.ambient
    · simpa only [c, pi, delta] using hXSecond.ambient

/-- The complete finite even table forces the last-gap condition `J3_E`.
The proof normalizes the signed source prefix to the representative that
actually indexes the table and then invokes the invariant terminal argument
above. -/
theorem heClassicEvenJ3_of_all_published
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    {m : Nat}
    (a : @BONG.GoodBONG K _ _ _ _ _ X.Carrier X.addCommGroup X.module
      X.form X.lattice (m + 4))
    (hSource : 2 * pairs + 4 <= m + 4)
    (hXClassic : X.IsClassicIntegral)
    (hAmbient : X.IsAmbientlyNUniversal (2 * pairs + 2))
    (hAll : forall i : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model
          (K := K) U hU pairs i)) :
    (by
      letI : AddCommGroup X.Carrier := X.addCommGroup
      letI : Module K X.Carrier := X.module
      exact a.HeClassicJ3E (2 * pairs + 2) (by omega)) := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  have hClassic : Lattice.IsClassicIntegral X.form X.lattice := hXClassic
  have hTests := literalLemma42Tests_of_all U hU pairs X a hSource hAll
  have hJ1 := a.he2022ClassicLemma42_j1Prime_of_publishedTests pairs
    hSource hClassic hTests
  have hJ2 := heClassicEvenJ2_of_all_published
    U hU pairs X a hSource hXClassic hAmbient hAll
  change a.HeClassicJ3E (2 * pairs + 2) (by omega)
  unfold BONG.GoodBONG.HeClassicJ3E
  intro hExtraRaw
  have hExtra : 2 * pairs + 5 <= m + 4 := by omega
  by_contra hNotBound
  have hLargeGap : 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * pairs + 4, by omega⟩ -
        a.order ⟨2 * pairs + 3, by omega⟩ := by
    have hNotBound' : ¬ (a.order ⟨2 * pairs + 4, by omega⟩ -
        a.order ⟨2 * pairs + 3, by omega⟩ <=
          2 * (ramificationIndex K : Int)) := by
      simpa only [show 2 * pairs + 2 + 1 = 2 * pairs + 3 by omega,
        show 2 * pairs + 2 + 2 = 2 * pairs + 4 by omega] using hNotBound
    omega
  let c0 : Kˣ := ((-1 : Kˣ) ^ (pairs + 2)) *
    a.prefixProduct (2 * pairs + 4)
  have hCases := a.he2022ClassicLemma46_j2_cases
    pairs hSource hJ1 hJ2
  have hc0OrderEq : ordUnit K c0 =
      a.order ⟨2 * pairs + 3, by omega⟩ := by
    simpa only [c0] using
      a.he2022ClassicLemma46_signedPrefix_order pairs hSource hJ1
  have hc0Order : ordUnit K c0 = 0 ∨ ordUnit K c0 = 1 := by
    rw [hc0OrderEq]
    exact hCases.1
  have hc0DefectEq : BONG.GoodBONG.defectOrder (K := K) c0 =
      a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
        (2 * pairs + 4) := by
    simpa only [c0] using
      a.he2022ClassicLemma46_rawDefect_eq_capped pairs hSource hExtra
        hJ1 hJ2 hLargeGap
  have hc0Defect : BONG.GoodBONG.defectOrder (K := K) c0 = 0 ∨
      BONG.GoodBONG.defectOrder (K := K) c0 = 1 := by
    rw [hc0DefectEq]
    exact hCases.2
  rcases hc0Order with hc0OrderZero | hc0OrderOne
  · have hc0Unit : IsValuationUnit K (c0 : K) :=
      (isValuationUnit_iff_ordUnit_eq_zero K c0).2 hc0OrderZero
    have hc0Even : Even (ordUnit K c0) := by
      rw [hc0OrderZero]
      exact Even.zero
    have hc0DefectOne : BONG.GoodBONG.defectOrder (K := K) c0 = 1 := by
      rcases hc0Defect with hzero | hone
      · have hlower := BONG.GoodBONG.defectOrder_one_le_of_even c0 hc0Even
        rw [hzero] at hlower
        exact (not_le_of_gt (show (0 : WithTop ℚ) < 1 by norm_num)
          hlower).elim
      · exact hone
    obtain ⟨i, s, hsUnit, hfactor⟩ := hU.complete c0 hc0Unit
    have hsOrder : ordUnit K s = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K s).1 hsUnit
    have hcDefect : BONG.GoodBONG.defectOrder (K := K) (U i) = 1 := by
      rw [hfactor, BONG.GoodBONG.defectOrder_mul_square] at hc0DefectOne
      exact hc0DefectOne
    have hcOrder : ordUnit K (U i) = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i)
    have hcOrderSource : ordUnit K (U i) =
        a.order ⟨2 * pairs + 3, by omega⟩ := by
      have hOrderFactor : ordUnit K c0 = ordUnit K (U i) := by
        rw [hfactor, ordUnit_mul, ordUnit_pow, hsOrder]
        simp
      exact hOrderFactor.symm.trans hc0OrderEq
    let di : HeClassicDefectOneIndex (K := K) U := ⟨i, hcDefect⟩
    let idxFirst : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K) := .inr (.inl (di, false))
    let idxSecond : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K) := .inr (.inl (di, true))
    let cSharp := heClassicDefectOneSharp (K := K) (U i) hcDefect
    let hcSharpOrder := heClassicDefectOneSharp_order (U i) hcDefect
    let bC1 := heClassicEvenC1GoodBONG (K := K) pairs (U i) (by omega)
    let bC2 := heClassicEvenC2GoodBONG (K := K) pairs (U i) cSharp
      (by omega) hcSharpOrder
    have hFirstConditions :=
      HeClassicPublishedEvenTestingIndex.primeConditions_of_represents_model
        U hU pairs idxFirst a (by omega) (hAll idxFirst)
    have hSecondConditions :=
      HeClassicPublishedEvenTestingIndex.primeConditions_of_represents_model
        U hU pairs idxSecond a (by omega) (hAll idxSecond)
    change RepresentationConditionsPrime a bC1 (by omega) at hFirstConditions
    change RepresentationConditionsPrime a bC2 (by omega) at hSecondConditions
    have hPair := BONG.GoodBONG.heClassicEvenC_pairProperties
      (K := K) pairs (U i) hcDefect
    have hJ3 := heClassicEvenJ3_of_published_pair
      (K := K) pairs a hSource (U i) s cSharp (by omega)
      hcSharpOrder hcOrderSource (by simpa only [c0] using hfactor)
      (by simpa only [cSharp] using hPair)
      (by simpa only [bC1] using hFirstConditions.longRepresentations)
      (by simpa only [bC2] using hSecondConditions.longRepresentations)
    exact hNotBound (hJ3 hExtraRaw)
  · have hc0Odd : Odd (ordUnit K c0) := by
      rw [hc0OrderOne]
      exact odd_one
    have hc0DefectZero : BONG.GoodBONG.defectOrder (K := K) c0 = 0 := by
      unfold BONG.GoodBONG.defectOrder
      rw [quadraticDefect_eq_zero_of_odd_ordUnit c0 hc0Odd]
      rfl
    let pi : Kˣ := uniformizerPowerUnit K (1 : Int)
    let unitPart : Kˣ := c0 / pi
    have hUnitPartOrder : ordUnit K unitPart = 0 := by
      dsimp only [unitPart, pi]
      rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
        ordUnit_uniformizerPowerUnit, hc0OrderOne]
      norm_num
    have hUnitPart : IsValuationUnit K (unitPart : K) :=
      (isValuationUnit_iff_ordUnit_eq_zero K unitPart).2 hUnitPartOrder
    obtain ⟨i, s, hsUnit, hunitFactor⟩ := hU.complete unitPart hUnitPart
    have hsOrder : ordUnit K s = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K s).1 hsUnit
    let c : Kˣ := U i * pi
    have hcOrder : ordUnit K c = 1 := by
      dsimp only [c, pi]
      rw [ordUnit_mul,
        (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i),
        ordUnit_uniformizerPowerUnit]
      norm_num
    have hcOdd : Odd (ordUnit K c) := by
      rw [hcOrder]
      exact odd_one
    have hfactor : c0 = c * s ^ 2 := by
      calc
        c0 = unitPart * pi := by simp [unitPart]
        _ = (U i * s ^ 2) * pi := by rw [hunitFactor]
        _ = c * s ^ 2 := by
          dsimp only [c]
          ac_rfl
    have hcDefect : BONG.GoodBONG.defectOrder (K := K) c = 0 := by
      rw [hfactor, BONG.GoodBONG.defectOrder_mul_square] at hc0DefectZero
      exact hc0DefectZero
    have hcOrderSource : ordUnit K c =
        a.order ⟨2 * pairs + 3, by omega⟩ := by
      have hOrderFactor : ordUnit K c0 = ordUnit K c := by
        rw [hfactor, ordUnit_mul, ordUnit_pow, hsOrder]
        simp
      exact hOrderFactor.symm.trans hc0OrderEq
    let delta :=
      (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminantUnit
    let hdeltaOrder : ordUnit K delta = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K _).1
        (Dyadic.dyadicDiscriminantClassLawsProved
          (K := K)).discriminant_isValuationUnit
    let idxFirst : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K) := .inr (.inr (i, false))
    let idxSecond : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K) := .inr (.inr (i, true))
    let bC1 := heClassicEvenC1GoodBONG (K := K) pairs c (by omega)
    let bC2 := heClassicEvenC2GoodBONG (K := K) pairs c delta
      (by omega) hdeltaOrder
    have hFirstConditions :=
      HeClassicPublishedEvenTestingIndex.primeConditions_of_represents_model
        U hU pairs idxFirst a (by omega) (hAll idxFirst)
    have hSecondConditions :=
      HeClassicPublishedEvenTestingIndex.primeConditions_of_represents_model
        U hU pairs idxSecond a (by omega) (hAll idxSecond)
    change RepresentationConditionsPrime a bC1 (by omega) at hFirstConditions
    change RepresentationConditionsPrime a bC2 (by omega) at hSecondConditions
    have hPair := heClassicEvenC_oddOrder_literalPairProperties
      (K := K) pairs c hcOdd
    have hJ3 := heClassicEvenJ3_of_published_pair
      (K := K) pairs a hSource c s delta (by omega)
      hdeltaOrder hcOrderSource (by simpa only [c0] using hfactor)
      (by simpa only [delta] using hPair)
      (by simpa only [bC1] using hFirstConditions.longRepresentations)
      (by simpa only [bC2] using hSecondConditions.longRepresentations)
    exact hNotBound (hJ3 hExtraRaw)

/-- A finite family tests classic rank-`n` universality.  The source is
required to be classic integral, exactly as in Theorem 1.3. -/
def IsClassicUniversalityTestingFamily {I : Type u}
    (family : I -> QuadraticLatticeModel (K := K)) (n : Nat) : Prop :=
  forall X : QuadraticLatticeModel (K := K),
    X.IsClassicIntegral -> (forall i, X.Represents (family i)) ->
      X.IsClassicNUniversal n

/-- Literal deletion minimality for a classic testing family.  Distinct
indices are retained because Theorem 1.3 counts and deletes the displayed
lattices themselves. -/
def IsLiteralMinimalClassicUniversalityTestingFamily {I : Type u}
    (family : I -> QuadraticLatticeModel (K := K)) (n : Nat) : Prop :=
  IsClassicUniversalityTestingFamily family n ∧
    forall i, exists X : QuadraticLatticeModel (K := K),
      X.IsClassicIntegral ∧ ¬ X.Represents (family i) ∧
        forall j, j ≠ i -> X.Represents (family j)

/-- Necessity in Lemma 7.4 for every even entry of the printed table. -/
theorem classicUniversal_represents_publishedEven
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hX : X.IsClassicNUniversal (2 * pairs + 2))
    (i : HeClassicPublishedEvenTestingIndex (K := K) U
      (ramificationIndex K)) :
    X.Represents
      (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs i) := by
  let T := HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs i
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  exact hX.2 T.form T.lattice
    (HeClassicPublishedEvenTestingIndex.model_rank U hU pairs i)
    (HeClassicPublishedEvenTestingIndex.model_isClassicIntegral U hU pairs i)

/-- Necessity in Lemma 7.4 for every odd entry of the printed table. -/
theorem classicUniversal_represents_publishedOdd
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K))
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hX : X.IsClassicNUniversal (2 * pairs + 3))
    (i : HeClassicPublishedOddTestingIndex I) :
    X.Represents
      (HeClassicPublishedOddTestingIndex.model
        (K := K) U hU omegaData pairs i) := by
  let T := HeClassicPublishedOddTestingIndex.model
    (K := K) U hU omegaData pairs i
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  exact hX.2 T.form T.lattice
    (HeClassicPublishedOddTestingIndex.model_rank U hU omegaData pairs i)
    (HeClassicPublishedOddTestingIndex.model_isClassicIntegral
      U hU omegaData pairs i)

/-- The necessity direction of Lemma 7.4, even rank. -/
theorem classicUniversal_implies_all_publishedEven
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hX : X.IsClassicNUniversal (2 * pairs + 2)) :
    forall i : HeClassicPublishedEvenTestingIndex (K := K) U
      (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs i) :=
  fun i => classicUniversal_represents_publishedEven U hU pairs X hX i

/-- The necessity direction of Lemma 7.4, odd rank. -/
theorem classicUniversal_implies_all_publishedOdd
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K))
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hX : X.IsClassicNUniversal (2 * pairs + 3)) :
    forall i : HeClassicPublishedOddTestingIndex I,
      X.Represents
        (HeClassicPublishedOddTestingIndex.model
          (K := K) U hU omegaData pairs i) :=
  fun i => classicUniversal_represents_publishedOdd
    U hU omegaData pairs X hX i

/-- Lemma 7.3, odd-rank branch.  The literal classic table exhausts all
ambient quadratic spaces because each row has the same space as its He--Hu
maximal representative and the latter family is already classified. -/
theorem all_publishedOdd_implies_ambientlyUniversal
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) (pairs : Nat)
    (X : QuadraticLatticeModel (K := K))
    (hAll : forall i : HeClassicPublishedOddTestingIndex I,
      X.Represents
        (HeClassicPublishedOddTestingIndex.model
          (K := K) U hU omegaData pairs i)) :
    X.IsAmbientlyNUniversal (2 * pairs + 3) := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  change Lattice.AmbientlyNUniversal.{u, u, u} X.form (2 * pairs + 3)
  intro W _instWGroup _instWModule r M hRank _hIntegral
  let Y := Lattice.quadraticLatticeModel r M
  have hYRank : Y.rank = 2 * pairs + 3 := by
    change Module.finrank K W = 2 * pairs + 3
    exact hRank
  obtain ⟨j, hYj⟩ :=
    exists_publishedOddIndex_for_model U hU pairs Y hYRank
  let i := classicOddIndexOfHeHu j
  let C := HeClassicPublishedOddTestingIndex.model
    (K := K) U hU omegaData pairs i
  let H := HeHuPublishedOddTestingIndex.model
    (K := K) (U := U) (pairs := pairs) j
  have hXC : X.Represents C := by
    simpa only [C, i] using hAll i
  have hCH : C.IsAmbientlyIsometric H := by
    simpa only [C, H, i] using
      classicOddModel_isAmbientlyIsometric_heHuModel
        U hU omegaData pairs j
  have hYH : Y.IsAmbientlyIsometric H := by
    simpa only [H] using hYj
  letI : AddCommGroup C.Carrier := C.addCommGroup
  letI : Module K C.Carrier := C.module
  letI : AddCommGroup H.Carrier := H.addCommGroup
  letI : Module K H.Carrier := H.module
  letI : AddCommGroup Y.Carrier := Y.addCommGroup
  letI : Module K Y.Carrier := Y.module
  rcases hCH with ⟨fCH⟩
  rcases hYH with ⟨fYH⟩
  exact hXC.ambient.trans
    ⟨fCH.symm.toRepresentation.trans fYH.toRepresentation⟩

/-- The two defect-one `C` rows already force an even-rank source to have
at least two extra variables.  Equal rank is excluded by nonisometry and
codimension one by He--Hu Lemma 3.13. -/
theorem all_publishedEven_implies_rank_add_two_le
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hAll : forall i : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model
          (K := K) U hU pairs i)) :
    2 * pairs + 4 <= X.rank := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : Module.Finite K X.Carrier := X.lattice.moduleFinite
  have homegaUnit : IsValuationUnit K ((heClassicOmega (K := K) : K)) :=
    (isValuationUnit_iff_ordUnit_eq_zero K _).2
      (heClassicOmega_order (K := K))
  obtain ⟨i, s, _hsUnit, hfactor⟩ :=
    hU.complete (heClassicOmega (K := K)) homegaUnit
  have hdefect : BONG.GoodBONG.defectOrder (K := K) (U i) =
      (1 : WithTop ℚ) := by
    have h := heClassicOmega_defect (K := K)
    rw [hfactor, BONG.GoodBONG.defectOrder_mul_square] at h
    exact h
  let di : HeClassicDefectOneIndex (K := K) U := ⟨i, hdefect⟩
  let iFirst : HeClassicPublishedEvenTestingIndex
      (K := K) U (ramificationIndex K) := .inr (.inl (di, false))
  let iSecond : HeClassicPublishedEvenTestingIndex
      (K := K) U (ramificationIndex K) := .inr (.inl (di, true))
  let CFirst := HeClassicPublishedEvenTestingIndex.model
    (K := K) U hU pairs iFirst
  let CSecond := HeClassicPublishedEvenTestingIndex.model
    (K := K) U hU pairs iSecond
  have hXFirst : X.Represents CFirst := by
    simpa only [CFirst] using hAll iFirst
  have hXSecond : X.Represents CSecond := by
    simpa only [CSecond] using hAll iSecond
  dsimp [CFirst, iFirst, di,
    HeClassicPublishedEvenTestingIndex.model,
    heClassicEvenC1Model, heHuExactModel] at hXFirst
  dsimp [CSecond, iSecond, di,
    HeClassicPublishedEvenTestingIndex.model,
    heClassicEvenC2Model, heHuExactModel] at hXSecond
  have hFirst : X.form.Represents
      (BONG.coefficientDiagonalSpace
        (heClassicEvenC1 (K := K) pairs (U i))) := by
    exact hXFirst.ambient
  have hSecond : X.form.Represents
      (BONG.coefficientDiagonalSpace
        (heClassicEvenC2 (K := K) pairs (U i)
          (heClassicDefectOneSharp (K := K) (U i) hdefect))) := by
    simpa only using hXSecond.ambient
  have hRankLower : 2 * pairs + 2 <= Module.finrank K X.Carrier := by
    rcases hFirst with ⟨f⟩
    have hle := f.toLinearMap.finrank_le_finrank_of_injective f.injective
    simpa using hle
  by_contra hnot
  have hRankCases : Module.finrank K X.Carrier = 2 * pairs + 2 ∨
      Module.finrank K X.Carrier = 2 * pairs + 3 := by
    have hRankDef : X.rank = Module.finrank K X.Carrier := by rfl
    rw [hRankDef] at hnot
    omega
  have pair := BONG.GoodBONG.heClassicEvenC_pairProperties
    (K := K) pairs (U i) hdefect
  rcases hRankCases with hEq | hEq
  · exact pair_not_both_represents_of_rank_eq
      (heClassicEvenC1 (K := K) pairs (U i))
      (heClassicEvenC2 (K := K) pairs (U i)
        (heClassicDefectOneSharp (K := K) (U i) hdefect))
      pair hEq hFirst hSecond
  · exact pair_not_both_represents_of_rank_eq_add_one
      (heClassicEvenC1 (K := K) pairs (U i))
      (heClassicEvenC2 (K := K) pairs (U i)
        (heClassicDefectOneSharp (K := K) (U i) hdefect))
      pair hEq hFirst hSecond

/-- Lemma 7.3, even-rank branch.  The only rank not covered directly by
high-rank isotropy is `n+2`.  Lemma 4.4 puts its signed determinant in one
of the two low-defect rows of the literal finite table, while Lemma 3.13
says that the corresponding two columns cannot both occur. -/
theorem all_publishedEven_implies_ambientlyUniversal
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hXClassic : X.IsClassicIntegral)
    (hAll : forall i : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model
          (K := K) U hU pairs i)) :
    (by
      letI : AddCommGroup X.Carrier := X.addCommGroup
      letI : Module K X.Carrier := X.module
      exact Lattice.AmbientlyNUniversal.{u, u, u}
        X.form (2 * pairs + 2)) := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : Module.Finite K X.Carrier := X.lattice.moduleFinite
  change Lattice.AmbientlyNUniversal.{u, u, u}
    X.form (2 * pairs + 2)
  by_cases hLarge : 2 * pairs + 5 <= Module.finrank K X.Carrier
  · exact Lattice.ambientlyNUniversal_of_rank_add_three_le.{u, u, u}
      (q := X.form) (2 * pairs + 2) (by simpa only [show
        2 * pairs + 2 + 3 = 2 * pairs + 5 by omega] using hLarge)
  · have hRankLower : 2 * pairs + 4 <= Module.finrank K X.Carrier := by
      have h := all_publishedEven_implies_rank_add_two_le
        (K := K) U hU pairs X hAll
      change 2 * pairs + 4 <= Module.finrank K X.Carrier at h
      exact h
    have hRankEq : Module.finrank K X.Carrier =
        2 * pairs + 4 := by omega
    obtain ⟨aRaw⟩ := exists_good_bong X.form X.lattice
    let a : BONG.GoodBONG X.form X.lattice (2 * pairs + 4) :=
      aRaw.castLength hRankEq
    have hClassic : Lattice.IsClassicIntegral X.form X.lattice :=
      hXClassic
    have hBound := signedPrefix_upper_of_all
      U hU pairs X a (by omega) hXClassic hAll
    have hTests := literalLemma42Tests_of_all U hU pairs X a (by omega) hAll
    have hJ1 := a.he2022ClassicLemma42_j1Prime_of_publishedTests
      pairs (by omega) hClassic hTests
    have hPrevious : a.order ⟨2 * pairs + 1, by omega⟩ = 0 := by
      exact hJ1.1 ⟨2 * pairs + 1, by omega⟩
    have hCases := a.he2022ClassicLemma44 (j := 2 * pairs + 4)
      (by omega) (by omega) hPrevious (by
        simpa only [show (2 * pairs + 4) / 2 = pairs + 2 by omega,
          show 2 * pairs + 4 - 1 = 2 * pairs + 3 by omega]
          using hBound)
    let c0 : Kˣ := ((-1 : Kˣ) ^ (pairs + 2)) *
      a.prefixProduct (2 * pairs + 4)
    have hDefectEq :
        a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
            (2 * pairs + 4) =
          BONG.GoodBONG.defectOrder (K := K) c0 := by
      dsimp only [c0]
      unfold BONG.GoodBONG.truncatedPrefixDefect
      rw [a.prefixAlphaCap_zero, a.prefixAlphaCap_last]
      simp [BONG.GoodBONG.prefixProduct]
    have hDefectCases :
        BONG.GoodBONG.defectOrder (K := K) c0 = 0 ∨
          BONG.GoodBONG.defectOrder (K := K) c0 = 1 := by
      simpa only [show (2 * pairs + 4) / 2 = pairs + 2 by omega,
        hDefectEq] using hCases.2
    have hPrefixZero :
        a.orderSequence.prefixSum (2 * pairs + 3) = 0 := by
      unfold BeliOrderSequence.prefixSum
      apply Finset.sum_eq_zero
      intro i hi
      rw [BeliOrderSequence.entryOrZero_of_lt _ (by
        have hi' := Finset.mem_range.mp hi
        omega)]
      exact hJ1.1 ⟨i, by
        have hi' := Finset.mem_range.mp hi
        omega⟩
    have hPrefixFull :
        a.orderSequence.prefixSum (2 * pairs + 4) =
          a.order ⟨2 * pairs + 3, by omega⟩ := by
      calc
        a.orderSequence.prefixSum (2 * pairs + 4) =
            a.orderSequence.prefixSum ((2 * pairs + 3) + 1) := by
              congr 1
        _ = a.orderSequence.prefixSum (2 * pairs + 3) +
            a.orderSequence.entryOrZero (2 * pairs + 3) :=
              a.orderSequence.prefixSum_succ (2 * pairs + 3)
        _ = a.order ⟨2 * pairs + 3, by omega⟩ := by
              rw [hPrefixZero,
                BeliOrderSequence.entryOrZero_of_lt _ (by omega)]
              simp
    have hOrdOne : ordUnit K (1 : Kˣ) = 0 := by
      apply WithTop.coe_injective
      rw [coe_ordUnit]
      simp
    have hOrderC0 : ordUnit K c0 =
        a.order ⟨2 * pairs + 3, by omega⟩ := by
      dsimp only [c0]
      rw [ordUnit_mul, ordUnit_pow, ordUnit_neg, hOrdOne,
        a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
          (2 * pairs + 4) (by omega),
        hPrefixFull]
      simp
    have hOrderCases : ordUnit K c0 = 0 ∨ ordUnit K c0 = 1 := by
      simpa only [show 2 * pairs + 4 - 1 = 2 * pairs + 3 by omega,
        hOrderC0] using hCases.1
    obtain ⟨c, s, second, hPair, hcNonnegative, hfactor,
        hFirst, hSecond⟩ :=
      exists_represented_publishedEven_pair_of_low_signed_parameter
        U hU pairs X hAll c0 hOrderCases hDefectCases
    exact (heClassicEvenPair_not_both_goodBONG_of_signedPrefix_factor
      (K := K) pairs a c s second hPair hcNonnegative
      (by simpa only [c0] using hfactor) hFirst hSecond).elim

/-- Lemma 7.4, sufficiency in even rank.  Actual representation of every
entry of the published finite table yields ambient universality by Lemma 7.3
and all three intrinsic BONG conditions of Theorem 4.1. -/
theorem all_publishedEven_implies_classicUniversal
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hXClassic : X.IsClassicIntegral)
    (hAll : forall i : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model
          (K := K) U hU pairs i)) :
    X.IsClassicNUniversal (2 * pairs + 2) := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : Module.Finite K X.Carrier := X.lattice.moduleFinite
  have hRankLower : 2 * pairs + 4 <= Module.finrank K X.Carrier := by
    have h := all_publishedEven_implies_rank_add_two_le
      (K := K) U hU pairs X hAll
    change 2 * pairs + 4 <= Module.finrank K X.Carrier at h
    exact h
  obtain ⟨aRaw⟩ := exists_good_bong X.form X.lattice
  let m : Nat := Module.finrank K X.Carrier - 4
  have hRankEq : Module.finrank K X.Carrier = m + 4 := by
    dsimp only [m]
    omega
  let a : BONG.GoodBONG X.form X.lattice (m + 4) :=
    aRaw.castLength hRankEq
  have hSource : 2 * pairs + 4 <= m + 4 := by
    rw [← hRankEq]
    exact hRankLower
  have hAmbientX : X.IsAmbientlyNUniversal (2 * pairs + 2) :=
    all_publishedEven_implies_ambientlyUniversal
    (K := K) U hU pairs X hXClassic hAll
  have hTests := literalLemma42Tests_of_all
    U hU pairs X a hSource hAll
  have hClassic : Lattice.IsClassicIntegral X.form X.lattice := hXClassic
  have hJ1Prime := a.he2022ClassicLemma42_j1Prime_of_publishedTests
    pairs hSource hClassic hTests
  have hJ2 := heClassicEvenJ2_of_all_published
    U hU pairs X a hSource hXClassic hAmbientX hAll
  have hJ3 := heClassicEvenJ3_of_all_published
    U hU pairs X a hSource hXClassic hAmbientX hAll
  change Lattice.IsClassicNUniversal.{u, u, u}
    X.form X.lattice (2 * pairs + 2)
  exact (a.he2022ClassicTheorem41 hSource).2
    ⟨hClassic, hAmbientX, ⟨hJ1Prime.1, hJ2, hJ3⟩⟩

/-- He (2024), Lemma 7.4, even-rank branch, for the literal published
testing family and an arbitrary complete unit square-class representative
system. -/
theorem he2022ClassicLemma74_even
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hXClassic : X.IsClassicIntegral) :
    X.IsClassicNUniversal (2 * pairs + 2) ↔
      forall i : HeClassicPublishedEvenTestingIndex
          (K := K) U (ramificationIndex K),
        X.Represents
          (HeClassicPublishedEvenTestingIndex.model
            (K := K) U hU pairs i) := by
  constructor
  · exact classicUniversal_implies_all_publishedEven U hU pairs X
  · exact all_publishedEven_implies_classicUniversal
      U hU pairs X hXClassic

end Lattice.QuadraticLatticeModel

end Bong
