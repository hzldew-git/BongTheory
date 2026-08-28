/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019IntegralSquareShift
import Bong.Bong.BinaryValueIsometry
import Bong.Bong.RepresentationDual
import Bong.Bong.BeliLemmas48To410
import Bong.Bong.Beli2019NestedOrder
import Bong.Lattice.ScaledHyperbolicMaximal

/-!
# Beli (2019), Lemma 9.7

Part (i) is the binary integral-square argument from the paper.  First the
second BONG vector of `M` is scaled to construct an intermediate sublattice
`K ≤ M`.  The first vector is then adjusted after reverse duality, producing
`K♯` as a lattice represented by `N♯`.  Representation duality and
transitivity give `N → M`.
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
  {M : Lattice K V} {N : Lattice K W}

/-- Comparing first good-BONG orders compares the norm ideals in the reverse
inclusion order. -/
private theorem normIdeal_le_of_firstOrder_le
    (a : GoodBONG q M 2) (b : GoodBONG r N 2)
    (horder : a.order 0 ≤ b.order 0) :
    Lattice.normIdeal r N ≤ Lattice.normIdeal q M := by
  rw [b.toBONG.head_isNormGenerator.normIdeal_eq,
    a.toBONG.head_isNormGenerator.normIdeal_eq]
  apply (Lattice.principalIdeal_le_iff_ord_ge
    b.toBONG.head_isAnisotropic a.toBONG.head_isAnisotropic).2
  rw [← a.toBONG.value_zero_eq_quadratic_head,
    ← b.toBONG.value_zero_eq_quadratic_head,
    ← a.toBONG.coe_order (0 : Fin 2),
    ← b.toBONG.coe_order (0 : Fin 2)]
  exact_mod_cast horder

/-- Geometric core of Beli (2019), Lemma 9.7(i).  It only needs the two
integral square shifts displayed in the proof; the order, parity, and
normalized-value formulation is recovered below. -/
theorem beli2019Lemma97_i_of_integralSquareShifts
    [structuralV : BONGStructuralLaws.{u, v} K]
    [structuralW : BONGStructuralLaws.{u, w} K]
    (a : GoodBONG q M 2) (b : GoodBONG r N 2)
    (s₀ s₁ : Kˣ) (hs₀ : (s₀ : K) ∈ IntegerRing K)
    (hs₁ : (s₁ : K) ∈ IntegerRing K)
    (hshift₀ : a.valueUnit 0 * s₀ ^ 2 = b.valueUnit 0)
    (hshift₁ : a.valueUnit 1 * s₁ ^ 2 = b.valueUnit 1) :
    Lattice.Represents q r M N := by
  letI : FiniteDimensional K V :=
    a.toBONG.basis.finiteDimensional_of_finite
  letI : FiniteDimensional K W :=
    b.toBONG.basis.finiteDimensional_of_finite
  change a.valueUnit 0 * s₀ ^ 2 = b.valueUnit 0 at hshift₀
  change a.valueUnit 1 * s₁ ^ 2 = b.valueUnit 1 at hshift₁

  let K₀ : Lattice K V :=
    a.toBONG.binaryIntegralSquareSubLattice s₁ hs₁
  let cBONG : BONG V q K₀ 2 :=
    a.toBONG.binaryIntegralSquareSubBONG s₁ hs₁
  let c : GoodBONG q K₀ 2 :=
    ⟨cBONG, cBONG.isGood_binary⟩

  have hcZero : c.valueUnit 0 = a.valueUnit 0 := by
    apply Units.ext
    change cBONG.value 0 = a.value 0
    exact a.toBONG.binaryIntegralSquareSubBONG_value_zero s₁ hs₁
  have hcOne : c.valueUnit 1 = b.valueUnit 1 := by
    apply Units.ext
    change cBONG.value 1 = b.toBONG.value 1
    rw [a.toBONG.binaryIntegralSquareSubBONG_value_one]
    have hcoe := congrArg (fun z : Kˣ => (z : K)) hshift₁
    change (a.toBONG.value 1) * (s₁ : K) ^ 2 =
      b.toBONG.value 1 at hcoe
    simpa [mul_comm] using hcoe
  have hK₀_le_M : K₀ ≤ M :=
    a.toBONG.binaryIntegralSquareSubLattice_le s₁ hs₁
  have hM_represents_K₀ : Lattice.Represents q q M K₀ :=
    Lattice.represents_of_le q hK₀_le_M

  have hcReverse := by
    letI : BONGStructuralLaws.{u, v} K := structuralV
    exact c.exists_reverseDual_with_values
  have hbReverse := by
    letI : BONGStructuralLaws.{u, w} K := structuralW
    exact b.exists_reverseDual_with_values
  rcases hcReverse with
    ⟨cDual, _hcDualVectors, hcDualValues, _hcDualOrders⟩
  rcases hbReverse with
    ⟨bDual, _hbDualVectors, hbDualValues, _hbDualOrders⟩

  let D : Lattice K W :=
    bDual.toBONG.binaryIntegralSquareSubLattice s₀ hs₀
  let dBONG : BONG W r D 2 :=
    bDual.toBONG.binaryIntegralSquareSubBONG s₀ hs₀
  let d : GoodBONG r D 2 :=
    ⟨dBONG, dBONG.isGood_binary⟩

  have hinverseShift :
      (b.valueUnit 0)⁻¹ * s₀ ^ 2 = (a.valueUnit 0)⁻¹ := by
    calc
      (b.valueUnit 0)⁻¹ * s₀ ^ 2 =
          (a.valueUnit 0 * s₀ ^ 2)⁻¹ * s₀ ^ 2 := by
        rw [hshift₀]
      _ = (a.valueUnit 0)⁻¹ := by
        simp [mul_inv_rev, mul_comm]

  have hdZero : d.valueUnit 0 = cDual.valueUnit 0 := by
    apply Units.ext
    change dBONG.value 0 = cDual.value 0
    rw [bDual.toBONG.binaryIntegralSquareSubBONG_value_zero]
    change bDual.value 0 = cDual.value 0
    rw [hbDualValues, hcDualValues]
    have hcoe := congrArg (fun z : Kˣ => (z : K)) hcOne
    change c.toBONG.value 1 = b.toBONG.value 1 at hcoe
    simpa using hcoe.symm
  have hdOne : d.valueUnit 1 = cDual.valueUnit 1 := by
    apply Units.ext
    change dBONG.value 1 = cDual.value 1
    rw [bDual.toBONG.binaryIntegralSquareSubBONG_value_one]
    change (s₀ : K) ^ 2 * bDual.value 1 = cDual.value 1
    rw [hbDualValues, hcDualValues]
    have hrev : Fin.rev (1 : Fin 2) = (0 : Fin 2) := by decide
    rw [hrev]
    change (s₀ : K) ^ 2 * (b.toBONG.value 0)⁻¹ =
      (c.toBONG.value 0)⁻¹
    have hshiftCoe := congrArg (fun z : Kˣ => (z : K)) hinverseShift
    change (b.toBONG.value 0)⁻¹ * (s₀ : K) ^ 2 =
      (a.toBONG.value 0)⁻¹ at hshiftCoe
    have hcZeroCoe := congrArg (fun z : Kˣ => (z : K)) hcZero
    change c.toBONG.value 0 = a.toBONG.value 0 at hcZeroCoe
    rw [hcZeroCoe]
    simpa [mul_comm] using hshiftCoe

  have hD_le_NDual : D ≤ Lattice.dualLattice r N :=
    bDual.toBONG.binaryIntegralSquareSubLattice_le s₀ hs₀
  have hNDual_represents_D :
      Lattice.Represents r r (Lattice.dualLattice r N) D :=
    Lattice.represents_of_le r hD_le_NDual
  have hD_isometric_KDual :
      Lattice.IsIsometric r q D (Lattice.dualLattice q K₀) :=
    d.toBONG.binary_isIsometric_of_valueUnit_eq cDual.toBONG hdZero hdOne
  have hD_represents_KDual :
      Lattice.Represents r q D (Lattice.dualLattice q K₀) := by
    rcases hD_isometric_KDual with ⟨f⟩
    exact ⟨f.symm.toRepresentation⟩
  have hNDual_represents_KDual :
      Lattice.Represents r q (Lattice.dualLattice r N)
        (Lattice.dualLattice q K₀) :=
    hNDual_represents_D.trans hD_represents_KDual

  have hfinrank : Module.finrank K V = Module.finrank K W :=
    a.toBONG.length_eq_finrank.symm.trans b.toBONG.length_eq_finrank
  have hK₀_represents_N :=
    hNDual_represents_KDual.dual_of_finrank_eq hfinrank
  have hK₀_represents_N' : Lattice.Represents q r K₀ N := by
    simpa using hK₀_represents_N
  exact hM_represents_K₀.trans hK₀_represents_N'

/-- Beli (2019), Lemma 9.7(i).  The hypotheses say that
`M ≈ [π^R₁ ε₁, π^R₂ ε₂]` and
`N ≈ [π^S₁ ε₁, π^S₂ ε₂]`, with `Rᵢ ≤ Sᵢ` and equal parity.

The conclusion follows from concrete sublattice constructions and duality;
the main representation theorem is not used. -/
theorem beli2019Lemma97_i
    [structuralV : BONGStructuralLaws.{u, v} K]
    [structuralW : BONGStructuralLaws.{u, w} K]
    (a : GoodBONG q M 2) (b : GoodBONG r N 2)
    (horders : ∀ i, a.order i ≤ b.order i)
    (hparity : ∀ i, Int.ModEq 2 (b.order i) (a.order i))
    (hnormalized : ∀ i,
      a.toBONG.normalizedValue i = b.toBONG.normalizedValue i) :
    Lattice.Represents q r M N := by
  rcases a.toBONG.exists_integralSquareShift_of_normalizedValue_eq
      b.toBONG (0 : Fin 2) (horders 0) (hparity 0) (hnormalized 0) with
    ⟨s₀, hs₀, hshift₀⟩
  rcases a.toBONG.exists_integralSquareShift_of_normalizedValue_eq
      b.toBONG (1 : Fin 2) (horders 1) (hparity 1) (hnormalized 1) with
    ⟨s₁, hs₁, hshift₁⟩
  exact beli2019Lemma97_i_of_integralSquareShifts
    (structuralV := structuralV) (structuralW := structuralW)
    a b s₀ s₁ hs₀ hs₁ hshift₀ hshift₁

/-- Beli (2019), Lemma 9.7(ii).  Under the common order hypotheses of the
lemma, ambient isometry and a scaled-hyperbolic source or target reduce the
representation to O'Meara's norm-maximality theorem. -/
theorem beli2019Lemma97_ii
    [structuralV : BONGStructuralLaws.{u, v} K]
    [structuralW : BONGStructuralLaws.{u, w} K]
    [maximalVW : ScaledHyperbolicMaximalLaws.{u, v, w} K]
    [maximalWV : ScaledHyperbolicMaximalLaws.{u, w, v} K]
    (a : GoodBONG q M 2) (b : GoodBONG r N 2)
    (horders : ∀ i, a.order i ≤ b.order i)
    (ambient : q.IsIsometric r)
    (hhyperbolic :
      Lattice.IsScaledHyperbolicLattice q M ∨
        Lattice.IsScaledHyperbolicLattice r N) :
    Lattice.Represents q r M N := by
  letI : FiniteDimensional K V :=
    a.toBONG.basis.finiteDimensional_of_finite
  letI : FiniteDimensional K W :=
    b.toBONG.basis.finiteDimensional_of_finite
  rcases hhyperbolic with hM | hN
  · letI : ScaledHyperbolicMaximalLaws.{u, v, w} K := maximalVW
    exact (ScaledHyperbolicMaximalLaws.normMaximal (K := K) hM) ambient
      (normIdeal_le_of_firstOrder_le a b (horders 0))
  · have hcReverse := by
      letI : BONGStructuralLaws.{u, v} K := structuralV
      exact a.exists_reverseDual_with_values
    have hbReverse := by
      letI : BONGStructuralLaws.{u, w} K := structuralW
      exact b.exists_reverseDual_with_values
    rcases hcReverse with
      ⟨aDual, _haDualVectors, _haDualValues, haDualOrders⟩
    rcases hbReverse with
      ⟨bDual, _hbDualVectors, _hbDualValues, hbDualOrders⟩
    have hdualFirstOrder : bDual.order 0 ≤ aDual.order 0 := by
      rw [hbDualOrders, haDualOrders]
      have hrev : Fin.rev (0 : Fin 2) = (1 : Fin 2) := by decide
      rw [hrev]
      exact neg_le_neg (horders 1)
    have hdualNorm :
        Lattice.normIdeal q (Lattice.dualLattice q M) ≤
          Lattice.normIdeal r (Lattice.dualLattice r N) :=
      normIdeal_le_of_firstOrder_le bDual aDual hdualFirstOrder
    have ambientSymm : r.IsIsometric q := by
      rcases ambient with ⟨f⟩
      exact ⟨f.symm⟩
    have hdualRepresentation :
        Lattice.Represents r q (Lattice.dualLattice r N)
          (Lattice.dualLattice q M) := by
      letI : ScaledHyperbolicMaximalLaws.{u, w, v} K := maximalWV
      exact (ScaledHyperbolicMaximalLaws.dualNormMaximal
        (K := K) hN) ambientSymm hdualNorm
    have hfinrank : Module.finrank K V = Module.finrank K W :=
      a.toBONG.length_eq_finrank.symm.trans b.toBONG.length_eq_finrank
    simpa using hdualRepresentation.dual_of_finrank_eq hfinrank

end BONG.GoodBONG

end Bong
