/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalCases
import Bong.Bong.Beli2019Lemma37UniversalModels

/-!
# Ambient universality for the universal-lattice theorem

This file formalizes Beli's Lemma 2.4 and the linear-algebraic part of the
last paragraph of the proof of Theorem 2.1.  In particular, an isotropic
diagonal prefix gives representations of all one-dimensional spaces, and
rank at least four gives the same conclusion unconditionally.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace QuadraticSpace

/-- A quadratic space is universal when it represents every nonzero line. -/
def IsLineUniversal (q : QuadraticSpace K V) : Prop :=
  ∀ a : Kˣ, q.Represents (rescaleUnit a (line K))

/-- The two line models used in the older and newer parts of the library are
canonically isometric. -/
def rescaleLineScaledLineIsometry (a : Kˣ) :
    Isometry (rescaleUnit a (line K)) (scaledLine a) where
  toLinearEquiv := LinearEquiv.refl K K
  map_bilin := by
    intro x y
    simp only [LinearEquiv.refl_apply, scaledLine_bilin_apply,
      rescaleUnit_bilin_apply, line_bilin_apply]
    ring

theorem represents_rescaleLine_iff_scaledLine
    (q : QuadraticSpace K V) (a : Kˣ) :
    q.Represents (rescaleUnit a (line K)) ↔ q.Represents (scaledLine a) := by
  constructor
  · intro h
    exact h.trans ⟨(rescaleLineScaledLineIsometry a).symm.toRepresentation⟩
  · intro h
    exact h.trans ⟨(rescaleLineScaledLineIsometry a).toRepresentation⟩

end QuadraticSpace

namespace BONG

/-- An isotropic full BONG diagonalization represents every nonzero line. -/
theorem represents_scaledLine_of_diagonalIsotropic {n : Nat}
    (a : BONG V q L n) (hiso : DiagonalIsotropic a.value) (b : Kˣ) :
    q.Represents (QuadraticSpace.scaledLine b) := by
  obtain ⟨coordinates, hcoordinates⟩ :=
    diagonal_exists_value_of_isotropic a.value a.value_ne_zero hiso b
  let x : V := a.basis.equivFun.symm coordinates
  have hqx : q.quadratic x = (b : K) := by
    dsimp only [x]
    rw [← a.diagonalQuadratic_value_eq]
    exact hcoordinates
  have hxne : x ≠ 0 := by
    intro hx
    have hbzero : (b : K) = 0 := by
      rw [← hqx, hx]
      exact q.quadratic_zero
    exact Units.ne_zero b hbzero
  refine ⟨{
    toLinearMap :=
      { toFun := fun c : K ↦ c • x
        map_add' := fun c d ↦ add_smul c d x
        map_smul' := fun c d ↦ by simp [mul_smul] }
    injective := ?_
    map_bilin := ?_ }⟩
  · intro c d hcd
    change c • x = d • x at hcd
    have hzero : (c - d) • x = 0 := by
      rw [sub_smul, hcd, sub_self]
    have : c - d = 0 := by
      simpa [hxne] using hzero
    exact sub_eq_zero.mp this
  · intro c d
    simp only [LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right,
      QuadraticSpace.scaledLine_bilin_apply]
    change d * (c * q.quadratic x) = (b : K) * c * d
    rw [hqx]
    ring

theorem isLineUniversal_of_diagonalIsotropic {n : Nat}
    (a : BONG V q L n) (hiso : DiagonalIsotropic a.value) :
    q.IsLineUniversal := by
  intro b
  rw [QuadraticSpace.represents_rescaleLine_iff_scaledLine]
  exact a.represents_scaledLine_of_diagonalIsotropic hiso b

end BONG

namespace BONG.GoodBONG

/-- Isotropy of any coefficient prefix propagates to the complete BONG. -/
theorem diagonalIsotropic_of_prefix {n k : Nat}
    (a : GoodBONG q L n) (hk : k ≤ n)
    (hiso : DiagonalIsotropic (a.prefixValues k hk)) :
    DiagonalIsotropic a.value := by
  have hrep : DiagonalRepresents (a.prefixValues k hk) a.value := by
    unfold prefixValues
    exact DiagonalRepresents.prefixOfLE a.value hk
  exact hrep.isotropic_of hiso

theorem isLineUniversal_of_firstTwoIsotropic {tail : Nat}
    (a : GoodBONG q L (tail + 2))
    (hiso : a.UniversalFirstTwoIsotropic) : q.IsLineUniversal := by
  apply a.toBONG.isLineUniversal_of_diagonalIsotropic
  exact a.diagonalIsotropic_of_prefix (k := 2) (by omega) hiso

theorem isLineUniversal_of_firstThreeIsotropic {tail : Nat}
    (a : GoodBONG q L (tail + 2)) (hthree : 0 < tail)
    (hiso : a.UniversalFirstThreeIsotropic hthree) : q.IsLineUniversal := by
  apply a.toBONG.isLineUniversal_of_diagonalIsotropic
  exact a.diagonalIsotropic_of_prefix (k := 3) (by omega) hiso

/-- The unconditional rank-at-least-four branch in the proof of Theorem
2.1. -/
theorem isLineUniversal_of_two_le_tail {tail : Nat}
    (a : GoodBONG q L (tail + 2)) (hfour : 2 ≤ tail) :
    q.IsLineUniversal := by
  letI : FiniteDimensional K V :=
    a.toBONG.basis.finiteDimensional_of_finite
  intro b
  rw [QuadraticSpace.represents_rescaleLine_iff_scaledLine]
  apply q.represents_scaledLine_of_four_le_finrank b
  rw [← a.toBONG.length_eq_finrank]
  omega

end BONG.GoodBONG

/-- Beli, Lemma 2.4, in the exact line-representation formulation used by
Lemma 2.3. -/
theorem beliUniversalLemma24 (q : QuadraticSpace K V) :
    (∀ b : Kˣ, ordUnit K b = 0 ∨ ordUnit K b = 1 →
      q.Represents (QuadraticSpace.rescaleUnit b (QuadraticSpace.line K))) ↔
      q.IsLineUniversal := by
  constructor
  · intro h b
    obtain ⟨c, s, hc, hfactor⟩ :=
      exists_order_zero_or_one_mul_square_any b
    rcases h c hc with ⟨f⟩
    let scale : K →ₗ[K] K := LinearMap.mulLeft K (s : K)
    refine ⟨{
      toLinearMap := f.toLinearMap.comp scale
      injective := f.injective.comp ?_
      map_bilin := ?_ }⟩
    · intro x y hxy
      change scale x = scale y at hxy
      change (s : K) * x = (s : K) * y at hxy
      exact mul_left_cancel₀ (Units.ne_zero s) hxy
    · intro x y
      simp only [LinearMap.comp_apply, scale, LinearMap.mulLeft_apply,
        QuadraticSpace.rescaleUnit_bilin_apply, QuadraticSpace.line_bilin_apply]
      rw [f.map_bilin]
      simp only [QuadraticSpace.rescaleUnit_bilin_apply,
        QuadraticSpace.line_bilin_apply]
      have hb : (b : K) = (c : K) * (s : K) ^ 2 := by
        exact congrArg Units.val hfactor
      rw [hb]
      ring
  · intro h b _
    exact h b

end Bong
