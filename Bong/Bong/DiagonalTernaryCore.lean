/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Classification
import Bong.Bong.Basis
import Bong.Bong.DiagonalRepresentationParity
import Bong.Dyadic.HilbertSymbol

/-!
# Elementary diagonal and ternary Hilbert-symbol lemmas

This module contains the paper-independent linear-algebra and Hilbert-symbol
facts used by several later parts of Beli's arguments.  Keeping them below the
2006/2009/2019 theorem modules prevents the basic diagonal theory from
acquiring a circular dependency on those theorems.
-/

namespace Bong

open Dyadic

universe u v

/-- A diagonal quadratic form has a nonzero isotropic vector. -/
def DiagonalIsotropic {K : Type u} [Field K] {n : Nat}
    (a : Fin n → K) : Prop :=
  ∃ x : Fin n → K, x ≠ 0 ∧ diagonalQuadratic a x = 0

/-- A diagonal quadratic form has no nonzero isotropic vector. -/
def DiagonalAnisotropic {K : Type u} [Field K] {n : Nat}
    (a : Fin n → K) : Prop :=
  ∀ x : Fin n → K, diagonalQuadratic a x = 0 → x = 0

namespace DiagonalRepresents

variable {K : Type u} [Field K] {m n : Nat}
  {source : Fin m → K} {target : Fin n → K}

/-- A diagonal representation sends a nonzero isotropic vector to a nonzero
isotropic vector. -/
theorem isotropic_of (h : DiagonalRepresents source target)
    (hsource : DiagonalIsotropic source) : DiagonalIsotropic target := by
  rcases h with ⟨f, hf, hquadratic⟩
  rcases hsource with ⟨x, hx, hzero⟩
  refine ⟨f x, ?_, ?_⟩
  · intro hfx
    apply hx
    apply hf
    simpa using hfx
  · rw [hquadratic, hzero]

/-- An anisotropic target forces every represented diagonal form to be
anisotropic. -/
theorem anisotropic_of (h : DiagonalRepresents source target)
    (htarget : DiagonalAnisotropic target) : DiagonalAnisotropic source := by
  rcases h with ⟨f, hf, hquadratic⟩
  intro x hzero
  apply hf
  have hfx : f x = 0 := htarget (f x) (by rw [hquadratic, hzero])
  simpa using hfx

end DiagonalRepresents

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The diagonal polynomial of the values of a BONG is the ambient
quadratic form written in its basis coordinates. -/
theorem diagonalQuadratic_value_eq
    (a : BONG V q L n) (x : Fin n → K) :
    diagonalQuadratic a.value x =
      q.quadratic (a.basis.equivFun.symm x) := by
  have h := q.bilin.dotProduct_toMatrix_mulVec a.basis x x
  change dotProduct x (a.gramMatrix.mulVec x) =
    q.quadratic (a.basis.equivFun.symm x) at h
  rw [a.gramMatrix_eq_diagonal] at h
  simpa [diagonalQuadratic, dotProduct, Matrix.mulVec,
    Matrix.diagonal_apply, pow_two, mul_assoc, mul_left_comm, mul_comm]
    using h

/-- Coordinate change between two BONG bases of the same quadratic space. -/
noncomputable def coordinateChange
    (a : BONG V q L n) (b : BONG V q M n) :
    (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  a.basis.equivFun.symm.trans b.basis.equivFun

/-- The full diagonal presentations associated with two BONG bases of one
quadratic space represent one another. -/
theorem diagonalRepresents_values
    (a : BONG V q L n) (b : BONG V q M n) :
    DiagonalRepresents a.value b.value := by
  refine ⟨(a.coordinateChange b).toLinearMap,
    (a.coordinateChange b).injective, ?_⟩
  intro x
  rw [b.diagonalQuadratic_value_eq, a.diagonalQuadratic_value_eq]
  simp [coordinateChange]

end BONG

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K]

/-- Orthogonally append the same one-dimensional coefficient to a diagonal
representation. -/
theorem diagonalRepresents_snoc {m n : Nat}
    {source : Fin m → K} {target : Fin n → K}
    (h : DiagonalRepresents source target) (d : K) :
    DiagonalRepresents (Fin.snoc source d) (Fin.snoc target d) := by
  rcases h with ⟨f, hf, hquadratic⟩
  let F : (Fin (m + 1) → K) →ₗ[K] (Fin (n + 1) → K) :=
    { toFun := fun x ↦ Fin.snoc (f (Fin.init x)) (x (Fin.last m))
      map_add' := by
        intro x y
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · simp only [Fin.snoc_castSucc, Pi.add_apply]
          change f (Fin.init (x + y)) j = f (Fin.init x) j + f (Fin.init y) j
          rw [show Fin.init (x + y) = Fin.init x + Fin.init y by rfl,
            map_add]
          rfl
      map_smul' := by
        intro c x
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · simp only [Fin.snoc_castSucc, Pi.smul_apply]
          change f (Fin.init (c • x)) j = c * f (Fin.init x) j
          rw [show Fin.init (c • x) = c • Fin.init x by rfl,
            map_smul]
          rfl }
  refine ⟨F, ?_, ?_⟩
  · intro x y hxy
    have hlast : x (Fin.last m) = y (Fin.last m) := by
      have h := congrFun hxy (Fin.last n)
      simpa [F] using h
    have hinit : Fin.init x = Fin.init y := by
      apply hf
      funext i
      have h := congrFun hxy i.castSucc
      simpa [F] using h
    rw [← Fin.snoc_init_self x, ← Fin.snoc_init_self y, hinit, hlast]
  · intro x
    unfold diagonalQuadratic
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [F, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_last,
      Fin.snoc_castSucc]
    simpa [diagonalQuadratic, Fin.init] using hquadratic (Fin.init x)

/-- Determinant of a diagonal list after appending one coefficient. -/
theorem diagonalUnitDeterminant_snoc {n : Nat}
    (a : Fin n → Kˣ) (d : Kˣ) :
    diagonalUnitDeterminant (Fin.snoc a d) =
      diagonalUnitDeterminant a * d := by
  unfold diagonalUnitDeterminant
  rw [Fin.prod_univ_castSucc]
  simp

/-- Deleting the appended coefficient recovers the original list. -/
theorem diagonalUnitPrefix_snoc {n : Nat}
    (a : Fin n → Kˣ) (d : Kˣ) :
    diagonalUnitPrefix (Fin.snoc a d) = a := by
  funext i
  simp [diagonalUnitPrefix]

/-- If the Hilbert symbol of the two adjacent products of a diagonal ternary
form is one, then that ternary form has a nonzero isotropic vector. -/
theorem diagonalTernary_isotropic_of_adjacent_hilbert_one
    (a₀ a₁ a₂ : Kˣ)
    (h : hilbertSymbol K (-(a₀ * a₁)) (-(a₁ * a₂)) = 1) :
    ∃ z : Fin 3 → K,
      z ≠ 0 ∧
        diagonalQuadratic
          (fun i => ![(a₀ : K), (a₁ : K), (a₂ : K)] i) z = 0 := by
  have hnorm := (hilbertSymbol_eq_one_iff K _ _).mp h
  rcases hnorm with ⟨x, y, hxy⟩
  let z : Fin 3 → K := ![y, x / (a₁ : K), 1]
  refine ⟨z, ?_, ?_⟩
  · intro hz
    have htwo := congrFun hz (2 : Fin 3)
    simp [z] at htwo
  · have hscaled :
        (a₀ : K) * y ^ 2 + x ^ 2 / (a₁ : K) + (a₂ : K) = 0 := by
      change x ^ 2 - (-(a₀ * a₁) : Kˣ) * y ^ 2 =
        (-(a₁ * a₂) : Kˣ) at hxy
      simp only [Units.val_neg, Units.val_mul] at hxy
      field_simp [Units.ne_zero a₁]
      linear_combination hxy
    simp only [z, diagonalQuadratic, Fin.sum_univ_three]
    simp
    calc
      (a₀ : K) * y ^ 2 + (a₁ : K) * (x / (a₁ : K)) ^ 2 +
          (a₂ : K) =
        (a₀ : K) * y ^ 2 + x ^ 2 / (a₁ : K) + (a₂ : K) := by
          field_simp [Units.ne_zero a₁]
      _ = 0 := hscaled

/-- A nonzero isotropic vector for a diagonal ternary form forces the Hilbert
symbol of its two adjacent products to be one. -/
theorem hilbertSymbol_eq_one_of_diagonalTernary_isotropic
    (a₀ a₁ a₂ : Kˣ) (z : Fin 3 → K)
    (hz : z ≠ 0)
    (hquadratic :
      diagonalQuadratic
        (fun i => ![(a₀ : K), (a₁ : K), (a₂ : K)] i) z = 0) :
    hilbertSymbol K (-(a₀ * a₁)) (-(a₁ * a₂)) = 1 := by
  apply (hilbertSymbol_eq_one_iff K _ _).2
  simp only [diagonalQuadratic, Nat.succ_eq_add_one, Nat.reduceAdd,
    Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val] at hquadratic
  by_cases hz₂ : z 2 = 0
  · have hquadratic' :
        (a₀ : K) * z 0 ^ 2 + (a₁ : K) * z 1 ^ 2 = 0 := by
      simpa [hz₂] using hquadratic
    have hz₁ : z 1 ≠ 0 := by
      intro hz₁
      have hz₀ : z 0 = 0 := by
        have hzero : (a₀ : K) * z 0 ^ 2 = 0 := by
          simpa [hz₁] using hquadratic'
        exact eq_zero_of_pow_eq_zero (mul_eq_zero.mp hzero |>.resolve_left
          (Units.ne_zero a₀))
      apply hz
      funext i
      fin_cases i <;> simp [hz₀, hz₁, hz₂]
    have hz₀ : z 0 ≠ 0 := by
      intro hz₀
      have hzero : (a₁ : K) * z 1 ^ 2 = 0 := by
        simpa [hz₀, hz₂] using hquadratic
      exact hz₁ (eq_zero_of_pow_eq_zero (mul_eq_zero.mp hzero |>.resolve_left
        (Units.ne_zero a₁)))
    let r : K := (a₀ : K) * z 0 / z 1
    have hnumerator :
        (a₀ : K) ^ 2 * z 0 ^ 2 =
          -((a₀ : K) * (a₁ : K)) * z 1 ^ 2 := by
      linear_combination (a₀ : K) * hquadratic'
    have hr : r ^ 2 = (-(a₀ * a₁) : Kˣ) := by
      change r ^ 2 = -((a₀ : K) * (a₁ : K))
      dsimp only [r]
      calc
        (((a₀ : K) * z 0 / z 1) ^ 2) =
            ((a₀ : K) ^ 2 * z 0 ^ 2) / z 1 ^ 2 := by ring
        _ = (-((a₀ : K) * (a₁ : K)) * z 1 ^ 2) /
            z 1 ^ 2 := by rw [hnumerator]
        _ = -((a₀ : K) * (a₁ : K)) := by field_simp [hz₁]
    have hrne : r ≠ 0 := by
      intro hrzero
      rw [hrzero] at hr
      simp at hr
    let target : K := (-(a₁ * a₂) : Kˣ)
    refine ⟨(target + 1) / 2, (target - 1) / (2 * r), ?_⟩
    change ((target + 1) / 2) ^ 2 -
        ((-(a₀ * a₁) : Kˣ) : K) *
          ((target - 1) / (2 * r)) ^ 2 = target
    rw [← hr]
    field_simp [hrne]
    ring
  · have hnumerator :
        ((a₁ : K) * z 1) ^ 2 +
            (a₀ : K) * (a₁ : K) * z 0 ^ 2 =
          -((a₁ : K) * (a₂ : K)) * z 2 ^ 2 := by
      linear_combination (a₁ : K) * hquadratic
    refine ⟨(a₁ : K) * z 1 / z 2, z 0 / z 2, ?_⟩
    simp only [Units.val_neg, Units.val_mul]
    calc
      ((a₁ : K) * z 1 / z 2) ^ 2 -
            -((a₀ : K) * (a₁ : K)) * (z 0 / z 2) ^ 2 =
          (((a₁ : K) * z 1) ^ 2 +
            (a₀ : K) * (a₁ : K) * z 0 ^ 2) / z 2 ^ 2 := by ring
      _ = (-((a₁ : K) * (a₂ : K)) * z 2 ^ 2) /
          z 2 ^ 2 := by rw [hnumerator]
      _ = -((a₁ : K) * (a₂ : K)) := by field_simp [hz₂]

end BONG.GoodBONG

end Bong
