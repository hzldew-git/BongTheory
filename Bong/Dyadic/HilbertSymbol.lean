/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.QuadraticDefect

/-!
# The quadratic norm relation and Hilbert symbol

For nonzero `a` and `b`, the relation `IsQuadraticNorm K a b` says that

`b = x² - a * y²`

for some `x y : K`.  This is the norm equation for the quadratic algebra
`K[√a]`.  The Hilbert symbol is `1` exactly when this equation is solvable and
is `-1` otherwise.

The elementary norm identities, symmetry, and invariance under square factors
are proved here over any field of characteristic zero.  The genuinely local
statements--bimultiplicativity, nondegeneracy, and Beli's defect criterion--are
recorded in `HilbertSymbolLaws`, since their proofs require local class-field
input that is not currently available in mathlib.
-/

namespace Bong.Dyadic

section Algebra

variable (K : Type*) [Field K]

/-- `b` is represented by the norm form `x² - a * y²`. -/
def IsQuadraticNorm (a b : Kˣ) : Prop :=
  ∃ x y : K, x ^ 2 - (a : K) * y ^ 2 = (b : K)

theorem isQuadraticNorm_one (a : Kˣ) : IsQuadraticNorm K a 1 := by
  refine ⟨1, 0, ?_⟩
  simp

theorem IsQuadraticNorm.mul {a b c : Kˣ} (hb : IsQuadraticNorm K a b)
    (hc : IsQuadraticNorm K a c) : IsQuadraticNorm K a (b * c) := by
  rcases hb with ⟨x₁, y₁, h₁⟩
  rcases hc with ⟨x₂, y₂, h₂⟩
  refine ⟨x₁ * x₂ + (a : K) * y₁ * y₂, x₁ * y₂ + y₁ * x₂, ?_⟩
  change
    (x₁ * x₂ + (a : K) * y₁ * y₂) ^ 2 -
        (a : K) * (x₁ * y₂ + y₁ * x₂) ^ 2 =
      (b : K) * (c : K)
  rw [← h₁, ← h₂]
  ring

theorem IsQuadraticNorm.inv {a b : Kˣ} (hb : IsQuadraticNorm K a b) :
    IsQuadraticNorm K a b⁻¹ := by
  rcases hb with ⟨x, y, h⟩
  refine ⟨x / (b : K), y / (b : K), ?_⟩
  rw [Units.val_inv_eq_inv_val]
  change
    (x / (b : K)) ^ 2 - (a : K) * (y / (b : K)) ^ 2 = ((b : K)⁻¹)
  calc
    (x / (b : K)) ^ 2 - (a : K) * (y / (b : K)) ^ 2 =
        (x ^ 2 - (a : K) * y ^ 2) / (b : K) ^ 2 := by ring
    _ = (b : K) / (b : K) ^ 2 := by rw [h]
    _ = (b : K)⁻¹ := by field_simp [Units.ne_zero b]

/-- The nonzero values represented by `x² - a * y²`. -/
def quadraticNormGroup (a : Kˣ) : Subgroup Kˣ where
  carrier := {b | IsQuadraticNorm K a b}
  one_mem' := isQuadraticNorm_one K a
  mul_mem' := IsQuadraticNorm.mul K
  inv_mem' := IsQuadraticNorm.inv K

@[simp]
theorem mem_quadraticNormGroup {a b : Kˣ} :
    b ∈ quadraticNormGroup K a ↔ IsQuadraticNorm K a b :=
  Iff.rfl

theorem isQuadraticNorm_of_isSquare_right {a b : Kˣ} (hb : IsSquare b) :
    IsQuadraticNorm K a b := by
  rcases hb with ⟨s, rfl⟩
  refine ⟨(s : K), 0, ?_⟩
  simp [pow_two]

theorem isQuadraticNorm_of_isSquare_left [CharZero K] {a b : Kˣ} (ha : IsSquare a) :
    IsQuadraticNorm K a b := by
  rcases ha with ⟨s, hs⟩
  have hsval : (a : K) = (s : K) ^ 2 := by
    rw [hs]
    simp [pow_two]
  refine ⟨((b : K) + 1) / 2, ((b : K) - 1) / (2 * (s : K)), ?_⟩
  rw [hsval]
  field_simp [Units.ne_zero s]
  ring

/-- Symmetry of the quadratic norm relation. -/
theorem IsQuadraticNorm.symm [CharZero K] {a b : Kˣ} (h : IsQuadraticNorm K a b) :
    IsQuadraticNorm K b a := by
  rcases h with ⟨x, y, hxy⟩
  by_cases hy : y = 0
  · have hx_sq : x ^ 2 = (b : K) := by simpa [hy] using hxy
    have hx : x ≠ 0 := by
      intro hx
      rw [hx] at hx_sq
      exact (Units.ne_zero b) (by simpa using hx_sq.symm)
    have hb : IsSquare b := by
      refine ⟨Units.mk0 x hx, ?_⟩
      apply Units.ext
      simpa [pow_two] using hx_sq.symm
    exact isQuadraticNorm_of_isSquare_left K hb
  · refine ⟨x / y, 1 / y, ?_⟩
    calc
      (x / y) ^ 2 - (b : K) * (1 / y) ^ 2 =
          (x ^ 2 - (b : K)) / y ^ 2 := by ring
      _ = (a : K) := by
        rw [← hxy]
        field_simp [hy]
        ring

theorem isQuadraticNorm_comm [CharZero K] (a b : Kˣ) :
    IsQuadraticNorm K a b ↔ IsQuadraticNorm K b a :=
  ⟨IsQuadraticNorm.symm K, IsQuadraticNorm.symm K⟩

theorem isQuadraticNorm_mul_square_right_iff (a b s : Kˣ) :
    IsQuadraticNorm K a (b * s ^ 2) ↔ IsQuadraticNorm K a b := by
  constructor
  · intro h
    have hs : s ^ 2 ∈ quadraticNormGroup K a :=
      isQuadraticNorm_of_isSquare_right K ⟨s, by simp [pow_two]⟩
    have hprod : b * s ^ 2 ∈ quadraticNormGroup K a := h
    simpa using (quadraticNormGroup K a).mul_mem hprod
      ((quadraticNormGroup K a).inv_mem hs)
  · intro h
    apply IsQuadraticNorm.mul K h
    exact isQuadraticNorm_of_isSquare_right K ⟨s, by simp [pow_two]⟩

theorem isQuadraticNorm_mul_square_left_iff [CharZero K] (a b s : Kˣ) :
    IsQuadraticNorm K (a * s ^ 2) b ↔ IsQuadraticNorm K a b := by
  rw [isQuadraticNorm_comm K, isQuadraticNorm_comm K a b]
  exact isQuadraticNorm_mul_square_right_iff K b a s

/-- The Hilbert symbol, defined through solvability of the quadratic norm equation. -/
noncomputable def hilbertSymbol (a b : Kˣ) : ℤˣ := by
  classical
  exact if IsQuadraticNorm K a b then 1 else -1

theorem hilbertSymbol_eq_one_iff (a b : Kˣ) :
    hilbertSymbol K a b = 1 ↔ IsQuadraticNorm K a b := by
  classical
  simp [hilbertSymbol]

theorem hilbertSymbol_eq_neg_one_iff (a b : Kˣ) :
    hilbertSymbol K a b = -1 ↔ ¬IsQuadraticNorm K a b := by
  classical
  simp [hilbertSymbol]

theorem hilbertSymbol_comm [CharZero K] (a b : Kˣ) :
    hilbertSymbol K a b = hilbertSymbol K b a := by
  classical
  simp only [hilbertSymbol]
  rw [isQuadraticNorm_comm K a b]

theorem hilbertSymbol_eq_one_of_isSquare_left [CharZero K] {a b : Kˣ} (ha : IsSquare a) :
    hilbertSymbol K a b = 1 :=
  (hilbertSymbol_eq_one_iff K a b).2 (isQuadraticNorm_of_isSquare_left K ha)

theorem hilbertSymbol_eq_one_of_isSquare_right {a b : Kˣ} (hb : IsSquare b) :
    hilbertSymbol K a b = 1 :=
  (hilbertSymbol_eq_one_iff K a b).2 (isQuadraticNorm_of_isSquare_right K hb)

@[simp]
theorem hilbertSymbol_one_left [CharZero K] (b : Kˣ) : hilbertSymbol K 1 b = 1 :=
  hilbertSymbol_eq_one_of_isSquare_left K ⟨1, by simp⟩

@[simp]
theorem hilbertSymbol_one_right (a : Kˣ) : hilbertSymbol K a 1 = 1 :=
  hilbertSymbol_eq_one_of_isSquare_right K ⟨1, by simp⟩

theorem hilbertSymbol_mul_square_right (a b s : Kˣ) :
    hilbertSymbol K a (b * s ^ 2) = hilbertSymbol K a b := by
  classical
  simp only [hilbertSymbol]
  rw [isQuadraticNorm_mul_square_right_iff K a b s]

theorem hilbertSymbol_mul_square_left [CharZero K] (a b s : Kˣ) :
    hilbertSymbol K (a * s ^ 2) b = hilbertSymbol K a b := by
  rw [hilbertSymbol_comm K (a * s ^ 2) b, hilbertSymbol_mul_square_right]
  exact hilbertSymbol_comm K b a

end Algebra

section Dyadic

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K]

/--
The local-field laws needed to use the concrete Hilbert symbol in BONG theory.
They are kept as an explicit interface until the requisite local norm theorem
has been developed in mathlib or in this project.
-/
class HilbertSymbolLaws : Prop where
  map_mul_right (a b c : Kˣ) :
    hilbertSymbol K a (b * c) = hilbertSymbol K a b * hilbertSymbol K a c
  nondegenerate (a : Kˣ) :
    (∀ b : Kˣ, hilbertSymbol K a b = 1) → IsSquare a
  eq_one_of_defect_add_gt_two_mul_e (a b : Kˣ)
      (h : ((2 * ramificationIndex K : ℕ) : ℕ∞) <
        quadraticDefect K a + quadraticDefect K b) :
    hilbertSymbol K a b = 1

variable [HilbertSymbolLaws K]

theorem hilbertSymbol_mul_right (a b c : Kˣ) :
    hilbertSymbol K a (b * c) = hilbertSymbol K a b * hilbertSymbol K a c :=
  HilbertSymbolLaws.map_mul_right a b c

theorem hilbertSymbol_mul_left (a b c : Kˣ) :
    hilbertSymbol K (a * b) c = hilbertSymbol K a c * hilbertSymbol K b c := by
  rw [hilbertSymbol_comm K (a * b) c, hilbertSymbol_mul_right]
  rw [hilbertSymbol_comm K c a, hilbertSymbol_comm K c b]

theorem hilbertSymbol_left_trivial_iff_isSquare (a : Kˣ) :
    (∀ b : Kˣ, hilbertSymbol K a b = 1) ↔ IsSquare a := by
  constructor
  · exact HilbertSymbolLaws.nondegenerate a
  · intro ha b
    exact hilbertSymbol_eq_one_of_isSquare_left K ha

theorem hilbertSymbol_eq_one_of_defect_add_gt_two_mul_e {a b : Kˣ}
    (h : ((2 * ramificationIndex K : ℕ) : ℕ∞) <
      quadraticDefect K a + quadraticDefect K b) :
    hilbertSymbol K a b = 1 :=
  HilbertSymbolLaws.eq_one_of_defect_add_gt_two_mul_e a b h

/-- For fixed `a`, the Hilbert symbol is a quadratic character. -/
noncomputable def hilbertCharacter (a : Kˣ) : Kˣ →* ℤˣ where
  toFun b := hilbertSymbol K a b
  map_one' := hilbertSymbol_one_right K a
  map_mul' := hilbertSymbol_mul_right K a

@[simp]
theorem hilbertCharacter_apply (a b : Kˣ) :
    hilbertCharacter K a b = hilbertSymbol K a b :=
  rfl

end Dyadic

end Bong.Dyadic
