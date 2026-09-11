/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Rat.Star

/-!
# He (2025), publisher Table 1

This file transcribes the 48 integral quaternary Gram matrices in Table 1 of
the publisher version of record.  A row
`[a,b,c,d,f₁,f₂,f₃,f₄,f₅,f₆]` denotes the symmetric matrix displayed in the
paragraph immediately preceding the table.

The two negative entries in row 38 and the negative entry in row 46 are
deliberately retained; they are easy to lose in plain-text PDF extraction.
-/

namespace Bong

/-- The ten published coordinates of each of the 48 Table 1 rows. The outer
container is an executable array so finite certificate evaluation does not
expand a 48-level dependent-function case tree. -/
private def heADC2025TableOneCoordinateRows : Array (Fin 10 → ℤ) := #[
  ![2, 2, 2, 2, 0, 0, 0, 1, 1, 1],
  ![2, 2, 2, 2, 1, 0, 0, 1, 0, 1],
  ![2, 2, 2, 2, 0, 0, 0, 1, 1, 0],
  ![2, 2, 2, 2, 1, 0, 0, 0, 0, 1],
  ![2, 2, 2, 4, 1, 1, 0, 1, 0, 0],
  ![2, 2, 2, 2, 1, 0, 0, 0, 0, 0],
  ![2, 2, 2, 4, 1, 1, 0, 0, 1, 0],
  ![2, 2, 2, 4, 1, 0, 0, 1, 0, 1],
  ![2, 2, 2, 4, 0, 0, 0, 1, 1, 1],
  ![2, 2, 2, 4, 1, 0, 0, 1, 0, 0],
  ![2, 2, 2, 4, 1, 0, 0, 0, 0, 1],
  ![2, 2, 2, 6, 1, 1, 0, 0, 1, 0],
  ![2, 2, 2, 4, 0, 0, 0, 1, 1, 0],
  ![2, 2, 4, 4, 1, 1, 0, 1, 1, 2],
  ![2, 2, 4, 4, 1, 1, 0, 0, 1, 1],
  ![2, 2, 2, 6, 1, 0, 0, 1, 0, 0],
  ![2, 2, 4, 4, 0, 0, 0, 1, 1, 2],
  ![2, 2, 4, 4, 1, 1, 0, 1, 0, 0],
  ![2, 2, 4, 4, 0, 1, 1, 1, 0, 2],
  ![2, 2, 2, 10, 1, 1, 0, 1, 0, 0],
  ![2, 2, 2, 6, 0, 0, 0, 1, 1, 1],
  ![2, 2, 2, 6, 1, 0, 0, 0, 0, 0],
  ![2, 2, 4, 4, 1, 0, 0, 0, 0, 2],
  ![2, 2, 4, 4, 0, 1, 1, 1, 1, 1],
  ![2, 2, 4, 4, 1, 0, 0, 0, 0, 1],
  ![2, 2, 4, 4, 0, 1, 0, 0, 1, 1],
  ![2, 2, 4, 6, 1, 1, 0, 0, 1, 1],
  ![2, 2, 4, 4, 0, 1, 1, 0, 0, 0],
  ![2, 4, 4, 4, 0, 0, 0, 1, 2, 2],
  ![2, 2, 4, 4, 0, 1, 0, 0, 1, 0],
  ![2, 4, 4, 4, 1, 0, 2, 0, 1, 2],
  ![2, 2, 4, 6, 0, 1, 0, 1, 1, 0],
  ![2, 4, 4, 4, 1, 1, 0, 1, 0, 0],
  ![2, 2, 4, 8, 0, 1, 0, 0, 0, 2],
  ![2, 4, 4, 4, 0, 0, 0, 1, 1, 1],
  ![2, 2, 6, 6, 0, 1, 1, 1, 1, 1],
  ![2, 4, 4, 6, 1, 0, 2, 0, 1, 2],
  ![2, 4, 4, 6, 0, 0, 2, -1, 1, -1],
  ![2, 4, 4, 6, 1, 0, 2, 0, 1, 0],
  ![2, 2, 6, 8, 0, 1, 1, 1, 0, 3],
  ![2, 4, 4, 8, 1, 0, 2, 0, 2, 0],
  ![2, 4, 4, 6, 1, 1, 0, 0, 1, 1],
  ![2, 4, 4, 8, 1, 1, 0, 1, 2, 2],
  ![2, 4, 4, 8, 1, 0, 1, 1, 1, 2],
  ![2, 4, 6, 6, 0, 1, 1, 1, 2, 1],
  ![2, 4, 6, 6, 1, 0, 1, 0, -1, 2],
  ![2, 4, 6, 10, 0, 1, 2, 0, 2, 1],
  ![2, 4, 6, 12, 0, 1, 0, 0, 2, 0]
]

def heADC2025TableOneCoordinates (i : Fin 48) : Fin 10 → ℤ :=
  heADC2025TableOneCoordinateRows.getD i.val (fun _ ↦ 0)

/-- The integral symmetric Gram matrix represented by a published coordinate row. -/
def heADC2025TableOneGramOfCoordinates
    (x : Fin 10 → ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![x 0, x 4, x 5, x 7;
     x 4, x 1, x 6, x 8;
     x 5, x 6, x 2, x 9;
     x 7, x 8, x 9, x 3]

/-- The explicit determinant polynomial for a `3 × 3` matrix, used to keep
the finite Table 1 certificate small and auditable. -/
def heADC2025TableOneDet3 {R : Type*} [CommRing R]
    (a b c d e f g h i : R) : R :=
  a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g

/-- The first-row Laplace expansion specialized to the published symmetric
`4 × 4` coordinate convention. -/
def heADC2025TableOneDetFormula {R : Type*} [CommRing R]
    (x : Fin 10 → R) : R :=
  x 0 * heADC2025TableOneDet3
      (x 1) (x 6) (x 8) (x 6) (x 2) (x 9) (x 8) (x 9) (x 3) -
  x 4 * heADC2025TableOneDet3
      (x 4) (x 6) (x 8) (x 5) (x 2) (x 9) (x 7) (x 9) (x 3) +
  x 5 * heADC2025TableOneDet3
      (x 4) (x 1) (x 8) (x 5) (x 6) (x 9) (x 7) (x 8) (x 3) -
  x 7 * heADC2025TableOneDet3
      (x 4) (x 1) (x 6) (x 5) (x 6) (x 2) (x 7) (x 8) (x 9)

/-- The first three leading principal minors in the published coordinate
convention. They are polymorphic so that the integer computation and the
rational `LDLᵀ` proof use literally the same polynomials. -/
def heADC2025TableOneLeadingMinorOne {R : Type*} [CommRing R]
    (x : Fin 10 → R) : R := x 0

def heADC2025TableOneLeadingMinorTwo {R : Type*} [CommRing R]
    (x : Fin 10 → R) : R := x 0 * x 1 - x 4 ^ 2

def heADC2025TableOneLeadingMinorThree {R : Type*} [CommRing R]
    (x : Fin 10 → R) : R :=
  heADC2025TableOneDet3
    (x 0) (x 4) (x 5) (x 4) (x 1) (x 6) (x 5) (x 6) (x 2)

/-- The specialized polynomial is the actual determinant of every matrix
written in the Table 1 coordinate convention. -/
theorem heADC2025TableOneGramOfCoordinates_det
    (x : Fin 10 → ℤ) :
    (heADC2025TableOneGramOfCoordinates x).det =
      heADC2025TableOneDetFormula x := by
  rw [Matrix.det_succ_row_zero]
  simp [heADC2025TableOneGramOfCoordinates,
    heADC2025TableOneDetFormula, heADC2025TableOneDet3,
    Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- The concrete integral Gram matrix in Table 1, indexed from zero. -/
def heADC2025TableOneGram (i : Fin 48) : Matrix (Fin 4) (Fin 4) ℤ :=
  heADC2025TableOneGramOfCoordinates (heADC2025TableOneCoordinates i)

theorem heADC2025TableOneGramOfCoordinates_transpose
    (x : Fin 10 → ℤ) :
    (heADC2025TableOneGramOfCoordinates x).transpose =
      heADC2025TableOneGramOfCoordinates x := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem heADC2025TableOneGram_transpose (i : Fin 48) :
    (heADC2025TableOneGram i).transpose = heADC2025TableOneGram i :=
  heADC2025TableOneGramOfCoordinates_transpose _

/-- The literal discriminants printed in Table 1. -/
private def heADC2025TableOnePublishedDiscriminants : Array ℤ := #[
  4, 5, 8, 9, 12, 12, 13, 17, 20, 20, 21, 21, 24, 25, 28, 32,
  32, 32, 33, 36, 36, 36, 36, 36, 45, 45, 48, 48, 48, 49, 60, 69,
  80, 96, 96, 100, 100, 108, 112, 125, 128, 128, 144, 169, 189,
  192, 324, 484
]

def heADC2025TableOnePublishedDiscriminant (i : Fin 48) : ℤ :=
  heADC2025TableOnePublishedDiscriminants.getD i.val 0

/-- Every concrete Gram determinant agrees with the corresponding printed
Table 1 discriminant. -/
private theorem heADC2025TableOneBasicCertificate :
    ∀ i : Fin 48,
      heADC2025TableOneDetFormula (heADC2025TableOneCoordinates i) =
          heADC2025TableOnePublishedDiscriminant i ∧
        0 < heADC2025TableOnePublishedDiscriminant i := by
  decide

theorem heADC2025TableOneGram_det (i : Fin 48) :
    (heADC2025TableOneGram i).det =
      heADC2025TableOnePublishedDiscriminant i := by
  rw [show heADC2025TableOneGram i =
      heADC2025TableOneGramOfCoordinates
        (heADC2025TableOneCoordinates i) from rfl,
    heADC2025TableOneGramOfCoordinates_det]
  exact (heADC2025TableOneBasicCertificate i).1

theorem heADC2025TableOnePublishedDiscriminant_pos (i : Fin 48) :
    0 < heADC2025TableOnePublishedDiscriminant i :=
  (heADC2025TableOneBasicCertificate i).2

/-- A small integer certificate for Sylvester's first three leading minors.
The fourth minor is the published discriminant already checked above. -/
private theorem heADC2025TableOneLeadingMinorCertificate :
    ∀ i : Fin 48,
      0 < heADC2025TableOneLeadingMinorOne
          (heADC2025TableOneCoordinates i) ∧
        0 < heADC2025TableOneLeadingMinorTwo
          (heADC2025TableOneCoordinates i) ∧
        0 < heADC2025TableOneLeadingMinorThree
          (heADC2025TableOneCoordinates i) := by
  decide

theorem heADC2025TableOneLeadingMinorOne_pos (i : Fin 48) :
    0 < heADC2025TableOneLeadingMinorOne
      (heADC2025TableOneCoordinates i) :=
  (heADC2025TableOneLeadingMinorCertificate i).1

theorem heADC2025TableOneLeadingMinorTwo_pos (i : Fin 48) :
    0 < heADC2025TableOneLeadingMinorTwo
      (heADC2025TableOneCoordinates i) :=
  (heADC2025TableOneLeadingMinorCertificate i).2.1

theorem heADC2025TableOneLeadingMinorThree_pos (i : Fin 48) :
    0 < heADC2025TableOneLeadingMinorThree
      (heADC2025TableOneCoordinates i) :=
  (heADC2025TableOneLeadingMinorCertificate i).2.2

/-! ## Exact positive-definiteness certificates -/

/-- A rational coordinate row interpreted by the same convention as the
integral Table 1 matrix. -/
def heADC2025TableOneGramRatOfCoordinates
    (x : Fin 10 → ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![x 0, x 4, x 5, x 7;
     x 4, x 1, x 6, x 8;
     x 5, x 6, x 2, x 9;
     x 7, x 8, x 9, x 3]

/-- The published integral row cast entrywise to rational coordinates. -/
def heADC2025TableOneCoordinatesRat (i : Fin 48) : Fin 10 → ℚ :=
  fun j ↦ heADC2025TableOneCoordinates i j

/-- The Table 1 Gram matrix over the ordered field of rational numbers. -/
def heADC2025TableOneGramRat (i : Fin 48) : Matrix (Fin 4) (Fin 4) ℚ :=
  heADC2025TableOneGramRatOfCoordinates
    (heADC2025TableOneCoordinatesRat i)

theorem heADC2025TableOneGramRat_eq_map (i : Fin 48) :
    heADC2025TableOneGramRat i =
      (heADC2025TableOneGram i).map (Int.castRingHom ℚ) := by
  ext r c
  fin_cases r <;> fin_cases c <;> rfl

def heADC2025LDLD0 (x : Fin 10 → ℚ) : ℚ := x 0
def heADC2025LDLL10 (x : Fin 10 → ℚ) : ℚ := x 4 / heADC2025LDLD0 x
def heADC2025LDLL20 (x : Fin 10 → ℚ) : ℚ := x 5 / heADC2025LDLD0 x
def heADC2025LDLL30 (x : Fin 10 → ℚ) : ℚ := x 7 / heADC2025LDLD0 x
def heADC2025LDLD1 (x : Fin 10 → ℚ) : ℚ :=
  x 1 - heADC2025LDLL10 x ^ 2 * heADC2025LDLD0 x
def heADC2025LDLL21 (x : Fin 10 → ℚ) : ℚ :=
  (x 6 - heADC2025LDLL20 x * heADC2025LDLL10 x * heADC2025LDLD0 x) /
    heADC2025LDLD1 x
def heADC2025LDLL31 (x : Fin 10 → ℚ) : ℚ :=
  (x 8 - heADC2025LDLL30 x * heADC2025LDLL10 x * heADC2025LDLD0 x) /
    heADC2025LDLD1 x
def heADC2025LDLD2 (x : Fin 10 → ℚ) : ℚ :=
  x 2 - heADC2025LDLL20 x ^ 2 * heADC2025LDLD0 x -
    heADC2025LDLL21 x ^ 2 * heADC2025LDLD1 x
def heADC2025LDLL32 (x : Fin 10 → ℚ) : ℚ :=
  (x 9 - heADC2025LDLL30 x * heADC2025LDLL20 x * heADC2025LDLD0 x -
      heADC2025LDLL31 x * heADC2025LDLL21 x * heADC2025LDLD1 x) /
    heADC2025LDLD2 x
def heADC2025LDLD3 (x : Fin 10 → ℚ) : ℚ :=
  x 3 - heADC2025LDLL30 x ^ 2 * heADC2025LDLD0 x -
    heADC2025LDLL31 x ^ 2 * heADC2025LDLD1 x -
    heADC2025LDLL32 x ^ 2 * heADC2025LDLD2 x

theorem heADC2025LDLD1_eq_minor_ratio
    (x : Fin 10 → ℚ)
    (h1 : heADC2025TableOneLeadingMinorOne x ≠ 0) :
    heADC2025LDLD1 x =
      heADC2025TableOneLeadingMinorTwo x /
        heADC2025TableOneLeadingMinorOne x := by
  have hx0 : x 0 ≠ 0 := by
    simpa [heADC2025TableOneLeadingMinorOne] using h1
  simp [heADC2025LDLD1, heADC2025LDLL10, heADC2025LDLD0,
    heADC2025TableOneLeadingMinorOne,
    heADC2025TableOneLeadingMinorTwo]
  field_simp [hx0]

set_option maxHeartbeats 1000000 in
-- Clearing the two symbolic rational denominators needs a larger algebra budget.
theorem heADC2025LDLD2_eq_minor_ratio
    (x : Fin 10 → ℚ)
    (h1 : heADC2025TableOneLeadingMinorOne x ≠ 0)
    (h2 : heADC2025TableOneLeadingMinorTwo x ≠ 0) :
    heADC2025LDLD2 x =
      heADC2025TableOneLeadingMinorThree x /
        heADC2025TableOneLeadingMinorTwo x := by
  have hx0 : x 0 ≠ 0 := by
    simpa [heADC2025TableOneLeadingMinorOne] using h1
  have hx2 : x 0 * x 1 - x 4 ^ 2 ≠ 0 := by
    simpa [heADC2025TableOneLeadingMinorTwo] using h2
  simp only [heADC2025LDLD2, heADC2025LDLL20,
    heADC2025LDLL21, heADC2025LDLL10, heADC2025LDLD0]
  rw [show heADC2025LDLD1 x =
      heADC2025TableOneLeadingMinorTwo x /
        heADC2025TableOneLeadingMinorOne x from
    heADC2025LDLD1_eq_minor_ratio x h1]
  simp [heADC2025TableOneLeadingMinorOne,
    heADC2025TableOneLeadingMinorTwo,
    heADC2025TableOneLeadingMinorThree,
    heADC2025TableOneDet3]
  field_simp [hx0, hx2]
  ring

/-- The diagonal in the exact rank-four `LDLᵀ` decomposition. -/
def heADC2025LDLDiagonal (x : Fin 10 → ℚ) : Fin 4 → ℚ :=
  ![heADC2025LDLD0 x, heADC2025LDLD1 x,
    heADC2025LDLD2 x, heADC2025LDLD3 x]

/-- The unit lower-triangular factor in the exact rank-four `LDLᵀ`
decomposition. -/
def heADC2025LDLUnitLower
    (x : Fin 10 → ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, 0;
     heADC2025LDLL10 x, 1, 0, 0;
     heADC2025LDLL20 x, heADC2025LDLL21 x, 1, 0;
     heADC2025LDLL30 x, heADC2025LDLL31 x, heADC2025LDLL32 x, 1]

set_option maxHeartbeats 1000000 in
-- Expanding all sixteen symbolic entries of the rank-four product needs this budget.
/-- The symbolic rank-four `LDLᵀ` identity. It is proved once; concrete rows
need only certify their four positive pivots. -/
theorem heADC2025TableOneGramRatOfCoordinates_eq_ldl
    (x : Fin 10 → ℚ) (h0 : heADC2025LDLD0 x ≠ 0)
    (h1 : heADC2025LDLD1 x ≠ 0) (h2 : heADC2025LDLD2 x ≠ 0) :
    heADC2025TableOneGramRatOfCoordinates x =
      heADC2025LDLUnitLower x *
        Matrix.diagonal (heADC2025LDLDiagonal x) *
          (heADC2025LDLUnitLower x).transpose := by
  have hx0 : x 0 ≠ 0 := by simpa [heADC2025LDLD0] using h0
  have hl10 : heADC2025LDLL10 x * x 0 = x 4 := by
    simp [heADC2025LDLL10, heADC2025LDLD0, hx0]
  have hl20 : heADC2025LDLL20 x * x 0 = x 5 := by
    simp [heADC2025LDLL20, heADC2025LDLD0, hx0]
  have hl30 : heADC2025LDLL30 x * x 0 = x 7 := by
    simp [heADC2025LDLL30, heADC2025LDLD0, hx0]
  have hd1 :
      heADC2025LDLD1 x + heADC2025LDLL10 x ^ 2 * x 0 = x 1 := by
    simp [heADC2025LDLD1, heADC2025LDLD0]
  have hl21 :
      heADC2025LDLL21 x * heADC2025LDLD1 x +
        heADC2025LDLL20 x * heADC2025LDLL10 x * x 0 = x 6 := by
    simp [heADC2025LDLL21, heADC2025LDLD0, h1]
  have hl31 :
      heADC2025LDLL31 x * heADC2025LDLD1 x +
        heADC2025LDLL30 x * heADC2025LDLL10 x * x 0 = x 8 := by
    simp [heADC2025LDLL31, heADC2025LDLD0, h1]
  have hd2 :
      heADC2025LDLD2 x + heADC2025LDLL20 x ^ 2 * x 0 +
        heADC2025LDLL21 x ^ 2 * heADC2025LDLD1 x = x 2 := by
    simp [heADC2025LDLD2, heADC2025LDLD0]
    ring
  have hl32 :
      heADC2025LDLL32 x * heADC2025LDLD2 x +
        heADC2025LDLL30 x * heADC2025LDLL20 x * x 0 +
        heADC2025LDLL31 x * heADC2025LDLL21 x * heADC2025LDLD1 x =
          x 9 := by
    simp [heADC2025LDLL32, heADC2025LDLD0, h2]
    ring
  have hd3 :
      heADC2025LDLD3 x + heADC2025LDLL30 x ^ 2 * x 0 +
        heADC2025LDLL31 x ^ 2 * heADC2025LDLD1 x +
        heADC2025LDLL32 x ^ 2 * heADC2025LDLD2 x = x 3 := by
    simp [heADC2025LDLD3, heADC2025LDLD0]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heADC2025TableOneGramRatOfCoordinates,
      heADC2025LDLUnitLower, heADC2025LDLDiagonal,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      heADC2025LDLD0]
  all_goals first
    | nlinarith only [hl10]
    | nlinarith only [hl20]
    | nlinarith only [hl30]
    | nlinarith only [hd1]
    | nlinarith only [hl21]
    | nlinarith only [hl31]
    | nlinarith only [hd2]
    | nlinarith only [hl32]
    | nlinarith only [hd3]

/-- The integer minor certificates transported to rational coordinates. -/
private theorem heADC2025TableOneLeadingMinorOneRat_pos (i : Fin 48) :
    0 < heADC2025TableOneLeadingMinorOne
      (heADC2025TableOneCoordinatesRat i) := by
  have h := heADC2025TableOneLeadingMinorOne_pos i
  simp only [heADC2025TableOneLeadingMinorOne,
    heADC2025TableOneCoordinatesRat] at h ⊢
  exact_mod_cast h

private theorem heADC2025TableOneLeadingMinorTwoRat_pos (i : Fin 48) :
    0 < heADC2025TableOneLeadingMinorTwo
      (heADC2025TableOneCoordinatesRat i) := by
  have h := heADC2025TableOneLeadingMinorTwo_pos i
  simp only [heADC2025TableOneLeadingMinorTwo,
    heADC2025TableOneCoordinatesRat] at h ⊢
  exact_mod_cast h

private theorem heADC2025TableOneLeadingMinorThreeRat_pos (i : Fin 48) :
    0 < heADC2025TableOneLeadingMinorThree
      (heADC2025TableOneCoordinatesRat i) := by
  have h := heADC2025TableOneLeadingMinorThree_pos i
  simp only [heADC2025TableOneLeadingMinorThree,
    heADC2025TableOneDet3, heADC2025TableOneCoordinatesRat] at h ⊢
  exact_mod_cast h

theorem heADC2025TableOneLDLD0_pos (i : Fin 48) :
    0 < heADC2025LDLD0 (heADC2025TableOneCoordinatesRat i) := by
  simpa [heADC2025LDLD0, heADC2025TableOneLeadingMinorOne] using
    heADC2025TableOneLeadingMinorOneRat_pos i

theorem heADC2025TableOneLDLD1_pos (i : Fin 48) :
    0 < heADC2025LDLD1 (heADC2025TableOneCoordinatesRat i) := by
  rw [heADC2025LDLD1_eq_minor_ratio _
    (ne_of_gt (heADC2025TableOneLeadingMinorOneRat_pos i))]
  exact div_pos (heADC2025TableOneLeadingMinorTwoRat_pos i)
    (heADC2025TableOneLeadingMinorOneRat_pos i)

theorem heADC2025TableOneLDLD2_pos (i : Fin 48) :
    0 < heADC2025LDLD2 (heADC2025TableOneCoordinatesRat i) := by
  rw [heADC2025LDLD2_eq_minor_ratio _
    (ne_of_gt (heADC2025TableOneLeadingMinorOneRat_pos i))
    (ne_of_gt (heADC2025TableOneLeadingMinorTwoRat_pos i))]
  exact div_pos (heADC2025TableOneLeadingMinorThreeRat_pos i)
    (heADC2025TableOneLeadingMinorTwoRat_pos i)

/-- Machine-checked exact `LDLᵀ` factorization for every published row. -/
theorem heADC2025TableOneGramRat_eq_ldl (i : Fin 48) :
    heADC2025TableOneGramRat i =
      heADC2025LDLUnitLower (heADC2025TableOneCoordinatesRat i) *
        Matrix.diagonal
          (heADC2025LDLDiagonal (heADC2025TableOneCoordinatesRat i)) *
          (heADC2025LDLUnitLower
            (heADC2025TableOneCoordinatesRat i)).transpose :=
  heADC2025TableOneGramRatOfCoordinates_eq_ldl _
    (ne_of_gt (heADC2025TableOneLDLD0_pos i))
    (ne_of_gt (heADC2025TableOneLDLD1_pos i))
    (ne_of_gt (heADC2025TableOneLDLD2_pos i))

/-- Every unit lower-triangular factor used above has determinant one. -/
theorem heADC2025TableOneLDLUnitLower_det (x : Fin 10 → ℚ) :
    (heADC2025LDLUnitLower x).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [heADC2025LDLUnitLower, Matrix.det_fin_three,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.succAbove]

/-- The rational determinant is the cast of the checked published integer
discriminant. -/
theorem heADC2025TableOneGramRat_det_pos (i : Fin 48) :
    0 < (heADC2025TableOneGramRat i).det := by
  rw [heADC2025TableOneGramRat_eq_map]
  change 0 < ((Int.castRingHom ℚ).mapMatrix
    (heADC2025TableOneGram i)).det
  rw [← (Int.castRingHom ℚ).map_det, heADC2025TableOneGram_det]
  change (0 : ℚ) < (heADC2025TableOnePublishedDiscriminant i : ℚ)
  exact_mod_cast heADC2025TableOnePublishedDiscriminant_pos i

/-- Taking determinants in the exact `LDLᵀ` identity expresses the checked
discriminant as the product of the four pivots. -/
theorem heADC2025TableOneGramRat_det_eq_pivotProduct (i : Fin 48) :
    (heADC2025TableOneGramRat i).det =
      ((heADC2025LDLD0 (heADC2025TableOneCoordinatesRat i) *
          heADC2025LDLD1 (heADC2025TableOneCoordinatesRat i)) *
        heADC2025LDLD2 (heADC2025TableOneCoordinatesRat i)) *
          heADC2025LDLD3 (heADC2025TableOneCoordinatesRat i) := by
  rw [heADC2025TableOneGramRat_eq_ldl, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose,
    heADC2025TableOneLDLUnitLower_det]
  simp [heADC2025LDLDiagonal, Fin.prod_univ_succ, mul_assoc]

theorem heADC2025TableOneLDLD3_pos (i : Fin 48) :
    0 < heADC2025LDLD3 (heADC2025TableOneCoordinatesRat i) := by
  have hdet :
      0 < ((heADC2025LDLD0 (heADC2025TableOneCoordinatesRat i) *
          heADC2025LDLD1 (heADC2025TableOneCoordinatesRat i)) *
        heADC2025LDLD2 (heADC2025TableOneCoordinatesRat i)) *
          heADC2025LDLD3 (heADC2025TableOneCoordinatesRat i) := by
    rw [← heADC2025TableOneGramRat_det_eq_pivotProduct]
    exact heADC2025TableOneGramRat_det_pos i
  exact pos_of_mul_pos_right hdet
    (le_of_lt (mul_pos
      (mul_pos (heADC2025TableOneLDLD0_pos i)
        (heADC2025TableOneLDLD1_pos i))
      (heADC2025TableOneLDLD2_pos i)))

/-- All four exact pivots are positive in every published row. -/
theorem heADC2025TableOneLDLDiagonal_pos (i : Fin 48) (j : Fin 4) :
    0 < heADC2025LDLDiagonal (heADC2025TableOneCoordinatesRat i) j := by
  fin_cases j
  · simpa [heADC2025LDLDiagonal] using heADC2025TableOneLDLD0_pos i
  · simpa [heADC2025LDLDiagonal] using heADC2025TableOneLDLD1_pos i
  · simpa [heADC2025LDLDiagonal] using heADC2025TableOneLDLD2_pos i
  · simpa [heADC2025LDLDiagonal] using heADC2025TableOneLDLD3_pos i

/-- Every integral Gram matrix printed in Table 1 is positive definite after
the canonical inclusion into `ℚ`. -/
theorem heADC2025TableOneGramRat_posDef (i : Fin 48) :
    (heADC2025TableOneGramRat i).PosDef := by
  rw [heADC2025TableOneGramRat_eq_ldl]
  have hD :
      (Matrix.diagonal
        (heADC2025LDLDiagonal
          (heADC2025TableOneCoordinatesRat i))).PosDef :=
    Matrix.PosDef.diagonal (heADC2025TableOneLDLDiagonal_pos i)
  have hL :
      IsUnit (heADC2025LDLUnitLower
        (heADC2025TableOneCoordinatesRat i)) := by
    rw [Matrix.isUnit_iff_isUnit_det,
      heADC2025TableOneLDLUnitLower_det]
    exact isUnit_one
  simpa [Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.IsUnit.posDef_star_right_conjugate_iff hL).mpr hD

/-- `none` records the word `None` in the last column; `some p` records the
unique printed prime where the half-scaled row is not `2`-ADC. -/
private def heADC2025TableOnePublishedBadPrimes : Array (Option ℕ) := #[
  none, none, none, none, none, none, none, none,
  none, none, none, none, none, none, none,
  some 2, some 2, some 2, none, some 3, some 3, some 2,
  some 3, some 2, none, some 3, some 2, some 2, some 2,
  none, none, none, some 2, some 2, some 2, some 5,
  some 2, some 3, some 2, some 5, some 2, some 2,
  some 2, none, some 3, some 2, some 3, some 11
]

def heADC2025TableOnePublishedBadPrime (i : Fin 48) : Option ℕ :=
  heADC2025TableOnePublishedBadPrimes.getD i.val none

/-- Literal selection predicate defined by the last column of Table 1. -/
def HeADC2025TableOnePassesPublishedLocalCheck (i : Fin 48) : Prop :=
  heADC2025TableOnePublishedBadPrime i = none

instance (i : Fin 48) :
    Decidable (HeADC2025TableOnePassesPublishedLocalCheck i) :=
  by
    unfold HeADC2025TableOnePassesPublishedLocalCheck
    infer_instance

/-- The word `None` occurs exactly in rows 1--15, 19, 25, 30--32, and 44. -/
private theorem heADC2025TableOneSelectionCertificate :
    (∀ i : Fin 48,
      HeADC2025TableOnePassesPublishedLocalCheck i ↔
        i.val < 15 ∨ i.val = 18 ∨ i.val = 24 ∨ i.val = 29 ∨
          i.val = 30 ∨ i.val = 31 ∨ i.val = 43) ∧
      Fintype.card
        {i : Fin 48 // HeADC2025TableOnePassesPublishedLocalCheck i} = 21 := by
  decide

theorem heADC2025TableOnePassesPublishedLocalCheck_iff (i : Fin 48) :
    HeADC2025TableOnePassesPublishedLocalCheck i ↔
      i.val < 15 ∨ i.val = 18 ∨ i.val = 24 ∨ i.val = 29 ∨
        i.val = 30 ∨ i.val = 31 ∨ i.val = 43 :=
  heADC2025TableOneSelectionCertificate.1 i

/-- Exactly 21 of the 48 rows carry `None` in the last published column. -/
theorem card_heADC2025TableOnePassesPublishedLocalCheck :
    Fintype.card {i : Fin 48 // HeADC2025TableOnePassesPublishedLocalCheck i} = 21 :=
  heADC2025TableOneSelectionCertificate.2

end Bong
