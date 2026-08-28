/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalLocalClassificationProof

/-!
# Hasse symbols under binary-pair scaling

This file isolates the paper-independent orthogonal-sum calculation used in
O'Meara 93:18(iii) and in Beli's quaternary arguments.  Scaling the final
binary pair of a four-dimensional diagonal form by `eta` changes Beli's
Hasse symbol by the Hilbert symbol of `eta` with the signed determinant of
that pair.
-/

namespace Bong

open Dyadic BONG.GoodBONG

namespace DiagonalHassePairScaling

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Determinants multiply under appending diagonal coefficient families. -/
theorem determinant_append {m n : Nat}
    (a : Fin m → Kˣ) (b : Fin n → Kˣ) :
    diagonalUnitDeterminant (Fin.append a b) =
      diagonalUnitDeterminant a * diagonalUnitDeterminant b := by
  unfold diagonalUnitDeterminant
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- Hasse-symbol orthogonal-sum formula for appended diagonal families. -/
theorem hasse_append [HilbertSymbolLaws K] {m n : Nat}
    (a : Fin m → Kˣ) (b : Fin n → Kˣ) :
    diagonalHasseSymbol K (Fin.append a b) =
      diagonalHasseSymbol K a *
        hilbertSymbol K (diagonalUnitDeterminant a)
          (diagonalUnitDeterminant b) *
        diagonalHasseSymbol K b := by
  induction n with
  | zero =>
      have happ : Fin.append a b = a := by
        funext i
        simpa using Fin.append_left a b i
      rw [happ]
      simp [diagonalUnitDeterminant]
  | succ n ih =>
      let b0 : Fin n → Kˣ := Fin.init b
      let d : Kˣ := b (Fin.last n)
      have hb : b = Fin.snoc b0 d := (Fin.snoc_init_self b).symm
      rw [hb, Fin.append_snoc, diagonalHasseSymbol_snoc,
        diagonalHasseSymbol_snoc, ih]
      rw [determinant_append, diagonalUnitDeterminant_snoc,
        hilbertSymbol_mul_left, hilbertSymbol_mul_right]
      ac_rfl

/-- Scaling both coefficients of a binary diagonal form changes Beli's
Hasse symbol by `(eta,-det)`. -/
theorem hasse_fin_two_scale [HilbertSymbolLaws K]
    (c : Fin 2 → Kˣ) (eta : Kˣ) :
    diagonalHasseSymbol K (fun i ↦ eta * c i) =
      hilbertSymbol K eta (-diagonalUnitDeterminant c) *
        diagonalHasseSymbol K c := by
  rw [diagonalHasseSymbol_fin_two_eq_det_cross,
    diagonalHasseSymbol_fin_two_eq_det_cross]
  have hdet :
      diagonalUnitDeterminant (fun i ↦ eta * c i) =
        diagonalUnitDeterminant c * eta ^ 2 := by
    apply Units.ext
    simp only [diagonalUnitDeterminant, Fin.prod_univ_two,
      Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hdet, hilbertSymbol_mul_square_left]
  change
    hilbertSymbol K (diagonalUnitDeterminant c) (-1) *
        hilbertSymbol K (eta * c 0) (eta * c 1) = _
  rw [hilbertSymbol_mul_left, hilbertSymbol_mul_right,
    hilbertSymbol_mul_right, hilbertSymbol_comm K (c 0) eta,
    hilbertSymbol_self_eq_neg_one]
  rw [show -diagonalUnitDeterminant c =
      (-1 : Kˣ) * c 0 * c 1 by
    apply Units.ext
    simp [diagonalUnitDeterminant, Fin.prod_univ_two]]
  rw [hilbertSymbol_mul_right, hilbertSymbol_mul_right]
  ac_rfl

/-- Scaling only the final binary pair changes the quaternary Hasse symbol
by the Hilbert symbol of that pair's signed determinant. -/
theorem hasse_fin_four_scale_last_pair [HilbertSymbolLaws K]
    (c : Fin 4 → Kˣ) (eta : Kˣ) :
    diagonalHasseSymbol K ![c 0, c 1, eta * c 2, eta * c 3] =
      hilbertSymbol K eta (-(c 2 * c 3)) *
        diagonalHasseSymbol K c := by
  let head : Fin 2 → Kˣ := ![c 0, c 1]
  let tail : Fin 2 → Kˣ := ![c 2, c 3]
  let changed : Fin 4 → Kˣ := ![c 0, c 1, eta * c 2, eta * c 3]
  have hchanged : changed = Fin.append head (fun i ↦ eta * tail i) := by
    funext i
    fin_cases i <;> rfl
  have hc : c = Fin.append head tail := by
    funext i
    fin_cases i <;> rfl
  rw [show ![c 0, c 1, eta * c 2, eta * c 3] = changed by rfl,
    hchanged, hc, hasse_append, hasse_append, hasse_fin_two_scale]
  have htailDet :
      diagonalUnitDeterminant (fun i ↦ eta * tail i) =
        diagonalUnitDeterminant tail * eta ^ 2 := by
    apply Units.ext
    simp only [diagonalUnitDeterminant, Fin.prod_univ_two,
      Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [htailDet, hilbertSymbol_mul_square_right]
  have hsignedTail : -diagonalUnitDeterminant tail =
      -(c 2 * c 3) := by
    simp [tail, diagonalUnitDeterminant, Fin.prod_univ_two]
  rw [hsignedTail]
  ac_rfl

end DiagonalHassePairScaling

end Bong
