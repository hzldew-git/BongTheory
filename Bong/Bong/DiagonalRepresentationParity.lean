/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Classification
import Bong.Bong.TruthParity
import Bong.Dyadic.HilbertSymbol

/-!
# Parity laws for codimension-one diagonal representations

This file extracts the three forms of the quadratic-space parity argument
from Beli's Lemma 1.5 into a paper-independent local-field interface.  The
interface is stated for arbitrary nonzero diagonal coefficients; later Beli
modules only instantiate these generic laws.
-/

namespace Bong

open Dyadic

universe u

variable {K : Type u}

/-- The defect criterion for the Hilbert symbol, restated in the rational
`WithTop` scale used by the BONG invariants. -/
theorem hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
    [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] [HilbertSymbolLaws K] {a b : Kˣ}
    (h : (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
      BONG.GoodBONG.defectOrder (K := K) a +
        BONG.GoodBONG.defectOrder (K := K) b) :
    hilbertSymbol K a b = 1 := by
  let f : Nat →+ ℚ := Nat.castAddMonoidHom ℚ
  have hf : StrictMono (f : Nat → ℚ) := by
    intro x y hxy
    change (x : ℚ) < (y : ℚ)
    exact_mod_cast hxy
  let da : WithTop Nat := quadraticDefect K a
  let db : WithTop Nat := quadraticDefect K b
  apply hilbertSymbol_eq_one_of_defect_add_gt_two_mul_e
  change ((2 * ramificationIndex K : Nat) : WithTop Nat) < da + db
  apply (hf.withTop_map.lt_iff_lt).mp
  rw [WithTop.map_add]
  change (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
    WithTop.map (fun m : Nat => (m : ℚ)) (quadraticDefect K a) +
      WithTop.map (fun m : Nat => (m : ℚ)) (quadraticDefect K b)
  exact h

/-- Delete the last coefficient of a nonempty diagonal presentation. -/
def diagonalUnitPrefix [Monoid K] {n : Nat}
    (a : Fin (n + 1) → Kˣ) : Fin n → Kˣ :=
  fun i ↦ a i.castSucc

/-- Restrict a diagonal presentation to an arbitrary initial segment. -/
def diagonalUnitTake [Monoid K] {m : Nat} (a : Fin m → Kˣ)
    (k : Nat) (hk : k ≤ m) : Fin k → Kˣ :=
  fun i ↦ a (Fin.castLE hk i)

/-- The three codimension-one parity cycles, formulated independently of
good BONGs and lattices. -/
class DiagonalRepresentationParityLaws
    (K : Type u) [Field K] [CharZero K] : Prop where
  caseI {i j k : Nat} (a : Fin i → Kˣ) (b : Fin j → Kˣ)
      (c : Fin k → Kˣ) (hab : i = j) (hkb : k + 1 = j) :
    EvenTruthParity
      (DiagonalRepresents
        (BONG.GoodBONG.diagonalUnitCoefficients
          (diagonalUnitTake b k (by omega)))
        (BONG.GoodBONG.diagonalUnitCoefficients a))
      (DiagonalRepresents
        (BONG.GoodBONG.diagonalUnitCoefficients c)
        (BONG.GoodBONG.diagonalUnitCoefficients b))
      (DiagonalRepresents
        (BONG.GoodBONG.diagonalUnitCoefficients c)
        (BONG.GoodBONG.diagonalUnitCoefficients a))
      (hilbertSymbol K
        (BONG.GoodBONG.diagonalUnitDeterminant a *
          BONG.GoodBONG.diagonalUnitDeterminant b)
        (BONG.GoodBONG.diagonalUnitDeterminant
            (diagonalUnitTake b k (by omega)) *
          BONG.GoodBONG.diagonalUnitDeterminant c) = 1)
  caseII {i j k : Nat} (a : Fin i → Kˣ) (b : Fin j → Kˣ)
      (c : Fin k → Kˣ) (hba : j + 1 = i) (hck : k + 1 = j) :
    EvenTruthParity
      (DiagonalRepresents
        (BONG.GoodBONG.diagonalUnitCoefficients b)
        (BONG.GoodBONG.diagonalUnitCoefficients a))
      (DiagonalRepresents
        (BONG.GoodBONG.diagonalUnitCoefficients c)
        (BONG.GoodBONG.diagonalUnitCoefficients b))
      (DiagonalRepresents
        (BONG.GoodBONG.diagonalUnitCoefficients c)
        (BONG.GoodBONG.diagonalUnitCoefficients
          (diagonalUnitTake a j (by omega))))
      (hilbertSymbol K
        (BONG.GoodBONG.diagonalUnitDeterminant
            (diagonalUnitTake a j (by omega)) *
          BONG.GoodBONG.diagonalUnitDeterminant b)
        (-BONG.GoodBONG.diagonalUnitDeterminant a *
          BONG.GoodBONG.diagonalUnitDeterminant c) = 1)
  caseIII {i j k l : Nat} (a : Fin i → Kˣ) (b : Fin j → Kˣ)
      (c : Fin k → Kˣ) (hba : j + 1 = i) (hcb : k = j)
      (hlc : l + 1 = k) :
    EvenTruthParity
      (DiagonalRepresents
        (BONG.GoodBONG.diagonalUnitCoefficients b)
        (BONG.GoodBONG.diagonalUnitCoefficients a))
      (DiagonalRepresents
        (BONG.GoodBONG.diagonalUnitCoefficients
          (diagonalUnitTake c l (by omega)))
        (BONG.GoodBONG.diagonalUnitCoefficients b))
      (DiagonalRepresents
        (BONG.GoodBONG.diagonalUnitCoefficients c)
        (BONG.GoodBONG.diagonalUnitCoefficients a))
      (hilbertSymbol K
        (BONG.GoodBONG.diagonalUnitDeterminant b *
          BONG.GoodBONG.diagonalUnitDeterminant c)
        (-BONG.GoodBONG.diagonalUnitDeterminant a *
          BONG.GoodBONG.diagonalUnitDeterminant
            (diagonalUnitTake c l (by omega))) = 1)

end Bong
