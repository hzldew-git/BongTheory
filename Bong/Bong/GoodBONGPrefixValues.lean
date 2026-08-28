/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Classification
import Bong.Bong.DiagonalRepresentationParity

/-!
# Unit-valued prefixes of a good BONG

This paper-independent module packages a finite good-BONG prefix as nonzero
diagonal coefficients and identifies its determinant with the BONG prefix
product.  Keeping these definitions below the 2009 and 2019 theorem modules
prevents the elementary diagonal determinant layer from depending on the
later classification arguments.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The first `k` good-BONG values, retained as nonzero field elements. -/
noncomputable def prefixValueUnits
    (a : GoodBONG q L (n + 1)) (k : Nat) (hk : k ≤ n + 1) :
    Fin k → Kˣ :=
  fun i ↦ a.valueUnit ⟨i.val, i.isLt.trans_le hk⟩

/-- A nonempty unit-valued prefix is obtained by appending its last BONG
value to the preceding prefix. -/
theorem prefixValueUnits_succ_eq_snoc
    (a : GoodBONG q L (n + 1)) (k : Nat) (hk : k + 1 ≤ n + 1) :
    a.prefixValueUnits (k + 1) hk =
      Fin.snoc (a.prefixValueUnits k (by omega))
        (a.valueUnit ⟨k, by omega⟩) := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [prefixValueUnits]
  · simp [prefixValueUnits]

@[simp]
theorem diagonalUnitCoefficients_prefixValueUnits
    (a : GoodBONG q L (n + 1)) (k : Nat) (hk : k ≤ n + 1) :
    diagonalUnitCoefficients (a.prefixValueUnits k hk) =
      a.prefixValues k hk := by
  rfl

/-- The determinant of the canonical diagonal prefix is its BONG prefix
product. -/
theorem diagonalUnitDeterminant_prefixValueUnits
    (a : GoodBONG q L (n + 1)) (k : Nat) (hk : k ≤ n + 1) :
    diagonalUnitDeterminant (a.prefixValueUnits k hk) =
      a.prefixProduct k := by
  induction k with
  | zero =>
      simp [diagonalUnitDeterminant, prefixValueUnits,
        GoodBONG.prefixProduct]
  | succ k ih =>
      unfold diagonalUnitDeterminant
      rw [Fin.prod_univ_castSucc]
      change
        (∏ i : Fin k, a.valueUnit ⟨i.val, by omega⟩) *
            a.valueUnit ⟨k, by omega⟩ =
          a.prefixProduct (k + 1)
      have hprefix :
          (∏ i : Fin k, a.valueUnit ⟨i.val, by omega⟩) =
            a.prefixProduct k := by
        simpa [diagonalUnitDeterminant, prefixValueUnits] using
          ih (by omega)
      rw [hprefix]
      unfold GoodBONG.prefixProduct
      exact (a.toBONG.prefixProduct_succ k (by omega)).symm

@[simp]
theorem diagonalUnitPrefix_prefixValueUnits
    (a : GoodBONG q L (n + 1)) (k : Nat) (hk : k + 1 ≤ n + 1) :
    diagonalUnitPrefix (a.prefixValueUnits (k + 1) hk) =
      a.prefixValueUnits k (by omega) := by
  funext i
  rfl

@[simp]
theorem diagonalUnitTake_prefixValueUnits
    (a : GoodBONG q L (n + 1)) (m k : Nat) (hm : m ≤ n + 1)
    (hk : k ≤ m) :
    diagonalUnitTake (a.prefixValueUnits m hm) k hk =
      a.prefixValueUnits k (hk.trans hm) := by
  funext i
  rfl

end BONG.GoodBONG

end Bong
