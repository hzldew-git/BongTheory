/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.DVRFactorization
import Bong.Lattice.VolumeRigidity

/-!
# Volume orders of nested lattices

The determinant of an inclusion matrix is a nonzero integral scalar.  DVR
factorization therefore writes the volume-order difference of two nested
full lattices as twice a natural number.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- A lattice inclusion changes the volume order by twice a nonnegative
integer. -/
theorem exists_volumeOrder_eq_add_two_mul_nat
    (q : QuadraticSpace K V) {N M : Lattice K V} (hNM : N ≤ M) :
    ∃ k : Nat,
      volumeOrder q N = volumeOrder q M + 2 * (k : Int) := by
  let d : IntegerRing K := (inclusionMatrix hNM).det
  have hdne : d ≠ 0 := by
    intro hzero
    have hdet := determinant_eq_mul_sq_inclusionMatrix_det q hNM
    change determinant q N =
      determinant q M * ((d : IntegerRing K) : K) ^ 2 at hdet
    rw [hzero] at hdet
    apply determinant_ne_zero q N
    simpa using hdet
  rcases exists_eq_uniformizerInteger_pow_mul_unit K d hdne with
    ⟨k, u, hfactor⟩
  refine ⟨k, ?_⟩
  have hdOrder : ord K ((d : IntegerRing K) : K) =
      ((k : Int) : WithTop Int) := by
    have hfactorK : ((d : IntegerRing K) : K) =
        uniformizer K ^ k *
          ((((u : (IntegerRing K)ˣ) : IntegerRing K) : K)) := by
      simpa [coe_uniformizerInteger] using
        congrArg (fun z : IntegerRing K ↦ (z : K)) hfactor
    have hu := isValuationUnit_coe_integerRingUnit u
    change ord K ((((u : (IntegerRing K)ˣ) : IntegerRing K) : K)) = 0 at hu
    rw [hfactorK, ord_mul, ord_pow, ord_uniformizer, hu]
    norm_num
  apply WithTop.coe_injective
  change (volumeOrder q N : WithTop Int) =
    (volumeOrder q M : WithTop Int) + 2 * ((k : Int) : WithTop Int)
  rw [coe_volumeOrder, coe_volumeOrder]
  have hdet := determinant_eq_mul_sq_inclusionMatrix_det q hNM
  change determinant q N =
    determinant q M * ((d : IntegerRing K) : K) ^ 2 at hdet
  rw [hdet, ord_mul, ord_pow, hdOrder]
  norm_cast

/-- Volume order is monotone in the reverse direction of lattice
inclusion. -/
theorem volumeOrder_mono_of_le
    (q : QuadraticSpace K V) {N M : Lattice K V} (hNM : N ≤ M) :
    volumeOrder q M ≤ volumeOrder q N := by
  rcases exists_volumeOrder_eq_add_two_mul_nat q hNM with ⟨k, hk⟩
  rw [hk]
  omega

end Lattice

end Bong
