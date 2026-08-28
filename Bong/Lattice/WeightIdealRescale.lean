/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009WeightIdealIsometry
import Bong.Lattice.OmearaModularNormClassification
import Bong.Lattice.OmearaFundamentalIdeals
import Bong.Lattice.LatticeRescaleIsometry

/-!
# Weight ideals under scalar rescaling

Multiplying a quadratic form by a nonzero scalar multiplies its weight ideal
by the same scalar.  At the level of the selected integral order this is an
additive valuation shift.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Multiplying a quadratic form by a field unit shifts the selected
weight order by the valuation of that unit. -/
theorem weightIdealOrder_rescaleQuadraticUnit
    (a c : Kˣ) (ha : IsNormGeneratorValue q L a) :
    weightIdealOrder (q.rescaleUnit c) L =
      ordUnit K c + weightIdealOrder q L := by
  let W : Int := ordUnit K c + weightIdealOrder q L
  let w : OrderedFractionalIdeal K :=
    { carrier := powerIdeal (K := K) W
      order := W
      carrier_eq_powerIdeal := rfl }
  have htwo : twoScaleIdeal (q.rescaleUnit c) L ≤ w.carrier := by
    change twoScaleIdeal (q.rescaleUnit c) L ≤ powerIdeal (K := K) W
    rw [twoScaleIdeal_rescaleQuadraticUnit,
      show powerIdeal (K := K) W =
        scalarIdeal (c : K) (weightIdeal q L) by
          rw [weightIdeal_eq_powerIdeal,
            scalarIdeal_powerIdeal_units]]
    exact Submodule.map_mono (twoScaleIdeal_le_weightIdeal q L)
  have hgroup : normGroupSet (q.rescaleUnit c) L =
      integralSquareCoset ((c * a : Kˣ) : K) w.carrier := by
    ext z
    rw [mem_normGroupSet_rescaleQuadraticUnit_iff,
      normGroupSet_eq_integralSquareCoset_weightIdeal a ha]
    constructor
    · rintro ⟨d, y, hy, hzy⟩
      let y' : K := (c : K) * y
      have hy' : y' ∈ w.carrier := by
        change y' ∈ powerIdeal (K := K) W
        rw [mem_powerIdeal_iff]
        dsimp only [y']
        rw [ord_mul]
        have hyOrder :
            ((weightIdealOrder q L : Int) : WithTop Int) ≤ ord K y := by
          rw [weightIdeal_eq_powerIdeal, mem_powerIdeal_iff] at hy
          exact hy
        rw [← coe_ordUnit]
        change (((ordUnit K c + weightIdealOrder q L : Int) :
          WithTop Int)) ≤
            ((ordUnit K c : Int) : WithTop Int) + ord K y
        simpa only [WithTop.coe_add, add_comm] using
          add_le_add_left hyOrder ((ordUnit K c : Int) : WithTop Int)
      refine ⟨d, y', hy', ?_⟩
      calc
        z = (c : K) * (((c⁻¹ : Kˣ) : K) * z) := by
          symm
          calc
            (c : K) * (((c⁻¹ : Kˣ) : K) * z) =
                ((c : K) * ((c : K)⁻¹)) * z := by
              simp only [Units.val_inv_eq_inv_val]
              ring
            _ = z := by rw [mul_inv_cancel₀ (Units.ne_zero c), one_mul]
        _ = (c : K) * ((a : K) * (d : K) ^ 2 + y) := by rw [hzy]
        _ = ((c * a : Kˣ) : K) * (d : K) ^ 2 + y' := by
          simp only [Units.val_mul]
          dsimp only [y']
          ring
    · rintro ⟨d, y, hy, hzy⟩
      let y' : K := ((c⁻¹ : Kˣ) : K) * y
      have hy' : y' ∈ weightIdeal q L := by
        rw [weightIdeal_eq_powerIdeal, mem_powerIdeal_iff]
        change ((weightIdealOrder q L : Int) : WithTop Int) ≤ ord K y'
        dsimp only [y']
        rw [ord_mul, ← coe_ordUnit, ordUnit_inv]
        have hyOrder : ((W : Int) : WithTop Int) ≤ ord K y := by
          exact (mem_powerIdeal_iff (K := K) W y).1 hy
        change ((weightIdealOrder q L : Int) : WithTop Int) ≤
          ((-ordUnit K c : Int) : WithTop Int) + ord K y
        have hEq : -ordUnit K c + W = weightIdealOrder q L := by
          dsimp only [W]
          omega
        rw [← hEq, WithTop.coe_add]
        simpa only [add_comm] using
          add_le_add_left hyOrder
            ((-ordUnit K c : Int) : WithTop Int)
      refine ⟨d, y', hy', ?_⟩
      calc
        ((c⁻¹ : Kˣ) : K) * z =
            ((c⁻¹ : Kˣ) : K) *
              (((c * a : Kˣ) : K) * (d : K) ^ 2 + y) := by rw [hzy]
        _ = (a : K) * (d : K) ^ 2 + y' := by
          simp only [Units.val_inv_eq_inv_val, Units.val_mul]
          dsimp only [y']
          calc
            (c : K)⁻¹ * ((c : K) * (a : K) * (d : K) ^ 2 + y) =
                ((c : K)⁻¹ * (c : K)) *
                    ((a : K) * (d : K) ^ 2) + (c : K)⁻¹ * y := by ring
            _ = (a : K) * (d : K) ^ 2 +
                ((c⁻¹ : Kˣ) : K) * y := by
              rw [Units.val_inv_eq_inv_val,
                inv_mul_cancel₀ (Units.ne_zero c), one_mul]
  have hparity : w.carrier = twoScaleIdeal (q.rescaleUnit c) L ∨
      Odd (ordUnit K (c * a) + w.order) := by
    rcases weightIdeal_eq_twoScale_or_odd a ha with hterminal | hodd
    · left
      change powerIdeal (K := K) W = twoScaleIdeal (q.rescaleUnit c) L
      rw [twoScaleIdeal_rescaleQuadraticUnit, ← hterminal,
        weightIdeal_eq_powerIdeal, scalarIdeal_powerIdeal_units]
    · right
      rcases hodd with ⟨m, hm⟩
      refine ⟨m + ordUnit K c, ?_⟩
      dsimp only [w, W]
      rw [ordUnit_mul]
      omega
  have hw : w.carrier = weightIdeal (q.rescaleUnit c) L :=
    (beli2009Lemma210 (c * a) (ha.rescaleQuadraticUnit c) w htwo).2
      ⟨hgroup, hparity⟩
  apply powerIdeal_order_eq_of_eq (K := K)
  calc
    powerIdeal (K := K) (weightIdealOrder (q.rescaleUnit c) L) =
        weightIdeal (q.rescaleUnit c) L :=
      (weightIdeal_eq_powerIdeal _ _).symm
    _ = w.carrier := hw.symm
    _ = powerIdeal (K := K) W := rfl

/-- Rescaling the lattice by `c` shifts its weight order by twice the
valuation of `c`. -/
theorem weightIdealOrder_rescaleLattice
    (q : QuadraticSpace K V) (L : Lattice K V) (c : Kˣ)
    (hpos : 0 < Module.finrank K V) :
    weightIdealOrder q (rescale c L) =
      2 * ordUnit K c + weightIdealOrder q L := by
  rcases exists_isNormGenerator_of_finrank_pos q L hpos with
    ⟨x, hx, hxne⟩
  let a : Kˣ := Units.mk0 (q.quadratic x) hxne
  have ha : IsNormGeneratorValue q L a :=
    hx.isNormGeneratorValue hxne
  let f := scalarMultiplicationRescaleLatticeIsometry q L c
  calc
    weightIdealOrder q (rescale c L) =
        weightIdealOrder (q.rescaleUnit (c ^ 2)) L :=
      weightIdealOrder_eq_of_isometry f hpos
    _ = ordUnit K (c ^ 2) + weightIdealOrder q L :=
      weightIdealOrder_rescaleQuadraticUnit a (c ^ 2) ha
    _ = 2 * ordUnit K c + weightIdealOrder q L := by
      rw [ordUnit_pow]
      ring

end Lattice

end Bong
