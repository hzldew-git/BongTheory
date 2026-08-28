/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9318EvenParity
import Bong.Lattice.OmearaModularNormClassification

/-!
# Transporting O'Meara 93:18 across a modular-scale normalization

O'Meara routinely multiplies the ambient form by the inverse of the modular
scale, proves the unimodular assertion, and scales back.  This file packages
that operation for the concrete `Omeara9318vData` output.  It is a literal
transport of a displayed integral isometry and introduces no local law.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Omeara9318vData

/-- Transport a displayed hyperbolic summand back after multiplying the
ambient form by `c`.  The modular parameter in the rescaled form is `c * a`,
so the hyperbolic plane and the complementary form both scale back by
`c⁻¹`. -/
noncomputable def unscaleQuadraticUnit
    (c a : Kˣ) (hmodular : IsModular q L a)
    (D : Omeara9318vData (q.rescaleUnit c) L (c * a)) :
    Omeara9318vData q L a := by
  let C := D.decomposition.component 1
  let r : QuadraticSpace K C.carrier := C.space.rescaleUnit c⁻¹
  let f := D.displayedIsometry
  let displayed : Isometry q
      ((QuadraticSpace.hyperbolicPlane a).orthogonalSum r)
      L (product (hyperbolicPlaneLattice (K := K)) C.lattice) :=
    { toLinearEquiv := f.toLinearEquiv
      map_bilin := by
        intro x y
        have h := f.map_bilin x y
        have hc : (c : K) ≠ 0 := Units.ne_zero c
        calc
          ((QuadraticSpace.hyperbolicPlane a).orthogonalSum r).bilin
              (f.toLinearEquiv x) (f.toLinearEquiv y) =
              ((c⁻¹ : Kˣ) : K) *
                (((QuadraticSpace.hyperbolicPlane (c * a)).orthogonalSum
                    C.space).bilin
                  (f.toLinearEquiv x) (f.toLinearEquiv y)) := by
            simp only [QuadraticSpace.orthogonalSum_bilin_apply,
              QuadraticSpace.hyperbolicPlane_bilin_apply,
              QuadraticSpace.rescaleUnit_bilin_apply, r,
              Units.val_inv_eq_inv_val, Units.val_mul]
            field_simp
          _ = ((c⁻¹ : Kˣ) : K) *
                (q.rescaleUnit c).bilin x y := by rw [h]
          _ = q.bilin x y := by
            simp only [QuadraticSpace.rescaleUnit_bilin_apply,
              Units.val_inv_eq_inv_val]
            field_simp
      map_mem := f.map_mem }
  exact Omeara9318vData.ofDisplayedIsometry r C.lattice
    hmodular displayed

end Omeara9318vData

/-- Scale-normalized form of O'Meara 93:18(ii).  The norm generator and
weight parity are stated in the normalized unimodular form, exactly as they
are used after O'Meara's phrase "by scaling we may assume". -/
noncomputable def omeara9318iiData_of_modular
    (s : Kˣ) (hmodular : IsModular q L s)
    (hrank : 3 ≤ finrank K V)
    (b : Kˣ)
    (hb : IsNormGeneratorValue (q.rescaleUnit s⁻¹) L b)
    (heven : Even
      (ordUnit K b + weightIdealOrder (q.rescaleUnit s⁻¹) L)) :
    Omeara9318vData q L s := by
  let D₀ := omeara9318iiData
    hmodular.isUnimodular_rescaleQuadraticInverse hrank b hb heven
  have hscale : s⁻¹ * s = (1 : Kˣ) := by simp
  let D : Omeara9318vData (q.rescaleUnit s⁻¹) L (s⁻¹ * s) := by
    simpa only [hscale] using D₀
  exact D.unscaleQuadraticUnit s⁻¹ s hmodular

end Lattice

end Bong
