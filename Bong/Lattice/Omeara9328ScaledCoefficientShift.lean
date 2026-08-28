/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaCoefficientShift
import Bong.Lattice.OrthogonalSumRescale

/-!
# O'Meara 93:19 at an arbitrary first-component scale

The constructive proof of 93:19 is normalized so that the binary plane is
unimodular.  A Jordan component normally has scale `a`.  Rescaling the
normalized identity by `a` gives the exact version used in 93:28, including
the modular parameter and norm-group containment for the new complement.
-/

namespace Bong

open Dyadic Module

namespace Lattice.Omeara9319ExchangeSetup

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {s a : Kˣ}

/-- Build the scalar package for 93:19 from a value represented by the
modular tail.  The quotient `gamma = delta / s` is integral because every
represented norm belongs to the scale ideal. -/
noncomputable def ofRepresentedScalar
    (hL : IsModular q L s) (hpos : 0 < finrank K V)
    (alpha beta delta : K)
    (halpha : alpha ∈ IntegerRing K)
    (hbeta : beta ∈ IntegerRing K)
    (hscale : IsInMaximalIdeal K (s : K))
    (hdet : IsValuationUnit K (alpha * beta - 1))
    (hdelta : delta ∈ normGroupSet q L) :
    Omeara9319ExchangeSetup q L s := by
  let gamma : K := ((s⁻¹ : Kˣ) : K) * delta
  have hdeltaScale : delta ∈ scaleIdeal q L :=
    normIdeal_le_scaleIdeal q L
      (normGroupSet_subset_normIdeal q L hdelta)
  have hdeltaPrincipal : delta ∈ principalIdeal (K := K) (s : K) := by
    rw [← hL.scaleIdeal_eq_principal hpos]
    exact hdeltaScale
  have hdeltaEq : delta = (s : K) * gamma := by
    dsimp [gamma]
    rw [Units.val_inv_eq_inv_val, ← mul_assoc,
      mul_inv_cancel₀ (Units.ne_zero s), one_mul]
  have hgamma : gamma ∈ IntegerRing K := by
    apply mem_integerRing_of_mul_mem_principalIdeal (Units.ne_zero s)
    rw [← hdeltaEq]
    exact hdeltaPrincipal
  have hscaleIntegral : (s : K) ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 (le_of_lt hscale)
  have hnewDeterminant :
      IsValuationUnit K ((alpha + (s : K) * gamma) * beta - 1) :=
    omearaExchangeDeterminant_isValuationUnit
      alpha beta gamma s hbeta hgamma hscale hdet
  exact
    { alpha := alpha
      beta := beta
      delta := delta
      gamma := gamma
      alpha_integral := halpha
      beta_integral := hbeta
      gamma_integral := hgamma
      scale_integral := hscaleIntegral
      old_determinant_unit := hdet
      new_determinant_unit := hnewDeterminant
      delta_mem := hdelta
      delta_eq := hdeltaEq }

@[simp] theorem ofRepresentedScalar_delta
    (hL : IsModular q L s) (hpos : 0 < finrank K V)
    (alpha beta delta : K)
    (halpha : alpha ∈ IntegerRing K)
    (hbeta : beta ∈ IntegerRing K)
    (hscale : IsInMaximalIdeal K (s : K))
    (hdet : IsValuationUnit K (alpha * beta - 1))
    (hdelta : delta ∈ normGroupSet q L) :
    (ofRepresentedScalar hL hpos alpha beta delta halpha hbeta hscale hdet hdelta).delta =
      delta := rfl

/-- Rescale the complete 93:19 identity back from normalized scale one. -/
noncomputable def shiftedRescale
    (E : Omeara9319ExchangeSetup q L s)
    (hL : IsModular q L s) (hrank : 3 ≤ finrank K V) (a : Kˣ) :
    Isometry
      ((E.oldPlane.rescaleUnit a).orthogonalSum (q.rescaleUnit a))
      ((E.newPlane.rescaleUnit a).orthogonalSum
        (((E.coefficientShift hL hrank).splitting.decomposition.component 1).space
          |>.rescaleUnit a))
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K))
        ((E.coefficientShift hL hrank).splitting.decomposition.component 1).lattice) := by
  let D := E.coefficientShift hL hrank
  exact (rescaleUnitOrthogonalProductIsometry E.oldPlane q
      (hyperbolicPlaneLattice (K := K)) L a).symm.trans <|
    (D.shifted.rescaleUnitBoth a).trans <|
      rescaleUnitOrthogonalProductIsometry E.newPlane
        (D.splitting.decomposition.component 1).space
        (hyperbolicPlaneLattice (K := K))
        (D.splitting.decomposition.component 1).lattice a

/-- The rescaled 93:19 complement is modular at the correspondingly
rescaled Jordan parameter. -/
theorem complement_modular_rescale
    (E : Omeara9319ExchangeSetup q L s)
    (hL : IsModular q L s) (hrank : 3 ≤ finrank K V) (a : Kˣ) :
    IsModular
      (((E.coefficientShift hL hrank).splitting.decomposition.component 1).space
        |>.rescaleUnit a)
      ((E.coefficientShift hL hrank).splitting.decomposition.component 1).lattice
      (a * s) :=
  (E.coefficientShift hL hrank).splitting.complement_modular
    |>.rescaleQuadraticUnit a

/-- The norm-group containment in 93:19 is preserved by common form
rescaling. -/
theorem normGroupSet_subset_complement_rescale
    (E : Omeara9319ExchangeSetup q L s)
    (hL : IsModular q L s) (hrank : 3 ≤ finrank K V) (a : Kˣ) :
    normGroupSet (q.rescaleUnit a) L ⊆
      normGroupSet
        (((E.coefficientShift hL hrank).splitting.decomposition.component 1).space
          |>.rescaleUnit a)
        ((E.coefficientShift hL hrank).splitting.decomposition.component 1).lattice := by
  intro z hz
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff] at hz ⊢
  exact (E.coefficientShift hL hrank).normGroup_subset hz

end Lattice.Omeara9319ExchangeSetup

end Bong
