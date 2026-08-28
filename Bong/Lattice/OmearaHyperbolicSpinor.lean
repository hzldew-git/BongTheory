/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaHyperbolicTransvection
import Bong.Lattice.SpinorNorm

/-!
# Spinor norm of an integral Eichler transformation

The Wall residual space of a nontrivial Eichler transformation has an
explicit two-vector basis.  In that basis its Wall matrix has determinant
`4a²`, so its spinor norm is trivial, including when the complement vector
itself is isotropic.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

theorem integralSpinorNorm_hyperbolicEichlerLatticeIsometry_scaled
    (a : Kˣ) (z : V) (hzL : z ∈ L)
    (hzDual : z ∈ dualLattice (q.rescaleUnit a⁻¹) L)
    (s : K) (hquadratic : (q.rescaleUnit a⁻¹).quadratic z = 2 * s)
    (hs : s ∈ IntegerRing K) :
    integralSpinorNorm
        (hyperbolicEichlerLatticeIsometry_scaled
          a q L z hzL hzDual s hquadratic hs) = 1 := by
  letI : Module.Finite K V := L.moduleFinite
  let Q := (QuadraticSpace.hyperbolicPlane a).orthogonalSum q
  let q' := q.rescaleUnit a⁻¹
  let E : IntegralOrthogonalGroup Q
      (product (hyperbolicPlaneLattice (K := K)) L) :=
    hyperbolicEichlerLatticeIsometry_scaled
      a q L z hzL hzDual s hquadratic hs
  change QuadraticSpace.spinorNorm E.toQuadraticSpaceIsometry = 1
  have hEzero (x : (Fin 2 → K) × V) :
      (E.toLinearEquiv x).1 0 =
        x.1 0 - s * x.1 1 - q'.bilin x.2 z := by
    exact hyperbolicEichlerLatticeIsometry_scaled_apply_first_zero
      a z hzL hzDual s hquadratic hs x
  have hEone (x : (Fin 2 → K) × V) :
      (E.toLinearEquiv x).1 1 = x.1 1 := by
    exact hyperbolicEichlerLatticeIsometry_scaled_apply_first_one
      a z hzL hzDual s hquadratic hs x
  have hEsecond (x : (Fin 2 → K) × V) :
      (E.toLinearEquiv x).2 = x.2 + x.1 1 • z := by
    exact hyperbolicEichlerLatticeIsometry_scaled_apply_second
      a z hzL hzDual s hquadratic hs x
  by_cases hz : z = 0
  · subst z
    have hs0 : s = 0 := by
      rw [(q.rescaleUnit a⁻¹).quadratic_zero] at hquadratic
      have htwo : (2 : K) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp hquadratic.symm).resolve_left htwo
    subst s
    have hE : E.toQuadraticSpaceIsometry = QuadraticSpace.Isometry.refl Q := by
      apply QuadraticSpace.Isometry.ext
      intro x
      apply Prod.ext
      · funext i
        fin_cases i
        · change (E.toLinearEquiv x).1 0 = x.1 0
          rw [hEzero]
          simp
        · change (E.toLinearEquiv x).1 1 = x.1 1
          rw [hEone]
      · change (E.toLinearEquiv x).2 = x.2
        rw [hEsecond]
        simp
    rw [hE]
    exact QuadraticSpace.spinorNorm_refl
  · have hex : ∃ w : V, q'.bilin w z ≠ 0 := by
      by_contra h
      push Not at h
      apply hz
      apply q'.nondegenerate.1
      intro w
      rw [q'.isSymm.eq]
      exact h w
    obtain ⟨w₀, hw₀⟩ := hex
    let c : K := (q'.bilin w₀ z)⁻¹
    let w : V := c • w₀
    have hw : q'.bilin w z = 1 := by
      simp only [w, LinearMap.BilinForm.smul_left, c]
      exact inv_mul_cancel₀ hw₀
    let X : (Fin 2 → K) × V := (![0, 0], w)
    let Y : (Fin 2 → K) × V := (![0, 1], 0)
    let e := E.toQuadraticSpaceIsometry
    let residualFirst (x : (Fin 2 → K) × V) : Fin 2 → K :=
      Fin.cases (s * x.1 1 + q'.bilin x.2 z) (fun _ => 0)
    have hresidualCoe (x : (Fin 2 → K) × V) :
        ((QuadraticSpace.residualMap e x :
            QuadraticSpace.residualSpace e) : (Fin 2 → K) × V) =
          (residualFirst x, -(x.1 1 • z)) := by
      rw [QuadraticSpace.residualMap_coe]
      apply Prod.ext
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · change x.1 0 - (E.toLinearEquiv x).1 0 = _
          rw [hEzero]
          simp [residualFirst]
          ring
        · have hj : j = 0 := Subsingleton.elim j 0
          subst j
          change x.1 1 - (E.toLinearEquiv x).1 1 = 0
          rw [hEone]
          exact sub_self _
      · change x.2 - (E.toLinearEquiv x).2 = -(x.1 1 • z)
        rw [hEsecond]
        abel
    let u : QuadraticSpace.residualSpace e :=
      QuadraticSpace.residualMap e X
    let v : QuadraticSpace.residualSpace e :=
      QuadraticSpace.residualMap e Y
    have huCoe : (u : (Fin 2 → K) × V) = (![1, 0], 0) := by
      rw [show (u : (Fin 2 → K) × V) =
          (residualFirst X, -(X.1 1 • z)) by
        exact hresidualCoe X]
      apply Prod.ext
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [residualFirst, X, hw]
        · have hj : j = 0 := Subsingleton.elim j 0
          subst j
          simp [residualFirst, X]
          change @Fin.cases 1 (fun _ => K) (q'.bilin w z)
            (fun _ : Fin 1 => (0 : K)) (Fin.succ 0) = 0
          rfl
      · simp [X]
    have hvCoe : (v : (Fin 2 → K) × V) = (![s, 0], -z) := by
      rw [show (v : (Fin 2 → K) × V) =
          (residualFirst Y, -(Y.1 1 • z)) by
        exact hresidualCoe Y]
      apply Prod.ext
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [residualFirst, Y]
        · have hj : j = 0 := Subsingleton.elim j 0
          subst j
          simp [residualFirst, Y]
          change @Fin.cases 1 (fun _ => K) s
            (fun _ : Fin 1 => (0 : K)) (Fin.succ 0) = 0
          rfl
      · simp [Y]
    let family : Fin 2 → QuadraticSpace.residualSpace e := ![u, v]
    have hli : LinearIndependent K family := by
      rw [linearIndependent_fin2]
      constructor
      · intro hv0
        have hcoe := congrArg
          (fun t : QuadraticSpace.residualSpace e =>
            (t : (Fin 2 → K) × V)) hv0
        change (v : (Fin 2 → K) × V) = 0 at hcoe
        rw [hvCoe] at hcoe
        exact hz (neg_eq_zero.mp (congrArg Prod.snd hcoe))
      · intro d hd
        have hcoe := congrArg
          (fun t : QuadraticSpace.residualSpace e =>
            (t : (Fin 2 → K) × V)) hd
        change d • (v : (Fin 2 → K) × V) =
          (u : (Fin 2 → K) × V) at hcoe
        rw [huCoe, hvCoe] at hcoe
        have hsecond : d • (-z) = 0 := by
          simpa using congrArg Prod.snd hcoe
        have hd0 : d = 0 := by
          rcases smul_eq_zero.mp hsecond with hd | hz'
          · exact hd
          · exact False.elim (hz (neg_eq_zero.mp hz'))
        subst d
        have hfirst := congrArg (fun p : (Fin 2 → K) × V => p.1 0) hcoe
        simp at hfirst
    have hspan : ⊤ ≤ Submodule.span K (Set.range family) := by
      intro r _
      rcases r.property with ⟨x, hx⟩
      let d₀ : K := q'.bilin x.2 z
      let d₁ : K := x.1 1
      have hr : r = d₀ • u + d₁ • v := by
        apply Subtype.ext
        change (r : (Fin 2 → K) × V) =
          ((d₀ • u + d₁ • v : QuadraticSpace.residualSpace e) :
            (Fin 2 → K) × V)
        rw [← hx]
        change ((QuadraticSpace.residualMap e x :
            QuadraticSpace.residualSpace e) : (Fin 2 → K) × V) = _
        rw [hresidualCoe]
        apply Prod.ext
        · funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · simp [residualFirst, d₀, d₁, huCoe, hvCoe]
            ring
          · have hj : j = 0 := Subsingleton.elim j 0
            subst j
            simp [residualFirst, d₀, d₁, huCoe, hvCoe]
            change @Fin.cases 1 (fun _ => K)
              (s * x.1 1 + q'.bilin x.2 z)
                (fun _ : Fin 1 => (0 : K)) (Fin.succ 0) = 0
            rfl
        · simp [d₀, d₁, huCoe, hvCoe]
      rw [hr]
      apply Submodule.add_mem
      · exact Submodule.smul_mem _ _
          (Submodule.subset_span (Set.mem_range_self 0))
      · exact Submodule.smul_mem _ _
          (Submodule.subset_span (Set.mem_range_self 1))
    let b : Module.Basis (Fin 2) K (QuadraticSpace.residualSpace e) :=
      Module.Basis.mk hli hspan
    have hb0 : b 0 = u := by
      exact Module.Basis.mk_apply hli hspan 0
    have hb1 : b 1 = v := by
      exact Module.Basis.mk_apply hli hspan 1
    have hfin : Module.finrank K (QuadraticSpace.residualSpace e) = 2 := by
      simpa using Module.finrank_eq_card_basis b
    have hqa : q.bilin w z = (a : K) := by
      have hw' := hw
      change ((a⁻¹ : Kˣ) : K) * q.bilin w z = 1 at hw'
      have hw'' : (a : K)⁻¹ * q.bilin w z = 1 := by
        simpa only [Units.val_inv_eq_inv_val] using hw'
      exact ((inv_mul_eq_one₀ (Units.ne_zero a)).mp hw'').symm
    have h00 : QuadraticSpace.wallForm e (b 0) (b 0) = 0 := by
      rw [hb0, QuadraticSpace.wallForm_residualMap_left]
      simp [X, Q, huCoe, QuadraticSpace.orthogonalSum_bilin_apply,
        QuadraticSpace.hyperbolicPlane_bilin_apply]
    have h01 : QuadraticSpace.wallForm e (b 0) (b 1) =
        -(2 * (a : K)) := by
      rw [hb0, hb1, QuadraticSpace.wallForm_residualMap_left]
      simp [X, Q, hvCoe, QuadraticSpace.orthogonalSum_bilin_apply,
        QuadraticSpace.hyperbolicPlane_bilin_apply, hqa]
    have h10 : QuadraticSpace.wallForm e (b 1) (b 0) =
        2 * (a : K) := by
      rw [hb1, hb0, QuadraticSpace.wallForm_residualMap_left]
      simp [Y, Q, huCoe, QuadraticSpace.orthogonalSum_bilin_apply,
        QuadraticSpace.hyperbolicPlane_bilin_apply]
    have h11 : QuadraticSpace.wallForm e (b 1) (b 1) =
        2 * (a : K) * s := by
      rw [hb1, QuadraticSpace.wallForm_residualMap_left]
      simp [Y, Q, hvCoe, QuadraticSpace.orthogonalSum_bilin_apply,
        QuadraticSpace.hyperbolicPlane_bilin_apply]
      ring
    rw [QuadraticSpace.spinorNorm_eq_basisDeterminantOfFinrankEq e hfin b]
    have hdet : Matrix.det
        (LinearMap.BilinForm.toMatrix b (QuadraticSpace.wallForm e)) =
          (2 * (a : K)) ^ 2 := by
      rw [Matrix.det_fin_two]
      simp only [LinearMap.BilinForm.toMatrix_apply]
      rw [h00, h01, h10, h11]
      ring
    let twoA : Kˣ := Units.mk0 (2 * (a : K))
      (mul_ne_zero (by norm_num) (Units.ne_zero a))
    have hu : Units.mk0
        (Matrix.det
          (LinearMap.BilinForm.toMatrix b (QuadraticSpace.wallForm e)))
        ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1
          (QuadraticSpace.wallForm_nondegenerate e)) = twoA ^ 2 := by
      apply Units.ext
      exact hdet
    rw [hu]
    change squareClass K (twoA ^ 2) = squareClass K (1 : Kˣ)
    simpa only [one_mul] using squareClass_mul_square K (1 : Kˣ) twoA

end Lattice

end Bong
