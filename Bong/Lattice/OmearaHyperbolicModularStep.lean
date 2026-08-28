/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaHyperbolicCancellation
import Bong.Lattice.OmearaPrimitiveIsotropicSplitting
import Bong.Lattice.OrthogonalProductIsometry
import Bong.Lattice.ProjectionScaling

/-!
# Splitting a modular lattice on a hyperbolic summand

This file is the recursive field-space step behind the use of O'Meara 82:16
in Corollary 93:14a.  For an `a`-modular lattice on `H ⟂ W`, the first
isotropic line is scaled to a primitive lattice vector and split off as an
`a A(alpha,0)` plane.  Its orthogonal complement is identified explicitly
with `W` by a graph map; no Witt-cancellation law is assumed.
-/

namespace Bong

open Dyadic
open Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {W : Type v} [AddCommGroup W] [Module K W]

/-- The distinguished isotropic vector in the first hyperbolic summand. -/
def hyperbolicFirstInSum : (Fin 2 → K) × W :=
  (omearaHyperbolicFirst (K := K), 0)

theorem hyperbolicFirstInSum_ne :
    hyperbolicFirstInSum (K := K) (W := W) ≠ 0 := by
  intro hzero
  have hcoordinate := congrArg (fun z : (Fin 2 → K) × W ↦ z.1 0) hzero
  simpa [hyperbolicFirstInSum, omearaHyperbolicFirst] using hcoordinate

theorem hyperbolicFirstInSum_isotropic (r : QuadraticSpace K W) :
    ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r).quadratic
      (hyperbolicFirstInSum (K := K) (W := W)) = 0 := by
  change
    (QuadraticSpace.hyperbolicPlane (1 : Kˣ)).bilin
        (omearaHyperbolicFirst (K := K))
        (omearaHyperbolicFirst (K := K)) + r.bilin 0 0 = 0
  rw [QuadraticSpace.hyperbolicPlane_bilin_apply]
  simp [omearaHyperbolicFirst]

/-- The 82:16 data selected from the first isotropic line of `H ⟂ W`. -/
noncomputable def hyperbolicModularLineData
    (r : QuadraticSpace K W)
    (L : Lattice K ((Fin 2 → K) × W)) (a : Kˣ)
    (hmodular : IsModular
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a) :
    Omeara8216LineData
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a
      (hyperbolicFirstInSum (K := K) (W := W)) :=
  omeara8216LineData hmodular hyperbolicFirstInSum_ne

namespace Omeara8216LineData

variable {r : QuadraticSpace K W}
  {L : Lattice K ((Fin 2 → K) × W)} {a : Kˣ}

/-- The second hyperbolic coordinate of the 82:16 partner is nonzero. -/
theorem hyperbolic_partner_one_ne
    (E : Omeara8216LineData
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a
      (hyperbolicFirstInSum (K := K) (W := W))) :
    E.pairingData.partner.1 1 ≠ 0 := by
  intro hone
  have hpair : (E.scale : K) * E.pairingData.partner.1 1 = (a : K) := by
    calc
      (E.scale : K) * E.pairingData.partner.1 1 =
          ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r).bilin
            E.vector E.pairingData.partner := by
        simp [Omeara8216LineData.vector, hyperbolicFirstInSum,
          QuadraticSpace.orthogonalSum_bilin_apply,
          QuadraticSpace.hyperbolicPlane_bilin_apply,
          omearaHyperbolicFirst]
      _ = (a : K) := E.pairingData.pairing_eq
  rw [hone, mul_zero] at hpair
  exact Units.ne_zero a hpair.symm

/-- The graph map from the old complement into the complement of the plane
selected by 82:16. -/
noncomputable def hyperbolicComplementGraphLinearMap
    (E : Omeara8216LineData
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a
      (hyperbolicFirstInSum (K := K) (W := W))) :
    W →ₗ[K] ((Fin 2 → K) × W) where
  toFun w :=
    ((-(r.bilin E.pairingData.partner.2 w) /
        E.pairingData.partner.1 1) •
      omearaHyperbolicFirst (K := K), w)
  map_add' x y := by
    apply Prod.ext
    · funext i
      fin_cases i <;>
        simp [omearaHyperbolicFirst,
          LinearMap.BilinForm.add_right] <;> ring
    · simp
  map_smul' c x := by
    apply Prod.ext
    · funext i
      fin_cases i <;>
        simp [omearaHyperbolicFirst,
          LinearMap.BilinForm.smul_right] <;> ring
    · simp

@[simp]
theorem hyperbolicComplementGraphLinearMap_apply_second
    (E : Omeara8216LineData
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a
      (hyperbolicFirstInSum (K := K) (W := W))) (w : W) :
    (E.hyperbolicComplementGraphLinearMap w).2 = w :=
  rfl

theorem bilin_vector_hyperbolicComplementGraph_zero
    (E : Omeara8216LineData
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a
      (hyperbolicFirstInSum (K := K) (W := W))) (w : W) :
    ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r).bilin
      E.vector (E.hyperbolicComplementGraphLinearMap w) = 0 := by
  simp only [Omeara8216LineData.vector]
  rw [QuadraticSpace.orthogonalSum_bilin_apply,
    QuadraticSpace.hyperbolicPlane_bilin_apply]
  simp [hyperbolicFirstInSum, omearaHyperbolicFirst,
    hyperbolicComplementGraphLinearMap]

theorem bilin_partner_hyperbolicComplementGraph_zero
    (E : Omeara8216LineData
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a
      (hyperbolicFirstInSum (K := K) (W := W))) (w : W) :
    ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r).bilin
      E.pairingData.partner (E.hyperbolicComplementGraphLinearMap w) = 0 := by
  rw [QuadraticSpace.orthogonalSum_bilin_apply,
    QuadraticSpace.hyperbolicPlane_bilin_apply]
  simp [hyperbolicComplementGraphLinearMap, omearaHyperbolicFirst]
  field_simp [E.hyperbolic_partner_one_ne]
  ring

/-- The specialized 82:16 splitting on the first hyperbolic line. -/
noncomputable def hyperbolicSplitting
    (E : Omeara8216LineData
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a
      (hyperbolicFirstInSum (K := K) (W := W)))
    (hmodular : IsModular
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a) :
    OrthogonalDecomposition
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L 2 :=
  E.splitting hmodular (hyperbolicFirstInSum_isotropic r)

/-- The graph vector belongs to the orthogonal complement of the binary
plane selected by 82:16. -/
noncomputable def hyperbolicComplementGraph
    (E : Omeara8216LineData
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a
      (hyperbolicFirstInSum (K := K) (W := W)))
    (hmodular : IsModular
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a)
    (w : W) : (E.hyperbolicSplitting hmodular).component 1 |>.carrier := by
  let g := E.hyperbolicComplementGraphLinearMap w
  refine ⟨g, ?_⟩
  change g ∈
    (E.pairingData.component hmodular
      (E.vector_isotropic (hyperbolicFirstInSum_isotropic r))).orthogonalCarrier
  intro z hz
  change z ∈ BONG.binaryPairSpan (K := K)
    E.vector E.pairingData.partner at hz
  refine Submodule.span_induction
    (p := fun z _ ↦
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r).bilin
        z g = 0) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact E.bilin_vector_hyperbolicComplementGraph_zero w
    · exact E.bilin_partner_hyperbolicComplementGraph_zero w
  · simp
  · intro x y _ _ hx hy
    rw [LinearMap.BilinForm.add_left, hx, hy, add_zero]
  · intro c x _ hx
    rw [LinearMap.BilinForm.smul_left, hx]
    simp

/-- The graph construction as a linear map into the new orthogonal
complement. -/
noncomputable def hyperbolicComplementGraphToOrthogonalLinearMap
    (E : Omeara8216LineData
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a
      (hyperbolicFirstInSum (K := K) (W := W)))
    (hmodular : IsModular
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a) :
    W →ₗ[K] (E.hyperbolicSplitting hmodular).component 1 |>.carrier where
  toFun := E.hyperbolicComplementGraph hmodular
  map_add' x y := by
    apply Subtype.ext
    exact E.hyperbolicComplementGraphLinearMap.map_add x y
  map_smul' c x := by
    apply Subtype.ext
    exact E.hyperbolicComplementGraphLinearMap.map_smul c x

/-- Projection of the new graph complement back to the old complement. -/
noncomputable def hyperbolicComplementProjectionLinearMap
    (E : Omeara8216LineData
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a
      (hyperbolicFirstInSum (K := K) (W := W)))
    (hmodular : IsModular
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a) :
    ((E.hyperbolicSplitting hmodular).component 1 |>.carrier) →ₗ[K] W :=
  (LinearMap.snd K (Fin 2 → K) W).comp
    ((E.hyperbolicSplitting hmodular).component 1 |>.carrier).subtype

@[simp]
theorem hyperbolicComplementProjection_graph
    (E : Omeara8216LineData
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a
      (hyperbolicFirstInSum (K := K) (W := W)))
    (hmodular : IsModular
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a)
    (w : W) :
    E.hyperbolicComplementProjectionLinearMap hmodular
        (E.hyperbolicComplementGraphToOrthogonalLinearMap hmodular w) = w :=
  rfl

/-- A vector in the new orthogonal complement is recovered from its old
complement coordinate by the graph construction. -/
theorem hyperbolicComplementGraph_projection
    (E : Omeara8216LineData
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a
      (hyperbolicFirstInSum (K := K) (W := W)))
    (hmodular : IsModular
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a)
    (z : (E.hyperbolicSplitting hmodular).component 1 |>.carrier) :
    E.hyperbolicComplementGraphToOrthogonalLinearMap hmodular
        (E.hyperbolicComplementProjectionLinearMap hmodular z) = z := by
  let hisotropic := E.vector_isotropic (hyperbolicFirstInSum_isotropic r)
  let C := E.pairingData.component hmodular hisotropic
  have hvectorMem : E.vector ∈ C.carrier := by
    change E.vector ∈ BONG.binaryPairSpan (K := K)
      E.vector E.pairingData.partner
    apply Submodule.subset_span
    exact ⟨0, rfl⟩
  have hpartnerMem : E.pairingData.partner ∈ C.carrier := by
    change E.pairingData.partner ∈ BONG.binaryPairSpan (K := K)
      E.vector E.pairingData.partner
    apply Submodule.subset_span
    exact ⟨1, rfl⟩
  have hvectorOrth :
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r).bilin
        E.vector z = 0 := by
    exact z.property E.vector hvectorMem
  have hcoordinateOne : (z : (Fin 2 → K) × W).1 1 = 0 := by
    have hproduct : (E.scale : K) * (z : (Fin 2 → K) × W).1 1 = 0 := by
      calc
        (E.scale : K) * (z : (Fin 2 → K) × W).1 1 =
            ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r).bilin
              E.vector z := by
          simp [Omeara8216LineData.vector, hyperbolicFirstInSum,
            QuadraticSpace.orthogonalSum_bilin_apply,
            QuadraticSpace.hyperbolicPlane_bilin_apply,
            omearaHyperbolicFirst]
        _ = 0 := hvectorOrth
    exact (mul_eq_zero.mp hproduct).resolve_left (Units.ne_zero E.scale)
  have hpartnerOrth :
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r).bilin
        E.pairingData.partner z = 0 := by
    exact z.property E.pairingData.partner hpartnerMem
  have hcoordinateZero :
      (z : (Fin 2 → K) × W).1 0 =
        -(r.bilin E.pairingData.partner.2
          (z : (Fin 2 → K) × W).2) /
            E.pairingData.partner.1 1 := by
    have hsum :
        E.pairingData.partner.1 1 * (z : (Fin 2 → K) × W).1 0 +
          r.bilin E.pairingData.partner.2
            (z : (Fin 2 → K) × W).2 = 0 := by
      simpa [QuadraticSpace.orthogonalSum_bilin_apply,
        QuadraticSpace.hyperbolicPlane_bilin_apply,
        hcoordinateOne] using hpartnerOrth
    apply (eq_div_iff E.hyperbolic_partner_one_ne).2
    rw [mul_comm]
    linear_combination hsum
  apply Subtype.ext
  apply Prod.ext
  · funext i
    fin_cases i
    · simpa [hyperbolicComplementGraphToOrthogonalLinearMap,
        hyperbolicComplementGraph, hyperbolicComplementProjectionLinearMap,
        hyperbolicComplementGraphLinearMap,
        omearaHyperbolicFirst] using hcoordinateZero.symm
    · simpa [hyperbolicComplementGraphToOrthogonalLinearMap,
        hyperbolicComplementGraph, hyperbolicComplementGraphLinearMap,
        omearaHyperbolicFirst] using hcoordinateOne.symm
  · rfl

/-- The old complement is linearly equivalent to the complement of the
binary plane selected by 82:16. -/
noncomputable def hyperbolicComplementLinearEquiv
    (E : Omeara8216LineData
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a
      (hyperbolicFirstInSum (K := K) (W := W)))
    (hmodular : IsModular
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a) :
    W ≃ₗ[K] (E.hyperbolicSplitting hmodular).component 1 |>.carrier :=
  LinearEquiv.ofLinear
    (E.hyperbolicComplementGraphToOrthogonalLinearMap hmodular)
    (E.hyperbolicComplementProjectionLinearMap hmodular)
    (by
      apply LinearMap.ext
      intro z
      exact E.hyperbolicComplementGraph_projection hmodular z)
    (by
      apply LinearMap.ext
      intro w
      exact E.hyperbolicComplementProjection_graph hmodular w)

/-- The complement equivalence preserves the bilinear forms. -/
theorem hyperbolicComplementLinearEquiv_map_bilin
    (E : Omeara8216LineData
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a
      (hyperbolicFirstInSum (K := K) (W := W)))
    (hmodular : IsModular
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a)
    (x y : W) :
    ((E.hyperbolicSplitting hmodular).component 1).space.bilin
        (E.hyperbolicComplementLinearEquiv hmodular x)
        (E.hyperbolicComplementLinearEquiv hmodular y) = r.bilin x y := by
  change
    ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r).bilin
      (E.hyperbolicComplementGraphLinearMap x)
      (E.hyperbolicComplementGraphLinearMap y) = r.bilin x y
  rw [QuadraticSpace.orthogonalSum_bilin_apply,
    QuadraticSpace.hyperbolicPlane_bilin_apply]
  simp [hyperbolicComplementGraphLinearMap, omearaHyperbolicFirst]

/-- The new orthogonal complement is genuinely isometric to the old
quadratic-space complement.  This is the cancellation-free recursive step
needed in 93:14a. -/
noncomputable def hyperbolicComplementSpaceIsometry
    (E : Omeara8216LineData
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a
      (hyperbolicFirstInSum (K := K) (W := W)))
    (hmodular : IsModular
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a) :
    QuadraticSpace.Isometry r
      ((E.hyperbolicSplitting hmodular).component 1).space where
  toLinearEquiv := E.hyperbolicComplementLinearEquiv hmodular
  map_bilin := E.hyperbolicComplementLinearEquiv_map_bilin hmodular

/-- Pull the complement lattice back to the old quadratic-space tail. -/
noncomputable def hyperbolicTailLattice
    (E : Omeara8216LineData
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a
      (hyperbolicFirstInSum (K := K) (W := W)))
    (hmodular : IsModular
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a) :
    Lattice K W :=
  map (E.hyperbolicComplementSpaceIsometry hmodular).toLinearEquiv.symm
    ((E.hyperbolicSplitting hmodular).component 1).lattice

/-- The new complement lattice and its pullback to the old tail are
integrally isometric. -/
noncomputable def hyperbolicComplementLatticeIsometry
    (E : Omeara8216LineData
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a
      (hyperbolicFirstInSum (K := K) (W := W)))
    (hmodular : IsModular
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a) :
    Isometry
      ((E.hyperbolicSplitting hmodular).component 1).space r
      ((E.hyperbolicSplitting hmodular).component 1).lattice
      (E.hyperbolicTailLattice hmodular) :=
  Isometry.toMap ((E.hyperbolicSplitting hmodular).component 1).space
    (E.hyperbolicComplementSpaceIsometry hmodular).symm
    ((E.hyperbolicSplitting hmodular).component 1).lattice

/-- The pulled-back tail lattice remains `a`-modular. -/
theorem hyperbolicTailLattice_modular
    (E : Omeara8216LineData
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a
      (hyperbolicFirstInSum (K := K) (W := W)))
    (hmodular : IsModular
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a) :
    IsModular r (E.hyperbolicTailLattice hmodular) a :=
  (E.complement_modular hmodular
      (hyperbolicFirstInSum_isotropic r)).mapLatticeIsometry
    (E.hyperbolicComplementLatticeIsometry hmodular)

/-- One recursive 82:16 step, expressed entirely on the original tail type:
the ambient modular lattice is isometric to `a A(alpha,0)` orthogonally
summed with another `a`-modular lattice on `W`. -/
noncomputable def hyperbolicModularStepIsometry
    (E : Omeara8216LineData
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a
      (hyperbolicFirstInSum (K := K) (W := W)))
    (hmodular : IsModular
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) L a) :
    Isometry
      (((QuadraticSpace.omearaPlane
          E.pairingData.planeCoefficient).rescaleUnit a).orthogonalSum r)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K))
        (E.hyperbolicTailLattice hmodular)) L :=
  ((E.planeIsometry hmodular (hyperbolicFirstInSum_isotropic r)).orthogonalProductBasic
      (E.hyperbolicComplementLatticeIsometry hmodular).symm).trans
    (E.hyperbolicSplitting hmodular).pairProductLatticeIsometry

end Omeara8216LineData

end Lattice

end Bong
