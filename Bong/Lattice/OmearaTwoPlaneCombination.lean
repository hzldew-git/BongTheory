/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaBinaryExchange
import Bong.Lattice.OmearaHyperbolicTransvection

/-!
# Combining two O'Meara planes

The last step of O'Meara 93:18(v) combines two binary modular blocks.
The integral four-dimensional exchange sends

`A(alpha + gamma, 0) ⊥ A(-gamma, 0)`

to

`A(alpha, 0) ⊥ A(gamma, 0)`.

Consequently, if `alpha + gamma = 2 * eta` with `eta` integral, the first
plane on the left is hyperbolic by O'Meara 93:10.  All maps below are
explicit integral changes of basis.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The identity coordinates identify `A(alpha,0)` in the two notations,
including their common standard lattice. -/
noncomputable def omearaGeneralPlaneZeroRightLatticeIsometry (alpha : K) :
    Isometry
      (QuadraticSpace.omearaGeneralPlane alpha 0 (by simp))
      (QuadraticSpace.omearaPlane alpha)
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) where
  toLinearEquiv := LinearEquiv.refl K (Fin 2 → K)
  map_bilin :=
    (QuadraticSpace.omearaGeneralPlaneZeroRightIsometry alpha).map_bilin
  map_mem _ := Iff.rfl

/-- For `beta = 0` and exchange scale one, the complementary Gram matrix
is `A(-gamma,0)` after negating its second basis vector. -/
noncomputable def omearaExchangeComplementZeroRightLatticeIsometry
    (alpha gamma : K) :
    Isometry (QuadraticSpace.omearaPlane (-gamma))
      (QuadraticSpace.omearaExchangeComplement alpha 0 gamma 1
        (by simp) (by simp) (by simp))
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) where
  toLinearEquiv :=
    { toFun := fun x ↦ ![x 0, -x 1]
      invFun := fun x ↦ ![x 0, -x 1]
      left_inv := by
        intro x
        funext i
        fin_cases i <;> simp
      right_inv := by
        intro x
        funext i
        fin_cases i <;> simp
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp [add_comm]
      map_smul' := by
        intro c x
        funext i
        fin_cases i <;> simp }
  map_bilin x y := by
    rw [QuadraticSpace.omearaExchangeComplement_bilin_apply,
      QuadraticSpace.omearaPlane_bilin_apply]
    simp
  map_mem x := by
    rw [mem_omearaPlaneLattice_iff, mem_omearaPlaneLattice_iff]
    constructor
    · rintro ⟨hx0, hx1⟩
      exact ⟨hx0, (IntegerRing K).toSubring.neg_mem hx1⟩
    · rintro ⟨hx0, hx1⟩
      exact ⟨hx0, by simpa using (IntegerRing K).toSubring.neg_mem hx1⟩

/-- Integral coefficient addition for two unscaled O'Meara planes. -/
noncomputable opaque omearaTwoPlaneAddLatticeIsometry
    (alpha gamma : K)
    (halpha : alpha ∈ IntegerRing K)
    (hgamma : gamma ∈ IntegerRing K) :
    Isometry
      ((QuadraticSpace.omearaPlane (alpha + gamma)).orthogonalSum
        (QuadraticSpace.omearaPlane (-gamma)))
      ((QuadraticSpace.omearaPlane alpha).orthogonalSum
        (QuadraticSpace.omearaPlane gamma))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K)))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K))) := by
  have hminusOne : IsValuationUnit K (-1 : K) := by
    simp [IsValuationUnit]
  let complement := QuadraticSpace.omearaExchangeComplement
    alpha 0 gamma 1 (by simp) (by simp) (by simp)
  let identifySource : Isometry
      ((QuadraticSpace.omearaPlane (alpha + gamma)).orthogonalSum
        (QuadraticSpace.omearaPlane (-gamma)))
      ((QuadraticSpace.omearaGeneralPlane
          (alpha + gamma) 0 (by simp)).orthogonalSum complement)
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K)))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K))) :=
    (omearaGeneralPlaneZeroRightLatticeIsometry
      (alpha + gamma)).symm.orthogonalProductBasic
        (omearaExchangeComplementZeroRightLatticeIsometry alpha gamma)
  let exchangeRaw := omearaBinaryExchangeLatticeIsometry
    alpha 0 gamma (1 : Kˣ) halpha (by simp) hgamma (by simp)
      (by simpa using hminusOne) (by simpa using hminusOne)
  let exchange : Isometry
      ((QuadraticSpace.omearaGeneralPlane
          (alpha + gamma) 0 (by simp)).orthogonalSum complement)
      ((QuadraticSpace.omearaGeneralPlane alpha 0 (by simp)).orthogonalSum
        ((QuadraticSpace.omearaPlane gamma).rescaleUnit (1 : Kˣ)))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K)))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K))) := by
    simpa only [Units.val_one, one_mul] using exchangeRaw
  let identifyTarget : Isometry
      ((QuadraticSpace.omearaGeneralPlane alpha 0 (by simp)).orthogonalSum
        ((QuadraticSpace.omearaPlane gamma).rescaleUnit (1 : Kˣ)))
      ((QuadraticSpace.omearaPlane alpha).orthogonalSum
        (QuadraticSpace.omearaPlane gamma))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K)))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K))) :=
    (omearaGeneralPlaneZeroRightLatticeIsometry alpha).orthogonalProductBasic
      (Isometry.rescaleUnitOne (QuadraticSpace.omearaPlane gamma)
        (hyperbolicPlaneLattice (K := K)))
  exact identifySource.trans (exchange.trans identifyTarget)

/-- In a second O'Meara plane, the integral vector `c * e₀` belongs to
both the standard lattice and its integral dual. -/
theorem omearaPlane_first_smul_mem_and_mem_dual
    (gamma c : K) (hgamma : gamma ∈ IntegerRing K)
    (hc : c ∈ IntegerRing K) :
    let z : Fin 2 → K := ![c, 0]
    z ∈ hyperbolicPlaneLattice (K := K) ∧
      z ∈ dualLattice (QuadraticSpace.omearaPlane gamma)
        (hyperbolicPlaneLattice (K := K)) := by
  let z : Fin 2 → K := ![c, 0]
  have hz : z ∈ hyperbolicPlaneLattice (K := K) := by
    rw [mem_omearaPlaneLattice_iff]
    simpa [z] using And.intro hc (IntegerRing K).zero_mem
  refine ⟨hz, ?_⟩
  rw [mem_dualLattice_iff]
  intro y hy
  have hy' := (mem_omearaPlaneLattice_iff y).1 hy
  rw [QuadraticSpace.omearaPlane_bilin_apply]
  have hmain : gamma * c * y 0 + c * y 1 ∈ IntegerRing K :=
    (IntegerRing K).toSubring.add_mem
    ((IntegerRing K).toSubring.mul_mem
      ((IntegerRing K).toSubring.mul_mem hgamma hc) hy'.1)
    ((IntegerRing K).toSubring.mul_mem hc hy'.2)
  simpa [z] using hmain

/-- Integral square-weighted coefficient addition.  This is 93:12 with
`z = c * e₀` in the second plane:
`A(alpha + gamma*c²,0) ⊥ A(gamma,0) ≅ A(alpha,0) ⊥ A(gamma,0)`. -/
noncomputable opaque omearaTwoPlaneSquareAddLatticeIsometry
    (alpha gamma c : K)
    (hgamma : gamma ∈ IntegerRing K)
    (hc : c ∈ IntegerRing K) :
    Isometry
      ((QuadraticSpace.omearaPlane (alpha + gamma * c ^ 2)).orthogonalSum
        (QuadraticSpace.omearaPlane gamma))
      ((QuadraticSpace.omearaPlane alpha).orthogonalSum
        (QuadraticSpace.omearaPlane gamma))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K)))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K))) := by
  let z : Fin 2 → K := ![c, 0]
  have hz := omearaPlane_first_smul_mem_and_mem_dual gamma c hgamma hc
  let f := omeara9312_general
    (QuadraticSpace.omearaPlane gamma)
    (hyperbolicPlaneLattice (K := K)) alpha z hz.1 hz.2
  have hqz :
      (QuadraticSpace.omearaPlane gamma).quadratic z = gamma * c ^ 2 := by
    rw [QuadraticSpace.quadratic,
      QuadraticSpace.omearaPlane_bilin_apply]
    simp [z]
    ring
  simpa only [hqz] using f

/-- The square-weighted two-plane change after a common modular scaling. -/
noncomputable def scaledOmearaTwoPlaneSquareAddLatticeIsometry
    (a : Kˣ) (alpha gamma c : K)
    (hgamma : gamma ∈ IntegerRing K)
    (hc : c ∈ IntegerRing K) :
    Isometry
      (((QuadraticSpace.omearaPlane (alpha + gamma * c ^ 2)).rescaleUnit a)
        |>.orthogonalSum
          ((QuadraticSpace.omearaPlane gamma).rescaleUnit a))
      (((QuadraticSpace.omearaPlane alpha).rescaleUnit a)
        |>.orthogonalSum
          ((QuadraticSpace.omearaPlane gamma).rescaleUnit a))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K)))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K))) := by
  let f := (omearaTwoPlaneSquareAddLatticeIsometry
    alpha gamma c hgamma hc).rescaleUnitBoth a
  exact
    { toLinearEquiv := f.toLinearEquiv
      map_bilin := by
        intro x y
        have h := f.map_bilin x y
        simp only [QuadraticSpace.rescaleUnit_bilin_apply,
          QuadraticSpace.orthogonalSum_bilin_apply] at h ⊢
        rw [← mul_add, ← mul_add]
        exact h
      map_mem := f.map_mem }

/-- The same two-plane exchange after a common modular scaling. -/
noncomputable def scaledOmearaTwoPlaneAddLatticeIsometry
    (a : Kˣ) (alpha gamma : K)
    (halpha : alpha ∈ IntegerRing K)
    (hgamma : gamma ∈ IntegerRing K) :
    Isometry
      (((QuadraticSpace.omearaPlane (alpha + gamma)).rescaleUnit a)
        |>.orthogonalSum
          ((QuadraticSpace.omearaPlane (-gamma)).rescaleUnit a))
      (((QuadraticSpace.omearaPlane alpha).rescaleUnit a)
        |>.orthogonalSum
          ((QuadraticSpace.omearaPlane gamma).rescaleUnit a))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K)))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K))) := by
  let f := (omearaTwoPlaneAddLatticeIsometry
    alpha gamma halpha hgamma).rescaleUnitBoth a
  exact
    { toLinearEquiv := f.toLinearEquiv
      map_bilin := by
        intro x y
        have h := f.map_bilin x y
        simp only [QuadraticSpace.rescaleUnit_bilin_apply,
          QuadraticSpace.orthogonalSum_bilin_apply] at h ⊢
        rw [← mul_add, ← mul_add]
        exact h
      map_mem := f.map_mem }

/-- A commonly scaled even O'Meara plane is a scaled hyperbolic plane. -/
noncomputable def scaledHyperbolicToEvenOmearaPlaneLatticeIsometry
    (a : Kˣ) (alpha eta : K) (hcoeff : alpha = 2 * eta)
    (heta : eta ∈ IntegerRing K) :
    Isometry (QuadraticSpace.hyperbolicPlane a)
      ((QuadraticSpace.omearaPlane alpha).rescaleUnit a)
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) := by
  let f := (hyperbolicToOmearaPlaneLatticeIsometry
    alpha eta hcoeff heta).rescaleUnitBoth a
  exact
    { toLinearEquiv := f.toLinearEquiv
      map_bilin := by
        intro x y
        have h := f.map_bilin x y
        simpa only [QuadraticSpace.rescaleUnit_bilin_apply,
          QuadraticSpace.hyperbolicPlane_bilin_apply,
          Units.val_one, one_mul] using h
      map_mem := f.map_mem }

/-- If the sum of two integral plane coefficients is even, their scaled
orthogonal product displays a scaled hyperbolic summand. -/
noncomputable def scaledTwoOmearaPlanesHyperbolicDisplayedIsometry
    (a : Kˣ) (alpha gamma eta : K)
    (halpha : alpha ∈ IntegerRing K)
    (hgamma : gamma ∈ IntegerRing K)
    (hsum : alpha + gamma = 2 * eta)
    (heta : eta ∈ IntegerRing K) :
    Isometry
      ((QuadraticSpace.hyperbolicPlane a).orthogonalSum
        ((QuadraticSpace.omearaPlane (-gamma)).rescaleUnit a))
      (((QuadraticSpace.omearaPlane alpha).rescaleUnit a)
        |>.orthogonalSum
          ((QuadraticSpace.omearaPlane gamma).rescaleUnit a))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K)))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K))) :=
  ((scaledHyperbolicToEvenOmearaPlaneLatticeIsometry
      a (alpha + gamma) eta hsum heta).orthogonalProductBasic
    (Isometry.refl
      ((QuadraticSpace.omearaPlane (-gamma)).rescaleUnit a)
      (hyperbolicPlaneLattice (K := K)))).trans
        (scaledOmearaTwoPlaneAddLatticeIsometry
          a alpha gamma halpha hgamma)

/-- Square-coset form of the two-plane hyperbolic extraction. -/
noncomputable def scaledTwoOmearaPlanesHyperbolicDisplayedIsometryOfSquare
    (a : Kˣ) (alpha gamma c eta : K)
    (hgamma : gamma ∈ IntegerRing K)
    (hc : c ∈ IntegerRing K)
    (hsum : alpha + gamma * c ^ 2 = 2 * eta)
    (heta : eta ∈ IntegerRing K) :
    Isometry
      ((QuadraticSpace.hyperbolicPlane a).orthogonalSum
        ((QuadraticSpace.omearaPlane gamma).rescaleUnit a))
      (((QuadraticSpace.omearaPlane alpha).rescaleUnit a)
        |>.orthogonalSum
          ((QuadraticSpace.omearaPlane gamma).rescaleUnit a))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K)))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K))) :=
  ((scaledHyperbolicToEvenOmearaPlaneLatticeIsometry
      a (alpha + gamma * c ^ 2) eta hsum heta).orthogonalProductBasic
    (Isometry.refl
      ((QuadraticSpace.omearaPlane gamma).rescaleUnit a)
      (hyperbolicPlaneLattice (K := K)))).trans
        (scaledOmearaTwoPlaneSquareAddLatticeIsometry
          a alpha gamma c hgamma hc)

end Lattice

end Bong
