/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.DeterminantProjection

/-!
# Integral bases adapted to a chosen projected basis

The exact norm-generator line and projection sequence identifies `L` with
the product of the valuation ring and its projected lattice.  This file uses
any selected integral basis of the projection, rather than the fixed standard
basis used for determinant computations.
-/

namespace Bong

open Dyadic
open Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- An integral basis of `L` whose first vector is `x` and whose remaining
vectors project to the chosen basis `c`. -/
noncomputable def adaptedIntegralBasisOfProjectedBasis
    {q : QuadraticSpace K V} (L : Lattice K V) (x : V)
    (generator : IsNormGenerator q L x)
    (anisotropic : q.IsAnisotropic x) {ι : Type w}
    (c : Basis ι (IntegerRing K)
      (L.projectedLattice q x anisotropic).toSubmodule) :
    Basis (Unit ⊕ ι) (IntegerRing K) L.toSubmodule :=
  ((Basis.singleton Unit (IntegerRing K)).prod c).map
    (splittingEquiv q L x generator anisotropic).symm

@[simp]
theorem adaptedIntegralBasisOfProjectedBasis_inl
    {q : QuadraticSpace K V} (L : Lattice K V) (x : V)
    (generator : IsNormGenerator q L x)
    (anisotropic : q.IsAnisotropic x) {ι : Type w}
    (c : Basis ι (IntegerRing K)
      (L.projectedLattice q x anisotropic).toSubmodule) (i : Unit) :
    ((adaptedIntegralBasisOfProjectedBasis L x generator anisotropic c
      (Sum.inl i) : L.toSubmodule) : V) = x := by
  have hb :
      ((Basis.singleton Unit (IntegerRing K)).prod c) (Sum.inl i) =
        (1, 0) := by
    apply Prod.ext
    · rw [Basis.prod_apply_inl_fst, Basis.singleton_apply]
    · rw [Basis.prod_apply_inl_snd]
  have h := LinearMap.congr_fun
    (splittingEquiv_spec q L x generator anisotropic).1
      (1 : IntegerRing K)
  rw [adaptedIntegralBasisOfProjectedBasis, Basis.map_apply, hb]
  have heq :
      (splittingEquiv q L x generator anisotropic).symm (1, 0) =
        lineMap L x generator.mem 1 := by
    change
      ((splittingEquiv q L x generator anisotropic).symm.toLinearMap)
          ((LinearMap.inl (IntegerRing K) (IntegerRing K)
            (L.projectedLattice q x anisotropic).toSubmodule) 1) =
        lineMap L x generator.mem 1
    exact h.symm
  calc
    (((splittingEquiv q L x generator anisotropic).symm (1, 0) :
        L.toSubmodule) : V) =
        (lineMap L x generator.mem 1 : V) := congrArg Subtype.val heq
    _ = x := by rw [lineMap_coe, one_smul]

@[simp]
theorem projectionMap_adaptedIntegralBasisOfProjectedBasis_inr
    {q : QuadraticSpace K V} (L : Lattice K V) (x : V)
    (generator : IsNormGenerator q L x)
    (anisotropic : q.IsAnisotropic x) {ι : Type w}
    (c : Basis ι (IntegerRing K)
      (L.projectedLattice q x anisotropic).toSubmodule) (i : ι) :
    projectionMap q L x anisotropic
        (adaptedIntegralBasisOfProjectedBasis L x generator
          anisotropic c (Sum.inr i)) = c i := by
  have hb :
      ((Basis.singleton Unit (IntegerRing K)).prod c) (Sum.inr i) =
        (0, c i) := by
    apply Prod.ext
    · rw [Basis.prod_apply_inr_fst]
    · rw [Basis.prod_apply_inr_snd]
  rw [(splittingEquiv_spec q L x generator anisotropic).2]
  rw [LinearMap.comp_apply, adaptedIntegralBasisOfProjectedBasis,
    Basis.map_apply, hb]
  change
    ((splittingEquiv q L x generator anisotropic)
      ((splittingEquiv q L x generator anisotropic).symm
        (0, c i))).2 = c i
  exact congrArg Prod.snd
    ((splittingEquiv q L x generator anisotropic).apply_symm_apply
      (0, c i))

end Lattice

end Bong
