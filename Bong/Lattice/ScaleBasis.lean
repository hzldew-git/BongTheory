/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Ideals
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Computing scale containment from an integral basis

To bound the scale ideal it is enough to bound the finitely many pairings of
an integral basis.  Bilinearity then handles arbitrary lattice vectors.
-/

namespace Bong

open Dyadic
open Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- Pairing containment on an integral basis implies containment of the
whole scale ideal. -/
theorem scaleIdeal_le_of_integralBasis
    {q : QuadraticSpace K V} {L : Lattice K V}
    {ι : Type w} [Finite ι]
    (b : Basis ι (IntegerRing K) L.toSubmodule)
    (I : CoefficientIdeal (K := K))
    (hp : ∀ i j,
      q.bilin ((b i : L.toSubmodule) : V)
        ((b j : L.toSubmodule) : V) ∈ I) :
    scaleIdeal q L ≤ I := by
  classical
  letI := Fintype.ofFinite ι
  rw [scaleIdeal, Submodule.span_le]
  rintro _ ⟨p, rfl⟩
  change q.bilin (p.1 : V) (p.2 : V) ∈ I
  have hxO :
      ∑ i, (b.repr p.1 i : IntegerRing K) •
        ((b i : L.toSubmodule) : V) = (p.1 : V) := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using
      congrArg Subtype.val (b.sum_repr p.1)
  have hyO :
      ∑ j, (b.repr p.2 j : IntegerRing K) •
        ((b j : L.toSubmodule) : V) = (p.2 : V) := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using
      congrArg Subtype.val (b.sum_repr p.2)
  have hx :
      ∑ i, algebraMap (IntegerRing K) K (b.repr p.1 i) •
        ((b i : L.toSubmodule) : V) = (p.1 : V) := by
    simpa only [IsScalarTower.algebraMap_smul] using hxO
  have hy :
      ∑ j, algebraMap (IntegerRing K) K (b.repr p.2 j) •
        ((b j : L.toSubmodule) : V) = (p.2 : V) := by
    simpa only [IsScalarTower.algebraMap_smul] using hyO
  rw [← hx, ← hy]
  simp only [map_sum, LinearMap.coe_sum, Finset.sum_apply]
  apply I.sum_mem (t := Finset.univ)
  intro j _
  have hpair (i : ι) :
      q.bilin
          (algebraMap (IntegerRing K) K (b.repr p.1 i) •
            ((b i : L.toSubmodule) : V))
          (algebraMap (IntegerRing K) K (b.repr p.2 j) •
            ((b j : L.toSubmodule) : V)) =
        algebraMap (IntegerRing K) K (b.repr p.1 i) *
          (algebraMap (IntegerRing K) K (b.repr p.2 j) *
            q.bilin ((b i : L.toSubmodule) : V)
              ((b j : L.toSubmodule) : V)) := by
    rw [LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right]
  apply I.sum_mem (t := Finset.univ)
  intro i _
  rw [hpair i]
  convert I.smul_mem
    (b.repr p.1 i * b.repr p.2 j) (hp i j) using 1
  simp [Algebra.smul_def, mul_assoc]

end Lattice

end Bong
