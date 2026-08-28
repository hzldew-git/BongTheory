/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OrthogonalDecompositionProduct

/-!
# Orthogonal sums of quadratic sublattices

Two orthogonal quadratic sublattices whose carriers and integral ambient
modules sum to a third one give a concrete isometry from their orthogonal
product onto the third lattice.
-/

namespace Bong

open Dyadic Module

namespace Lattice.QuadraticSublattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}

/-- The sum map from two orthogonal complementary sublattices onto their
displayed total sublattice. -/
noncomputable def orthogonalSumLatticeIsometry
    (A B S : QuadraticSublattice q)
    (hcarrier : A.carrier ⊔ B.carrier = S.carrier)
    (hintegral : A.ambientSubmodule ⊔ B.ambientSubmodule =
      S.ambientSubmodule)
    (horth : ∀ (x : A.carrier) (y : B.carrier),
      q.bilin (x : V) (y : V) = 0) :
    Isometry (A.space.orthogonalSum B.space) S.space
      (product A.lattice B.lattice) S.lattice := by
  have hdisjoint : Disjoint A.carrier B.carrier := by
    rw [Submodule.disjoint_def]
    intro z hzA hzB
    let zA : A.carrier := ⟨z, hzA⟩
    let zB : B.carrier := ⟨z, hzB⟩
    have hzZero : zA = 0 := by
      apply A.nondegenerate.1 zA
      intro x
      change q.bilin z (x : V) = 0
      exact q.isSymm.eq z (x : V) |>.trans (horth x zB)
    exact congrArg Subtype.val hzZero
  let sumMap : (A.carrier × B.carrier) →ₗ[K] S.carrier :=
    { toFun := fun z => ⟨(z.1 : V) + (z.2 : V), by
        rw [← hcarrier]
        exact Submodule.add_mem (A.carrier ⊔ B.carrier)
          (Submodule.mem_sup_left z.1.property)
          (Submodule.mem_sup_right z.2.property)⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        change (x.1 : V) + (y.1 : V) +
          ((x.2 : V) + (y.2 : V)) =
          (x.1 : V) + (x.2 : V) + ((y.1 : V) + (y.2 : V))
        module
      map_smul' := by
        intro c x
        apply Subtype.ext
        simp }
  have hsumInjective : Function.Injective sumMap := by
    intro x y hxy
    have hxyV := congrArg (fun z : S.carrier => (z : V)) hxy
    change (x.1 : V) + (x.2 : V) =
      (y.1 : V) + (y.2 : V) at hxyV
    have hdifference : (x.1 : V) - (y.1 : V) =
        (y.2 : V) - (x.2 : V) := by
      calc
        (x.1 : V) - (y.1 : V) =
            ((x.1 : V) + (x.2 : V)) -
              ((y.1 : V) + (x.2 : V)) := by abel
        _ = ((y.1 : V) + (y.2 : V)) -
              ((y.1 : V) + (x.2 : V)) := by rw [hxyV]
        _ = (y.2 : V) - (x.2 : V) := by abel
    have hzero : (x.1 : V) - (y.1 : V) = 0 :=
      Submodule.disjoint_def.mp hdisjoint
        ((x.1 : V) - (y.1 : V))
        (A.carrier.sub_mem x.1.property y.1.property)
        (by
          rw [hdifference]
          exact B.carrier.sub_mem y.2.property x.2.property)
    have hfirst : x.1 = y.1 := by
      apply Subtype.ext
      exact sub_eq_zero.mp hzero
    have hsecond : x.2 = y.2 := by
      apply Subtype.ext
      rw [hfirst] at hxyV
      exact add_left_cancel hxyV
    exact Prod.ext hfirst hsecond
  have hsumSurjective : Function.Surjective sumMap := by
    intro z
    have hz : (z : V) ∈ A.carrier ⊔ B.carrier := by
      rw [hcarrier]
      exact z.property
    rw [Submodule.mem_sup] at hz
    rcases hz with ⟨a, ha, b, hb, hab⟩
    refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), ?_⟩
    apply Subtype.ext
    exact hab
  let sumEquiv : (A.carrier × B.carrier) ≃ₗ[K] S.carrier :=
    LinearEquiv.ofBijective sumMap ⟨hsumInjective, hsumSurjective⟩
  refine
    { toLinearEquiv := sumEquiv
      map_bilin := ?_
      map_mem := ?_ }
  · intro x y
    change q.bilin ((x.1 : V) + (x.2 : V))
        ((y.1 : V) + (y.2 : V)) =
      q.bilin (x.1 : V) (y.1 : V) +
        q.bilin (x.2 : V) (y.2 : V)
    simp only [map_add, LinearMap.add_apply]
    rw [horth x.1 y.2,
      q.isSymm.eq (x.2 : V) (y.1 : V), horth y.1 x.2]
    simp
  · intro z
    rw [mem_product_iff]
    constructor
    · rintro ⟨hzA, hzB⟩
      have hzAmbient : ((sumEquiv z : S.carrier) : V) ∈
          A.ambientSubmodule ⊔ B.ambientSubmodule := by
        rw [Submodule.mem_sup]
        exact ⟨(z.1 : V), ⟨z.1, hzA, rfl⟩,
          (z.2 : V), ⟨z.2, hzB, rfl⟩, rfl⟩
      rw [hintegral] at hzAmbient
      rcases hzAmbient with ⟨s, hs, hsz⟩
      have hsEq : s = sumEquiv z := Subtype.ext hsz
      rwa [← hsEq]
    · intro hzS
      have hzAmbient : ((sumEquiv z : S.carrier) : V) ∈
          S.ambientSubmodule := ⟨sumEquiv z, hzS, rfl⟩
      rw [← hintegral, Submodule.mem_sup] at hzAmbient
      rcases hzAmbient with
        ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hab⟩
      have hpair : (a, b) = z := by
        apply sumEquiv.injective
        apply Subtype.ext
        exact hab
      rw [← congrArg Prod.fst hpair, ← congrArg Prod.snd hpair]
      exact ⟨ha, hb⟩

end Lattice.QuadraticSublattice

end Bong
