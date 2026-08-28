/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.GoodBONGScalarAgreement
import Bong.Bong.GoodMap
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Same-rank integral images of good BONGs

An injective integral representation between spaces carrying equally long
BONG bases is automatically an ambient isometry.  Its image lattice is a
literal sublattice of the target, and the transported good BONG has exactly
the original scalar sequence.
-/

namespace Bong

open Dyadic
open Module

universe u v w

/-- The literal image of a same-rank integral representation, equipped with
the transported source good BONG. -/
structure GoodBONGSameRankIntegralImageData
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {n : Nat}
    (a : BONG.GoodBONG q L (n + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (f : Lattice.Representation r q M L) where
  imageLattice : Lattice K V
  imageBONG : BONG.GoodBONG q imageLattice (n + 1)
  image_le : imageLattice ≤ L
  scalarAgreement : BONG.GoodBONG.ScalarAgreement imageBONG b

/-- A same-rank integral representation has a literal image realization.
This is the equal-rank case of the geometric reduction in Lemma 2.21. -/
theorem exists_goodBONGSameRankIntegralImageData
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {n : Nat}
    (a : BONG.GoodBONG q L (n + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (f : Lattice.Representation r q M L) :
    Nonempty (GoodBONGSameRankIntegralImageData a b f) := by
  letI : FiniteDimensional K W :=
    b.toBONG.basis.finiteDimensional_of_finite
  letI : FiniteDimensional K V :=
    a.toBONG.basis.finiteDimensional_of_finite
  have hfinrank : finrank K W = finrank K V := by
    rw [← b.toBONG.length_eq_finrank,
      ← a.toBONG.length_eq_finrank]
  have hsurjective : Function.Surjective f.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hfinrank).mp f.injective
  let e : W ≃ₗ[K] V := LinearEquiv.ofBijective f.toLinearMap
    ⟨f.injective, hsurjective⟩
  let C : Lattice K V := Lattice.map e M
  let g : Lattice.Isometry r q M C := {
    toLinearEquiv := e
    map_bilin x y := f.map_bilin x y
    map_mem x := (Lattice.map_mem_map_iff e M x).symm }
  let c : BONG.GoodBONG q C (n + 1) := b.mapLatticeIsometry g
  refine ⟨⟨C, c, ?_, ?_⟩⟩
  · intro y hy
    have hySource : e.symm y ∈ M := (Lattice.mem_map_iff e M y).mp hy
    have hyTarget := f.map_mem hySource
    change e (e.symm y) ∈ L at hyTarget
    apply Lattice.mem_toSubmodule.mpr
    simpa only [e.apply_symm_apply] using hyTarget
  · refine ⟨?_⟩
    intro i
    apply Units.ext
    change (b.toBONG.mapLatticeIsometry g).value i = b.toBONG.value i
    exact BONG.value_mapLatticeIsometry g b.toBONG i

end Bong
