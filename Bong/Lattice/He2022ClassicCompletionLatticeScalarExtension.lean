/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.He2022ClassicNumberFieldBONGBridge
import Bong.Lattice.He2022ClassicScalarExtensionLattice

/-!
# Scalar extension of lattices at a pair of finite places

This file supplies the integral-ring preservation required to apply the
intrinsic lattice scalar-extension theorem to the actual embedding of two
number-field completions.  It uses the proved ramification-index formula,
including the zero case.  No isometry between the chosen upper good-BONG
realization and this specified scalar extension is asserted here.
-/

open scoped NumberField TensorProduct

namespace Bong.HeClassic2024NumberFieldScalarExtension

open Dyadic

universe u v w

variable {K : Type u} {E : Type v}
  [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E]

/-- The embedding of finite completions carries the lower valuation ring
into the upper one.  This is the arithmetic premise needed to identify the
true scalar-extension lattice as the integral span of pure tensors. -/
theorem completionMap_preserves_integerRing
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    [P.asIdeal.LiesOver p.asIdeal]
    (hp : NumberFieldCompletion.IsDyadic p) :
    letI := NumberFieldCompletion.dyadicContext p hp
    let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
    letI := NumberFieldCompletion.dyadicContext P hpP
    ∀ a : IntegerRing (p.adicCompletion K),
      Dyadic.IsIntegral (P.adicCompletion E)
        (HeClassic2024NumberFieldLocalExtension.completionMap p P
          (a : p.adicCompletion K)) := by
  letI := NumberFieldCompletion.dyadicContext p hp
  let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
  letI := NumberFieldCompletion.dyadicContext P hpP
  change ∀ a : IntegerRing (p.adicCompletion K),
    Dyadic.IsIntegral (P.adicCompletion E)
      (HeClassic2024NumberFieldLocalExtension.completionMap p P
        (a : p.adicCompletion K))
  intro a
  have ha : Dyadic.IsIntegral (p.adicCompletion K) (a : p.adicCompletion K) :=
    (mem_integerRing_iff (p.adicCompletion K)).mp a.property
  change (0 : WithTop Int) ≤ ord (p.adicCompletion K) (a : p.adicCompletion K) at ha
  by_cases hzero : (a : p.adicCompletion K) = 0
  · simp [Dyadic.IsIntegral, hzero]
  let t : (p.adicCompletion K)ˣ := Units.mk0 (a : p.adicCompletion K) hzero
  have hbase : 0 ≤ ordUnit (p.adicCompletion K) t := by
    have h : (0 : WithTop Int) ≤
        (ordUnit (p.adicCompletion K) t : WithTop Int) := by
      simpa only [coe_ordUnit, t, Units.val_mk0] using ha
    exact WithTop.coe_le_coe.mp h
  have hscale :
      ordUnit (P.adicCompletion E)
        (Units.map
          (HeClassic2024NumberFieldLocalExtension.completionMap p P) t) =
      ordUnit (p.adicCompletion K) t *
        (P.asIdeal.ramificationIdx (𝓞 K) : Int) := by
    rw [HeClassic2024NumberFieldBONGBridge.ordUnit_eq_completionAdicOrder P hpP,
      HeClassic2024NumberFieldLocalExtension.completionAdicOrder_liesOver p P,
      ← HeClassic2024NumberFieldBONGBridge.ordUnit_eq_completionAdicOrder p hp]
  have hupper :
      0 ≤ ordUnit (P.adicCompletion E)
        (Units.map
          (HeClassic2024NumberFieldLocalExtension.completionMap p P) t) := by
    rw [hscale]
    exact mul_nonneg hbase (Int.natCast_nonneg _)
  have hupper' : (0 : WithTop Int) ≤
      ord (P.adicCompletion E)
        (HeClassic2024NumberFieldLocalExtension.completionMap p P
          (a : p.adicCompletion K)) := by
    have h := (WithTop.coe_le_coe).mpr hupper
    simpa [coe_ordUnit, t] using h
  exact hupper'

/-- At finite places, the specified scalar-extension lattice has exactly the
upper integral span of the pure tensors of vectors in the lower lattice. -/
theorem completionScalarExtension_toSubmodule_eq_span
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    [P.asIdeal.LiesOver p.asIdeal]
    (hp : NumberFieldCompletion.IsDyadic p)
    {V : Type w} [AddCommGroup V] [Module (p.adicCompletion K) V]
    [FiniteDimensional (p.adicCompletion K) V] :
    letI := NumberFieldCompletion.dyadicContext p hp
    let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
    letI := NumberFieldCompletion.dyadicContext P hpP
    letI := HeClassic2024NumberFieldLocalExtension.CompletionLiesOver.instAlgebra
      (p := p) (P := P)
    ∀ L : Bong.Lattice (p.adicCompletion K) V,
      (Bong.Lattice.scalarExtension (E := P.adicCompletion E) L).toSubmodule =
        Submodule.span (IntegerRing (P.adicCompletion E))
          (Set.range (fun x : L.toSubmodule =>
            (1 : P.adicCompletion E) ⊗ₜ[p.adicCompletion K] (x : V))) := by
  letI := NumberFieldCompletion.dyadicContext p hp
  let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
  letI := NumberFieldCompletion.dyadicContext P hpP
  letI := HeClassic2024NumberFieldLocalExtension.CompletionLiesOver.instAlgebra
    (p := p) (P := P)
  change ∀ L : Bong.Lattice (p.adicCompletion K) V,
    (Bong.Lattice.scalarExtension (E := P.adicCompletion E) L).toSubmodule =
      Submodule.span (IntegerRing (P.adicCompletion E))
        (Set.range (fun x : L.toSubmodule =>
          (1 : P.adicCompletion E) ⊗ₜ[p.adicCompletion K] (x : V)))
  intro L
  apply Bong.Lattice.scalarExtension_toSubmodule_eq_span L
  intro a
  simpa only [RingHom.algebraMap_toAlgebra] using
    (completionMap_preserves_integerRing p P hp a)

/-- A chosen integral basis at the lower finite place becomes an integral
basis of its actual scalar-extension lattice at the upper finite place. -/
theorem completionScalarExtension_basisLattice
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    [P.asIdeal.LiesOver p.asIdeal]
    (hp : NumberFieldCompletion.IsDyadic p)
    {V : Type w} [AddCommGroup V] [Module (p.adicCompletion K) V]
    [FiniteDimensional (p.adicCompletion K) V] :
    letI := NumberFieldCompletion.dyadicContext p hp
    let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
    letI := NumberFieldCompletion.dyadicContext P hpP
    letI := HeClassic2024NumberFieldLocalExtension.CompletionLiesOver.instAlgebra
      (p := p) (P := P)
    ∀ {ι : Type*} [Finite ι] (b : Module.Basis ι (p.adicCompletion K) V),
      Bong.Lattice.scalarExtension (E := P.adicCompletion E)
          (Bong.Lattice.basisLattice b) =
        Bong.Lattice.basisLattice (b.baseChange (P.adicCompletion E)) := by
  letI := NumberFieldCompletion.dyadicContext p hp
  let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
  letI := NumberFieldCompletion.dyadicContext P hpP
  letI := HeClassic2024NumberFieldLocalExtension.CompletionLiesOver.instAlgebra
    (p := p) (P := P)
  dsimp only
  intro ι _ b
  apply Bong.Lattice.scalarExtension_basisLattice b
  intro a
  simpa only [RingHom.algebraMap_toAlgebra] using
    (completionMap_preserves_integerRing p P hp a)

end Bong.HeClassic2024NumberFieldScalarExtension
