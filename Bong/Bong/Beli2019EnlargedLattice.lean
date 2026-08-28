/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.AdjoinVector
import Bong.Lattice.NormRescale
import Bong.Lattice.PowerIdeal

/-!
# Beli (2019), the enlarged lattice in Lemma 5.7

For an integer `s`, the paper enlarges `N` to
`O · (π⁻ˢ y) + N`.  This file defines that lattice, proves its elementary
containment properties, identifies its projection along `y`, and checks the
order shift of the scaled vector.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- If the inverse of `a` is integral, a lattice embeds in its rescaling by
`a`. -/
theorem le_rescale_of_inv_mem_integerRing (a : Kˣ) (L : Lattice K V)
    (hinv : ((a⁻¹ : Kˣ) : K) ∈ IntegerRing K) : L ≤ rescale a L := by
  intro x hx
  apply (mem_rescale_iff a L x).2
  refine ⟨((a⁻¹ : Kˣ) : K) • x, ?_, ?_⟩
  · exact L.smul_mem ⟨((a⁻¹ : Kˣ) : K), hinv⟩ hx
  · rw [smul_smul]
    simp

end Lattice

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- The vector `π⁻ˢ y` used as the new first vector in Lemma 5.7. -/
noncomputable def lemma57EnlargedHead (y : V) (s : Int) : V :=
  (uniformizerPowerUnit K (-s) : K) • y

/-- The lattice `O · (π⁻ˢ y) + N` from the proof of Lemma 5.7. -/
noncomputable def lemma57EnlargedLattice (N : Lattice K V)
    (y : V) (s : Int) : Lattice K V :=
  Lattice.adjoinVector N (lemma57EnlargedHead (K := K) y s)

/-- The original lattice is contained in the Lemma 5.7 enlargement. -/
theorem le_lemma57EnlargedLattice (N : Lattice K V) (y : V) (s : Int) :
    N ≤ lemma57EnlargedLattice N y s :=
  Lattice.le_adjoinVector N (lemma57EnlargedHead (K := K) y s)

/-- The scaled first vector belongs to the Lemma 5.7 enlargement. -/
theorem lemma57EnlargedHead_mem (N : Lattice K V) (y : V) (s : Int) :
    lemma57EnlargedHead (K := K) y s ∈ lemma57EnlargedLattice N y s :=
  Lattice.mem_adjoinVector N (lemma57EnlargedHead (K := K) y s)

/-- For `s ≥ 0`, the Lemma 5.7 enlargement lies inside the uniformly
rescaled lattice `π⁻ˢ N`. -/
theorem lemma57EnlargedLattice_le_rescale
    (N : Lattice K V) {y : V} (hy : y ∈ N) {s : Int} (hs : 0 ≤ s) :
    lemma57EnlargedLattice N y s ≤
      Lattice.rescale (uniformizerPowerUnit K (-s)) N := by
  let a : Kˣ := uniformizerPowerUnit K (-s)
  have hinv : ((a⁻¹ : Kˣ) : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, ← coe_ordUnit, ordUnit_inv]
    dsimp [a]
    rw [ordUnit_uniformizerPowerUnit]
    norm_cast
    omega
  rw [lemma57EnlargedLattice]
  apply Lattice.adjoinVector_le
  · exact Lattice.le_rescale_of_inv_mem_integerRing a N hinv
  · change (a : K) • y ∈ Lattice.rescale a N
    exact Lattice.smul_mem_rescale a N hy

/-- Scaling an anisotropic vector by `π⁻ˢ` preserves anisotropy. -/
theorem lemma57EnlargedHead_isAnisotropic (q : QuadraticSpace K V)
    {y : V} (anisotropic : q.IsAnisotropic y) (s : Int) :
    q.IsAnisotropic (lemma57EnlargedHead (K := K) y s) := by
  change q.quadratic ((uniformizerPowerUnit K (-s) : K) • y) ≠ 0
  rw [q.quadratic_smul]
  exact mul_ne_zero
    (pow_ne_zero 2 (Units.ne_zero (uniformizerPowerUnit K (-s))))
    anisotropic

/-- The enlarged lattice has the same projection along `y` as `N`. -/
theorem projectedLattice_lemma57EnlargedLattice
    (q : QuadraticSpace K V) (N : Lattice K V) (y : V)
    (anisotropic : q.IsAnisotropic y) (s : Int) :
    Lattice.projectedLattice q (lemma57EnlargedLattice N y s) y
        anisotropic =
      Lattice.projectedLattice q N y anisotropic := by
  exact Lattice.projectedLattice_adjoinVector_smul q N y anisotropic
    (uniformizerPowerUnit K (-s) : K)

/-- If `Q(y)` has order `S`, then `Q(π⁻ˢ y)` has order `S - 2s`. -/
theorem ord_quadratic_lemma57EnlargedHead
    (q : QuadraticSpace K V) (y : V) (s S : Int)
    (horder : ord K (q.quadratic y) = (S : WithTop Int)) :
    ord K (q.quadratic (lemma57EnlargedHead (K := K) y s)) =
      ((S - 2 * s : Int) : WithTop Int) := by
  rw [lemma57EnlargedHead, q.quadratic_smul, ord_mul, ord_pow,
    ← coe_ordUnit, ordUnit_uniformizerPowerUnit, horder]
  norm_cast
  ring

/-- The scaled vector is a norm generator of the enlarged lattice.  This is
the norm-ideal argument in the first paragraph of Lemma 5.7's proof. -/
theorem lemma57EnlargedHead_isNormGenerator
    (q : QuadraticSpace K V) {N : Lattice K V} {y : V}
    (generator : Lattice.IsNormGenerator q N y)
    {s : Int} (hs : 0 ≤ s) :
    Lattice.IsNormGenerator q (lemma57EnlargedLattice N y s)
      (lemma57EnlargedHead (K := K) y s) := by
  let a : Kˣ := uniformizerPowerUnit K (-s)
  have hmem := lemma57EnlargedHead_mem (K := K) N y s
  have hle : lemma57EnlargedLattice N y s ≤ Lattice.rescale a N := by
    exact lemma57EnlargedLattice_le_rescale (K := K) N generator.mem hs
  have hscaled := generator.rescale a
  constructor
  · exact hmem
  · apply le_antisymm
    · calc
        Lattice.normIdeal q (lemma57EnlargedLattice N y s) ≤
            Lattice.normIdeal q (Lattice.rescale a N) :=
          Lattice.normIdeal_mono q hle
        _ = Lattice.principalIdeal (K := K)
            (q.quadratic ((a : K) • y)) := hscaled.normIdeal_eq
        _ = Lattice.principalIdeal (K := K)
            (q.quadratic (lemma57EnlargedHead (K := K) y s)) := by
          rfl
    · rw [Lattice.principalIdeal, Submodule.span_le]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact Lattice.quadratic_mem_normIdeal_of_mem q
        (lemma57EnlargedLattice N y s) hmem

end BONG

end Bong
