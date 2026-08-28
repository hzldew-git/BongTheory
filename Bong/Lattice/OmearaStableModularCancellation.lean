/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaHyperbolicTowerNormalizationScaled

/-!
# O'Meara 93:14a: modular hyperbolic cancellation

The proof follows the published argument literally.  O'Meara 82:16 splits a
modular lattice on a hyperbolic space into planes `a A(alpha_i,0)`.  The norm
group containment and 93:13 normalize all coefficients to zero.  Theorem
93:14 then cancels the resulting common `a A(0,0)` planes one at a time.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {W : Type u} [AddCommGroup W] [Module K W]

/-- The identity coordinates identify `a A(0,0)` with the scaled
hyperbolic plane of scale `a`. -/
noncomputable def scaledZeroOmearaPlaneLatticeIsometry (a : Kˣ) :
    Isometry
      ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit a)
      (QuadraticSpace.hyperbolicPlane a)
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) where
  toLinearEquiv := LinearEquiv.refl K (Fin 2 → K)
  map_bilin := by
    intro x y
    rw [QuadraticSpace.hyperbolicPlane_bilin_apply,
      QuadraticSpace.rescaleUnit_bilin_apply,
      QuadraticSpace.omearaPlane_bilin_apply]
    simp only [LinearEquiv.refl_apply, zero_mul, zero_add]
  map_mem _ := Iff.rfl

/-- Cancel a finite common tower of scaled zero-coefficient O'Meara planes.
This is Theorem 93:14 iterated over the explicit nested carrier. -/
noncomputable def cancelScaledZeroOmearaPlaneExtension (a : Kˣ) :
    (n : Nat) →
      {q : QuadraticSpace K V} → {r : QuadraticSpace K W} →
      {L : Lattice K V} → {M : Lattice K W} →
      Isometry
        (omearaPlaneExtensionForm q a n (fun _ => 0))
        (omearaPlaneExtensionForm r a n (fun _ => 0))
        (hyperbolicExtensionLattice L n)
        (hyperbolicExtensionLattice M n) →
      Isometry q r L M
  | 0, _, _, _, _, f => f
  | n + 1, q, r, L, M, f => by
      have f' : Isometry
          (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit a).orthogonalSum
            (omearaPlaneExtensionForm q a n (fun _ => 0)))
          (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit a).orthogonalSum
            (omearaPlaneExtensionForm r a n (fun _ => 0)))
          (product (hyperbolicPlaneLattice (K := K))
            (hyperbolicExtensionLattice L n))
          (product (hyperbolicPlaneLattice (K := K))
            (hyperbolicExtensionLattice M n)) := by
        change Isometry
          (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit a).orthogonalSum
            (omearaPlaneExtensionForm q a n (fun _ => 0)))
          (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit a).orthogonalSum
            (omearaPlaneExtensionForm r a n (fun _ => 0)))
          (product (hyperbolicPlaneLattice (K := K))
            (hyperbolicExtensionLattice L n))
          (product (hyperbolicPlaneLattice (K := K))
            (hyperbolicExtensionLattice M n)) at f
        exact f
      let tailIsometry := omeara9314_scaled_of_isometric_summand
        a (scaledZeroOmearaPlaneLatticeIsometry a)
          (scaledZeroOmearaPlaneLatticeIsometry a) f'
      exact cancelScaledZeroOmearaPlaneExtension a n tailIsometry

/-- O'Meara 93:14a on the explicit modular decompositions supplied by
82:16.  No cancellation or local-law instance is assumed. -/
noncomputable def omeara9314a
    {n : Nat}
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K (HyperbolicExtension K V n)}
    {M : Lattice K (HyperbolicExtension K W n)}
    (a : Kˣ)
    (D : HyperbolicModularDecomposition q a n L)
    (E : HyperbolicModularDecomposition r a n M)
    (hD : normGroupSet (hyperbolicExtensionForm q n) L ⊆
      normGroupSet q (omearaScaleTruncation q D.tailLattice a))
    (hE : normGroupSet (hyperbolicExtensionForm r n) M ⊆
      normGroupSet r (omearaScaleTruncation r E.tailLattice a))
    (f : Isometry (hyperbolicExtensionForm q n)
      (hyperbolicExtensionForm r n) L M) :
    Isometry q r D.tailLattice E.tailLattice := by
  let normalizeD := D.normalizedIsometry hD
  let normalizeE := E.normalizedIsometry hE
  let commonTower := normalizeD.trans (f.trans normalizeE.symm)
  exact cancelScaledZeroOmearaPlaneExtension a n commonTower

/-- Construct the two 82:16 decompositions and apply 93:14a.  The only
hypotheses are the published modularity and norm-group containments, phrased
against the tails canonically produced by the decomposition. -/
noncomputable def omeara9314a_of_modular
    {n : Nat}
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (a : Kˣ)
    (L : Lattice K (HyperbolicExtension K V n))
    (M : Lattice K (HyperbolicExtension K W n))
    (hL : IsModular (hyperbolicExtensionForm q n) L a)
    (hM : IsModular (hyperbolicExtensionForm r n) M a)
    (hgroupL : normGroupSet (hyperbolicExtensionForm q n) L ⊆
      normGroupSet q
        (omearaScaleTruncation q
          (hyperbolicModularDecomposition q a n L hL).tailLattice a))
    (hgroupM : normGroupSet (hyperbolicExtensionForm r n) M ⊆
      normGroupSet r
        (omearaScaleTruncation r
          (hyperbolicModularDecomposition r a n M hM).tailLattice a))
    (f : Isometry (hyperbolicExtensionForm q n)
      (hyperbolicExtensionForm r n) L M) :
    Isometry q r
      (hyperbolicModularDecomposition q a n L hL).tailLattice
      (hyperbolicModularDecomposition r a n M hM).tailLattice :=
  omeara9314a a
    (hyperbolicModularDecomposition q a n L hL)
    (hyperbolicModularDecomposition r a n M hM)
    hgroupL hgroupM f

end Lattice

end Bong
