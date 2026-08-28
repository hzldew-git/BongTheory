/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaHyperbolicCancellation

/-!
# Finite hyperbolic cancellation

This file iterates the one-plane cancellation theorem `omeara9314_scaled`.
Instead of fixing a parenthesized product carrier in advance, it records the
successive common adjunctions as a proof-relevant tower.  This avoids any
universe-dependent coercion at the bottom of the tower and matches the way
O'Meara 93:14a is used: first identify finitely many common scaled
hyperbolic planes, then cancel them from the outside in.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A quadratic space together with a full lattice, bundled so that finite
hyperbolic adjunctions may change the carrier while retaining their actual
additive and scalar structures. -/
structure QuadraticLatticeModel where
  Carrier : Type u
  [addCommGroup : AddCommGroup Carrier]
  [module : Module K Carrier]
  form : QuadraticSpace K Carrier
  lattice : Lattice K Carrier

namespace QuadraticLatticeModel

/-- Integral isometries between bundled quadratic lattices. -/
abbrev Isometry (X Y : QuadraticLatticeModel (K := K)) : Type u := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup Y.Carrier := Y.addCommGroup
  letI : Module K Y.Carrier := Y.module
  exact Lattice.Isometry X.form Y.form X.lattice Y.lattice

/-- Adjoin one standard lattice on the scaled hyperbolic plane. -/
noncomputable def adjoinHyperbolic (scale : Kˣ)
    (X : QuadraticLatticeModel (K := K)) :
    QuadraticLatticeModel (K := K) := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  exact
    { Carrier := (Fin 2 → K) × X.Carrier
      form := (QuadraticSpace.hyperbolicPlane scale).orthogonalSum X.form
      lattice := product (hyperbolicPlaneLattice (K := K)) X.lattice }

end QuadraticLatticeModel

/-- A finite sequence of simultaneous scaled-hyperbolic adjunctions to two
quadratic lattices.  The `step` constructor adds the same outer plane on
both sides. -/
inductive CommonHyperbolicTower
    (source target : QuadraticLatticeModel (K := K)) :
    QuadraticLatticeModel (K := K) →
      QuadraticLatticeModel (K := K) → Type (u + 1)
  | base : CommonHyperbolicTower source target source target
  | step (scale : Kˣ) {left right : QuadraticLatticeModel (K := K)}
      (tail : CommonHyperbolicTower source target left right) :
      CommonHyperbolicTower source target
        (left.adjoinHyperbolic scale) (right.adjoinHyperbolic scale)

namespace CommonHyperbolicTower

/-- O'Meara 93:14 iterated over an arbitrary finite common hyperbolic
tower.  Thus the finite cancellation step of 93:14a contains no additional
cancellation hypothesis. -/
noncomputable def cancel
    {source target left right : QuadraticLatticeModel (K := K)}
    (tower : CommonHyperbolicTower source target left right)
    (f : left.Isometry right) : source.Isometry target := by
  induction tower with
  | base => exact f
  | @step scale left right tail ih =>
      letI : AddCommGroup left.Carrier := left.addCommGroup
      letI : Module K left.Carrier := left.module
      letI : AddCommGroup right.Carrier := right.addCommGroup
      letI : Module K right.Carrier := right.module
      apply ih
      exact omeara9314_scaled scale f

end CommonHyperbolicTower

/-- Bundle an ordinary quadratic lattice without changing any structure. -/
noncomputable def quadraticLatticeModel
    {V : Type u} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) :
    QuadraticLatticeModel (K := K) where
  Carrier := V
  form := q
  lattice := L

end Lattice

end Bong
