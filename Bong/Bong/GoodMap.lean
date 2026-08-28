/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Good
import Bong.Bong.Map

/-!
# Transporting good BONGs by lattice isometries

Lattice isometries preserve every BONG order.  Consequently they transport
the two-step inequalities defining a good BONG.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- A lattice isometry preserves every integral BONG order. -/
@[simp]
theorem order_mapLatticeIsometry (f : Lattice.Isometry q r L M)
    (b : BONG V q L n) (i : Fin n) :
    (b.mapLatticeIsometry f).order i = b.order i := by
  apply WithTop.coe_injective
  rw [coe_order, coe_order, value_mapLatticeIsometry]

/-- Goodness is invariant under a lattice isometry. -/
theorem IsGood.mapLatticeIsometry (f : Lattice.Isometry q r L M)
    {b : BONG V q L n} (good : b.IsGood) :
    (b.mapLatticeIsometry f).IsGood := by
  intro i hi
  simpa only [order_mapLatticeIsometry] using good i hi

namespace GoodBONG

/-- Transport a good BONG along an ambient isometry, placing it on the
image lattice. -/
noncomputable def map (f : QuadraticSpace.Isometry q r)
    (b : GoodBONG q L n) :
    GoodBONG r (Lattice.map f.toLinearEquiv L) n where
  toBONG := b.toBONG.map f
  good := by
    intro i hi
    simpa only [BONG.order_map] using b.good i hi

@[simp]
theorem order_map (f : QuadraticSpace.Isometry q r)
    (b : GoodBONG q L n) (i : Fin n) :
    (b.map f).order i = b.order i :=
  BONG.order_map f b.toBONG i

/-- Ambient isometries preserve the nonzero BONG values as units. -/
@[simp]
theorem valueUnit_map (f : QuadraticSpace.Isometry q r)
    (b : GoodBONG q L n) (i : Fin n) :
    (b.map f).valueUnit i = b.valueUnit i := by
  apply Units.ext
  exact BONG.value_map f b.toBONG i

/-- Transport a good BONG along a lattice isometry. -/
noncomputable def mapLatticeIsometry (f : Lattice.Isometry q r L M)
    (b : GoodBONG q L n) : GoodBONG r M n where
  toBONG := b.toBONG.mapLatticeIsometry f
  good := b.good.mapLatticeIsometry f

@[simp]
theorem order_mapLatticeIsometry (f : Lattice.Isometry q r L M)
    (b : GoodBONG q L n) (i : Fin n) :
    (b.mapLatticeIsometry f).order i = b.order i := by
  exact BONG.order_mapLatticeIsometry f b.toBONG i

@[simp]
theorem valueUnit_mapLatticeIsometry (f : Lattice.Isometry q r L M)
    (b : GoodBONG q L n) (i : Fin n) :
    (b.mapLatticeIsometry f).valueUnit i = b.valueUnit i := by
  apply Units.ext
  exact BONG.value_mapLatticeIsometry f b.toBONG i

end GoodBONG

end BONG

end Bong
