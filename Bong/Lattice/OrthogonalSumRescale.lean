/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Isometry
import Bong.Lattice.Product
import Bong.QuadraticSpace.OrthogonalSum

/-!
# Rescaling orthogonal sums

Common rescaling distributes over an orthogonal sum.  We expose both the
ambient and integral identity isometries, together with composition of two
form rescalings.  These elementary transports let the normalized statement
of O'Meara 93:19 be used at an arbitrary first Jordan scale.
-/

namespace Bong

namespace QuadraticSpace

universe u v w

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

/-- Rescaling the source and target of a field isometry by the same scalar
preserves the isometry. -/
def Isometry.rescaleUnitBoth
    {p : QuadraticSpace K V} {q : QuadraticSpace K W}
    (f : Isometry p q) (a : Kˣ) :
    Isometry (p.rescaleUnit a) (q.rescaleUnit a) where
  toLinearEquiv := f.toLinearEquiv
  map_bilin := by
    intro x y
    simp only [rescaleUnit_bilin_apply]
    rw [f.map_bilin]

/-- Common form rescaling distributes over an orthogonal sum. -/
def rescaleUnitOrthogonalSumIsometry
    (p : QuadraticSpace K V) (q : QuadraticSpace K W) (a : Kˣ) :
    Isometry ((p.orthogonalSum q).rescaleUnit a)
      ((p.rescaleUnit a).orthogonalSum (q.rescaleUnit a)) where
  toLinearEquiv := LinearEquiv.refl K (V × W)
  map_bilin := by
    intro x y
    simp only [rescaleUnit_bilin_apply, orthogonalSum_bilin_apply,
      LinearEquiv.refl_apply]
    ring

/-- Two successive rescalings multiply their factors in outer-to-inner
order. -/
def rescaleUnitMulIsometry
    (q : QuadraticSpace K V) (a b : Kˣ) :
    Isometry ((q.rescaleUnit a).rescaleUnit b)
      (q.rescaleUnit (b * a)) where
  toLinearEquiv := LinearEquiv.refl K V
  map_bilin := by
    intro x y
    simp only [rescaleUnit_bilin_apply, LinearEquiv.refl_apply,
      Units.val_mul]
    rw [mul_assoc]

end QuadraticSpace

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

/-- Integral version of distribution of a common form rescaling. -/
def rescaleUnitOrthogonalProductIsometry
    (p : QuadraticSpace K V) (q : QuadraticSpace K W)
    (L : Lattice K V) (M : Lattice K W) (a : Kˣ) :
    Isometry ((p.orthogonalSum q).rescaleUnit a)
      ((p.rescaleUnit a).orthogonalSum (q.rescaleUnit a))
      (product L M) (product L M) where
  toLinearEquiv := LinearEquiv.refl K (V × W)
  map_bilin := by
    intro x y
    simp only [QuadraticSpace.rescaleUnit_bilin_apply,
      QuadraticSpace.orthogonalSum_bilin_apply, LinearEquiv.refl_apply]
    ring
  map_mem := by intro x; rfl

/-- Integral identity for composition of two form rescalings. -/
def rescaleUnitMulLatticeIsometry
    (q : QuadraticSpace K V) (L : Lattice K V) (a b : Kˣ) :
    Isometry ((q.rescaleUnit a).rescaleUnit b)
      (q.rescaleUnit (b * a)) L L where
  toLinearEquiv := LinearEquiv.refl K V
  map_bilin := by
    intro x y
    simp only [QuadraticSpace.rescaleUnit_bilin_apply,
      LinearEquiv.refl_apply, Units.val_mul]
    rw [mul_assoc]
  map_mem := by intro x; rfl

end Lattice

end Bong
