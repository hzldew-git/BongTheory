/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Basis
import Bong.Lattice.OrthogonalMap

/-!
# Transporting BONGs by ambient isometries

An isometry carries a BONG to a BONG of the image lattice.  The recursive
step uses the induced isometry between orthogonal complements and the fact
that projected lattices commute with ambient isometries.
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
  {L : Lattice K V} {n : Nat}

/-- The image of a BONG under an ambient quadratic-space isometry. -/
noncomputable def map (f : QuadraticSpace.Isometry q r)
    (b : BONG V q L n) :
    BONG W r (Lattice.map f.toLinearEquiv L) n :=
  BONG.rec
    (motive := fun V _ _ q L n _ =>
      ∀ {W : Type w} [AddCommGroup W] [Module K W]
        (r : QuadraticSpace K W) (f : QuadraticSpace.Isometry q r),
        BONG W r (Lattice.map f.toLinearEquiv L) n)
    (fun _ _ exhausted _ _ _ r f =>
      .nil r (Lattice.map f.toLinearEquiv _)
        ⟨fun y z => f.toLinearEquiv.symm.injective
          (exhausted.elim (f.toLinearEquiv.symm y)
            (f.toLinearEquiv.symm z))⟩)
    (fun x generator anisotropic _ mapTail _ _ _ r f =>
      let mappedAnisotropic := f.map_isAnisotropic anisotropic
      let mappedGenerator : Lattice.IsNormGenerator r
          (Lattice.map f.toLinearEquiv _) (f.toLinearEquiv x) :=
        ⟨(Lattice.map_mem_map_iff f.toLinearEquiv _ x).2 generator.mem,
          by
            rw [Lattice.normIdeal_map_isometry f,
              generator.normIdeal_eq, f.map_quadratic]⟩
      let mappedTail := mapTail _ (f.orthogonalIsometry x anisotropic)
      let transportedTail := mappedTail.castLattice
        (Lattice.projectedLattice_map_isometry f x anisotropic).symm
      .cons (f.toLinearEquiv x) mappedGenerator mappedAnisotropic
        transportedTail)
    b r f

/-- Ambient isometries preserve the quadratic-value sequence of a BONG. -/
@[simp]
theorem value_map (f : QuadraticSpace.Isometry q r)
    (b : BONG V q L n) (i : Fin n) :
    (b.map f).value i = b.value i := by
  induction b generalizing W with
  | nil => exact Fin.elim0 i
  | cons x generator anisotropic tail ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [map]
      · simpa [map] using
          ih (f := f.orthogonalIsometry x anisotropic) j

/-- Ambient isometries preserve the order sequence of a BONG. -/
@[simp]
theorem order_map (f : QuadraticSpace.Isometry q r)
    (b : BONG V q L n) (i : Fin n) :
    (b.map f).order i = b.order i := by
  apply WithTop.coe_injective
  rw [coe_order, coe_order, value_map]

/-- The ambient vectors of the mapped BONG are the isometric images. -/
@[simp]
theorem ambientVector_map (f : QuadraticSpace.Isometry q r)
    (b : BONG V q L n) (i : Fin n) :
    (b.map f).ambientVector i = f.toLinearEquiv (b.ambientVector i) := by
  induction b generalizing W with
  | nil => exact Fin.elim0 i
  | cons x generator anisotropic tail ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [map]
      · simp only [map, ambientVector_cons_succ,
          ambientVector_castLattice]
        have h := ih (f := f.orthogonalIsometry x anisotropic) j
        exact congrArg Subtype.val h

/-- A lattice isometry carries a BONG directly to the target lattice. -/
noncomputable def mapLatticeIsometry {M : Lattice K W}
    (f : Lattice.Isometry q r L M) (b : BONG V q L n) :
    BONG W r M n :=
  (b.map f.toQuadraticSpaceIsometry).castLattice f.map_eq

/-- A lattice isometry preserves the quadratic-value sequence. -/
@[simp]
theorem value_mapLatticeIsometry {M : Lattice K W}
    (f : Lattice.Isometry q r L M) (b : BONG V q L n)
    (i : Fin n) :
    (b.mapLatticeIsometry f).value i = b.value i := by
  simp [mapLatticeIsometry]

/-- Ambient vectors are carried by the underlying lattice isometry. -/
@[simp]
theorem ambientVector_mapLatticeIsometry {M : Lattice K W}
    (f : Lattice.Isometry q r L M) (b : BONG V q L n)
    (i : Fin n) :
    (b.mapLatticeIsometry f).ambientVector i =
      f.toLinearEquiv (b.ambientVector i) := by
  simp [mapLatticeIsometry]
  rfl

end BONG

end Bong
