/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M6 structural smoke tests

These examples exercise the M6 interfaces: refined unit square classes, exact
defect domination, full dual lattices, rescaling and modularity, determinant
classes, Jordan structures, and the ambient orthogonal basis carried by a BONG.
-/

namespace BongTest.M6

open Bong
open Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

example : IsPrincipalIdealRing (IntegerRing K) :=
  inferInstance

example (a u : Kˣ) (hu : IsValuationUnit K (u : K)) :
    unitSquareClass K (a * u ^ 2) = unitSquareClass K a :=
  unitSquareClass_mul_unit_square K a u hu

example {a b : Kˣ} (h : quadraticDefect K a ≠ quadraticDefect K b) :
    quadraticDefect K (a * b) =
      min (quadraticDefect K a) (quadraticDefect K b) :=
  quadraticDefect_mul_eq_min_of_ne (K := K) h

example (q : QuadraticSpace K V) (M : Submodule (IntegerRing K) V) :
    M ≤ Bong.Lattice.dualSubmodule q (Bong.Lattice.dualSubmodule q M) :=
  Bong.Lattice.le_dualSubmodule_dualSubmodule q M

example (q : QuadraticSpace K V) (L : Bong.Lattice K V) :
    L.toSubmodule ≤ Bong.Lattice.dualModule q L ↔
      Bong.Lattice.IsScaleIntegral q L :=
  Bong.Lattice.le_dualModule_iff_isScaleIntegral q L

example (q : QuadraticSpace K V) (L : Bong.Lattice K V) :
    Bong.Lattice.dualLattice q (Bong.Lattice.dualLattice q L) = L :=
  Bong.Lattice.dualLattice_dualLattice q L

example (q : QuadraticSpace K V) (L : Bong.Lattice K V) (a : Kˣ) :
    Bong.Lattice.dualLattice q (Bong.Lattice.rescale a L) =
      Bong.Lattice.rescale a⁻¹ (Bong.Lattice.dualLattice q L) :=
  Bong.Lattice.dualLattice_rescale q a L

example {q : QuadraticSpace K V} {L : Bong.Lattice K V} {a : Kˣ}
    (hL : Bong.Lattice.IsModular q L a) :
    Bong.Lattice.IsModular q (Bong.Lattice.dualLattice q L) a⁻¹ :=
  hL.dual

example {q : QuadraticSpace K V} {L : Bong.Lattice K V} {n : Nat}
    (b : Bong.BONG V q L n) : n = Module.finrank K V :=
  b.length_eq_finrank

example {q : QuadraticSpace K V} {L : Bong.Lattice K V} {n : Nat}
    (b : Bong.BONG V q L n) :
    b.gramDeterminant = (b.valueProduct : K) :=
  b.gramDeterminant_eq_valueProduct

example {q : QuadraticSpace K V} {L : Bong.Lattice K V} {n : Nat}
    (b : Bong.BONG V q L n) :
    squareClass K (Bong.Lattice.determinantUnit q L) =
      squareClass K b.valueProduct :=
  Bong.Lattice.determinantSquareClass_eq_valueProduct b

example {q : QuadraticSpace K V} {L M : Bong.Lattice K V} {n : Nat}
    (b : Bong.BONG V q L n) (c : Bong.BONG V q M n) :
    squareClass K b.valueProduct = squareClass K c.valueProduct :=
  b.valueProduct_squareClass_eq c

example {q : QuadraticSpace K V} {L : Bong.Lattice K V} {n : Nat}
    (b : Bong.BONG V q L n) (i : Fin n) :
    IsValuationUnit K (b.normalizedValue i : K) :=
  b.normalizedValue_isValuationUnit i

example {q : QuadraticSpace K V} {L : Bong.Lattice K V} {n : Nat}
    (b : Bong.BONG V q L (n + 1)) (hb : b.HasPropertyB) : b.IsGood :=
  hb.isGood

example {q : QuadraticSpace K V} {L : Bong.Lattice K V} {n : Nat}
    (b : Bong.BONG V q L n) (i : Fin n) :
    q.quadratic (b.reverseDualVector i) =
      ((b.valueUnit (Fin.rev i))⁻¹ : K) :=
  b.quadratic_reverseDualVector i

section StructuralLaws

variable [Bong.BONGStructuralLaws.{u, v} K]

example {q : QuadraticSpace K V} {L : Bong.Lattice K V} {n : Nat}
    (b : Bong.BONG V q L n) :
    Bong.Lattice.HasJordanPropertyA q L ↔ b.HasPropertyA :=
  Bong.Lattice.hasJordanPropertyA_iff_bongHasPropertyA b

example {q : QuadraticSpace K V} {L : Bong.Lattice K V} {n : Nat}
    (b : Bong.BONG V q L n) (start length : Nat)
    (bound : start + length ≤ n) :
    Nonempty (Bong.BONG.SegmentWitness b start length bound) :=
  b.exists_segmentWitness start length bound

end StructuralLaws

end

end BongTest.M6
