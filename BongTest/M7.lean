/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M7 Section 2 smoke tests

These examples exercise the minimal projection laws for Beli (2003), Section 2,
their recursive determinant and reconstruction consequences, and the concrete
API of consecutive BONG segment witnesses.
-/

namespace BongTest.M7

open Bong
open Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

example (q : QuadraticSpace K V) (L : Bong.Lattice K V)
    (hV : Subsingleton V) :
    Bong.Lattice.determinantClass q L = 1 :=
  Bong.Lattice.determinantClass_eq_one_of_subsingleton q L hV

section DeterminantProjection

variable [Bong.BONGDeterminantProjectionLaws.{u, v} K]

example {q : QuadraticSpace K V} {L : Bong.Lattice K V} {n : Nat}
    (b : Bong.BONG V q L n) :
    Bong.Lattice.determinantClass q L = unitSquareClass K b.valueProduct :=
  b.determinantClass_eq_valueProduct

end DeterminantProjection

section Reconstruction

variable [Bong.BONGReconstructionLaws.{u, v} K]

example {q : QuadraticSpace K V} {L M : Bong.Lattice K V} {n : Nat}
    (b : Bong.BONG V q L n) (c : Bong.BONG V q M n)
    (vectors : ∀ i, b.ambientVector i = c.ambientVector i) : L = M :=
  b.lattice_eq_of_ambientVector_eq_from_projection c vectors

end Reconstruction

section Combined

variable [Bong.BONGSectionTwoLaws.{u, v} K]

example : Bong.BONGDeterminantProjectionLaws.{u, v} K :=
  inferInstance

example : Bong.BONGReconstructionLaws.{u, v} K :=
  inferInstance

end Combined

section Segments

variable {q : QuadraticSpace K V} {L : Bong.Lattice K V} {n : Nat}
  {b : Bong.BONG V q L n} {start length : Nat}
  {bound : start + length ≤ n}

example (w : Bong.BONG.SegmentWitness b start length bound)
    (i : Fin length) :
    w.bong.value i = b.value (w.sourceIndex i) :=
  w.value_eq i

example (w : Bong.BONG.SegmentWitness b start length bound)
    (hb : b.IsGood) : w.bong.IsGood :=
  w.isGood hb

example (w : Bong.BONG.SegmentWitness b start length bound)
    (hb : b.HasPropertyA) : w.bong.HasPropertyA :=
  w.hasPropertyA hb

end Segments

end

end BongTest.M7
