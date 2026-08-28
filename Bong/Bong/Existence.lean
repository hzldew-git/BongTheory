/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Basic
import Bong.Lattice.NormGenerator

/-!
# Existence of BONGs

Every positive-dimensional lattice has an anisotropic norm generator.  Taking
its projected lattice lowers dimension by one, so recursive construction
terminates and produces a BONG of the ambient dimension.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Transport only the length index of a BONG. -/
noncomputable def castLength {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {m n : ℕ}
    (b : BONG V q L m) (h : m = n) : BONG V q L n :=
  h ▸ b

/-- Casting the length index does not change ambient vectors. -/
@[simp]
theorem ambientVector_castLength {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {m n : ℕ}
    (b : BONG V q L m) (h : m = n) (i : Fin n) :
    (b.castLength h).ambientVector i =
      b.ambientVector ⟨i.1, by simpa [h] using i.2⟩ := by
  subst n
  rfl

/-- A chosen BONG of every quadratic lattice. -/
noncomputable def ofLattice {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) :
    BONG V q L (Module.finrank K V) := by
  letI : Module.Finite K V := L.moduleFinite
  by_cases hzero : Module.finrank K V = 0
  · have hV : Subsingleton V := Module.finrank_zero_iff.mp hzero
    exact castLength (BONG.nil q L hV) hzero.symm
  · have hpos : 0 < Module.finrank K V := Nat.pos_of_ne_zero hzero
    let hexists := Lattice.exists_isNormGenerator_of_finrank_pos q L hpos
    let x := Classical.choose hexists
    have hx := Classical.choose_spec hexists
    let generator : Lattice.IsNormGenerator q L x := hx.1
    let anisotropic : q.IsAnisotropic x := hx.2
    let tail := ofLattice (q.orthogonalSpace x anisotropic)
      (L.projectedLattice q x anisotropic)
    have horth : Module.finrank K (q.vectorOrthogonal x) =
        Module.finrank K V - 1 := by
      change Module.finrank K (q.bilin.orthogonal (K ∙ x)) = _
      rw [q.bilin.finrank_orthogonal q.nondegenerate,
        finrank_span_singleton anisotropic.ne_zero]
    have hlength : Module.finrank K (q.vectorOrthogonal x) + 1 =
        Module.finrank K V := by
      rw [horth]
      exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hzero)
    exact castLength (BONG.cons x generator anisotropic tail) hlength
termination_by Module.finrank K V
decreasing_by
  letI : Module.Finite K V := L.moduleFinite
  change Module.finrank K (q.bilin.orthogonal (K ∙ x)) <
    Module.finrank K V
  rw [q.bilin.finrank_orthogonal q.nondegenerate,
    finrank_span_singleton anisotropic.ne_zero]
  exact Nat.sub_lt hpos Nat.zero_lt_one

/-- Every lattice admits a BONG of its ambient dimension. -/
theorem exists_ofLattice {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) :
    Nonempty (BONG V q L (Module.finrank K V)) :=
  ⟨ofLattice q L⟩

/-- A prescribed anisotropic norm generator can be chosen as the first vector
of a binary BONG. -/
noncomputable def ofNormGeneratorBinary
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) (x : V)
    (generator : Lattice.IsNormGenerator q L x)
    (anisotropic : q.IsAnisotropic x)
    (hfin : Module.finrank K V = 2) :
    BONG V q L 2 := by
  letI : Module.Finite K V := L.moduleFinite
  have horthfin : Module.finrank K (q.vectorOrthogonal x) = 1 := by
    have hdim := q.finrank_vectorOrthogonal anisotropic
    omega
  let tail := (ofLattice (q.orthogonalSpace x anisotropic)
    (L.projectedLattice q x anisotropic)).castLength horthfin
  exact BONG.cons x generator anisotropic tail

@[simp]
theorem ambientVector_ofNormGeneratorBinary_zero
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) (x : V)
    (generator : Lattice.IsNormGenerator q L x)
    (anisotropic : q.IsAnisotropic x)
    (hfin : Module.finrank K V = 2) :
    (ofNormGeneratorBinary q L x generator anisotropic hfin).ambientVector 0 =
      x := by
  rw [ofNormGeneratorBinary, ambientVector_cons_zero]

@[simp]
theorem head_ofNormGeneratorBinary
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) (x : V)
    (generator : Lattice.IsNormGenerator q L x)
    (anisotropic : q.IsAnisotropic x)
    (hfin : Module.finrank K V = 2) :
    (ofNormGeneratorBinary q L x generator anisotropic hfin).head = x := by
  rw [← ambientVector_zero_eq_head,
    ambientVector_ofNormGeneratorBinary_zero]

end BONG

end Bong
