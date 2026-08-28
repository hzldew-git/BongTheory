/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaFundamentalInvariants

/-!
# Algebra of O'Meara fundamental types

Equality of complete fundamental type is reflexive, symmetric, and
transitive.  The explicit constructions are useful when a Jordan splitting
is replaced by a saturated splitting of the same lattice.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w z

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {X : Type z} [AddCommGroup X] [Module K X]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K X}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K X}
  {a b c : Nat}
  {J : JordanDecomposition q L a}
  {H : JordanDecomposition r M b}
  {T : JordanDecomposition s N c}

/-- Reflexivity of complete fundamental type. -/
noncomputable def SameFundamentalType.refl
    (J : JordanDecomposition q L a) : SameFundamentalType J J where
  indexEquiv := Equiv.refl _
  index_val := fun _ ↦ rfl
  componentRank_eq := fun _ ↦ rfl
  scaleOrder_eq := fun _ ↦ rfl
  normGroup_eq := fun _ ↦ rfl

/-- Symmetry of complete fundamental type. -/
noncomputable def SameFundamentalType.symm
    (F : SameFundamentalType J H) : SameFundamentalType H J where
  indexEquiv := F.indexEquiv.symm
  index_val := by
    intro j
    have h := F.index_val (F.indexEquiv.symm j)
    rw [F.indexEquiv.apply_symm_apply] at h
    exact h.symm
  componentRank_eq := by
    intro j
    have h := F.componentRank_eq (F.indexEquiv.symm j)
    rw [F.indexEquiv.apply_symm_apply] at h
    exact h.symm
  scaleOrder_eq := by
    intro j
    have h := F.scaleOrder_eq (F.indexEquiv.symm j)
    rw [F.indexEquiv.apply_symm_apply] at h
    exact h.symm
  normGroup_eq := by
    intro j
    have h := F.normGroup_eq (F.indexEquiv.symm j)
    rw [F.indexEquiv.apply_symm_apply] at h
    exact h.symm

/-- Transitivity of complete fundamental type. -/
noncomputable def SameFundamentalType.trans
    (F : SameFundamentalType J H) (G : SameFundamentalType H T) :
    SameFundamentalType J T where
  indexEquiv := F.indexEquiv.trans G.indexEquiv
  index_val := by
    intro i
    exact (G.index_val (F.indexEquiv i)).trans (F.index_val i)
  componentRank_eq := by
    intro i
    exact (G.componentRank_eq (F.indexEquiv i)).trans
      (F.componentRank_eq i)
  scaleOrder_eq := by
    intro i
    exact (G.scaleOrder_eq (F.indexEquiv i)).trans
      (F.scaleOrder_eq i)
  normGroup_eq := by
    intro i
    exact (G.normGroup_eq (F.indexEquiv i)).trans
      (F.normGroup_eq i)

end Lattice.JordanDecomposition

end Bong
