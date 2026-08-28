/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Structural

/-!
# Choosing and reindexing good BONGs

This file provides the small choice and length-transport layer needed by
recursive constructions that use `BONGStructuralLaws.exists_good_bong`.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {m n : Nat}

/-- Transport only the length index of a good BONG. -/
noncomputable def castLength (b : GoodBONG q L m) (h : m = n) :
    GoodBONG q L n :=
  h ▸ b

@[simp]
theorem order_castLength (b : GoodBONG q L m) (h : m = n)
    (i : Fin n) :
    (b.castLength h).order i = b.order ⟨i.val, by omega⟩ := by
  subst n
  rfl

@[simp]
theorem ambientVector_castLength_eq (b : GoodBONG q L m) (h : m = n)
    (i : Fin n) :
    (b.castLength h).toBONG.ambientVector i =
      b.toBONG.ambientVector ⟨i.val, by omega⟩ := by
  subst n
  rfl

/-- A chosen good BONG of a lattice, using the explicit structural-law
interface for good-BONG existence. -/
noncomputable def ofLattice [BONGStructuralLaws.{u, v} K]
    (q : QuadraticSpace K V) (L : Lattice K V) :
    GoodBONG q L (Module.finrank K V) :=
  Classical.choice (exists_good_bong q L)

end BONG.GoodBONG

end Bong
