/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrefixExtensionBase

/-!
# Beli (2019), replacing a good projected tail

The induction step in Corollary 5.10 replaces the good BONG of a projected
lattice and then prepends the already chosen head.  Since good BONG orders are
invariant on a fixed lattice, the new tail has the same orders as the old one,
so goodness at the head boundary is preserved.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Replace the projected tail of a nonempty BONG while retaining its head. -/
noncomputable def replaceTail (c : BONG V q L (n + 2))
    (t : BONG (q.vectorOrthogonal c.head)
      (q.orthogonalSpace c.head c.head_isAnisotropic)
      (L.projectedLattice q c.head c.head_isAnisotropic) (n + 1)) :
    BONG V q L (n + 2) :=
  BONG.cons c.head c.head_isNormGenerator c.head_isAnisotropic t

@[simp]
theorem replaceTail_head (c : BONG V q L (n + 2))
    (t : BONG (q.vectorOrthogonal c.head)
      (q.orthogonalSpace c.head c.head_isAnisotropic)
      (L.projectedLattice q c.head c.head_isAnisotropic) (n + 1)) :
    (c.replaceTail t).head = c.head :=
  rfl

@[simp]
theorem replaceTail_tail (c : BONG V q L (n + 2))
    (t : BONG (q.vectorOrthogonal c.head)
      (q.orthogonalSpace c.head c.head_isAnisotropic)
      (L.projectedLattice q c.head c.head_isAnisotropic) (n + 1)) :
    (c.replaceTail t).tail = t :=
  rfl

end BONG

namespace BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Replacing a good projected tail by another good BONG of the same
projected lattice preserves goodness after the common head is prepended. -/
theorem replaceTail_isGood [BeliLemma47Laws.{u, v} K]
    (c : GoodBONG q L (n + 2))
    (t : GoodBONG
      (q.orthogonalSpace c.toBONG.head c.toBONG.head_isAnisotropic)
      (L.projectedLattice q c.toBONG.head c.toBONG.head_isAnisotropic)
      (n + 1)) :
    (c.toBONG.replaceTail t.toBONG).IsGood := by
  let d := c.toBONG.replaceTail t.toBONG
  have horders :=
    t.toBONG.beliLemma47_orders_eq c.tail.toBONG t.good c.tail.good
  cases n with
  | zero =>
      exact d.isGood_of_length_le_two (by omega)
  | succ n =>
      intro i hi
      cases i using Fin.cases with
      | zero =>
          calc
            d.order 0 = c.toBONG.order 0 :=
              d.order_zero_eq_of_same_lattice c.toBONG
            _ ≤ c.toBONG.order 2 := c.good 0 (by omega)
            _ = c.toBONG.tail.order 1 :=
              (c.toBONG.order_tail 1).symm
            _ = t.toBONG.order 1 := (horders 1).symm
            _ = d.order 2 := d.order_tail 1
      | succ j =>
          simp only [Fin.val_succ] at hi
          let k : Fin (n + 1 + 1) := ⟨j.val + 2, by omega⟩
          have ht : t.toBONG.order j ≤ t.toBONG.order k :=
            t.good j (by omega)
          have hk :
              k.succ =
                (⟨j.val + 1 + 2, hi⟩ : Fin (n + 1 + 2)) := by
            apply Fin.ext
            simp [k]
          calc
            d.order j.succ = t.toBONG.order j :=
              (d.order_tail j).symm
            _ ≤ t.toBONG.order k := ht
            _ = d.order k.succ := d.order_tail k
            _ = d.order ⟨j.val + 1 + 2, hi⟩ :=
              congrArg d.order hk

/-- The bundled good BONG obtained after replacing the projected tail. -/
noncomputable def replaceTailGood [BeliLemma47Laws.{u, v} K]
    (c : GoodBONG q L (n + 2))
    (t : GoodBONG
      (q.orthogonalSpace c.toBONG.head c.toBONG.head_isAnisotropic)
      (L.projectedLattice q c.toBONG.head c.toBONG.head_isAnisotropic)
      (n + 1)) :
    GoodBONG q L (n + 2) where
  toBONG := c.toBONG.replaceTail t.toBONG
  good := c.replaceTail_isGood t

@[simp]
theorem replaceTailGood_head [BeliLemma47Laws.{u, v} K]
    (c : GoodBONG q L (n + 2))
    (t : GoodBONG
      (q.orthogonalSpace c.toBONG.head c.toBONG.head_isAnisotropic)
      (L.projectedLattice q c.toBONG.head c.toBONG.head_isAnisotropic)
      (n + 1)) :
    (c.replaceTailGood t).toBONG.head = c.toBONG.head :=
  rfl

end BONG.GoodBONG

end Bong
