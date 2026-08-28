/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BasisLattice
import Bong.Bong.BinaryInvariant

/-!
# Binary lattice uniqueness from a common norm generator

This file formalizes Beli (2003), Lemma 3.2(ii): a binary lattice is uniquely
determined by a chosen norm generator and its relative order `R(L)`.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- Binary BONGs with the same head have the same first order. -/
theorem order_zero_eq_of_head_eq {M : Lattice K V}
    (b : BONG V q L 2) (c : BONG V q M 2)
    (hhead : b.head = c.head) : b.order 0 = c.order 0 := by
  apply WithTop.coe_injective
  rw [b.coe_order, c.coe_order,
    b.value_zero_eq_quadratic_head,
    c.value_zero_eq_quadratic_head, hhead]

/-- Beli (2003), Lemma 3.2(ii): a common norm generator and equal relative
order determine a binary lattice. -/
theorem lattice_eq_of_head_eq_of_binaryOrderGap_eq
    {M : Lattice K V} (b : BONG V q L 2) (c : BONG V q M 2)
    (hhead : b.head = c.head)
    (hgap : b.binaryOrderGap = c.binaryOrderGap) : L = M := by
  have hzero : b.order 0 = c.order 0 :=
    b.order_zero_eq_of_head_eq c hhead
  have hone : b.order 1 = c.order 1 := by
    change b.order 1 - b.order 0 =
      c.order 1 - c.order 0 at hgap
    omega
  cases b with
  | @cons V _ _ q L _ x generator anisotropic tail =>
      cases c with
      | @cons _ _ _ _ M _ y generator' anisotropic' tail' =>
          change x = y at hhead
          subst y
          have han : anisotropic' = anisotropic := Subsingleton.elim _ _
          subst anisotropic'
          have htailOrder : tail.order 0 = tail'.order 0 := by
            calc
              tail.order 0 =
                  (BONG.cons x generator anisotropic tail).order 1 :=
                order_tail (BONG.cons x generator anisotropic tail) 0
              _ = (BONG.cons x generator' anisotropic tail').order 1 :=
                hone
              _ = tail'.order 0 :=
                (order_tail
                  (BONG.cons x generator' anisotropic tail') 0).symm
          have hprojection :
              L.projectedLattice q x anisotropic =
                M.projectedLattice q x anisotropic :=
            tail.lattice_eq_of_order_eq tail' htailOrder
          apply Lattice.eq_of_normIdeal_eq_of_projectedLattice_eq
            q L M x generator generator' anisotropic
          · exact generator.normIdeal_eq.trans
              generator'.normIdeal_eq.symm
          · exact hprojection

/-- Beli (2003), Lemma 3.2(i): for binary BONGs with a common head norm
generator, lattice inclusion is reverse relative-order comparison. -/
theorem le_iff_binaryOrderGap_ge_of_head_eq
    {M : Lattice K V} (b : BONG V q L 2) (c : BONG V q M 2)
    (hhead : b.head = c.head) :
    L ≤ M ↔ c.binaryOrderGap ≤ b.binaryOrderGap := by
  have hzero : b.order 0 = c.order 0 :=
    b.order_zero_eq_of_head_eq c hhead
  constructor
  · intro hLM
    cases b with
    | @cons V _ _ q L _ x generator anisotropic tail =>
        cases c with
        | @cons _ _ _ _ M _ y generator' anisotropic' tail' =>
            change x = y at hhead
            subst y
            have han : anisotropic' = anisotropic := Subsingleton.elim _ _
            subst anisotropic'
            have hprojection :
                L.projectedLattice q x anisotropic ≤
                  M.projectedLattice q x anisotropic :=
              Lattice.projectedLattice_mono q hLM x anisotropic
            have htailOrder : tail'.order 0 ≤ tail.order 0 :=
              tail.order_ge_of_le tail' hprojection
            have hone :
                (BONG.cons x generator' anisotropic tail').order 1 ≤
                  (BONG.cons x generator anisotropic tail).order 1 := by
              calc
                (BONG.cons x generator' anisotropic tail').order 1 =
                    tail'.order 0 :=
                  (order_tail
                    (BONG.cons x generator' anisotropic tail') 0).symm
                _ ≤ tail.order 0 := htailOrder
                _ = (BONG.cons x generator anisotropic tail).order 1 :=
                  order_tail
                    (BONG.cons x generator anisotropic tail) 0
            change
              (BONG.cons x generator' anisotropic tail').order 1 -
                  (BONG.cons x generator' anisotropic tail').order 0 ≤
                (BONG.cons x generator anisotropic tail).order 1 -
                  (BONG.cons x generator anisotropic tail).order 0
            omega
  · intro hgap
    have hone : c.order 1 ≤ b.order 1 := by
      change c.order 1 - c.order 0 ≤
        b.order 1 - b.order 0 at hgap
      omega
    cases b with
    | @cons V _ _ q L _ x generator anisotropic tail =>
        cases c with
        | @cons _ _ _ _ M _ y generator' anisotropic' tail' =>
            change x = y at hhead
            subst y
            have han : anisotropic' = anisotropic := Subsingleton.elim _ _
            subst anisotropic'
            have htailOrder : tail'.order 0 ≤ tail.order 0 := by
              calc
                tail'.order 0 =
                    (BONG.cons x generator' anisotropic tail').order 1 :=
                  order_tail
                    (BONG.cons x generator' anisotropic tail') 0
                _ ≤ (BONG.cons x generator anisotropic tail).order 1 :=
                  hone
                _ = tail.order 0 :=
                  (order_tail
                    (BONG.cons x generator anisotropic tail) 0).symm
            have hprojection :
                L.projectedLattice q x anisotropic ≤
                  M.projectedLattice q x anisotropic :=
              tail.le_of_order_ge tail' htailOrder
            apply Lattice.le_of_normIdeal_le_of_projectedLattice_le
              q M L x generator' anisotropic
            · rw [generator.normIdeal_eq, generator'.normIdeal_eq]
            · exact hprojection

end BONG

end Bong
