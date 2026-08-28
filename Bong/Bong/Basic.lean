/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Projection

/-!
# Bases of norm generators

A BONG is defined recursively, exactly as in Beli's Definition 2.  Its first
vector is an anisotropic norm generator of the lattice, and its tail is a BONG
of the lattice obtained by orthogonally projecting to the complement of that
vector.  The empty constructor records that the remaining quadratic space has
been exhausted.

The successive vectors live in successive orthogonal complements, so the
recursive certificate is dependent.  Scalar quadratic values nevertheless all
live in the original field and can be exposed as a `Fin`-indexed family.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/--
A basis of norm generators (BONG) of length `n`.

The ambient vector space is an index rather than a fixed parameter: after the
head is removed, the recursive tail belongs to its orthogonal complement.
-/
inductive BONG :
    (V : Type v) → [AddCommGroup V] → [Module K V] → QuadraticSpace K V →
      Lattice K V → Nat → Type (max (u + 1) (v + 1))
  | nil {V : Type v} [AddCommGroup V] [Module K V]
      (q : QuadraticSpace K V) (L : Lattice K V) (exhausted : Subsingleton V) :
      BONG V q L 0
  | cons {V : Type v} [AddCommGroup V] [Module K V]
      {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
      (x : V) (generator : Lattice.IsNormGenerator q L x)
      (anisotropic : q.IsAnisotropic x)
      (tail : BONG (q.vectorOrthogonal x) (q.orthogonalSpace x anisotropic)
        (L.projectedLattice q x anisotropic) n) :
      BONG V q L (n + 1)

namespace BONG

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The first vector in a nonempty BONG. -/
def head (b : BONG V q L (n + 1)) : V := by
  cases b with
  | cons x _ _ _ => exact x

/-- The first vector is a norm generator of the original lattice. -/
theorem head_isNormGenerator (b : BONG V q L (n + 1)) :
    Lattice.IsNormGenerator q L b.head := by
  cases b with
  | cons _ generator _ _ => exact generator

/-- The first vector in a nonempty BONG is anisotropic. -/
theorem head_isAnisotropic (b : BONG V q L (n + 1)) :
    q.IsAnisotropic b.head := by
  cases b with
  | cons _ _ anisotropic _ => exact anisotropic

/-- The recursive BONG in the projected orthogonal complement. -/
def tail (b : BONG V q L (n + 1)) :
    BONG (q.vectorOrthogonal b.head) (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic) n := by
  cases b with
  | cons _ _ _ tail => exact tail

private def valueNil {V' : Type v} [AddCommGroup V'] [Module K V']
    (_q : QuadraticSpace K V') (_L : Lattice K V') (_ : Subsingleton V') :
    Fin 0 → K :=
  Fin.elim0

private def valueCons {V' : Type v} [AddCommGroup V'] [Module K V']
    {q' : QuadraticSpace K V'} {L' : Lattice K V'} {m : Nat}
    (x : V') (_ : Lattice.IsNormGenerator q' L' x) (hx : q'.IsAnisotropic x)
    (_tail : BONG (q'.vectorOrthogonal x) (q'.orthogonalSpace x hx)
      (L'.projectedLattice q' x hx) m) (tailValue : Fin m → K) :
    Fin (m + 1) → K :=
  Fin.cases (q'.quadratic x) tailValue

/-- The quadratic values `a_i = Q(x_i)` of a BONG. -/
noncomputable def value (b : BONG V q L n) : Fin n → K :=
  BONG.rec (motive := fun _ _ _ _ _ m _ => Fin m → K) valueNil valueCons b

@[simp]
theorem value_cons_zero {x : V} {hx : Lattice.IsNormGenerator q L x}
    {han : q.IsAnisotropic x}
    {b : BONG (q.vectorOrthogonal x) (q.orthogonalSpace x han)
      (L.projectedLattice q x han) n} :
    (BONG.cons x hx han b).value 0 = q.quadratic x :=
  rfl

@[simp]
theorem value_cons_succ {x : V} {hx : Lattice.IsNormGenerator q L x}
    {han : q.IsAnisotropic x}
    {b : BONG (q.vectorOrthogonal x) (q.orthogonalSpace x han)
      (L.projectedLattice q x han) n} (i : Fin n) :
    (BONG.cons x hx han b).value i.succ = b.value i :=
  rfl

@[simp]
theorem value_tail (b : BONG V q L (n + 1)) (i : Fin n) :
    b.tail.value i = b.value i.succ := by
  cases b
  rfl

/-- The zeroth BONG value is the quadratic value of the recursive head. -/
theorem value_zero_eq_quadratic_head (b : BONG V q L (n + 1)) :
    b.value 0 = q.quadratic b.head := by
  cases b with
  | cons x _ _ _ =>
      change q.quadratic x = q.quadratic x
      rfl

/-- Every quadratic value occurring in a BONG is nonzero. -/
theorem value_ne_zero (b : BONG V q L n) (i : Fin n) : b.value i ≠ 0 := by
  induction b with
  | nil => exact Fin.elim0 i
  | cons x _ anisotropic _ ih =>
      refine Fin.cases ?_ (fun j => ih j) i
      exact anisotropic

/-- The nonzero quadratic values, regarded as units of the field. -/
noncomputable def valueUnit (b : BONG V q L n) (i : Fin n) : Kˣ :=
  Units.mk0 (b.value i) (b.value_ne_zero i)

@[simp]
theorem coe_valueUnit (b : BONG V q L n) (i : Fin n) :
    (b.valueUnit i : K) = b.value i :=
  rfl

/-- The integral order `R_i = ord(a_i)` of a BONG value. -/
noncomputable def order (b : BONG V q L n) (i : Fin n) : Int :=
  (ord K (b.value i)).untop ((ord_eq_top_iff K).not.mpr (b.value_ne_zero i))

@[simp]
theorem coe_order (b : BONG V q L n) (i : Fin n) :
    (b.order i : WithTop Int) = ord K (b.value i) :=
  WithTop.coe_untop _ _

@[simp]
theorem order_eq_ordUnit (b : BONG V q L n) (i : Fin n) :
    b.order i = ordUnit K (b.valueUnit i) :=
  rfl

@[simp]
theorem order_tail (b : BONG V q L (n + 1)) (i : Fin n) :
    b.tail.order i = b.order i.succ := by
  apply WithTop.coe_injective
  simp only [coe_order, value_tail]

/-- Product of the first `i` BONG values. -/
noncomputable def prefixProduct (b : BONG V q L n) (i : Nat) : Kˣ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.1 < i), b.valueUnit j

@[simp]
theorem prefixProduct_zero (b : BONG V q L n) : b.prefixProduct 0 = 1 := by
  simp [prefixProduct]

/-- Appending one BONG value gives the expected recurrence for prefix
products. -/
theorem prefixProduct_succ (b : BONG V q L n) (i : Nat) (hi : i < n) :
    b.prefixProduct (i + 1) =
      b.prefixProduct i * b.valueUnit ⟨i, hi⟩ := by
  classical
  have hset :
      Finset.univ.filter (fun j : Fin n ↦ j.1 < i + 1) =
        insert ⟨i, hi⟩
          (Finset.univ.filter (fun j : Fin n ↦ j.1 < i)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro hj
      by_cases hji : j.1 = i
      · left
        exact Fin.ext hji
      · right
        omega
    · rintro (rfl | hj)
      · exact Nat.lt_succ_self i
      · omega
  rw [prefixProduct, prefixProduct, hset]
  rw [Finset.prod_insert]
  · ac_rfl
  · simp

/-- Product of all quadratic values of a BONG. -/
noncomputable def valueProduct (b : BONG V q L n) : Kˣ :=
  b.prefixProduct n

end BONG

end Bong
