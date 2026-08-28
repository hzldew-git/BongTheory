/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019EnlargedProjection
import Bong.Bong.GoodCons

/-!
# Beli (2019), the good BONG of the Lemma 5.7 enlargement

This file prepends `π⁻ˢy` to the transported projected good BONG.  Its first
order is `S - 2s`, its remaining orders are unchanged, and the inequality
`S - 2s ≤ R₃` makes the resulting BONG good.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- The possibly bad BONG of `N` beginning with the prescribed norm
generator `y` and followed by the chosen good projected tail. -/
noncomputable def lemma57OriginalCandidate (q : QuadraticSpace K V)
    (N : Lattice K V) {y : V}
    (generator : Lattice.IsNormGenerator q N y)
    (anisotropic : q.IsAnisotropic y) {n : Nat}
    (tail : GoodBONG (q.orthogonalSpace y anisotropic)
      (Lattice.projectedLattice q N y anisotropic) (n + 1)) :
    BONG V q N (n + 2) :=
  BONG.cons y generator anisotropic tail.toBONG

/-- The BONG of the enlarged lattice beginning with `π⁻ˢy` and followed by
the transported chosen tail. -/
noncomputable def lemma57EnlargedCandidate (q : QuadraticSpace K V)
    (N : Lattice K V) {y : V}
    (generator : Lattice.IsNormGenerator q N y)
    (anisotropic : q.IsAnisotropic y) (s : Int) (hs : 0 ≤ s)
    {n : Nat}
    (tail : GoodBONG (q.orthogonalSpace y anisotropic)
      (Lattice.projectedLattice q N y anisotropic) (n + 1)) :
    BONG V q (lemma57EnlargedLattice N y s) (n + 2) :=
  BONG.cons (lemma57EnlargedHead (K := K) y s)
    (lemma57EnlargedHead_isNormGenerator q generator hs)
    (q.isAnisotropic_smul anisotropic
      (Units.ne_zero (uniformizerPowerUnit K (-s))))
    (lemma57ProjectedGoodBONG q N anisotropic s tail).toBONG

@[simp]
theorem lemma57OriginalCandidate_head (q : QuadraticSpace K V)
    (N : Lattice K V) {y : V}
    (generator : Lattice.IsNormGenerator q N y)
    (anisotropic : q.IsAnisotropic y) {n : Nat}
    (tail : GoodBONG (q.orthogonalSpace y anisotropic)
      (Lattice.projectedLattice q N y anisotropic) (n + 1)) :
    (lemma57OriginalCandidate q N generator anisotropic tail).head = y :=
  rfl

@[simp]
theorem lemma57EnlargedCandidate_head (q : QuadraticSpace K V)
    (N : Lattice K V) {y : V}
    (generator : Lattice.IsNormGenerator q N y)
    (anisotropic : q.IsAnisotropic y) (s : Int) (hs : 0 ≤ s)
    {n : Nat}
    (tail : GoodBONG (q.orthogonalSpace y anisotropic)
      (Lattice.projectedLattice q N y anisotropic) (n + 1)) :
    (lemma57EnlargedCandidate q N generator anisotropic s hs tail).head =
      lemma57EnlargedHead (K := K) y s :=
  rfl

@[simp]
theorem lemma57OriginalCandidate_order_succ (q : QuadraticSpace K V)
    (N : Lattice K V) {y : V}
    (generator : Lattice.IsNormGenerator q N y)
    (anisotropic : q.IsAnisotropic y) {n : Nat}
    (tail : GoodBONG (q.orthogonalSpace y anisotropic)
      (Lattice.projectedLattice q N y anisotropic) (n + 1))
    (i : Fin (n + 1)) :
    (lemma57OriginalCandidate q N generator anisotropic tail).order i.succ =
      tail.order i := by
  rfl

@[simp]
theorem lemma57EnlargedCandidate_order_succ (q : QuadraticSpace K V)
    (N : Lattice K V) {y : V}
    (generator : Lattice.IsNormGenerator q N y)
    (anisotropic : q.IsAnisotropic y) (s : Int) (hs : 0 ≤ s)
    {n : Nat}
    (tail : GoodBONG (q.orthogonalSpace y anisotropic)
      (Lattice.projectedLattice q N y anisotropic) (n + 1))
    (i : Fin (n + 1)) :
    (lemma57EnlargedCandidate q N generator anisotropic s hs tail).order
        i.succ =
      tail.order i := by
  exact lemma57ProjectedGoodBONG_order q N anisotropic s tail i

/-- The first order of the enlarged candidate is `S - 2s`. -/
theorem lemma57EnlargedCandidate_order_zero (q : QuadraticSpace K V)
    (N : Lattice K V) {y : V}
    (generator : Lattice.IsNormGenerator q N y)
    (anisotropic : q.IsAnisotropic y) (s S : Int) (hs : 0 ≤ s)
    {n : Nat}
    (tail : GoodBONG (q.orthogonalSpace y anisotropic)
      (Lattice.projectedLattice q N y anisotropic) (n + 1))
    (horder : ord K (q.quadratic y) = (S : WithTop Int)) :
    (lemma57EnlargedCandidate q N generator anisotropic s hs tail).order 0 =
      S - 2 * s := by
  apply WithTop.coe_injective
  rw [BONG.coe_order]
  change ord K
      (q.quadratic (lemma57EnlargedHead (K := K) y s)) =
    ((S - 2 * s : Int) : WithTop Int)
  exact ord_quadratic_lemma57EnlargedHead q y s S horder

/-- The condition `S - 2s ≤ R₃` is precisely the only new goodness
condition for the enlarged candidate. -/
theorem lemma57EnlargedCandidate_isGood (q : QuadraticSpace K V)
    (N : Lattice K V) {y : V}
    (generator : Lattice.IsNormGenerator q N y)
    (anisotropic : q.IsAnisotropic y) (s S : Int) (hs : 0 ≤ s)
    {n : Nat}
    (tail : GoodBONG (q.orthogonalSpace y anisotropic)
      (Lattice.projectedLattice q N y anisotropic) (n + 1))
    (horder : ord K (q.quadratic y) = (S : WithTop Int))
    (headLeThird : ∀ hi : 2 < n + 2,
      S - 2 * s ≤ tail.order ⟨1, by omega⟩) :
    (lemma57EnlargedCandidate q N generator anisotropic s hs tail).IsGood := by
  let b := lemma57EnlargedCandidate q N generator anisotropic s hs tail
  apply BONG.IsGood.cons_of_tail_of_head_le_third
  · exact (lemma57ProjectedGoodBONG q N anisotropic s tail).good
  · intro hi
    let i : Fin (n + 1) := ⟨1, by omega⟩
    have hindex : i.succ = (⟨2, hi⟩ : Fin (n + 2)) := by
      apply Fin.ext
      simp [i]
    calc
      b.order 0 = S - 2 * s :=
        lemma57EnlargedCandidate_order_zero q N generator anisotropic
          s S hs tail horder
      _ ≤ tail.order i := headLeThird hi
      _ = b.order i.succ := by
        symm
        exact lemma57EnlargedCandidate_order_succ q N generator
          anisotropic s hs tail i
      _ = b.order ⟨2, hi⟩ := congrArg b.order hindex

/-- The bundled good BONG of the Lemma 5.7 enlarged lattice. -/
noncomputable def lemma57EnlargedGoodBONG (q : QuadraticSpace K V)
    (N : Lattice K V) {y : V}
    (generator : Lattice.IsNormGenerator q N y)
    (anisotropic : q.IsAnisotropic y) (s S : Int) (hs : 0 ≤ s)
    {n : Nat}
    (tail : GoodBONG (q.orthogonalSpace y anisotropic)
      (Lattice.projectedLattice q N y anisotropic) (n + 1))
    (horder : ord K (q.quadratic y) = (S : WithTop Int))
    (headLeThird : ∀ hi : 2 < n + 2,
      S - 2 * s ≤ tail.order ⟨1, by omega⟩) :
    GoodBONG q (lemma57EnlargedLattice N y s) (n + 2) where
  toBONG := lemma57EnlargedCandidate q N generator anisotropic s hs tail
  good := lemma57EnlargedCandidate_isGood q N generator anisotropic
    s S hs tail horder headLeThird

end BONG

end Bong
