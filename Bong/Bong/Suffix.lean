/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Map
import Bong.Bong.Segment

/-!
# Suffixes of a recursive BONG

This file realizes every recursive tail of a BONG inside the original ambient
space.  It is the BONG-existence part of Beli (2003), Lemma 2.7(i).
-/

namespace Bong

open Dyadic

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

private theorem restrictTop_nondegenerate :
    (q.bilin.restrict (⊤ : Submodule K V)).Nondegenerate := by
  constructor
  · intro x hx
    apply Subtype.ext
    exact q.nondegenerate.1 (x : V) (fun y => hx ⟨y, trivial⟩)
  · intro y hy
    apply Subtype.ext
    exact q.nondegenerate.2 (y : V) (fun x => hy ⟨x, trivial⟩)

private theorem mapCarrier_nondegenerate {x : V}
    (anisotropic : q.IsAnisotropic x)
    (S : Submodule K (q.vectorOrthogonal x))
    (hS : ((q.orthogonalSpace x anisotropic).bilin.restrict S).Nondegenerate) :
    (q.bilin.restrict
      (S.map (q.vectorOrthogonal x).subtype)).Nondegenerate := by
  let e := (q.vectorOrthogonal x).equivSubtypeMap S
  constructor
  · intro y hy
    apply e.symm.injective
    apply hS.1
    intro z
    change q.bilin ((e.symm y : S) : V) (z : V) = 0
    simpa [e] using hy (e z)
  · intro y hy
    apply e.symm.injective
    apply hS.2
    intro z
    change q.bilin (z : V) ((e.symm y : S) : V) = 0
    simpa [e] using hy (e z)

private noncomputable def zeroSuffixWitness (b : BONG V q L n) :
    SegmentWitness b 0 n (by omega) := by
  let nondegenerate := restrictTop_nondegenerate (q := q)
  let f : QuadraticSpace.Isometry q
      (q.restrict (⊤ : Submodule K V) nondegenerate) :=
    { toLinearEquiv := Submodule.topEquiv.symm
      map_bilin _ _ := rfl }
  exact
    { carrier := ⊤
      nondegenerate := nondegenerate
      lattice := Lattice.map f.toLinearEquiv L
      bong := b.map f
      ambientVector_eq := by
        intro i
        rw [ambientVector_map]
        change b.ambientVector i = b.ambientVector ⟨0 + i.1, by omega⟩
        congr 1
        apply Fin.ext
        simp }

private noncomputable def liftSuffixWitness
    {m start length : Nat} {x : V}
    {generator : Lattice.IsNormGenerator q L x}
    {anisotropic : q.IsAnisotropic x}
    (tail : BONG (q.vectorOrthogonal x) (q.orthogonalSpace x anisotropic)
      (L.projectedLattice q x anisotropic) m)
    (bound : start + length ≤ m)
    (w : SegmentWitness tail start length bound) :
    SegmentWitness (BONG.cons x generator anisotropic tail)
      (start + 1) length (by omega) := by
  let carrier : Submodule K V :=
    w.carrier.map (q.vectorOrthogonal x).subtype
  let nondegenerate : (q.bilin.restrict carrier).Nondegenerate :=
    mapCarrier_nondegenerate anisotropic w.carrier w.nondegenerate
  let f : QuadraticSpace.Isometry
      ((q.orthogonalSpace x anisotropic).restrict
        w.carrier w.nondegenerate)
      (q.restrict carrier nondegenerate) :=
    { toLinearEquiv := (q.vectorOrthogonal x).equivSubtypeMap w.carrier
      map_bilin _ _ := rfl }
  exact
    { carrier := carrier
      nondegenerate := nondegenerate
      lattice := Lattice.map f.toLinearEquiv w.lattice
      bong := w.bong.map f
      ambientVector_eq := by
        intro i
        rw [ambientVector_map]
        change (w.bong.ambientVector i : V) =
          (BONG.cons x generator anisotropic tail).ambientVector
            ⟨(start + 1) + i.1, by omega⟩
        calc
          (w.bong.ambientVector i : V) =
              (tail.ambientVector (w.sourceIndex i) : V) :=
            congrArg Subtype.val (w.ambientVector_eq i)
          _ = (BONG.cons x generator anisotropic tail).ambientVector
              (w.sourceIndex i).succ := by
            rw [ambientVector_cons_succ]
          _ = (BONG.cons x generator anisotropic tail).ambientVector
              ⟨(start + 1) + i.1, by omega⟩ := by
            congr 1
            apply Fin.ext
            simp [SegmentWitness.sourceIndex]
            omega }

/-- The suffix beginning at `start` is a BONG in its ambient subspace. -/
noncomputable def suffixWitness (b : BONG V q L n)
    (start : Nat) (bound : start ≤ n) :
    SegmentWitness b start (n - start) (by omega) := by
  induction start generalizing V n with
  | zero =>
      simpa using zeroSuffixWitness b
  | succ start ih =>
      cases b with
      | nil _ _ _ => omega
      | @cons V _ _ q L m x generator anisotropic tail =>
          have tailBound : start ≤ m := by omega
          let w := ih tail tailBound
          simpa [Nat.succ_eq_add_one] using
            liftSuffixWitness tail (by omega) w

/-- Every recursive suffix has a segment realization, without extra laws. -/
theorem exists_suffixWitness (b : BONG V q L n)
    (start : Nat) (bound : start ≤ n) :
    Nonempty (SegmentWitness b start (n - start) (by omega)) :=
  ⟨b.suffixWitness start bound⟩

end BONG

end Bong
