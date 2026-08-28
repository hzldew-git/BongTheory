/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Prefix
import Bong.Lattice.Determinant

/-!
# Determinants of BONG prefixes

This file identifies the value product of the BONG carried by an exact prefix
witness with the corresponding prefix product of the original BONG.  Combined
with the ordinary change-of-basis determinant calculation, it gives an actual
square-factor witness between a BONG prefix product and the determinant of its
exact prefix lattice.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n length : Nat}
  {bound : length ≤ n} {b : BONG V q L n}

/-- The BONG on an exact prefix has the original BONG's prefix value product. -/
theorem PrefixWitness.valueProduct_eq_prefixProduct
    (w : PrefixWitness b length bound) :
    w.bong.valueProduct = b.prefixProduct length := by
  have hleft :
      w.bong.valueProduct = ∏ i : Fin length, w.bong.valueUnit i := by
    simp [valueProduct, prefixProduct]
  rw [hleft]
  unfold prefixProduct
  refine Finset.prod_bij (fun i _ => w.sourceIndex i) ?_ ?_ ?_ ?_
  · intro i _
    simp [SegmentWitness.sourceIndex]
  · intro i₁ _ i₂ _ h
    apply Fin.ext
    simpa [SegmentWitness.sourceIndex] using congrArg Fin.val h
  · intro j hj
    have hjlt : j.val < length := (Finset.mem_filter.mp hj).2
    refine ⟨⟨j.val, hjlt⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp [SegmentWitness.sourceIndex]
  · intro i _
    exact w.valueUnit_eq i

/--
The original BONG prefix product is the determinant of its exact prefix lattice
times a square.  This is the witness-level bridge used with O'Meara 93:28(i).
-/
theorem PrefixWitness.exists_prefixProduct_eq_determinantUnit_mul_square
    (w : PrefixWitness b length bound) :
    ∃ p : Kˣ,
      b.prefixProduct length =
        Lattice.determinantUnit (q.restrict w.carrier w.nondegenerate)
          w.lattice * p ^ 2 := by
  rcases Lattice.exists_valueProduct_eq_determinantUnit_mul_square w.bong with
    ⟨p, hp⟩
  exact ⟨p, w.valueProduct_eq_prefixProduct.symm.trans hp⟩

end BONG

end Bong
