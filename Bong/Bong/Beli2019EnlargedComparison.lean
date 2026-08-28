/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019EnlargedCandidate
import Bong.Bong.Beli2019NestedOrder
import Bong.Bong.Beli2019ProjectionNormIdeal
import Bong.Bong.Beli2019VolumeOrders

/-!
# Beli (2019), comparison data from the Lemma 5.7 enlargement

This file assembles the enlarged-lattice construction into the exact
`NormGeneratorComparisonData` interface used by Corollary 5.9.  The order
relation comes from `N ≤ M`; the suffix equality follows from the determinant
formula for the two BONGs sharing the same projected tail.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {N : Lattice K V} {n : Nat}

/-- Any BONG of the same lattice has tail-order sum equal to the suffix of a
good BONG once their common, lattice-determined first order is removed. -/
theorem orderSequence_suffixSum_one_eq_sum_tail_order_of_bong
    (a : GoodBONG q N (n + 2)) (c : BONG V q N (n + 2)) :
    a.orderSequence.suffixSum 1 = ∑ i, c.tail.order i := by
  rw [a.orderSequence_suffixSum_one_eq_volumeOrder_sub,
    c.sum_tail_order_eq_volumeOrder_sub_order_zero]
  have hzero := c.order_zero_eq_of_same_lattice a.toBONG
  rw [hzero]
  rfl

/-- Lemma 5.7's enlarged lattice supplies all comparison data required in
Corollary 5.9. -/
theorem normGeneratorComparisonData_lemma57
    [Beli2019OrderNecessityLaws.{u, v} K]
    (a : GoodBONG q N (n + 2)) {y : V}
    (generator : Lattice.IsNormGenerator q N y)
    (anisotropic : q.IsAnisotropic y) (s S : Int) (hs : 0 ≤ s)
    (tail : GoodBONG (q.orthogonalSpace y anisotropic)
      (Lattice.projectedLattice q N y anisotropic) (n + 1))
    (horder : ord K (q.quadratic y) = (S : WithTop Int))
    (headLeThird : ∀ hi : 2 < n + 2,
      S - 2 * s ≤ tail.order ⟨1, by omega⟩) :
    NormGeneratorComparisonData a
      (lemma57OriginalCandidate q N generator anisotropic tail)
      (lemma57EnlargedGoodBONG q N generator anisotropic s S hs tail
        horder headLeThird).orderSequence := by
  let c := lemma57OriginalCandidate q N generator anisotropic tail
  let d := lemma57EnlargedGoodBONG q N generator anisotropic s S hs
    tail horder headLeThird
  change NormGeneratorComparisonData a c d.orderSequence
  refine
    { order_le := ?_
      tail_sum := ?_
      tail_good := ?_
      tail_order := ?_ }
  · exact d.orderSequence_le_of_lattice_le a
      (le_lemma57EnlargedLattice N y s)
  · calc
      d.orderSequence.suffixSum 1 = ∑ i, d.toBONG.tail.order i :=
        d.orderSequence_suffixSum_one_eq_sum_tail_order
      _ = ∑ i, c.tail.order i := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          d.toBONG.tail.order i = d.toBONG.order i.succ :=
            d.toBONG.order_tail i
          _ = tail.order i := by
            exact lemma57EnlargedCandidate_order_succ q N generator
              anisotropic s hs tail i
          _ = c.order i.succ := by
            exact (lemma57OriginalCandidate_order_succ q N generator
              anisotropic tail i).symm
          _ = c.tail.order i := (c.order_tail i).symm
      _ = a.orderSequence.suffixSum 1 :=
        (a.orderSequence_suffixSum_one_eq_sum_tail_order_of_bong c).symm
  · change tail.toBONG.IsGood
    exact tail.good
  · intro i
    have hi : i.val + 1 < n + 2 := by omega
    calc
      d.orderSequence.entryOrZero (i.val + 1) =
          d.order ⟨i.val + 1, hi⟩ := by
        rw [BeliOrderSequence.entryOrZero_of_lt d.orderSequence hi]
        exact d.orderSequence_at (i.val + 1) hi
      _ = d.order i.succ := by
        congr 2
      _ = tail.order i := by
        exact lemma57EnlargedCandidate_order_succ q N generator
          anisotropic s hs tail i
      _ = c.order i.succ := by
        exact (lemma57OriginalCandidate_order_succ q N generator
          anisotropic tail i).symm

end BONG.GoodBONG

end Bong
