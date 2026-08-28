/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019EnlargedComparison
import Bong.Bong.Beli2019PrescribedHead

/-!
# Beli (2019), existence of the enlarged comparison sequence

For a prescribed norm-generator head and a chosen good projected tail, this
file chooses a sufficiently large nonnegative `s` and constructs the
comparison sequence required by Corollary 5.9.  In rank at least three we use
`s = max 0 (S₁ - R₃)`; in rank two the head-to-third condition is vacuous.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- The enlarged lattice construction automatically supplies a comparison
sequence for the prescribed-head candidate. -/
theorem exists_normGeneratorComparisonData_prescribedHeadCandidateWithTail
    [Beli2019OrderNecessityLaws.{u, v} K]
    (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (hNM : N ≤ M) (hzero : a.order 0 = b.order 0)
    (tail : GoodBONG
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (M.projectedLattice q b.toBONG.head
        b.toBONG.head_isAnisotropic) (n + 1)) :
    ∃ x : BeliOrderSequence (n + 2) Int,
      NormGeneratorComparisonData a
        (a.prescribedHeadCandidateWithTail b hNM hzero tail) x := by
  let generator := a.prescribedHead_isNormGenerator b hNM hzero
  have horder : ord K (q.quadratic b.toBONG.head) =
      ((a.order 0 : Int) : WithTop Int) := by
    rw [← b.toBONG.value_zero_eq_quadratic_head,
      ← b.toBONG.coe_order]
    norm_cast
    exact hzero.symm
  cases n with
  | zero =>
      let d := lemma57EnlargedGoodBONG q M generator
        b.toBONG.head_isAnisotropic 0 (a.order 0) (by omega) tail
        horder (by intro hi; omega)
      refine ⟨d.orderSequence, ?_⟩
      change NormGeneratorComparisonData a
        (lemma57OriginalCandidate q M generator
          b.toBONG.head_isAnisotropic tail) d.orderSequence
      exact a.normGeneratorComparisonData_lemma57 generator
        b.toBONG.head_isAnisotropic 0 (a.order 0) (by omega) tail
        horder (by intro hi; omega)
  | succ m =>
      let third : Int := tail.order (1 : Fin (m + 2))
      let s : Int := max 0 (a.order 0 - third)
      have hs : 0 ≤ s := by
        exact le_max_left 0 (a.order 0 - third)
      have hdifference : a.order 0 - third ≤ s := by
        exact le_max_right 0 (a.order 0 - third)
      have hthird : a.order 0 - 2 * s ≤ third := by
        omega
      have headLeThird : ∀ hi : 2 < m.succ + 2,
          a.order 0 - 2 * s ≤ tail.order ⟨1, by omega⟩ := by
        intro hi
        have hindex : (⟨1, by omega⟩ : Fin (m + 2)) = 1 := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact hthird
      let d := lemma57EnlargedGoodBONG q M generator
        b.toBONG.head_isAnisotropic s (a.order 0) hs tail horder
        headLeThird
      refine ⟨d.orderSequence, ?_⟩
      change NormGeneratorComparisonData a
        (lemma57OriginalCandidate q M generator
          b.toBONG.head_isAnisotropic tail) d.orderSequence
      exact a.normGeneratorComparisonData_lemma57 generator
        b.toBONG.head_isAnisotropic s (a.order 0) hs tail horder
        headLeThird

end BONG.GoodBONG

end Bong
