/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Good

/-!
# Prepending a head to a good BONG

For a nonempty good tail, the only new two-step inequality after prepending
a head is the comparison between the new first and third orders.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- A good nonempty tail extends to a good BONG exactly when the possible
new head-to-third comparison is supplied. -/
theorem IsGood.cons_of_tail_of_head_le_third {x : V}
    {generator : Lattice.IsNormGenerator q L x}
    {anisotropic : q.IsAnisotropic x}
    {tail : BONG (q.vectorOrthogonal x)
      (q.orthogonalSpace x anisotropic)
      (L.projectedLattice q x anisotropic) (n + 1)}
    (tailGood : tail.IsGood)
    (headLeThird : ∀ hi : 2 < n + 2,
      (BONG.cons x generator anisotropic tail).order 0 ≤
        (BONG.cons x generator anisotropic tail).order ⟨2, hi⟩) :
    (BONG.cons x generator anisotropic tail).IsGood := by
  let b := BONG.cons x generator anisotropic tail
  change b.IsGood
  intro i hi
  cases i using Fin.cases with
  | zero =>
      exact headLeThird hi
  | succ j =>
      have hj : j.val + 2 < n + 1 := by
        simp only [Fin.val_succ] at hi
        omega
      have htail := tailGood j hj
      let k : Fin (n + 1) := ⟨j.val + 2, hj⟩
      have hk : k.succ =
          (⟨j.succ.val + 2, hi⟩ : Fin (n + 2)) := by
        apply Fin.ext
        simp [k]
      calc
        b.order j.succ = tail.order j := (b.order_tail j).symm
        _ ≤ tail.order k := htail
        _ = b.order k.succ := b.order_tail k
        _ = b.order ⟨j.succ.val + 2, hi⟩ := congrArg b.order hk

end BONG

end Bong
