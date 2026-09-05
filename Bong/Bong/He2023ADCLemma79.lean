/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.NADCMonotonicity

/-!
# He (2025), Lemma 7.9

An `n`-ADC lattice of rank `n+2` is `(n-1)`-universal. The proof first
descends ADC rank by one and then uses the already proved stable-rank ambient
universality theorem; this is equivalent to the determinant-extension argument
printed in the paper.
-/

namespace Bong

open Dyadic Module

universe u

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- He (2025), Lemma 7.9. -/
theorem heADC2025Lemma79 (n : Nat) (hn : 3 ≤ n) (_hodd : Odd n)
    (hrank : finrank K V = n + 2) (hADC : IsNADC.{u, u, u} q L n) :
    IsNUniversal.{u, u, u} q L (n - 1) := by
  letI : Module.Finite K V := L.moduleFinite
  have hADCAsSucc : IsNADC.{u, u, u} q L ((n - 1) + 1) := by
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hADC
  have hPrevious : IsNADC.{u, u, u} q L (n - 1) :=
    hADCAsSucc.of_succ (by rw [hrank]; omega)
  exact (isNADC_iff_isNUniversal_of_rank_add_three_le
    q L (n - 1) (by rw [hrank]; omega)).mp hPrevious

end Lattice

end Bong
