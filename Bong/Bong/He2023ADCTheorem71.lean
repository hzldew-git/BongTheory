/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCQuaternaryBoundaryClassification
import Bong.Bong.He2023ADCExceptionalQuaternaryNonThree
import Bong.Lattice.NADCMonotonicity

/-!
# He (2025), Theorem 7.1

The published proof omits the second-discriminant binary boundary exposed by
the formalization of Lemma 6.8(iv). The statement remains true: at `n=3`,
the corrected binary classification has two nonmaximal classes, and both have
been proved not to be 3-ADC. For odd `n>=5`, the corrected stable Theorem 6.2
applies directly.
-/

namespace Bong

open Dyadic Module

universe u

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]

/-- He (2025), Theorem 7.1, with the omitted `n=3` branch repaired. -/
theorem heADC2025Theorem71
    (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat)
    (hn : 3 ≤ n) (hodd : Odd n) (hrank : finrank K V = n + 1) :
    IsNADC.{u, u, u} q L n ↔ IsOMaximal q L := by
  constructor
  · intro hADC
    have hADCAsSucc : IsNADC.{u, u, u} q L ((n - 1) + 1) := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hADC
    have hPrevious : IsNADC.{u, u, u} q L (n - 1) :=
      hADCAsSucc.of_succ (by rw [hrank]; omega)
    by_cases hnThree : n = 3
    · subst n
      rcases heADC2025Theorem62_binary_corrected
          (by simpa using hPrevious) (by simpa using hrank) with
        hmaximal | hexceptional | hboundary
      · exact hmaximal
      · have hExceptionalADC := hADC.of_latticeIsometry
          (Classical.choice hexceptional)
        exact False.elim
          (BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_not_is3ADC
            hExceptionalADC)
      · have hBoundaryADC := hADC.of_latticeIsometry
          (Classical.choice hboundary)
        exact False.elim
          (BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_not_is3ADC
            hBoundaryADC)
    · obtain ⟨k, hk⟩ := hodd
      let p := k - 1
      have hp : 0 < p := by
        dsimp only [p]
        omega
      have hPreviousRank : n - 1 = 2 * p + 2 := by
        dsimp only [p]
        omega
      have hAmbientRank : finrank K V = 2 * p + 4 := by
        rw [hrank]
        dsimp only [p]
        omega
      exact (heADC2025Theorem62_of_four_le p hp hAmbientRank).mp
        (by simpa only [hPreviousRank] using hPrevious)
  · exact fun hmaximal ↦ hmaximal.isNADC n

end Lattice

end Bong
