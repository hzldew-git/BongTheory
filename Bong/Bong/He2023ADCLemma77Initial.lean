/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma710
import Bong.Bong.HeHu2022SectionFive

/-!
# He (2025), Lemma 7.7(i)--(ii)

The order and defect parts of Lemma 7.7 are the codimension-two boundary
specialization of the calculations in He--Hu, Lemma 5.6.  The latter proof
uses only the weaker rank bound exposed by its formal interface.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V W : Type u} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- He (2025), Lemma 7.7(i): condition (i) of Theorem 3.6 holds for every
integral maximal test lattice of rank `n`.  Maximality is not needed by the
calculation, so the formal conclusion is valid for every integral target. -/
theorem heADC2025Lemma77i (k : Nat)
    (a : GoodBONG q L (((2 * k + 2) + 1) + 2))
    (b : GoodBONG r M ((2 * k + 1) + 2))
    (hInitial : a.HeHuI1E (2 * k + 2) (by omega))
    (hM : Lattice.IsIntegral r M) :
    a.RepresentationOrderCondition b (by omega) := by
  exact a.heHu2022Lemma56i (m := 2 * k + 2) (n := 2 * k + 1) b
    (by omega) ⟨k + 1, by omega⟩ (by omega) hInitial hM

/-- He (2025), Lemma 7.7(ii): under the two alternatives in Lemma 7.5(ii),
condition (ii) of Theorem 3.6 holds for every integral target. -/
theorem heADC2025Lemma77ii (k : Nat)
    (a : GoodBONG q L (((2 * k + 2) + 1) + 2))
    (b : GoodBONG r M ((2 * k + 1) + 2))
    (hA : Lattice.IsIntegral q L)
    (hInitial : a.HeHuI1E (2 * k + 2) (by omega))
    (hBoundary : a.HeHuI2E (2 * k + 2) (by omega))
    (hM : Lattice.IsIntegral r M) :
    a.RepresentationDefectCondition b := by
  exact a.heHu2022Lemma56ii (m := 2 * k + 2) (n := 2 * k + 1) b
    (by omega) ⟨k + 1, by omega⟩ (by omega) hA hM
      hInitial hBoundary

end BONG.GoodBONG

end Bong
