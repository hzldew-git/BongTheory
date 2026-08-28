/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma27

/-!
# Beli (2019), Lemma 7.9(ii): the current-prefix secondary bound

Lemma 2.7(ii) replaces the target prefix ending two places earlier in the
secondary candidate by the current target prefix.  This file records the
resulting candidate as a direct upper bound for the finite representation
alpha used repeatedly in the later case analysis.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The replacement-current secondary candidate bounds the representation
alpha whenever its crossing order hypothesis holds. -/
theorem representationAlphaValue_le_secondaryCurrent
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < n + 1)
    (hcross : b.order ⟨i.val - 1, by
      have := i.le_small
      omega⟩ ≤ a.order ⟨i.val + 1, hi.2⟩) :
    (a.representationAlphaValue b i : WithTop ℚ) ≤
      a.representationSecondaryCurrentDefect b i hi := by
  rw [a.coe_representationAlphaValue b i]
  calc
    a.representationAlpha b i ≤ a.representationAlphaPrime b i :=
      a.representationAlpha_le_prime b i
    _ = min (a.representationPrimaryDefect b i)
        (a.representationSecondaryCurrentDefect b i hi) :=
      a.representationAlphaPrime_eq_min_primary_current b i hi hcross
    _ ≤ a.representationSecondaryCurrentDefect b i hi := min_le_right _ _

end BONG.GoodBONG

end Bong
