/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveDual
import Bong.Bong.Beli2019Lemma513CollisionSelected

/-!
# Beli (2019), Section 5: direct-range defect certificates

This file assembles the concrete approximation statements of Lemma 5.13
with the alpha estimates following Lemma 5.17.  The first result isolates
the equal-order branch; later results split the remaining direct-range
Jordan cases without placing their conclusions in a law interface.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

namespace Beli2019Lemma513LocalData

/-- On the literal Lemma 5.17 range, equality of the current source and
target orders gives a complete common-approximation certificate for
condition 2.1(ii).  Lemma 5.13 supplies the common scalar and the corrected
two-step form of Lemma 5.17 supplies the common alpha bound. -/
theorem equalCertificate
    [BONGStructuralLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (hNM : N ≤ M)
    {InReducedRange : RepresentationIndex (n + 1) (n + 1) → Prop}
    (localData : Beli2019Lemma513LocalData a b InReducedRange)
    (lemma517 : Beli2019Lemma517Data a b InReducedRange)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : InReducedRange i)
    (hcurrent : a.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val - 1)) :
    Beli2019SectionFiveDefectCertificate a b i := by
  have hnotSucc : b.orderSequence.entryOrZero (i.val - 1) ≠
      a.orderSequence.entryOrZero (i.val - 1) + 1 := by
    rw [← hcurrent]
    omega
  obtain ⟨X, hsource, htarget⟩ :=
    localData.commonApproximation i hi hnotSucc
  exact Beli2019SectionFiveDefectCertificate.common X hsource htarget
    (lemma517.commonBound_of_twoStep_split a b hNM i hi hcurrent)

end Beli2019Lemma513LocalData

end BONG.GoodBONG

end Bong
