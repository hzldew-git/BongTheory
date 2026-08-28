/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenAssembly
import Bong.Bong.Beli2019Lemma79EvenTypeICentralSource
import Bong.Bong.Beli2019Lemma79EvenTypeITargetCentral

/-!
# Beli (2019), Lemma 7.9(ii), case 3: central type-I assembly

The source and target capped self-prefix bounds are now both available in the
strict central interval.  The even-coordinate assembly lemma converts them
into the diagonal source-target defect required by condition 2.1(ii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 5000000 in
/-- Lemma 7.9(ii), case 3, at strict central even type-I coordinates whose
two-step successor remains inside the canonical central interval. -/
theorem beli2019Lemma79_ii_typeI_even_central
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hiLeft : C.leftSwitch < i.val)
    (hfarRight : i.val + 2 ≤ C.rightSwitch) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hiTwo : 2 ≤ i.val := by omega
  have hsource := beli2019Lemma79_typeI_central_even_sourceCapped
    a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
      horderBC i hi hiEven hiLeft hfarRight
  have hpreviousEven : Even (i.val - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hpreviousLeft : C.leftSwitch ≤ i.val - 2 := by
    rcases hiEven with ⟨d, hd⟩
    rcases C.left_even with ⟨e, he⟩
    omega
  have hpreviousRaw := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst (i.val - 2) hpreviousLeft (by omega) hpreviousEven
  have hcurrentRaw := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst i.val hiLeft.le (by omega) hiEven
  have htwo : b.order ⟨i.val - 2, by omega⟩ =
      b.order ⟨i.val, i.lt_large⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hpreviousRaw.symm.trans hcurrentRaw
  have hsourceGap := b.orderGap_previous_le_twoE_of_twoStep
    i hiTwo htwo
  have hcross :=
    crossGap_le_twoE_of_representationOrder_of_sourceGap_le_twoE
      b c horderBC i hsourceGap
  have htarget := beli2019Lemma79_typeI_central_even_target
    a b c D C hfirst hnorm i hiTwo hiEven hiLeft.le (by omega) hcross
  exact lemma79_ii_of_even_selfCapped_bounds b c i hsource htarget

end BONG.GoodBONG

end Bong
