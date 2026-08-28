/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveGapTwoAlpha
import Bong.Bong.Beli2019AlmostJordanWeakUnaryShiftEntries

/-!
# Beli (2019), Section 5: the proper unary exceptional interval

In cases 3--4 following Lemma 5.13 the selected unary component crosses the
unique common component at the intermediate scale.  This file treats the
effective-proper branch.  On the exceptional interval the source orders are
`r - 2, r - 1, ..., r - 1`, whereas the target orders are
`r - 1, ..., r - 1, r`.  Thus every comparison prefix has odd total order,
and the shifted primary defect is odd as well.  The resulting primary
coefficient is zero, which proves condition 2.1(ii) directly.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace BONG.GoodBONG

/-- If the comparison prefixes differ by one and the next source order is
the current target order, then the signed unequal-prefix product occurring
in the primary representation candidate has odd valuation. -/
theorem signedShiftedPrefix_order_odd_of_prefixSum_succ_of_next_eq_current
    {n : Nat} (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hsum : b.orderSequence.prefixSum i.val =
      a.orderSequence.prefixSum i.val + 1)
    (hnext : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩) :
    Odd (ordUnit K ((-1 : Kˣ) * a.prefixProduct (i.val + 1) *
      b.prefixProduct (i.val - 1))) := by
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have hnegOne : ordUnit K (-1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (-1 : Kˣ) (-1)
    have hmul : (-1 : Kˣ) * (-1) = 1 := by norm_num
    rw [hmul, hone] at h
    omega
  have haStep := a.orderSequence.prefixSum_succ i.val
  have hbStep := b.orderSequence.prefixSum_succ (i.val - 1)
  have hindex : i.val - 1 + 1 = i.val := by
    have := i.pos
    omega
  have haEntry : a.orderSequence.entryOrZero i.val =
      a.order ⟨i.val, i.lt_large⟩ := by
    rw [a.orderSequence.entryOrZero_of_lt i.lt_large]
    rfl
  have hbEntry : b.orderSequence.entryOrZero (i.val - 1) =
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ := by
    rw [b.orderSequence.entryOrZero_of_lt (by
      have := i.le_small
      omega)]
    rfl
  rw [hindex] at hbStep
  rw [ordUnit_mul, ordUnit_mul, hnegOne, zero_add,
    a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (i.val + 1) (Nat.succ_le_of_lt i.lt_large),
    b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (i.val - 1) ((Nat.sub_le i.val 1).trans i.lt_large.le)]
  refine ⟨a.orderSequence.prefixSum i.val, ?_⟩
  rw [haEntry] at haStep
  rw [hbEntry] at hbStep
  omega

end BONG.GoodBONG

namespace Lattice.Beli2019Lemma51Data

/-- On every nonempty initial part of the proper unary exceptional interval,
the target cumulative order is exactly one above the source cumulative
order. -/
theorem weakUnaryShift_proper_prefixSum_succ
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (heffective : D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
      ordUnit K (D.complementStrictWeak.scaleGenerator i₀))
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (j : Nat) (hjpos : 0 < j)
    (hjle : j ≤ finrank K (D.complementStrictWeak.component i₀).carrier) :
    let start := ∑ p ∈ Finset.Iio D.largeSelectedPosition,
      finrank K (D.largeAlmostJordan.component p).carrier
    b.orderSequence.prefixSum (start + j) =
      a.orderSequence.prefixSum (start + j) + 1 := by
  let start := ∑ p ∈ Finset.Iio D.largeSelectedPosition,
    finrank K (D.largeAlmostJordan.component p).carrier
  let c := finrank K (D.complementStrictWeak.component i₀).carrier
  have hcpos : 0 < c := D.complementStrictWeak.component_finrank_pos i₀
  have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
  have hstartPrefix : a.orderSequence.prefixSum start =
      b.orderSequence.prefixSum start := by
    exact D.weakUnaryShift_previousPrefixSum_eq_at_intervalStart
      hfin i₀ hi₀ a b
  have hselectedScale : ordUnit K D.input.block.enlargedScaleGenerator =
      ordUnit K D.input.block.scaleGenerator - 2 := by
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hOne | hTwo
    · exact hOne.2
    · omega
  have hmiddleScale :
      ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
        ordUnit K D.input.block.scaleGenerator - 1 := by
    omega
  change b.orderSequence.prefixSum (start + j) =
    a.orderSequence.prefixSum (start + j) + 1
  induction j with
  | zero => omega
  | succ j ih =>
      by_cases hjzero : j = 0
      · subst j
        have hsourceBound : start < n := by
          dsimp only [start, c] at hbound ⊢
          omega
        have htargetBound : start < n := hsourceBound
        have hsourceEntry : a.orderSequence.entryOrZero start =
            ordUnit K D.input.block.scaleGenerator - 2 := by
          rw [a.orderSequence.entryOrZero_of_lt hsourceBound]
          exact D.weakUnaryShift_largeSelected_entry hfin a
        have htargetEntry : b.orderSequence.entryOrZero start =
            ordUnit K D.input.block.scaleGenerator - 1 := by
          rw [b.orderSequence.entryOrZero_of_lt htargetBound]
          have hentry := D.weakUnaryShift_smallCommon_entry
            hfin i₀ hi₀ a b 0 (by simpa only [c] using hcpos)
          rw [heffective, JordanProfileOrder.localOrder_of_proper] at hentry
          simpa only [start, Nat.add_zero] using hentry.trans hmiddleScale
        rw [show start + (0 + 1) = start + 1 by omega,
          b.orderSequence.prefixSum_succ,
          a.orderSequence.prefixSum_succ,
          hstartPrefix, hsourceEntry, htargetEntry]
        omega
      · have hjpos' : 0 < j := Nat.pos_of_ne_zero hjzero
        have hjle' : j ≤ c := by
          dsimp only [c] at hjle ⊢
          omega
        have ih' := ih hjpos' hjle'
        have hjlt : j < c := by
          dsimp only [c] at hjle ⊢
          omega
        have hglobalBound : start + j < n := by
          dsimp only [start, c] at hbound ⊢
          omega
        have hsourceEntry : a.orderSequence.entryOrZero (start + j) =
            ordUnit K D.input.block.scaleGenerator - 1 := by
          rw [a.orderSequence.entryOrZero_of_lt hglobalBound]
          have hentry := D.weakUnaryShift_largeCommon_entry
            hfin i₀ hi₀ a (j - 1) (by
              dsimp only [c] at hjlt ⊢
              omega)
          rw [heffective, JordanProfileOrder.localOrder_of_proper] at hentry
          have hindex : start + j = start + ((j - 1) + 1) := by omega
          exact (weakOrderSequence_entry_eq_of_index_eq
            a.orderSequence (start + j) (start + ((j - 1) + 1))
              hglobalBound (by omega) hindex).trans
                (hentry.trans hmiddleScale)
        have htargetEntry : b.orderSequence.entryOrZero (start + j) =
            ordUnit K D.input.block.scaleGenerator - 1 := by
          rw [b.orderSequence.entryOrZero_of_lt hglobalBound]
          have hentry := D.weakUnaryShift_smallCommon_entry
            hfin i₀ hi₀ a b j (by simpa only [c] using hjlt)
          rw [heffective, JordanProfileOrder.localOrder_of_proper] at hentry
          exact hentry.trans hmiddleScale
        rw [show start + (j + 1) = (start + j) + 1 by omega,
          b.orderSequence.prefixSum_succ,
          a.orderSequence.prefixSum_succ,
          hsourceEntry, htargetEntry, ih']
        abel

/-- In the proper unary exceptional interval the next source order is the
current target order, both equal to the intermediate scale. -/
theorem weakUnaryShift_proper_nextOrder_eq_currentTarget
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (heffective : D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
      ordUnit K (D.complementStrictWeak.scaleGenerator i₀))
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hleft : D.largeSelectedStart < i.val)
    (hright : i.val ≤ D.largeSelectedStart +
      finrank K (D.complementStrictWeak.component i₀).carrier) :
    a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ := by
  let start := ∑ p ∈ Finset.Iio D.largeSelectedPosition,
    finrank K (D.largeAlmostJordan.component p).carrier
  let c := finrank K (D.complementStrictWeak.component i₀).carrier
  let j := i.val - start
  have hstart : start = D.largeSelectedStart := rfl
  have hjpos : 0 < j := by
    dsimp only [j]
    rw [hstart]
    omega
  have hjle : j ≤ c := by
    dsimp only [j, c]
    rw [← hstart] at hright
    omega
  have hjpredLt : j - 1 < c := by omega
  have hmiddleScale :
      ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
        ordUnit K D.input.block.scaleGenerator - 1 := by
    have hselectedScale : ordUnit K D.input.block.enlargedScaleGenerator =
        ordUnit K D.input.block.scaleGenerator - 2 := by
      rcases D.input.block.componentRank_and_enlargedScaleOrder with
        hOne | hTwo
      · exact hOne.2
      · omega
    omega
  have hsourceEntry := D.weakUnaryShift_largeCommon_entry
    hfin i₀ hi₀ a (j - 1) (by simpa only [c] using hjpredLt)
  have htargetEntry := D.weakUnaryShift_smallCommon_entry
    hfin i₀ hi₀ a b (j - 1) (by simpa only [c] using hjpredLt)
  rw [heffective, JordanProfileOrder.localOrder_of_proper] at hsourceEntry htargetEntry
  have hsourceIndex : i.val = start + ((j - 1) + 1) := by
    dsimp only [j]
    rw [← hstart] at hleft
    omega
  have htargetIndex : i.val - 1 = start + (j - 1) := by
    dsimp only [j]
    rw [← hstart] at hleft
    omega
  have hsourceBound : start + ((j - 1) + 1) < n + 2 := by
    rw [← hsourceIndex]
    exact i.lt_large
  have htargetBound : start + (j - 1) < n + 2 := by
    rw [← htargetIndex]
    have := i.le_small
    omega
  have htargetOriginalBound : i.val - 1 < n + 2 := by
    have := i.le_small
    omega
  calc
    a.order ⟨i.val, i.lt_large⟩ =
        a.orderSequence.entry (start + ((j - 1) + 1)) hsourceBound := by
      exact weakOrderSequence_entry_eq_of_index_eq a.orderSequence
        i.val (start + ((j - 1) + 1)) i.lt_large hsourceBound hsourceIndex
    _ = ordUnit K D.input.block.scaleGenerator - 1 :=
      hsourceEntry.trans hmiddleScale
    _ = b.orderSequence.entry (start + (j - 1)) htargetBound :=
      (htargetEntry.trans hmiddleScale).symm
    _ = b.order ⟨i.val - 1, by have := i.le_small; omega⟩ := by
      exact weakOrderSequence_entry_eq_of_index_eq b.orderSequence
        (start + (j - 1)) (i.val - 1) htargetBound htargetOriginalBound
          htargetIndex.symm

/-- Case 3 after Lemma 5.13: every boundary in the proper unary exceptional
interval has an odd-prefix certificate with representation alpha at most
zero. -/
theorem weakUnaryShift_proper_defectCertificate
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (heffective : D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
      ordUnit K (D.complementStrictWeak.scaleGenerator i₀))
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.DefectReducedRange i)
    (hout : ¬D.Lemma517Range i) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  let c := finrank K (D.complementStrictWeak.component i₀).carrier
  have hstartEnd :=
    D.weakUnaryShift_smallSelectedStart_eq_intervalEnd hfin i₀ hi₀
  change D.smallSelectedStart = D.largeSelectedStart + c at hstartEnd
  have hleft : D.largeSelectedStart < i.val := by
    change ¬ i.val ≤ D.largeSelectedStart +
      finrank K
        (D.largeAlmostJordan.component D.largeSelectedPosition).carrier - 1
      at hout
    rw [D.largeAlmostJordan_finrank_selected, hfin] at hout
    omega
  have hright : i.val ≤ D.largeSelectedStart + c := by
    change i.val ≤ D.smallSelectedStart +
      finrank K
        (D.smallAlmostJordan.component D.smallSelectedPosition).carrier - 1
      at hi
    rw [D.smallAlmostJordan_finrank_selected, hfin, hstartEnd] at hi
    omega
  let j := i.val - D.largeSelectedStart
  have hjpos : 0 < j := by dsimp only [j]; omega
  have hjle : j ≤ c := by dsimp only [j]; omega
  have hsum : b.orderSequence.prefixSum i.val =
      a.orderSequence.prefixSum i.val + 1 := by
    have h := D.weakUnaryShift_proper_prefixSum_succ
      hfin i₀ hi₀ heffective a b j hjpos (by simpa only [c] using hjle)
    change b.orderSequence.prefixSum (D.largeSelectedStart + j) =
      a.orderSequence.prefixSum (D.largeSelectedStart + j) + 1 at h
    rw [show D.largeSelectedStart + j = i.val by
      dsimp only [j]
      exact Nat.add_sub_of_le hleft.le] at h
    exact h
  have hnext := D.weakUnaryShift_proper_nextOrder_eq_currentTarget
    hfin i₀ hi₀ heffective a b i hleft hright
  have hodd :=
    a.signedShiftedPrefix_order_odd_of_prefixSum_succ_of_next_eq_current
      b i hsum hnext
  have hzero := a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed b
    (-1) (i.val + 1) (i.val - 1) hodd
  have hbound :=
    a.representationAlphaValue_le_primaryCoefficient_of_defect_zero b i hzero
  apply BONG.GoodBONG.Beli2019SectionFiveDefectCertificate.odd hsum
  rw [hnext] at hbound
  rw [← a.coe_representationAlphaValue b i]
  exact_mod_cast (by simpa only [sub_self, Int.cast_zero] using hbound)

end Lattice.Beli2019Lemma51Data

end Bong
