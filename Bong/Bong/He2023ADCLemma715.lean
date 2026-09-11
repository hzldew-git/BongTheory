/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma714
import Bong.Bong.He2023ADCCorankOneVolume
import Bong.Bong.Beli2009ClassificationProof

/-!
# He (2025), Lemma 7.15

Two odd-corank-two ADC lattices are classified by their ambient quadratic
space and penultimate BONG order.  The proof verifies Beli's four integral
classification conditions rather than assuming a uniqueness principle.
-/

namespace Bong

open Dyadic Module AlternatingEndpointTower

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V W : Type u} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

private theorem even_ordUnit_of_square_for_lemma715 (x : Kˣ)
    (hx : IsSquare x) : Even (ordUnit K x) := by
  rcases hx with ⟨s, rfl⟩
  refine ⟨ordUnit K s, ?_⟩
  rw [ordUnit_mul]

/-- Isometric ambient spaces give the same parity for the two full BONG
determinants. -/
theorem heADC2025Lemma715_fullComparisonEven (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 5))
    (ambient : q.IsIsometric r) :
    Even (ordUnit K (a.prefixProduct (2 * k + 5)) +
      ordUnit K (b.prefixProduct (2 * k + 5))) := by
  have hvalues :=
    a.toBONG.diagonalRepresents_values_of_isometric b.toBONG ambient
  have hrep : DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients a.valueUnit) := by
    convert hvalues using 1 <;> funext i <;>
      exact GoodBONG.coe_valueUnit _ _
  have hsquare :=
    DiagonalIsometryInvariantLaws.determinant_square b.valueUnit a.valueUnit hrep
  have haFull : a.prefixProduct (2 * k + 5) =
      diagonalUnitDeterminant a.valueUnit := by
    classical
    unfold GoodBONG.prefixProduct BONG.prefixProduct diagonalUnitDeterminant
    rw [Finset.filter_eq_self.mpr]
    · rfl
    · intro i _
      exact i.isLt
  have hbFull : b.prefixProduct (2 * k + 5) =
      diagonalUnitDeterminant b.valueUnit := by
    classical
    unfold GoodBONG.prefixProduct BONG.prefixProduct diagonalUnitDeterminant
    rw [Finset.filter_eq_self.mpr]
    · rfl
    · intro i _
      exact i.isLt
  have hproduct : IsSquare
      (a.prefixProduct (2 * k + 5) * b.prefixProduct (2 * k + 5)) := by
    rw [haFull, hbFull]
    simpa only [mul_comm] using hsquare
  have heven := even_ordUnit_of_square_for_lemma715 _ hproduct
  rwa [ordUnit_mul] at heven

/-- The ambient isometry and penultimate-order equality force equality of
the complete order sequences. -/
theorem heADC2025Lemma715_sameOrders (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3))
    (hADC' : Lattice.IsNADC.{u, u, u} r M (2 * k + 3))
    (ambient : q.IsIsometric r)
    (hpenultimate : a.order ⟨2 * k + 3, by omega⟩ =
      b.order ⟨2 * k + 3, by omega⟩) :
    a.SameOrders b := by
  have C := a.heADC2025Theorem74Necessity k hADC
  have D := b.heADC2025Theorem74Necessity k hADC'
  have hfullEven := a.heADC2025Lemma715_fullComparisonEven k b ambient
  rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum (2 * k + 5) le_rfl,
    b.ordUnit_prefixProduct_eq_orderSequence_prefixSum (2 * k + 5) le_rfl,
    a.orderSequence.prefixSum_succ (2 * k + 4),
    b.orderSequence.prefixSum_succ (2 * k + 4),
    a.orderSequence_entryOrZero_eq_order ⟨2 * k + 4, by omega⟩,
    b.orderSequence_entryOrZero_eq_order ⟨2 * k + 4, by omega⟩] at hfullEven
  have hprefixA := a.heADC2025Lemma714_initialPrefixEven k C
  have hprefixB := b.heADC2025Lemma714_initialPrefixEven k D
  rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum (2 * k + 4) (by omega)]
    at hprefixA
  rw [b.ordUnit_prefixProduct_eq_orderSequence_prefixSum (2 * k + 4) (by omega)]
    at hprefixB
  have hlastSum : Even (a.order ⟨2 * k + 4, by omega⟩ +
      b.order ⟨2 * k + 4, by omega⟩) := by
    rcases hfullEven.sub (hprefixA.add hprefixB) with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    omega
  have hlast : a.order ⟨2 * k + 4, by omega⟩ =
      b.order ⟨2 * k + 4, by omega⟩ := by
    rcases C.last with ha | ha <;> rcases D.last with hb | hb
    · exact ha.trans hb.symm
    · rw [ha, hb] at hlastSum
      norm_num at hlastSum
    · rw [ha, hb] at hlastSum
      norm_num at hlastSum
    · exact ha.trans hb.symm
  intro i
  by_cases hinitial : i.val < 2 * k + 3
  · rcases Nat.even_or_odd i.val with heven | hodd
    · have ha := C.initial.oddOrder ⟨i.val, hinitial⟩ heven.add_one
      have hb := D.initial.oddOrder ⟨i.val, hinitial⟩ heven.add_one
      simpa only using ha.trans hb.symm
    · have hbound : i.val < 2 * k + 2 := by
        rcases hodd with ⟨j, hj⟩
        omega
      have ha := C.initial.evenOrder ⟨i.val, hbound⟩ hodd.add_one
      have hb := D.initial.evenOrder ⟨i.val, hbound⟩ hodd.add_one
      simpa only using ha.trans hb.symm
  · by_cases hpen : i.val = 2 * k + 3
    · have hi : i = (⟨2 * k + 3, by omega⟩ : Fin (2 * k + 5)) := Fin.ext hpen
      simpa only [hi] using hpenultimate
    · have hlastIndex : i =
          (⟨2 * k + 4, by omega⟩ : Fin (2 * k + 5)) := by
        have hiLower : 2 * k + 3 ≤ i.val := Nat.le_of_not_gt hinitial
        have hiUpper : i.val < 2 * k + 5 := i.isLt
        have hiValue : i.val = 2 * k + 4 := by omega
        exact Fin.ext hiValue
      simpa only [hlastIndex] using hlast

/-- Formula (7.5) at the odd paper indices preceding the ADC boundary. -/
theorem heADC2025Lemma715_earlyOddAlpha (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (C : a.HeADCTheorem74Conditions k)
    (i : Fin (2 * k + 4)) (hi : i.val < 2 * k + 2)
    (heven : Even i.val) :
    a.alphaValue i = 0 := by
  apply (a.heADC2025Proposition34 i).alphaZero.mpr
  have hcurrent : a.order i.castSucc = 0 := by
    have h := C.initial.oddOrder ⟨i.val, by omega⟩ heven.add_one
    rw [show i.castSucc = (⟨i.val, by omega⟩ : Fin (2 * k + 5)) by
      apply Fin.ext
      rfl]
    exact h
  rcases heven with ⟨z, hz⟩
  have hnext : a.order i.succ =
      -(2 * (ramificationIndex K : Int)) := by
    have h := C.initial.evenOrder
      ⟨i.val + 1, by omega⟩
        (show Even (i.val + 1 + 1) by exact ⟨z + 1, by omega⟩)
    rw [show i.succ = (⟨i.val + 1, by omega⟩ : Fin (2 * k + 5)) by
      apply Fin.ext
      rfl]
    exact h
  unfold orderGap
  rw [hcurrent, hnext]
  simp

/-- Formula (7.5) at the even paper indices preceding the ADC boundary. -/
theorem heADC2025Lemma715_earlyEvenAlpha (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (C : a.HeADCTheorem74Conditions k)
    (i : Fin (2 * k + 4)) (hi : i.val < 2 * k + 2)
    (hodd : Odd i.val) :
    a.alphaValue i = 2 * (ramificationIndex K : ℚ) := by
  apply ((a.heADC2025Proposition33 i).compareTwoE.2.1).mp
  have hcurrent : a.order i.castSucc =
      -(2 * (ramificationIndex K : Int)) := by
    have h := C.initial.evenOrder ⟨i.val, hi⟩ hodd.add_one
    rw [show i.castSucc = (⟨i.val, by omega⟩ : Fin (2 * k + 5)) by
      apply Fin.ext
      rfl]
    exact h
  have hnext : a.order i.succ = 0 := by
    have h := C.initial.oddOrder
      ⟨i.val + 1, by omega⟩
        (show Odd (i.val + 1 + 1) by
          simpa only [Nat.add_assoc] using hodd.add_one.add_one)
    rw [show i.succ = (⟨i.val + 1, by omega⟩ : Fin (2 * k + 5)) by
      apply Fin.ext
      rfl]
    exact h
  unfold orderGap
  rw [hcurrent, hnext]
  ring

/-- Away from the maximal endpoint, Theorem 7.4(c) forces
`alpha_n = 1`. -/
theorem heADC2025Lemma715_boundaryAlpha (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (C : a.HeADCTheorem74Conditions k)
    (hpenultimate : a.order ⟨2 * k + 3, by omega⟩ ≠
      -(2 * (ramificationIndex K : Int))) :
    a.alphaValue ⟨2 * k + 2, by omega⟩ = 1 := by
  rcases C.alpha with hzero | hone
  · have hgap :=
      (a.heADC2025Proposition34 ⟨2 * k + 2, by omega⟩).alphaZero.mp hzero
    have hcurrent := C.initial.oddOrder ⟨2 * k + 2, by omega⟩
      (show Odd (2 * k + 3) by exact ⟨k + 1, by omega⟩)
    unfold orderGap at hgap
    simp only [Fin.castSucc_mk, Fin.succ_mk] at hgap
    rw [hcurrent, sub_zero] at hgap
    exact False.elim (hpenultimate hgap)
  · exact hone

/-- The terminal alpha is `1-R_(n+1)` in both possible last-order cases. -/
theorem heADC2025Lemma715_terminalAlpha (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (C : a.HeADCTheorem74Conditions k)
    (hpenultimate : a.order ⟨2 * k + 3, by omega⟩ ≠
      -(2 * (ramificationIndex K : Int))) :
    a.alphaValue ⟨2 * k + 3, by omega⟩ =
      1 - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) := by
  let boundary : Fin (2 * k + 4) := ⟨2 * k + 2, by omega⟩
  let terminal : Fin (2 * k + 4) := ⟨2 * k + 3, by omega⟩
  have hboundaryOrder : a.order ⟨2 * k + 2, by omega⟩ = 0 :=
    C.initial.oddOrder ⟨2 * k + 2, by omega⟩
      (show Odd (2 * k + 3) by exact ⟨k + 1, by omega⟩)
  have hboundaryAlpha := a.heADC2025Lemma715_boundaryAlpha k C hpenultimate
  rcases C.last with hlast | hlast
  · have hsum : a.adjacentOrderSum boundary =
        a.adjacentOrderSum terminal := by
      unfold adjacentOrderSum boundary terminal
      simp only [Fin.castSucc_mk, Fin.succ_mk]
      rw [hboundaryOrder, hlast]
      simp
    have hendpoint :=
      (a.beli2009Corollary23 boundary terminal (by
        change 2 * k + 2 ≤ 2 * k + 3
        omega) hsum).leftEndpoint_eq terminal (by
          change 2 * k + 2 ≤ 2 * k + 3
          omega) le_rfl
    unfold alphaLeftEndpoint boundary terminal at hendpoint
    simp only [Fin.castSucc_mk] at hendpoint
    rw [hboundaryOrder, hboundaryAlpha] at hendpoint
    push_cast at hendpoint
    linarith
  · have hgap : a.orderGap terminal =
        1 - a.order ⟨2 * k + 3, by omega⟩ := by
      unfold orderGap terminal
      simp only [Fin.castSucc_mk, Fin.succ_mk]
      rw [hlast]
    have hpenLower : 2 - 2 * (ramificationIndex K : Int) ≤
        a.order ⟨2 * k + 3, by omega⟩ := by
      rcases C.penultimate.1 with ⟨z, hz⟩
      have hlower := C.penultimate.2.1
      by_contra hnot
      have hle : a.order ⟨2 * k + 3, by omega⟩ ≤
          -(2 * (ramificationIndex K : Int)) := by omega
      have heq : a.order ⟨2 * k + 3, by omega⟩ =
          -(2 * (ramificationIndex K : Int)) := by omega
      exact hpenultimate heq
    have hgapLe : a.orderGap terminal ≤
        2 * (ramificationIndex K : Int) := by
      rw [hgap]
      omega
    have hgapOdd : Odd (a.orderGap terminal) := by
      rcases C.penultimate.1 with ⟨z, hz⟩
      rw [hgap, hz]
      exact ⟨-z, by ring⟩
    have halpha :=
      ((a.heADC2025Proposition33 terminal).lowerBound hgapLe).2.mpr
        (Or.inr hgapOdd)
    rw [hgap] at halpha
    exact_mod_cast halpha

/-- In the nonmaximal endpoint branch, the ADC conditions and equal orders
force all Beli alpha invariants to agree. -/
theorem heADC2025Lemma715_sameAlphas (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 5))
    (C : a.HeADCTheorem74Conditions k)
    (D : b.HeADCTheorem74Conditions k)
    (horders : a.SameOrders b)
    (hpenultimate : a.order ⟨2 * k + 3, by omega⟩ ≠
      -(2 * (ramificationIndex K : Int))) :
    a.SameAlphas b := by
  have hpenultimateB : b.order ⟨2 * k + 3, by omega⟩ ≠
      -(2 * (ramificationIndex K : Int)) := by
    rw [← horders ⟨2 * k + 3, by omega⟩]
    exact hpenultimate
  intro i
  by_cases hearly : i.val < 2 * k + 2
  · rcases Nat.even_or_odd i.val with heven | hodd
    · rw [a.heADC2025Lemma715_earlyOddAlpha k C i hearly heven,
        b.heADC2025Lemma715_earlyOddAlpha k D i hearly heven]
    · rw [a.heADC2025Lemma715_earlyEvenAlpha k C i hearly hodd,
        b.heADC2025Lemma715_earlyEvenAlpha k D i hearly hodd]
  · by_cases hboundary : i.val = 2 * k + 2
    · have hi : i = (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 4)) :=
        Fin.ext hboundary
      rw [hi, a.heADC2025Lemma715_boundaryAlpha k C hpenultimate,
        b.heADC2025Lemma715_boundaryAlpha k D hpenultimateB]
    · have hi : i = (⟨2 * k + 3, by omega⟩ : Fin (2 * k + 4)) := by
        have hiLower : 2 * k + 2 ≤ i.val := Nat.le_of_not_gt hearly
        have hiLower' : 2 * k + 3 ≤ i.val := by omega
        have hiUpper := i.isLt
        apply Fin.ext
        exact Nat.eq_of_lt_succ_of_not_lt hiUpper (by omega)
      rw [hi, a.heADC2025Lemma715_terminalAlpha k C hpenultimate,
        b.heADC2025Lemma715_terminalAlpha k D hpenultimateB,
        horders ⟨2 * k + 3, by omega⟩]

/-- Proposition 3.5(iii) supplies the signed even-prefix defect used in
condition (iii) of Beli's classification theorem. -/
theorem heADC2025Lemma715_alternatingPrefixDefect (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hIntegral : Lattice.IsIntegral q L)
    (i : Fin (2 * k + 4)) (hodd : Odd i.val)
    (horder : a.order i.castSucc =
      -(2 * (ramificationIndex K : Int))) :
    ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.alternatingPrefixDefect (i.val + 1) := by
  have H := (a.heADC2025Proposition35 hIntegral).clausesIIIIV
    i.castSucc (by
      change Odd i.val
      exact hodd) horder
  have htruncated := H.alternatingPrefixDefect
  have hraw := a.truncatedPrefixDefect_self_le_alternating (i.val + 1)
  have hiPositive : 0 < i.val := by
    rcases hodd with ⟨z, hz⟩
    omega
  have hlength : i.val - 1 + 2 = i.val + 1 := by omega
  dsimp only at htruncated
  simp only [Fin.val_castSucc] at htruncated
  rw [hlength] at htruncated
  exact htruncated.trans hraw

/-- The two Proposition 3.5 signed-prefix bounds combine by quadratic-defect
domination to give Beli's comparison-prefix bound. -/
theorem heADC2025Lemma715_earlyEvenPrefixBound (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 5))
    (hIntegral : Lattice.IsIntegral q L)
    (hIntegral' : Lattice.IsIntegral r M)
    (C : a.HeADCTheorem74Conditions k)
    (D : b.HeADCTheorem74Conditions k)
    (i : Fin (2 * k + 4)) (hi : i.val < 2 * k + 2)
    (hodd : Odd i.val) :
    ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) (a.comparisonPrefixProduct b i) := by
  have haOrder : a.order i.castSucc =
      -(2 * (ramificationIndex K : Int)) := by
    have h := C.initial.evenOrder ⟨i.val, hi⟩ hodd.add_one
    rw [show i.castSucc = (⟨i.val, by omega⟩ : Fin (2 * k + 5)) by
      apply Fin.ext
      rfl]
    exact h
  have hbOrder : b.order i.castSucc =
      -(2 * (ramificationIndex K : Int)) := by
    have h := D.initial.evenOrder ⟨i.val, hi⟩ hodd.add_one
    rw [show i.castSucc = (⟨i.val, by omega⟩ : Fin (2 * k + 5)) by
      apply Fin.ext
      rfl]
    exact h
  have ha := a.heADC2025Lemma715_alternatingPrefixDefect k hIntegral
    i hodd haOrder
  have hb := b.heADC2025Lemma715_alternatingPrefixDefect k hIntegral'
    i hodd hbOrder
  have hdom := defectOrder_mul_ge_min (K := K)
    (((-1 : Kˣ) ^ ((i.val + 1) / 2)) * a.prefixProduct (i.val + 1))
    (((-1 : Kˣ) ^ ((i.val + 1) / 2)) * b.prefixProduct (i.val + 1))
  have hlower : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      min (a.alternatingPrefixDefect (i.val + 1))
        (b.alternatingPrefixDefect (i.val + 1)) := le_min ha hb
  have hproduct :
      (((-1 : Kˣ) ^ ((i.val + 1) / 2)) * a.prefixProduct (i.val + 1)) *
          (((-1 : Kˣ) ^ ((i.val + 1) / 2)) * b.prefixProduct (i.val + 1)) =
        a.comparisonPrefixProduct b i := by
    unfold comparisonPrefixProduct
    have hsquare : ((-1 : Kˣ) ^ ((i.val + 1) / 2)) ^ 2 = 1 := by
      rw [← pow_mul]
      simp
    rw [show
      (((-1 : Kˣ) ^ ((i.val + 1) / 2)) * a.prefixProduct (i.val + 1)) *
          (((-1 : Kˣ) ^ ((i.val + 1) / 2)) * b.prefixProduct (i.val + 1)) =
        (((-1 : Kˣ) ^ ((i.val + 1) / 2)) ^ 2) *
          (a.prefixProduct (i.val + 1) * b.prefixProduct (i.val + 1)) by
            rw [pow_two]
            ac_rfl, hsquare, one_mul]
  unfold alternatingPrefixDefect at hlower
  rw [hproduct] at hdom
  exact hlower.trans hdom

/-- Proposition 3.4(v), with the brackets removed, gives the local defect
bound at the last nontrivial ADC boundary. -/
theorem heADC2025Lemma715_boundaryAdjacentDefect (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (C : a.HeADCTheorem74Conditions k)
    (hpenultimate : a.order ⟨2 * k + 3, by omega⟩ ≠
      -(2 * (ramificationIndex K : Int))) :
    ((1 - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) ≤
      a.adjacentDefect ⟨2 * k + 2, by omega⟩ := by
  let boundary : Fin (2 * k + 4) := ⟨2 * k + 2, by omega⟩
  have hboundaryOrder : a.order ⟨2 * k + 2, by omega⟩ = 0 :=
    C.initial.oddOrder ⟨2 * k + 2, by omega⟩
      (show Odd (2 * k + 3) by exact ⟨k + 1, by omega⟩)
  have hgap : a.orderGap boundary =
      a.order ⟨2 * k + 3, by omega⟩ := by
    unfold orderGap boundary
    simp only [Fin.castSucc_mk, Fin.succ_mk]
    rw [hboundaryOrder, sub_zero]
  have halpha := a.heADC2025Lemma715_boundaryAlpha k C hpenultimate
  have hcap :=
    ((a.heADC2025Proposition34 boundary).alphaOneDefect (by
      simpa only [boundary] using halpha)).1
  rw [hgap] at hcap
  have hcapRaw : a.heADCAdjacentCappedDefect boundary ≤
      a.adjacentDefect boundary := by
    change a.truncatedPrefixDefect a (-1) boundary.val (boundary.val + 2) ≤
      a.adjacentDefect boundary
    have hraw :=
      a.truncatedPrefixDefect_le_defect a (-1) boundary.val (boundary.val + 2)
    rw [a.defectOrder_prefixPair_eq_adjacentDefect boundary] at hraw
    exact hraw
  exact hcap.trans hcapRaw

/-- In the nonmaximal branch the full comparison-prefix condition (iii) of
Beli's theorem follows exactly from (7.5), Proposition 3.5(iii), and the
terminal domination argument printed in Lemma 7.15. -/
theorem heADC2025Lemma715_prefixDefectBounds (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 5))
    (hIntegral : Lattice.IsIntegral q L)
    (hIntegral' : Lattice.IsIntegral r M)
    (C : a.HeADCTheorem74Conditions k)
    (D : b.HeADCTheorem74Conditions k)
    (horders : a.SameOrders b)
    (hpenultimate : a.order ⟨2 * k + 3, by omega⟩ ≠
      -(2 * (ramificationIndex K : Int))) :
    a.PrefixDefectBounds b := by
  have hpenultimateB : b.order ⟨2 * k + 3, by omega⟩ ≠
      -(2 * (ramificationIndex K : Int)) := by
    rw [← horders ⟨2 * k + 3, by omega⟩]
    exact hpenultimate
  intro i
  by_cases hearly : i.val < 2 * k + 2
  · rcases Nat.even_or_odd i.val with heven | hodd
    · rw [a.heADC2025Lemma715_earlyOddAlpha k C i hearly heven]
      exact defectOrder_nonneg _
    · rw [a.heADC2025Lemma715_earlyEvenAlpha k C i hearly hodd]
      exact a.heADC2025Lemma715_earlyEvenPrefixBound k b hIntegral
        hIntegral' C D i hearly hodd
  · by_cases hboundary : i.val = 2 * k + 2
    · have hi : i = (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 4)) :=
        Fin.ext hboundary
      rw [hi, a.heADC2025Lemma715_boundaryAlpha k C hpenultimate]
      exact defectOrder_one_le_of_even _
        (a.comparisonPrefixProduct_order_even b horders _)
    · have hiLower : 2 * k + 2 ≤ i.val := Nat.le_of_not_gt hearly
      have hiLower' : 2 * k + 3 ≤ i.val := by omega
      have hiUpper := i.isLt
      have hi : i = (⟨2 * k + 3, by omega⟩ : Fin (2 * k + 4)) := by
        apply Fin.ext
        apply Nat.eq_of_le_of_lt_succ hiLower'
        simpa only [show 2 * k + 3 + 1 = 2 * k + 4 by omega] using hiUpper
      rw [hi, a.heADC2025Lemma715_terminalAlpha k C hpenultimate]
      have hbase := a.heADC2025Lemma715_earlyEvenPrefixBound k b
        hIntegral hIntegral' C D (⟨2 * k + 1, by omega⟩ : Fin (2 * k + 4))
          (by simp) (show Odd (2 * k + 1) by exact ⟨k, by omega⟩)
      change ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
        comparisonPrefixDefect a b (2 * k + 2) at hbase
      have haLocal := a.heADC2025Lemma715_boundaryAdjacentDefect k C hpenultimate
      have hbLocal := b.heADC2025Lemma715_boundaryAdjacentDefect k D hpenultimateB
      rw [← horders ⟨2 * k + 3, by omega⟩] at hbLocal
      have hpenLower : 2 - 2 * (ramificationIndex K : Int) ≤
          a.order ⟨2 * k + 3, by omega⟩ := by
        rcases C.penultimate.1 with ⟨z, hz⟩
        have hlower := C.penultimate.2.1
        by_contra hnot
        have heq : a.order ⟨2 * k + 3, by omega⟩ =
            -(2 * (ramificationIndex K : Int)) := by omega
        exact hpenultimate heq
      have hthreshold :
          ((1 - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) ≤
            ((2 * ramificationIndex K : ℚ) : WithTop ℚ) := by
        apply WithTop.coe_le_coe.mpr
        have hInt : 1 - a.order ⟨2 * k + 3, by omega⟩ ≤
            2 * (ramificationIndex K : Int) := by omega
        exact_mod_cast hInt
      have hdom := comparisonPrefixDefect_add_two a b (2 * k + 2) (by omega)
      have hcombined :
          ((1 - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) ≤
            comparisonPrefixDefect a b (2 * k + 4) :=
        (le_min (hthreshold.trans hbase) (le_min haLocal hbLocal)).trans hdom
      exact hcombined

/-- Proposition 3.5(v) puts the odd prefix occurring in condition (iv) into
the first-column hyperbolic-plus-unit normal form. -/
theorem heADC2025Lemma715_prefixOddFirst (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hIntegral : Lattice.IsIntegral q L)
    (hlast : a.order ⟨2 * k + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hnextEven : Even (a.order ⟨2 * k + 2, by omega⟩)) :
    ∃ ε : Kˣ, IsValuationUnit K (ε : K) ∧
      DiagonalRepresents (a.prefixValues (2 * k + 3) (by omega))
        (diagonalUnitCoefficients (heHuOddFirst k ε)) := by
  let j : Fin (2 * k + 5) := ⟨2 * k + 1, by omega⟩
  have hj : Odd j.val := ⟨k, by rfl⟩
  have hnext : j.val + 1 < 2 * k + 5 := by
    dsimp only [j]
    omega
  have heven : Even (a.order ⟨j.val + 1, hnext⟩) := by
    simpa only [j, show 2 * k + 1 + 1 = 2 * k + 2 by omega] using hnextEven
  obtain ⟨⟨pairs, hpairs, hbound, ε, s, hε, hclass, hnormal⟩⟩ :=
    a.heHu2022Proposition27v hIntegral j hj hlast hnext heven
  have hp : pairs = k + 1 := by
    dsimp only [j] at hpairs
    omega
  subst pairs
  obtain ⟨f⟩ := hnormal
  refine ⟨ε, hε, ?_⟩
  have hdiag : DiagonalRepresents
      (a.prefixValues (2 * (k + 1) + 1) hbound)
      (diagonalUnitCoefficients (Fin.snoc
        (standardHyperbolicEndpointTower (K := K) (k + 1)) ε)) := by
    refine ⟨f.toLinearEquiv.toLinearMap, f.toLinearEquiv.injective, ?_⟩
    intro x
    have hq : diagonalQuadratic (diagonalUnitCoefficients (Fin.snoc
        (standardHyperbolicEndpointTower (K := K) (k + 1)) ε))
        (f.toLinearEquiv x) =
          diagonalQuadratic (a.prefixValues (2 * (k + 1) + 1) hbound) x := by
      simpa only [prefixDiagonalSpace, hyperbolicEndpointTowerWithLineSpace,
        QuadraticSpace.finiteDiagonal_quadratic_apply,
        diagonalUnitCoefficients] using f.map_quadratic x
    exact hq
  rw [heHuLemma43_snoc_standard_eq_oddFirst (K := K) k ε] at hdiag
  let hdim : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  have hcast := heHuLemma43_diagonalRepresents_castLengths hdim hdim hdiag
  have hsource : (fun i : Fin (2 * k + 3) ↦
      a.prefixValues (2 * (k + 1) + 1) hbound (Fin.cast hdim.symm i)) =
      a.prefixValues (2 * k + 3) (by omega) := by
    funext i
    unfold prefixValues
    congr 1
  have htarget : (fun i : Fin (2 * k + 3) ↦
      diagonalUnitCoefficients (heHuOddFirst k ε) (Fin.cast hdim.symm i)) =
      diagonalUnitCoefficients (heHuOddFirst k ε) := by
    funext i
    unfold diagonalUnitCoefficients
    congr 1
  rw [hsource, htarget] at hcast
  exact hcast

/-- Proposition 3.5(iv) identifies the even prefix with one of the two
first-column endpoint classes. -/
theorem heADC2025Lemma715_prefixEvenFirst (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hfirst : a.order 0 = 0)
    (hlast : a.order ⟨2 * k + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (μ : Kˣ)
    (hμ : μ = 1 ∨ μ =
      (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (hclass : IsSquare (a.toBONG.signedEvenPrefixProduct (k + 1) * μ)) :
    DiagonalRepresents (diagonalUnitCoefficients (heHuEvenFirst k μ))
      (a.prefixValues (2 * k + 2) (by omega)) := by
  let source := a.prefixValueUnits (2 * (k + 1)) (by omega)
  have hend : a.order ⟨2 * (k + 1) - 1, by omega⟩ =
      0 - 2 * (ramificationIndex K : Int) := by
    simpa only [zero_sub, show 2 * (k + 1) - 1 = 2 * k + 1 by omega] using hlast
  have hs : AlternatingEndpointPairClasses source :=
    a.lemma79_endpointTower_pairClasses 0 (k + 1) (by omega) (by omega)
      hfirst hend
  have ho : AlternatingEndpointLeadingOrdersAt source (1 : Kˣ) := by
    intro t
    have hone : ordUnit K (1 : Kˣ) = 0 := by
      have H := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at H
      omega
    rw [hone]
    exact a.lemma79_endpointTower_leadingOrders 0 (k + 1) (by omega)
      (by omega) hfirst hend t
  have hdet : IsSquare (diagonalUnitDeterminant source *
      diagonalUnitDeterminant (heHuEvenFirst k μ)) := by
    rw [diagonalUnitDeterminant_heHuEvenFirst]
    simpa [source, diagonalUnitDeterminant_prefixValueUnits,
      BONG.signedEvenPrefixProduct, GoodBONG.prefixProduct, mul_comm,
      mul_left_comm, mul_assoc] using hclass
  have hrep := AlternatingEndpointTower.equalDeterminantRepresentation_proved
    source (heHuEvenFirst k μ) (1 : Kˣ) hs
      (heHuLemma45_evenFirst_pairClasses k μ hμ) ho
        (heHuLemma45_evenFirst_leadingOrders k μ) hdet
  have hrep' : DiagonalRepresents
      (diagonalUnitCoefficients (heHuEvenFirst k μ))
      (a.prefixValues (2 * (k + 1)) (by omega)) := by
    simpa only [source, diagonalUnitCoefficients_prefixValueUnits] using hrep
  let hdim : 2 * (k + 1) = 2 * k + 2 := by omega
  have hcast := heHuLemma43_diagonalRepresents_castLengths hdim hdim hrep'
  convert hcast using 1 <;> funext i
  · unfold diagonalUnitCoefficients
    congr 1
  · unfold prefixValues
    congr 1

/-- The unique trigger in condition (iv) is represented by the first-column
endpoint embedding of He, Lemma 4.4(ii). -/
theorem heADC2025Lemma715_boundaryRepresentation (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 5))
    (hIntegral : Lattice.IsIntegral q L)
    (hIntegral' : Lattice.IsIntegral r M)
    (C : a.HeADCTheorem74Conditions k)
    (D : b.HeADCTheorem74Conditions k) :
    DiagonalRepresents (b.prefixValues (2 * k + 2) (by omega))
      (a.prefixValues (2 * k + 3) (by omega)) := by
  have haLast := C.initial.evenOrder ⟨2 * k + 1, by omega⟩
    (show Even (2 * k + 2) by exact ⟨k + 1, by omega⟩)
  have hbLast := D.initial.evenOrder ⟨2 * k + 1, by omega⟩
    (show Even (2 * k + 2) by exact ⟨k + 1, by omega⟩)
  have haNext : a.order ⟨2 * k + 2, by omega⟩ = 0 :=
    C.initial.oddOrder ⟨2 * k + 2, by omega⟩
      (show Odd (2 * k + 3) by exact ⟨k + 1, by omega⟩)
  have hnextEven : Even (a.order ⟨2 * k + 2, by omega⟩) := by
    rw [haNext]
    exact Even.zero
  obtain ⟨ε, hε, haPrefix⟩ :=
    a.heADC2025Lemma715_prefixOddFirst k hIntegral haLast hnextEven
  have HB := (b.heADC2025Proposition35 hIntegral').clausesIIIIV
    (⟨2 * k + 1, by omega⟩ : Fin (2 * k + 5))
      (show Odd (2 * k + 1) by exact ⟨k, by omega⟩) hbLast
  obtain ⟨pairs, hpairs, hclass⟩ := HB.prefixEndpointClass
  have hpairs' : 2 * pairs = 2 * k + 2 := by
    simpa only [Fin.val_mk] using hpairs
  have hp : pairs = k + 1 := by omega
  subst pairs
  rcases hclass with hone | hdelta
  · have hbPrefix := b.heADC2025Lemma715_prefixEvenFirst k
      (D.initial.oddOrder 0 (show Odd 1 by exact ⟨0, rfl⟩)) hbLast
        (1 : Kˣ) (Or.inl rfl) (by simpa only [mul_one] using hone)
    exact hbPrefix.symm_of_sameRank.trans
      ((heHu2022Lemma314iRepresents k (1 : Kˣ) ε (Or.inl rfl) hε).trans
        haPrefix.symm_of_sameRank)
  · let Δ :=
      (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
    have hbPrefix := b.heADC2025Lemma715_prefixEvenFirst k
      (D.initial.oddOrder 0 (show Odd 1 by exact ⟨0, rfl⟩)) hbLast
        Δ (Or.inr rfl) (by simpa only [Δ] using hdelta)
    exact hbPrefix.symm_of_sameRank.trans
      ((heHu2022Lemma314iRepresents k Δ ε (Or.inr rfl) hε).trans
        haPrefix.symm_of_sameRank)

/-- Formula (7.5) leaves exactly one condition-(iv) trigger; the preceding
lemma supplies its required prefix representation. -/
theorem heADC2025Lemma715_internalRepresentations (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 5))
    (hIntegral : Lattice.IsIntegral q L)
    (hIntegral' : Lattice.IsIntegral r M)
    (C : a.HeADCTheorem74Conditions k)
    (D : b.HeADCTheorem74Conditions k)
    (hpenultimate : a.order ⟨2 * k + 3, by omega⟩ ≠
      -(2 * (ramificationIndex K : Int))) :
    a.InternalRepresentationConditions b := by
  intro i hi htrigger
  by_cases hcritical : i.val = 2 * k + 2
  · have hiEq : i = (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 4)) :=
      Fin.ext hcritical
    rw [hiEq]
    exact a.heADC2025Lemma715_boundaryRepresentation k b hIntegral hIntegral' C D
  · by_cases hbefore : i.val < 2 * k + 2
    · let previous : Fin (2 * k + 4) := ⟨i.val - 1, by omega⟩
      have hpreviousEarly : previous.val < 2 * k + 2 := by
        dsimp only [previous]
        omega
      rcases Nat.even_or_odd i.val with heven | hodd
      · have hpreviousOdd : Odd previous.val := by
          rcases heven with ⟨z, hz⟩
          refine ⟨z - 1, ?_⟩
          dsimp only [previous]
          omega
        have hpreviousAlpha := a.heADC2025Lemma715_earlyEvenAlpha k C
          previous hpreviousEarly hpreviousOdd
        have hcurrentAlpha := a.heADC2025Lemma715_earlyOddAlpha k C
          i hbefore heven
        change 2 * (ramificationIndex K : ℚ) <
          a.alphaValue previous + a.alphaValue i at htrigger
        rw [hpreviousAlpha, hcurrentAlpha] at htrigger
        norm_num at htrigger
      · have hpreviousEven : Even previous.val := by
          rcases hodd with ⟨z, hz⟩
          refine ⟨z, ?_⟩
          dsimp only [previous]
          omega
        have hpreviousAlpha := a.heADC2025Lemma715_earlyOddAlpha k C
          previous hpreviousEarly hpreviousEven
        have hcurrentAlpha := a.heADC2025Lemma715_earlyEvenAlpha k C
          i hbefore hodd
        change 2 * (ramificationIndex K : ℚ) <
          a.alphaValue previous + a.alphaValue i at htrigger
        rw [hpreviousAlpha, hcurrentAlpha] at htrigger
        norm_num at htrigger
    · have hiLower : 2 * k + 2 ≤ i.val := Nat.le_of_not_gt hbefore
      have hiLower' : 2 * k + 3 ≤ i.val := by omega
      have hiUpper := i.isLt
      have hiEq : i = (⟨2 * k + 3, by omega⟩ : Fin (2 * k + 4)) := by
        apply Fin.ext
        apply Nat.eq_of_le_of_lt_succ hiLower'
        simpa only [show 2 * k + 3 + 1 = 2 * k + 4 by omega] using hiUpper
      have hpenLower : 2 - 2 * (ramificationIndex K : Int) ≤
          a.order ⟨2 * k + 3, by omega⟩ := by
        rcases C.penultimate.1 with ⟨z, hz⟩
        have hlower := C.penultimate.2.1
        by_contra hnot
        have heq : a.order ⟨2 * k + 3, by omega⟩ =
            -(2 * (ramificationIndex K : Int)) := by omega
        exact hpenultimate heq
      have htrigger' : 2 * (ramificationIndex K : ℚ) <
          a.alphaValue ⟨2 * k + 2, by omega⟩ +
            a.alphaValue ⟨2 * k + 3, by omega⟩ := by
        simpa only [hiEq, Fin.val_mk,
          show 2 * k + 3 - 1 = 2 * k + 2 by omega] using htrigger
      rw [a.heADC2025Lemma715_boundaryAlpha k C hpenultimate,
        a.heADC2025Lemma715_terminalAlpha k C hpenultimate] at htrigger'
      have hpenLowerQ : (2 : ℚ) - 2 * (ramificationIndex K : ℚ) ≤
          (a.order ⟨2 * k + 3, by omega⟩ : ℚ) := by
        exact_mod_cast hpenLower
      linarith

/-- The four concrete Beli conditions complete the nonmaximal branch of
Lemma 7.15. -/
theorem heADC2025Lemma715_nonmaximal (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3))
    (hADC' : Lattice.IsNADC.{u, u, u} r M (2 * k + 3))
    (ambient : q.IsIsometric r)
    (hpenultimate : a.order ⟨2 * k + 3, by omega⟩ =
      b.order ⟨2 * k + 3, by omega⟩)
    (hnonmaximal : a.order ⟨2 * k + 3, by omega⟩ ≠
      -(2 * (ramificationIndex K : Int))) :
    Lattice.IsIsometric q r L M := by
  have C := a.heADC2025Theorem74Necessity k hADC
  have D := b.heADC2025Theorem74Necessity k hADC'
  have horders := a.heADC2025Lemma715_sameOrders k b hADC hADC'
    ambient hpenultimate
  apply (a.beli2009Theorem31_concrete ambient b).mpr
  exact
    { sameOrders := horders
      sameAlphas := a.heADC2025Lemma715_sameAlphas k b C D horders hnonmaximal
      prefixDefectBounds := a.heADC2025Lemma715_prefixDefectBounds k b
        hADC.isIntegral hADC'.isIntegral C D horders hnonmaximal
      internalRepresentations := a.heADC2025Lemma715_internalRepresentations k b
        hADC.isIntegral hADC'.isIntegral C D hnonmaximal }

/-- At `R_(n+1)=-2e`, the ADC order profile is the standard odd maximal
profile, so the lattice is `O`-maximal. -/
theorem heADC2025Lemma715_isOMaximal_of_penultimate (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3))
    (hpenultimate : a.order ⟨2 * k + 3, by omega⟩ =
      -(2 * (ramificationIndex K : Int))) :
    Lattice.IsOMaximal q L := by
  have C := a.heADC2025Theorem74Necessity k hADC
  let ac := a.castLength (by omega : 2 * k + 5 = 2 * (k + 1) + 3)
  apply ac.heADCCorankOne_standardTail_isOMaximal (k + 1) hADC.isIntegral
  · intro i
    rw [order_castLength]
    rcases Nat.even_or_odd i.val with heven | hodd
    · have h := C.initial.oddOrder ⟨i.val, by omega⟩ heven.add_one
      simpa only [if_pos heven] using h
    · have h := C.initial.evenOrder ⟨i.val, by omega⟩ hodd.add_one
      have hnotEven : ¬ Even i.val := by
        exact Nat.not_even_iff_odd.mpr hodd
      simpa only [if_neg hnotEven] using h
  · rw [order_castLength]
    exact C.initial.oddOrder ⟨2 * k + 2, by omega⟩
      (show Odd (2 * k + 3) by exact ⟨k + 1, by omega⟩)
  · rw [order_castLength]
    simpa only [show 2 * (k + 1) + 1 = 2 * k + 3 by omega] using hpenultimate
  · rw [order_castLength]
    change a.order ⟨2 * k + 4, by omega⟩ ≤ 1
    rcases C.last with hzero | hone
    · rw [hzero]
      norm_num
    · rw [hone]

/-- He (2025), Lemma 7.15.  The right-hand side retains both invariants
printed in the published statement. -/
theorem heADC2025Lemma715 (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3))
    (hADC' : Lattice.IsNADC.{u, u, u} r M (2 * k + 3)) :
    Lattice.IsIsometric q r L M ↔
      q.IsIsometric r ∧
        a.order ⟨2 * k + 3, by omega⟩ =
          b.order ⟨2 * k + 3, by omega⟩ := by
  constructor
  · rintro ⟨f⟩
    have horders : a.SameOrders b := a.sameOrders_of_latticeIsometry b f
    exact ⟨⟨f.toQuadraticSpaceIsometry⟩, horders ⟨2 * k + 3, by omega⟩⟩
  · rintro ⟨ambient, hpenultimate⟩
    by_cases hmaximal : a.order ⟨2 * k + 3, by omega⟩ =
        -(2 * (ramificationIndex K : Int))
    · have hmaximal' : b.order ⟨2 * k + 3, by omega⟩ =
          -(2 * (ramificationIndex K : Int)) := hpenultimate.symm.trans hmaximal
      exact Lattice.oMaximal_isIsometric_of_isometric
        (a.heADC2025Lemma715_isOMaximal_of_penultimate k hADC hmaximal)
        (b.heADC2025Lemma715_isOMaximal_of_penultimate k hADC' hmaximal') ambient
    · exact a.heADC2025Lemma715_nonmaximal k b hADC hADC' ambient
        hpenultimate hmaximal

end BONG.GoodBONG

end Bong
