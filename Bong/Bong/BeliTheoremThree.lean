/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma73
import Bong.Bong.BeliTheoremOneReverse
import Bong.Bong.BinaryAdmissibility

/-!
# Beli (2003), Theorem 3

The theorem characterizes when the integral spinor-norm image is contained in
the valuation-unit square classes.  Its two conditions are stated for every
adjacent pair and every equal-order three-entry block of a good BONG.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n m : Nat}

namespace BONG

/-- A unit-bounded adjacent binary group has even order gap. -/
theorem adjacentOrderGap_even_of_spinorGroup_le_unit
    [BeliLemma72Laws K] (b : BONG V q L n)
    (i : Fin n) (hi : i.1 + 1 < n)
    (hunit : beliSpinorGroup K (b.adjacentUnitSquareClass i hi) ≤
      valuationUnitSquareClassSubgroup K) :
    Even (b.order ⟨i.1 + 1, hi⟩ - b.order i) := by
  have hunit' : beliSpinorGroupRepresentative K
        (b.adjacentParameter i hi) ≤
      valuationUnitSquareClassSubgroup K := by
    simpa only [adjacentUnitSquareClass,
      beliSpinorGroup_unitSquareClass] using hunit
  have hcriterion := (beliLemma72_i (K := K)
    (b.adjacentParameter i hi)
    (b.adjacentParameter_isBinaryParameterAdmissible i hi)).1 hunit'
  unfold SatisfiesLemma72UnitCriterion at hcriterion
  rw [b.ordUnit_adjacentParameter i hi] at hcriterion
  exact hcriterion.1

/-- The two conditions in Beli (2003), Theorem 3. -/
def SatisfiesTheoremThreeConditions (b : BONG V q L n) : Prop :=
  (∀ (i : Fin n) (hi : i.1 + 1 < n),
    beliSpinorGroup K (b.adjacentUnitSquareClass i hi) ≤
      valuationUnitSquareClassSubgroup K) ∧
  ∀ (i : Fin n) (hi : i.1 + 2 < n),
    b.order i = b.order ⟨i.1 + 2, hi⟩ →
      Int.ModEq 2
        ((b.order ⟨i.1 + 1, by omega⟩ - b.order i) / 2)
        (ramificationIndex K : Int)

/-- Condition (i) forces every adjacent order difference to be even. -/
theorem SatisfiesTheoremThreeConditions.adjacentOrderGap_even
    [BeliLemma72Laws K] {b : BONG V q L n}
    (h : b.SatisfiesTheoremThreeConditions)
    (i : Fin n) (hi : i.1 + 1 < n) :
    Even (b.order ⟨i.1 + 1, hi⟩ - b.order i) :=
  b.adjacentOrderGap_even_of_spinorGroup_le_unit i hi (h.1 i hi)

/-- Even adjacent gaps force all BONG orders to have the same parity. -/
theorem order_modEq_zero_of_adjacentOrderGap_even
    (b : BONG V q L (n + 1))
    (hgap : ∀ (i : Fin (n + 1)) (hi : i.1 + 1 < n + 1),
      Even (b.order ⟨i.1 + 1, hi⟩ - b.order i))
    (i : Fin (n + 1)) :
    Int.ModEq 2 (b.order i) (b.order 0) := by
  induction i using Fin.induction with
  | zero => exact Int.ModEq.rfl
  | succ j ih =>
      have hgap' := hgap j.castSucc (by
        change j.1 + 1 < n + 1
        exact Nat.succ_lt_succ j.isLt)
      change Even (b.order j.succ - b.order j.castSucc) at hgap'
      rcases hgap' with ⟨t, ht⟩
      have hstep : Int.ModEq 2 (b.order j.succ)
          (b.order j.castSucc) := by
        rw [Int.modEq_iff_dvd]
        refine ⟨-t, ?_⟩
        omega
      exact hstep.trans ih

/-- Under condition (i), all BONG orders have the same parity. -/
theorem SatisfiesTheoremThreeConditions.order_modEq_zero
    [BeliLemma72Laws K] {b : BONG V q L (n + 1)}
    (h : b.SatisfiesTheoremThreeConditions) (i : Fin (n + 1)) :
    Int.ModEq 2 (b.order i) (b.order 0) :=
  order_modEq_zero_of_adjacentOrderGap_even b
    (fun j hj => h.adjacentOrderGap_even j hj) i

/-- Condition (i) places the adjacent part of Theorem 1 in the unit group. -/
theorem theoremOneAdjacentFactor_le_valuationUnit
    {b : BONG V q L (n + 3)}
    (h : b.SatisfiesTheoremThreeConditions) :
    b.theoremOneAdjacentFactor ≤ valuationUnitSquareClassSubgroup K := by
  apply iSup_le
  intro i
  exact h.1 i.castSucc (by
    change i.1 + 1 < n + 3
    exact Nat.succ_lt_succ i.isLt)

/-- Under property A and condition (i), every two-step depth is positive, so
the whole right side of Theorem 1 is unit-bounded. -/
theorem theoremOneRHS_le_valuationUnit
    [BeliLemma72Laws K]
    {b : BONG V q L (n + 3)}
    (hA : b.HasPropertyA)
    (h : b.SatisfiesTheoremThreeConditions) :
    b.theoremOneRHS ≤ valuationUnitSquareClassSubgroup K := by
  have halpha : 0 < b.theoremOneAlpha := by
    have hmem := b.theoremOneAlpha_mem_candidates
    rw [theoremOneAlphaCandidates, Finset.mem_image] at hmem
    rcases hmem with ⟨i, _hi, hidepth⟩
    rw [← hidepth]
    let i0 : Fin (n + 3) := ⟨i.1, by omega⟩
    let i1 : Fin (n + 3) := ⟨i.1 + 1, by omega⟩
    let i2 : Fin (n + 3) := ⟨i.1 + 2, by omega⟩
    have hlt : b.order i0 < b.order i2 := by
      have hi0 : i0.1 + 2 < n + 3 := by
        simp [i0]
        omega
      simpa [i0, i2] using hA i0 hi0
    have hgap0 : Even (b.order i1 - b.order i0) := by
      have hi0 : i0.1 + 1 < n + 3 := by
        simp [i0]
        omega
      simpa [i0, i1] using h.adjacentOrderGap_even i0 hi0
    have hgap1 : Even (b.order i2 - b.order i1) := by
      have hi1 : i1.1 + 1 < n + 3 := by
        simp [i1]
        omega
      simpa [i1, i2] using h.adjacentOrderGap_even i1 hi1
    rcases hgap0 with ⟨r, hr⟩
    rcases hgap1 with ⟨s, hs⟩
    have hhalf : (b.order i2 - b.order i0) / 2 = r + s := by
      omega
    have hrs : 0 < r + s := by
      omega
    unfold theoremOneTwoStepDepth
    change 0 < Int.toNat ((b.order i2 - b.order i0) / 2)
    rw [hhalf]
    exact Int.lt_toNat.mpr hrs
  apply sup_le
  · exact theoremOneAdjacentFactor_le_valuationUnit h
  · rw [theoremOneCongruenceFactor,
      beliCongruenceSquareClassSubgroup_of_pos K halpha]
    exact principalUnitSquareClassSubgroup_le_valuationUnit K
      b.theoremOneAlpha

/-- Unit-boundedness of the full spinor image implies condition (i). -/
theorem adjacentSpinorGroup_le_unit_of_spinorNormIsUnitBounded
    [BeliLemma49Laws.{u, v} K] [BinarySpinorLocalLaws.{u, v} K]
    (b : BONG V q L n) (hgood : b.IsGood)
    (hunit : Lattice.SpinorNormIsUnitBounded q L)
    (i : Fin n) (hi : i.1 + 1 < n) :
    beliSpinorGroup K (b.adjacentUnitSquareClass i hi) ≤
      valuationUnitSquareClassSubgroup K := by
  intro z hz
  apply hunit
  change z ∈ (Lattice.spinorNormImageSubgroup (q := q) (L := L) :
    Set (SquareClass K))
  rw [Lattice.coe_spinorNormImageSubgroup]
  exact b.beliCorollary410_ii hgood i hi hz

/-- Lemmas 7.1 and 7.3 give condition (ii) from a unit-bounded spinor image. -/
theorem twoStepParity_of_spinorNormIsUnitBounded
    [BeliLemma49Laws.{u, v} K] [BinarySpinorLocalLaws.{u, v} K]
    [BeliLemma71Laws.{u, v} K] [BeliLemma72Laws K]
    [BeliLemma73Laws.{u, v} K]
    (b : BONG V q L (n + 3)) (hgood : b.IsGood)
    (hunit : Lattice.SpinorNormIsUnitBounded q L)
    (i : Fin (n + 3)) (hi : i.1 + 2 < n + 3)
    (heq : b.order i = b.order ⟨i.1 + 2, hi⟩) :
    Int.ModEq 2
      ((b.order ⟨i.1 + 1, by omega⟩ - b.order i) / 2)
      (ramificationIndex K : Int) := by
  let j : Fin (n + 1) := ⟨i.1, by omega⟩
  have hadj : ∀ (k : Fin (n + 3)) (hk : k.1 + 1 < n + 3),
      beliSpinorGroup K (b.adjacentUnitSquareClass k hk) ≤
        valuationUnitSquareClassSubgroup K :=
    fun k hk => b.adjacentSpinorGroup_le_unit_of_spinorNormIsUnitBounded
      hgood hunit k hk
  have hblock : b.Lemma73Hypotheses j := by
    unfold Lemma73Hypotheses
    refine ⟨?_, ?_, ?_⟩
    · simpa [j, lemma73FirstIndex, lemma73LastIndex] using heq
    · simpa [j, lemma73FirstIndex] using hadj i (by omega)
    · simpa [j, lemma73MiddleIndex] using
        hadj ⟨i.1 + 1, by omega⟩ (by omega)
  rcases b.beliLemma73 j hgood hblock with ⟨w⟩
  have hcomponent := Lattice.beliLemma71_i w.decomposition
    w.componentNormData hunit (0 : Fin 2) (1 : Fin 2)
  rw [w.hyperbolicNorm_order, w.remainderNorm_order] at hcomponent
  have hgap : ∀ (k : Fin (n + 3)) (hk : k.1 + 1 < n + 3),
      Even (b.order ⟨k.1 + 1, hk⟩ - b.order k) :=
    fun k hk => b.adjacentOrderGap_even_of_spinorGroup_le_unit
      k hk (hadj k hk)
  have hRi0 : Int.ModEq 2 (b.order i) (b.order 0) :=
    order_modEq_zero_of_adjacentOrderGap_even b hgap i
  have hlocalGap := hgap i (by omega)
  rcases hlocalGap with ⟨t, ht⟩
  change b.order ⟨i.1 + 1, by omega⟩ - b.order i = t + t at ht
  have hscale : b.lemma73HyperbolicScaleOrder j = b.order i + t := by
    unfold lemma73HyperbolicScaleOrder
    change (b.order i + b.order ⟨i.1 + 1, by omega⟩) / 2 =
      b.order i + t
    omega
  have htotal : Int.ModEq 2
      (b.lemma73HyperbolicScaleOrder j + ramificationIndex K)
      (b.order i) := hcomponent.trans hRi0.symm
  rw [hscale] at htotal
  have hsum : Int.ModEq 2 (t + ramificationIndex K) 0 := by
    apply Int.ModEq.add_left_cancel' (b.order i)
    simpa only [add_assoc, add_zero] using htotal
  have htneg : Int.ModEq 2 t (-(ramificationIndex K : Int)) := by
    have := hsum.sub_right (ramificationIndex K : Int)
    simpa only [add_sub_cancel_right, zero_sub] using this
  have hneg : Int.ModEq 2 (-(ramificationIndex K : Int))
      (ramificationIndex K : Int) := by
    rw [Int.modEq_iff_dvd]
    refine ⟨ramificationIndex K, ?_⟩
    ring
  have htparity : Int.ModEq 2 t (ramificationIndex K : Int) :=
    htneg.trans hneg
  have hhalf :
      (b.order ⟨i.1 + 1, by omega⟩ - b.order i) / 2 = t := by
    omega
  rw [hhalf]
  exact htparity

/-- The two conditions in Theorem 3 are necessary. -/
theorem theoremThreeConditions_of_spinorNormIsUnitBounded
    [BeliLemma49Laws.{u, v} K] [BinarySpinorLocalLaws.{u, v} K]
    [BeliLemma71Laws.{u, v} K] [BeliLemma72Laws K]
    [BeliLemma73Laws.{u, v} K]
    (b : BONG V q L m) (hgood : b.IsGood)
    (hunit : Lattice.SpinorNormIsUnitBounded q L) :
    b.SatisfiesTheoremThreeConditions := by
  refine ⟨fun i hi =>
    b.adjacentSpinorGroup_le_unit_of_spinorNormIsUnitBounded
      hgood hunit i hi, ?_⟩
  intro i hi heq
  obtain ⟨n, hn⟩ : ∃ n, m = n + 3 := by
    use m - 3
    omega
  subst m
  exact b.twoStepParity_of_spinorNormIsUnitBounded
    hgood hunit i hi heq

/-- The parity condition needed to reattach the hyperbolic plane in the
inductive proof of Theorem 3. -/
theorem Lemma73SplittingWitness.normOrdersSameParity
    [BeliLemma72Laws K]
    {b : BONG V q L (n + 3)} {i : Fin (n + 1)}
    (w : Lemma73SplittingWitness b i)
    (h : b.SatisfiesTheoremThreeConditions)
    (heq : b.order (lemma73FirstIndex i) =
      b.order (lemma73LastIndex i)) :
    w.toHyperbolicPlaneSplitting.NormOrdersSameParity := by
  unfold Lattice.HyperbolicPlaneSplitting.NormOrdersSameParity
  rw [w.toHyperbolicPlaneSplitting_hyperbolic_order,
    w.toHyperbolicPlaneSplitting_remainder_order]
  have hlocal : Int.ModEq 2
      ((b.order (lemma73MiddleIndex i) -
        b.order (lemma73FirstIndex i)) / 2)
      (ramificationIndex K : Int) := by
    have hcondition := h.2 (lemma73FirstIndex i) (by
      simp only [lemma73FirstIndex]
      omega) (by
        simpa [lemma73FirstIndex, lemma73LastIndex] using heq)
    simpa [lemma73FirstIndex, lemma73MiddleIndex] using hcondition
  have hgap := h.adjacentOrderGap_even (lemma73FirstIndex i) (by
    simp only [lemma73FirstIndex]
    omega)
  change Even (b.order (lemma73MiddleIndex i) -
    b.order (lemma73FirstIndex i)) at hgap
  rcases hgap with ⟨t, ht⟩
  have hhalf : (b.order (lemma73MiddleIndex i) -
      b.order (lemma73FirstIndex i)) / 2 = t := by
    omega
  have htparity : Int.ModEq 2 t (ramificationIndex K : Int) := by
    rw [hhalf] at hlocal
    exact hlocal
  have hdouble : Int.ModEq 2
      ((ramificationIndex K : Int) + ramificationIndex K) 0 := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-(ramificationIndex K : Int), ?_⟩
    ring
  have htzero : Int.ModEq 2
      (t + ramificationIndex K) 0 :=
    (htparity.add Int.ModEq.rfl).trans hdouble
  have hfirst : Int.ModEq 2 (b.order (lemma73FirstIndex i))
      (b.order 0) := h.order_modEq_zero (lemma73FirstIndex i)
  have hscale : b.lemma73HyperbolicScaleOrder i =
      b.order (lemma73FirstIndex i) + t := by
    unfold lemma73HyperbolicScaleOrder
    omega
  rw [hscale]
  simpa only [add_assoc, add_zero] using hfirst.add htzero

end BONG

/-- The low-rank base cases and the Lemma 7.2(ii) condition-transfer step in
the induction proving Beli (2003), Theorem 3.  There is no default instance. -/
class BeliTheoremThreeLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  low_rank_unitBounded
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {m : Nat}
    (b : BONG V q L m) : b.IsGood → m ≤ 2 →
      b.SatisfiesTheoremThreeConditions →
        Lattice.SpinorNormIsUnitBounded q L
  replacement_conditions
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 3)) (i : Fin (n + 1)) :
    b.IsGood → b.SatisfiesTheoremThreeConditions →
    b.Lemma73Hypotheses i →
    (w : b.Lemma73SplittingWitness i) →
      w.remainderBONG.SatisfiesTheoremThreeConditions

namespace BONG

variable [BeliLemma49Laws.{u, v} K] [BinarySpinorLocalLaws.{u, v} K]
  [BeliTheoremOneTernaryLaws.{u, v} K]
  [BeliLemma66Laws.{u, v} K] [BeliLemma67Laws.{u, v} K]
  [BeliLemma411Laws.{u, v} K]
  [BeliLemma71Laws.{u, v} K] [BeliLemma72Laws K]
  [BeliLemma73Laws.{u, v} K]
  [BeliTheoremThreeLaws.{u, v} K]

omit [BeliLemma71Laws K] [BeliLemma73Laws K]
  [BeliTheoremThreeLaws K] in
/-- The property-A branch of the sufficient direction follows from
Theorem 1. -/
theorem spinorNormIsUnitBounded_of_propertyA
    (b : BONG V q L (n + 3)) (hA : b.HasPropertyA)
    (h : b.SatisfiesTheoremThreeConditions) :
    Lattice.SpinorNormIsUnitBounded q L := by
  unfold Lattice.SpinorNormIsUnitBounded
  rw [b.beliTheoremOne hA]
  exact b.theoremOneRHS_le_valuationUnit hA h

/-- The sufficient direction of Theorem 3, by induction after splitting off
the hyperbolic plane supplied by Lemma 7.3. -/
theorem spinorNormIsUnitBounded_of_theoremThreeConditions
    (b : BONG V q L m) (hgood : b.IsGood)
    (h : b.SatisfiesTheoremThreeConditions) :
    Lattice.SpinorNormIsUnitBounded q L := by
  induction m using Nat.strong_induction_on generalizing V with
  | h m ih =>
      by_cases hm : m ≤ 2
      · exact BeliTheoremThreeLaws.low_rank_unitBounded b hgood hm h
      · obtain ⟨n, hn⟩ : ∃ n, m = n + 3 := by
          use m - 3
          omega
        subst m
        by_cases hA : b.HasPropertyA
        · exact b.spinorNormIsUnitBounded_of_propertyA hA h
        · have hexists : ∃ (i : Fin (n + 3))
              (hi : i.1 + 2 < n + 3),
              b.order i = b.order ⟨i.1 + 2, hi⟩ := by
            by_contra hnone
            apply hA
            rw [hasPropertyA_iff_isGood_and_ne]
            refine ⟨hgood, ?_⟩
            intro i hi heq
            exact hnone ⟨i, hi, heq⟩
          rcases hexists with ⟨i, hi, heq⟩
          let j : Fin (n + 1) := ⟨i.1, by omega⟩
          have heqj : b.order (lemma73FirstIndex j) =
              b.order (lemma73LastIndex j) := by
            simpa [j, lemma73FirstIndex, lemma73LastIndex] using heq
          have hblock : b.Lemma73Hypotheses j := by
            unfold Lemma73Hypotheses
            refine ⟨heqj, ?_, ?_⟩
            · simpa [j, lemma73FirstIndex] using h.1 i (by omega)
            · simpa [j, lemma73MiddleIndex] using
                h.1 ⟨i.1 + 1, by omega⟩ (by omega)
          rcases b.beliLemma73 j hgood hblock with ⟨w⟩
          have hremConditions :=
            BeliTheoremThreeLaws.replacement_conditions
              b j hgood h hblock w
          have hremUnit := ih (n + 1) (by omega)
            w.remainderBONG w.good hremConditions
          let S := w.toHyperbolicPlaneSplitting
          have hrem : S.RemainderIsUnitBounded := by
            change Lattice.SpinorNormIsUnitBounded
              (w.decomposition.component 1).space
              (w.decomposition.component 1).lattice
            exact hremUnit
          have hparity : S.NormOrdersSameParity := by
            simpa [S] using w.normOrdersSameParity h heqj
          exact le_of_eq (Lattice.beliLemma71_ii_same S hrem hparity)

/-- Beli (2003), Theorem 3. -/
theorem beliTheoremThree (b : BONG V q L m) (hgood : b.IsGood) :
    Lattice.SpinorNormIsUnitBounded q L ↔
      b.SatisfiesTheoremThreeConditions :=
  ⟨b.theoremThreeConditions_of_spinorNormIsUnitBounded hgood,
    b.spinorNormIsUnitBounded_of_theoremThreeConditions hgood⟩

end BONG

end Bong
