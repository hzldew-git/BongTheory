/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009QuadraticRepresentation

/-!
# Beli (2009/2010), Lemmas 3.8--3.9 and Theorem 3.1

The ideal-containment thresholds of Lemma 3.8 are reduced to rational
arithmetic.  Lemma 3.9 is assembled from checked local BONG sites and
O'Meara clauses.  The main theorem then follows from O'Meara 93:28, which
is isolated in one non-default interface.
-/

namespace Bong

theorem threshold_congr_of_eq_or_both_gt
    (e x alpha fundamental : ℚ) (hx : 0 ≤ x)
    (hcomparison : alpha = fundamental ∨
      (2 * e < alpha ∧ 2 * e < fundamental)) :
    2 * e < x + fundamental ↔ 2 * e < x + alpha := by
  rcases hcomparison with h | ⟨halpha, hfundamental⟩
  · rw [h]
  · constructor <;> intro <;> linarith

theorem sum_gt_iff_sum_capped_min (e alpha beta : ℚ) :
    2 * e < alpha + beta ↔
      2 * e < alpha + min alpha (min beta e) ∨
        2 * e < beta + min alpha (min beta e) := by
  constructor
  · intro hsum
    by_cases ha : e < alpha
    · by_cases hb : e < beta
      · left
        rw [min_eq_right (le_of_lt hb), min_eq_right (le_of_lt ha)]
        linarith
      · have hbe : beta ≤ e := le_of_not_gt hb
        have hba : beta ≤ alpha := by linarith
        left
        rw [min_eq_left hbe, min_eq_right hba]
        exact hsum
    · have hae : alpha ≤ e := le_of_not_gt ha
      by_cases hb : e < beta
      · have hab : alpha ≤ beta := by linarith
        right
        rw [min_eq_right (le_of_lt hb), min_eq_left hae]
        simpa [add_comm] using hsum
      · have hbe : beta ≤ e := le_of_not_gt hb
        linarith
  · rintro (hleft | hright)
    · have hm : min alpha (min beta e) ≤ beta :=
          (min_le_right _ _).trans (min_le_left _ _)
      linarith
    · have hm := min_le_left alpha (min beta e)
      linarith

/-! ## Lemma 3.8 -/

/-- A non-unary boundary case in Lemma 3.8.  The containment proposition
is connected to its ideal-order inequality, while Lemma 2.16(ii) supplies
the comparison between the fundamental order and the adjacent alpha. -/
structure Beli2009RegularBoundaryThresholdData where
  e : ℚ
  neighboringAlpha : ℚ
  boundaryAlpha : ℚ
  normalizedWeightOrder : ℚ
  fundamentalOrder : ℚ
  containment : Prop
  weight_nonnegative : 0 ≤ normalizedWeightOrder
  weight_eq_neighboringAlpha : normalizedWeightOrder = neighboringAlpha
  boundaryComparison : boundaryAlpha = fundamentalOrder ∨
    (2 * e < boundaryAlpha ∧ 2 * e < fundamentalOrder)
  containment_iff_order : containment ↔
    2 * e < normalizedWeightOrder + fundamentalOrder

namespace Beli2009RegularBoundaryThresholdData

theorem threshold_iff_containment
    (D : Beli2009RegularBoundaryThresholdData) :
    2 * D.e < D.neighboringAlpha + D.boundaryAlpha ↔ D.containment := by
  have hthreshold := threshold_congr_of_eq_or_both_gt
    D.e D.normalizedWeightOrder D.boundaryAlpha D.fundamentalOrder
      D.weight_nonnegative D.boundaryComparison
  rw [D.weight_eq_neighboringAlpha] at hthreshold
  have hcontainment : D.containment ↔
      2 * D.e < D.neighboringAlpha + D.fundamentalOrder := by
    simpa [D.weight_eq_neighboringAlpha] using D.containment_iff_order
  exact (hcontainment.trans hthreshold).symm

/-- Beli (2009/2010), Lemma 3.8(i). -/
theorem beli2009Lemma38_i (D : Beli2009RegularBoundaryThresholdData) :
    2 * D.e < D.neighboringAlpha + D.boundaryAlpha ↔ D.containment :=
  D.threshold_iff_containment

/-- Beli (2009/2010), Lemma 3.8(ii). -/
theorem beli2009Lemma38_ii (D : Beli2009RegularBoundaryThresholdData) :
    2 * D.e < D.boundaryAlpha + D.neighboringAlpha ↔ D.containment := by
  rw [add_comm]
  exact D.threshold_iff_containment

end Beli2009RegularBoundaryThresholdData

/-- The internal unary-component case of Lemma 3.8(iii).  Endpoint unary
components are omitted later because condition 3.1(iv) is then vacuous. -/
structure Beli2009UnaryBoundaryThresholdData where
  e : ℚ
  leftAlpha : ℚ
  rightAlpha : ℚ
  normalizedWeightOrder : ℚ
  previousFundamentalOrder : ℚ
  nextFundamentalOrder : ℚ
  previousContainment : Prop
  nextContainment : Prop
  weight_nonnegative : 0 ≤ normalizedWeightOrder
  weight_eq_cappedMinimum :
    normalizedWeightOrder = min leftAlpha (min rightAlpha e)
  previousComparison : leftAlpha = previousFundamentalOrder ∨
    (2 * e < leftAlpha ∧ 2 * e < previousFundamentalOrder)
  nextComparison : rightAlpha = nextFundamentalOrder ∨
    (2 * e < rightAlpha ∧ 2 * e < nextFundamentalOrder)
  previousContainment_iff_order : previousContainment ↔
    2 * e < normalizedWeightOrder + previousFundamentalOrder
  nextContainment_iff_order : nextContainment ↔
    2 * e < normalizedWeightOrder + nextFundamentalOrder

namespace Beli2009UnaryBoundaryThresholdData

/-- Beli (2009/2010), Lemma 3.8(iii), at a non-endpoint unary block. -/
theorem beli2009Lemma38_iii (D : Beli2009UnaryBoundaryThresholdData) :
    2 * D.e < D.leftAlpha + D.rightAlpha ↔
      D.previousContainment ∨ D.nextContainment := by
  have hprevious := threshold_congr_of_eq_or_both_gt
    D.e D.normalizedWeightOrder D.leftAlpha D.previousFundamentalOrder
      D.weight_nonnegative D.previousComparison
  have hnext := threshold_congr_of_eq_or_both_gt
    D.e D.normalizedWeightOrder D.rightAlpha D.nextFundamentalOrder
      D.weight_nonnegative D.nextComparison
  have hprevious' : D.previousContainment ↔
      2 * D.e < D.leftAlpha + D.normalizedWeightOrder := by
    exact D.previousContainment_iff_order.trans (by
      simpa [add_comm] using hprevious)
  have hnext' : D.nextContainment ↔
      2 * D.e < D.rightAlpha + D.normalizedWeightOrder := by
    exact D.nextContainment_iff_order.trans (by
      simpa [add_comm] using hnext)
  rw [D.weight_eq_cappedMinimum] at hprevious' hnext'
  exact (sum_gt_iff_sum_capped_min D.e D.leftAlpha D.rightAlpha).trans
    (or_congr hprevious'.symm hnext'.symm)

end Beli2009UnaryBoundaryThresholdData

/-! ## Lemma 3.9 -/

open Dyadic

universe u v w

/-- Checked local sites and O'Meara clauses in the proof of Lemma 3.9.
Each non-vacuous BONG index is a site; an internal unary site can be incident
to both neighboring O'Meara clauses. -/
structure Beli2009RepresentationReduction
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {n : Nat}
    (a : BONG.GoodBONG q L (n + 1))
    (b : BONG.GoodBONG r M (n + 1)) where
  siteCount : Nat
  clauseCount : Nat
  siteTrigger : Fin siteCount → Prop
  siteRepresentation : Fin siteCount → Prop
  clauseContainment : Fin clauseCount → Prop
  clauseRepresentation : Fin clauseCount → Prop
  incident : Fin siteCount → Fin clauseCount → Prop
  omearaII : Prop
  omearaIII : Prop
  trigger_iff (i : Fin siteCount) :
    siteTrigger i ↔ ∃ c, incident i c ∧ clauseContainment c
  representation_iff (i : Fin siteCount) (c : Fin clauseCount) :
    incident i c → (siteRepresentation i ↔ clauseRepresentation c)
  clause_covered (c : Fin clauseCount) : ∃ i, incident i c
  internal_iff_sites : a.InternalRepresentationConditions b ↔
    ∀ i, siteTrigger i → siteRepresentation i
  omeara_iff_clauses : omearaII ∧ omearaIII ↔
    ∀ c, clauseContainment c → clauseRepresentation c

namespace Beli2009RepresentationReduction

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {a : BONG.GoodBONG q L (n + 1)}
  {b : BONG.GoodBONG r M (n + 1)}

theorem allSites_iff_allClauses (D : Beli2009RepresentationReduction a b) :
    (∀ i, D.siteTrigger i → D.siteRepresentation i) ↔
      ∀ c, D.clauseContainment c → D.clauseRepresentation c := by
  constructor
  · intro hsites c hcontainment
    obtain ⟨i, hincident⟩ := D.clause_covered c
    have htrigger : D.siteTrigger i :=
      (D.trigger_iff i).2 ⟨c, hincident, hcontainment⟩
    exact (D.representation_iff i c hincident).1 (hsites i htrigger)
  · intro hclauses i htrigger
    obtain ⟨c, hincident, hcontainment⟩ := (D.trigger_iff i).1 htrigger
    exact (D.representation_iff i c hincident).2
      (hclauses c hcontainment)

/-- Beli (2009/2010), Lemma 3.9. -/
theorem beli2009Lemma39 (D : Beli2009RepresentationReduction a b) :
    a.InternalRepresentationConditions b ↔ D.omearaII ∧ D.omearaIII :=
  D.internal_iff_sites.trans
    (D.allSites_iff_allClauses.trans D.omeara_iff_clauses.symm)

end Beli2009RepresentationReduction

/-! ## Theorem 3.1 -/

/-- The reductions from good-BONG conditions to the fundamental type and
the three clauses of O'Meara 93:28. -/
structure Beli2009ClassificationReduction
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {n : Nat}
    (ambient : q.IsIsometric r)
    (a : BONG.GoodBONG q L (n + 1))
    (b : BONG.GoodBONG r M (n + 1)) where
  preliminaryFundamentalType : Prop
  fundamentalType : Prop
  omearaI : Prop
  jordanCount : Nat
  jordan : a.JordanClassificationReduction b jordanCount
  jordanLaws : BONG.GoodBONG.Beli2009JordanReductionLaws jordan
  representation : Beli2009RepresentationReduction a b
  firstTwo_iff : a.SameOrders b ∧ a.SameAlphas b ↔
    preliminaryFundamentalType
  fundamental_iff : fundamentalType ↔
    preliminaryFundamentalType ∧ ∀ k, jordan.componentCongruence k
  omearaI_iff : omearaI ↔ ∀ k, jordan.boundaryCongruence k

/-- O'Meara 93:28, isolated as the sole classification input.  It has no
default instance. -/
class Beli2009Omeara9328Laws
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {n : Nat}
    {ambient : q.IsIsometric r}
    {a : BONG.GoodBONG q L (n + 1)}
    {b : BONG.GoodBONG r M (n + 1)}
    (D : Beli2009ClassificationReduction ambient a b) : Prop where
  fundamental_of_isometric :
    Lattice.IsIsometric q r L M → D.fundamentalType
  classify_of_fundamental (hfundamental : D.fundamentalType) :
    Lattice.IsIsometric q r L M ↔
      D.omearaI ∧ D.representation.omearaII ∧
        D.representation.omearaIII

namespace Beli2009ClassificationReduction

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {ambient : q.IsIsometric r}
  {a : BONG.GoodBONG q L (n + 1)}
  {b : BONG.GoodBONG r M (n + 1)}

/-- Conditions 3.1(i)--(iii) are the fundamental-type assertion together
with O'Meara 93:28(i).  This is the first step of Beli's proof. -/
theorem firstThree_iff
    (D : Beli2009ClassificationReduction ambient a b) :
    (a.SameOrders b ∧ a.SameAlphas b ∧ a.PrefixDefectBounds b) ↔
      D.fundamentalType ∧ D.omearaI := by
  letI := D.jordanLaws
  constructor
  · rintro ⟨horders, halphas, hprefix⟩
    have hpreliminary := D.firstTwo_iff.1 ⟨horders, halphas⟩
    have hlocal := D.jordan.beli2009Lemma33.1 hprefix
    exact ⟨D.fundamental_iff.2 ⟨hpreliminary, hlocal.1⟩,
      D.omearaI_iff.2 hlocal.2⟩
  · rintro ⟨hfundamental, homearaI⟩
    obtain ⟨hpreliminary, hcomponents⟩ := D.fundamental_iff.1 hfundamental
    obtain ⟨horders, halphas⟩ := D.firstTwo_iff.2 hpreliminary
    have hboundaries := D.omearaI_iff.1 homearaI
    exact ⟨horders, halphas,
      D.jordan.beli2009Lemma33.2 ⟨hcomponents, hboundaries⟩⟩

/-- Beli (2009/2010), Theorem 3.1, derived from O'Meara 93:28 and the
preceding reductions. -/
theorem beli2009Theorem31
    (D : Beli2009ClassificationReduction ambient a b)
    [Beli2009Omeara9328Laws D] :
    Lattice.IsIsometric q r L M ↔ ClassificationConditions a b := by
  constructor
  · intro hisometric
    have hfundamental :=
      Beli2009Omeara9328Laws.fundamental_of_isometric (D := D) hisometric
    have homeara :=
      (Beli2009Omeara9328Laws.classify_of_fundamental
        (D := D) hfundamental).1
        hisometric
    have hfirstThree := D.firstThree_iff.2 ⟨hfundamental, homeara.1⟩
    exact ⟨hfirstThree.1, hfirstThree.2.1, hfirstThree.2.2,
      D.representation.beli2009Lemma39.mpr ⟨homeara.2.1, homeara.2.2⟩⟩
  · rintro ⟨horders, halphas, hthird, hfourth⟩
    obtain ⟨hfundamental, homearaI⟩ :=
      D.firstThree_iff.1 ⟨horders, halphas, hthird⟩
    apply (Beli2009Omeara9328Laws.classify_of_fundamental
      (D := D) hfundamental).2
    exact ⟨homearaI,
      D.representation.beli2009Lemma39.mp hfourth⟩

end Beli2009ClassificationReduction

end Bong
