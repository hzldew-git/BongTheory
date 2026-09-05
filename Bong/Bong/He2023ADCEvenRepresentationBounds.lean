/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCSectionThree
import Bong.Bong.HeHu2022Lemma42

/-!
# Representation bounds used in the even-rank ADC classification

These are the pair-order and determinant-prefix arguments in He (2025),
Lemma 6.4. They apply to arbitrary supplied good BONGs. The complete
published lemma additionally requires specialization to its named maximal
test lattices and the remaining branches.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- A represented endpoint pair forces the same endpoint in the larger
integral lattice and hence the complete preceding alternating pattern.
Unlike a stable-rank criterion, this includes equal rank and codimension one. -/
theorem heADCAlternatingPrefix_of_represented_endpoint {m n : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (n + 2))
    (hrank : n ≤ m) (hL : Lattice.IsIntegral q L)
    (hrep : Lattice.Represents q r L M) (j : Fin (n + 2)) (hj : Odd j.val)
    (hprevious : b.order ⟨j.val - 1, by omega⟩ = 0)
    (hcurrent : b.order j = -(2 * (ramificationIndex K : Int))) :
    HeHuProposition27iiiivConclusions a ⟨j.val, by omega⟩ := by
  have hjPos : 0 < j.val := by obtain ⟨k, hk⟩ := hj; omega
  have hprevEven : Even (j.val - 1) := by
    obtain ⟨k, hk⟩ := hj
    exact ⟨k, by omega⟩
  have C := (a.heADC2025Theorem36 (by omega) hrep.ambient b).mp hrep
  have O := (a.representationOrderCondition_iff b (by omega)).mp C.orderCondition
  have hpair := O.pairSum_le (j.val - 1) (by omega)
  have hpair' : a.order ⟨j.val - 1, by omega⟩ + a.order ⟨j.val, by omega⟩ ≤
      b.order ⟨j.val - 1, by omega⟩ + b.order j := by
    simpa only [orderSequence_at, Nat.sub_add_cancel hjPos] using hpair
  rw [hprevious, hcurrent, zero_add] at hpair'
  have A := a.heHu2022Proposition27i hL
  have hprev := (A.oddIndexed ⟨j.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩
    le_rfl hprevEven hprevEven).1
  have hcurr := (A.evenIndexed ⟨j.val, by omega⟩ ⟨j.val, by omega⟩
    le_rfl hj hj).1
  apply a.heHu2022Proposition27iiiiv hL ⟨j.val, by omega⟩ hj
  omega

/-- Beli's strict cross-gap square conclusion for a represented target
of any smaller rank at least two. The deep completion is constructed, and
its common prefix is transported back to the original target. -/
theorem heADCComparisonPrefix_isSquare_of_strict_crossGap {m n : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (n + 2))
    (hrank : n < m) (hrep : Lattice.Represents q r L M)
    (hstrict : b.order ⟨n + 1, by omega⟩ + 2 * (ramificationIndex K : Int) <
      a.order ⟨n + 2, by omega⟩) :
    IsSquare (a.prefixProduct (n + 2) * b.prefixProduct (n + 2)) := by
  have C := (a.heADC2025Theorem36 (by omega) hrep.ambient b).mp hrep
  obtain ⟨f⟩ := hrep
  obtain ⟨D⟩ := a.exists_deepIntegralExtension b (by omega) f
    a.rankCompletionTailOrderBound
    (a.representationAlphaValue b (rankCompletionBoundaryIndex (by omega)))
  have horder : a.RepresentationOrderCondition D.completedBONG le_rfl :=
    a.representationOrderCondition_toSameRank_of_prefixAgreement
      D.prefixAgreement D.tailOrder C.orderCondition
  have hdefect : a.RepresentationDefectCondition D.completedBONG :=
    a.representationDefectCondition_toSameRank_of_prefixAgreement
      D.prefixAgreement (by omega) D.tailOrder D.boundaryAlpha.le C.defectCondition
  let i : RepresentationIndex (m + 2) (m + 2) :=
    { val := n + 2
      pos := by omega
      lt_large := by omega
      le_small := by omega }
  have hlast : D.completedBONG.order ⟨n + 1, by omega⟩ =
      b.order ⟨n + 1, by omega⟩ := D.prefixAgreement.order_eq_nat (by omega)
  have hgap : D.completedBONG.order ⟨i.val - 1, by dsimp [i]; omega⟩ +
        2 * (ramificationIndex K : Int) < a.order ⟨i.val, i.lt_large⟩ := by
    simpa only [i, show n + 2 - 1 = n + 1 by omega, hlast] using hstrict
  have hsquare := a.beli2019Corollary210_complete D.completedBONG horder hdefect i
    (by dsimp [i]; omega) hgap
  have hprefix := D.prefixAgreement.prefixProduct_eq (n + 2) le_rfl
  simpa only [i, hprefix] using hsquare

/-- Two represented even-rank endpoint lattices in distinct determinant
classes force the next order to vanish, including codimension one. The
class-separation hypothesis is explicit here and must be proved for each
named testing pair before using this support lemma as a paper endpoint. -/
theorem heADCBoundaryOrder_zero_of_two_represented_classes {m n : Nat}
    {rOne rDelta : QuadraticSpace K W} {MOne MDelta : Lattice K W}
    (a : GoodBONG q L (m + 2))
    (bOne : GoodBONG rOne MOne (n + 2))
    (bDelta : GoodBONG rDelta MDelta (n + 2))
    (hrank : n < m) (hnEven : Even (n + 2)) (hL : Lattice.IsIntegral q L)
    (hOne : Lattice.Represents q rOne L MOne)
    (hDelta : Lattice.Represents q rDelta L MDelta)
    (hOneLast : bOne.order ⟨n + 1, by omega⟩ = -(2 * (ramificationIndex K : Int)))
    (hDeltaLast : bDelta.order ⟨n + 1, by omega⟩ = -(2 * (ramificationIndex K : Int)))
    (hclasses : ¬ IsSquare (bOne.prefixProduct (n + 2) * bDelta.prefixProduct (n + 2))) :
    a.order ⟨n + 2, by omega⟩ = 0 := by
  have hlower := ((a.heHu2022Proposition27i hL).oddIndexed
    ⟨n + 2, by omega⟩ ⟨n + 2, by omega⟩ le_rfl hnEven hnEven).1
  apply le_antisymm ?_ hlower
  by_contra hnot
  have hpos : 0 < a.order ⟨n + 2, by omega⟩ := lt_of_not_ge hnot
  have hsquareOne := a.heADCComparisonPrefix_isSquare_of_strict_crossGap bOne hrank hOne
    (by rw [hOneLast]; simpa using hpos)
  have hsquareDelta := a.heADCComparisonPrefix_isSquare_of_strict_crossGap bDelta hrank hDelta
    (by rw [hDeltaLast]; simpa using hpos)
  exact hclasses (targetPrefixProduct_isSquare_of_common_source _ _ _ hsquareOne hsquareDelta)

end BONG.GoodBONG

end Bong
