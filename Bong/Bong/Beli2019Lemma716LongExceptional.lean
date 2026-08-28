/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716CentralComplete

/-!
# Beli (2019), Lemma 7.16: the exceptional case of condition (iv)

For a type-I replacement, the strict jump in condition (iv) can occur before
the unchanged tail only at the paper index `s - 3`.  The trigger fixes the
last two orders of the comparison prefix.  Lemma 7.5 then identifies both
prefixes as alternating endpoint towers, and the shorter one embeds in the
tower with one additional endpoint pair.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

variable [Beli2006AlphaLaws.{u, v} K]
variable [DyadicDiscriminantClassLaws K]
variable [DyadicAlternatingEndpointTowerRepresentationLaws K]

/-- A rigid endpoint tower with one additional pair represents a shorter
rigid endpoint tower.  The one-pair extension theorem is applied after adding
an arbitrary line of the common scale to the shorter tower. -/
theorem lemma716_endpointTower_onePairExtension_shortPrefixRepresents
    (b : GoodBONG q M (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (pairs : Nat) (hpairs : 0 < pairs)
    (hlargeInterior : 2 * (pairs + 1) < n + 3)
    (hsmallInterior : 2 * pairs < n + 3)
    (Plarge : Beli2019Lemma716TypeIIFailureProfile b R
      (2 * (pairs + 1)) (by omega) hlargeInterior)
    (Psmall : Beli2019Lemma716TypeIIFailureProfile c R
      (2 * pairs) (by omega) hsmallInterior) :
    DiagonalRepresents
      (c.prefixValues (2 * pairs) (Nat.le_of_lt hsmallInterior))
      (b.prefixValues (2 * (pairs + 1))
        (Nat.le_of_lt hlargeInterior)) := by
  let large : Fin (2 * (pairs + 1)) → Kˣ :=
    b.prefixValueUnits (2 * (pairs + 1))
      (Nat.le_of_lt hlargeInterior)
  let small : Fin (2 * pairs) → Kˣ :=
    c.prefixValueUnits (2 * pairs) (Nat.le_of_lt hsmallInterior)
  let extra : Kˣ := uniformizerPowerUnit K (R + 1)
  have hlargeClasses : AlternatingEndpointPairClasses large := by
    simpa only [large] using
      b.lemma716_typeIIFailureProfile_pairClasses R (pairs + 1)
        (Nat.succ_pos pairs) hlargeInterior Plarge
  have hsmallClasses : AlternatingEndpointPairClasses small := by
    simpa only [small] using
      c.lemma716_typeIIFailureProfile_pairClasses R pairs hpairs
        hsmallInterior Psmall
  have hextra : ordUnit K extra = R + 1 := by
    simpa only [extra] using ordUnit_uniformizerPowerUnit (K := K) (R + 1)
  have hlargeOrders : ∀ t : Fin (pairs + 1),
      ordUnit K (large ⟨2 * t.val, by omega⟩) = ordUnit K extra := by
    intro t
    calc
      ordUnit K (large ⟨2 * t.val, by omega⟩) = R + 1 := by
        simpa only [large] using
          b.lemma716_typeIIFailureProfile_leadingOrders R (pairs + 1)
            (Nat.succ_pos pairs) hlargeInterior Plarge t
      _ = ordUnit K extra := hextra.symm
  have hsmallOrders : ∀ t : Fin pairs,
      ordUnit K (small ⟨2 * t.val, by omega⟩) = ordUnit K extra := by
    intro t
    calc
      ordUnit K (small ⟨2 * t.val, by omega⟩) = R + 1 := by
        simpa only [small] using
          c.lemma716_typeIIFailureProfile_leadingOrders R pairs hpairs
            hsmallInterior Psmall t
      _ = ordUnit K extra := hextra.symm
  have hextended := alternatingEndpointTower_onePairExtensionRepresentation
    large small extra hlargeClasses hsmallClasses hlargeOrders hsmallOrders
  have hprefix : DiagonalRepresents
      (diagonalUnitCoefficients small)
      (diagonalUnitCoefficients (Fin.snoc small extra)) := by
    convert DiagonalRepresents.prefixOfLE
      (diagonalUnitCoefficients (Fin.snoc small extra))
      (show 2 * pairs ≤ 2 * pairs + 1 by omega) using 1
    funext i
    simp [diagonalUnitCoefficients, Fin.snoc, small]
  have hrep := hprefix.trans hextended
  have hsmallCoefficients : diagonalUnitCoefficients small =
      c.prefixValues (2 * pairs) (Nat.le_of_lt hsmallInterior) := by
    simpa only [small, diagonalUnitCoefficients_prefixValueUnits]
  have hlargeCoefficients : diagonalUnitCoefficients large =
      b.prefixValues (2 * (pairs + 1))
        (Nat.le_of_lt hlargeInterior) := by
    simpa only [large, diagonalUnitCoefficients_prefixValueUnits]
  rwa [hsmallCoefficients, hlargeCoefficients] at hrep

/-- At the exceptional type-I long index, the trigger forces the comparison
prefix of length `s - 4` to have the rigid endpoint profile of Lemma 7.5. -/
theorem lemma716_typeI_sMinusThree_longComparisonProfile
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (hsSix : 6 ≤ s)
    (htrigger : b.LongRepresentationTrigger c
      { val := s - 3
        one_lt := by omega
        succ_lt_large := by have := D.le_rank; omega
        le_small_succ := by have := D.le_rank; omega }) :
    Beli2019Lemma716TypeIIFailureProfile c R (s - 4)
      (by omega) (by have := D.le_rank; omega) := by
  let i : LongRepresentationIndex (n + 3) (n + 3) :=
    { val := s - 3
      one_lt := by omega
      succ_lt_large := by have := D.le_rank; omega
      le_small_succ := by have := D.le_rank; omega }
  have hsRank := D.le_rank
  let sourceLow : Fin (n + 3) := ⟨s - 3, by
    have := D.le_rank
    omega⟩
  let sourceHigh : Fin (n + 3) := ⟨s - 2, by
    have := D.le_rank
    omega⟩
  let comparisonLow : Fin (n + 3) := ⟨s - 5, by
    have := D.le_rank
    omega⟩
  let comparisonHigh : Fin (n + 3) := ⟨s - 6, by
    have := D.le_rank
    omega⟩
  have htrigger' : b.LongRepresentationTrigger c i := by
    simpa only [i] using htrigger
  have hsourceLow : b.order sourceLow =
      R - 2 * (ramificationIndex K : Int) + 1 := by
    have hodd : Odd sourceLow.val := by
      rcases D.even with ⟨d, hd⟩
      exact ⟨d - 2, by dsimp only [sourceLow]; omega⟩
    exact a.lemma716_typeI_prefix_order_eq_low b R s D
      hthird hvalues sourceLow (by dsimp only [sourceLow]; omega) hodd
  have hsourceHigh : b.order sourceHigh = R + 2 := by
    simpa only [sourceHigh] using
      a.lemma716_typeI_leftBoundary_order_eq b R s D hfirst hvalues
  have hlowLe : b.order sourceLow ≤ c.order comparisonLow := by
    have h := htrigger'.2.2
    have hsourceIndex : (⟨s - 3, by omega⟩ : Fin (n + 3)) =
        sourceLow := by rfl
    have hcomparisonIndex : (⟨s - 3 - 2, by omega⟩ : Fin (n + 3)) =
        comparisonLow := by
      apply Fin.ext
      dsimp only [comparisonLow]
      omega
    have h' : b.order sourceLow + 2 * (ramificationIndex K : Int) ≤
        c.order comparisonLow + 2 * (ramificationIndex K : Int) := by
      simpa only [i, hsourceIndex, hcomparisonIndex] using h
    omega
  have hlowStrict : c.order comparisonLow +
      2 * (ramificationIndex K : Int) < b.order sourceHigh := by
    have h := htrigger'.2.1
    have hsourceIndex : (⟨s - 3 + 1, by omega⟩ : Fin (n + 3)) =
        sourceHigh := by
      apply Fin.ext
      dsimp only [sourceHigh]
      omega
    have hcomparisonIndex : (⟨s - 3 - 2, by omega⟩ : Fin (n + 3)) =
        comparisonLow := by
      apply Fin.ext
      dsimp only [comparisonLow]
      omega
    simpa only [i, hsourceIndex, hcomparisonIndex] using h
  have hcomparisonLow : c.order comparisonLow =
      R - 2 * (ramificationIndex K : Int) + 1 := by
    rw [hsourceLow] at hlowLe
    rw [hsourceHigh] at hlowStrict
    omega
  let gap : Fin (n + 2) := ⟨comparisonHigh.val, by
    dsimp only [comparisonHigh]
    have := D.le_rank
    omega⟩
  have hgap : c.orderGap gap =
      c.order comparisonLow - c.order comparisonHigh := by
    unfold orderGap
    have hcast : gap.castSucc = comparisonHigh := by
      apply Fin.ext
      rfl
    have hsucc : gap.succ = comparisonLow := by
      apply Fin.ext
      change (s - 6) + 1 = s - 5
      omega
    rw [hcast, hsucc]
  have hgapLower := c.orderGap_ge_neg_two_mul_e gap
  rw [hgap] at hgapLower
  have hcomparisonHighUpper : c.order comparisonHigh ≤ R + 1 := by
    rw [hcomparisonLow] at hgapLower
    omega
  have hcomparisonHighEven : Even comparisonHigh.val := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 3, by dsimp only [comparisonHigh]; omega⟩
  have hcomparisonHighLower : R + 1 ≤ c.order comparisonHigh :=
    a.lemma716_comparison_even_order_ge c R hfirst hnorm comparisonHigh
      hcomparisonHighEven
  have hcomparisonHigh : c.order comparisonHigh = R + 1 := by omega
  have hzeroLower : R + 1 ≤ c.order 0 :=
    a.lemma716_comparison_order_zero_ge c R hfirst hnorm
  have hzeroHigh : c.order 0 ≤ c.order comparisonHigh := by
    apply lemma716_order_le_of_evenGap c 0 comparisonHigh (Fin.zero_le _)
    simpa only [Fin.val_zero, Nat.sub_zero] using hcomparisonHighEven
  have hzero : c.order 0 = R + 1 := by omega
  refine {
    first := hzero
    high := ?_
    low := ?_ }
  · have hindex : (⟨(s - 4) - 2, by
          have := D.le_rank
          omega⟩ : Fin (n + 3)) = comparisonHigh := by
      apply Fin.ext
      dsimp only [comparisonHigh]
      omega
    simpa only [hindex] using hcomparisonHigh
  · have hindex : (⟨(s - 4) - 1, by
          have := D.le_rank
          omega⟩ : Fin (n + 3)) = comparisonLow := by
      apply Fin.ext
      dsimp only [comparisonLow]
      omega
    simpa only [hindex] using hcomparisonLow

/-- Condition (iv) at the unique exceptional type-I index `s - 3`. -/
theorem lemma716_typeI_sMinusThree_longRepresentationAt
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (hsSix : 6 ≤ s)
    (htrigger : b.LongRepresentationTrigger c
      { val := s - 3
        one_lt := by omega
        succ_lt_large := by have := D.le_rank; omega
        le_small_succ := by have := D.le_rank; omega }) :
    DiagonalRepresents
      (c.prefixValues (s - 4) (by have := D.le_rank; omega))
      (b.prefixValues (s - 2) (by have := D.le_rank; omega)) := by
  rcases D.even with ⟨d, hd⟩
  let pairs := d - 2
  have hsmallLength : 2 * pairs = s - 4 := by
    dsimp only [pairs]
    omega
  have hlargeLength : 2 * (pairs + 1) = s - 2 := by
    dsimp only [pairs]
    omega
  have hpairs : 0 < pairs := by
    dsimp only [pairs]
    omega
  have hsmallInterior : 2 * pairs < n + 3 := by
    rw [hsmallLength]
    have := D.le_rank
    omega
  have hlargeInterior : 2 * (pairs + 1) < n + 3 := by
    rw [hlargeLength]
    have := D.le_rank
    omega
  have PlargeRaw := a.lemma716_typeI_sMinusTwo_sourceProfile b R s D
    hthird hvalues (by omega)
  have Plarge : Beli2019Lemma716TypeIIFailureProfile b R
      (2 * (pairs + 1)) (by omega) hlargeInterior := by
    simpa only [hlargeLength] using PlargeRaw
  have PsmallRaw := a.lemma716_typeI_sMinusThree_longComparisonProfile
    b c R s D hfirst hthird hnorm hvalues hsSix htrigger
  have Psmall : Beli2019Lemma716TypeIIFailureProfile c R
      (2 * pairs) (by omega) hsmallInterior := by
    simpa only [hsmallLength] using PsmallRaw
  have hrep := b.lemma716_endpointTower_onePairExtension_shortPrefixRepresents
    c R pairs hpairs hlargeInterior hsmallInterior Plarge Psmall
  exact prefixRepresents_cast c b hsmallLength hlargeLength hrep

end BONG.GoodBONG

end Bong
