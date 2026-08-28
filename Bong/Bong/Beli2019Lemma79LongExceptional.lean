/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79LongGap

/-!
# Beli (2019), Lemma 7.9(iv): the exceptional type-I long branch

The endpoint-tower machinery used earlier for Lemma 7.16 was stated for a
rank written as `n + 3`.  Lemma 7.9 naturally carries rank `n + 2`, so this
file records the same rigid profile at that rank and proves the corresponding
one-pair extension theorem without reindexing the ambient good BONGs.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- A rigid alternating endpoint prefix at the ambient rank of Lemma 7.9. -/
structure Beli2019Lemma79EndpointTowerProfile
    (x : GoodBONG q N (n + 2)) (R : Int) (s : Nat)
    (hsTwo : 2 ≤ s) (hsInterior : s < n + 2) : Prop where
  first : x.order 0 = R + 1
  high : x.order ⟨s - 2, by omega⟩ = R + 1
  low : x.order ⟨s - 1, by omega⟩ =
    R - 2 * (ramificationIndex K : Int) + 1

/-- Lemma 7.5 arithmetic for the rank-`n + 2` endpoint profile. -/
theorem lemma79_endpointTowerProfile_arithmetic
    [Beli2006AlphaLaws.{u, v} K]
    (x : GoodBONG q N (n + 2)) (R : Int) (pairs : Nat)
    (hpairs : 0 < pairs) (hInterior : 2 * pairs < n + 2)
    (P : Beli2019Lemma79EndpointTowerProfile x R (2 * pairs)
      (by omega) hInterior) :
    Lemma75ArithmeticConsequences x
      (⟨0, by omega⟩ : Fin (n + 1))
      (⟨2 * pairs - 2, by omega⟩ : Fin (n + 1)) (R + 1) := by
  let first : Fin (n + 1) := ⟨0, by omega⟩
  let last : Fin (n + 1) := ⟨2 * pairs - 2, by omega⟩
  have hfirstLast : first ≤ last := Fin.zero_le last
  have hsegmentEven : Even (last.val - first.val) := by
    exact ⟨pairs - 1, by dsimp only [first, last]; omega⟩
  have hfirstOrder : x.order first.castSucc = R + 1 := by
    have hindex : first.castSucc = (0 : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact P.first
  have hterminal : x.order last.succ =
      (R + 1) - 2 * (ramificationIndex K : Int) := by
    have hindex : last.succ =
        (⟨2 * pairs - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      simp only [last, Fin.val_succ]
      omega
    rw [hindex]
    have hlow := P.low
    have hlowIndex :
        (⟨(2 * pairs) - 1, by omega⟩ : Fin (n + 2)) =
          ⟨2 * pairs - 1, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [← hlowIndex, hlow]
    ring
  simpa only [first, last] using
    x.beli2019Lemma75_arithmetic first last (R + 1) hfirstLast
      hsegmentEven hfirstOrder hterminal

/-- Every adjacent pair in a rank-`n + 2` endpoint tower has one of the two
unramified endpoint classes. -/
theorem lemma79_endpointTowerProfile_pairClasses
    [Beli2006AlphaLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    (x : GoodBONG q N (n + 2)) (R : Int) (pairs : Nat)
    (hpairs : 0 < pairs) (hInterior : 2 * pairs < n + 2)
    (P : Beli2019Lemma79EndpointTowerProfile x R (2 * pairs)
      (by omega) hInterior) :
    AlternatingEndpointPairClasses
      (x.prefixValueUnits (2 * pairs) (Nat.le_of_lt hInterior)) := by
  let first : Fin (n + 1) := ⟨0, by omega⟩
  let last : Fin (n + 1) := ⟨2 * pairs - 2, by omega⟩
  have A := x.lemma79_endpointTowerProfile_arithmetic
    R pairs hpairs hInterior P
  intro t
  let k : Fin (n + 1) := ⟨2 * t.val, by omega⟩
  have hfirstLast : first ≤ last := Fin.zero_le last
  have hsegmentEven : Even (last.val - first.val) := by
    exact ⟨pairs - 1, by dsimp only [first, last]; omega⟩
  have hfirstOrder : x.order first.castSucc = R + 1 := by
    have hindex : first.castSucc = (0 : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact P.first
  have hterminal : x.order last.succ =
      (R + 1) - 2 * (ramificationIndex K : Int) := by
    have hindex : last.succ =
        (⟨2 * pairs - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      simp only [last, Fin.val_succ]
      omega
    rw [hindex]
    have hlow : x.order (⟨2 * pairs - 1, by omega⟩ : Fin (n + 2)) =
        R - 2 * (ramificationIndex K : Int) + 1 := by
      simpa only using P.low
    rw [hlow]
    ring
  have hfirstK : first ≤ k := Fin.zero_le k
  have hkLast : k ≤ last :=
    Fin.mk_le_mk.mpr (by omega)
  have hkEven : Even (k.val - first.val) := by
    exact ⟨t.val, by dsimp only [k, first]; omega⟩
  have hclasses := x.beli2019Lemma75_pairBlock_endpointClass
    first last k (R + 1) hfirstLast hsegmentEven hfirstOrder hterminal
      hfirstK hkLast hkEven
  have hpair := x.toBONG.adjacentSignedProduct_endpoint_cases
    k.castSucc (Nat.succ_lt_succ k.isLt) hclasses
  simpa only [prefixValueUnits, GoodBONG.valueUnit, k, Fin.castSucc_mk]
    using hpair

/-- All leading entries of the rank-`n + 2` endpoint tower have order
`R + 1`. -/
theorem lemma79_endpointTowerProfile_leadingOrders
    [Beli2006AlphaLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    (x : GoodBONG q N (n + 2)) (R : Int) (pairs : Nat)
    (hpairs : 0 < pairs) (hInterior : 2 * pairs < n + 2)
    (P : Beli2019Lemma79EndpointTowerProfile x R (2 * pairs)
      (by omega) hInterior) :
    ∀ t : Fin pairs,
      ordUnit K ((x.prefixValueUnits (2 * pairs)
        (Nat.le_of_lt hInterior)) ⟨2 * t.val, by omega⟩) = R + 1 := by
  let first : Fin (n + 1) := ⟨0, by omega⟩
  let last : Fin (n + 1) := ⟨2 * pairs - 2, by omega⟩
  have A := x.lemma79_endpointTowerProfile_arithmetic
    R pairs hpairs hInterior P
  intro t
  let k : Fin (n + 1) := ⟨2 * t.val, by omega⟩
  have hkOrder := A.even_order k (Fin.zero_le k)
    (Fin.mk_le_mk.mpr (by omega))
    ⟨t.val, by dsimp only [k, first]; omega⟩
  calc
    ordUnit K ((x.prefixValueUnits (2 * pairs)
        (Nat.le_of_lt hInterior)) ⟨2 * t.val, by omega⟩) =
        x.order k.castSucc := by
      simpa only [prefixValueUnits, k, GoodBONG.valueUnit,
        Fin.castSucc_mk, GoodBONG.order] using
          (x.toBONG.order_eq_ordUnit k.castSucc).symm
    _ = R + 1 := hkOrder

/-- A rank-`n + 2` endpoint tower with one additional pair represents the
shorter tower. -/
theorem lemma79_endpointTower_onePairExtension_shortPrefixRepresents
    [Beli2006AlphaLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (R : Int) (pairs : Nat) (hpairs : 0 < pairs)
    (hlargeInterior : 2 * (pairs + 1) < n + 2)
    (hsmallInterior : 2 * pairs < n + 2)
    (Plarge : Beli2019Lemma79EndpointTowerProfile b R
      (2 * (pairs + 1)) (by omega) hlargeInterior)
    (Psmall : Beli2019Lemma79EndpointTowerProfile c R
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
      b.lemma79_endpointTowerProfile_pairClasses R (pairs + 1)
        (Nat.succ_pos pairs) hlargeInterior Plarge
  have hsmallClasses : AlternatingEndpointPairClasses small := by
    simpa only [small] using
      c.lemma79_endpointTowerProfile_pairClasses R pairs hpairs
        hsmallInterior Psmall
  have hextra : ordUnit K extra = R + 1 := by
    simpa only [extra] using ordUnit_uniformizerPowerUnit (K := K) (R + 1)
  have hlargeOrders : ∀ t : Fin (pairs + 1),
      ordUnit K (large ⟨2 * t.val, by omega⟩) = ordUnit K extra := by
    intro t
    calc
      ordUnit K (large ⟨2 * t.val, by omega⟩) = R + 1 := by
        simpa only [large] using
          b.lemma79_endpointTowerProfile_leadingOrders R (pairs + 1)
            (Nat.succ_pos pairs) hlargeInterior Plarge t
      _ = ordUnit K extra := hextra.symm
  have hsmallOrders : ∀ t : Fin pairs,
      ordUnit K (small ⟨2 * t.val, by omega⟩) = ordUnit K extra := by
    intro t
    calc
      ordUnit K (small ⟨2 * t.val, by omega⟩) = R + 1 := by
        simpa only [small] using
          c.lemma79_endpointTowerProfile_leadingOrders R pairs hpairs
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

/-- The unique large-gap type-I branch of Lemma 7.9(iv).  The canonical
switch identifies the source prefix as an endpoint tower with one more pair
than the comparison prefix.  The long trigger determines the two missing
comparison endpoint orders, and the strict norm inequality determines its
first order. -/
theorem lemma79_typeI_exceptional_longRepresentation
    [Beli2006AlphaLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (i : LongRepresentationIndex (n + 2) (n + 2))
    (hswitch : i.val + 1 = C.leftSwitch)
    (hgap : b.orderGap
      ⟨i.val, by have := i.succ_lt_large; omega⟩ =
        2 * (ramificationIndex K : Int) + 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (htrigger : b.LongRepresentationTrigger c i) :
    DiagonalRepresents
      (c.prefixValues (i.val - 1) (by
        have := i.succ_lt_large
        omega))
      (b.prefixValues (i.val + 1) (by
        have := i.succ_lt_large
        omega)) := by
  rcases C.left_even with ⟨d, hd⟩
  let pairs := d - 1
  have hpairs : 0 < pairs := by
    dsimp only [pairs]
    have hiTwo := i.one_lt
    omega
  have hsmallLength : 2 * pairs = i.val - 1 := by
    dsimp only [pairs]
    omega
  have hlargeLength : 2 * (pairs + 1) = i.val + 1 := by
    dsimp only [pairs]
    omega
  have hsmallInterior : 2 * pairs < n + 2 := by
    rw [hsmallLength]
    have := i.succ_lt_large
    omega
  have hlargeInterior : 2 * (pairs + 1) < n + 2 := by
    rw [hlargeLength]
    exact i.succ_lt_large
  let R : Int := a.orderSequence.entryOrZero D.anchor
  have hleftPos : 0 < C.leftSwitch := by omega
  have haZeroEntry := C.source_to_anchor 0 (Nat.zero_le D.anchor)
    ⟨0, by omega⟩
  have haZero : a.order 0 = R := by
    calc
      a.order (0 : Fin (n + 2)) =
          a.orderSequence.entryOrZero (0 : Nat) := by
        simpa using
          (a.orderSequence_entryOrZero_eq_order
            (0 : Fin (n + 2))).symm
      _ = R := by simpa only [R] using haZeroEntry
  have hbZeroEntry := C.target_before_left 0 hleftPos ⟨0, by omega⟩
  have hbZero : b.order 0 = R + 1 := by
    calc
      b.order (0 : Fin (n + 2)) =
          b.orderSequence.entryOrZero (0 : Nat) := by
        simpa using
          (b.orderSequence_entryOrZero_eq_order
            (0 : Fin (n + 2))).symm
      _ = R + 1 := by simpa only [R] using hbZeroEntry
  have hiPreviousEven : Even (i.val - 1) :=
    ⟨d - 1, by omega⟩
  have hbHighEntry := C.target_before_left (i.val - 1)
    (by omega) hiPreviousEven
  have hbHigh : b.order ⟨i.val - 1, by
      have := i.succ_lt_large
      omega⟩ = R + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order]
    simpa only [R] using hbHighEntry
  have hiNextEven : Even (i.val + 1) := ⟨d, by omega⟩
  have hbNextEntry := C.target_from_left (i.val + 1)
    (by omega) (by rw [hswitch]; exact C.left_le_anchor) hiNextEven
  have hbNext : b.order ⟨i.val + 1, i.succ_lt_large⟩ = R + 2 := by
    rw [← b.orderSequence_entryOrZero_eq_order]
    simpa only [R] using hbNextEntry
  have hgap' := hgap
  change b.order ⟨i.val + 1, i.succ_lt_large⟩ -
      b.order ⟨i.val, by have := i.succ_lt_large; omega⟩ =
        2 * (ramificationIndex K : Int) + 1 at hgap'
  have hbLow : b.order ⟨i.val, by
      have := i.succ_lt_large
      omega⟩ = R - 2 * (ramificationIndex K : Int) + 1 := by
    rw [hbNext] at hgap'
    omega
  have PlargeRaw : Beli2019Lemma79EndpointTowerProfile b R
      (i.val + 1) (by have := i.one_lt; omega) i.succ_lt_large := by
    refine {
      first := hbZero
      high := ?_
      low := ?_ }
    · have hindex : (⟨(i.val + 1) - 2, by
            have := i.succ_lt_large
            omega⟩ : Fin (n + 2)) =
          ⟨i.val - 1, by have := i.succ_lt_large; omega⟩ := by
        apply Fin.ext
        change (i.val + 1) - 2 = i.val - 1
        omega
      simpa only [hindex] using hbHigh
    · have hindex : (⟨(i.val + 1) - 1, by
            have := i.succ_lt_large
            omega⟩ : Fin (n + 2)) =
          ⟨i.val, by have := i.succ_lt_large; omega⟩ := by
        apply Fin.ext
        change (i.val + 1) - 1 = i.val
        omega
      simpa only [hindex] using hbLow
  have Plarge : Beli2019Lemma79EndpointTowerProfile b R
      (2 * (pairs + 1)) (by omega) hlargeInterior := by
    simpa only [hlargeLength] using PlargeRaw
  let comparisonHigh : Fin (n + 2) := ⟨i.val - 3, by
    have := i.succ_lt_large
    omega⟩
  let comparisonLow : Fin (n + 2) := ⟨i.val - 2, by
    have := i.succ_lt_large
    omega⟩
  have hlowLe : b.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩ ≤ c.order comparisonLow := by
    have h := htrigger.2.2
    change b.order ⟨i.val, by have := i.succ_lt_large; omega⟩ +
        2 * (ramificationIndex K : Int) ≤
      c.order comparisonLow + 2 * (ramificationIndex K : Int) at h
    omega
  have hlowStrict : c.order comparisonLow +
      2 * (ramificationIndex K : Int) <
        b.order ⟨i.val + 1, i.succ_lt_large⟩ := by
    have h := htrigger.2.1
    change c.order comparisonLow + 2 * (ramificationIndex K : Int) <
      b.order ⟨i.val + 1, i.succ_lt_large⟩ at h
    exact h
  have hcLow : c.order comparisonLow =
      R - 2 * (ramificationIndex K : Int) + 1 := by
    rw [hbLow] at hlowLe
    rw [hbNext] at hlowStrict
    omega
  have hnormOrder :=
    a.toBONG.order_zero_add_one_le_of_normIdeal_lt c.toBONG hnorm
  change a.order 0 + 1 ≤ c.order 0 at hnormOrder
  have hcZeroLower : R + 1 ≤ c.order 0 := by
    rw [haZero] at hnormOrder
    exact hnormOrder
  have hcomparisonHighEven : Even comparisonHigh.val := by
    exact ⟨d - 2, by dsimp only [comparisonHigh]; omega⟩
  have hcHighMonotoneRaw := c.orderSequence.entryOrZero_le_of_evenGap
    0 comparisonHigh.val (Nat.zero_le _) comparisonHigh.isLt
      hcomparisonHighEven
  have hcHighMonotone : c.order 0 ≤ c.order comparisonHigh := by
    rw [← c.orderSequence_entryOrZero_eq_order (0 : Fin (n + 2)),
      ← c.orderSequence_entryOrZero_eq_order comparisonHigh]
    exact hcHighMonotoneRaw
  let gapIndex : Fin (n + 1) := ⟨comparisonHigh.val, by
    dsimp only [comparisonHigh]
    have := i.succ_lt_large
    omega⟩
  have hgapFormula : c.orderGap gapIndex =
      c.order comparisonLow - c.order comparisonHigh := by
    unfold orderGap
    have hcast : gapIndex.castSucc = comparisonHigh := by
      apply Fin.ext
      rfl
    have hsucc : gapIndex.succ = comparisonLow := by
      apply Fin.ext
      change (i.val - 3) + 1 = i.val - 2
      have hiTwo := i.one_lt
      omega
    rw [hcast, hsucc]
  have hgapLower := c.orderGap_ge_neg_two_mul_e gapIndex
  rw [hgapFormula, hcLow] at hgapLower
  have hcHighUpper : c.order comparisonHigh ≤ R + 1 := by omega
  have hcHigh : c.order comparisonHigh = R + 1 := by omega
  have hcZero : c.order 0 = R + 1 := by omega
  have PsmallRaw : Beli2019Lemma79EndpointTowerProfile c R
      (i.val - 1) (by omega) (by
        have := i.succ_lt_large
        omega) := by
    refine {
      first := hcZero
      high := ?_
      low := ?_ }
    · have hindex : (⟨(i.val - 1) - 2, by
            have := i.succ_lt_large
            omega⟩ : Fin (n + 2)) = comparisonHigh := by
        apply Fin.ext
        dsimp only [comparisonHigh]
        omega
      simpa only [hindex] using hcHigh
    · have hindex : (⟨(i.val - 1) - 1, by
            have := i.succ_lt_large
            omega⟩ : Fin (n + 2)) = comparisonLow := by
        apply Fin.ext
        dsimp only [comparisonLow]
        omega
      simpa only [hindex] using hcLow
  have Psmall : Beli2019Lemma79EndpointTowerProfile c R
      (2 * pairs) (by omega) hsmallInterior := by
    simpa only [hsmallLength] using PsmallRaw
  have hrep := b.lemma79_endpointTower_onePairExtension_shortPrefixRepresents
    c R pairs hpairs hlargeInterior hsmallInterior Plarge Psmall
  exact prefixRepresents_cast c b hsmallLength hlargeLength hrep

/-- Pointwise condition (iv) in Lemma 7.9.  A long trigger itself forces a
target gap larger than `2e`; the large-gap dichotomy then sends the index to
either the common suffix or the unique type-I endpoint-tower branch. -/
theorem Lemma79NormalizedClassification.longRepresentationAt
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    (D : Lemma79NormalizedClassification a b)
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : LongRepresentationIndex (n + 2) (n + 2))
    (htrigger : b.LongRepresentationTrigger c i) :
    DiagonalRepresents
      (c.prefixValues (i.val - 1) i.previous_le_sameRank)
      (b.prefixValues (i.val + 1) i.next_le_sameRank) := by
  have hstrict : b.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩ + 2 * (ramificationIndex K : Int) <
      b.order ⟨i.val + 1, i.succ_lt_large⟩ :=
    htrigger.2.2.trans_lt htrigger.2.1
  have hlarge : 2 * (ramificationIndex K : Int) <
      b.orderGap ⟨i.val, by have := i.succ_lt_large; omega⟩ := by
    change 2 * (ramificationIndex K : Int) <
      b.order ⟨i.val + 1, i.succ_lt_large⟩ -
        b.order ⟨i.val, by have := i.succ_lt_large; omega⟩
    omega
  rcases D.longGap_alternative hab.orderCondition hab.defectCondition
      htotal i hlarge with htail | ⟨E, C, _hfirst, hswitch, hgap⟩
  · apply D.longRepresentation_of_commonSuffix hab hac i htail
    simpa only [LongRepresentationTrigger,
      dif_pos (show i.val ≤ n + 2 by
        have := i.succ_lt_large
        omega)] using htrigger
  · exact lemma79_typeI_exceptional_longRepresentation
      a b c E C i hswitch hgap hnorm htrigger

/-- Lemma 7.9(iv), assembled for every long index. -/
theorem Lemma79NormalizedClassification.longRepresentationConditions
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    (D : Lemma79NormalizedClassification a b)
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2)) :
    b.LongRepresentationConditions c := by
  rw [b.longRepresentationConditions_iff_forall_trigger c]
  intro i htrigger
  exact D.longRepresentationAt hab hac hnorm htotal i htrigger

end BONG.GoodBONG

end Bong
