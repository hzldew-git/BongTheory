/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716TypeISMinusOneCentral
import Bong.Bong.Beli2019Lemma93TailCentral

/-!
# Beli (2019), Lemma 7.16(iii'): the type-I boundary `i = s - 2`

The first trigger inequality fixes the comparison coefficient at paper index
`s - 3` at order `R + 1`.  Lemmas 2.16 and 2.13 show that the boundary is
essential.  When `s > 4`, its second essential inequality and the negative-gap
parity law give the rigid endpoint profile on the preceding length-`s - 4`
comparison prefix.  Lemma 7.5 then reduces the required representation to the
paper-independent one-pair extension theorem for endpoint towers.  The same
theorem includes the zero-tower case `s = 4`.
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
variable [Beli2009AlphaParityLaws.{u, v} K]
variable [DyadicDiscriminantClassLaws K]
variable [DyadicAlternatingEndpointTowerRepresentationLaws K]

/-- The first inequality in condition (iii') at `i = s - 2` fixes the
comparison coefficient at zero-based index `s - 4`. -/
theorem lemma716_typeI_sMinusTwo_comparisonExtra_order_eq_of_cross
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (hsFour : 4 ≤ s)
    (hcross : c.order ⟨s - 4, by
        have := D.le_rank
        omega⟩ <
      b.order ⟨s - 2, by
        have := D.le_rank
        omega⟩) :
    c.order ⟨s - 4, by
      have := D.le_rank
      omega⟩ = R + 1 := by
  let extra : Fin (n + 3) := ⟨s - 4, by
    have := D.le_rank
    omega⟩
  let target : Fin (n + 3) := ⟨s - 2, by
    have := D.le_rank
    omega⟩
  have hextraEven : Even extra.val := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 2, by dsimp only [extra]; omega⟩
  have hextraLower : R + 1 ≤ c.order extra :=
    a.lemma716_comparison_even_order_ge c R hfirst hnorm extra hextraEven
  have htarget : b.order target = R + 2 := by
    simpa only [target] using
      a.lemma716_typeI_leftBoundary_order_eq b R s D hfirst hvalues
  have hcross' : c.order extra < b.order target := by
    simpa only [extra, target] using hcross
  rw [htarget] at hcross'
  have : c.order extra = R + 1 := by omega
  simpa only [extra] using this

/-- For `s > 4`, essentiality gives the rigid endpoint profile on the
comparison prefix of length `s - 4`. -/
theorem lemma716_typeI_sMinusTwo_comparisonSmallProfile_of_essential
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (hsSix : 6 ≤ s)
    (hextra : c.order ⟨s - 4, by
        have := D.le_rank
        omega⟩ = R + 1)
    (hessential : b.IsEssentialFor c ⟨s - 3, by
      have := D.le_rank
      omega⟩) :
    Beli2019Lemma716TypeIIFailureProfile c R (s - 4)
      (by omega) (by have := D.le_rank; omega) := by
  let boundary : Fin (n + 3) := ⟨s - 3, by
    have := D.le_rank
    omega⟩
  let high : Fin (n + 3) := ⟨boundary.val - 3, by omega⟩
  let low : Fin (n + 3) := ⟨boundary.val - 2, by omega⟩
  let extra : Fin (n + 3) := ⟨boundary.val - 1, by omega⟩
  let sourceLeft : Fin (n + 3) := ⟨boundary.val + 1, by
    dsimp only [boundary]
    have := D.le_rank
    omega⟩
  let sourceRight : Fin (n + 3) := ⟨boundary.val + 2, by
    dsimp only [boundary]
    have := D.le_rank
    omega⟩
  have hessential' : b.IsEssentialFor c boundary := by
    simpa only [boundary] using hessential
  unfold IsEssentialFor BeliOrderSequence.IsEssentialFor at hessential'
  have hsumRaw := hessential'.2 (by
      dsimp only [boundary]
      omega) (by
      dsimp only [boundary]
      have := D.le_rank
      omega)
  have hsum : c.order low + c.order extra <
      b.order sourceLeft + b.order sourceRight := by
    simpa only [orderSequence_at, low, extra, sourceLeft, sourceRight]
      using hsumRaw
  have hsourceLeft : b.order sourceLeft = R + 2 := by
    have hindex : sourceLeft = ⟨s - 2, by
        have := D.le_rank
        omega⟩ := by
      apply Fin.ext
      dsimp only [sourceLeft, boundary]
      omega
    rw [hindex]
    exact a.lemma716_typeI_leftBoundary_order_eq b R s D hfirst hvalues
  have hsourceRight : b.order sourceRight =
      R - 2 * (ramificationIndex K : Int) + 2 := by
    have hindex : sourceRight = ⟨s - 1, by
        have := D.le_rank
        omega⟩ := by
      apply Fin.ext
      dsimp only [sourceRight, boundary]
      omega
    rw [hindex]
    exact a.lemma716_typeI_rightBoundary_order_eq b R s D hsecond hvalues
  have hextra' : c.order extra = R + 1 := by
    have hindex : extra = ⟨s - 4, by
        have := D.le_rank
        omega⟩ := by
      apply Fin.ext
      dsimp only [extra, boundary]
      omega
    rw [hindex]
    exact hextra
  have hsumNumeric : c.order low + (R + 1) <
      (R + 2) + (R - 2 * (ramificationIndex K : Int) + 2) := by
    rw [← hextra', ← hsourceLeft, ← hsourceRight]
    exact hsum
  have hhighEven : Even high.val := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 3, by dsimp only [high, boundary]; omega⟩
  have hlowOdd : Odd low.val := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 3, by dsimp only [low, boundary]; omega⟩
  have hhighLower : R + 1 ≤ c.order high :=
    a.lemma716_comparison_even_order_ge c R hfirst hnorm high hhighEven
  have hhighExtraEven : Even (extra.val - high.val) := by
    exact ⟨1, by dsimp only [extra, high, boundary]; omega⟩
  have hhighExtra : c.order high ≤ c.order extra :=
    lemma716_order_le_of_evenGap c high extra (by
      dsimp only [high, extra, boundary]
      omega) hhighExtraEven
  have hhighEq : c.order high = R + 1 := by omega
  have hlowLower : R - 2 * (ramificationIndex K : Int) + 1 ≤
      c.order low :=
    a.lemma716_comparison_odd_order_ge c R hfirst hnorm low hlowOdd
  let gap : Fin (n + 2) := ⟨high.val, by
    dsimp only [high, boundary]
    have := D.le_rank
    omega⟩
  have hgapDef : c.orderGap gap = c.order low - c.order high := by
    unfold orderGap
    have hcast : gap.castSucc = high := by
      apply Fin.ext
      rfl
    have hsucc : gap.succ = low := by
      apply Fin.ext
      simp only [gap, high, low, boundary, Fin.val_succ]
      omega
    rw [hcast, hsucc]
  have hgapLower := c.orderGap_ge_neg_two_mul_e gap
  rw [hgapDef] at hgapLower
  have hgapNegative : c.orderGap gap < 0 := by
    rw [hgapDef, hhighEq]
    have he := ramificationIndex_pos (K := K)
    omega
  have hgapEven := c.orderGap_even_of_negative gap hgapNegative
  rw [hgapDef] at hgapEven
  rcases hgapEven with ⟨z, hz⟩
  have hgapUpper : c.order low - c.order high <
      2 - 2 * (ramificationIndex K : Int) := by
    rw [hhighEq]
    linarith [hsumNumeric]
  have hgapAsTwice : c.order low - c.order high = z + z := by
    exact hz
  have hgapLowerZ : -(2 * (ramificationIndex K : Int)) ≤ z + z := by
    calc
      -(2 * (ramificationIndex K : Int)) ≤
          c.order low - c.order high := hgapLower
      _ = z + z := hgapAsTwice
  have hgapUpperZ : z + z <
      2 - 2 * (ramificationIndex K : Int) := by
    calc
      z + z = c.order low - c.order high := hgapAsTwice.symm
      _ < 2 - 2 * (ramificationIndex K : Int) := hgapUpper
  have hzEq : z = -(ramificationIndex K : Int) := by
    omega
  have hgapEq : c.order low - c.order high =
      -(2 * (ramificationIndex K : Int)) := by
    calc
      c.order low - c.order high = z + z := hgapAsTwice
      _ = -(2 * (ramificationIndex K : Int)) := by
        rw [hzEq]
        ring
  have hlowEq : c.order low =
      R - 2 * (ramificationIndex K : Int) + 1 := by
    omega
  let zero : Fin (n + 3) := 0
  have hzeroLower : R + 1 ≤ c.order zero := by
    simpa only [zero] using
      a.lemma716_comparison_order_zero_ge c R hfirst hnorm
  have hzeroHigh : c.order zero ≤ c.order high := by
    apply lemma716_order_le_of_evenGap c zero high
    · exact Fin.zero_le high
    · simpa only [zero, Fin.val_zero, Nat.sub_zero] using hhighEven
  have hzeroEq : c.order zero = R + 1 := by omega
  refine {
    first := by simpa only [zero] using hzeroEq
    high := ?_
    low := ?_ }
  · have hindex : (⟨(s - 4) - 2, by
        have := D.le_rank
        omega⟩ : Fin (n + 3)) = high := by
      apply Fin.ext
      dsimp only [high, boundary]
      omega
    simpa only [hindex] using hhighEq
  · have hindex : (⟨(s - 4) - 1, by
        have := D.le_rank
        omega⟩ : Fin (n + 3)) = low := by
      apply Fin.ext
      dsimp only [low, boundary]
      omega
    simpa only [hindex] using hlowEq

/-- A rigid endpoint tower with one additional pair represents a rigid
shorter tower followed by one line at the common scale. -/
theorem lemma716_endpointTower_onePairExtension_prefixRepresents
    (b : GoodBONG q M (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (pairs : Nat)
    (hlargeInterior : 2 * (pairs + 1) < n + 3)
    (Plarge : Beli2019Lemma716TypeIIFailureProfile b R
      (2 * (pairs + 1)) (by omega) hlargeInterior)
    (hsmallClasses : AlternatingEndpointPairClasses
      (c.prefixValueUnits (2 * pairs) (by omega)))
    (hsmallOrders : ∀ t : Fin pairs,
      ordUnit K ((c.prefixValueUnits (2 * pairs) (by omega))
        ⟨2 * t.val, by omega⟩) = R + 1)
    (hextraOrder : c.order ⟨2 * pairs, by omega⟩ = R + 1) :
    DiagonalRepresents
      (c.prefixValues (2 * pairs + 1) (by omega))
      (b.prefixValues (2 * (pairs + 1)) (Nat.le_of_lt hlargeInterior)) := by
  let large : Fin (2 * (pairs + 1)) → Kˣ :=
    b.prefixValueUnits (2 * (pairs + 1)) (Nat.le_of_lt hlargeInterior)
  let small : Fin (2 * pairs) → Kˣ :=
    c.prefixValueUnits (2 * pairs) (by omega)
  let extraIndex : Fin (n + 3) := ⟨2 * pairs, by omega⟩
  let extra : Kˣ := c.valueUnit extraIndex
  have hlargeClasses : AlternatingEndpointPairClasses large := by
    simpa only [large] using
      b.lemma716_typeIIFailureProfile_pairClasses R (pairs + 1)
        (Nat.succ_pos pairs) hlargeInterior Plarge
  have hextra : ordUnit K extra = R + 1 := by
    calc
      ordUnit K extra = c.order extraIndex := by
        exact (c.toBONG.order_eq_ordUnit extraIndex).symm
      _ = R + 1 := by simpa only [extraIndex] using hextraOrder
  have hlargeOrders : ∀ t : Fin (pairs + 1),
      ordUnit K (large ⟨2 * t.val, by omega⟩) = ordUnit K extra := by
    intro t
    calc
      ordUnit K (large ⟨2 * t.val, by omega⟩) = R + 1 := by
        simpa only [large] using
          b.lemma716_typeIIFailureProfile_leadingOrders R (pairs + 1)
            (Nat.succ_pos pairs) hlargeInterior Plarge t
      _ = ordUnit K extra := hextra.symm
  have hsmallOrders' : ∀ t : Fin pairs,
      ordUnit K (small ⟨2 * t.val, by omega⟩) = ordUnit K extra := by
    intro t
    calc
      ordUnit K (small ⟨2 * t.val, by omega⟩) = R + 1 := by
        simpa only [small] using hsmallOrders t
      _ = ordUnit K extra := hextra.symm
  have hrep := alternatingEndpointTower_onePairExtensionRepresentation
    large small extra hlargeClasses (by simpa only [small] using hsmallClasses)
      hlargeOrders hsmallOrders'
  have hsmallCoefficients :
      diagonalUnitCoefficients (Fin.snoc small extra) =
        c.prefixValues (2 * pairs + 1) (by omega) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [small, extra, extraIndex, diagonalUnitCoefficients,
        prefixValues, prefixValueUnits, GoodBONG.valueUnit, GoodBONG.value]
    · simp [small, diagonalUnitCoefficients, prefixValues,
        prefixValueUnits, GoodBONG.valueUnit, GoodBONG.value]
  have hlargeCoefficients : diagonalUnitCoefficients large =
      b.prefixValues (2 * (pairs + 1))
        (Nat.le_of_lt hlargeInterior) := by
    simpa only [large, diagonalUnitCoefficients_prefixValueUnits]
  rwa [hsmallCoefficients, hlargeCoefficients] at hrep

/-- Condition (iii') at the type-I boundary with paper index `s - 2`. -/
theorem lemma716_typeI_sMinusTwo_centralRepresentationAt
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (horder : b.RepresentationOrderCondition c le_rfl)
    (hdefect : b.RepresentationDefectCondition c)
    (hsFour : 4 ≤ s)
    (htrigger : b.centralDefectTrigger c
      { val := s - 2
        one_lt := by omega
        lt_large := by have := D.le_rank; omega
        le_small_succ := by have := D.le_rank; omega }) :
    DiagonalRepresents
      (c.prefixValues (s - 3) (by have := D.le_rank; omega))
      (b.prefixValues (s - 2) (by have := D.le_rank; omega)) := by
  let i : CentralRepresentationIndex (n + 3) (n + 3) :=
    { val := s - 2
      one_lt := by omega
      lt_large := by have := D.le_rank; omega
      le_small_succ := by have := D.le_rank; omega }
  have hcross : c.order ⟨s - 4, by
        have := D.le_rank
        omega⟩ <
      b.order ⟨s - 2, by
        have := D.le_rank
        omega⟩ := by
    have h := htrigger.1
    have hleft : (⟨(s - 2) - 2, by
          have := D.le_rank
          omega⟩ : Fin (n + 3)) =
        ⟨s - 4, by have := D.le_rank; omega⟩ := by
      apply Fin.ext
      change (s - 2) - 2 = s - 4
      omega
    simpa only [hleft] using h
  have hextra := a.lemma716_typeI_sMinusTwo_comparisonExtra_order_eq_of_cross
    b c R s D hfirst hnorm hvalues hsFour hcross
  have halpha : b.centralAlphaTrigger c i :=
    ((b.beli2019Lemma216 c le_rfl horder hdefect) i).mpr (by
      simpa only [i] using htrigger)
  have hessentialRaw :=
    b.isEssentialFor_of_centralAlphaTrigger c i halpha
  have hessential : b.IsEssentialFor c ⟨s - 3, by
      have := D.le_rank
      omega⟩ := by
    have hindex : (⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : Fin (n + 3)) =
        ⟨s - 3, by have := D.le_rank; omega⟩ := by
      apply Fin.ext
      dsimp only [i]
      change (s - 2) - 1 = s - 3
      omega
    rw [hindex] at hessentialRaw
    exact hessentialRaw
  rcases D.even with ⟨d, hd⟩
  let pairs := d - 2
  have hpairsLarge : 2 * (pairs + 1) = s - 2 := by
    dsimp only [pairs]
    omega
  have hpairsSmall : 2 * pairs = s - 4 := by
    dsimp only [pairs]
    omega
  have hlargeInterior : 2 * (pairs + 1) < n + 3 := by
    rw [hpairsLarge]
    have := D.le_rank
    omega
  have PlargeRaw := a.lemma716_typeI_sMinusTwo_sourceProfile
    b R s D hthird hvalues hsFour
  have Plarge : Beli2019Lemma716TypeIIFailureProfile b R
      (2 * (pairs + 1)) (by omega) hlargeInterior := by
    simpa only [hpairsLarge] using PlargeRaw
  have hsmallClasses : AlternatingEndpointPairClasses
      (c.prefixValueUnits (2 * pairs) (by omega)) := by
    by_cases hsEq : s = 4
    · have hpairsZero : pairs = 0 := by
        dsimp only [pairs]
        omega
      intro t
      exfalso
      have ht := t.isLt
      omega
    · have hsSix : 6 ≤ s := by omega
      have PsmallRaw :=
        a.lemma716_typeI_sMinusTwo_comparisonSmallProfile_of_essential
          b c R s D hfirst hsecond hnorm hvalues hsSix hextra hessential
      have hpairsPos : 0 < pairs := by
        dsimp only [pairs]
        omega
      have hsmallInterior : 2 * pairs < n + 3 := by
        rw [hpairsSmall]
        have := D.le_rank
        omega
      have Psmall : Beli2019Lemma716TypeIIFailureProfile c R
          (2 * pairs) (by omega) hsmallInterior := by
        simpa only [hpairsSmall] using PsmallRaw
      exact c.lemma716_typeIIFailureProfile_pairClasses R pairs hpairsPos
        hsmallInterior Psmall
  have hsmallOrders : ∀ t : Fin pairs,
      ordUnit K ((c.prefixValueUnits (2 * pairs) (by omega))
        ⟨2 * t.val, by omega⟩) = R + 1 := by
    by_cases hpairsZero : pairs = 0
    · intro t
      exfalso
      have ht := t.isLt
      omega
    · intro t
      have hpairsPos : 0 < pairs := Nat.pos_of_ne_zero hpairsZero
      have hsSix : 6 ≤ s := by
        dsimp only [pairs] at hpairsPos
        omega
      have PsmallRaw :=
        a.lemma716_typeI_sMinusTwo_comparisonSmallProfile_of_essential
          b c R s D hfirst hsecond hnorm hvalues hsSix hextra hessential
      have hsmallInterior : 2 * pairs < n + 3 := by
        rw [hpairsSmall]
        have := D.le_rank
        omega
      have Psmall : Beli2019Lemma716TypeIIFailureProfile c R
          (2 * pairs) (by omega) hsmallInterior := by
        simpa only [hpairsSmall] using PsmallRaw
      exact c.lemma716_typeIIFailureProfile_leadingOrders R pairs hpairsPos
        hsmallInterior Psmall t
  have hextraPairs : c.order ⟨2 * pairs, by omega⟩ = R + 1 := by
    have hindex : (⟨2 * pairs, by omega⟩ : Fin (n + 3)) =
        ⟨s - 4, by have := D.le_rank; omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      rw [hpairsSmall]
    rw [hindex]
    exact hextra
  have hrep := b.lemma716_endpointTower_onePairExtension_prefixRepresents
    c R pairs hlargeInterior Plarge hsmallClasses hsmallOrders hextraPairs
  exact prefixRepresents_cast c b (by omega) hpairsLarge hrep

end BONG.GoodBONG

end Bong
