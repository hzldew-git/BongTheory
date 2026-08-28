/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716TypeISCentral

/-!
# Beli (2019), Lemma 7.16(iii'): the type-I boundary `i = s - 1`

The first inequality in the central trigger rigidifies the comparison
prefix to the same alternating endpoint profile as the constructed prefix.
The geometric argument already used in condition (ii) shows that their
determinants have the same square class.  Equal-determinant endpoint-tower
cancellation then identifies the two length-`s - 2` prefixes, after which
the last target line is added by the tautological prefix inclusion.
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
variable [laws : DyadicDiscriminantClassLaws K]
variable [DyadicAlternatingEndpointTowerRepresentationLaws K]

/-- The crossing in condition (iii') at `i = s - 1` forces the comparison
prefix through `c_(s-2)` to have the rigid Lemma 7.5 endpoint profile. -/
theorem lemma716_typeI_sMinusOne_comparisonProfile_of_cross
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (hsFour : 4 ≤ s)
    (hcross : c.order ⟨s - 3, by
        have := D.le_rank
        omega⟩ <
      b.order ⟨s - 1, by
        have := D.le_rank
        omega⟩) :
    Beli2019Lemma716TypeIIFailureProfile c R (s - 2)
      (by omega) (by have := D.le_rank; omega) := by
  let zero : Fin (n + 3) := 0
  let high : Fin (n + 3) := ⟨s - 4, by
    have := D.le_rank
    omega⟩
  let low : Fin (n + 3) := ⟨s - 3, by
    have := D.le_rank
    omega⟩
  let targetBoundary : Fin (n + 3) := ⟨s - 1, by
    have := D.le_rank
    omega⟩
  have htargetBoundary : b.order targetBoundary =
      R - 2 * (ramificationIndex K : Int) + 2 := by
    simpa only [targetBoundary] using
      a.lemma716_typeI_rightBoundary_order_eq b R s D hsecond hvalues
  have hlowOdd : Odd low.val := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 2, by dsimp only [low]; omega⟩
  have hlowLower : R - 2 * (ramificationIndex K : Int) + 1 ≤
      c.order low :=
    a.lemma716_comparison_odd_order_ge c R hfirst hnorm low hlowOdd
  have hcross' : c.order low < b.order targetBoundary := by
    simpa only [low, targetBoundary] using hcross
  have hlowEq : c.order low =
      R - 2 * (ramificationIndex K : Int) + 1 := by
    rw [htargetBoundary] at hcross'
    omega
  have hhighEven : Even high.val := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 2, by dsimp only [high]; omega⟩
  have hhighLower : R + 1 ≤ c.order high :=
    a.lemma716_comparison_even_order_ge c R hfirst hnorm high hhighEven
  let gap : Fin (n + 2) := ⟨s - 4, by
    have := D.le_rank
    omega⟩
  have hgap : -(2 * (ramificationIndex K : Int)) ≤
      c.order low - c.order high := by
    have hraw := c.orderGap_ge_neg_two_mul_e gap
    unfold orderGap at hraw
    have hcast : gap.castSucc = high := by
      apply Fin.ext
      rfl
    have hsucc : gap.succ = low := by
      apply Fin.ext
      simp only [gap, low, Fin.val_succ]
      omega
    rwa [hcast, hsucc] at hraw
  have hhighEq : c.order high = R + 1 := by
    rw [hlowEq] at hgap
    omega
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
  · have hindex : (⟨(s - 2) - 2, by
        have := D.le_rank
        omega⟩ : Fin (n + 3)) = high := by
      apply Fin.ext
      dsimp only [high]
      omega
    simpa only [hindex] using hhighEq
  · have hindex : (⟨(s - 2) - 1, by
        have := D.le_rank
        omega⟩ : Fin (n + 3)) = low := by
      apply Fin.ext
      dsimp only [low]
      omega
    simpa only [hindex] using hlowEq

/-- Two rigid length-`s - 2` endpoint prefixes with equal determinant
square class represent one another. -/
theorem lemma716_typeI_sMinusOne_prefixRepresents_of_profiles
    (b : GoodBONG q M (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (hsEven : Even s) (hsFour : 4 ≤ s)
    (hsRank : s ≤ n + 3)
    (Pb : Beli2019Lemma716TypeIIFailureProfile b R (s - 2)
      (by omega) (by omega))
    (Pc : Beli2019Lemma716TypeIIFailureProfile c R (s - 2)
      (by omega) (by omega))
    (hsquare : IsSquare
      (b.prefixProduct (s - 2) * c.prefixProduct (s - 2))) :
    DiagonalRepresents
      (c.prefixValues (s - 2) (by omega))
      (b.prefixValues (s - 2) (by omega)) := by
  rcases hsEven with ⟨d, hd⟩
  let pairs := d - 1
  have hpairs : 0 < pairs := by dsimp only [pairs]; omega
  have hlength : 2 * pairs = s - 2 := by dsimp only [pairs]; omega
  have hInterior : 2 * pairs < n + 3 := by omega
  let source : Fin (2 * pairs) → Kˣ :=
    b.prefixValueUnits (2 * pairs) (Nat.le_of_lt hInterior)
  let comparison : Fin (2 * pairs) → Kˣ :=
    c.prefixValueUnits (2 * pairs) (Nat.le_of_lt hInterior)
  have Pb' : Beli2019Lemma716TypeIIFailureProfile b R (2 * pairs)
      (by omega) hInterior := by
    simpa only [hlength] using Pb
  have Pc' : Beli2019Lemma716TypeIIFailureProfile c R (2 * pairs)
      (by omega) hInterior := by
    simpa only [hlength] using Pc
  have hsourceClasses : AlternatingEndpointPairClasses source := by
    simpa only [source] using
      b.lemma716_typeIIFailureProfile_pairClasses R pairs hpairs
        hInterior Pb'
  have hcomparisonClasses : AlternatingEndpointPairClasses comparison := by
    simpa only [comparison] using
      c.lemma716_typeIIFailureProfile_pairClasses R pairs hpairs
        hInterior Pc'
  let scale : Kˣ := uniformizerPowerUnit K (R + 1)
  have hscaleOrder : ordUnit K scale = R + 1 := by
    simp only [scale, ordUnit_uniformizerPowerUnit]
  have hsourceOrders : AlternatingEndpointLeadingOrdersAt source scale := by
    intro t
    calc
      ordUnit K (source ⟨2 * t.val, by omega⟩) = R + 1 := by
        simpa only [source] using
          b.lemma716_typeIIFailureProfile_leadingOrders R pairs hpairs
            hInterior Pb' t
      _ = ordUnit K scale := hscaleOrder.symm
  have hcomparisonOrders :
      AlternatingEndpointLeadingOrdersAt comparison scale := by
    intro t
    calc
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) = R + 1 := by
        simpa only [comparison] using
          c.lemma716_typeIIFailureProfile_leadingOrders R pairs hpairs
            hInterior Pc' t
      _ = ordUnit K scale := hscaleOrder.symm
  have hdet : IsSquare
      (diagonalUnitDeterminant source *
        diagonalUnitDeterminant comparison) := by
    simpa only [source, comparison,
      diagonalUnitDeterminant_prefixValueUnits, hlength] using hsquare
  have hrep := alternatingEndpointTower_equalDeterminantRepresentation
    source comparison scale hsourceClasses hcomparisonClasses
      hsourceOrders hcomparisonOrders hdet
  have hrep' : DiagonalRepresents
      (c.prefixValues (2 * pairs) (Nat.le_of_lt hInterior))
      (b.prefixValues (2 * pairs) (Nat.le_of_lt hInterior)) := by
    simpa only [source, comparison,
      diagonalUnitCoefficients_prefixValueUnits] using hrep
  exact prefixRepresents_cast c b hlength hlength hrep'

/-- Condition (iii') at the type-I boundary with paper index `s - 1`. -/
theorem lemma716_typeI_sMinusOne_centralRepresentationAt
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hI : Lemma714IsTypeI a R s)
    (hdiscriminant : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (hsFour : 4 ≤ s)
    (htrigger : b.centralDefectTrigger c
      { val := s - 1
        one_lt := by omega
        lt_large := by have := D.le_rank; omega
        le_small_succ := by have := D.le_rank; omega }) :
    DiagonalRepresents
      (c.prefixValues (s - 2) (by have := D.le_rank; omega))
      (b.prefixValues (s - 1) (by have := D.le_rank; omega)) := by
  let i : CentralRepresentationIndex (n + 3) (n + 3) :=
    { val := s - 1
      one_lt := by omega
      lt_large := by have := D.le_rank; omega
      le_small_succ := by have := D.le_rank; omega }
  have hcross : c.order ⟨s - 3, by
        have := D.le_rank
        omega⟩ <
      b.order ⟨s - 1, by
        have := D.le_rank
        omega⟩ := by
    have := htrigger.1
    have hleft : (⟨(s - 1) - 2, by
          have := D.le_rank
          omega⟩ : Fin (n + 3)) =
        ⟨s - 3, by
          have := D.le_rank
          omega⟩ := by
      apply Fin.ext
      change (s - 1) - 2 = s - 3
      omega
    simpa only [hleft] using this
  have Pc := a.lemma716_typeI_sMinusOne_comparisonProfile_of_cross
    b c R s D hfirst hsecond hnorm hvalues hsFour hcross
  have Pb := a.lemma716_typeI_sMinusTwo_sourceProfile
    b R s D hthird hvalues hsFour
  have hsquare :=
    a.lemma716_typeI_sMinusTwo_exceptional_prefixProduct_isSquare
      b c R s D hfirst hsecond hthird hvalues hac hI hdiscriminant
        hsFour Pc
  have hprefix := b.lemma716_typeI_sMinusOne_prefixRepresents_of_profiles
    c R s D.even hsFour D.le_rank Pb Pc hsquare
  have hlast := b.prefixValues_represents_of_le
    (s - 2) (s - 1) (by have := D.le_rank; omega) (by
      have := D.le_rank
      omega)
  exact hprefix.trans hlast

end BONG.GoodBONG

end Bong
