/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Lemma311
import Bong.Bong.HeHu2022Lemma314
import Bong.Bong.Beli2019Lemma911
import Bong.Bong.BeliUniversalSectionFour
import Bong.Bong.StructuralProof

/-!
# He--Hu (2024), Proposition 3.7

This file proves that the explicit lattices in Table 2 are `O`-maximal and
identifies them with the intrinsic maximal representatives chosen in
Definition 3.6.  The maximality proof follows the published volume argument:
a proper integral over-lattice lowers the volume order by a positive even
integer, while Proposition 2.7 gives sharp lower bounds for the orders in a
good BONG.  The three equality profiles are excluded by the quadratic-space
classification from Proposition 3.5.
-/

namespace Bong

open Dyadic Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Lattice

variable {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- O'Meara 82:23 in the direction needed in Proposition 3.7: adjoining
any number of literal half-hyperbolic planes to an `O`-maximal lattice again
gives an `O`-maximal lattice.  This is derived from the proved maximal-lattice
splitting theorem, rather than installed as an additional local axiom. -/
theorem IsOMaximal.halfHyperbolicExtension
    (hL : IsOMaximal q L) (k : Nat) :
    IsOMaximal (halfHyperbolicExtensionForm q k)
      (halfHyperbolicExtensionLattice L k) := by
  obtain ⟨M, hM⟩ := exists_oMaximal_lattice
    (halfHyperbolicExtensionForm q k)
    (halfHyperbolicExtensionLattice L k)
  have hambient :
      (halfHyperbolicExtensionForm q k).IsIsometric
        (halfHyperbolicExtensionForm q k) :=
    ⟨QuadraticSpace.Isometry.refl _⟩
  rcases beliUniversalLemma42 hM hL k hambient with ⟨f⟩
  exact hM.of_latticeIsometry f

end Lattice

namespace BONG.GoodBONG

variable {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Choose a good BONG of an over-lattice and transport its length to that
of a fixed reference BONG in the same ambient quadratic space. -/
noncomputable def heHuGoodBONGOfSameSpace {n : Nat}
    (b : GoodBONG q L n) (M : Lattice K V) : GoodBONG q M n := by
  letI : BONGStructuralLaws.{u, u} K := bongStructuralLawsProved K
  exact (GoodBONG.ofLattice q M).castLength b.toBONG.length_eq_finrank.symm

/-- Proposition 2.7(i) gives the sharp rank-one volume lower bound. -/
theorem heHuVolumeOrder_lower_rankOne
    (b : GoodBONG q L 1) (hL : Lattice.IsIntegral q L) :
    0 ≤ Lattice.volumeOrder q L := by
  let C := b.heHu2022Proposition27i hL
  have hzero :=
    (C.oddIndexed (0 : Fin 1) 0 le_rfl Even.zero Even.zero).1
  rw [b.toBONG.volumeOrder_eq_sum_order, Fin.sum_univ_one]
  exact hzero

/-- Proposition 2.7(i) gives the sharp rank-two volume lower bound. -/
theorem heHuVolumeOrder_lower_rankTwo
    (b : GoodBONG q L 2) (hL : Lattice.IsIntegral q L) :
    -(2 * (ramificationIndex K : Int)) ≤ Lattice.volumeOrder q L := by
  let C := b.heHu2022Proposition27i hL
  have hzero :=
    (C.oddIndexed (0 : Fin 2) 0 le_rfl Even.zero Even.zero).1
  have hone :=
    (C.evenIndexed (1 : Fin 2) 1 le_rfl odd_one odd_one).1
  change 0 ≤ b.toBONG.order 0 at hzero
  change -(2 * (ramificationIndex K : Int)) ≤
    b.toBONG.order 1 at hone
  rw [b.toBONG.volumeOrder_eq_sum_order, Fin.sum_univ_two]
  omega

/-- Proposition 2.7(i) gives the sharp rank-three volume lower bound. -/
theorem heHuVolumeOrder_lower_rankThree
    (b : GoodBONG q L 3) (hL : Lattice.IsIntegral q L) :
    -(2 * (ramificationIndex K : Int)) ≤ Lattice.volumeOrder q L := by
  let C := b.heHu2022Proposition27i hL
  have hzero :=
    (C.oddIndexed (0 : Fin 3) 0 le_rfl Even.zero Even.zero).1
  have hone :=
    (C.evenIndexed (1 : Fin 3) 1 le_rfl odd_one odd_one).1
  have htwo :=
    (C.oddIndexed (2 : Fin 3) 2 le_rfl (by norm_num) (by norm_num)).1
  change 0 ≤ b.toBONG.order 0 at hzero
  change -(2 * (ramificationIndex K : Int)) ≤
    b.toBONG.order 1 at hone
  change 0 ≤ b.toBONG.order 2 at htwo
  rw [b.toBONG.volumeOrder_eq_sum_order, Fin.sum_univ_three]
  omega

/-- Proposition 2.7(i) gives the sharp rank-four volume lower bound. -/
theorem heHuVolumeOrder_lower_rankFour
    (b : GoodBONG q L 4) (hL : Lattice.IsIntegral q L) :
    -(4 * (ramificationIndex K : Int)) ≤ Lattice.volumeOrder q L := by
  let C := b.heHu2022Proposition27i hL
  have hzero :=
    (C.oddIndexed (0 : Fin 4) 0 le_rfl Even.zero Even.zero).1
  have hone :=
    (C.evenIndexed (1 : Fin 4) 1 le_rfl odd_one odd_one).1
  have htwo :=
    (C.oddIndexed (2 : Fin 4) 2 le_rfl (by norm_num) (by norm_num)).1
  have hthree :=
    (C.evenIndexed (3 : Fin 4) 3 le_rfl (by norm_num) (by norm_num)).1
  change 0 ≤ b.toBONG.order 0 at hzero
  change -(2 * (ramificationIndex K : Int)) ≤
    b.toBONG.order 1 at hone
  change 0 ≤ b.toBONG.order 2 at htwo
  change -(2 * (ramificationIndex K : Int)) ≤
    b.toBONG.order 3 at hthree
  rw [b.toBONG.volumeOrder_eq_sum_order, Fin.sum_univ_four]
  omega

/-- The common strict-over-lattice reduction in Proposition 3.7.  If the
index exponent is zero, volume rigidity already gives equality; otherwise
the over-lattice volume is at least two below the displayed candidate. -/
theorem heHuEqOrVolumeDropTwo {n : Nat}
    (_b : GoodBONG q L n) (M : Lattice K V) (hLM : L ≤ M) :
    M = L ∨ Lattice.volumeOrder q M ≤
      Lattice.volumeOrder q L - 2 := by
  rcases Lattice.exists_volumeOrder_eq_add_two_mul_nat q hLM with ⟨k, hk⟩
  by_cases hkzero : k = 0
  · left
    apply (Lattice.eq_of_le_of_volumeOrder_eq q L M hLM ?_).symm
    rw [hk, hkzero]
    norm_num
  · right
    have hkpos : 1 ≤ k := by omega
    omega

/-- A rank-one integral good BONG whose order is at most one is already
`O`-maximal.  This covers both unary rows in Table 2. -/
theorem heHuRankOne_isOMaximal_of_order_le_one
    (b : GoodBONG q L 1) (hL : Lattice.IsIntegral q L)
    (horder : b.order 0 ≤ 1) : Lattice.IsOMaximal q L := by
  refine ⟨hL, ?_⟩
  intro M hLM hM
  rcases b.heHuEqOrVolumeDropTwo M hLM with heq | hdrop
  · exact heq
  · let c := b.heHuGoodBONGOfSameSpace M
    have hlower := c.heHuVolumeOrder_lower_rankOne hM
    have hbvol : Lattice.volumeOrder q L = b.order 0 := by
      rw [b.toBONG.volumeOrder_eq_sum_order, Fin.sum_univ_one]
      rfl
    rw [hbvol] at hdrop
    omega

/-- The sharp lower profile `0,-2e` is volume-minimal in rank two. -/
theorem heHuRankTwo_isOMaximal_of_volume_lower
    (b : GoodBONG q L 2) (hL : Lattice.IsIntegral q L)
    (hvolume : Lattice.volumeOrder q L =
      -(2 * (ramificationIndex K : Int))) :
    Lattice.IsOMaximal q L := by
  refine ⟨hL, ?_⟩
  intro M hLM hM
  rcases b.heHuEqOrVolumeDropTwo M hLM with heq | hdrop
  · exact heq
  · let c := b.heHuGoodBONGOfSameSpace M
    have hlower := c.heHuVolumeOrder_lower_rankTwo hM
    rw [hvolume] at hdrop
    omega

/-- The noncritical odd-rank profile `0,-2e,1` is maximal by the strict
two-step volume drop. -/
theorem heHuRankThree_isOMaximal_of_volume_le_lower_add_one
    (b : GoodBONG q L 3) (hL : Lattice.IsIntegral q L)
    (hvolume : Lattice.volumeOrder q L ≤
      1 - 2 * (ramificationIndex K : Int)) :
    Lattice.IsOMaximal q L := by
  refine ⟨hL, ?_⟩
  intro M hLM hM
  rcases b.heHuEqOrVolumeDropTwo M hLM with heq | hdrop
  · exact heq
  · let c := b.heHuGoodBONGOfSameSpace M
    have hlower := c.heHuVolumeOrder_lower_rankThree hM
    omega

/-- Binary version of the source's inequality (2.3): if the candidate has
volume `1-d` and adjacent defect `d`, every proper integral enlargement
would have volume at most `-1-d`, whereas Beli's local defect inequality
forces volume at least `-d`. -/
theorem heHuBinary_isOMaximal_of_volume_and_adjacentDefect
    (b : GoodBONG q L 2) (hL : Lattice.IsIntegral q L) (d : Int)
    (hvolume : Lattice.volumeOrder q L = 1 - d)
    (hdefect : b.adjacentDefect 0 =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    Lattice.IsOMaximal q L := by
  refine ⟨hL, ?_⟩
  intro M hLM hM
  rcases b.heHuEqOrVolumeDropTwo M hLM with heq | hdrop
  · exact heq
  · let c := b.heHuGoodBONGOfSameSpace M
    have hc0 :=
      ((c.heHu2022Proposition27i hM).oddIndexed
        (0 : Fin 2) 0 le_rfl Even.zero Even.zero).1
    have hlocal := c.zero_le_orderGap_add_adjacentDefect (0 : Fin 1)
    have hsame := adjacentDefect_eq_of_binaryBONGs b c
    rw [hsame, hdefect] at hlocal
    norm_cast at hlocal
    have hcvol : Lattice.volumeOrder q M = c.order 0 + c.order 1 := by
      rw [c.toBONG.volumeOrder_eq_sum_order, Fin.sum_univ_two]
      rfl
    rw [hvolume] at hdrop
    exfalso
    rw [hcvol] at hdrop
    unfold orderGap at hlocal
    have hlocal' : 0 ≤ c.order 1 - c.order 0 + d := by
      simpa only [Fin.castSucc_zero, Fin.succ_zero_eq_one] using hlocal
    omega

/-- The sole critical binary volume case in Proposition 3.7.  A proper
integral over-lattice would have the exact endpoint profile `0,-2e`; the
caller rules out that profile in the fixed ambient space. -/
theorem heHuRankTwo_isOMaximal_of_excluding_endpoint
    (b : GoodBONG q L 2) (hL : Lattice.IsIntegral q L)
    (hvolume : Lattice.volumeOrder q L =
      2 - 2 * (ramificationIndex K : Int))
    (hexclude : ∀ (M : Lattice K V) (c : GoodBONG q M 2),
      Lattice.IsIntegral q M →
      c.order 0 = 0 →
      c.order 1 = -(2 * (ramificationIndex K : Int)) → False) :
    Lattice.IsOMaximal q L := by
  refine ⟨hL, ?_⟩
  intro M hLM hM
  rcases b.heHuEqOrVolumeDropTwo M hLM with heq | hdrop
  · exact heq
  · let c := b.heHuGoodBONGOfSameSpace M
    let C := c.heHu2022Proposition27i hM
    have hzero :=
      (C.oddIndexed (0 : Fin 2) 0 le_rfl Even.zero Even.zero).1
    have hone :=
      (C.evenIndexed (1 : Fin 2) 1 le_rfl odd_one odd_one).1
    change 0 ≤ c.order 0 at hzero
    change -(2 * (ramificationIndex K : Int)) ≤ c.order 1 at hone
    have hcvol : Lattice.volumeOrder q M = c.order 0 + c.order 1 := by
      rw [c.toBONG.volumeOrder_eq_sum_order, Fin.sum_univ_two]
      rfl
    have hlower := c.heHuVolumeOrder_lower_rankTwo hM
    have heqvol : Lattice.volumeOrder q M =
        -(2 * (ramificationIndex K : Int)) := by
      omega
    have hzeroEq : c.order 0 = 0 := by
      rw [hcvol] at heqvol
      omega
    have honeEq : c.order 1 =
        -(2 * (ramificationIndex K : Int)) := by
      rw [hcvol] at heqvol
      omega
    exact (hexclude M c hM hzeroEq honeEq).elim

/-- The sole critical quaternary volume case in Proposition 3.7. -/
theorem heHuRankFour_isOMaximal_of_excluding_endpoint
    (b : GoodBONG q L 4) (hL : Lattice.IsIntegral q L)
    (hvolume : Lattice.volumeOrder q L =
      2 - 4 * (ramificationIndex K : Int))
    (hexclude : ∀ (M : Lattice K V) (c : GoodBONG q M 4),
      Lattice.IsIntegral q M →
      c.order 0 = 0 →
      c.order 1 = -(2 * (ramificationIndex K : Int)) →
      c.order 2 = 0 →
      c.order 3 = -(2 * (ramificationIndex K : Int)) → False) :
    Lattice.IsOMaximal q L := by
  refine ⟨hL, ?_⟩
  intro M hLM hM
  rcases b.heHuEqOrVolumeDropTwo M hLM with heq | hdrop
  · exact heq
  · let c := b.heHuGoodBONGOfSameSpace M
    let C := c.heHu2022Proposition27i hM
    have hzero :=
      (C.oddIndexed (0 : Fin 4) 0 le_rfl Even.zero Even.zero).1
    have hone :=
      (C.evenIndexed (1 : Fin 4) 1 le_rfl odd_one odd_one).1
    have htwo :=
      (C.oddIndexed (2 : Fin 4) 2 le_rfl (by norm_num)
        (by norm_num)).1
    have hthree :=
      (C.evenIndexed (3 : Fin 4) 3 le_rfl (by norm_num)
        (by norm_num)).1
    change 0 ≤ c.order 0 at hzero
    change -(2 * (ramificationIndex K : Int)) ≤ c.order 1 at hone
    change 0 ≤ c.order 2 at htwo
    change -(2 * (ramificationIndex K : Int)) ≤ c.order 3 at hthree
    have hcvol : Lattice.volumeOrder q M =
        c.order 0 + c.order 1 + c.order 2 + c.order 3 := by
      rw [c.toBONG.volumeOrder_eq_sum_order, Fin.sum_univ_four]
      rfl
    have hlower := c.heHuVolumeOrder_lower_rankFour hM
    have heqvol : Lattice.volumeOrder q M =
        -(4 * (ramificationIndex K : Int)) := by
      omega
    rw [hcvol] at heqvol
    have hzeroEq : c.order 0 = 0 := by omega
    have honeEq : c.order 1 =
        -(2 * (ramificationIndex K : Int)) := by omega
    have htwoEq : c.order 2 = 0 := by omega
    have hthreeEq : c.order 3 =
        -(2 * (ramificationIndex K : Int)) := by omega
    exact (hexclude M c hM hzeroEq honeEq htwoEq hthreeEq).elim

/-- The sole critical ternary volume case in Proposition 3.7. -/
theorem heHuRankThree_isOMaximal_of_excluding_endpoint
    (b : GoodBONG q L 3) (hL : Lattice.IsIntegral q L)
    (hvolume : Lattice.volumeOrder q L =
      2 - 2 * (ramificationIndex K : Int))
    (hexclude : ∀ (M : Lattice K V) (c : GoodBONG q M 3),
      Lattice.IsIntegral q M →
      c.order 0 = 0 →
      c.order 1 = -(2 * (ramificationIndex K : Int)) →
      c.order 2 = 0 → False) :
    Lattice.IsOMaximal q L := by
  refine ⟨hL, ?_⟩
  intro M hLM hM
  rcases b.heHuEqOrVolumeDropTwo M hLM with heq | hdrop
  · exact heq
  · let c := b.heHuGoodBONGOfSameSpace M
    let C := c.heHu2022Proposition27i hM
    have hzero :=
      (C.oddIndexed (0 : Fin 3) 0 le_rfl Even.zero Even.zero).1
    have hone :=
      (C.evenIndexed (1 : Fin 3) 1 le_rfl odd_one odd_one).1
    have htwo :=
      (C.oddIndexed (2 : Fin 3) 2 le_rfl (by norm_num)
        (by norm_num)).1
    change 0 ≤ c.order 0 at hzero
    change -(2 * (ramificationIndex K : Int)) ≤ c.order 1 at hone
    change 0 ≤ c.order 2 at htwo
    have hcvol : Lattice.volumeOrder q M =
        c.order 0 + c.order 1 + c.order 2 := by
      rw [c.toBONG.volumeOrder_eq_sum_order, Fin.sum_univ_three]
      rfl
    have hlower := c.heHuVolumeOrder_lower_rankThree hM
    have heqvol : Lattice.volumeOrder q M =
        -(2 * (ramificationIndex K : Int)) := by
      omega
    rw [hcvol] at heqvol
    have hzeroEq : c.order 0 = 0 := by omega
    have honeEq : c.order 1 =
        -(2 * (ramificationIndex K : Int)) := by omega
    have htwoEq : c.order 2 = 0 := by omega
    exact (hexclude M c hM hzeroEq honeEq htwoEq).elim

/-! ## Endpoint-space exclusions in the three critical rows -/

/-- A good BONG with the alternating endpoint order profile has the two
allowed signed determinant classes pair by pair.  This is the coefficient
form of Proposition 2.7(iii), separated out for the equality cases in
Proposition 3.7. -/
theorem heHuAlternatingPairClasses_of_orders {pairs : Nat}
    (c : GoodBONG q L (2 * pairs))
    (horders : ∀ t : Fin pairs,
      c.order ⟨2 * t.val, by omega⟩ = 0 ∧
        c.order ⟨2 * t.val + 1, by omega⟩ =
          -(2 * (ramificationIndex K : Int))) :
    AlternatingEndpointPairClasses c.valueUnit := by
  intro t
  let evenIndex : Fin (2 * pairs) := ⟨2 * t.val, by omega⟩
  have hevenNext : evenIndex.val + 1 < 2 * pairs := by
    simp only [evenIndex]
    omega
  have hindexNext :
      (⟨evenIndex.val + 1, hevenNext⟩ : Fin (2 * pairs)) =
        ⟨2 * t.val + 1, by omega⟩ := by
    apply Fin.ext
    rfl
  have hpair := horders t
  have hgap :
      c.order ⟨evenIndex.val + 1, hevenNext⟩ - c.order evenIndex =
        -(2 * (ramificationIndex K : Int)) := by
    rw [hindexNext, hpair.2]
    change -(2 * (ramificationIndex K : Int)) -
        c.order ⟨2 * t.val, by omega⟩ = _
    rw [hpair.1]
    omega
  have hpClass := c.toBONG.adjacentUnitSquareClass_endpoint_cases
    evenIndex hevenNext hgap
  have hpSigned := c.toBONG.adjacentSignedProduct_endpoint_cases
    evenIndex hevenNext hpClass
  simpa [AlternatingEndpointPairClasses, GoodBONG.valueUnit,
    evenIndex, hindexNext] using hpSigned

/-- The leading entries in an alternating endpoint profile all have unit
scale. -/
theorem heHuAlternatingLeadingOrders_of_orders {pairs : Nat}
    (c : GoodBONG q L (2 * pairs))
    (horders : ∀ t : Fin pairs,
      c.order ⟨2 * t.val, by omega⟩ = 0 ∧
        c.order ⟨2 * t.val + 1, by omega⟩ =
          -(2 * (ramificationIndex K : Int))) :
    AlternatingEndpointLeadingOrdersAt c.valueUnit (1 : Kˣ) := by
  intro t
  change ordUnit K (c.toBONG.valueUnit ⟨2 * t.val, by omega⟩) =
    ordUnit K (1 : Kˣ)
  rw [← c.toBONG.order_eq_ordUnit]
  change c.order ⟨2 * t.val, by omega⟩ = ordUnit K (1 : Kˣ)
  rw [(horders t).1]
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  exact hone.symm

/-- The conventional diagonal representative of the discriminant endpoint
at scale `pi^R`. -/
noncomputable def heHuDiscriminantEndpointStandardValues
    (R : Int) : Fin 2 → Kˣ :=
  ![uniformizerPowerUnit K R,
    -((inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit *
      uniformizerPowerUnit K R)]

/-- The coordinate squares which remove the literal `pi^(-2e)` appearing
in Lemma 3.9 from a discriminant endpoint. -/
noncomputable def heHuDiscriminantEndpointStandardFactors : Fin 2 → Kˣ :=
  ![1, uniformizerPowerUnit K (-(ramificationIndex K : Int))]

theorem heHuDiscriminantEndpointValues_eq_standard_mul_square
    (R : Int) (i : Fin 2) :
    heHuDiscriminantEndpointValues (K := K) R i =
      heHuDiscriminantEndpointStandardValues (K := K) R i *
        heHuDiscriminantEndpointStandardFactors (K := K) i ^ 2 := by
  fin_cases i
  · simp [heHuDiscriminantEndpointValues,
      heHuDiscriminantEndpointStandardValues,
      heHuDiscriminantEndpointStandardFactors]
  · change
      -((inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit *
        uniformizerPowerUnit K
          (R - 2 * (ramificationIndex K : Int))) =
        -((inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit *
          uniformizerPowerUnit K R) *
          uniformizerPowerUnit K (-(ramificationIndex K : Int)) ^ 2
    have hpowers :
        uniformizerPowerUnit K
            (R - 2 * (ramificationIndex K : Int)) =
          uniformizerPowerUnit K R *
            uniformizerPowerUnit K (-(ramificationIndex K : Int)) ^ 2 := by
      rw [pow_two]
      unfold uniformizerPowerUnit
      rw [← zpow_add, ← zpow_add]
      congr 1
      ring
    rw [hpowers, ← mul_assoc, neg_mul]

/-- The literal Lemma 3.9 endpoint and its conventional diagonal pair are
equal-rank isometric presentations. -/
theorem heHuDiscriminantEndpoint_diagonalRepresents_standard
    (R : Int) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuDiscriminantEndpointValues (K := K) R))
      (diagonalUnitCoefficients
        (heHuDiscriminantEndpointStandardValues (K := K) R)) :=
  Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square
    (heHuDiscriminantEndpointValues (K := K) R)
    (heHuDiscriminantEndpointStandardValues (K := K) R)
    (heHuDiscriminantEndpointStandardFactors (K := K))
    (heHuDiscriminantEndpointValues_eq_standard_mul_square R)

@[simp]
theorem heHuDiscriminantEndpointGoodBONG_diagonalRepresents_standard
    (R : Int) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuDiscriminantEndpointGoodBONG (K := K) R).valueUnit)
      (diagonalUnitCoefficients
        (heHuDiscriminantEndpointStandardValues (K := K) R)) := by
  have hvalues :
      (heHuDiscriminantEndpointGoodBONG (K := K) R).valueUnit =
        heHuDiscriminantEndpointValues (K := K) R := by
    funext i
    exact heHuDiscriminantEndpointGoodBONG_valueUnit R i
  rw [hvalues]
  exact heHuDiscriminantEndpoint_diagonalRepresents_standard R

/-- Literal coefficients of the quaternary second-column candidate. -/
theorem heHuLemma311EvenSecondOneTail_valueUnit
    (i : Fin 4) :
    (heHuLemma311EvenSecondOneTail (K := K)).valueUnit i =
      ![heHuDiscriminantEndpointValues (K := K) 0 0,
        heHuDiscriminantEndpointValues (K := K) 0 1,
        heHuDiscriminantEndpointValues (K := K) 1 0,
        heHuDiscriminantEndpointValues (K := K) 1 1] i := by
  unfold heHuLemma311EvenSecondOneTail
  fin_cases i
  · change
      ((heHuDiscriminantEndpointGoodBONG (K := K) 0)
        |>.orthogonalProductRight_of_orderBounds
          (heHuDiscriminantEndpointGoodBONG (K := K) 1)
          heHuLemma311EvenSecondOne_orderBound
          heHuLemma311EvenSecondOne_lastSecondBound).valueUnit
            (BONG.orthogonalProductLeftIndex 2 (0 : Fin 2)) = _
    rw [GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_left,
      heHuDiscriminantEndpointGoodBONG_valueUnit]
    rfl
  · change
      ((heHuDiscriminantEndpointGoodBONG (K := K) 0)
        |>.orthogonalProductRight_of_orderBounds
          (heHuDiscriminantEndpointGoodBONG (K := K) 1)
          heHuLemma311EvenSecondOne_orderBound
          heHuLemma311EvenSecondOne_lastSecondBound).valueUnit
            (BONG.orthogonalProductLeftIndex 2 (1 : Fin 2)) = _
    rw [GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_left,
      heHuDiscriminantEndpointGoodBONG_valueUnit]
    rfl
  · change
      ((heHuDiscriminantEndpointGoodBONG (K := K) 0)
        |>.orthogonalProductRight_of_orderBounds
          (heHuDiscriminantEndpointGoodBONG (K := K) 1)
          heHuLemma311EvenSecondOne_orderBound
          heHuLemma311EvenSecondOne_lastSecondBound).valueUnit
            (BONG.orthogonalProductRightIndex 2 (0 : Fin 2)) = _
    rw [GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_right,
      heHuDiscriminantEndpointGoodBONG_valueUnit]
    rfl
  · change
      ((heHuDiscriminantEndpointGoodBONG (K := K) 0)
        |>.orthogonalProductRight_of_orderBounds
          (heHuDiscriminantEndpointGoodBONG (K := K) 1)
          heHuLemma311EvenSecondOne_orderBound
          heHuLemma311EvenSecondOne_lastSecondBound).valueUnit
            (BONG.orthogonalProductRightIndex 2 (1 : Fin 2)) = _
    rw [GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_right,
      heHuDiscriminantEndpointGoodBONG_valueUnit]
    rfl

noncomputable def heHuLemma311EvenSecondOneStandardValues
    : Fin 4 → Kˣ :=
  ![heHuDiscriminantEndpointStandardValues (K := K) 0 0,
    heHuDiscriminantEndpointStandardValues (K := K) 0 1,
    heHuDiscriminantEndpointStandardValues (K := K) 1 0,
    heHuDiscriminantEndpointStandardValues (K := K) 1 1]

noncomputable def heHuLemma311EvenSecondOneFactors : Fin 4 → Kˣ :=
  ![heHuDiscriminantEndpointStandardFactors (K := K) 0,
    heHuDiscriminantEndpointStandardFactors (K := K) 1,
    heHuDiscriminantEndpointStandardFactors (K := K) 0,
    heHuDiscriminantEndpointStandardFactors (K := K) 1]

theorem heHuLemma311EvenSecondOneTail_eq_anisotropic_mul_square
    (i : Fin 4) :
    (heHuLemma311EvenSecondOneTail (K := K)).valueUnit i =
      heHuLemma311EvenSecondOneStandardValues (K := K) i *
        heHuLemma311EvenSecondOneFactors (K := K) i ^ 2 := by
  fin_cases i
  · rw [heHuLemma311EvenSecondOneTail_valueUnit]
    change heHuDiscriminantEndpointValues (K := K) 0 0 =
      heHuDiscriminantEndpointStandardValues (K := K) 0 0 *
        heHuDiscriminantEndpointStandardFactors (K := K) 0 ^ 2
    exact heHuDiscriminantEndpointValues_eq_standard_mul_square 0 0
  · rw [heHuLemma311EvenSecondOneTail_valueUnit]
    change heHuDiscriminantEndpointValues (K := K) 0 1 =
      heHuDiscriminantEndpointStandardValues (K := K) 0 1 *
        heHuDiscriminantEndpointStandardFactors (K := K) 1 ^ 2
    exact heHuDiscriminantEndpointValues_eq_standard_mul_square 0 1
  · rw [heHuLemma311EvenSecondOneTail_valueUnit]
    change heHuDiscriminantEndpointValues (K := K) 1 0 =
      heHuDiscriminantEndpointStandardValues (K := K) 1 0 *
        heHuDiscriminantEndpointStandardFactors (K := K) 0 ^ 2
    exact heHuDiscriminantEndpointValues_eq_standard_mul_square 1 0
  · rw [heHuLemma311EvenSecondOneTail_valueUnit]
    change heHuDiscriminantEndpointValues (K := K) 1 1 =
      heHuDiscriminantEndpointStandardValues (K := K) 1 1 *
        heHuDiscriminantEndpointStandardFactors (K := K) 1 ^ 2
    exact heHuDiscriminantEndpointValues_eq_standard_mul_square 1 1

theorem heHuLemma311EvenSecondOneStandardValues_eq_anisotropic
    :
    heHuLemma311EvenSecondOneStandardValues (K := K) =
      beliAnisotropicQuaternaryUnits (K := K) := by
  funext i
  fin_cases i <;>
    simp [heHuLemma311EvenSecondOneStandardValues,
      heHuDiscriminantEndpointStandardValues,
      beliAnisotropicQuaternaryUnits, uniformizerPowerUnit]

/-- The quaternary candidate in Table 2 is the anisotropic Table 1 space. -/
theorem heHuLemma311EvenSecondOneTail_anisotropic
    :
    DiagonalAnisotropic
      (diagonalUnitCoefficients
        (heHuLemma311EvenSecondOneTail (K := K)).valueUnit) := by
  apply
    (Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square
      (heHuLemma311EvenSecondOneTail (K := K)).valueUnit
      (heHuLemma311EvenSecondOneStandardValues (K := K))
      (heHuLemma311EvenSecondOneFactors (K := K))
      (heHuLemma311EvenSecondOneTail_eq_anisotropic_mul_square
        (K := K))).anisotropic_of
  rw [heHuLemma311EvenSecondOneStandardValues_eq_anisotropic]
  exact heHuAnisotropicQuaternary_units_anisotropic (K := K)

theorem heHuEvenFirstTail_one_pairClasses :
    AlternatingEndpointPairClasses (pairs := 2)
      (heHuEvenFirstTail (K := K) (1 : Kˣ)) := by
  intro t
  fin_cases t
  · left
    refine ⟨1, ?_⟩
    simp [heHuEvenFirstTail_eq_vector]
  · left
    refine ⟨1, ?_⟩
    simp [heHuEvenFirstTail_eq_vector]

theorem heHuEvenFirstTail_discriminant_pairClasses :
    AlternatingEndpointPairClasses (pairs := 2)
      (heHuEvenFirstTail (K := K)
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit) := by
  intro t
  fin_cases t
  · left
    refine ⟨1, ?_⟩
    simp [heHuEvenFirstTail_eq_vector]
  · right
    refine ⟨(inferInstance :
      DyadicDiscriminantClassLaws K).discriminantUnit, ?_⟩
    simp [heHuEvenFirstTail_eq_vector]

theorem heHuEvenFirstTail_leadingOrders (d : Kˣ) :
    AlternatingEndpointLeadingOrdersAt (pairs := 2)
      (heHuEvenFirstTail (K := K) d) (1 : Kˣ) := by
  intro t
  fin_cases t <;>
    simp [heHuEvenFirstTail_eq_vector]

/-- Every integral rank-four BONG with the exact `0,-2e,0,-2e` profile is
isotropic.  Its signed determinant chooses between `H ⊥ H` and
`H ⊥ [1,-Delta]`; both contain a hyperbolic plane. -/
theorem heHuRankFour_endpoint_isotropic
    (c : GoodBONG q L 4) (hIntegral : Lattice.IsIntegral q L)
    (hzero : c.order 0 = 0)
    (hone : c.order 1 = -(2 * (ramificationIndex K : Int)))
    (htwo : c.order 2 = 0)
    (hthree : c.order 3 = -(2 * (ramificationIndex K : Int))) :
    DiagonalIsotropic (diagonalUnitCoefficients c.valueUnit) := by
  let _ := hIntegral
  have horders : ∀ t : Fin 2,
      c.order ⟨2 * t.val, by omega⟩ = 0 ∧
        c.order ⟨2 * t.val + 1, by omega⟩ =
          -(2 * (ramificationIndex K : Int)) := by
    intro t
    fin_cases t
    · exact ⟨hzero, hone⟩
    · exact ⟨htwo, hthree⟩
  have hcClasses := c.heHuAlternatingPairClasses_of_orders
    (pairs := 2) horders
  have hcOrders := c.heHuAlternatingLeadingOrders_of_orders
    (pairs := 2) horders
  rcases AlternatingEndpointTower.signedDeterminant_cases (pairs := 2) c.valueUnit
      hcClasses with hsquare | hdiscriminant
  · let target := heHuEvenFirstTail (K := K) (1 : Kˣ)
    have htargetClasses : AlternatingEndpointPairClasses (pairs := 2) target := by
      simpa only [target] using heHuEvenFirstTail_one_pairClasses (K := K)
    have htargetOrders :
        AlternatingEndpointLeadingOrdersAt (pairs := 2) target (1 : Kˣ) := by
      simpa only [target] using
        heHuEvenFirstTail_leadingOrders (K := K) (1 : Kˣ)
    have hdet : IsSquare
        (diagonalUnitDeterminant c.valueUnit *
          diagonalUnitDeterminant target) := by
      simpa [AlternatingEndpointTower.signedDeterminant, target,
        diagonalUnitDeterminant, heHuEvenFirstTail_eq_vector,
        Fin.prod_univ_four] using hsquare
    have hrep := alternatingEndpointTower_equalDeterminantRepresentation
      (pairs := 2)
      c.valueUnit target (1 : Kˣ) hcClasses htargetClasses hcOrders
        htargetOrders hdet
    exact hrep.isotropic_of (by
      simpa only [target] using
        heHuEvenFirstTail_isotropic (K := K) (1 : Kˣ))
  · let delta :=
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    let target := heHuEvenFirstTail (K := K) delta
    have htargetClasses : AlternatingEndpointPairClasses (pairs := 2) target := by
      simpa only [target, delta] using
        heHuEvenFirstTail_discriminant_pairClasses (K := K)
    have htargetOrders :
        AlternatingEndpointLeadingOrdersAt (pairs := 2) target (1 : Kˣ) := by
      simpa only [target] using
        heHuEvenFirstTail_leadingOrders (K := K) delta
    have hdet : IsSquare
        (diagonalUnitDeterminant c.valueUnit *
          diagonalUnitDeterminant target) := by
      simpa [AlternatingEndpointTower.signedDeterminant, target, delta,
        diagonalUnitDeterminant, heHuEvenFirstTail_eq_vector,
        Fin.prod_univ_four] using hdiscriminant
    have hrep := alternatingEndpointTower_equalDeterminantRepresentation
      (pairs := 2)
      c.valueUnit target (1 : Kˣ) hcClasses htargetClasses hcOrders
        htargetOrders hdet
    exact hrep.isotropic_of (by
      simpa only [target] using heHuEvenFirstTail_isotropic (K := K) delta)

/-- Cyclically move the third coordinate of a ternary diagonal form to the
front. -/
def heHuFinThreeRotate : Equiv.Perm (Fin 3) where
  toFun i := ![(2 : Fin 3), (0 : Fin 3), (1 : Fin 3)] i
  invFun i := ![(1 : Fin 3), (2 : Fin 3), (0 : Fin 3)] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

noncomputable def heHuLemma712SourceToOddSecondFactors : Fin 3 → Kˣ :=
  ![1, 1, Lattice.dyadicHalfUnit (K := K)]

/-- After a cyclic reindexing, the literal Lemma 7.12 source differs from
the even-valuation odd Table 1 row only by the square `(1/2)^2` in its
last coordinate. -/
theorem heHuLemma712SourceValues_eq_oddSecondRotate_mul_square
    (δ : Kˣ) (i : Fin 3) :
    lemma712SourceValues
        (heHuLemma39iiiSourceUnary (K := K) δ)
        (uniformizerPowerUnit K 1) i =
      (heHuOddSecondTailEven (K := K) δ ∘ heHuFinThreeRotate) i *
        heHuLemma712SourceToOddSecondFactors (K := K) i ^ 2 := by
  fin_cases i
  · simp [lemma712SourceValues, heHuLemma39iiiSourceUnary,
      heHuOddSecondTailEven, heHuFinThreeRotate,
      heHuLemma712SourceToOddSecondFactors]
  · simp [lemma712SourceValues, heHuOddSecondTailEven,
      heHuFinThreeRotate, heHuLemma712SourceToOddSecondFactors]
  · apply Units.ext
    simp [lemma712SourceValues, lemma712DiscriminantParameter,
      negativeQuarterUnit, heHuOddSecondTailEven, heHuFinThreeRotate,
      heHuLemma712SourceToOddSecondFactors, Lattice.dyadicHalfUnit,
      Lattice.dyadicTwoUnit]
    ring

/-- The normalized unary--binary source used in Lemma 3.9(iii) is the
anisotropic even-valuation odd Table 1 space. -/
theorem heHuLemma712Source_diagonalRepresents_oddSecondTailEven
    (δ : Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (lemma712SourceValues
          (heHuLemma39iiiSourceUnary (K := K) δ)
          (uniformizerPowerUnit K 1)))
      (diagonalUnitCoefficients (heHuOddSecondTailEven (K := K) δ)) := by
  have hscale :=
    Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square
      (lemma712SourceValues
        (heHuLemma39iiiSourceUnary (K := K) δ)
        (uniformizerPowerUnit K 1))
      (heHuOddSecondTailEven (K := K) δ ∘ heHuFinThreeRotate)
      (heHuLemma712SourceToOddSecondFactors (K := K))
      (heHuLemma712SourceValues_eq_oddSecondRotate_mul_square
        (K := K) δ)
  have hrotate := diagonalRepresents_reindex
    (diagonalUnitCoefficients (heHuOddSecondTailEven (K := K) δ))
    heHuFinThreeRotate
  have hrotate' : DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuOddSecondTailEven (K := K) δ ∘ heHuFinThreeRotate))
      (diagonalUnitCoefficients (heHuOddSecondTailEven (K := K) δ)) := by
    change DiagonalRepresents
      ((diagonalUnitCoefficients
        (heHuOddSecondTailEven (K := K) δ)) ∘ heHuFinThreeRotate)
      (diagonalUnitCoefficients (heHuOddSecondTailEven (K := K) δ))
    exact hrotate
  exact hscale.trans hrotate'

/-- The literal unit-row candidate of Lemma 3.11(ii) has the quadratic
space printed in the even-valuation row of Table 1.  This equal-rank
identification is separated from anisotropy so that Lemma 5.11 can lift it
through Lemma 3.10 to the full odd-dimensional test lattice. -/
theorem heHuLemma311OddSecondUnitTail_represents_oddSecondTailEven
    [GoodBONGClassificationLaws.{u, u, u} K]
    (δ κ : Kˣ)
    (hδ : IsValuationUnit K (δ : K))
    (hκ : IsValuationUnit K (κ : K))
    (hκDefect : defectOrder (K := K) κ =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuLemma311OddSecondUnitTail
          δ κ hδ hκ hκDefect).valueUnit)
      (diagonalUnitCoefficients
        (heHuOddSecondTailEven (K := K) δ)) := by
  let hc := heHuSharpDomain_of_defect_twoE_sub_one κ hκDefect
  let κSharp := heHuSharp κ hc
  let a := heHuLemma39iiiSourceUnary (K := K) δ
  let p := uniformizerPowerUnit K 1
  let ε := heHuLemma39iiiEpsilon (K := K) κSharp
  let η := heHuLemma39iiiEta (K := K) κ
  let b := heHuLemma311OddSecondUnitTail δ κ hδ hκ hκDefect
  have hsharp := heHu2022Proposition32 κ hc
  have hdeltaOrder : ordUnit K
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit).1
        ((inferInstance : DyadicDiscriminantClassLaws K)
          |>.discriminant_isValuationUnit)
  have hδOrder : ordUnit K δ = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ
  have haOrder : ordUnit K a = 0 := by
    dsimp only [a, heHuLemma39iiiSourceUnary]
    rw [ordUnit_mul, hdeltaOrder, hδOrder]
    simp
  have hp : ordUnit K p = ordUnit K a + 1 := by
    dsimp only [p]
    rw [ordUnit_uniformizerPowerUnit, haOrder]
    norm_num
  have hεUnit : IsValuationUnit K (ε : K) := by
    dsimp only [ε]
    exact heHuLemma39iiiEpsilon_isValuationUnit κSharp hsharp.1
  have hηUnit : IsValuationUnit K (η : K) := by
    dsimp only [η]
    exact heHuLemma39iiiEta_isValuationUnit κ hκ
  have hεηHilbert : hilbertSymbol K ε η = -1 := by
    dsimp only [ε, η]
    exact heHuLemma39iiiEpsilonEta_hilbert
      κ κSharp hκ hsharp.1 hsharp.2.2
  have hpublishedNormalized :=
    heHuLemma39iiiValues_diagonalRepresents_normalized
      (K := K) δ κ κSharp
  have hnormalizedSource := lemma712Target_diagonalRepresents_source
    a p ε η hp hεUnit hηUnit hεηHilbert
  have hcandidateSource : DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients
        (lemma712SourceValues a p)) := by
    have hbValues : b.valueUnit =
        heHuLemma39iiiValues (K := K) δ κ κSharp := by
      funext i
      dsimp only [b, κSharp, hc]
      exact heHuLemma311OddSecondUnitTail_valueUnit
        δ κ hδ hκ hκDefect i
    rw [hbValues]
    exact hpublishedNormalized.trans_exact hnormalizedSource
  have hsourceTarget :=
    heHuLemma712Source_diagonalRepresents_oddSecondTailEven
      (K := K) δ
  have hcandidateTarget : DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heHuOddSecondTailEven (K := K) δ)) := by
    simpa only [a, p] using
      hcandidateSource.trans_exact hsourceTarget
  exact hcandidateTarget

/-- The ternary candidate in the unit row of the odd second column is the
anisotropic Table 1 space `[pi,-Delta*pi,Delta*delta]`. -/
theorem heHuLemma311OddSecondUnitTail_anisotropic
    [GoodBONGClassificationLaws.{u, u, u} K]
    (δ κ : Kˣ)
    (hδ : IsValuationUnit K (δ : K))
    (hκ : IsValuationUnit K (κ : K))
    (hκDefect : defectOrder (K := K) κ =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    DiagonalAnisotropic
      (diagonalUnitCoefficients
        (heHuLemma311OddSecondUnitTail
          δ κ hδ hκ hκDefect).valueUnit) := by
  have hcandidateTarget :=
    heHuLemma311OddSecondUnitTail_represents_oddSecondTailEven
      δ κ hδ hκ hκDefect
  apply hcandidateTarget.anisotropic_of
  apply heHuOddSecondTailEven_anisotropic δ
  refine ⟨0, ?_⟩
  rw [(isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ]
  norm_num

/-- Every integral rank-three BONG with profile `0,-2e,0` is isotropic.
Proposition 2.7(v) identifies its full diagonal space with a hyperbolic
endpoint pair followed by one valuation-unit line. -/
theorem heHuRankThree_endpoint_isotropic
    (c : GoodBONG q L 3) (hIntegral : Lattice.IsIntegral q L)
    (hzero : c.order 0 = 0)
    (hone : c.order 1 = -(2 * (ramificationIndex K : Int)))
    (htwo : c.order 2 = 0) :
    DiagonalIsotropic (diagonalUnitCoefficients c.valueUnit) := by
  let _ := hzero
  let j : Fin 3 := ⟨1, by omega⟩
  have hjOdd : Odd j.val := by
    simp [j]
  have hnext : j.val + 1 < 3 := by
    simp [j]
  have hnextEven : Even (c.order ⟨j.val + 1, hnext⟩) := by
    have hindex : (⟨j.val + 1, hnext⟩ : Fin 3) = 2 := by
      apply Fin.ext
      rfl
    rw [hindex, htwo]
    exact Even.zero
  have C := c.heHu2022Proposition27v hIntegral j hjOdd (by
      change c.order (1 : Fin 3) =
        -(2 * (ramificationIndex K : Int))
      exact hone) hnext hnextEven
  rcases C with ⟨w⟩
  rcases w with
    ⟨pairs, hpairCount, hextended, epsilon, squareFactor,
      hepsilonUnit, hepsilonClass, hnormal⟩
  have hpairs : pairs = 1 := by omega
  subst pairs
  have hnormal' :
      (c.prefixDiagonalSpace 3 (Nat.le_refl 3)).IsIsometric
        (AlternatingEndpointTower.hyperbolicEndpointTowerWithLineSpace
          (K := K) 1 epsilon) := by
    simpa using hnormal
  rcases hnormal' with ⟨f⟩
  have hdiag : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.snoc
          (AlternatingEndpointTower.standardHyperbolicEndpointTower
          (K := K) 1) epsilon))
      (diagonalUnitCoefficients c.valueUnit) := by
    refine ⟨f.symm.toLinearEquiv.toLinearMap,
      f.symm.toLinearEquiv.injective, ?_⟩
    intro x
    have hq := f.symm.map_quadratic x
    have hpref : c.prefixValues 3 (Nat.le_refl 3) =
        diagonalUnitCoefficients c.valueUnit := by
      funext i
      rfl
    have hq' : diagonalQuadratic
        (c.prefixValues 3 (Nat.le_refl 3))
        (f.symm.toLinearEquiv x) =
      diagonalQuadratic
        (diagonalUnitCoefficients
          (Fin.snoc
            (AlternatingEndpointTower.standardHyperbolicEndpointTower
              (K := K) 1) epsilon)) x := by
      simpa only [BONG.GoodBONG.prefixDiagonalSpace,
        AlternatingEndpointTower.hyperbolicEndpointTowerWithLineSpace,
        QuadraticSpace.finiteDiagonal_quadratic_apply,
        diagonalUnitCoefficients] using hq
    rw [hpref] at hq'
    exact hq'
  have hsourceIsotropic : DiagonalIsotropic
      (diagonalUnitCoefficients
        (Fin.snoc
          (AlternatingEndpointTower.standardHyperbolicEndpointTower
            (K := K) 1) epsilon)) := by
    have hfamily :
        Fin.snoc
          (AlternatingEndpointTower.standardHyperbolicEndpointTower
            (K := K) 1) epsilon = heHuOddFirstTail (K := K) epsilon := by
      funext i
      fin_cases i
      · change (1 : Kˣ) = 1
        exact AlternatingEndpointTower.standardHyperbolicEndpointTower_even
          (K := K) (0 : Fin 1)
      · change (-1 : Kˣ) = -1
        exact AlternatingEndpointTower.standardHyperbolicEndpointTower_odd
          (K := K) (0 : Fin 1)
      · rfl
    rw [hfamily]
    exact heHuOddFirstTail_isotropic (K := K) epsilon
  exact hdiag.isotropic_of hsourceIsotropic

end BONG.GoodBONG

/-! ## Explicit noncritical rows of Table 2 -/

namespace BONG.GoodBONG

variable {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

@[simp]
theorem heHuUnitDefectTailGoodBONG_adjacentDefect
    [QuadraticDefectLaws K]
    (a c : Kˣ) (d : Int)
    (ha : IsValuationUnit K (a : K))
    (hc : IsValuationUnit K (c : K))
    (hdOdd : Odd d)
    (hdNonneg : 0 ≤ d)
    (hdLt : d < 2 * (ramificationIndex K : Int))
    (hcDefect : defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    (heHuUnitDefectTailGoodBONG a c d ha hc hdOdd hdNonneg hdLt
      hcDefect).adjacentDefect 0 =
        (((d : Int) : ℚ) : WithTop ℚ) := by
  let b := heHuUnitDefectTailGoodBONG
    a c d ha hc hdOdd hdNonneg hdLt hcDefect
  rw [b.binary_adjacentDefect_eq_parameterDefect]
  unfold BONG.binaryParameter
  dsimp only [b]
  unfold heHuUnitDefectTailGoodBONG
  change defectOrder (K := K)
      (-((binaryDiagonalExactGoodBONG
          (heHuUnitDefectTailValues (K := K) a c d 0)
          (heHuUnitDefectTailValues (K := K) a c d 1)
          (heHuUnitDefectTail_admissible a c d ha hc hdOdd hdNonneg hdLt
            hcDefect)).valueUnit 1 /
        (binaryDiagonalExactGoodBONG
          (heHuUnitDefectTailValues (K := K) a c d 0)
          (heHuUnitDefectTailValues (K := K) a c d 1)
          (heHuUnitDefectTail_admissible a c d ha hc hdOdd hdNonneg hdLt
            hcDefect)).valueUnit 0)) = _
  rw [binaryDiagonalExactGoodBONG_valueUnit,
    binaryDiagonalExactGoodBONG_valueUnit]
  exact heHuUnitDefectTail_negativeParameter_defect
    a c d hdOdd hcDefect

@[simp]
theorem heHuUnitUniformizerPairGoodBONG_adjacentDefect
    (a δ : Kˣ)
    (ha : IsValuationUnit K (a : K))
    (hδ : IsValuationUnit K (δ : K)) :
    (heHuUnitUniformizerPairGoodBONG a δ ha hδ).adjacentDefect 0 = 0 := by
  let b := heHuUnitUniformizerPairGoodBONG a δ ha hδ
  rw [b.binary_adjacentDefect_eq_parameterDefect]
  unfold BONG.binaryParameter
  dsimp only [b]
  unfold heHuUnitUniformizerPairGoodBONG
  change defectOrder (K := K)
      (-((binaryDiagonalExactGoodBONG
          (heHuUnitUniformizerPairValues (K := K) a δ 0)
          (heHuUnitUniformizerPairValues (K := K) a δ 1)
          (heHuUnitUniformizerPair_admissible a δ ha hδ)).valueUnit 1 /
        (binaryDiagonalExactGoodBONG
          (heHuUnitUniformizerPairValues (K := K) a δ 0)
          (heHuUnitUniformizerPairValues (K := K) a δ 1)
          (heHuUnitUniformizerPair_admissible a δ ha hδ)).valueUnit 0)) = 0
  rw [binaryDiagonalExactGoodBONG_valueUnit,
    binaryDiagonalExactGoodBONG_valueUnit]
  have hparameter :
      -(heHuUnitUniformizerPairValues (K := K) a δ 1 /
          heHuUnitUniformizerPairValues (K := K) a δ 0) =
        δ * uniformizerPowerUnit K 1 := by
    apply Units.ext
    simp [heHuUnitUniformizerPairValues]
    field_simp
  change defectOrder (K := K)
    (-(heHuUnitUniformizerPairValues (K := K) a δ 1 /
      heHuUnitUniformizerPairValues (K := K) a δ 0)) = 0
  rw [hparameter]
  unfold defectOrder
  rw [quadraticDefect_eq_zero_of_odd_ordUnit]
  · rfl
  · rw [ordUnit_mul,
      (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ,
      ordUnit_uniformizerPowerUnit]
    exact odd_one

/-- Proposition 3.7, even first column, square row:
`H^(k+1)` is maximal. -/
theorem heHu2022Proposition37EvenFirstOne (k : Nat) :
    let r := (QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
      (Lattice.dyadicHalfUnit (K := K))
    let b := heHuHyperbolicHeadGoodBONG (K := K)
    let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuHyperbolicHeadGoodBONG_order_zero])
    Lattice.IsOMaximal
      (Lattice.halfHyperbolicExtensionForm r k)
      (Lattice.halfHyperbolicExtensionLattice
        (Lattice.hyperbolicPlaneLattice (K := K)) k) := by
  dsimp only
  let b := heHuHyperbolicHeadGoodBONG (K := K)
  have hIntegral : Lattice.IsIntegral _
      (Lattice.hyperbolicPlaneLattice (K := K)) :=
    heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuHyperbolicHeadGoodBONG_order_zero])
  have hvolume : Lattice.volumeOrder
      ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
        (Lattice.dyadicHalfUnit (K := K)))
      (Lattice.hyperbolicPlaneLattice (K := K)) =
        -(2 * (ramificationIndex K : Int)) := by
    rw [b.toBONG.volumeOrder_eq_sum_order, Fin.sum_univ_two]
    change b.order 0 + b.order 1 = _
    rw [heHuHyperbolicHeadGoodBONG_order_zero,
      heHuHyperbolicHeadGoodBONG_order_one]
    omega
  exact (heHuRankTwo_isOMaximal_of_volume_lower b hIntegral hvolume)
    |>.halfHyperbolicExtension k

/-- Proposition 3.7, even first column, discriminant row:
`H^k ⊥ 2⁻¹A(2,2rho)` is maximal. -/
theorem heHu2022Proposition37EvenFirstDelta
    [DyadicDiscriminantClassLaws K] (k : Nat) :
    let r := BONG.binaryDiagonalModelSpace
      (heHuDiscriminantEndpointValues (K := K) 0 0)
      (heHuDiscriminantEndpointValues (K := K) 0 1)
      (heHuDiscriminantEndpoint_admissible (K := K) 0)
    let b := heHuDiscriminantEndpointGoodBONG (K := K) 0
    let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuDiscriminantEndpointGoodBONG_order]
      norm_num)
    Lattice.IsOMaximal
      (Lattice.halfHyperbolicExtensionForm r k)
      (Lattice.halfHyperbolicExtensionLattice
        (BONG.binaryDiagonalModelLattice (K := K)) k) := by
  dsimp only
  let b := heHuDiscriminantEndpointGoodBONG (K := K) 0
  have hIntegral : Lattice.IsIntegral _
      (BONG.binaryDiagonalModelLattice (K := K)) :=
    heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuDiscriminantEndpointGoodBONG_order]
      norm_num)
  have hvolume : Lattice.volumeOrder
      (BONG.binaryDiagonalModelSpace
        (heHuDiscriminantEndpointValues (K := K) 0 0)
        (heHuDiscriminantEndpointValues (K := K) 0 1)
        (heHuDiscriminantEndpoint_admissible (K := K) 0))
      (BONG.binaryDiagonalModelLattice (K := K)) =
        -(2 * (ramificationIndex K : Int)) := by
    rw [b.toBONG.volumeOrder_eq_sum_order, Fin.sum_univ_two]
    change b.order 0 + b.order 1 = _
    rw [heHuDiscriminantEndpointGoodBONG_order,
      heHuDiscriminantEndpointGoodBONG_order]
    norm_num
  exact (heHuRankTwo_isOMaximal_of_volume_lower b hIntegral hvolume)
    |>.halfHyperbolicExtension k

/-- Proposition 3.7, even second column, square row.  The residual
quaternary lattice has the anisotropic Table 1 space and is maximal. -/
theorem heHu2022Proposition37EvenSecondOne (k : Nat) :
    let r :=
      (BONG.binaryDiagonalModelSpace
        (heHuDiscriminantEndpointValues (K := K) 0 0)
        (heHuDiscriminantEndpointValues (K := K) 0 1)
        (heHuDiscriminantEndpoint_admissible (K := K) 0)).orthogonalSum
      (BONG.binaryDiagonalModelSpace
        (heHuDiscriminantEndpointValues (K := K) 1 0)
        (heHuDiscriminantEndpointValues (K := K) 1 1)
        (heHuDiscriminantEndpoint_admissible (K := K) 1))
    let M := Lattice.product
      (BONG.binaryDiagonalModelLattice (K := K))
      (BONG.binaryDiagonalModelLattice (K := K))
    let b := heHuLemma311EvenSecondOneTail (K := K)
    let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuLemma311EvenSecondOneTail_order]
      norm_num)
    Lattice.IsOMaximal
      (Lattice.halfHyperbolicExtensionForm r k)
      (Lattice.halfHyperbolicExtensionLattice M k) := by
  dsimp only
  let b := heHuLemma311EvenSecondOneTail (K := K)
  have hIntegral : Lattice.IsIntegral _
      (Lattice.product
        (BONG.binaryDiagonalModelLattice (K := K))
        (BONG.binaryDiagonalModelLattice (K := K))) :=
    heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuLemma311EvenSecondOneTail_order]
      norm_num)
  have hvolume : Lattice.volumeOrder
      ((BONG.binaryDiagonalModelSpace
        (heHuDiscriminantEndpointValues (K := K) 0 0)
        (heHuDiscriminantEndpointValues (K := K) 0 1)
        (heHuDiscriminantEndpoint_admissible (K := K) 0)).orthogonalSum
      (BONG.binaryDiagonalModelSpace
        (heHuDiscriminantEndpointValues (K := K) 1 0)
        (heHuDiscriminantEndpointValues (K := K) 1 1)
        (heHuDiscriminantEndpoint_admissible (K := K) 1)))
      (Lattice.product
        (BONG.binaryDiagonalModelLattice (K := K))
        (BONG.binaryDiagonalModelLattice (K := K))) =
        2 - 4 * (ramificationIndex K : Int) := by
    rw [b.toBONG.volumeOrder_eq_sum_order, Fin.sum_univ_four]
    change b.order 0 + b.order 1 + b.order 2 + b.order 3 = _
    rw [heHuLemma311EvenSecondOneTail_order,
      heHuLemma311EvenSecondOneTail_order,
      heHuLemma311EvenSecondOneTail_order,
      heHuLemma311EvenSecondOneTail_order]
    simp
    ring
  have hmax := heHuRankFour_isOMaximal_of_excluding_endpoint
    b hIntegral hvolume (by
      intro N c hN hzero hone htwo hthree
      have hcIsotropic := c.heHuRankFour_endpoint_isotropic
        hN hzero hone htwo hthree
      have hbc : DiagonalRepresents
          (diagonalUnitCoefficients b.valueUnit)
          (diagonalUnitCoefficients c.valueUnit) := by
        exact b.toBONG.diagonalRepresents_values c.toBONG
      have hbIsotropic : DiagonalIsotropic
          (diagonalUnitCoefficients b.valueUnit) :=
        hbc.symm_of_sameRank.isotropic_of hcIsotropic
      exact ((not_diagonalIsotropic_iff_diagonalAnisotropic
        (diagonalUnitCoefficients b.valueUnit)).2
          (heHuLemma311EvenSecondOneTail_anisotropic (K := K)))
            hbIsotropic)
  exact hmax.halfHyperbolicExtension k

/-- Proposition 3.7, even second column, discriminant row.  The candidate
binary space is `W_2^2(Delta)`.  A proper integral over-lattice would have
the endpoint profile `0,-2e`, hence would lie in the other binary class
`W_1^2(Delta)`, contradicting Proposition 3.5. -/
theorem heHu2022Proposition37EvenSecondDelta (k : Nat) :
    let r := BONG.binaryDiagonalModelSpace
      (heHuDiscriminantEndpointValues (K := K) 1 0)
      (heHuDiscriminantEndpointValues (K := K) 1 1)
      (heHuDiscriminantEndpoint_admissible (K := K) 1)
    let b := heHuDiscriminantEndpointGoodBONG (K := K) 1
    let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuDiscriminantEndpointGoodBONG_order]
      norm_num)
    Lattice.IsOMaximal
      (Lattice.halfHyperbolicExtensionForm r k)
      (Lattice.halfHyperbolicExtensionLattice
        (BONG.binaryDiagonalModelLattice (K := K)) k) := by
  dsimp only
  let b := heHuDiscriminantEndpointGoodBONG (K := K) 1
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let first := heHuBinaryFirst (K := K) delta
  let second := heHuDiscriminantBinary (K := K) delta
  have hdeltaNotSquare : ¬ IsSquare delta := by
    dsimp only [delta]
    exact AlternatingEndpointNormalization.discriminantUnit_not_isSquare
      (K := K)
  have hdefined : HeHuEvenSecondDefined (K := K) 0 delta := by
    right
    exact hdeltaNotSquare
  have Praw := heHu2022Definition34Proposition35Even
    (K := K) 0 delta hdefined
  have hdeltaClass : IsSquare
      (delta /
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit) := by
    dsimp only [delta]
    simp
  have hsecondEq : heHuEvenSecond (K := K) 0 delta hdefined = second := by
    rw [heHuEvenSecond_zero_of_discriminant delta hdefined hdeltaClass]
  have P : HeHuSpacePairProperties first second := by
    rw [hsecondEq] at Praw
    simpa only [first, second, heHuEvenFirst] using Praw
  have hIntegral : Lattice.IsIntegral _
      (BONG.binaryDiagonalModelLattice (K := K)) :=
    heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuDiscriminantEndpointGoodBONG_order]
      norm_num)
  have hvolume : Lattice.volumeOrder
      (BONG.binaryDiagonalModelSpace
        (heHuDiscriminantEndpointValues (K := K) 1 0)
        (heHuDiscriminantEndpointValues (K := K) 1 1)
        (heHuDiscriminantEndpoint_admissible (K := K) 1))
      (BONG.binaryDiagonalModelLattice (K := K)) =
        2 - 2 * (ramificationIndex K : Int) := by
    rw [b.toBONG.volumeOrder_eq_sum_order, Fin.sum_univ_two]
    change b.order 0 + b.order 1 = _
    rw [heHuDiscriminantEndpointGoodBONG_order,
      heHuDiscriminantEndpointGoodBONG_order]
    norm_num
    ring
  have hmax := heHuRankTwo_isOMaximal_of_excluding_endpoint
    b hIntegral hvolume (by
      intro N c hN hzero hone
      have horders : ∀ t : Fin 1,
          c.order ⟨2 * t.val, by omega⟩ = 0 ∧
            c.order ⟨2 * t.val + 1, by omega⟩ =
              -(2 * (ramificationIndex K : Int)) := by
        intro t
        fin_cases t
        exact ⟨hzero, hone⟩
      have hcClasses := c.heHuAlternatingPairClasses_of_orders
        (pairs := 1) horders
      have hcOrders := c.heHuAlternatingLeadingOrders_of_orders
        (pairs := 1) horders
      have hfirstClasses : AlternatingEndpointPairClasses
          (pairs := 1) first := by
        intro t
        fin_cases t
        right
        refine ⟨delta, ?_⟩
        simp [first, delta, heHuBinaryFirst]
      have hfirstOrders : AlternatingEndpointLeadingOrdersAt
          (pairs := 1) first (1 : Kˣ) := by
        intro t
        fin_cases t
        simp [first, heHuBinaryFirst]
      have hstandardEq :
          heHuDiscriminantEndpointStandardValues (K := K) 1 = second := by
        funext i
        fin_cases i <;>
          simp [second, delta, heHuDiscriminantBinary, heHuBinaryTwist,
            heHuDiscriminantEndpointStandardValues, mul_comm]
      have hbSecond : DiagonalRepresents
          (diagonalUnitCoefficients b.valueUnit)
          (diagonalUnitCoefficients second) := by
        have hstandard :=
          heHuDiscriminantEndpointGoodBONG_diagonalRepresents_standard
            (K := K) 1
        rw [hstandardEq] at hstandard
        exact hstandard
      have hbc : DiagonalRepresents
          (diagonalUnitCoefficients b.valueUnit)
          (diagonalUnitCoefficients c.valueUnit) :=
        b.toBONG.diagonalRepresents_values c.toBONG
      have hbcDet := DiagonalIsometryInvariantLaws.determinant_square
        b.valueUnit c.valueUnit hbc
      have hcB : IsSquare
          (diagonalUnitDeterminant c.valueUnit *
            diagonalUnitDeterminant b.valueUnit) := by
        simpa only [mul_comm] using hbcDet
      have hbSecondDet := DiagonalIsometryInvariantLaws.determinant_square
        b.valueUnit second hbSecond
      have hcSecond : IsSquare
          (diagonalUnitDeterminant c.valueUnit *
            diagonalUnitDeterminant second) :=
        isSquare_mul_trans
          (diagonalUnitDeterminant c.valueUnit)
          (diagonalUnitDeterminant b.valueUnit)
          (diagonalUnitDeterminant second) hcB hbSecondDet
      have hcFirst : IsSquare
          (diagonalUnitDeterminant c.valueUnit *
            diagonalUnitDeterminant first) :=
        isSquare_mul_trans
          (diagonalUnitDeterminant c.valueUnit)
          (diagonalUnitDeterminant second)
          (diagonalUnitDeterminant first) hcSecond P.determinantSquare
      have hfirstC := alternatingEndpointTower_equalDeterminantRepresentation
        (pairs := 1) c.valueUnit first (1 : Kˣ)
          hcClasses hfirstClasses hcOrders hfirstOrders hcFirst
      have hcFirstRep : DiagonalRepresents
          (diagonalUnitCoefficients c.valueUnit)
          (diagonalUnitCoefficients first) :=
        hfirstC.symm_of_sameRank
      have hsecondFirst : DiagonalRepresents
          (diagonalUnitCoefficients second)
          (diagonalUnitCoefficients first) :=
        hbSecond.symm_of_sameRank.trans_exact hbc |>.trans_exact hcFirstRep
      exact P.nonisometric hsecondFirst)
  exact hmax.halfHyperbolicExtension k

/-- Proposition 3.7, both generic even binary rows. -/
theorem heHu2022Proposition37EvenGeneric
    [QuadraticDefectLaws K]
    (a c : Kˣ) (d : Int)
    (ha : IsValuationUnit K (a : K))
    (hc : IsValuationUnit K (c : K))
    (hdOdd : Odd d)
    (hdNonneg : 0 ≤ d)
    (hdLt : d < 2 * (ramificationIndex K : Int))
    (hcDefect : defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ)) (k : Nat) :
    let r := BONG.binaryDiagonalModelSpace
      (heHuUnitDefectTailValues (K := K) a c d 0)
      (heHuUnitDefectTailValues (K := K) a c d 1)
      (heHuUnitDefectTail_admissible a c d ha hc hdOdd hdNonneg hdLt
        hcDefect)
    let b := heHuUnitDefectTailGoodBONG
      a c d ha hc hdOdd hdNonneg hdLt hcDefect
    let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuUnitDefectTailGoodBONG_order]
      norm_num)
    Lattice.IsOMaximal
      (Lattice.halfHyperbolicExtensionForm r k)
      (Lattice.halfHyperbolicExtensionLattice
        (BONG.binaryDiagonalModelLattice (K := K)) k) := by
  dsimp only
  let b := heHuUnitDefectTailGoodBONG
    a c d ha hc hdOdd hdNonneg hdLt hcDefect
  have hIntegral : Lattice.IsIntegral _
      (BONG.binaryDiagonalModelLattice (K := K)) :=
    heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuUnitDefectTailGoodBONG_order]
      norm_num)
  have hvolume : Lattice.volumeOrder
      (BONG.binaryDiagonalModelSpace
        (heHuUnitDefectTailValues (K := K) a c d 0)
        (heHuUnitDefectTailValues (K := K) a c d 1)
        (heHuUnitDefectTail_admissible a c d ha hc hdOdd hdNonneg hdLt
          hcDefect))
      (BONG.binaryDiagonalModelLattice (K := K)) = 1 - d := by
    rw [b.toBONG.volumeOrder_eq_sum_order, Fin.sum_univ_two]
    change b.order 0 + b.order 1 = _
    rw [heHuUnitDefectTailGoodBONG_order,
      heHuUnitDefectTailGoodBONG_order]
    norm_num
  have hmax := heHuBinary_isOMaximal_of_volume_and_adjacentDefect
    b hIntegral d hvolume
      (heHuUnitDefectTailGoodBONG_adjacentDefect
        a c d ha hc hdOdd hdNonneg hdLt hcDefect)
  exact hmax.halfHyperbolicExtension k

/-- Proposition 3.7, both even `delta*pi` rows. -/
theorem heHu2022Proposition37EvenUnitUniformizer
    (a δ : Kˣ)
    (ha : IsValuationUnit K (a : K))
    (hδ : IsValuationUnit K (δ : K)) (k : Nat) :
    let r := BONG.binaryDiagonalModelSpace
      (heHuUnitUniformizerPairValues (K := K) a δ 0)
      (heHuUnitUniformizerPairValues (K := K) a δ 1)
      (heHuUnitUniformizerPair_admissible a δ ha hδ)
    let b := heHuUnitUniformizerPairGoodBONG a δ ha hδ
    let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuUnitUniformizerPairGoodBONG_orders]
      norm_num)
    Lattice.IsOMaximal
      (Lattice.halfHyperbolicExtensionForm r k)
      (Lattice.halfHyperbolicExtensionLattice
        (BONG.binaryDiagonalModelLattice (K := K)) k) := by
  dsimp only
  let b := heHuUnitUniformizerPairGoodBONG a δ ha hδ
  have hIntegral : Lattice.IsIntegral _
      (BONG.binaryDiagonalModelLattice (K := K)) :=
    heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuUnitUniformizerPairGoodBONG_orders]
      norm_num)
  have hvolume : Lattice.volumeOrder
      (BONG.binaryDiagonalModelSpace
        (heHuUnitUniformizerPairValues (K := K) a δ 0)
        (heHuUnitUniformizerPairValues (K := K) a δ 1)
        (heHuUnitUniformizerPair_admissible a δ ha hδ))
      (BONG.binaryDiagonalModelLattice (K := K)) = 1 := by
    rw [b.toBONG.volumeOrder_eq_sum_order, Fin.sum_univ_two]
    change b.order 0 + b.order 1 = 1
    rw [heHuUnitUniformizerPairGoodBONG_orders,
      heHuUnitUniformizerPairGoodBONG_orders]
    norm_num
  have hmax := heHuBinary_isOMaximal_of_volume_and_adjacentDefect
    b hIntegral 0 (by simpa using hvolume)
      (heHuUnitUniformizerPairGoodBONG_adjacentDefect a δ ha hδ)
  exact hmax.halfHyperbolicExtension k

/-- Proposition 3.7, odd first column, unit row. -/
theorem heHu2022Proposition37OddFirstUnit
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) (k : Nat) :
    let r := QuadraticSpace.rescaleUnit δ (QuadraticSpace.line K)
    let b := BONG.unaryModelGoodBONG δ
    let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
      rw [BONG.unaryModelGoodBONG_order,
        (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ])
    Lattice.IsOMaximal
      (Lattice.halfHyperbolicExtensionForm r k)
      (Lattice.halfHyperbolicExtensionLattice
        (BONG.unaryModelLattice (K := K)) k) := by
  dsimp only
  let b := BONG.unaryModelGoodBONG δ
  have hIntegral : Lattice.IsIntegral _
      (BONG.unaryModelLattice (K := K)) :=
    heHuIntegral_of_firstOrder_nonneg b (by
      rw [BONG.unaryModelGoodBONG_order,
        (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ])
  have horder : b.order 0 ≤ 1 := by
    rw [BONG.unaryModelGoodBONG_order,
      (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ]
    norm_num
  exact (heHuRankOne_isOMaximal_of_order_le_one b hIntegral horder)
    |>.halfHyperbolicExtension k

/-- Proposition 3.7, odd first column, `delta*pi` row. -/
theorem heHu2022Proposition37OddFirstUnitUniformizer
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) (k : Nat) :
    let a := δ * uniformizerPowerUnit K 1
    let r := QuadraticSpace.rescaleUnit a (QuadraticSpace.line K)
    let b := BONG.unaryModelGoodBONG a
    let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
      rw [BONG.unaryModelGoodBONG_order, ordUnit_mul,
        (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ,
        ordUnit_uniformizerPowerUnit]
      norm_num)
    Lattice.IsOMaximal
      (Lattice.halfHyperbolicExtensionForm r k)
      (Lattice.halfHyperbolicExtensionLattice
        (BONG.unaryModelLattice (K := K)) k) := by
  dsimp only
  let a := δ * uniformizerPowerUnit K 1
  let b := BONG.unaryModelGoodBONG a
  have hIntegral : Lattice.IsIntegral _
      (BONG.unaryModelLattice (K := K)) :=
    heHuIntegral_of_firstOrder_nonneg b (by
      rw [BONG.unaryModelGoodBONG_order, ordUnit_mul,
        (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ,
        ordUnit_uniformizerPowerUnit]
      norm_num)
  have horder : b.order 0 ≤ 1 := by
    rw [BONG.unaryModelGoodBONG_order, ordUnit_mul,
      (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ,
      ordUnit_uniformizerPowerUnit]
    norm_num
  exact (heHuRankOne_isOMaximal_of_order_le_one b hIntegral horder)
    |>.halfHyperbolicExtension k

/-- Proposition 3.7, odd second column, unit row.  The residual ternary
lattice is anisotropic, whereas the only volume-lowering endpoint profile
would be isotropic by Proposition 2.7(v). -/
theorem heHu2022Proposition37OddSecondUnit
    [GoodBONGClassificationLaws.{u, u, u} K]
    (δ κ : Kˣ)
    (hδ : IsValuationUnit K (δ : K))
    (hκ : IsValuationUnit K (κ : K))
    (hκDefect : defectOrder (K := K) κ =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ))
    (k : Nat) :
    let r := unaryBinaryModelSpace
      (heHuLemma39iiiSourceUnary (K := K) δ)
      (uniformizerPowerUnit K 1)
      (uniformizerPowerUnit K 1 *
        lemma712DiscriminantParameter (K := K))
      (lemma712_sourceBinaryAdmissible
        (uniformizerPowerUnit K 1))
    let M := unaryBinaryModelLattice (K := K)
    let b := heHuLemma311OddSecondUnitTail δ κ hδ hκ hκDefect
    let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuLemma311OddSecondUnitTail_order]
      norm_num)
    Lattice.IsOMaximal
      (Lattice.halfHyperbolicExtensionForm r k)
      (Lattice.halfHyperbolicExtensionLattice M k) := by
  dsimp only
  let b := heHuLemma311OddSecondUnitTail δ κ hδ hκ hκDefect
  have hIntegral : Lattice.IsIntegral _
      (unaryBinaryModelLattice (K := K)) :=
    heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuLemma311OddSecondUnitTail_order]
      norm_num)
  have hvolume : Lattice.volumeOrder
      (unaryBinaryModelSpace
        (heHuLemma39iiiSourceUnary (K := K) δ)
        (uniformizerPowerUnit K 1)
        (uniformizerPowerUnit K 1 *
          lemma712DiscriminantParameter (K := K))
        (lemma712_sourceBinaryAdmissible
          (uniformizerPowerUnit K 1)))
      (unaryBinaryModelLattice (K := K)) =
        2 - 2 * (ramificationIndex K : Int) := by
    rw [b.toBONG.volumeOrder_eq_sum_order, Fin.sum_univ_three]
    change b.order 0 + b.order 1 + b.order 2 = _
    rw [heHuLemma311OddSecondUnitTail_order,
      heHuLemma311OddSecondUnitTail_order,
      heHuLemma311OddSecondUnitTail_order]
    simp
  have hmax := heHuRankThree_isOMaximal_of_excluding_endpoint
    b hIntegral hvolume (by
      intro N c hN hzero hone htwo
      have hcIsotropic := c.heHuRankThree_endpoint_isotropic
        hN hzero hone htwo
      have hbc : DiagonalRepresents
          (diagonalUnitCoefficients b.valueUnit)
          (diagonalUnitCoefficients c.valueUnit) := by
        exact b.toBONG.diagonalRepresents_values c.toBONG
      have hbIsotropic : DiagonalIsotropic
          (diagonalUnitCoefficients b.valueUnit) :=
        hbc.symm_of_sameRank.isotropic_of hcIsotropic
      exact ((not_diagonalIsotropic_iff_diagonalAnisotropic
        (diagonalUnitCoefficients b.valueUnit)).2
          (heHuLemma311OddSecondUnitTail_anisotropic
            δ κ hδ hκ hκDefect)) hbIsotropic)
  exact hmax.halfHyperbolicExtension k

/-- Proposition 3.7, odd second column, `delta*pi` row. -/
theorem heHu2022Proposition37OddSecondUnitUniformizer
    [DyadicDiscriminantClassLaws K]
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) (k : Nat) :
    let r :=
      (BONG.binaryDiagonalModelSpace
        (heHuDiscriminantEndpointValues (K := K) 0 0)
        (heHuDiscriminantEndpointValues (K := K) 0 1)
        (heHuDiscriminantEndpoint_admissible (K := K) 0)).orthogonalSum
          (QuadraticSpace.rescaleUnit
            (heHuLemma311OddSecondUnitUniformizerValue δ)
            (QuadraticSpace.line K))
    let M := Lattice.product
      (BONG.binaryDiagonalModelLattice (K := K))
      (BONG.unaryModelLattice (K := K))
    let b := heHuLemma311OddSecondUnitUniformizerTail δ hδ
    let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuLemma311OddSecondUnitUniformizerTail_order]
      norm_num)
    Lattice.IsOMaximal
      (Lattice.halfHyperbolicExtensionForm r k)
      (Lattice.halfHyperbolicExtensionLattice M k) := by
  dsimp only
  let b := heHuLemma311OddSecondUnitUniformizerTail δ hδ
  have hIntegral : Lattice.IsIntegral _
      (Lattice.product
        (BONG.binaryDiagonalModelLattice (K := K))
        (BONG.unaryModelLattice (K := K))) :=
    heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuLemma311OddSecondUnitUniformizerTail_order]
      norm_num)
  have hvolume : Lattice.volumeOrder
      ((BONG.binaryDiagonalModelSpace
        (heHuDiscriminantEndpointValues (K := K) 0 0)
        (heHuDiscriminantEndpointValues (K := K) 0 1)
        (heHuDiscriminantEndpoint_admissible (K := K) 0)).orthogonalSum
          (QuadraticSpace.rescaleUnit
            (heHuLemma311OddSecondUnitUniformizerValue δ)
            (QuadraticSpace.line K)))
      (Lattice.product
        (BONG.binaryDiagonalModelLattice (K := K))
        (BONG.unaryModelLattice (K := K))) =
      1 - 2 * (ramificationIndex K : Int) := by
    rw [b.toBONG.volumeOrder_eq_sum_order, Fin.sum_univ_three]
    change b.order 0 + b.order 1 + b.order 2 = _
    rw [heHuLemma311OddSecondUnitUniformizerTail_order,
      heHuLemma311OddSecondUnitUniformizerTail_order,
      heHuLemma311OddSecondUnitUniformizerTail_order]
    simp
    ring
  exact
    (heHuRankThree_isOMaximal_of_volume_le_lower_add_one
      b hIntegral (le_of_eq hvolume)).halfHyperbolicExtension k

end BONG.GoodBONG

end Bong
