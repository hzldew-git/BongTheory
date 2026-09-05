/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenCentralTrigger
import Bong.Bong.HeHu2022Lemma45

/-!
# Prefix-space geometry for He (2025), Lemma 6.6

The parity alternative uses an arbitrary even next order, not order zero.
The defect alternative selects the specified first-column class from its
raw signed-prefix defect. All representations here are of quadratic spaces.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- An even next order gives a unit-line odd normal form for the prefix. -/
theorem heADCEvenCentral_prefix_oddFirst (k : Nat) (a : GoodBONG q L (2 * k + 4))
    (hIntegral : Lattice.IsIntegral q L)
    (hlast : a.order ⟨2 * k + 1, by omega⟩ = -(2 * (ramificationIndex K : Int)))
    (hnextEven : Even (a.order ⟨2 * k + 2, by omega⟩)) :
    ∃ ε : Kˣ, IsValuationUnit K (ε : K) ∧
      DiagonalRepresents (a.prefixValues (2 * k + 3) (by omega))
        (diagonalUnitCoefficients (heHuOddFirst k ε)) := by
  let j : Fin (2 * k + 4) := ⟨2 * k + 1, by omega⟩
  have hj : Odd j.val := ⟨k, by rfl⟩
  have hnext : j.val + 1 < 2 * k + 4 := by dsimp [j]; omega
  have heven : Even (a.order ⟨j.val + 1, hnext⟩) := by
    simpa only [j, show 2 * k + 1 + 1 = 2 * k + 2 by omega] using hnextEven
  obtain ⟨⟨pairs, hpairs, hbound, ε, s, hε, hclass, hnormal⟩⟩ :=
    a.heHu2022Proposition27v hIntegral j hj hlast hnext heven
  have hp : pairs = k + 1 := by dsimp only [j] at hpairs; omega
  subst pairs
  obtain ⟨f⟩ := hnormal
  refine ⟨ε, hε, ?_⟩
  have hdiag : DiagonalRepresents (a.prefixValues (2 * (k + 1) + 1) hbound)
      (diagonalUnitCoefficients (Fin.snoc
        (AlternatingEndpointTower.standardHyperbolicEndpointTower (K := K) (k + 1)) ε)) := by
    refine ⟨f.toLinearEquiv.toLinearMap, f.toLinearEquiv.injective, ?_⟩
    intro x
    have hq : diagonalQuadratic (diagonalUnitCoefficients (Fin.snoc
        (AlternatingEndpointTower.standardHyperbolicEndpointTower (K := K) (k + 1)) ε))
        (f.toLinearEquiv x) = diagonalQuadratic
          (a.prefixValues (2 * (k + 1) + 1) hbound) x := by
      simpa only [prefixDiagonalSpace,
        AlternatingEndpointTower.hyperbolicEndpointTowerWithLineSpace,
        QuadraticSpace.finiteDiagonal_quadratic_apply, diagonalUnitCoefficients] using
        f.map_quadratic x
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

/-- The raw-defect alternative selects the specified signed determinant class. -/
theorem heADCEvenCentral_signedClass (k : Nat) (a : GoodBONG q L (2 * k + 4))
    (hIntegral : Lattice.IsIntegral q L)
    (hlast : a.order ⟨2 * k + 1, by omega⟩ = -(2 * (ramificationIndex K : Int)))
    (μ : Kˣ)
    (hμ : μ = 1 ∨ μ = (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (hdefect : quadraticDefect K (a.toBONG.signedEvenPrefixProduct (k + 1)) =
      quadraticDefect K μ) :
    IsSquare (a.toBONG.signedEvenPrefixProduct (k + 1) * μ) := by
  rcases hμ with hOne | hDelta
  · subst μ
    rw [mul_one]
    apply (quadraticDefect_eq_top_iff_isSquare K _).mp
    exact hdefect.trans (quadraticDefect_eq_top_of_isSquare (K := K) ⟨1, by simp⟩)
  · have C := a.heHu2022Proposition27iiiiv hIntegral ⟨2 * k + 1, by omega⟩
      (show Odd (2 * k + 1) from ⟨k, rfl⟩) hlast
    obtain ⟨p, hp, hclass⟩ := C.prefixEndpointClass
    have hpk : p = k + 1 := by dsimp at hp; omega
    subst p
    rcases hclass with hsquare | hdelta
    · have htop := quadraticDefect_eq_top_of_isSquare (K := K) hsquare
      have hfinite : quadraticDefect K μ = (2 * ramificationIndex K : Nat) := by
        rw [hDelta]
        exact (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminant_defect
      exact False.elim (ENat.coe_ne_top _ (hfinite.symm.trans (hdefect.symm.trans htop)))
    · simpa only [hDelta, heHuDiscriminantClassLaws] using hdelta

/-- The selected first-column even space embeds in the alternating prefix. -/
theorem heADCEvenCentral_prefix_evenFirst (k : Nat) (a : GoodBONG q L (2 * k + 4))
    (hfirst : a.order 0 = 0)
    (hlast : a.order ⟨2 * k + 1, by omega⟩ = -(2 * (ramificationIndex K : Int)))
    (μ : Kˣ)
    (hμ : μ = 1 ∨ μ = (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (hclass : IsSquare (a.toBONG.signedEvenPrefixProduct (k + 1) * μ)) :
    DiagonalRepresents (diagonalUnitCoefficients (heHuEvenFirst k μ))
      (a.prefixValues (2 * k + 2) (by omega)) := by
  let source := a.prefixValueUnits (2 * (k + 1)) (by omega)
  have hend : a.order ⟨2 * (k + 1) - 1, by omega⟩ =
      0 - 2 * (ramificationIndex K : Int) := by
    simpa only [zero_sub, show 2 * (k + 1) - 1 = 2 * k + 1 by omega] using hlast
  have hs : AlternatingEndpointPairClasses source :=
    a.lemma79_endpointTower_pairClasses 0 (k + 1) (by omega) (by omega) hfirst hend
  have ho : AlternatingEndpointLeadingOrdersAt source (1 : Kˣ) := by
    intro t
    have hone : ordUnit K (1 : Kˣ) = 0 := by
      have H := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at H
      omega
    rw [hone]
    exact a.lemma79_endpointTower_leadingOrders 0 (k + 1) (by omega) (by omega)
      hfirst hend t
  have hdet : IsSquare (diagonalUnitDeterminant source *
      diagonalUnitDeterminant (heHuEvenFirst k μ)) := by
    rw [diagonalUnitDeterminant_heHuEvenFirst]
    simpa [source, diagonalUnitDeterminant_prefixValueUnits, BONG.signedEvenPrefixProduct,
      GoodBONG.prefixProduct, mul_comm, mul_left_comm, mul_assoc] using hclass
  have hrep := AlternatingEndpointTower.equalDeterminantRepresentation_proved
    source (heHuEvenFirst k μ) (1 : Kˣ) hs (heHuLemma45_evenFirst_pairClasses k μ hμ)
      ho (heHuLemma45_evenFirst_leadingOrders k μ) hdet
  have hrep' : DiagonalRepresents (diagonalUnitCoefficients (heHuEvenFirst k μ))
      (a.prefixValues (2 * (k + 1)) (by omega)) := by
    simpa only [source, diagonalUnitCoefficients_prefixValueUnits] using hrep
  let hdim : 2 * (k + 1) = 2 * k + 2 := by omega
  have hcast := heHuLemma43_diagonalRepresents_castLengths hdim hdim hrep'
  convert hcast using 1 <;> funext i
  · unfold diagonalUnitCoefficients
    congr 1
  · unfold prefixValues
    congr 1

/-- Either source alternative in Lemma 6.6 gives the positive first-column test. -/
theorem heADCEvenCentral_prefix_represents_first (k : Nat)
    (a : GoodBONG q L (2 * k + 4)) (hIntegral : Lattice.IsIntegral q L)
    (hhead : ∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (μ : Kˣ)
    (hμ : μ = 1 ∨ μ = (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (hcase : Even (a.order ⟨2 * k + 2, by omega⟩) ∨
      quadraticDefect K (a.toBONG.signedEvenPrefixProduct (k + 1)) = quadraticDefect K μ) :
    DiagonalRepresents (diagonalUnitCoefficients (heHuEvenFirst k μ))
      (a.prefixValues (2 * k + 3) (by omega)) := by
  have hfirst : a.order 0 = 0 := by simpa using hhead 0
  have hlast : a.order ⟨2 * k + 1, by omega⟩ = -(2 * (ramificationIndex K : Int)) := by
    have hodd : ¬ Even (2 * k + 1) := by rintro ⟨s, hs⟩; omega
    simpa only [if_neg hodd] using hhead ⟨2 * k + 1, by omega⟩
  rcases hcase with heven | hdefect
  · obtain ⟨ε, hε, hnormal⟩ := a.heADCEvenCentral_prefix_oddFirst k hIntegral hlast heven
    exact (heHu2022Lemma314iRepresents k μ ε hμ hε).trans hnormal.symm_of_sameRank
  · have hclass := a.heADCEvenCentral_signedClass k hIntegral hlast μ hμ hdefect
    have hprefix := a.heADCEvenCentral_prefix_evenFirst k hfirst hlast μ hμ hclass
    exact hprefix.trans (a.prefixValues_represents_succ (2 * k + 2) (by omega))

/-- The complementary second-column space cannot embed in the same odd prefix. -/
theorem heADCEvenCentral_prefix_not_represents_second (k : Nat)
    (a : GoodBONG q L (2 * k + 4)) (hIntegral : Lattice.IsIntegral q L)
    (hhead : ∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (μ : Kˣ) (hdefined : HeHuEvenSecondDefined k μ)
    (hμ : μ = 1 ∨ μ = (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (hcase : Even (a.order ⟨2 * k + 2, by omega⟩) ∨
      quadraticDefect K (a.toBONG.signedEvenPrefixProduct (k + 1)) = quadraticDefect K μ) :
    ¬ DiagonalRepresents (diagonalUnitCoefficients (heHuEvenSecond k μ hdefined))
      (a.prefixValues (2 * k + 3) (by omega)) := by
  have hfirst := a.heADCEvenCentral_prefix_represents_first k hIntegral hhead μ hμ hcase
  have hexact := heADC2025Lemma45iCodimensionOne (heHuEvenFirst k μ)
    (heHuEvenSecond k μ hdefined) (heADC2025Proposition42iEven k μ hdefined)
      (a.prefixValueUnits (2 * k + 3) (by omega))
  simp only [HeHuRepresentsExactlyOne, diagonalUnitCoefficients_prefixValueUnits] at hexact
  rcases hexact with h | h
  · exact h.2
  · exact False.elim (h.1 hfirst)

end BONG.GoodBONG

end Bong
