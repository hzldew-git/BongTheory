/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenCentralObstruction
import Bong.Bong.He2023ADCPublishedRepresentation

/-!
# He (2025), Lemma 6.7: the terminal alpha and uncapped defect

Actual lattice representation rules out the literal condition-(iii) failure
from Lemma 6.6. The last alpha cap is omitted at the endpoint; the preceding
one is proved strictly larger than the defect, not simply discarded.
-/

namespace Bong

open Dyadic

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The two alternatives printed in Lemma 6.7, with both raw and capped defects. -/
def HeADCEvenCentralAlphaAlternatives (k : Nat) (a : GoodBONG q L (2 * k + 4)) : Prop :=
  a.alphaValue ⟨2 * k + 2, by omega⟩ = 0 ∨
    a.alphaValue ⟨2 * k + 2, by omega⟩ = 1 ∧
      a.adjacentDefect ⟨2 * k + 2, by omega⟩ =
        a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩ ∧
      a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩ =
        ((1 - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ)

/-- Actual representation excludes the central obstruction and bounds the capped defect. -/
theorem heADCEvenCentral_capped_le_of_represents (k : Nat)
    (a : GoodBONG q L (2 * k + 4)) (b : GoodBONG r M (2 * k + 2))
    (hIntegral : Lattice.IsIntegral q L) (hM : Lattice.IsIntegral r M)
    (hhead : ∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hR : 2 - 2 * (ramificationIndex K : Int) ≤ a.order ⟨2 * k + 3, by omega⟩)
    (μ : Kˣ) (hdefined : HeHuEvenSecondDefined k μ)
    (hμ : μ = 1 ∨ μ = (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (hcase : Even (a.order ⟨2 * k + 2, by omega⟩) ∨
      quadraticDefect K (a.toBONG.signedEvenPrefixProduct (k + 1)) = quadraticDefect K μ)
    (hmodel : Lattice.IsIsometric r (BONG.coefficientDiagonalSpace
      (heADCW2Even k μ hdefined)) M (heADCN2Even k μ hdefined).lattice)
    (hrep : Lattice.Represents q r L M) :
    a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩ ≤
      ((1 - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) := by
  by_contra hnot
  have hfail := a.heADC2025Lemma66_endpoint k b hIntegral hM hhead hR
    (lt_of_not_ge hnot) μ hdefined hμ hcase hmodel
  have hconditions := (heADC2025Theorem36Published (by omega : 2 * k + 1 ≤ 2 * k + 3)
    hrep.ambient a b).mp hrep
  apply hfail.2
  have hc := hconditions.centralRepresentations (heHuLemma43CentralIndex k le_rfl) hfail.1
  change DiagonalRepresents (b.prefixValues (2 * k + 3 - 1) (by omega))
    (a.prefixValues (2 * k + 3) (by omega)) at hc
  have hcast := heHuLemma43_diagonalRepresents_castLengths
    (show 2 * k + 3 - 1 = 2 * k + 2 by omega) (rfl : 2 * k + 3 = 2 * k + 3) hc
  convert hcast using 1 <;> funext j <;> unfold prefixValues <;> congr 1

/-- A small terminal capped defect forces the exact alternatives, including uncapping. -/
theorem heADCEvenCentral_alphaAlternatives_of_capped_le (k : Nat)
    (a : GoodBONG q L (2 * k + 4)) (hIntegral : Lattice.IsIntegral q L)
    (hhead : ∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hR : 2 - 2 * (ramificationIndex K : Int) ≤ a.order ⟨2 * k + 3, by omega⟩)
    (hcap : a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩ ≤
      ((1 - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ)) :
    a.HeADCEvenCentralAlphaAlternatives k := by
  let i : Fin (2 * k + 3) := ⟨2 * k + 2, by omega⟩
  let previous : Fin (2 * k + 3) := ⟨2 * k + 1, by omega⟩
  have hnext : 0 ≤ a.order i.castSucc :=
    ((a.heHu2022Proposition27i hIntegral).oddIndexed i.castSucc i.castSucc le_rfl
      ⟨k + 1, by dsimp [i]; omega⟩ ⟨k + 1, by dsimp [i]; omega⟩).1
  have hnextQ : (0 : ℚ) ≤ (a.order i.castSucc : ℚ) := by exact_mod_cast hnext
  have hαle : a.alphaValue i ≤ 1 := by
    apply WithTop.coe_le_coe.mp
    calc
      (a.alphaValue i : WithTop ℚ) ≤
          (((a.order i.succ - a.order i.castSucc : Int) : ℚ) : WithTop ℚ) +
            a.heADCAdjacentCappedDefect i := a.alpha_le_orderGap_add_cappedAdjacent i
      _ ≤ (((a.order i.succ - a.order i.castSucc : Int) : ℚ) : WithTop ℚ) +
          ((1 - (a.order i.succ : ℚ) : ℚ) : WithTop ℚ) := add_le_add le_rfl hcap
      _ = ((1 - (a.order i.castSucc : ℚ) : ℚ) : WithTop ℚ) := by
        rw [← WithTop.coe_add]
        congr 1
        push_cast
        ring
      _ ≤ (1 : WithTop ℚ) := WithTop.coe_le_coe.mpr (by linarith)
  rcases a.alphaBoundary_eq_zero_or_one_of_le_one (by omega) hαle with hzero | hone
  · exact Or.inl hzero
  have hcapEq : a.heADCAdjacentCappedDefect i =
      ((1 - (a.order i.succ : ℚ) : ℚ) : WithTop ℚ) := by
    apply le_antisymm hcap
    calc
      ((1 - (a.order i.succ : ℚ) : ℚ) : WithTop ℚ) ≤
          ((((a.order i.castSucc - a.order i.succ : Int) : ℚ) +
            a.alphaValue i : ℚ) : WithTop ℚ) := by
        apply WithTop.coe_le_coe.mpr
        rw [hone]
        push_cast
        linarith
      _ ≤ a.heADCAdjacentCappedDefect i := a.order_sub_add_alpha_le_cappedAdjacent i
  have hheadLast : a.order previous.castSucc = -(2 * (ramificationIndex K : Int)) := by
    have h := hhead ⟨2 * k + 1, by omega⟩
    have hodd : ¬ Even (2 * k + 1) := by rintro ⟨z, hz⟩; omega
    change a.order ⟨2 * k + 1, by omega⟩ = _
    simpa only [Fin.val_mk, hodd, if_false] using h
  have hgap : 2 * (ramificationIndex K : Int) ≤ a.orderGap previous := by
    change 2 * (ramificationIndex K : Int) ≤ a.order i.castSucc - a.order previous.castSucc
    rw [hheadLast]
    omega
  have hprevAlpha : 2 * (ramificationIndex K : ℚ) ≤ a.alphaValue previous := by
    by_contra hnot
    exact (not_lt_of_ge hgap)
      ((a.heADC2025Proposition33 previous).compareTwoE.2.2.mpr (lt_of_not_ge hnot))
  have hstrict : ((1 - (a.order i.succ : ℚ) : ℚ) : WithTop ℚ) <
      (a.alphaValue previous : WithTop ℚ) := by
    apply WithTop.coe_lt_coe.mpr
    have hRQ : (2 : ℚ) - 2 * (ramificationIndex K : ℚ) ≤ (a.order i.succ : ℚ) := by
      exact_mod_cast hR
    linarith
  have hmin : a.heADCAdjacentCappedDefect i =
      min (a.adjacentDefect i) (a.alphaValue previous : WithTop ℚ) := by
    have hleft : a.prefixAlphaCap i.val = (a.alphaValue previous : WithTop ℚ) := by
      rw [a.prefixAlphaCap_of_internal (by dsimp [i]; omega) (by dsimp [i]; omega)]
      congr 2
    have hright : a.prefixAlphaCap (i.val + 2) = ⊤ := a.prefixAlphaCap_last
    change a.truncatedPrefixDefect a (-1) i.val (i.val + 2) = _
    rw [truncatedPrefixDefect, a.defectOrder_prefixPair_eq_adjacentDefect i,
      hleft, hright, min_top_right]
  have hraw : a.adjacentDefect i = a.heADCAdjacentCappedDefect i := by
    by_cases hle : a.adjacentDefect i ≤ (a.alphaValue previous : WithTop ℚ)
    · simpa only [min_eq_left hle] using hmin.symm
    · rw [min_eq_right (le_of_not_ge hle), hcapEq] at hmin
      exact False.elim (hstrict.ne hmin)
  exact Or.inr ⟨hone, hraw, hcapEq⟩

/-- Lemma 6.7's common implication on the actual, defined second-column lattice. -/
theorem heADC2025Lemma67_endpoint (k : Nat)
    (a : GoodBONG q L (2 * k + 4)) (hIntegral : Lattice.IsIntegral q L)
    (hhead : ∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hR : 2 - 2 * (ramificationIndex K : Int) ≤ a.order ⟨2 * k + 3, by omega⟩)
    (μ : Kˣ) (hdefined : HeHuEvenSecondDefined k μ)
    (hμ : μ = 1 ∨ μ = (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (hcase : Even (a.order ⟨2 * k + 2, by omega⟩) ∨
      quadraticDefect K (a.toBONG.signedEvenPrefixProduct (k + 1)) = quadraticDefect K μ)
    (hrep : Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW2Even k μ hdefined))
      L (heADCN2Even k μ hdefined).lattice) :
    a.HeADCEvenCentralAlphaAlternatives k := by
  apply a.heADCEvenCentral_alphaAlternatives_of_capped_le k hIntegral hhead hR
  exact a.heADCEvenCentral_capped_le_of_represents k
    (heADCMaximalGoodBONG (heADCW2Even k μ hdefined)) hIntegral
    (heHuOMaximalLattice_isOMaximal _).isIntegral hhead hR μ hdefined hμ hcase
    (Lattice.isIsometric_refl _ _) hrep

/-- He (2025), Lemma 6.7(i), including n=2 and arbitrary ramification. -/
theorem heADC2025Lemma67i (k : Nat)
    (a : GoodBONG q L (2 * k + 4)) (hIntegral : Lattice.IsIntegral q L)
    (hhead : ∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hR : 2 - 2 * (ramificationIndex K : Int) ≤ a.order ⟨2 * k + 3, by omega⟩)
    (hcase : Even (a.order ⟨2 * k + 2, by omega⟩) ∨
      quadraticDefect K (a.toBONG.signedEvenPrefixProduct (k + 1)) =
        (2 * ramificationIndex K : Nat))
    (hrep : Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW2Even k
      (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
      (heHuLemma43_evenSecondDefined (K := K) k))) L (heADCN2Even k
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) k)).lattice) :
    a.HeADCEvenCentralAlphaAlternatives k := by
  apply a.heADC2025Lemma67_endpoint k hIntegral hhead hR _
    (heHuLemma43_evenSecondDefined (K := K) k) (Or.inr rfl) _ hrep
  simpa only [(Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminant_defect]
    using hcase

/-- He (2025), Lemma 6.7(ii), on the square target defined from rank four. -/
theorem heADC2025Lemma67ii (k : Nat) (hk : 0 < k)
    (a : GoodBONG q L (2 * k + 4)) (hIntegral : Lattice.IsIntegral q L)
    (hhead : ∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hR : 2 - 2 * (ramificationIndex K : Int) ≤ a.order ⟨2 * k + 3, by omega⟩)
    (hcase : Even (a.order ⟨2 * k + 2, by omega⟩) ∨
      quadraticDefect K (a.toBONG.signedEvenPrefixProduct (k + 1)) = ⊤)
    (hrep : Lattice.Represents q (BONG.coefficientDiagonalSpace
      (heADCW2Even k (1 : Kˣ) (Or.inl hk))) L (heADCN2Even k (1 : Kˣ) (Or.inl hk)).lattice) :
    a.HeADCEvenCentralAlphaAlternatives k := by
  apply a.heADC2025Lemma67_endpoint k hIntegral hhead hR 1 (Or.inl hk) (Or.inl rfl) _ hrep
  simpa only [quadraticDefect_eq_top_of_isSquare (K := K) (show IsSquare (1 : Kˣ) from
    ⟨1, by simp⟩)] using hcase

end BONG.GoodBONG

end Bong
