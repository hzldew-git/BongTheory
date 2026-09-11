/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCPublishedProfiles
import Bong.Bong.He2023ADCSectionThree
import Bong.Bong.HeHu2022PublishedTestingSet

/-!
# He (2025), Proposition 4.13: odd-rank maximal lattice structure

The ambient classification is normalized to valuation-zero or valuation-one
parameters before applying Lemma 4.12. No prescribed representative system
or maximal-profile hypothesis is added to the published proposition.
-/

namespace Bong

open Dyadic Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Replace the last hyperbolic pair and a unary tail by a ternary tail,
without changing any coordinate of the maximal order sequence. -/
theorem heADCMaximalOrderProfile_unary_eq_ternary (k : Nat) (s : Int)
    (i : Fin (2 * k + 3)) :
    heADCMaximalOrderProfile (K := K) (k + 1) ![s] ⟨i.val, by omega⟩ =
      heADCMaximalOrderProfile (K := K) k
        ![0, -(2 * (ramificationIndex K : Int)), s] ⟨i.val, by omega⟩ := by
  by_cases hi : i.val < 2 * k
  · simp [heADCMaximalOrderProfile, hi, show i.val < 2 * (k + 1) by omega]
  · have heven : Even (2 * k) := ⟨k, by omega⟩
    have hodd : ¬ Even (2 * k + 1) := by rintro ⟨z, hz⟩; omega
    have hcases : i.val = 2 * k ∨ i.val = 2 * k + 1 ∨ i.val = 2 * k + 2 := by omega
    rcases hcases with hzero | hone | htwo
    · simp [heADCMaximalOrderProfile, hzero, heven,
        show 2 * k < 2 * (k + 1) by omega]
    · simp [heADCMaximalOrderProfile, hone, hodd,
        show 2 * k + 1 < 2 * (k + 1) by omega,
        show ¬ 2 * k + 1 < 2 * k by omega,
        show 2 * k + 1 - 2 * k = 1 by omega]
    · simp [heADCMaximalOrderProfile, htwo,
        show ¬ 2 * k + 2 < 2 * (k + 1) by omega,
        show ¬ 2 * k + 2 < 2 * k by omega,
        show 2 * k + 2 - 2 * (k + 1) = 0 by omega,
        show 2 * k + 2 - 2 * k = 2 by omega]

namespace BONG.GoodBONG

variable {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The four normalized ambient rows needed in Proposition 4.13. The
valuation-unit parameter is constructed, not assumed to belong to a table. -/
theorem exists_heADCOddNormalizedAmbient (k : Nat) (a : GoodBONG q L (2 * k + 3)) :
    ∃ δ : Kˣ, IsValuationUnit K (δ : K) ∧
      (q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Odd k δ)) ∨
        q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW2Odd k δ)) ∨
        q.IsIsometric (BONG.coefficientDiagonalSpace
          (heADCW1Odd k (δ * uniformizerPowerUnit K 1))) ∨
        q.IsIsometric (BONG.coefficientDiagonalSpace
          (heADCW2Odd k (δ * uniformizerPowerUnit K 1)))) := by
  obtain ⟨c, hfirst | hsecond⟩ := heADC2025Proposition42iiOdd k a.valueUnit
  · obtain ⟨b, z, hbOrder, hc⟩ := exists_order_zero_or_one_mul_square_any (K := K) c
    obtain ⟨f⟩ := a.ambientIsometric_of_diagonalRepresents _ rfl hfirst
    obtain ⟨g⟩ :=
      Lattice.QuadraticLatticeModel.heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
        _ _ (Lattice.QuadraticLatticeModel.heHuOddFirst_represents_of_mul_square k c b z hc)
    have hspace : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Odd k b)) :=
      ⟨f.trans g⟩
    rcases hbOrder with hbZero | hbOne
    · exact ⟨b, (isValuationUnit_iff_ordUnit_eq_zero K b).2 hbZero, Or.inl hspace⟩
    · let δ := normalizedUnitPart K b
      have hb : b = δ * uniformizerPowerUnit K 1 := by
        simpa only [δ, hbOne, mul_comm] using
          (uniformizerPower_mul_normalizedUnitPart K b).symm
      rw [hb] at hspace
      exact ⟨δ, normalizedUnitPart_isValuationUnit K b, Or.inr (Or.inr (Or.inl hspace))⟩
  · obtain ⟨b, z, hbOrder, hc⟩ := exists_order_zero_or_one_mul_square_any (K := K) c
    obtain ⟨f⟩ := a.ambientIsometric_of_diagonalRepresents _ rfl hsecond
    obtain ⟨g⟩ :=
      Lattice.QuadraticLatticeModel.heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
        _ _ (Lattice.QuadraticLatticeModel.heHuOddSecond_represents_of_mul_square k c b z hc)
    have hspace : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW2Odd k b)) :=
      ⟨f.trans g⟩
    rcases hbOrder with hbZero | hbOne
    · exact ⟨b, (isValuationUnit_iff_ordUnit_eq_zero K b).2 hbZero, Or.inr (Or.inl hspace)⟩
    · let δ := normalizedUnitPart K b
      have hb : b = δ * uniformizerPowerUnit K 1 := by
        simpa only [δ, hbOne, mul_comm] using
          (uniformizerPower_mul_normalizedUnitPart K b).symm
      rw [hb] at hspace
      exact ⟨δ, normalizedUnitPart_isValuationUnit K b, Or.inr (Or.inr (Or.inr hspace))⟩

/-- The full odd maximal order profile, derived for an arbitrary maximal
lattice by ambient exhaustion and maximal-lattice uniqueness. -/
theorem heADCOddMaximal_orders (k : Nat) (a : GoodBONG q L (2 * k + 3))
    (hL : Lattice.IsOMaximal q L) :
    ∃ p s : Int,
      ((p = -(2 * (ramificationIndex K : Int)) ∧ (s = 0 ∨ s = 1)) ∨
        (p = 2 - 2 * (ramificationIndex K : Int) ∧ s = 0)) ∧
      ∀ i, a.order i = heADCMaximalOrderProfile (K := K) k ![0, p, s]
        ⟨i.val, by omega⟩ := by
  obtain ⟨δ, hδ, hfirst | hsecond | hfirstπ | hsecondπ⟩ :=
    a.exists_heADCOddNormalizedAmbient k
  · have horders := (heADC2025Lemma412iPublished δ hδ k
        (a.castLength (by omega)) hL.isIntegral hfirst).mp
      (Lattice.oMaximal_isIsometric_of_isometric hL
        (heHuOMaximalLattice_isOMaximal _) hfirst)
    refine ⟨_, 0, Or.inl ⟨rfl, Or.inl rfl⟩, fun i ↦ ?_⟩
    have hi := horders ⟨i.val, by omega⟩
    simpa only [order_castLength, heADCMaximalOrderProfile_unary_eq_ternary k 0 i] using hi
  · have horders := (heADC2025Lemma412iiPublished δ hδ k
        (a.castLength (by omega)) hL.isIntegral hsecond).mp
      (Lattice.oMaximal_isIsometric_of_isometric hL
        (heHuOMaximalLattice_isOMaximal _) hsecond)
    refine ⟨_, 0, Or.inr ⟨rfl, rfl⟩, fun i ↦ ?_⟩
    simpa only [order_castLength] using horders ⟨i.val, by omega⟩
  · have horders := (heADC2025Lemma412iiiFirstPublished δ hδ k
        (a.castLength (by omega)) hL.isIntegral hfirstπ).mp
      (Lattice.oMaximal_isIsometric_of_isometric hL
        (heHuOMaximalLattice_isOMaximal _) hfirstπ)
    refine ⟨_, 1, Or.inl ⟨rfl, Or.inr rfl⟩, fun i ↦ ?_⟩
    have hi := horders ⟨i.val, by omega⟩
    simpa only [order_castLength, heADCMaximalOrderProfile_unary_eq_ternary k 1 i] using hi
  · have horders := (heADC2025Lemma412iiiSecondPublished δ hδ k
        (a.castLength (by omega)) hL.isIntegral hsecondπ).mp
      (Lattice.oMaximal_isIsometric_of_isometric hL
        (heHuOMaximalLattice_isOMaximal _) hsecondπ)
    refine ⟨_, 1, Or.inl ⟨rfl, Or.inr rfl⟩, fun i ↦ ?_⟩
    simpa only [order_castLength] using horders ⟨i.val, by omega⟩

/-- All clauses of Proposition 4.13. Paper indices start at one; the
penultimate adjacent pair therefore has Lean index `2*k`. -/
structure HeADCProposition413Conclusions {k : Nat}
    (a : GoodBONG q L (2 * k + 3)) : Prop where
  initialOrders (i : Fin (2 * k + 3)) (hi : i.val ≤ 2 * k) :
    a.order i = if Even i.val then 0 else -(2 * (ramificationIndex K : Int))
  penultimate :
    a.order ⟨2 * k + 1, by omega⟩ = -(2 * (ramificationIndex K : Int)) ∨
      a.order ⟨2 * k + 1, by omega⟩ = 2 - 2 * (ramificationIndex K : Int)
  standardTail (hp :
      a.order ⟨2 * k + 1, by omega⟩ = -(2 * (ramificationIndex K : Int))) :
    (a.order ⟨2 * k + 2, by omega⟩ = 0 ∨ a.order ⟨2 * k + 2, by omega⟩ = 1) ∧
      a.alphaValue ⟨2 * k, by omega⟩ = 0 ∧
      a.heADCAdjacentCappedDefect ⟨2 * k, by omega⟩ ≤
        (a.alphaValue ⟨2 * k + 1, by omega⟩ : WithTop ℚ) ∧
      ((2 * (ramificationIndex K : ℚ)) : WithTop ℚ) ≤
        a.heADCAdjacentCappedDefect ⟨2 * k, by omega⟩
  raisedTail (hp :
      a.order ⟨2 * k + 1, by omega⟩ = 2 - 2 * (ramificationIndex K : Int)) :
    a.order ⟨2 * k + 2, by omega⟩ = 0 ∧
      a.alphaValue ⟨2 * k, by omega⟩ = 1 ∧
      a.heADCAdjacentCappedDefect ⟨2 * k, by omega⟩ =
        ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) ∧
      a.alphaValue ⟨2 * k + 1, by omega⟩ = 2 * (ramificationIndex K : ℚ) - 1

/-- He (2025), Proposition 4.13, for every odd rank at least three.
The order, alpha, and bracketed-defect conclusions are all derived from
maximality; none is an additional hypothesis. -/
theorem heADC2025Proposition413 (k : Nat) (a : GoodBONG q L (2 * k + 3))
    (hL : Lattice.IsOMaximal q L) : HeADCProposition413Conclusions a := by
  obtain ⟨p, s, hcases, horders⟩ := a.heADCOddMaximal_orders k hL
  have heven : Even (2 * k) := ⟨k, by omega⟩
  have hprefix (i : Fin (2 * k + 3)) (hi : i.val ≤ 2 * k) :
      a.order i = if Even i.val then 0 else -(2 * (ramificationIndex K : Int)) := by
    rw [horders]
    by_cases hlt : i.val < 2 * k
    · simp [heADCMaximalOrderProfile, hlt]
    · have heq : i.val = 2 * k := by omega
      simp [heADCMaximalOrderProfile, heq, heven]
  have hp : a.order ⟨2 * k + 1, by omega⟩ = p := by
    simpa [heADCMaximalOrderProfile, show ¬ 2 * k + 1 < 2 * k by omega,
      show 2 * k + 1 - 2 * k = 1 by omega] using horders ⟨2 * k + 1, by omega⟩
  have hs : a.order ⟨2 * k + 2, by omega⟩ = s := by
    simpa [heADCMaximalOrderProfile, show ¬ 2 * k + 2 < 2 * k by omega,
      show 2 * k + 2 - 2 * k = 2 by omega] using horders ⟨2 * k + 2, by omega⟩
  let i : Fin (2 * k + 2) := ⟨2 * k, by omega⟩
  let j : Fin (2 * k + 2) := ⟨2 * k + 1, by omega⟩
  have hzero : a.order i.castSucc = 0 := by
    simpa [i, heven] using hprefix i.castSucc (by dsimp [i]; omega)
  have hgap : a.orderGap i = p := by
    change a.order ⟨2 * k + 1, by omega⟩ - a.order i.castSucc = p
    rw [hp, hzero, sub_zero]
  have hgapNext : a.orderGap j = s - p := by
    change a.order ⟨2 * k + 2, by omega⟩ - a.order ⟨2 * k + 1, by omega⟩ = s - p
    rw [hs, hp]
  have hcap : a.heADCAdjacentCappedDefect i ≤ (a.alphaValue j : WithTop ℚ) := by
    have hbound := a.truncatedPrefixDefect_le_rightCap a (-1) (2 * k) (2 * k + 2)
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hbound
    simpa only [heADCAdjacentCappedDefect, heHuAdjacentCappedDefect, i, j,
      show 2 * k + 2 - 1 = 2 * k + 1 by omega] using hbound
  refine ⟨hprefix, ?_, ?_, ?_⟩
  · rw [hp]
    exact hcases.elim (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.1)
  · intro hstandard
    have hpValue : p = -(2 * (ramificationIndex K : Int)) := hp.symm.trans hstandard
    have hsValue : s = 0 ∨ s = 1 := by
      rcases hcases with h | h
      · exact h.2
      · linarith [h.1]
    have halpha : a.alphaValue i = 0 :=
      (a.heADC2025Proposition34 i).alphaZero.mpr (hgap.trans hpValue)
    exact ⟨by simpa only [hs] using hsValue, halpha, hcap,
      (a.heADC2025Proposition34 i).alphaZeroDefect halpha⟩
  · intro hraised
    have hpValue : p = 2 - 2 * (ramificationIndex K : Int) := hp.symm.trans hraised
    have hsValue : s = 0 := by
      rcases hcases with h | h
      · linarith [h.1]
      · exact h.2
    have hgapValue : a.orderGap i = 2 - 2 * (ramificationIndex K : Int) :=
      hgap.trans hpValue
    have hgapNextValue : a.orderGap j = 2 * (ramificationIndex K : Int) - 2 := by
      rw [hgapNext, hpValue, hsValue]
      ring
    have halpha : a.alphaValue i = 1 := by
      rw [(a.heADC2025Proposition33 i).halfGap (Or.inr (Or.inr (Or.inl hgapValue))),
        halfGapValue, hgapValue]
      push_cast
      ring
    have halphaNext : a.alphaValue j = 2 * (ramificationIndex K : ℚ) - 1 := by
      rw [(a.heADC2025Proposition33 j).halfGap
        (Or.inr (Or.inr (Or.inr hgapNextValue))), halfGapValue, hgapNextValue]
      push_cast
      ring
    have hlower : ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) ≤
        a.heADCAdjacentCappedDefect i := by
      have h := ((a.heADC2025Proposition34 i).alphaOneDefect halpha).1
      rw [hgapValue] at h
      have hnum : (1 : ℚ) - ((2 - 2 * (ramificationIndex K : Int) : Int) : ℚ) =
          2 * (ramificationIndex K : ℚ) - 1 := by
        push_cast
        ring
      simpa only [hnum] using h
    have hdefect := le_antisymm (hcap.trans_eq (congrArg (fun x : ℚ ↦
      (x : WithTop ℚ)) halphaNext)) hlower
    exact ⟨hs.trans hsValue, halpha, hdefect, halphaNext⟩

end BONG.GoodBONG

end Bong
