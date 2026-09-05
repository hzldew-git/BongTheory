/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma315
import Bong.Bong.HeHu2022SectionFour

/-!
# He (2024), Section 4: even-rank classic universality conditions

This file fixes the exact quantified condition packages used in Section 4.
The revised two-defect form of condition (iii) is used internally and is
transported to Theorem 2.5 by Beli's Lemma 2.16.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice

/-- The ambient-space component of classic rank-`n` universality, stated for
spaces equipped with a classic integral presentation.  This is the exact
classic counterpart of `AmbientlyNUniversal` used in the He--Hu development. -/
def AmbientlyClassicNUniversal (q : QuadraticSpace K V) (n : Nat) : Prop :=
  forall {W : Type w} [AddCommGroup W] [Module K W]
    (r : QuadraticSpace K W) (M : Lattice K W),
    Module.finrank K W = n -> IsClassicIntegral r M -> q.Represents r

end Lattice

namespace BONG.GoodBONG

/-- The four revised representation conditions, uniformly over every
classic integral target of rank `n+1`. -/
def HeClassicAllRepresentationConditionsPrime {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hRank : n <= m) : Prop :=
  forall {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (b : GoodBONG r M (n + 1)), Lattice.IsClassicIntegral r M ->
      RepresentationConditionsPrime a b hRank

/-- Conditions (i)--(ii), uniformly over classic integral targets. -/
def HeClassicAllOrderAndDefectConditions {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hRank : n <= m) : Prop :=
  forall {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (b : GoodBONG r M (n + 1)), Lattice.IsClassicIntegral r M ->
      a.RepresentationOrderCondition b hRank ∧
        a.RepresentationDefectCondition b

/-- Revised condition (iii'), uniformly over classic integral targets. -/
def HeClassicAllCentralRepresentationConditionsPrime {m n : Nat}
    (a : GoodBONG q L (m + 1)) : Prop :=
  forall {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (b : GoodBONG r M (n + 1)), Lattice.IsClassicIntegral r M ->
      a.CentralRepresentationConditionsPrime b

/-- Condition (iv), uniformly over classic integral targets. -/
def HeClassicAllLongRepresentationConditions {m n : Nat}
    (a : GoodBONG q L (m + 1)) : Prop :=
  forall {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (b : GoodBONG r M (n + 1)), Lattice.IsClassicIntegral r M ->
      a.LongRepresentationConditions b

theorem heClassicAllRepresentationConditionsPrime_iff_components
    {m n : Nat} (a : GoodBONG q L (m + 1)) (hRank : n <= m) :
    HeClassicAllRepresentationConditionsPrime.{u, v, w} a hRank ↔
      HeClassicAllOrderAndDefectConditions.{u, v, w} a hRank ∧
        HeClassicAllCentralRepresentationConditionsPrime.{u, v, w}
            (n := n) a ∧
          HeClassicAllLongRepresentationConditions.{u, v, w}
            (n := n) a := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro W _ _ r M b hM
      exact ⟨(h b hM).orderCondition, (h b hM).defectCondition⟩
    · intro W _ _ r M b hM
      exact (h b hM).centralRepresentations
    · intro W _ _ r M b hM
      exact (h b hM).longRepresentations
  · rintro ⟨hInitial, hCentral, hLong⟩
    intro W _ _ r M b hM
    exact
      { orderCondition := (hInitial b hM).1
        defectCondition := (hInitial b hM).2
        centralRepresentations := hCentral b hM
        longRepresentations := hLong b hM }

/-- Classic universality factors through ambient-space universality and the
four revised Beli representation conditions. -/
theorem heClassicNUniversality_factorization {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hRank : n <= m) :
    Lattice.IsClassicNUniversal.{u, v, w} q L (n + 1) ↔
      Lattice.IsClassicIntegral q L ∧
        Lattice.AmbientlyClassicNUniversal.{u, v, w} q (n + 1) ∧
          HeClassicAllRepresentationConditionsPrime.{u, v, w} a hRank := by
  constructor
  · intro hUniversal
    refine ⟨hUniversal.1, ?_, ?_⟩
    · intro W _ _ r M hfin hM
      exact (hUniversal.2 r M hfin hM).ambient
    · intro W _ _ r M b hM
      have hfin : Module.finrank K W = n + 1 :=
        b.toBONG.length_eq_finrank.symm
      have hrep := hUniversal.2 r M hfin hM
      have horiginal :=
        (a.he2022ClassicTheorem25 hRank hrep.ambient b).1 hrep
      let sourceLaws : Beli2006AlphaLaws.{u, v} K :=
        beliUniversalAlphaLaws
      let targetLaws : Beli2006AlphaLaws.{u, w} K :=
        beliUniversalAlphaLaws
      have htrigger := a.beli2019Lemma216
        (sourceLaws := sourceLaws) (targetLaws := targetLaws)
        b hRank horiginal.orderCondition horiginal.defectCondition
      exact (representationConditions_iff_prime a b hRank htrigger).1
        horiginal
  · rintro ⟨hClassic, hAmbient, hConditions⟩
    refine ⟨hClassic, ?_⟩
    intro W _ _ r M hfin hM
    letI : BONGStructuralLaws.{u, w} K := bongStructuralLawsProved K
    let b : GoodBONG r M (n + 1) :=
      (GoodBONG.ofLattice r M).castLength hfin
    have hprime := hConditions b hM
    let sourceLaws : Beli2006AlphaLaws.{u, v} K :=
      beliUniversalAlphaLaws
    let targetLaws : Beli2006AlphaLaws.{u, w} K :=
      beliUniversalAlphaLaws
    have htrigger := a.beli2019Lemma216
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b hRank hprime.orderCondition hprime.defectCondition
    have horiginal :=
      (representationConditions_iff_prime a b hRank htrigger).2 hprime
    exact (a.he2022ClassicTheorem25 hRank
      (hAmbient r M hfin hM) b).2 horiginal

/-! ## The invariant conditions printed in Section 4 -/

/-- `J1'_E(n)` from Lemma 4.2. -/
def HeClassicJ1EPrime {m : Nat} (a : GoodBONG q L (m + 1))
    (n : Nat) (hm : n + 1 <= m) : Prop :=
  (forall i : Fin (n + 1), a.order ⟨i.val, by omega⟩ = 0) ∧
    (forall i : Fin n, a.alphaValue ⟨i.val, by omega⟩ = 1)

/-- `J2'_E(n)` from Lemma 4.2. -/
noncomputable def HeClassicJ2EPrime {m : Nat}
    (a : GoodBONG q L (m + 1)) (n : Nat) (hm : n + 1 <= m) : Prop :=
  1 < ramificationIndex K ->
    (((a.order ⟨n + 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        a.truncatedPrefixDefect a ((-1) ^ ((n + 2) / 2)) 0 (n + 2) <= 1

/-- `J1_E(n)` from Theorem 4.1. -/
def HeClassicJ1E {m : Nat} (a : GoodBONG q L (m + 1))
    (n : Nat) (hm : n + 1 <= m) : Prop :=
  forall i : Fin (n + 1), a.order ⟨i.val, by omega⟩ = 0

/-- `J2_E(n)` from Theorem 4.1.  The final implication is the printed
binary-rank requirement `n=2 -> m>=5`. -/
noncomputable def HeClassicJ2E {m : Nat}
    (a : GoodBONG q L (m + 1)) (n : Nat) (hm : n + 1 <= m) : Prop :=
  a.alphaValue ⟨n, by omega⟩ = 1 ∧
    (((a.order ⟨n + 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        a.truncatedPrefixDefect a ((-1) ^ ((n + 2) / 2)) 0 (n + 2) = 1 ∧
      (n = 2 -> 4 <= m)

/-- `J3_E(n)` from Theorem 4.1. -/
def HeClassicJ3E {m : Nat} (a : GoodBONG q L (m + 1))
    (n : Nat) (_hm : n + 1 <= m) : Prop :=
  forall hmStable : n + 2 <= m,
    a.order ⟨n + 2, by omega⟩ - a.order ⟨n + 1, by omega⟩ <=
      2 * (ramificationIndex K : Int)

structure HeClassicEvenSectionConditions {m : Nat}
    (a : GoodBONG q L (m + 1)) (n : Nat) (hm : n + 1 <= m) : Prop where
  j1 : a.HeClassicJ1E n hm
  j2 : a.HeClassicJ2E n hm
  j3 : a.HeClassicJ3E n hm

/-- Equation (4.3): `J1_E` and `J2_E` imply the strengthened alpha part of
`J1'_E`; the reverse implication is immediate. -/
theorem he2022ClassicEquation43 {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hm : n + 1 <= m)
    (hClassic : Lattice.IsClassicIntegral q L) :
    (a.HeClassicJ1EPrime n hm ∧
        a.HeClassicJ2EPrime n hm ∧
        a.HeClassicJ2E n hm) ↔
      (a.HeClassicJ1E n hm ∧ a.HeClassicJ2E n hm) := by
  constructor
  · rintro ⟨hJ1Prime, _hJ2Prime, hJ2⟩
    exact ⟨hJ1Prime.1, hJ2⟩
  · rintro ⟨hJ1, hJ2⟩
    have horders : forall i : Fin (m + 1),
        i.val <= n -> a.order i = 0 := by
      intro i hi
      exact hJ1 ⟨i.val, by omega⟩
    have hPred : m = (m - 1) + 1 := by omega
    have hLength : m + 1 = (m - 1) + 2 :=
      congrArg (fun k => k + 1) hPred
    let ac : GoodBONG q L ((m - 1) + 2) := a.castLength hLength
    let terminal : Fin ((m - 1) + 1) := ⟨n, by omega⟩
    have hprefixAlpha := ac.he2022ClassicAlphaOneThrough hClassic terminal
      (by
        intro i hi
        have hiVal : i.val <= n := by
          simpa only [terminal] using Fin.mk_le_mk.mp hi
        change (a.castLength hLength).order i = 0
        rw [GoodBONG.order_castLength]
        exact horders ⟨i.val, by omega⟩ hiVal)
      (by
        change (a.castLength hLength).alphaValue terminal = 1
        rw [GoodBONG.alphaValue_castLength' a hPred terminal]
        have hindex : Fin.cast hPred.symm terminal =
            (⟨n, by omega⟩ : Fin m) := Fin.ext rfl
        rw [hindex]
        exact hJ2.1)
    have hAlpha : forall i : Fin n,
        a.alphaValue ⟨i.val, by omega⟩ = 1 := by
      intro i
      have hi := hprefixAlpha ⟨i.val, by omega⟩
        (Fin.mk_le_mk.mpr (by omega))
      change (a.castLength hLength).alphaValue ⟨i.val, by omega⟩ = 1 at hi
      rw [GoodBONG.alphaValue_castLength' a hPred] at hi
      have hindex : Fin.cast hPred.symm
          (⟨i.val, by omega⟩ : Fin ((m - 1) + 1)) =
          (⟨i.val, by omega⟩ : Fin m) := Fin.ext rfl
      rw [hindex] at hi
      exact hi
    have hJ1Prime : a.HeClassicJ1EPrime n (by omega) :=
      ⟨hJ1, hAlpha⟩
    have hJ2Prime : a.HeClassicJ2EPrime n (by omega) := by
      intro _heLarge
      exact le_of_eq hJ2.2.1
    exact ⟨hJ1Prime, hJ2Prime, hJ2⟩

end BONG.GoodBONG

end Bong
