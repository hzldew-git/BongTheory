/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Lemma43
import Bong.Bong.Beli2019Lemma79CentralEndpointTowers

/-!
# He--Hu 2022, Lemma 4.4

This file proves the equivalence between condition (iii) of Theorem 2.8
for every integral even-rank target and the boundary condition `I2^E`.
The intermediate test is the literal lattice `N_2^n(Delta)` from Lemma 4.3.
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

/-- Cross-space form of the endpoint-tower representation used in the
`S_n=-2e` branch of Lemma 4.4.  The existing Beli 7.9 interface constructs
the two endpoint towers separately; this lemma records that the resulting
diagonal representation is independent of their ambient vector spaces. -/
theorem endpointTowers_representationInUnaryExtension_cross
    (sourceLaws : Beli2006AlphaLaws.{u, v} K)
    (targetLaws : Beli2006AlphaLaws.{u, w} K)
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {ma mb pairs : Nat} (a : GoodBONG q L (ma + 2))
    (b : GoodBONG r M (mb + 2)) (R : Int)
    (hpairs : 0 < pairs)
    (haBound : 2 * pairs + 1 ≤ ma + 2)
    (hbBound : 2 * pairs ≤ mb + 2)
    (haFirst : a.order 0 = R)
    (haLast : a.order ⟨2 * pairs - 1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hbFirst : b.order 0 = R)
    (hbLast : b.order ⟨2 * pairs - 1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (haExtra : a.order ⟨2 * pairs, by omega⟩ = R) :
    DiagonalRepresents
      (b.prefixValues (2 * pairs) hbBound)
      (a.prefixValues (2 * pairs + 1) haBound) := by
  let sourceTower : Fin (2 * pairs) → Kˣ :=
    a.prefixValueUnits (2 * pairs) (by omega)
  let targetTower : Fin (2 * pairs) → Kˣ :=
    b.prefixValueUnits (2 * pairs) hbBound
  let extraIndex : Fin (ma + 2) := ⟨2 * pairs, by omega⟩
  let extra : Kˣ := a.valueUnit extraIndex
  have hsourceClasses : AlternatingEndpointPairClasses sourceTower := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    simpa only [sourceTower] using
      a.lemma79_endpointTower_pairClasses R pairs hpairs (by omega)
        haFirst haLast
  have htargetClasses : AlternatingEndpointPairClasses targetTower := by
    letI : Beli2006AlphaLaws.{u, w} K := targetLaws
    simpa only [targetTower] using
      b.lemma79_endpointTower_pairClasses R pairs hpairs hbBound
        hbFirst hbLast
  have hextra : ordUnit K extra = R := by
    calc
      ordUnit K extra = a.order extraIndex :=
        (a.toBONG.order_eq_ordUnit extraIndex).symm
      _ = R := by simpa only [extraIndex] using haExtra
  have hsourceOrders : AlternatingEndpointLeadingOrdersAt sourceTower extra := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    intro t
    calc
      ordUnit K (sourceTower ⟨2 * t.val, by omega⟩) = R := by
        simpa only [sourceTower] using
          a.lemma79_endpointTower_leadingOrders R pairs hpairs (by omega)
            haFirst haLast t
      _ = ordUnit K extra := hextra.symm
  have htargetOrders : AlternatingEndpointLeadingOrdersAt targetTower extra := by
    letI : Beli2006AlphaLaws.{u, w} K := targetLaws
    intro t
    calc
      ordUnit K (targetTower ⟨2 * t.val, by omega⟩) = R := by
        simpa only [targetTower] using
          b.lemma79_endpointTower_leadingOrders R pairs hpairs hbBound
            hbFirst hbLast t
      _ = ordUnit K extra := hextra.symm
  have hrep := alternatingEndpointTower_representationInUnaryExtension
    sourceTower targetTower extra hsourceClasses htargetClasses
      hsourceOrders htargetOrders
  have htargetCoefficients :
      diagonalUnitCoefficients targetTower =
        b.prefixValues (2 * pairs) hbBound := by
    simp only [targetTower, diagonalUnitCoefficients_prefixValueUnits]
  have hsourceCoefficients :
      diagonalUnitCoefficients (Fin.snoc sourceTower extra) =
        a.prefixValues (2 * pairs + 1) haBound := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [sourceTower, extra, extraIndex, diagonalUnitCoefficients,
        prefixValues, GoodBONG.valueUnit, GoodBONG.value]
    · simp [sourceTower, diagonalUnitCoefficients, prefixValues,
        prefixValueUnits, GoodBONG.valueUnit, GoodBONG.value]
  rwa [htargetCoefficients, hsourceCoefficients] at hrep

/-- Integrality of the lattice underlying a displayed good BONG.  Packaging
the implicit space and lattice this way keeps concrete Table 2 models usable
without repeating their long ambient types. -/
def UnderlyingLatticeIsIntegral {X : Type u} [AddCommGroup X] [Module K X]
    {s : QuadraticSpace K X} {N : Lattice K X} {n : Nat}
    (_b : GoodBONG s N n) : Prop :=
  Lattice.IsIntegral s N

/-- The special `N_2^(2k+2)(Delta)` target used in Lemma 4.4 is integral. -/
theorem heHuLemma43Target_isIntegral
    (k : Nat) :
    UnderlyingLatticeIsIntegral (heHuLemma43Target (K := K) k) := by
  let b := heHuLemma43Target (K := K) k
  apply heHuIntegral_of_firstOrder_nonneg b
  cases k with
  | zero =>
      have h := (heHuLemma43Target_lastOrders (K := K) 0).1
      have hnonneg : 0 ≤
          (heHuLemma43Target (K := K) 0).order
            ⟨2 * 0, by omega⟩ := by
        rw [h]
        norm_num
      dsimp only [b]
      convert hnonneg using 1
      congr 1
  | succ k =>
      have h :=
        (heHu2022Lemma311iSecondDelta (K := K) (k + 1)).1
          (0 : Fin (k + 1)) |>.1
      dsimp only [b]
      unfold heHuLemma43Target heHuLemma43TargetSpace
        heHuLemma43TargetLattice
      rw [order_castLength]
      have hnonneg : 0 ≤
          (heHuLemma311EvenSecondDeltaBONG (K := K) (k + 1)).order
            ⟨2 * (0 : Fin (k + 1)).val, by omega⟩ := by
        rw [h]
      convert hnonneg using 1
      congr 1

/-- Transport the prefix representation supplied by condition (iii') across
explicit arithmetic equalities of the two prefix lengths.  Keeping the good
BONGs abstract prevents concrete Table models from being unfolded by the
kernel during routine index conversion. -/
theorem centralRepresentationConditionsPrime_represents_castLengths
    {m n s t : Nat} (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1))
    (hPrime : a.CentralRepresentationConditionsPrime b)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (htrigger : a.centralDefectTrigger b i)
    (hs : i.val - 1 = s) (ht : i.val = t) :
    DiagonalRepresents
      (b.prefixValues s (by
        have := i.le_small_succ
        omega))
      (a.prefixValues t (by
        have := i.lt_large
        omega)) := by
  have hrep := hPrime i htrigger
  have hcast := heHuLemma43_diagonalRepresents_castLengths hs ht hrep
  have hsourceEq :
      (fun j : Fin s =>
        b.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega) (Fin.cast hs.symm j)) =
        b.prefixValues s (by
          have := i.le_small_succ
          omega) := by
    funext j
    unfold prefixValues
    congr 1
  have htargetEq :
      (fun j : Fin t =>
        a.prefixValues i.val (by
          have := i.lt_large
          omega) (Fin.cast ht.symm j)) =
        a.prefixValues t (by
          have := i.lt_large
          omega) := by
    funext j
    unfold prefixValues
    congr 1
  rw [hsourceEq, htargetEq] at hcast
  exact hcast

/-- Elimination rule for condition (iii'), kept abstract in both BONGs so
concrete model definitions never need to unfold at an application site. -/
theorem centralRepresentationConditionsPrime_apply
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1))
    (hPrime : a.CentralRepresentationConditionsPrime b)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (htrigger : a.centralDefectTrigger b i) :
    DiagonalRepresents
      (b.prefixValues (i.val - 1) (by
        have := i.le_small_succ
        omega))
      (a.prefixValues i.val (by
        have := i.lt_large
        omega)) :=
  hPrime i htrigger

/-- A failed representation at arithmetically identified prefix lengths
rules out the corresponding revised central trigger. -/
theorem CentralRepresentationConditionsPrime.notTrigger_of_not_represents
    {m n s t : Nat} {a : GoodBONG q L (m + 1)}
    {b : GoodBONG r M (n + 1)}
    (hPrime : a.CentralRepresentationConditionsPrime b)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hs : i.val - 1 = s) (ht : i.val = t)
    (hnot : ¬ DiagonalRepresents
      (b.prefixValues s (by
        have := i.le_small_succ
        omega))
      (a.prefixValues t (by
        have := i.lt_large
        omega))) :
    ¬a.centralDefectTrigger b i := by
  intro htrigger
  exact hnot (a.centralRepresentationConditionsPrime_represents_castLengths
    b hPrime i htrigger hs ht)

/-- Under `I1^E`, the boundary gap is the order `R_(n+2)` itself. -/
theorem heHuI1E_boundaryGap_eq_boundaryNextOrder
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (hm : n + 1 ≤ m) (hnEven : Even n)
    (hI1 : a.HeHuI1E n hm) :
    a.orderGap ⟨n, by omega⟩ = a.order ⟨n + 1, by omega⟩ := by
  have hboundary : a.order ⟨n, by omega⟩ = 0 :=
    hI1.oddOrder ⟨n, by omega⟩ (Even.add_one hnEven)
  unfold orderGap
  rw [show (⟨n, by omega⟩ : Fin m).castSucc =
      (⟨n, by omega⟩ : Fin (m + 1)) by ext; rfl]
  rw [show (⟨n, by omega⟩ : Fin m).succ =
      (⟨n + 1, by omega⟩ : Fin (m + 1)) by ext; rfl]
  rw [hboundary, sub_zero]

/-- The strict alternative above the minimal dyadic gap is separated from it
by two.  This is the Corollary 2.3(i) step in Lemma 4.4. -/
theorem heHu_boundaryNextOrder_ge_two_sub_two_e_of_ne_minimal
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (hm : n + 1 ≤ m) (hnEven : Even n)
    (hI1 : a.HeHuI1E n hm)
    (hne : a.order ⟨n + 1, by omega⟩ ≠
      -(2 * (ramificationIndex K : Int))) :
    2 - 2 * (ramificationIndex K : Int) ≤
      a.order ⟨n + 1, by omega⟩ := by
  let boundary : Fin m := ⟨n, by omega⟩
  have hgap : a.orderGap boundary = a.order ⟨n + 1, by omega⟩ := by
    simpa only [boundary] using
      a.heHuI1E_boundaryGap_eq_boundaryNextOrder hm hnEven hI1
  have hlower := a.orderGap_ge_neg_two_mul_e boundary
  rw [hgap] at hlower
  by_cases hnegative : a.order ⟨n + 1, by omega⟩ < 0
  · have heven := a.orderGap_even_of_negative boundary (by
      rw [hgap]
      exact hnegative)
    rw [hgap] at heven
    rcases heven with ⟨d, hd⟩
    omega
  · have hePos := ramificationIndex_pos (K := K)
    omega

/-- The sole central index not eliminated by equation (4.1) for an even
target of rank `2k+2`. -/
def heHuLemma44TerminalIndex {m : Nat} (k : Nat)
    (hm : 2 * k + 2 ≤ m + 1) :
    CentralRepresentationIndex ((m + 1) + 2) (2 * k + 2) where
  val := 2 * k + 3
  one_lt := by omega
  lt_large := by omega
  le_small_succ := by omega

/-- The boundary long index at which Lemma 2.10(iii) is applied in the
terminal branch of Lemma 4.4. -/
def heHuLemma44BoundaryLongIndex {m : Nat} (k : Nat)
    (hm : 2 * k + 2 ≤ m + 1) :
    LongRepresentationIndex ((m + 1) + 2) (2 * k + 1) where
  val := 2 * k + 2
  one_lt := by omega
  succ_lt_large := by omega
  le_small_succ := by omega

/-- For the special target, Lemma 4.2 supplies the hypotheses of Beli's
Lemma 2.16 and hence identifies the original and revised central conditions. -/
theorem heHuLemma44_special_original_iff_prime
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (hm : 2 * k + 2 ≤ m + 1)
    (hAIntegral : Lattice.IsIntegral q L)
    (hAmbient : Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 2))
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega)) :
    a.CentralRepresentationConditions (heHuLemma43Target (K := K) k) ↔
      a.CentralRepresentationConditionsPrime
        (heHuLemma43Target (K := K) k) := by
  have hbIntegral := heHuLemma43Target_isIntegral (K := K) k
  unfold UnderlyingLatticeIsIntegral at hbIntegral
  have hOD := a.heHu2022Lemma42Sufficiency
    (m := m + 1) (t := 2 * k) hm
    (by refine ⟨k + 1, ?_⟩; omega)
    hAIntegral hAmbient hI1 (heHuLemma43Target (K := K) k) hbIntegral
  have htriggers := a.beli2019Lemma216
    (sourceLaws := sourceLaws)
    (targetLaws := beliUniversalAlphaLaws)
      (heHuLemma43Target (K := K) k) (by omega) hOD.1 hOD.2
  exact a.centralRepresentationConditions_iff_prime
    (heHuLemma43Target (K := K) k) htriggers

/- The revised central condition for the special target rules out its
terminal defect trigger, because Lemma 4.3 proves the required prefix is not
represented. -/
theorem heHuLemma44_special_prime_not_terminalTrigger
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (hm : 2 * k + 2 ≤ m + 1)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hPrime : a.CentralRepresentationConditionsPrime
      (heHuLemma43Target (K := K) k)) :
    ¬a.centralDefectTrigger (heHuLemma43Target (K := K) k)
      (heHuLemma43CentralIndex k hm) := by
  intro htrigger
  exact (a.heHu2022Lemma43_not_represents_atCentralIndex
      k (m := m + 1) hm hAIntegral hI1)
    (hPrime (heHuLemma43CentralIndex k hm) htrigger)

/-- If Theorem 2.8(iii) holds for the special second-column target, the
strict defect alternative isolated by Lemma 4.3 is impossible. -/
theorem heHuLemma44_special_cappedBoundary_le
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (hm : 2 * k + 2 ≤ m + 1)
    (hAIntegral : Lattice.IsIntegral q L)
    (hAmbient : Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 2))
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hR : 2 - 2 * (ramificationIndex K : Int) ≤
      a.order ⟨2 * k + 3, by omega⟩)
    (hSpecial : a.CentralRepresentationConditions
      (heHuLemma43Target (K := K) k)) :
    a.heHuAdjacentCappedDefect ⟨2 * k + 2, by omega⟩ ≤
      ((((1 : ℚ) -
        (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) : WithTop ℚ) := by
  have hPrime :=
    (a.heHuLemma44_special_original_iff_prime hm hAIntegral hAmbient hI1).mp
      hSpecial
  have hnotTrigger := a.heHuLemma44_special_prime_not_terminalTrigger
    (k := k) (m := m) hm hAIntegral hI1 hPrime
  by_contra hnot
  have hstrict :
      ((((1 : ℚ) -
        (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) : WithTop ℚ) <
        a.heHuAdjacentCappedDefect ⟨2 * k + 2, by omega⟩ :=
    lt_of_not_ge hnot
  apply hnotTrigger
  exact a.heHu2022Lemma43_defectTrigger
    (sourceLaws := sourceLaws) k (m := m + 1) hm hAIntegral
      hI1 hR hstrict

/-- Lemma 4.4, implication `(ii) -> (iii)`.  Only the special
`N_2^(2k+2)(Delta)` instance of Theorem 2.8(iii) is used. -/
theorem heHu2022Lemma44Necessity
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (hm : 2 * k + 2 ≤ m + 1)
    (hAIntegral : Lattice.IsIntegral q L)
    (hAmbient : Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 2))
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hSpecial : a.CentralRepresentationConditions
      (heHuLemma43Target (K := K) k)) :
    a.HeHuI2E (2 * k + 2) (by omega) := by
  let n := 2 * k + 2
  let idx : LongRepresentationIndex ((m + 1) + 2) (n + 1) :=
    { val := n
      one_lt := by simp only [n]; omega
      succ_lt_large := by omega
      le_small_succ := by omega }
  let boundary : Fin (m + 2) := ⟨idx.val, by
    have := idx.succ_lt_large
    omega⟩
  have hnEven : Even n := ⟨k + 1, by simp only [n]; omega⟩
  have hgap : a.orderGap boundary = a.order ⟨n + 1, by omega⟩ := by
    simpa only [boundary] using
      a.heHuI1E_boundaryGap_eq_boundaryNextOrder (by omega) hnEven hI1
  by_cases hminimal : a.order ⟨n + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int))
  · unfold HeHuI2E
    dsimp only
    left
    exact ((a.heHu2022Proposition26 boundary).alphaZero).2 (by
      rw [hgap]
      exact hminimal)
  · have hR : 2 - 2 * (ramificationIndex K : Int) ≤
        a.order ⟨n + 1, by omega⟩ :=
      a.heHu_boundaryNextOrder_ge_two_sub_two_e_of_ne_minimal
        (by omega) hnEven hI1 hminimal
    have hprevious : a.order ⟨idx.val - 1, by
        have := idx.succ_lt_large
        omega⟩ = -(2 * (ramificationIndex K : Int)) := by
      have h := hI1.evenOrder ⟨n - 1, by omega⟩ (by
        simp only [n]
        refine ⟨k + 1, ?_⟩
        omega)
      simpa only [idx] using h
    have hcurrent : a.order ⟨idx.val, by
        have := idx.succ_lt_large
        omega⟩ = 0 := by
      have h := hI1.oddOrder ⟨n, by omega⟩ (Even.add_one hnEven)
      simpa only [idx] using h
    have hnext : -(2 * (ramificationIndex K : Int)) <
        a.order ⟨idx.val + 1, idx.succ_lt_large⟩ := by
      simpa only [idx] using lt_of_lt_of_le (by omega :
        -(2 * (ramificationIndex K : Int)) <
          2 - 2 * (ramificationIndex K : Int)) hR
    let C := a.heHu2022Lemma210i hAIntegral idx hnEven
      hprevious hcurrent hnext
    let threshold : WithTop ℚ :=
      (((1 - a.order ⟨idx.val + 1, idx.succ_lt_large⟩ : Int) : ℚ) :
        WithTop ℚ)
    have hlower : threshold ≤ a.heHuAdjacentCappedDefect boundary := by
      have h := C.adjacentLower
      simpa only [threshold, heHuAdjacentCappedDefect, idx, boundary,
        Int.cast_sub, Int.cast_one] using h
    have hupperRaw := a.heHuLemma44_special_cappedBoundary_le
      (sourceLaws := sourceLaws) (k := k) (m := m) hm hAIntegral hAmbient hI1
        (by simpa only [n] using hR) hSpecial
    have hupper : a.heHuAdjacentCappedDefect boundary ≤ threshold := by
      simpa only [boundary, idx, n, threshold, Int.cast_sub,
        Int.cast_one] using hupperRaw
    have heq : a.heHuAdjacentCappedDefect boundary = threshold :=
      le_antisymm hupper hlower
    have heq' := heq
    unfold heHuAdjacentCappedDefect at heq'
    have hconsequences := C.equalityConsequences (by
      simpa only [boundary] using heq')
    unfold HeHuI2E
    dsimp only
    right
    exact ⟨by simpa only [boundary, n] using hconsequences.1,
      by simpa only [boundary, idx, threshold, n, Int.cast_sub,
        Int.cast_one] using heq⟩

/-- In the branch `S_n >= 1-2e`, the terminal revised trigger is impossible.
This is the second half of the published implication `(iii) -> (i)`: Lemma
2.10(iii) first fixes the mixed defect, and the discrete target boundary gap
then forces the other mixed defect to vanish. -/
theorem heHuLemma44_terminalTrigger_false_of_targetLast_ge
    (sourceLaws : Beli2006AlphaLaws.{u, v} K)
    (targetLaws : Beli2006AlphaLaws.{u, w} K)
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (b : GoodBONG r M (2 * k + 2))
    (hm : 2 * k + 2 ≤ m + 1)
    (hAIntegral : Lattice.IsIntegral q L)
    (hBIntegral : Lattice.IsIntegral r M)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (hLastLower : 1 - 2 * (ramificationIndex K : Int) ≤
      b.order ⟨2 * k + 1, by omega⟩) :
    ¬a.centralDefectTrigger b (heHuLemma44TerminalIndex k hm) := by
  intro htrigger
  let cidx := heHuLemma44TerminalIndex k hm
  let idx := heHuLemma44BoundaryLongIndex k hm
  let boundary : Fin (m + 2) := ⟨2 * k + 2, by omega⟩
  let sourcePrevious : Fin ((m + 1) + 2) := ⟨2 * k + 1, by omega⟩
  let sourceAt : Fin ((m + 1) + 2) := ⟨2 * k + 2, by omega⟩
  let sourceNext : Fin ((m + 1) + 2) := ⟨2 * k + 3, by omega⟩
  let targetPrevious : Fin (2 * k + 2) := ⟨2 * k, by omega⟩
  let targetLast : Fin (2 * k + 2) := ⟨2 * k + 1, by omega⟩
  let targetGap : Fin (2 * k + 1) := ⟨2 * k, by omega⟩
  have hLastLower' : 1 - 2 * (ramificationIndex K : Int) ≤
      b.order targetLast := by
    simpa only [targetLast] using hLastLower
  have hcTarget :
      (⟨cidx.val - 2, by
        have := cidx.one_lt
        have := cidx.le_small_succ
        omega⟩ : Fin (2 * k + 2)) = targetLast := by
    apply Fin.ext
    dsimp only [cidx, heHuLemma44TerminalIndex, targetLast]
    omega
  have hcSource :
      (⟨cidx.val, cidx.lt_large⟩ : Fin ((m + 1) + 2)) = sourceNext := by
    apply Fin.ext
    rfl
  have hBoundaryAlphaIndex :
      (⟨cidx.val - 1, by
        have := cidx.one_lt
        have := cidx.lt_large
        omega⟩ : Fin (m + 2)) = boundary := by
    apply Fin.ext
    dsimp only [cidx, heHuLemma44TerminalIndex, boundary]
    omega
  have hTargetAlphaIndex :
      (⟨cidx.val - 2 - 1, by
        have := cidx.one_lt
        have := cidx.le_small_succ
        omega⟩ : Fin (2 * k + 1)) = targetGap := by
    apply Fin.ext
    dsimp only [cidx, heHuLemma44TerminalIndex, targetGap]
    omega
  have hnEven : Even (2 * k + 2) := ⟨k + 1, by omega⟩
  have hEvenPrevious : Even ((2 * k + 1) + 1) :=
    ⟨k + 1, by omega⟩
  have hOddAt : Odd ((2 * k + 2) + 1) :=
    ⟨k + 1, by omega⟩
  have hSourcePrevious : a.order sourcePrevious =
      -(2 * (ramificationIndex K : Int)) := by
    simpa only [sourcePrevious] using
      hI1.evenOrder (⟨2 * k + 1, by omega⟩ : Fin (2 * k + 2))
        hEvenPrevious
  have hSourceAt : a.order sourceAt = 0 := by
    simpa only [sourceAt] using
      hI1.oddOrder (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 3)) hOddAt
  have hSourceGap : a.orderGap boundary = a.order sourceNext := by
    simpa only [boundary, sourceNext] using
      a.heHuI1E_boundaryGap_eq_boundaryNextOrder (by omega) hnEven hI1
  have hRgt : b.order targetLast < a.order sourceNext := by
    have h := htrigger.1
    rw [hcTarget, hcSource] at h
    exact h
  have hAlphaNe : a.alphaValue boundary ≠ 0 := by
    intro hzero
    have hminimal := ((a.heHu2022Proposition26 boundary).alphaZero).mp hzero
    rw [hSourceGap] at hminimal
    have hePos := ramificationIndex_pos (K := K)
    omega
  have hI2' := hI2
  unfold HeHuI2E at hI2'
  dsimp only at hI2'
  rcases hI2' with hAlphaZero | hBoundary
  · exact hAlphaNe (by simpa only [boundary] using hAlphaZero)
  have hAlphaOne : a.alphaValue boundary = 1 := by
    simpa only [boundary] using hBoundary.1
  have hLocal :
      a.truncatedPrefixDefect a (-1) (2 * k + 2) (2 * k + 4) =
        (((1 - a.order sourceNext : Int) : ℚ) : WithTop ℚ) := by
    unfold heHuAdjacentCappedDefect at hBoundary
    simpa only [boundary, sourceNext, Int.cast_sub, Int.cast_one] using
      hBoundary.2
  have hSourceNextLower :
      -(2 * (ramificationIndex K : Int)) < a.order sourceNext := by
    have hePos := ramificationIndex_pos (K := K)
    omega
  have h210 := a.heHu2022Lemma210iii b hAIntegral hBIntegral idx
    (by simpa only [idx, heHuLemma44BoundaryLongIndex] using hnEven)
    (by
      have hindex :
          (⟨idx.val - 1, by
            have := idx.succ_lt_large
            omega⟩ : Fin ((m + 1) + 2)) = sourcePrevious := by
        apply Fin.ext
        dsimp only [idx, heHuLemma44BoundaryLongIndex, sourcePrevious]
        omega
      rw [hindex]
      exact hSourcePrevious)
    (by
      have hindex :
          (⟨idx.val, by
            have := idx.succ_lt_large
            omega⟩ : Fin ((m + 1) + 2)) = sourceAt := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact hSourceAt)
    (by
      have hindex :
          (⟨idx.val + 1, idx.succ_lt_large⟩ : Fin ((m + 1) + 2)) =
            sourceNext := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact hSourceNextLower)
    (by
      convert hLocal using 1 <;>
        dsimp only [idx, heHuLemma44BoundaryLongIndex])
  have hCurrent : a.centralCurrentDefect b cidx =
      (((1 - a.order sourceNext : Int) : ℚ) : WithTop ℚ) := by
    rcases h210 with hMixed | hWitness
    · unfold centralCurrentDefect
      have hLargeLength : cidx.val + 1 = idx.val + 2 := by
        dsimp only [cidx, idx, heHuLemma44TerminalIndex,
          heHuLemma44BoundaryLongIndex]
      have hSmallLength : cidx.val - 1 = idx.val := by
        dsimp only [cidx, idx, heHuLemma44TerminalIndex,
          heHuLemma44BoundaryLongIndex]
        omega
      have hNextIndex :
          (⟨idx.val + 1, idx.succ_lt_large⟩ : Fin ((m + 1) + 2)) =
            sourceNext := by
        apply Fin.ext
        rfl
      rw [hLargeLength, hSmallLength]
      rw [hNextIndex] at hMixed
      exact hMixed
    · rcases hWitness with
        ⟨j, hjEven, _hjBefore, hRLeJ, _hBetaBounds⟩
      have hjSuccOdd : Odd j.succ.val := by
        simpa only [Fin.val_succ] using Even.add_one hjEven
      have hlastOdd : Odd targetLast.val := by
        refine ⟨k, ?_⟩
        simp only [targetLast]
      have hjLeLast : j.succ ≤ targetLast := by
        apply Fin.mk_le_mk.mpr
        have := j.isLt
        change j.val + 1 ≤ 2 * k + 1
        omega
      have hJLeLast :=
        (b.heHu2022Proposition27i hBIntegral).evenIndexed
          j.succ targetLast hjLeLast hjSuccOdd hlastOdd |>.2
      have hRLeJ' : a.order sourceNext ≤ b.order j.succ := by
        simpa only [idx, heHuLemma44BoundaryLongIndex, sourceNext] using hRLeJ
      exact (not_lt_of_ge (hRLeJ'.trans hJLeLast) hRgt).elim
  have hPreviousLe :
      a.centralPreviousDefect b cidx ≤ (1 : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_leftCap b (-1)
      cidx.val (cidx.val - 2)
    rw [a.prefixAlphaCap_of_internal (by
      dsimp only [cidx, heHuLemma44TerminalIndex]
      omega) (by
      dsimp only [cidx, heHuLemma44TerminalIndex]
      omega)] at hcap
    rw [hBoundaryAlphaIndex, hAlphaOne] at hcap
    norm_num at hcap
    simpa only [centralPreviousDefect] using hcap
  have hSumUpper :
      a.centralPreviousDefect b cidx + a.centralCurrentDefect b cidx ≤
        (((2 - a.order sourceNext : Int) : ℚ) : WithTop ℚ) := by
    rw [hCurrent]
    calc
      a.centralPreviousDefect b cidx +
          (((1 - a.order sourceNext : Int) : ℚ) : WithTop ℚ) ≤
          (1 : WithTop ℚ) +
            (((1 - a.order sourceNext : Int) : ℚ) : WithTop ℚ) :=
        add_le_add hPreviousLe le_rfl
      _ = (((2 - a.order sourceNext : Int) : ℚ) : WithTop ℚ) := by
        norm_cast
        ring
  have hFirstStrict :
      (((2 * (ramificationIndex K : ℚ) + (b.order targetLast : ℚ) -
        (a.order sourceNext : ℚ) : ℚ)) : WithTop ℚ) <
        (((2 - a.order sourceNext : Int) : ℚ) : WithTop ℚ) := by
    have hTriggerSecond := htrigger.2
    rw [hcTarget, hcSource] at hTriggerSecond
    exact hTriggerSecond.trans_le hSumUpper
  have hLastStrict : b.order targetLast <
      2 - 2 * (ramificationIndex K : Int) := by
    norm_cast at hFirstStrict
    have hFirstStrictInt :
        2 * (ramificationIndex K : Int) + b.order targetLast -
            a.order sourceNext < 2 - a.order sourceNext := by
      exact_mod_cast hFirstStrict
    omega
  have hTargetPreviousNonnegative : 0 ≤ b.order targetPrevious := by
    have C := b.heHu2022Proposition27i hBIntegral
    have h := C.oddIndexed 0 targetPrevious (Fin.zero_le targetPrevious)
      Even.zero (by
        refine ⟨k, ?_⟩
        simp only [targetPrevious]
        omega)
    exact h.1.trans h.2
  have hTargetGapFormula : b.orderGap targetGap =
      b.order targetLast - b.order targetPrevious := by
    unfold orderGap
    congr 1
  have hTargetGapLower := b.orderGap_ge_neg_two_mul_e targetGap
  have hTargetGapStrict : b.orderGap targetGap <
      2 - 2 * (ramificationIndex K : Int) := by
    rw [hTargetGapFormula]
    omega
  have hTargetGapNonpositive : b.orderGap targetGap ≤ 0 := by
    have hePos := ramificationIndex_pos (K := K)
    omega
  have hTargetGapEven :=
    (b.heHu2022Corollary23i targetGap).2 hTargetGapNonpositive
  have hTargetGapMinimal : b.orderGap targetGap =
      -(2 * (ramificationIndex K : Int)) := by
    rcases hTargetGapEven with ⟨z, hz⟩
    omega
  have hTargetAlphaZero : b.alphaValue targetGap = 0 :=
    ((b.heHu2022Proposition26 targetGap).alphaZero).2 hTargetGapMinimal
  have hPreviousZero : a.centralPreviousDefect b cidx = 0 := by
    have hupper := a.truncatedPrefixDefect_le_rightCap b (-1)
      cidx.val (cidx.val - 2)
    rw [b.prefixAlphaCap_of_internal (by
      dsimp only [cidx, heHuLemma44TerminalIndex]
      omega) (by
      dsimp only [cidx, heHuLemma44TerminalIndex]
      omega)] at hupper
    rw [hTargetAlphaIndex, hTargetAlphaZero] at hupper
    norm_num at hupper
    have hupper' : a.centralPreviousDefect b cidx ≤ 0 := by
      simpa only [centralPreviousDefect] using hupper
    have hlower : 0 ≤ a.centralPreviousDefect b cidx := by
      unfold centralPreviousDefect
      exact a.truncatedPrefixDefect_nonneg
        (alphaV := sourceLaws) (alphaW := targetLaws)
        b (-1) cidx.val (cidx.val - 2)
    exact le_antisymm hupper' hlower
  have hFinalStrict := htrigger.2
  rw [hcTarget, hcSource] at hFinalStrict
  have hcidxEq : heHuLemma44TerminalIndex k hm = cidx := rfl
  rw [hcidxEq, hPreviousZero, hCurrent] at hFinalStrict
  norm_num at hFinalStrict
  have hLastLowerQ :
      ((1 - 2 * (ramificationIndex K : Int) : Int) : ℚ) ≤
        (b.order targetLast : ℚ) := by
    exact_mod_cast hLastLower'
  push_cast at hLastLowerQ
  have honeLeQ : (1 : ℚ) ≤
      2 * (ramificationIndex K : ℚ) + (b.order targetLast : ℚ) := by
    linarith
  have honeLeTop : (1 : WithTop ℚ) ≤
      2 * ((ramificationIndex K : ℚ) : WithTop ℚ) +
        ((b.order targetLast : ℚ) : WithTop ℚ) := by
    calc
      (1 : WithTop ℚ) = ((1 : ℚ) : WithTop ℚ) := rfl
      _ ≤ ((2 * (ramificationIndex K : ℚ) +
          (b.order targetLast : ℚ) : ℚ) : WithTop ℚ) :=
        WithTop.coe_le_coe.mpr honeLeQ
      _ = 2 * ((ramificationIndex K : ℚ) : WithTop ℚ) +
          ((b.order targetLast : ℚ) : WithTop ℚ) := by norm_num
  exact (not_lt_of_ge honeLeTop) hFinalStrict

/-- If `S_n=-2e`, Proposition 2.7(iii)--(v) gives two endpoint towers and
one additional unit line.  The endpoint-tower representation theorem is the
coordinate-level form of the paper's application of Lemma 3.14(i). -/
theorem heHuLemma44_terminal_represents_of_targetLast_eq_minimal
    (sourceLaws : Beli2006AlphaLaws.{u, v} K)
    (targetLaws : Beli2006AlphaLaws.{u, w} K)
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (b : GoodBONG r M (2 * k + 2))
    (hm : 2 * k + 2 ≤ m + 1)
    (hBIntegral : Lattice.IsIntegral r M)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hLast : b.order ⟨2 * k + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int))) :
    DiagonalRepresents
      (b.prefixValues (2 * k + 2) le_rfl)
      (a.prefixValues (2 * k + 3) (by omega)) := by
  let targetLast : Fin (2 * k + 2) := ⟨2 * k + 1, by omega⟩
  let targetFirstOdd : Fin (2 * k + 2) := ⟨1, by omega⟩
  have hTargetLastOdd : Odd targetLast.val := by
    refine ⟨k, ?_⟩
    simp only [targetLast]
  have hTargetFirstOdd : Odd targetFirstOdd.val := by
    refine ⟨0, ?_⟩
    change 1 = 2 * 0 + 1
    rfl
  let C := b.heHu2022Proposition27iiiiv hBIntegral targetLast
    hTargetLastOdd (by simpa only [targetLast] using hLast)
  have hTargetFirst : b.order 0 = 0 := by
    have hpair := C.pairOrdersAndDefects targetFirstOdd (by
      apply Fin.mk_le_mk.mpr
      omega) hTargetFirstOdd
    have hindex :
        (⟨targetFirstOdd.val - 1, by omega⟩ : Fin (2 * k + 2)) = 0 := by
      apply Fin.ext
      change 1 - 1 = 0
      omega
    simpa only [hindex] using hpair.1
  have hSourceFirst : a.order 0 = 0 := by
    have hodd : Odd ((0 : Nat) + 1) := ⟨0, rfl⟩
    exact hI1.oddOrder (0 : Fin (2 * k + 3)) hodd
  have hSourceLast : a.order ⟨2 * k + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) := by
    have heven : Even ((2 * k + 1) + 1) := ⟨k + 1, by omega⟩
    exact hI1.evenOrder (⟨2 * k + 1, by omega⟩ : Fin (2 * k + 2))
      heven
  have hSourceExtra : a.order ⟨2 * k + 2, by omega⟩ = 0 := by
    have hodd : Odd ((2 * k + 2) + 1) := ⟨k + 1, by omega⟩
    exact hI1.oddOrder (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 3))
      hodd
  have hSourceLastForPairs :
      a.order ⟨2 * (k + 1) - 1, by omega⟩ =
        -(2 * (ramificationIndex K : Int)) := by
    convert hSourceLast using 1
    congr 1
  have hTargetLastForPairs :
      b.order ⟨2 * (k + 1) - 1, by omega⟩ =
        -(2 * (ramificationIndex K : Int)) := by
    convert hLast using 1
    congr 1
  have hrep := endpointTowers_representationInUnaryExtension_cross
    sourceLaws targetLaws (pairs := k + 1) a b 0
      (by omega) (by omega) (by omega)
      hSourceFirst (by simpa only [Int.zero_sub] using hSourceLastForPairs)
      hTargetFirst (by simpa only [Int.zero_sub] using hTargetLastForPairs)
      hSourceExtra
  exact prefixRepresents_cast b a (by omega) (by omega) hrep

/-- For an arbitrary integral even-rank target, Lemma 4.2 supplies conditions
(i)--(ii) of Theorem 2.8, so Beli's Lemma 2.16 identifies the original and
revised central conditions. -/
theorem heHuLemma44_original_iff_prime
    (sourceLaws : Beli2006AlphaLaws.{u, v} K)
    (targetLaws : Beli2006AlphaLaws.{u, w} K)
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (b : GoodBONG r M (2 * k + 2))
    (hm : 2 * k + 2 ≤ m + 1)
    (hAIntegral : Lattice.IsIntegral q L)
    (hAmbient : Lattice.AmbientlyNUniversal.{u, v, w} q (2 * k + 2))
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hBIntegral : Lattice.IsIntegral r M) :
    a.CentralRepresentationConditions b ↔
      a.CentralRepresentationConditionsPrime b := by
  have hOD : a.RepresentationOrderCondition b (by omega) ∧
      a.RepresentationDefectCondition b :=
    (a.heHu2022Lemma42Sufficiency
      (m := m + 1) (t := 2 * k) hm ⟨k + 1, by omega⟩
        hAIntegral hAmbient hI1) b hBIntegral
  have htriggers := a.beli2019Lemma216
    (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b (by omega) hOD.1 hOD.2
  exact a.centralRepresentationConditions_iff_prime b htriggers

/-- Lemma 4.4, implication `(iii) -> (i)`: condition `I2^E(n)` implies
Theorem 2.8(iii) for every integral target of even rank `n=2k+2`. -/
theorem heHu2022Lemma44Sufficiency
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (hm : 2 * k + 2 ≤ m + 1)
    (hAIntegral : Lattice.IsIntegral q L)
    (hAmbient : Lattice.AmbientlyNUniversal.{u, v, w} q (2 * k + 2))
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega)) :
    HeHuAllCentralRepresentationConditions.{u, v, w}
      (n := 2 * k + 1) a := by
  intro W _ _ r M b hBIntegral
  let targetLaws : Beli2006AlphaLaws.{u, w} K := beliUniversalAlphaLaws
  apply (a.heHuLemma44_original_iff_prime sourceLaws targetLaws b hm
    hAIntegral hAmbient hI1 hBIntegral).mpr
  intro i htrigger
  by_cases hiTerminal : i.val = 2 * k + 3
  · let terminal := heHuLemma44TerminalIndex k hm
    have hiEq : i = terminal := by
      cases i with
      | mk val hone hlarge hsmall =>
          dsimp only at hiTerminal
          subst val
          rfl
    subst i
    let targetLast : Fin (2 * k + 2) := ⟨2 * k + 1, by omega⟩
    have hlastOdd : Odd targetLast.val := by
      refine ⟨k, ?_⟩
      simp only [targetLast]
    have hLastLower : -(2 * (ramificationIndex K : Int)) ≤
        b.order targetLast :=
      ((b.heHu2022Proposition27i hBIntegral).evenIndexed
        targetLast targetLast le_rfl hlastOdd hlastOdd).1
    by_cases hLast : b.order targetLast =
        -(2 * (ramificationIndex K : Int))
    · have hrep := a.heHuLemma44_terminal_represents_of_targetLast_eq_minimal
        sourceLaws targetLaws b hm hBIntegral hI1 (by
          simpa only [targetLast] using hLast)
      exact prefixRepresents_cast b a (by
        change 2 * k + 2 = 2 * k + 3 - 1
        omega) (by
        change 2 * k + 3 = 2 * k + 3
        rfl) hrep
    · have hLastHigher : 1 - 2 * (ramificationIndex K : Int) ≤
          b.order ⟨2 * k + 1, by omega⟩ := by
        have hLastLower' : -(2 * (ramificationIndex K : Int)) ≤
            b.order ⟨2 * k + 1, by omega⟩ := by
          simpa only [targetLast] using hLastLower
        have hLast' : b.order ⟨2 * k + 1, by omega⟩ ≠
            -(2 * (ramificationIndex K : Int)) := by
          simpa only [targetLast] using hLast
        omega
      exact (a.heHuLemma44_terminalTrigger_false_of_targetLast_ge
        sourceLaws targetLaws b hm hAIntegral hBIntegral hI1 hI2
          hLastHigher htrigger).elim
  · have hiLast : i.val ≤ 2 * k + 2 := by
      have := i.le_small_succ
      omega
    have hbound := a.heHuI1E_sourceNext_le_targetPrevious b hm
      ⟨k + 1, by omega⟩ hI1 hBIntegral (i := i.val)
        (by have := i.one_lt; omega) hiLast
    exact (not_lt_of_ge hbound htrigger.1).elim

/-- Lemma 4.4, implication `(i) -> (iii)`, obtained by specializing the
universal central condition to the published test lattice
`N_2^(2k+2)(Delta)`. -/
theorem heHu2022Lemma44NecessityAll
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (hm : 2 * k + 2 ≤ m + 1)
    (hAIntegral : Lattice.IsIntegral q L)
    (hAmbient : Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 2))
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hAll : HeHuAllCentralRepresentationConditions.{u, v, u}
      (n := 2 * k + 1) a) :
    a.HeHuI2E (2 * k + 2) (by omega) := by
  have hSpecialIntegral := heHuLemma43Target_isIntegral (K := K) k
  unfold UnderlyingLatticeIsIntegral at hSpecialIntegral
  have hSpecial := hAll (heHuLemma43Target (K := K) k) hSpecialIntegral
  exact a.heHu2022Lemma44Necessity hm hAIntegral hAmbient hI1 hSpecial

/-- He--Hu, Lemma 4.4, complete equivalence of the universal central
representation condition, its single published test lattice, and
`I2^E(2k+2)`. -/
theorem heHu2022Lemma44
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (hm : 2 * k + 2 ≤ m + 1)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega)) :
    Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 2) →
      (HeHuAllCentralRepresentationConditions.{u, v, u}
          (n := 2 * k + 1) a ↔
        a.HeHuI2E (2 * k + 2) (by omega)) := by
  intro hAmbient
  constructor
  · exact a.heHu2022Lemma44NecessityAll hm hAIntegral hAmbient hI1
  · exact a.heHu2022Lemma44Sufficiency hm hAIntegral hAmbient hI1

end BONG.GoodBONG

end Bong
