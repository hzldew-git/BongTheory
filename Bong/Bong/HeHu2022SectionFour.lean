/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.HeHu2022Conditions
import Bong.Bong.HeHu2022SectionTwo

/-!
# He--Hu 2022, Section 4: the even-rank conditions

This file fixes the exact Lean statements of the three conditions in
He--Hu, Theorem 4.1.  Paper indices are one-based, whereas `GoodBONG.order`
and `GoodBONG.alphaValue` use zero-based `Fin` indices.  In particular,
the paper's `R_{n+2}` and `alpha_{n+1}` occur below at the Lean indices
`n+1` and `n`, respectively.

The source throughout Section 4 assumes that the target rank `n` is even,
`2 <= n`, and that the source rank `m` is at least `n+2`.  Parity and
integrality are hypotheses of the numbered theorems rather than parts of
the three named conditions themselves.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice

/-- The ambient-space component of rank-`n` universality, stated only for
spaces presented by integral rank-`n` lattices.  This is exactly the ambient
condition needed by He--Hu, Theorems 4.1 and 5.1 and avoids choosing a lattice
on an otherwise bare quadratic space. -/
def AmbientlyNUniversal (q : QuadraticSpace K V) (n : Nat) : Prop :=
  ∀ {W : Type w} [AddCommGroup W] [Module K W]
    (r : QuadraticSpace K W) (M : Lattice K W),
    Module.finrank K W = n → IsIntegral r M → q.Represents r

end Lattice

namespace BONG.GoodBONG

/-- All four conditions of He--Hu, Theorem 2.8, uniformly over integral
targets of rank `n+1`.  The parameter `n` here is the predecessor of the
paper rank because `RepresentationConditions` follows the native
`GoodBONG (n+1)` convention. -/
def HeHuAllRepresentationConditions {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hRank : n ≤ m) : Prop :=
  ∀ {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (b : GoodBONG r M (n + 1)), Lattice.IsIntegral r M →
      RepresentationConditions a b hRank

/-- Theorem 2.8(i)--(ii), uniformly over all integral targets. -/
def HeHuAllOrderAndDefectConditions {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hRank : n ≤ m) : Prop :=
  ∀ {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (b : GoodBONG r M (n + 1)), Lattice.IsIntegral r M →
      a.RepresentationOrderCondition b hRank ∧
        a.RepresentationDefectCondition b

/-- Theorem 2.8(iii), uniformly over all integral targets. -/
def HeHuAllCentralRepresentationConditions {m n : Nat}
    (a : GoodBONG q L (m + 1)) : Prop :=
  ∀ {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (b : GoodBONG r M (n + 1)), Lattice.IsIntegral r M →
      a.CentralRepresentationConditions b

/-- Theorem 2.8(iv), uniformly over all integral targets. -/
def HeHuAllLongRepresentationConditions {m n : Nat}
    (a : GoodBONG q L (m + 1)) : Prop :=
  ∀ {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (b : GoodBONG r M (n + 1)), Lattice.IsIntegral r M →
      a.LongRepresentationConditions b

/-- Splitting the four fields of `RepresentationConditions` commutes with
universal quantification over the target lattices. -/
theorem heHuAllRepresentationConditions_iff_components {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hRank : n ≤ m) :
    HeHuAllRepresentationConditions.{u, v, w} a hRank ↔
      HeHuAllOrderAndDefectConditions.{u, v, w} a hRank ∧
        HeHuAllCentralRepresentationConditions.{u, v, w} (n := n) a ∧
          HeHuAllLongRepresentationConditions.{u, v, w} (n := n) a := by
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

/-- A generic factorization of lattice `n+1`-universality into ambient-space
universality and the four Beli--He--Hu representation conditions.  This is
the formal bridge used in both Sections 4 and 5. -/
theorem heHuNUniversality_factorization {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hRank : n ≤ m) :
    Lattice.IsNUniversal.{u, v, w} q L (n + 1) ↔
      Lattice.IsIntegral q L ∧
        Lattice.AmbientlyNUniversal.{u, v, w} q (n + 1) ∧
          HeHuAllRepresentationConditions.{u, v, w} a hRank := by
  constructor
  · intro hUniversal
    refine ⟨hUniversal.1, ?_, ?_⟩
    · change ∀ {W : Type w} [AddCommGroup W] [Module K W]
        (r : QuadraticSpace K W) (M : Lattice K W),
        Module.finrank K W = n + 1 → Lattice.IsIntegral r M →
          q.Represents r
      intro W _ _ r M hfin hM
      exact (hUniversal.2 r M hfin hM).ambient
    · change ∀ {W : Type w} [AddCommGroup W] [Module K W]
        {r : QuadraticSpace K W} {M : Lattice K W}
        (b : GoodBONG r M (n + 1)), Lattice.IsIntegral r M →
          RepresentationConditions a b hRank
      intro W _ _ r M b hM
      have hfin : Module.finrank K W = n + 1 :=
        b.toBONG.length_eq_finrank.symm
      have hrep := hUniversal.2 r M hfin hM
      exact (a.heHu2022Theorem28 hRank hrep.ambient b).mp hrep
  · rintro ⟨hIntegral, hAmbient, hConditions⟩
    refine ⟨hIntegral, ?_⟩
    change ∀ {W : Type w} [AddCommGroup W] [Module K W]
      (r : QuadraticSpace K W) (M : Lattice K W),
      Module.finrank K W = n + 1 → Lattice.IsIntegral r M →
        Lattice.Represents q r L M
    intro W _ _ r M hfin hM
    letI : BONGStructuralLaws.{u, w} K := bongStructuralLawsProved K
    let b : GoodBONG r M (n + 1) :=
      (GoodBONG.ofLattice r M).castLength hfin
    exact (a.heHu2022Theorem28 hRank (hAmbient r M hfin hM) b).mpr
      (hConditions b hM)

/-- He--Hu, Theorem 4.1, condition `I1^E(n)`.

The first conjunct covers the paper indices in `[1,n+1]_O`; the second
covers `[1,n]_E`. -/
def HeHuI1E {m : Nat} (a : GoodBONG q L (m + 1)) (n : Nat)
    (hm : n + 1 ≤ m) : Prop :=
  (∀ i : Fin (n + 1), Odd (i.1 + 1) →
      a.order ⟨i.1, by omega⟩ = 0) ∧
    (∀ i : Fin n, Even (i.1 + 1) →
      a.order ⟨i.1, by omega⟩ =
        -(2 * (ramificationIndex K : Int)))

/-- He--Hu, Theorem 4.1, condition `I2^E(n)`.

`heHuAdjacentCappedDefect` is the paper's bracketed defect
`d[-a_{n+1,n+2}]`, not the uncapped field defect. -/
noncomputable def HeHuI2E {m : Nat} (a : GoodBONG q L (m + 1)) (n : Nat)
    (hm : n + 1 ≤ m) : Prop :=
  let boundary : Fin m := ⟨n, by omega⟩
  a.alphaValue boundary = 0 ∨
    (a.alphaValue boundary = 1 ∧
      a.heHuAdjacentCappedDefect boundary =
        ((((1 : ℚ) - (a.order ⟨n + 1, by omega⟩ : ℚ)) : ℚ) : WithTop ℚ))

/-- He--Hu, Theorem 4.1, condition `I3^E(n)`.

The quantified rank proof records the source phrase "if `m >= n+3`".
Keeping it explicit makes the condition meaningful also in the exceptional
quaternary case `m=n+2=4`, where it is vacuous. -/
def HeHuI3E {m : Nat} (a : GoodBONG q L (m + 1)) (n : Nat)
    (_hm : n + 1 ≤ m) : Prop :=
  ∀ hmStable : n + 2 ≤ m,
    2 * (ramificationIndex K : Int) <
        a.order ⟨n + 2, by omega⟩ - a.order ⟨n + 1, by omega⟩ →
      a.order ⟨n + 1, by omega⟩ =
          -(2 * (ramificationIndex K : Int)) ∧
        ((4 ≤ n ∨
            (n = 2 ∧ a.heHuPrefixDefect 4 =
              (((2 * (ramificationIndex K : Int) : Int) : ℚ) : WithTop ℚ))) →
          a.order ⟨n + 2, by omega⟩ = 1)

/-- The three lattice-invariant conditions appearing on the right-hand side
of He--Hu, Theorem 4.1. -/
structure HeHuEvenSectionConditions {m : Nat} (a : GoodBONG q L (m + 1))
    (n : Nat) (hm : n + 1 ≤ m) : Prop where
  i1 : a.HeHuI1E n hm
  i2 : a.HeHuI2E n hm
  i3 : a.HeHuI3E n hm

/-- The odd paper-index clause of `I1^E(n)`, exposed without unfolding the
condition at downstream call sites. -/
theorem HeHuI1E.oddOrder {m n : Nat} {a : GoodBONG q L (m + 1)}
    {hm : n + 1 ≤ m} (h : a.HeHuI1E n hm)
    (i : Fin (n + 1)) (hi : Odd (i.1 + 1)) :
    a.order ⟨i.1, by omega⟩ = 0 :=
  h.1 i hi

/-- The even paper-index clause of `I1^E(n)`. -/
theorem HeHuI1E.evenOrder {m n : Nat} {a : GoodBONG q L (m + 1)}
    {hm : n + 1 ≤ m} (h : a.HeHuI1E n hm)
    (i : Fin n) (hi : Even (i.1 + 1)) :
    a.order ⟨i.1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) :=
  h.2 i hi

/-- For even paper rank `n`, condition `I1^E(n)` is exactly the alternating
initial profile from Theorem 1.1 together with the final odd-index order
`R_{n+1}=0`.  This lemma is the index-translation bridge used in Section 6. -/
theorem heHuI1E_iff_alternatingInitialOrders_and_boundary
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (hmStable : n + 2 ≤ m) (hnEven : Even n) :
    a.HeHuI1E n (by omega) ↔
      a.HeHuAlternatingInitialOrders n (by omega) ∧
        a.order ⟨n, by omega⟩ = 0 := by
  constructor
  · rintro ⟨hodd, heven⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i hi
      exact hodd ⟨i.1, by omega⟩ hi
    · intro i hi
      exact heven i hi
    · exact hodd ⟨n, by omega⟩ (Even.add_one hnEven)
  · rintro ⟨⟨hodd, heven⟩, hboundary⟩
    constructor
    · intro i hi
      by_cases hilast : i.1 = n
      · simpa only [hilast] using hboundary
      · exact hodd ⟨i.1, by omega⟩ hi
    · intro i hi
      exact heven i hi

/-- Condition `I2^E(n)` forces the boundary alpha invariant to be at most
one.  This is the implication used in Theorem 4.7. -/
theorem HeHuI2E.alphaBoundary_le_one {m n : Nat}
    {a : GoodBONG q L (m + 1)} {hm : n + 1 ≤ m}
    (h : a.HeHuI2E n hm) :
    a.alphaValue ⟨n, by omega⟩ ≤ 1 := by
  unfold HeHuI2E at h
  dsimp only at h
  rcases h with halpha | ⟨halpha, _⟩
  · rw [halpha]
    norm_num
  · rw [halpha]

/-- Discreteness of Proposition 2.6 turns the inequality in Theorem 4.7
into the two alternatives `alpha_{n+1}=0` or `1`. -/
theorem alphaBoundary_eq_zero_or_one_of_le_one {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hm : n + 1 ≤ m)
    (hle : a.alphaValue ⟨n, by omega⟩ ≤ 1) :
    a.alphaValue ⟨n, by omega⟩ = 0 ∨
      a.alphaValue ⟨n, by omega⟩ = 1 := by
  by_cases hzero : a.alphaValue ⟨n, by omega⟩ = 0
  · exact Or.inl hzero
  · right
    exact le_antisymm hle
      (a.heHuOne_le_alphaValue_of_ne_zero ⟨n, by omega⟩ hzero)

/-- A logically normalized form of `I2^E(n)`: the boundary alpha is at most
one, and its nonzero case has the exact capped defect prescribed by the
paper. -/
theorem heHuI2E_iff_alpha_le_one_and_capped_boundary
    {m n : Nat} (a : GoodBONG q L (m + 1)) (hm : n + 1 ≤ m) :
    a.HeHuI2E n hm ↔
      a.alphaValue ⟨n, by omega⟩ ≤ 1 ∧
        (a.alphaValue ⟨n, by omega⟩ = 1 →
          a.heHuAdjacentCappedDefect ⟨n, by omega⟩ =
            ((((1 : ℚ) - (a.order ⟨n + 1, by omega⟩ : ℚ)) : ℚ) :
              WithTop ℚ)) := by
  constructor
  · intro h
    refine ⟨h.alphaBoundary_le_one, ?_⟩
    intro halpha
    unfold HeHuI2E at h
    dsimp only at h
    rcases h with hzero | hone
    · rw [hzero] at halpha
      norm_num at halpha
    · exact hone.2
  · rintro ⟨hle, hcapped⟩
    unfold HeHuI2E
    dsimp only
    rcases a.alphaBoundary_eq_zero_or_one_of_le_one hm hle with
      hzero | hone
    · exact Or.inl hzero
    · exact Or.inr ⟨hone, hcapped hone⟩

/-- Outside the exceptional order `R_{n+2}=2-2e`, Proposition 2.6(vi)
already supplies the exact capped defect required by `I2^E(n)`. -/
theorem cappedBoundary_eq_of_i1E_alpha_one_of_order_ne
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (hm : n + 1 ≤ m) (hnEven : Even n)
    (hI1 : a.HeHuI1E n hm)
    (halpha : a.alphaValue ⟨n, by omega⟩ = 1)
    (horderNe : a.order ⟨n + 1, by omega⟩ ≠
      2 - 2 * (ramificationIndex K : Int)) :
    a.heHuAdjacentCappedDefect ⟨n, by omega⟩ =
      ((((1 : ℚ) - (a.order ⟨n + 1, by omega⟩ : ℚ)) : ℚ) :
        WithTop ℚ) := by
  have hprevious : a.order ⟨n, by omega⟩ = 0 :=
    hI1.oddOrder ⟨n, by omega⟩ (Even.add_one hnEven)
  have hgapFormula : a.orderGap ⟨n, by omega⟩ =
      a.order ⟨n + 1, by omega⟩ := by
    unfold orderGap
    rw [show (⟨n, by omega⟩ : Fin m).succ =
        (⟨n + 1, by omega⟩ : Fin (m + 1)) by ext; rfl]
    rw [show (⟨n, by omega⟩ : Fin m).castSucc =
        (⟨n, by omega⟩ : Fin (m + 1)) by ext; rfl]
    rw [hprevious, sub_zero]
  let C := a.heHu2022Proposition26 ⟨n, by omega⟩
  have hconsequence := (C.alphaOne halpha).2.2
  have hgapNe : a.orderGap ⟨n, by omega⟩ ≠
      2 - 2 * (ramificationIndex K : Int) := by
    simpa only [hgapFormula] using horderNe
  simpa only [hgapFormula] using hconsequence hgapNe

/-- Under `I1^E(n)`, the zero-alpha alternative in `I2^E(n)` forces
`R_{n+2}=-2e`. -/
theorem boundaryOrder_eq_neg_two_e_of_i1E_alpha_zero
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (hm : n + 1 ≤ m) (hnEven : Even n)
    (hI1 : a.HeHuI1E n hm)
    (halpha : a.alphaValue ⟨n, by omega⟩ = 0) :
    a.order ⟨n + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) := by
  have hprevious : a.order ⟨n, by omega⟩ = 0 :=
    hI1.oddOrder ⟨n, by omega⟩ (Even.add_one hnEven)
  have hgap :=
    ((a.heHu2022Proposition26 ⟨n, by omega⟩).alphaZero).1 halpha
  unfold orderGap at hgap
  rw [show (⟨n, by omega⟩ : Fin m).succ =
      (⟨n + 1, by omega⟩ : Fin (m + 1)) by ext; rfl] at hgap
  rw [show (⟨n, by omega⟩ : Fin m).castSucc =
      (⟨n, by omega⟩ : Fin (m + 1)) by ext; rfl] at hgap
  rw [hprevious, sub_zero] at hgap
  exact hgap

/-- At the exceptional order `R_{n+2}=2-2e` and the adjacent gap
`R_{n+3}-R_{n+2}=2e`, the two alpha caps are both `2e`.  Consequently the
bracketed defect in `I2^E(n)` equals `2e-1` exactly when the raw field defect
does.  This is the exceptional equivalence in the proof of Theorem 4.7. -/
theorem cappedBoundary_eq_iff_rawBoundary_eq_of_exceptional_gaps
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (hmStable : n + 2 ≤ m) (hnTwo : 2 ≤ n) (hnEven : Even n)
    (hI1 : a.HeHuI1E n (by omega))
    (hnextGap : a.order ⟨n + 2, by omega⟩ -
        a.order ⟨n + 1, by omega⟩ =
      2 * (ramificationIndex K : Int)) :
    a.heHuAdjacentCappedDefect ⟨n, by omega⟩ =
        (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) ↔
      a.adjacentDefect ⟨n, by omega⟩ =
        (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) := by
  let previous : Fin m := ⟨n - 1, by omega⟩
  let boundary : Fin m := ⟨n, by omega⟩
  let next : Fin m := ⟨n + 1, by omega⟩
  have hpreviousOrder : a.order ⟨n - 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) :=
    hI1.evenOrder ⟨n - 1, by omega⟩ (by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnEven)
  have hmiddleOrder : a.order ⟨n, by omega⟩ = 0 :=
    hI1.oddOrder ⟨n, by omega⟩ (Even.add_one hnEven)
  have hpreviousGap : a.orderGap previous =
      2 * (ramificationIndex K : Int) := by
    unfold orderGap
    rw [show previous.succ = (⟨n, by omega⟩ : Fin (m + 1)) by
      ext
      simp only [previous, Fin.val_succ]
      omega]
    rw [show previous.castSucc = (⟨n - 1, by omega⟩ : Fin (m + 1)) by
      ext
      rfl]
    rw [hmiddleOrder, hpreviousOrder]
    omega
  have hnextGap' : a.orderGap next =
      2 * (ramificationIndex K : Int) := by
    unfold orderGap
    rw [show next.succ = (⟨n + 2, by omega⟩ : Fin (m + 1)) by
      ext
      rfl]
    rw [show next.castSucc = (⟨n + 1, by omega⟩ : Fin (m + 1)) by
      ext
      rfl]
    exact hnextGap
  have hpreviousAlpha : a.alphaValue previous =
      2 * (ramificationIndex K : ℚ) :=
    ((a.heHu2022Proposition26 previous).compareTwoE.2.1).2 hpreviousGap
  have hnextAlpha : a.alphaValue next =
      2 * (ramificationIndex K : ℚ) :=
    ((a.heHu2022Proposition26 next).compareTwoE.2.1).2 hnextGap'
  have hleftCap : a.prefixAlphaCap n =
      ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
    rw [show (⟨n - 1, by omega⟩ : Fin m) = previous by
      ext
      rfl]
    rw [hpreviousAlpha]
  have hrightCap : a.prefixAlphaCap (n + 2) =
      ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
    rw [show (⟨n + 2 - 1, by omega⟩ : Fin m) = next by
      ext
      dsimp only [next]
      omega]
    rw [hnextAlpha]
  have hraw : defectOrder (K := K)
      ((-1) * a.prefixProduct boundary.val *
        a.prefixProduct (boundary.val + 2)) =
      a.adjacentDefect boundary :=
    a.defectOrder_prefixPair_eq_adjacentDefect boundary
  have hraw' : defectOrder (K := K)
      ((-1) * a.prefixProduct n * a.prefixProduct (n + 2)) =
      a.adjacentDefect ⟨n, by omega⟩ := by
    simpa only [boundary] using hraw
  have hePosQ : (0 : ℚ) < (ramificationIndex K : ℚ) := by
    exact_mod_cast ramificationIndex_pos (K := K)
  have hthresholdLt :
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) <
        ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    exact_mod_cast (show
      (2 * (ramificationIndex K : ℚ) - 1 : ℚ) <
        2 * (ramificationIndex K : ℚ) by linarith)
  change
    min
        (defectOrder (K := K)
          ((-1) * a.prefixProduct n * a.prefixProduct (n + 2)))
        (min (a.prefixAlphaCap n) (a.prefixAlphaCap (n + 2))) =
          (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) ↔
      a.adjacentDefect ⟨n, by omega⟩ =
        (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)
  rw [hraw', hleftCap, hrightCap, min_self]
  change
    min (a.adjacentDefect boundary)
        ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) =
          (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) ↔
      a.adjacentDefect boundary =
        (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)
  constructor
  · intro hmin
    by_cases hle : a.adjacentDefect boundary ≤
        ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)
    · simpa only [min_eq_left hle] using hmin
    · have hreverse :
          ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤
            a.adjacentDefect boundary := le_of_not_ge hle
      rw [min_eq_right hreverse] at hmin
      exfalso
      exact (ne_of_gt hthresholdLt) hmin
  · intro hrawEq
    rw [hrawEq, min_eq_left (le_of_lt hthresholdLt)]

/-- Conditions (iii)(1) and (iii)(3) of He--Hu, Theorem 4.7.  The remaining
large-gap clause (iii)(2) is exactly `I3^E(n)` and is kept separate. -/
def HeHuTheorem47BoundaryCondition {m : Nat}
    (a : GoodBONG q L (m + 1)) (n : Nat) (hmStable : n + 2 ≤ m) : Prop :=
  a.alphaValue ⟨n, by omega⟩ ≤ 1 ∧
    (a.order ⟨n + 2, by omega⟩ - a.order ⟨n + 1, by omega⟩ =
          2 * (ramificationIndex K : Int) ∧
        a.order ⟨n + 1, by omega⟩ =
          2 - 2 * (ramificationIndex K : Int) →
      a.adjacentDefect ⟨n, by omega⟩ =
        (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ))

/-- The arithmetic core of Theorem 4.7: assuming `I1^E(n)` and `I3^E(n)`,
condition `I2^E(n)` is equivalent to the concise alpha bound plus the one
raw-defect exception displayed in Theorem 4.7(iii)(3). -/
theorem heHuI2E_iff_theorem47BoundaryCondition
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (hmStable : n + 2 ≤ m) (hnTwo : 2 ≤ n) (hnEven : Even n)
    (hI1 : a.HeHuI1E n (by omega))
    (hI3 : a.HeHuI3E n (by omega)) :
    a.HeHuI2E n (by omega) ↔
      a.HeHuTheorem47BoundaryCondition n hmStable := by
  let boundary : Fin m := ⟨n, by omega⟩
  let next : Fin m := ⟨n + 1, by omega⟩
  have hmiddleOrder : a.order ⟨n, by omega⟩ = 0 :=
    hI1.oddOrder ⟨n, by omega⟩ (Even.add_one hnEven)
  have hboundaryGap : a.orderGap boundary =
      a.order ⟨n + 1, by omega⟩ := by
    unfold orderGap
    rw [show boundary.succ = (⟨n + 1, by omega⟩ : Fin (m + 1)) by
      ext
      rfl]
    rw [show boundary.castSucc = (⟨n, by omega⟩ : Fin (m + 1)) by
      ext
      rfl]
    rw [hmiddleOrder, sub_zero]
  have hthresholdIdentity :
      (1 : ℚ) - ((2 - 2 * (ramificationIndex K : Int) : Int) : ℚ) =
        2 * (ramificationIndex K : ℚ) - 1 := by
    push_cast
    ring
  constructor
  · intro hI2
    refine ⟨hI2.alphaBoundary_le_one, ?_⟩
    rintro ⟨hnextGap, hboundaryOrder⟩
    unfold HeHuI2E at hI2
    dsimp only at hI2
    rcases hI2 with halphaZero | ⟨halphaOne, hcapped⟩
    · have hneg := a.boundaryOrder_eq_neg_two_e_of_i1E_alpha_zero
        (by omega) hnEven hI1 halphaZero
      omega
    · have hcappedThreshold :
          a.heHuAdjacentCappedDefect ⟨n, by omega⟩ =
            (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) := by
        rw [hcapped, hboundaryOrder, hthresholdIdentity]
      exact
        (a.cappedBoundary_eq_iff_rawBoundary_eq_of_exceptional_gaps
          hmStable hnTwo hnEven hI1 hnextGap).mp hcappedThreshold
  · rintro ⟨halphaLe, hrawCondition⟩
    apply (a.heHuI2E_iff_alpha_le_one_and_capped_boundary (by omega)).2
    refine ⟨halphaLe, ?_⟩
    intro halphaOne
    by_cases hboundaryExceptional :
        a.order ⟨n + 1, by omega⟩ =
          2 - 2 * (ramificationIndex K : Int)
    · have hnextGapLe :
          a.order ⟨n + 2, by omega⟩ -
              a.order ⟨n + 1, by omega⟩ ≤
            2 * (ramificationIndex K : Int) := by
        by_contra hnot
        have hlarge : 2 * (ramificationIndex K : Int) <
            a.order ⟨n + 2, by omega⟩ -
              a.order ⟨n + 1, by omega⟩ := lt_of_not_ge hnot
        have hforced := (hI3 hmStable hlarge).1
        omega
      by_cases hnextGapEq :
          a.order ⟨n + 2, by omega⟩ -
              a.order ⟨n + 1, by omega⟩ =
            2 * (ramificationIndex K : Int)
      · have hraw := hrawCondition ⟨hnextGapEq, hboundaryExceptional⟩
        have hcappedThreshold :=
          (a.cappedBoundary_eq_iff_rawBoundary_eq_of_exceptional_gaps
            hmStable hnTwo hnEven hI1 hnextGapEq).mpr hraw
        rw [hcappedThreshold, hboundaryExceptional, hthresholdIdentity]
      · have hnextGapLt :
            a.order ⟨n + 2, by omega⟩ -
                a.order ⟨n + 1, by omega⟩ <
              2 * (ramificationIndex K : Int) := by
          omega
        have hnextGapValue : a.orderGap next =
            a.order ⟨n + 2, by omega⟩ -
              a.order ⟨n + 1, by omega⟩ := by
          unfold orderGap
          rw [show next.succ = (⟨n + 2, by omega⟩ : Fin (m + 1)) by
            ext
            rfl]
          rw [show next.castSucc =
              (⟨n + 1, by omega⟩ : Fin (m + 1)) by
            ext
            rfl]
        have hnextAlphaLt : a.alphaValue next <
            2 * (ramificationIndex K : ℚ) :=
          ((a.heHu2022Proposition26 next).compareTwoE.1).2 (by
            rw [hnextGapValue]
            exact hnextGapLt)
        have hnextAlphaInteger : IsRationalInteger (a.alphaValue next) := by
          rcases (a.heHu2022Proposition26 next).arithmeticShape with
            hinteger | hlarge
          · exact hinteger.2.2
          · exact False.elim ((not_lt_of_ge (le_of_lt hlarge.1)) hnextAlphaLt)
        have hnextAlphaLe : a.alphaValue next ≤
            2 * (ramificationIndex K : ℚ) - 1 := by
          rcases hnextAlphaInteger with ⟨z, hz⟩
          have hzlt : z < 2 * (ramificationIndex K : Int) := by
            exact_mod_cast (show (z : ℚ) <
              2 * (ramificationIndex K : ℚ) by
                simpa only [← hz] using hnextAlphaLt)
          have hzle : z ≤ 2 * (ramificationIndex K : Int) - 1 := by
            omega
          rw [hz]
          exact_mod_cast hzle
        have hrightCap : a.prefixAlphaCap (n + 2) =
            (a.alphaValue next : WithTop ℚ) := by
          rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
          congr 2
        have hupper : a.heHuAdjacentCappedDefect boundary ≤
            (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) := by
          have hcap := a.truncatedPrefixDefect_le_rightCap
            a (-1) boundary.val (boundary.val + 2)
          rw [show boundary.val = n by rfl,
            show boundary.val + 2 = n + 2 by rfl, hrightCap] at hcap
          exact hcap.trans (by exact_mod_cast hnextAlphaLe)
        have hlower :
            (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) ≤
              a.heHuAdjacentCappedDefect boundary := by
          have hlocal :=
            ((a.heHu2022Proposition26 boundary).alphaOne halphaOne).2.1
          rw [hboundaryGap, hboundaryExceptional] at hlocal
          have hrat :
              (2 * (ramificationIndex K : ℚ) - 1 : ℚ) =
                1 - ((2 - 2 * (ramificationIndex K : Int) : Int) : ℚ) := by
            push_cast
            ring
          rw [← hrat] at hlocal
          exact hlocal
        have hcappedThreshold : a.heHuAdjacentCappedDefect boundary =
            (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) :=
          le_antisymm hupper hlower
        rw [hcappedThreshold, hboundaryExceptional, hthresholdIdentity]
    · exact a.cappedBoundary_eq_of_i1E_alpha_one_of_order_ne
        (by omega) hnEven hI1 halphaOne hboundaryExceptional

/-- The stable-rank right-hand side of He--Hu, Theorem 4.7(i),(iii), before
the ambient-space rank classification is inserted. -/
structure HeHuTheorem47StableConditions {m : Nat}
    (a : GoodBONG q L (m + 1)) (n : Nat) (hmStable : n + 2 ≤ m) : Prop where
  initial : a.HeHuI1E n (by omega)
  boundary : a.HeHuTheorem47BoundaryCondition n hmStable
  largeGap : a.HeHuI3E n (by omega)

/-- The three conditions of Theorem 4.1 are equivalent, in stable even rank,
to the concise invariant conditions of Theorem 4.7. -/
theorem heHuEvenSectionConditions_iff_theorem47StableConditions
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (hmStable : n + 2 ≤ m) (hnTwo : 2 ≤ n) (hnEven : Even n) :
    a.HeHuEvenSectionConditions n (by omega) ↔
      a.HeHuTheorem47StableConditions n hmStable := by
  constructor
  · intro h
    exact
      { initial := h.i1
        boundary :=
          (a.heHuI2E_iff_theorem47BoundaryCondition
            hmStable hnTwo hnEven h.i1 h.i3).mp h.i2
        largeGap := h.i3 }
  · intro h
    exact
      { i1 := h.initial
        i2 :=
          (a.heHuI2E_iff_theorem47BoundaryCondition
            hmStable hnTwo hnEven h.initial h.largeGap).mpr h.boundary
        i3 := h.largeGap }

/-- Logical assembly of He--Hu, Theorem 4.1 from the three component
equivalences proved in Lemmas 4.2, 4.4, and 4.5.  Keeping this assembly
separate ensures those source lemmas remain visible proof obligations rather
than being hidden inside the main theorem.  The Lean parameter `n` denotes
the predecessor of the paper's target rank `n+1`. -/
theorem heHuTheorem41_of_component_equivalences {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hRank : n ≤ m)
    (hmSection : n + 2 ≤ m)
    (h42 : Lattice.AmbientlyNUniversal.{u, v, w} q (n + 1) →
      (HeHuAllOrderAndDefectConditions.{u, v, w} a hRank ↔
        a.HeHuI1E (n + 1) hmSection))
    (h44 : Lattice.AmbientlyNUniversal.{u, v, w} q (n + 1) →
      a.HeHuI1E (n + 1) hmSection →
      (HeHuAllCentralRepresentationConditions.{u, v, w} (n := n) a ↔
        a.HeHuI2E (n + 1) hmSection))
    (h45 : Lattice.AmbientlyNUniversal.{u, v, w} q (n + 1) →
      a.HeHuI1E (n + 1) hmSection →
      a.HeHuI2E (n + 1) hmSection →
      (HeHuAllLongRepresentationConditions.{u, v, w} (n := n) a ↔
        a.HeHuI3E (n + 1) hmSection)) :
    Lattice.IsNUniversal.{u, v, w} q L (n + 1) ↔
      Lattice.IsIntegral q L ∧
        Lattice.AmbientlyNUniversal.{u, v, w} q (n + 1) ∧
          a.HeHuEvenSectionConditions (n + 1) hmSection := by
  rw [a.heHuNUniversality_factorization hRank]
  constructor
  · rintro ⟨hIntegral, hAmbient, hAll⟩
    have hparts :=
      (a.heHuAllRepresentationConditions_iff_components hRank).mp hAll
    have hI1 := (h42 hAmbient).mp hparts.1
    have hI2 := (h44 hAmbient hI1).mp hparts.2.1
    have hI3 := (h45 hAmbient hI1 hI2).mp hparts.2.2
    exact ⟨hIntegral, hAmbient, ⟨hI1, hI2, hI3⟩⟩
  · rintro ⟨hIntegral, hAmbient, hSection⟩
    refine ⟨hIntegral, hAmbient, ?_⟩
    apply (a.heHuAllRepresentationConditions_iff_components hRank).mpr
    exact
      ⟨(h42 hAmbient).mpr hSection.i1,
        (h44 hAmbient hSection.i1).mpr hSection.i2,
        (h45 hAmbient hSection.i1 hSection.i2).mpr hSection.i3⟩

/-- The large-last-gap conclusion of `I3^E(n)`, in the exact conjunctive
form used in the proof of Theorem 4.1. -/
theorem HeHuI3E.largeGap {m n : Nat} {a : GoodBONG q L (m + 1)}
    {hm : n + 1 ≤ m} (h : a.HeHuI3E n hm)
    (hmStable : n + 2 ≤ m)
    (hgap : 2 * (ramificationIndex K : Int) <
      a.order ⟨n + 2, by omega⟩ - a.order ⟨n + 1, by omega⟩) :
    a.order ⟨n + 1, by omega⟩ =
        -(2 * (ramificationIndex K : Int)) ∧
      ((4 ≤ n ∨
          (n = 2 ∧ a.heHuPrefixDefect 4 =
            (((2 * (ramificationIndex K : Int) : Int) : ℚ) : WithTop ℚ))) →
        a.order ⟨n + 2, by omega⟩ = 1) :=
  h hmStable hgap

end BONG.GoodBONG

end Bong
