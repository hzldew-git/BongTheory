/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma75
import Bong.Bong.He2022ClassicLemma314

/-!
# He (2024), Lemma 7.8

This file verifies the four pointwise conditions of Theorem 2.5 for the
auxiliary `P` rows used in the even-rank classification.  The first theorem
isolates the uniform all-zero-order, all-one-alpha calculation.  The next two
theorems are the two central-condition assertions printed in Lemma 7.8.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

namespace BONG.GoodBONG

/-- Lemma 7.8(i), in the profile-general form used by both `P` rows.
For an even target of rank `2r+2`, an all-zero source of rank `2r+4` with
all alpha invariants one satisfies conditions (i), (ii), and (iv) of
Theorem 2.5. -/
theorem he2022ClassicLemma78i_of_zero_one_profile
    (pairs : Nat) (a : GoodBONG q L (2 * pairs + 4))
    (b : GoodBONG r M (2 * pairs + 2))
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (heOne : ramificationIndex K = 1)
    (hzero : forall k : Fin (2 * pairs + 4), a.order k = 0)
    (halpha : forall k : Fin (2 * pairs + 3), a.alphaValue k = 1) :
    (forall i : Fin (2 * pairs + 2),
      a.HeClassicOrderConditionAt b (by omega) i) ∧
    (forall i : RepresentationIndex (2 * pairs + 4) (2 * pairs + 2),
      a.HeClassicDefectConditionAt b i) ∧
    (forall i : LongRepresentationIndex (2 * pairs + 4) (2 * pairs + 2),
      a.HeClassicLongConditionAt b i) := by
  constructor
  · intro i
    exact a.he2022ClassicCorollary310i (m := 2 * pairs + 2) pairs b
      (by omega) (by omega) hBClassic
      (by intro k _; exact hzero k) (Or.inl (hzero _)) i
  constructor
  · intro i
    exact a.he2022ClassicCorollary311ii (m := 2 * pairs + 1) pairs b
      (by omega) hAClassic hBClassic
      (by intro k _; exact hzero k)
      (by intro k _; exact halpha k)
      (hzero _) (halpha _) (Or.inl heOne) i
  · intro i
    apply a.he2022ClassicCorollary313ii (2 * pairs) b
      (by intro k _; exact hzero k) (Or.inl (hzero _))
    · rw [hzero _, hzero _]
      have hePos := ramificationIndex_pos (K := K)
      omega
    · have := i.succ_lt_large
      omega

/-- Lemma 7.8(iii): the published central condition holds through paper
index `n` for any classic integral target. -/
theorem he2022ClassicLemma78iii_of_zero_profile
    (pairs : Nat) (a : GoodBONG q L (2 * pairs + 4))
    (b : GoodBONG r M (2 * pairs + 2))
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hzero : forall k : Fin (2 * pairs + 4), a.order k = 0)
    (i : CentralRepresentationIndex (2 * pairs + 4) (2 * pairs + 2))
    (hiRange : i.val <= 2 * pairs + 2) :
    a.HeClassicPublishedCentralConditionAt b i := by
  exact a.he2022ClassicCorollary312iiInitial (m := 2 * pairs + 1)
    pairs b (by omega) hBClassic
    (by intro k _; exact hzero k) (hzero _) i hiRange

/-- Lemma 7.8(ii), abstract form.  If every source order is zero and every
target order is nonnegative, the first inequality in the central trigger is
impossible, so the implication is vacuous at every index, including the
terminal one. -/
theorem he2022ClassicLemma78ii_of_nonnegative_target
    (pairs : Nat) (a : GoodBONG q L (2 * pairs + 4))
    (b : GoodBONG r M (2 * pairs + 2))
    (hzero : forall k : Fin (2 * pairs + 4), a.order k = 0)
    (hnonnegative : forall k : Fin (2 * pairs + 2), 0 <= b.order k)
    (i : CentralRepresentationIndex (2 * pairs + 4) (2 * pairs + 2)) :
    a.HeClassicPublishedCentralConditionAt b i := by
  intro htrigger
  exfalso
  have hlt := htrigger.1
  rw [hzero _] at hlt
  exact (not_lt_of_ge (hnonnegative _)) hlt

end BONG.GoodBONG

/-! ## Literal `P(omega)` specializations -/

/-- The exact good BONG on the first published `P(omega)` row. -/
noncomputable def heClassicEvenP1OmegaGoodBONG (pairs : Nat) :=
  heClassicEvenP1GoodBONG (K := K) pairs (heClassicOmega (K := K))
    (heClassicOmega_order (K := K))

/-- The exact good BONG on the second published `P(omega)` row. -/
noncomputable def heClassicEvenP2OmegaGoodBONG (pairs : Nat) :=
  heClassicEvenP2GoodBONG (K := K) pairs
    (heClassicOmega (K := K)) (heClassicOmegaSharp (K := K))
    (heClassicOmega_order (K := K)) (by
      rw [heClassicOmegaSharp_order (K := K)])

theorem heClassicEvenP1OmegaGoodBONG_order_zero
    (pairs : Nat) (i : Fin (2 * pairs + 4)) :
    (heClassicEvenP1OmegaGoodBONG (K := K) pairs).order i = 0 := by
  simp only [heClassicEvenP1OmegaGoodBONG, heClassicEvenP1GoodBONG,
    heHuExactGoodBONG_order]
  exact heClassicEvenP1_order_zero pairs _
    (heClassicOmega_order (K := K)) i

theorem heClassicEvenP2OmegaGoodBONG_order_zero
    (pairs : Nat) (i : Fin (2 * pairs + 4)) :
    (heClassicEvenP2OmegaGoodBONG (K := K) pairs).order i = 0 := by
  simp only [heClassicEvenP2OmegaGoodBONG, heClassicEvenP2GoodBONG,
    heHuExactGoodBONG_order]
  exact heClassicEvenP2_order_zero pairs _ _
    (heClassicOmega_order (K := K))
    (heClassicOmegaSharp_order (K := K)) i

theorem heClassicEvenP1OmegaGoodBONG_alpha_eq_one
    (pairs : Nat) (i : Fin (2 * pairs + 3)) :
    (heClassicEvenP1OmegaGoodBONG (K := K) pairs).alphaValue i = 1 := by
  exact heClassicEvenP1_alpha_eq_one pairs _
    (heClassicOmega_order (K := K))
    (heClassicOmega_defect (K := K)) i

theorem heClassicEvenP2OmegaGoodBONG_alpha_eq_one
    (pairs : Nat) (i : Fin (2 * pairs + 3)) :
    (heClassicEvenP2OmegaGoodBONG (K := K) pairs).alphaValue i = 1 := by
  exact heClassicEvenP2_alpha_eq_one pairs _ _
    (heClassicOmega_order (K := K))
    (heClassicOmegaSharp_order (K := K))
    (heClassicOmega_defect (K := K)) i

/-- Lemma 7.8(i) for the first literal auxiliary row. -/
theorem he2022ClassicLemma78i_P1Omega
    (pairs : Nat) (b : BONG.GoodBONG r M (2 * pairs + 2))
    (hBClassic : Lattice.IsClassicIntegral r M)
    (heOne : ramificationIndex K = 1) :
    let a := heClassicEvenP1OmegaGoodBONG (K := K) pairs
    (forall i : Fin (2 * pairs + 2),
      a.HeClassicOrderConditionAt b (by omega) i) ∧
    (forall i : RepresentationIndex (2 * pairs + 4) (2 * pairs + 2),
      a.HeClassicDefectConditionAt b i) ∧
    (forall i : LongRepresentationIndex (2 * pairs + 4) (2 * pairs + 2),
      a.HeClassicLongConditionAt b i) := by
  dsimp only
  apply BONG.GoodBONG.he2022ClassicLemma78i_of_zero_one_profile
    pairs (heClassicEvenP1OmegaGoodBONG (K := K) pairs) b
      (by
        simpa only [heClassicEvenP1OmegaGoodBONG] using
          heClassicEvenP1_isClassicIntegral (K := K) pairs _
            (heClassicOmega_order (K := K))) hBClassic heOne
  · exact heClassicEvenP1OmegaGoodBONG_order_zero pairs
  · exact heClassicEvenP1OmegaGoodBONG_alpha_eq_one pairs

/-- Lemma 7.8(i) for the second literal auxiliary row. -/
theorem he2022ClassicLemma78i_P2Omega
    (pairs : Nat) (b : BONG.GoodBONG r M (2 * pairs + 2))
    (hBClassic : Lattice.IsClassicIntegral r M)
    (heOne : ramificationIndex K = 1) :
    let a := heClassicEvenP2OmegaGoodBONG (K := K) pairs
    (forall i : Fin (2 * pairs + 2),
      a.HeClassicOrderConditionAt b (by omega) i) ∧
    (forall i : RepresentationIndex (2 * pairs + 4) (2 * pairs + 2),
      a.HeClassicDefectConditionAt b i) ∧
    (forall i : LongRepresentationIndex (2 * pairs + 4) (2 * pairs + 2),
      a.HeClassicLongConditionAt b i) := by
  dsimp only
  apply BONG.GoodBONG.he2022ClassicLemma78i_of_zero_one_profile
    pairs (heClassicEvenP2OmegaGoodBONG (K := K) pairs) b
      (by
        simpa only [heClassicEvenP2OmegaGoodBONG] using
          heClassicEvenP2_isClassicIntegral (K := K) pairs _ _
            (heClassicOmega_order (K := K)) (by
              rw [heClassicOmegaSharp_order (K := K)])) hBClassic heOne
  · exact heClassicEvenP2OmegaGoodBONG_order_zero pairs
  · exact heClassicEvenP2OmegaGoodBONG_alpha_eq_one pairs

/-- Lemma 7.8(iii) for the first literal auxiliary row. -/
theorem he2022ClassicLemma78iii_P1Omega
    (pairs : Nat) (b : BONG.GoodBONG r M (2 * pairs + 2))
    (hBClassic : Lattice.IsClassicIntegral r M)
    (i : CentralRepresentationIndex (2 * pairs + 4) (2 * pairs + 2))
    (hiRange : i.val <= 2 * pairs + 2) :
    BONG.GoodBONG.HeClassicPublishedCentralConditionAt
      (heClassicEvenP1OmegaGoodBONG (K := K) pairs) b i := by
  exact BONG.GoodBONG.he2022ClassicLemma78iii_of_zero_profile
      pairs (heClassicEvenP1OmegaGoodBONG (K := K) pairs) b hBClassic
      (heClassicEvenP1OmegaGoodBONG_order_zero pairs) i hiRange

/-- Lemma 7.8(iii) for the second literal auxiliary row. -/
theorem he2022ClassicLemma78iii_P2Omega
    (pairs : Nat) (b : BONG.GoodBONG r M (2 * pairs + 2))
    (hBClassic : Lattice.IsClassicIntegral r M)
    (i : CentralRepresentationIndex (2 * pairs + 4) (2 * pairs + 2))
    (hiRange : i.val <= 2 * pairs + 2) :
    BONG.GoodBONG.HeClassicPublishedCentralConditionAt
      (heClassicEvenP2OmegaGoodBONG (K := K) pairs) b i := by
  exact BONG.GoodBONG.he2022ClassicLemma78iii_of_zero_profile
      pairs (heClassicEvenP2OmegaGoodBONG (K := K) pairs) b hBClassic
      (heClassicEvenP2OmegaGoodBONG_order_zero pairs) i hiRange

/-! ## Literal `C`-target specializations -/

/-- Lemma 7.8(ii) for the first published `C` column. -/
theorem he2022ClassicLemma78ii_C1_of_zero_profile
    (pairs : Nat) (a : BONG.GoodBONG q L (2 * pairs + 4))
    (hzero : forall k : Fin (2 * pairs + 4), a.order k = 0)
    (c : Kˣ) (hc : 0 <= ordUnit K c)
    (i : CentralRepresentationIndex (2 * pairs + 4) (2 * pairs + 2)) :
    BONG.GoodBONG.HeClassicPublishedCentralConditionAt a
      (heClassicEvenC1GoodBONG (K := K) pairs c hc) i := by
  apply BONG.GoodBONG.he2022ClassicLemma78ii_of_nonnegative_target
    pairs a (heClassicEvenC1GoodBONG (K := K) pairs c hc) hzero
  intro k
  simp only [heClassicEvenC1GoodBONG, heHuExactGoodBONG_order]
  rw [heClassicEvenC1_order]
  split
  · exact hc
  · exact le_rfl

/-- Lemma 7.8(ii) for the second published `C` column. -/
theorem he2022ClassicLemma78ii_C2_of_zero_profile
    (pairs : Nat) (a : BONG.GoodBONG q L (2 * pairs + 4))
    (hzero : forall k : Fin (2 * pairs + 4), a.order k = 0)
    (c cSharp : Kˣ) (hc : 0 <= ordUnit K c)
    (hcSharp : ordUnit K cSharp = 0)
    (i : CentralRepresentationIndex (2 * pairs + 4) (2 * pairs + 2)) :
    BONG.GoodBONG.HeClassicPublishedCentralConditionAt a
      (heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp) i := by
  apply BONG.GoodBONG.he2022ClassicLemma78ii_of_nonnegative_target
    pairs a (heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp)
      hzero
  intro k
  simp only [heClassicEvenC2GoodBONG, heHuExactGoodBONG_order]
  rw [heClassicEvenC2_order pairs c cSharp hcSharp]
  split
  · exact hc
  · exact le_rfl

end Bong
