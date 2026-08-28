/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009FundamentalTypeBridge

/-!
# Transport of Jordan fundamental weights from Beli invariants

This file proves the forward half of Beli (2009), Lemma 2.16 and
Corollary 2.17 needed in the classification theorem: on synchronously
aligned strict Jordan decompositions, equality of all BONG orders and alpha
invariants forces equality of every fundamental weight order.
-/

namespace Bong

open Dyadic

namespace BONG.StrictJordanAdaptedAlignment

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {a : GoodBONG q L (n + 2)} {b : GoodBONG r M (n + 2)}

/-- Swapping an aligned Jordan family does not change the numerical start
of a component. -/
@[simp] theorem symm_componentStart
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) :
    S.symm.componentStart k = S.componentStart k := by
  unfold componentStart
  apply Finset.sum_congr rfl
  intro i hi
  exact (S.componentRank_eq i).symm

/-- Swapping an aligned Jordan family does not change the numerical end of
a component. -/
@[simp] theorem symm_componentStop
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) :
    S.symm.componentStop k = S.componentStop k := by
  unfold componentStop
  rw [S.symm_componentStart]
  exact congrArg (S.componentStart k + ·) (S.componentRank_eq k).symm

/-- The first fundamental weight is determined by `R₁` and `α₁`. -/
theorem fundamentalWeightOrder_eq_first
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (horders : a.SameOrders b) (halphas : a.SameAlphas b) :
    S.sourceJordan.fundamentalWeightOrder S.sourceFirstComponent =
      S.targetJordan.fundamentalWeightOrder S.sourceFirstComponent := by
  unfold sourceFirstComponent
  rw [S.sourceJordan.fundamentalWeightOrder_zero S.componentCount_pos,
    S.targetJordan.fundamentalWeightOrder_zero S.componentCount_pos]
  have ha := a.lemma214_weightIdealOrder_all
  have hb := b.lemma214_weightIdealOrder_all
  have hq : (Lattice.weightIdealOrder q L : ℚ) =
      (Lattice.weightIdealOrder r M : ℚ) := by
    calc
      (Lattice.weightIdealOrder q L : ℚ) =
          min ((a.order 0 : ℚ) + a.alphaValue 0)
            ((a.order 0 : ℚ) + (ramificationIndex K : ℚ)) := ha
      _ = min ((b.order 0 : ℚ) + b.alphaValue 0)
            ((b.order 0 : ℚ) + (ramificationIndex K : ℚ)) := by
          rw [horders 0, halphas 0]
      _ = (Lattice.weightIdealOrder r M : ℚ) := hb.symm
  exact_mod_cast hq

/-- Equality of `R_i` and `α_i` determines all fundamental weights in the
aligned strict Jordan family.  This is the forward weight implication used
at the start of Beli's proof of Theorem 3.1. -/
theorem fundamentalWeightOrder_eq_of_sameOrders_sameAlphas
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (horders : a.SameOrders b) (halphas : a.SameAlphas b)
    (k : Fin S.componentCount) :
    S.sourceJordan.fundamentalWeightOrder k =
      S.targetJordan.fundamentalWeightOrder k := by
  change Lattice.weightIdealOrder q (S.sourceJordan.fundamentalLattice k) =
    Lattice.weightIdealOrder r (S.targetJordan.fundamentalLattice k)
  by_cases hkzero : k.val = 0
  · have hk : k = S.sourceFirstComponent := by
      apply Fin.ext
      exact hkzero
    subst k
    exact S.fundamentalWeightOrder_eq_first horders halphas
  · have hk : 0 < k.val := Nat.pos_of_ne_zero hkzero
    rcases S.source_hasTwoBlockSplit_componentStart k hk with ⟨Ts⟩
    rcases S.symm.source_hasTwoBlockSplit_componentStart k hk with ⟨Tt⟩
    by_cases hrank : S.sourceJordan.componentRank k = 1
    · have hrankTarget : S.symm.sourceJordan.componentRank k = 1 :=
        (S.componentRank_eq k).symm.trans hrank
      by_cases hright : S.componentStart k < n + 1
      · have hs :=
          S.sourceFundamentalWeightOrder_eq_order_add_min_neighborAlphas_e_of_unary
            k hk Ts hrank hright
        have ht :=
          S.symm.sourceFundamentalWeightOrder_eq_order_add_min_neighborAlphas_e_of_unary
            k hk Tt hrankTarget (by simpa using hright)
        dsimp only at hs ht
        simp only [S.symm_componentStart] at ht
        have hq :
            (Lattice.weightIdealOrder q
              (S.sourceJordan.fundamentalLattice k) : ℚ) =
            (Lattice.weightIdealOrder r
              (S.targetJordan.fundamentalLattice k) : ℚ) := by
          calc
            (Lattice.weightIdealOrder q
                (S.sourceJordan.fundamentalLattice k) : ℚ) =
                (a.order (⟨S.componentStart k, hright⟩ :
                  Fin (n + 1)).castSucc : ℚ) +
                  min (a.alphaValue ⟨S.componentStart k - 1, by omega⟩)
                    (min (a.alphaValue ⟨S.componentStart k, hright⟩)
                      (ramificationIndex K : ℚ)) := hs
            _ = (b.order (⟨S.componentStart k, hright⟩ :
                  Fin (n + 1)).castSucc : ℚ) +
                  min (b.alphaValue ⟨S.componentStart k - 1, by omega⟩)
                    (min (b.alphaValue ⟨S.componentStart k, hright⟩)
                      (ramificationIndex K : ℚ)) := by
                rw [horders, halphas, halphas]
            _ = (Lattice.weightIdealOrder r
                (S.targetJordan.fundamentalLattice k) : ℚ) := by
                change _ = (Lattice.weightIdealOrder r
                  (S.symm.sourceJordan.fundamentalLattice k) : ℚ)
                exact ht.symm
        exact_mod_cast hq
      · have hterminal : n + 2 - S.componentStart k = 1 := by
          have hbound := (S.componentStart_lt_componentStop k).trans_le
            (S.componentStop_le k)
          omega
        have hs :=
          S.sourceFundamentalWeightOrder_eq_order_add_min_alpha_e_of_unary_terminal
            k hk Ts hrank hterminal
        have ht :=
          S.symm.sourceFundamentalWeightOrder_eq_order_add_min_alpha_e_of_unary_terminal
            k hk Tt hrankTarget (by simpa using hterminal)
        dsimp only at hs ht
        simp only [S.symm_componentStart] at ht
        have hstartLt : S.componentStart k < n + 2 := by
          have hstart := S.componentStart_lt_componentStop k
          have hstop := S.componentStop_le k
          exact hstart.trans_le hstop
        have hq :
            (Lattice.weightIdealOrder q
              (S.sourceJordan.fundamentalLattice k) : ℚ) =
            (Lattice.weightIdealOrder r
              (S.targetJordan.fundamentalLattice k) : ℚ) := by
          calc
            (Lattice.weightIdealOrder q
                (S.sourceJordan.fundamentalLattice k) : ℚ) =
                (a.order ⟨S.componentStart k, hstartLt⟩ : ℚ) +
                  min (a.alphaValue ⟨S.componentStart k - 1, by omega⟩)
                    (ramificationIndex K : ℚ) := hs
            _ = (b.order ⟨S.componentStart k, hstartLt⟩ : ℚ) +
                  min (b.alphaValue ⟨S.componentStart k - 1, by omega⟩)
                    (ramificationIndex K : ℚ) := by
                rw [horders, halphas]
            _ = (Lattice.weightIdealOrder r
                (S.targetJordan.fundamentalLattice k) : ℚ) := by
                change _ = (Lattice.weightIdealOrder r
                  (S.symm.sourceJordan.fundamentalLattice k) : ℚ)
                exact ht.symm
        exact_mod_cast hq
    · have hrankTwo : 2 ≤ S.sourceJordan.componentRank k := by
        have hpos := S.sourceJordan.component_finrank_pos k
        change 0 < S.sourceJordan.componentRank k at hpos
        omega
      have hrankTarget : 2 ≤ S.symm.sourceJordan.componentRank k := by
        change 2 ≤ S.targetJordan.componentRank k
        have heq : S.sourceJordan.componentRank k =
            S.targetJordan.componentRank k := S.componentRank_eq k
        omega
      have hs :=
        S.sourceFundamentalWeightOrder_eq_order_add_alpha_componentStart
          k hk Ts hrankTwo
      have ht :=
        S.symm.sourceFundamentalWeightOrder_eq_order_add_alpha_componentStart
          k hk Tt hrankTarget
      dsimp only at hs ht
      simp only [S.symm_componentStart] at ht
      have hstartLt : S.componentStart k < n + 1 := by
        have hstop := S.componentStop_le k
        change S.componentStart k + S.sourceJordan.componentRank k ≤
          n + 1 + 1 at hstop
        omega
      have hq :
          (Lattice.weightIdealOrder q
            (S.sourceJordan.fundamentalLattice k) : ℚ) =
          (Lattice.weightIdealOrder r
            (S.targetJordan.fundamentalLattice k) : ℚ) := by
        calc
          (Lattice.weightIdealOrder q
              (S.sourceJordan.fundamentalLattice k) : ℚ) =
              (a.order (⟨S.componentStart k, hstartLt⟩ :
                Fin (n + 1)).castSucc : ℚ) +
                a.alphaValue ⟨S.componentStart k, hstartLt⟩ := hs
          _ = (b.order (⟨S.componentStart k, hstartLt⟩ :
                Fin (n + 1)).castSucc : ℚ) +
                b.alphaValue ⟨S.componentStart k, hstartLt⟩ := by
              rw [horders, halphas]
          _ = (Lattice.weightIdealOrder r
              (S.targetJordan.fundamentalLattice k) : ℚ) := by
              change _ = (Lattice.weightIdealOrder r
                (S.symm.sourceJordan.fundamentalLattice k) : ℚ)
              exact ht.symm
      exact_mod_cast hq

end BONG.StrictJordanAdaptedAlignment

end Bong
