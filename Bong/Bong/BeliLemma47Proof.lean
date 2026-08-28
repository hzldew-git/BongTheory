/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma43MaximalNormProof
import Bong.Bong.BeliLemma47ProfileReduction
import Bong.Bong.JordanDecompositionInvariants
import Bong.Bong.JordanProfileMerge
import Bong.Bong.MaximalNormSplittingDual
import Bong.Lattice.RankOneNormScale

/-!
# Proof of Beli (2003), Lemma 4.7

The proof follows Beli's maximal-norm argument.  A good BONG is first
blocked by an adapted maximal-norm splitting.  The norm-gap inequalities
show that the norm of each block is exactly the effective norm at its scale,
so the concatenated BONG has the alternating weak Jordan profile.  Equal
scales are then amalgamated, and the resulting strict profile is transported
to an arbitrary Jordan decomposition using the intrinsic scale ranks and
scale-truncation norms.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace JordanProfileOrder

/-- The norm-gap inequalities of a maximal-norm splitting say precisely
that the component norm is the effective norm at its own scale. -/
theorem effectiveAt_eq_of_maximalNormBounds {t : Nat}
    (scale norm : Fin t → Int) (i : Fin t)
    (hscale : Monotone scale)
    (hgap : ∀ {a b : Fin t}, a < b →
      0 ≤ norm b - norm a ∧
        norm b - norm a ≤ 2 * (scale b - scale a)) :
    effectiveAt scale norm i (scale i) = norm i := by
  apply le_antisymm
  · have h := effectiveAt_le scale norm i i (scale i)
    simpa [adjustedAt] using h
  · apply le_effectiveAt
    intro j
    rcases lt_trichotomy j i with hji | rfl | hij
    · have hs := hscale hji.le
      have hg := hgap hji
      simp only [adjustedAt]
      by_cases hlt : scale j < scale i
      · rw [if_pos hlt]
        omega
      · rw [if_neg hlt]
        have heq : scale j = scale i := le_antisymm hs (le_of_not_gt hlt)
        omega
    · simp [adjustedAt]
    · have hs := hscale hij.le
      have hg := hgap hij
      simp only [adjustedAt]
      rw [if_neg (not_lt_of_ge hs)]
      omega

end JordanProfileOrder

namespace Lattice.MaximalNormSplitting

open Lattice.OrthogonalDecomposition

variable {t : Nat} (M : Lattice.MaximalNormSplitting q L t)
  (c : M.toOrthogonalDecomposition.ComponentBONGFamily)

/-- A maximal-norm splitting, with its unary-component modularity witnessed
by the chosen component BONGs, is a weak Jordan decomposition. -/
noncomputable def toWeakJordan : Lattice.WeakJordanDecomposition q L t where
  toOrthogonalDecomposition := M.toOrthogonalDecomposition
  scaleGenerator := M.scaleGenerator
  modular := M.component_isModular c
  component_finrank_pos := M.componentRank_pos
  scaleOrder_mono := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact M.scaleOrder_mono hlt

@[simp]
theorem toWeakJordan_component (i : Fin t) :
    (M.toWeakJordan c).component i = M.component i :=
  rfl

@[simp]
theorem toWeakJordan_scaleGenerator (i : Fin t) :
    (M.toWeakJordan c).scaleGenerator i = M.scaleGenerator i :=
  rfl

/-- The independently chosen norm generator of the weak Jordan component
has the same order as the norm generator stored in the maximal splitting. -/
theorem toWeakJordan_normGeneratorOrder (i : Fin t) :
    ordUnit K ((M.toWeakJordan c).normGeneratorUnit i) =
      ordUnit K (M.normGenerator i) := by
  apply (principalIdeal_eq_iff_ordUnit_eq _ _).mp
  calc
    principalIdeal (K := K)
        (((M.toWeakJordan c).normGeneratorUnit i : K)) =
        normIdeal ((M.toWeakJordan c).component i).space
          ((M.toWeakJordan c).component i).lattice :=
      ((M.toWeakJordan c).normIdeal_eq_normGeneratorUnit i).symm
    _ = normIdeal (M.component i).space (M.component i).lattice := by
      rw [M.toWeakJordan_component c i]
    _ = principalIdeal (K := K) (M.normGenerator i : K) :=
      M.normIdeal_eq i

/-- At every component scale, the weak effective norm is the corresponding
maximal-splitting norm. -/
theorem toWeakJordan_effectiveNormOrderAt_eq (i : Fin t) :
    (M.toWeakJordan c).effectiveNormOrderAt i
        (ordUnit K (M.scaleGenerator i)) =
      ordUnit K (M.normGenerator i) := by
  let W := M.toWeakJordan c
  have hnorm : W.normOrderFamily =
      fun j ↦ ordUnit K (M.normGenerator j) := by
    funext j
    exact M.toWeakJordan_normGeneratorOrder c j
  change JordanProfileOrder.effectiveAt W.scaleOrderFamily
      W.normOrderFamily i (ordUnit K (M.scaleGenerator i)) = _
  rw [hnorm]
  change JordanProfileOrder.effectiveAt
      (fun j ↦ ordUnit K (M.scaleGenerator j))
      (fun j ↦ ordUnit K (M.normGenerator j)) i
      (ordUnit K (M.scaleGenerator i)) = _
  exact JordanProfileOrder.effectiveAt_eq_of_maximalNormBounds
    (fun j ↦ ordUnit K (M.scaleGenerator j))
    (fun j ↦ ordUnit K (M.normGenerator j)) i
    (M.toWeakJordan c).scaleOrder_mono
    (fun h ↦ M.normGap_bounds h)

/-- The weak Jordan family underlying a maximal-norm splitting satisfies
O'Meara's improper-even-rank invariant. -/
theorem toWeakJordan_hasImproperEvenRank :
    (M.toWeakJordan c).HasImproperEvenRank := by
  intro i hstrict
  rcases M.componentRank_eq_one_or_two i with hOne | hTwo
  · change finrank K (M.component i).carrier = 1 at hOne
    have hnormScale : ordUnit K (M.normGenerator i) =
        ordUnit K (M.scaleGenerator i) :=
      Lattice.ordUnit_normGenerator_eq_scaleGenerator_of_finrank_eq_one
        (M.component i).space (M.component i).lattice
        (M.scaleGenerator i) (M.normGenerator i) hOne
        (M.component_isModular c i) (M.normIdeal_eq i)
    have hnorm := M.toWeakJordan_normGeneratorOrder c i
    simp only [toWeakJordan_scaleGenerator] at hstrict
    omega
  · change finrank K (M.component i).carrier = 2 at hTwo
    change Even (finrank K (M.component i).carrier)
    rw [hTwo]
    exact even_two

/-- Every local component BONG has exactly the alternating order prescribed
by the maximal-norm weak Jordan profile. -/
theorem componentOrder_eq_weakJordanExpectedOrder
    (i : Fin t)
    (j : Fin (M.toOrthogonalDecomposition.componentRank i)) :
    (c i).order j =
      BONG.weakJordanExpectedOrder (M.toWeakJordan c) i j := by
  let W := M.toWeakJordan c
  have heffective := M.toWeakJordan_effectiveNormOrderAt_eq c i
  have hscaleLe : ordUnit K (M.scaleGenerator i) ≤
      ordUnit K (M.normGenerator i) := by
    have h := W.targetScale_le_effectiveNormOrderAt i
      (ordUnit K (M.scaleGenerator i))
    simpa only [W, M.toWeakJordan_scaleGenerator,
      heffective] using h
  rcases M.componentRank_eq_one_or_two i with hOne | hTwo
  · change finrank K (M.component i).carrier = 1 at hOne
    have hj : j = M.componentFirstIndex i := by
      apply Fin.ext
      change j.val = 0
      have hjlt : j.val < 1 := by
        simpa only [Lattice.OrthogonalDecomposition.componentRank,
          hOne] using j.isLt
      omega
    have hnormScale : ordUnit K (M.normGenerator i) =
        ordUnit K (M.scaleGenerator i) :=
      Lattice.ordUnit_normGenerator_eq_scaleGenerator_of_finrank_eq_one
        (M.component i).space (M.component i).lattice
        (M.scaleGenerator i) (M.normGenerator i) hOne
        (M.component_isModular c i) (M.normIdeal_eq i)
    rw [hj, M.componentFirst_order_eq_normGeneratorOrder c]
    simp only [BONG.weakJordanExpectedOrder, W,
      M.toWeakJordan_scaleGenerator, heffective]
    rw [hnormScale]
    exact (JordanProfileOrder.localOrder_of_proper _ _).symm
  · change finrank K (M.component i).carrier = 2 at hTwo
    have hjcases : j.val = 0 ∨ j.val = 1 := by
      have hjlt : j.val < 2 := by
        simpa only [Lattice.OrthogonalDecomposition.componentRank,
          hTwo] using j.isLt
      omega
    rcases hjcases with hjZero | hjOne
    · have hj : j = M.componentFirstIndex i := by
        apply Fin.ext
        simpa only [componentFirstIndex] using hjZero
      rw [hj, M.componentFirst_order_eq_normGeneratorOrder c]
      simp only [BONG.weakJordanExpectedOrder, W,
        M.toWeakJordan_scaleGenerator, heffective,
        componentFirstIndex, Fin.val_mk]
      exact (JordanProfileOrder.localOrder_even_of_scale_le
        hscaleLe (by simp)).symm
    · let b₂ := (c i).castLength hTwo
      have hOneLt : 1 < M.toOrthogonalDecomposition.componentRank i := by
        change 1 < finrank K (M.component i).carrier
        omega
      let one : Fin (M.toOrthogonalDecomposition.componentRank i) :=
        ⟨1, hOneLt⟩
      have hmodular : Lattice.IsModular (M.component i).space
          (M.component i).lattice (M.scaleGenerator i) :=
        M.component_isModular c i
      have hfirst : b₂.order 0 = ordUnit K (M.normGenerator i) := by
        have h := M.componentFirst_order_eq_normGeneratorOrder c i
        rw [BONG.order_castLength]
        convert h using 1
        apply congrArg (c i).order
        apply Fin.ext
        rfl
      have hsecond := b₂.order_one_eq_of_isModular
        (M.scaleGenerator i) hmodular
      have hj : j = one := Fin.ext hjOne
      rw [hj]
      have hcomponent : (c i).order one =
          2 * ordUnit K (M.scaleGenerator i) -
            ordUnit K (M.normGenerator i) := by
        have hcast : b₂.order 1 = (c i).order one := by
          rw [BONG.order_castLength]
          apply congrArg (c i).order
          apply Fin.ext
          rfl
        rw [← hcast]
        simpa only [hfirst] using hsecond
      rw [hcomponent]
      simp only [BONG.weakJordanExpectedOrder, W,
        M.toWeakJordan_scaleGenerator, heffective, one, Fin.val_mk]
      exact (JordanProfileOrder.localOrder_odd_of_scale_le
        hscaleLe (by norm_num)).symm

end Lattice.MaximalNormSplitting

namespace Lattice.WeakJordanDecomposition

/-- The profile of an arbitrary adjacent amalgamation, before requiring all
remaining scales to be strict, is the old profile at the retained index. -/
theorem weakJordanExpectedOrder_mergeAdjacentAt {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (p : Fin t) (oldAnchor : Fin (t + 1))
    (j : Fin (finrank K ((W.mergeAdjacentAt k heq).component p).carrier)) :
    BONG.weakJordanExpectedOrder (W.mergeAdjacentAt k heq) p j =
      JordanProfileOrder.localOrder
        (ordUnit K (W.scaleGenerator (k.succ.succAbove p)))
        (W.effectiveNormOrderAt oldAnchor
          (ordUnit K (W.scaleGenerator (k.succ.succAbove p)))) j.val := by
  simp only [BONG.weakJordanExpectedOrder,
    W.mergeAdjacentAt_scaleGenerator]
  rw [W.effectiveNormOrderAt_mergeAdjacentAt k heq p oldAnchor]

/-- Splitting one equal-scale amalgamation recovers the original weak
profile even if further equal-scale collisions remain. -/
theorem weakJordanExpectedOrder_mergeIndexEquiv_weak {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (z : Σ p : Fin t,
      Fin (finrank K ((W.mergeAdjacentAt k heq).component p).carrier)) :
    BONG.weakJordanExpectedOrder (W.mergeAdjacentAt k heq) z.1 z.2 =
      BONG.weakJordanExpectedOrder W (W.mergeIndexEquiv k heq z).1
        (W.mergeIndexEquiv k heq z).2 := by
  rcases z with ⟨p, j⟩
  rcases lt_trichotomy p k with hpk | hpkEq | hkp
  · have hmap := W.mergeIndexEquiv_of_lt k heq p hpk j
    rw [hmap]
    rw [W.weakJordanExpectedOrder_mergeAdjacentAt k heq p
      (k.succ.succAbove p)]
    simp only [BONG.weakJordanExpectedOrder]
    rw [Fin.succAbove_of_castSucc_lt]
    exact Fin.castSucc_lt_succ_iff.mpr hpk.le
  · subst p
    by_cases hj : j.val < finrank K (W.component k.castSucc).carrier
    · let left : Fin (finrank K (W.component k.castSucc).carrier) :=
        ⟨j.val, hj⟩
      let mergedLeft : Fin
          (finrank K ((W.mergeAdjacentAt k heq).component k).carrier) :=
        ⟨left.val, by
          rw [W.mergeAdjacentAt_componentRank_self k heq]
          omega⟩
      have hjEq : j = mergedLeft := Fin.ext rfl
      have hmap : W.mergeIndexEquiv k heq ⟨k, mergedLeft⟩ =
          ⟨k.castSucc, left⟩ := by
        simpa only [mergedLeft, left, Fin.val_mk] using
          W.mergeIndexEquiv_left k heq left
      rw [hjEq, hmap]
      rw [W.weakJordanExpectedOrder_mergeAdjacentAt k heq k k.castSucc]
      rw [Fin.succAbove_succ_self]
      simp only [BONG.weakJordanExpectedOrder, mergedLeft, left,
        Fin.val_mk]
    · have hjBound :
          j.val - finrank K (W.component k.castSucc).carrier <
            finrank K (W.component k.succ).carrier := by
        have hrank := W.mergeAdjacentAt_componentRank_self k heq
        have hbound : j.val <
            finrank K (W.component k.castSucc).carrier +
              finrank K (W.component k.succ).carrier := by
          simpa only [hrank] using j.isLt
        omega
      let right : Fin (finrank K (W.component k.succ).carrier) :=
        ⟨j.val - finrank K (W.component k.castSucc).carrier, hjBound⟩
      let mergedRight : Fin
          (finrank K ((W.mergeAdjacentAt k heq).component k).carrier) :=
        ⟨finrank K (W.component k.castSucc).carrier + right.val, by
          rw [W.mergeAdjacentAt_componentRank_self k heq]
          omega⟩
      have hjEq : j = mergedRight := by
        apply Fin.ext
        dsimp only [mergedRight, right, Fin.val_mk]
        omega
      have hmap : W.mergeIndexEquiv k heq ⟨k, mergedRight⟩ =
          ⟨k.succ, right⟩ := by
        simpa only [mergedRight, right, Fin.val_mk] using
          W.mergeIndexEquiv_right k heq right
      rw [hjEq, hmap]
      rw [W.weakJordanExpectedOrder_mergeAdjacentAt k heq k k.succ]
      rw [Fin.succAbove_succ_self]
      simp only [BONG.weakJordanExpectedOrder]
      rw [hW.localOrder_add_componentRank W k.succ k.castSucc right.val]
      rw [heq]
  · have hmap := W.mergeIndexEquiv_of_gt k heq p hkp j
    rw [hmap]
    rw [W.weakJordanExpectedOrder_mergeAdjacentAt k heq p
      (k.succ.succAbove p)]
    simp only [BONG.weakJordanExpectedOrder]
    rw [Fin.succAbove_of_le_castSucc]
    exact Fin.succ_le_castSucc_iff.mpr hkp

end Lattice.WeakJordanDecomposition

namespace BONG

open Lattice.OrthogonalDecomposition

/-- A BONG put together from a maximal-norm splitting has the exact weak
Jordan profile of that splitting. -/
noncomputable def weakJordanOrderProfileOfMaximalNormSplitting
    {n t : Nat} (b : BONG V q L n)
    (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily)
    (hput : b.IsPutTogether M.toOrthogonalDecomposition c) :
    WeakJordanOrderProfileWitness b (M.toWeakJordan c) := by
  let w := Classical.choice hput
  exact {
    indexEquiv := w.indexEquiv
    order_iff := by
      intro i j
      exact (w.order_iff i j).trans
        (JordanOrderProfileWitness.componentIndexBefore_iff_lex_lt
          M.toOrthogonalDecomposition (w.indexEquiv i) (w.indexEquiv j))
    order_eq := by
      intro i
      exact (w.order_eq i).trans
        (M.componentOrder_eq_weakJordanExpectedOrder c
          (w.indexEquiv i).1 (w.indexEquiv i).2)
  }

namespace WeakJordanOrderProfileWitness

/-- A strict weak Jordan profile is a profile for the associated Jordan
decomposition. -/
noncomputable def toJordanOfStrict {n t : Nat} {b : BONG V q L n}
    (W : Lattice.WeakJordanDecomposition q L t)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (w : WeakJordanOrderProfileWitness b W) :
    JordanOrderProfileWitness b (W.toJordan hstrict) where
  indexEquiv := w.indexEquiv
  order_iff := by
    intro i j
    exact (w.order_iff i j).trans
      (JordanOrderProfileWitness.componentIndexBefore_iff_lex_lt
        (W.toJordan hstrict).toOrthogonalDecomposition
        (w.indexEquiv i) (w.indexEquiv j)).symm
  order_eq := by
    intro i
    exact (w.order_eq i).trans
      (W.jordanExpectedOrder_toJordan hstrict
        (w.indexEquiv i).1 (w.indexEquiv i).2).symm

/-- A weak profile descends through one equal-scale adjacent amalgamation. -/
noncomputable def mergeAdjacentAt {n t : Nat} {b : BONG V q L n}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank) (w : WeakJordanOrderProfileWitness b W)
    (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    WeakJordanOrderProfileWitness b (W.mergeAdjacentAt k heq) where
  indexEquiv := w.indexEquiv.trans (W.mergeIndexEquiv k heq).symm
  order_iff := by
    intro i j
    let a := (W.mergeIndexEquiv k heq).symm (w.indexEquiv i)
    let d := (W.mergeIndexEquiv k heq).symm (w.indexEquiv j)
    have ha : W.mergeIndexOrderIso k heq (toLex a) =
        toLex (w.indexEquiv i) := by
      rw [← W.toLex_mergeIndexEquiv]
      simp only [a, (W.mergeIndexEquiv k heq).apply_symm_apply]
    have hd : W.mergeIndexOrderIso k heq (toLex d) =
        toLex (w.indexEquiv j) := by
      rw [← W.toLex_mergeIndexEquiv]
      simp only [d, (W.mergeIndexEquiv k heq).apply_symm_apply]
    change i < j ↔ toLex a < toLex d
    constructor
    · intro hij
      have hold := (w.order_iff i j).1 hij
      have hmapped : W.mergeIndexOrderIso k heq (toLex a) <
          W.mergeIndexOrderIso k heq (toLex d) := by
        rwa [ha, hd]
      exact (W.mergeIndexOrderIso k heq).lt_iff_lt.mp hmapped
    · intro hnew
      apply (w.order_iff i j).2
      have hmapped : W.mergeIndexOrderIso k heq (toLex a) <
          W.mergeIndexOrderIso k heq (toLex d) :=
        (W.mergeIndexOrderIso k heq).lt_iff_lt.mpr hnew
      rw [ha, hd] at hmapped
      exact hmapped
  order_eq := by
    intro i
    let z := (W.mergeIndexEquiv k heq).symm (w.indexEquiv i)
    have hz : W.mergeIndexEquiv k heq z = w.indexEquiv i :=
      (W.mergeIndexEquiv k heq).apply_symm_apply (w.indexEquiv i)
    calc
      b.order i = BONG.weakJordanExpectedOrder W
          (w.indexEquiv i).1 (w.indexEquiv i).2 := w.order_eq i
      _ = BONG.weakJordanExpectedOrder W
          (W.mergeIndexEquiv k heq z).1
          (W.mergeIndexEquiv k heq z).2 := by rw [hz]
      _ = BONG.weakJordanExpectedOrder (W.mergeAdjacentAt k heq)
          z.1 z.2 :=
        (W.weakJordanExpectedOrder_mergeIndexEquiv_weak
          hW k heq z).symm

/-- Repeatedly amalgamating equal-scale neighbours turns every weak profile
with the parity invariant into a profile for a strict Jordan decomposition. -/
theorem exists_jordanOrderProfile {n : Nat} {b : BONG V q L n} :
    ∀ (t : Nat) (W : Lattice.WeakJordanDecomposition q L t),
      W.HasImproperEvenRank → WeakJordanOrderProfileWitness b W →
        ∃ (s : Nat) (J : Lattice.JordanDecomposition q L s),
          Nonempty (JordanOrderProfileWitness b J) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro W hparity w
      let f : Fin t → Int := fun i ↦ ordUnit K (W.scaleGenerator i)
      by_cases hstrict : StrictMono f
      · exact ⟨t, W.toJordan hstrict,
          ⟨w.toJordanOfStrict W hstrict⟩⟩
      · cases t with
        | zero =>
            exfalso
            apply hstrict
            exact fun i ↦ Fin.elim0 i
        | succ t =>
            cases t with
            | zero =>
                exfalso
                apply hstrict
                intro i j hij
                omega
            | succ m =>
                have hadj : ¬∀ k : Fin (m + 1),
                    f k.castSucc < f k.succ := by
                  intro hall
                  exact hstrict ((Fin.strictMono_iff_lt_succ).2 hall)
                push Not at hadj
                obtain ⟨k, hk⟩ := hadj
                have hle : f k.castSucc ≤ f k.succ :=
                  W.scaleOrder_mono k.castSucc_lt_succ.le
                have heq : ordUnit K (W.scaleGenerator k.castSucc) =
                    ordUnit K (W.scaleGenerator k.succ) :=
                  le_antisymm hle hk
                let W' := W.mergeAdjacentAt k heq
                have hparity' : W'.HasImproperEvenRank := by
                  exact Lattice.WeakJordanDecomposition.HasImproperEvenRank.mergeAdjacentAt
                    W hparity k heq
                let w' : WeakJordanOrderProfileWitness b W' :=
                  w.mergeAdjacentAt W hparity k heq
                exact ih (m + 1) (by omega) W' hparity' w'

end WeakJordanOrderProfileWitness

namespace JordanOrderProfileWitness

/-- A profile for one strict Jordan decomposition transports to every
Jordan decomposition of the same lattice.  Scale positions and ranks are
intrinsic, and effective norms agree because they are norms of the same
scale truncations. -/
noncomputable def transportJordan {n s t : Nat} {b : BONG V q L n}
    (G : Lattice.JordanDecomposition q L s)
    (J : Lattice.JordanDecomposition q L t)
    (w : JordanOrderProfileWitness b G) :
    JordanOrderProfileWitness b J := by
  have hst : s = t := by
    have hcard := Fintype.card_congr (G.scaleIndexEquiv J)
    simpa only [Fintype.card_fin] using hcard
  subst t
  have hindex (k : Fin s) : G.scaleIndexEquiv J k = k := by
    apply Fin.ext
    exact G.scaleIndexEquiv_val J k
  have hRank : G.toOrthogonalDecomposition.componentRank =
      J.toOrthogonalDecomposition.componentRank := by
    funext k
    have h := G.componentRank_scaleIndexEquiv J k
    rw [hindex k] at h
    exact h.symm
  have hScale (k : Fin s) :
      ordUnit K (G.scaleGenerator k) =
        ordUnit K (J.scaleGenerator k) := by
    have h := G.scaleOrder_scaleIndexEquiv J k
    rw [hindex k] at h
    exact h.symm
  have hEffective (k : Fin s) :
      BONG.jordanEffectiveNormOrder G k =
        BONG.jordanEffectiveNormOrder J k := by
    calc
      BONG.jordanEffectiveNormOrder G k =
          BONG.jordanEffectiveNormOrderAt G k
            (ordUnit K (G.scaleGenerator k)) := rfl
      _ = BONG.jordanEffectiveNormOrderAt J k
            (ordUnit K (G.scaleGenerator k)) :=
        G.effectiveNormOrderAt_eq J k k
          (ordUnit K (G.scaleGenerator k))
      _ = BONG.jordanEffectiveNormOrderAt J k
            (ordUnit K (J.scaleGenerator k)) := by rw [hScale k]
      _ = BONG.jordanEffectiveNormOrder J k := rfl
  let R := JordanProfileIndexing.lexSigmaRankOrderIso
    G.toOrthogonalDecomposition.componentRank
    J.toOrthogonalDecomposition.componentRank hRank
  let E := w.indexOrderIso.trans R
  let e : Fin n ≃ Σ k : Fin s,
      Fin (J.toOrthogonalDecomposition.componentRank k) := {
    toFun := fun i ↦ ofLex (E i)
    invFun := fun z ↦ E.symm (toLex z)
    left_inv := by
      intro i
      change E.symm (E i) = i
      exact E.symm_apply_apply i
    right_inv := by
      intro z
      change ofLex (E (E.symm (toLex z))) = z
      rw [E.apply_symm_apply]
      exact ofLex_toLex z
  }
  have e_fst (i : Fin n) : (e i).1 = (w.indexEquiv i).1 := by
    simp only [e, E, R, OrderIso.trans_apply,
      indexOrderIso]
    exact JordanProfileIndexing.lexSigmaRankOrderIso_apply_fst'
      G.toOrthogonalDecomposition.componentRank
      J.toOrthogonalDecomposition.componentRank hRank (w.indexEquiv i)
  have e_snd_val (i : Fin n) :
      (e i).2.val = (w.indexEquiv i).2.val := by
    simp only [e, E, R, OrderIso.trans_apply,
      indexOrderIso]
    exact JordanProfileIndexing.lexSigmaRankOrderIso_apply_snd_val'
      G.toOrthogonalDecomposition.componentRank
      J.toOrthogonalDecomposition.componentRank hRank (w.indexEquiv i)
  exact {
    indexEquiv := e
    order_iff := by
      intro i j
      rw [JordanOrderProfileWitness.componentIndexBefore_iff_lex_lt]
      change i < j ↔ E i < E j
      exact E.lt_iff_lt.symm
    order_eq := by
      intro i
      have hscaleAt : ordUnit K
            (G.scaleGenerator (w.indexEquiv i).1) =
          ordUnit K (J.scaleGenerator (e i).1) := by
        exact (hScale (w.indexEquiv i).1).trans
          (congrArg (fun k ↦ ordUnit K (J.scaleGenerator k))
            (e_fst i).symm)
      have heffectiveAt : BONG.jordanEffectiveNormOrder G
            (w.indexEquiv i).1 =
          BONG.jordanEffectiveNormOrder J (e i).1 := by
        exact (hEffective (w.indexEquiv i).1).trans
          (congrArg (BONG.jordanEffectiveNormOrder J) (e_fst i).symm)
      calc
        b.order i = BONG.jordanExpectedOrder G
            (w.indexEquiv i).1 (w.indexEquiv i).2 := w.order_eq i
        _ = BONG.jordanExpectedOrder J (e i).1 (e i).2 := by
          simp only [BONG.jordanExpectedOrder]
          rw [hscaleAt, heffectiveAt, e_snd_val i]
  }

end JordanOrderProfileWitness

/-- Beli (2003), Lemma 4.7: every good BONG has the Jordan order profile
prescribed by every Jordan splitting of its lattice. -/
theorem jordanOrderProfile_proof {n t : Nat}
    (b : BONG V q L n) (hgood : b.IsGood)
    (J : Lattice.JordanDecomposition q L t) :
    Nonempty (JordanOrderProfileWitness b J) := by
  rcases b.good_has_improper_maximalNormSplitting_proof hgood with
    ⟨s, M, c, hput, _himproper⟩
  let W := M.toWeakJordan c
  let w : WeakJordanOrderProfileWitness b W :=
    weakJordanOrderProfileOfMaximalNormSplitting b M c hput
  have hparity : W.HasImproperEvenRank :=
    M.toWeakJordan_hasImproperEvenRank c
  rcases w.exists_jordanOrderProfile s W hparity with
    ⟨r, G, ⟨g⟩⟩
  exact ⟨g.transportJordan G J⟩

end BONG

/-- The fully proved law package for Beli (2003), Lemma 4.7. -/
@[reducible] noncomputable def beliLemma47LawsProved
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] :
    BeliLemma47Laws.{u, v} K :=
  beliLemma47LawsOfProfile (fun b hgood J ↦
    BONG.jordanOrderProfile_proof b hgood J)

noncomputable instance (K : Type u) [Field K] [CharZero K]
    [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] :
    BeliLemma47Laws.{u, v} K :=
  beliLemma47LawsProved K

end Bong
