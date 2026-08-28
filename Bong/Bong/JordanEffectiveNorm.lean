/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.JordanProfileOrder
import Bong.Lattice.JordanAmalgamation
import Bong.Lattice.RankOneNormScale

/-!
# Effective norm orders of Jordan decompositions

This file connects the finite profile arithmetic with weak and strict Jordan
decompositions.  Its main result says that amalgamating equal-scale adjacent
components preserves `ord n(L^s)` at every target scale.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice.WeakJordanDecomposition

/-- Scale orders of a weak Jordan decomposition. -/
noncomputable def scaleOrderFamily {t : Nat}
    (W : WeakJordanDecomposition q L t) : Fin t → Int :=
  fun j ↦ ordUnit K (W.scaleGenerator j)

/-- Component norm orders of a weak Jordan decomposition. -/
noncomputable def normOrderFamily {t : Nat}
    (W : WeakJordanDecomposition q L t) : Fin t → Int :=
  fun j ↦ ordUnit K (W.normGeneratorUnit j)

/-- The effective norm order at an arbitrary target scale. -/
noncomputable def effectiveNormOrderAt {t : Nat}
    (W : WeakJordanDecomposition q L t) (anchor : Fin t)
    (r : Int) : Int :=
  JordanProfileOrder.effectiveAt W.scaleOrderFamily W.normOrderFamily
    anchor r

/-- The norm ideal of a modular component is contained in its scale ideal,
so the chosen norm order is at least its scale order. -/
theorem scaleOrder_le_normOrder {t : Nat}
    (W : WeakJordanDecomposition q L t) (i : Fin t) :
    ordUnit K (W.scaleGenerator i) ≤
      ordUnit K (W.normGeneratorUnit i) := by
  have hideal : principalIdeal (K := K)
        (W.normGeneratorUnit i : K) ≤
      principalIdeal (K := K) (W.scaleGenerator i : K) := by
    rw [← W.normIdeal_eq_normGeneratorUnit,
      ← (W.modular i).scaleIdeal_eq_principal
        (W.component_finrank_pos i)]
    exact normIdeal_le_scaleIdeal (W.component i).space
      (W.component i).lattice
  have horder := (principalIdeal_le_iff_ord_ge
    (Units.ne_zero (W.normGeneratorUnit i))
    (Units.ne_zero (W.scaleGenerator i))).mp hideal
  apply WithTop.coe_le_coe.mp
  simpa only [coe_ordUnit] using horder

/-- The effective norm order at a target scale is never below that target
scale. -/
theorem targetScale_le_effectiveNormOrderAt {t : Nat}
    (W : WeakJordanDecomposition q L t) (anchor : Fin t) (r : Int) :
    r ≤ W.effectiveNormOrderAt anchor r := by
  apply JordanProfileOrder.target_le_effectiveAt
  intro j
  exact W.scaleOrder_le_normOrder j

/-- The anchor only witnesses that the component family is nonempty; it does
not affect the effective norm order. -/
theorem effectiveNormOrderAt_anchor_irrel {t : Nat}
    (W : WeakJordanDecomposition q L t) (a b : Fin t) (r : Int) :
    W.effectiveNormOrderAt a r = W.effectiveNormOrderAt b r :=
  JordanProfileOrder.effectiveAt_anchor_irrel
    W.scaleOrderFamily W.normOrderFamily a b r

/-- At the scale of a component, the effective norm order is bounded above
by that component's own norm order. -/
theorem effectiveNormOrderAt_scale_le_normOrder {t : Nat}
    (W : WeakJordanDecomposition q L t) (i : Fin t) :
    W.effectiveNormOrderAt i (ordUnit K (W.scaleGenerator i)) ≤
      ordUnit K (W.normGeneratorUnit i) := by
  calc
    W.effectiveNormOrderAt i (ordUnit K (W.scaleGenerator i)) ≤
        JordanProfileOrder.adjustedAt W.scaleOrderFamily W.normOrderFamily
          (ordUnit K (W.scaleGenerator i)) i :=
      JordanProfileOrder.effectiveAt_le _ _ _ _ _
    _ = ordUnit K (W.normGeneratorUnit i) := by
      simp [JordanProfileOrder.adjustedAt,
        WeakJordanDecomposition.scaleOrderFamily,
        WeakJordanDecomposition.normOrderFamily]

/-- An improper modular component (strict norm-scale gap) has even rank. -/
def HasImproperEvenRank {t : Nat}
    (W : WeakJordanDecomposition q L t) : Prop :=
  ∀ i, ordUnit K (W.scaleGenerator i) <
      ordUnit K (W.normGeneratorUnit i) →
    Even (finrank K (W.component i).carrier)

/-- If the global effective norm is strictly above a component scale, then
that component is improper and hence has even rank. -/
theorem HasImproperEvenRank.componentRank_even_of_lt_effectiveNormOrderAt
    {t : Nat} (W : WeakJordanDecomposition q L t)
    (hW : W.HasImproperEvenRank) (anchor i : Fin t)
    (hstrict : ordUnit K (W.scaleGenerator i) <
      W.effectiveNormOrderAt anchor (ordUnit K (W.scaleGenerator i))) :
    Even (finrank K (W.component i).carrier) := by
  apply hW i
  apply hstrict.trans_le
  calc
    W.effectiveNormOrderAt anchor (ordUnit K (W.scaleGenerator i)) =
        W.effectiveNormOrderAt i (ordUnit K (W.scaleGenerator i)) :=
      W.effectiveNormOrderAt_anchor_irrel anchor i _
    _ ≤ ordUnit K (W.normGeneratorUnit i) :=
      W.effectiveNormOrderAt_scale_le_normOrder i

/-- The profile of an equal-scale successor begins with the same parity as
the merged profile after the preceding component exactly when required by
O'Meara's improper-even-rank invariant. -/
theorem HasImproperEvenRank.localOrder_add_componentRank
    {t : Nat} (W : WeakJordanDecomposition q L t)
    (hW : W.HasImproperEvenRank) (anchor i : Fin t) (j : Nat) :
    JordanProfileOrder.localOrder
        (ordUnit K (W.scaleGenerator i))
        (W.effectiveNormOrderAt anchor (ordUnit K (W.scaleGenerator i)))
        (finrank K (W.component i).carrier + j) =
      JordanProfileOrder.localOrder
        (ordUnit K (W.scaleGenerator i))
        (W.effectiveNormOrderAt anchor (ordUnit K (W.scaleGenerator i))) j := by
  apply JordanProfileOrder.localOrder_add_left_of_proper_or_even
  by_cases hproper : ordUnit K (W.scaleGenerator i) =
      W.effectiveNormOrderAt anchor (ordUnit K (W.scaleGenerator i))
  · exact Or.inl hproper
  · exact Or.inr <| hW.componentRank_even_of_lt_effectiveNormOrderAt W anchor i
      (lt_of_le_of_ne (W.targetScale_le_effectiveNormOrderAt anchor _) hproper)

/-- For a weak Jordan family with the O'Meara parity invariant, the last
local coordinate of every component is the complementary alternating value.
In the proper case both sides reduce to the scale; in the improper case the
component rank is even, so its last zero-based coordinate is odd. -/
theorem HasImproperEvenRank.localOrder_last
    {t : Nat} (W : WeakJordanDecomposition q L t)
    (hW : W.HasImproperEvenRank) (i : Fin t) :
    JordanProfileOrder.localOrder
        (ordUnit K (W.scaleGenerator i))
        (W.effectiveNormOrderAt i (ordUnit K (W.scaleGenerator i)))
        (finrank K (W.component i).carrier - 1) =
      2 * ordUnit K (W.scaleGenerator i) -
        W.effectiveNormOrderAt i (ordUnit K (W.scaleGenerator i)) := by
  have hscale := W.targetScale_le_effectiveNormOrderAt i
    (ordUnit K (W.scaleGenerator i))
  by_cases hproper : ordUnit K (W.scaleGenerator i) =
      W.effectiveNormOrderAt i (ordUnit K (W.scaleGenerator i))
  · rw [← hproper]
    simp only [JordanProfileOrder.localOrder_of_proper]
    omega
  · have heffectiveStrict : ordUnit K (W.scaleGenerator i) <
        W.effectiveNormOrderAt i (ordUnit K (W.scaleGenerator i)) :=
      lt_of_le_of_ne hscale hproper
    have hnormStrict : ordUnit K (W.scaleGenerator i) <
        ordUnit K (W.normGeneratorUnit i) :=
      heffectiveStrict.trans_le
        (W.effectiveNormOrderAt_scale_le_normOrder i)
    have hrankEven := hW i hnormStrict
    have hrankPos := W.component_finrank_pos i
    have hlastOdd : ¬Even (finrank K (W.component i).carrier - 1) := by
      rcases hrankEven with ⟨k, hk⟩
      intro heven
      rcases heven with ⟨l, hl⟩
      omega
    exact JordanProfileOrder.localOrder_odd_of_scale_le hscale hlastOdd

/-- Every raw O'Meara component satisfies the improper-even-rank property:
rank-one components have equal norm and scale, while the other raw
components have rank two. -/
theorem hasImproperEvenRank_ofRaw {t : Nat}
    (R : RawJordanDecomposition q L t) :
    (WeakJordanDecomposition.ofRaw R).HasImproperEvenRank := by
  intro i hstrict
  rcases R.rank_one_or_two i with hOne | hTwo
  · have heq :=
      ordUnit_normGenerator_eq_scaleGenerator_of_finrank_eq_one
        ((WeakJordanDecomposition.ofRaw R).component i).space
        ((WeakJordanDecomposition.ofRaw R).component i).lattice
        ((WeakJordanDecomposition.ofRaw R).scaleGenerator i)
        ((WeakJordanDecomposition.ofRaw R).normGeneratorUnit i)
        hOne ((WeakJordanDecomposition.ofRaw R).modular i)
        ((WeakJordanDecomposition.ofRaw R).normIdeal_eq_normGeneratorUnit i)
    omega
  · change Even (finrank K (R.component i).carrier)
    rw [hTwo]
    exact even_two

/-- The improper-even-rank property is preserved by equal-scale
amalgamation. -/
theorem HasImproperEvenRank.mergeAdjacentAt {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    (W.mergeAdjacentAt k heq).HasImproperEvenRank := by
  intro j hstrict
  by_cases hjk : j = k
  · subst j
    have hnorm :=
      W.ordUnit_normGeneratorUnit_mergeAdjacentAt_self k heq
    have hscale := W.mergeAdjacentAt_scaleGenerator k heq k
    have hscale' :
        (W.mergeAdjacentAt k heq).scaleGenerator k =
          W.scaleGenerator k.castSucc := by
      simpa using hscale
    have hfirst : ordUnit K (W.scaleGenerator k.castSucc) <
        ordUnit K (W.normGeneratorUnit k.castSucc) := by
      rw [hnorm, hscale'] at hstrict
      exact hstrict.trans_le (min_le_left _ _)
    have hsecond : ordUnit K (W.scaleGenerator k.succ) <
        ordUnit K (W.normGeneratorUnit k.succ) := by
      rw [hnorm, hscale'] at hstrict
      rw [← heq]
      exact hstrict.trans_le (min_le_right _ _)
    rw [W.mergeAdjacentAt_componentRank_self k heq]
    exact (hW k.castSucc hfirst).add (hW k.succ hsecond)
  · have hscale := W.mergeAdjacentAt_scaleGenerator k heq j
    have hnorm :=
      W.ordUnit_normGeneratorUnit_mergeAdjacentAt_of_ne k heq j hjk
    have hold : ordUnit K
          (W.scaleGenerator (k.succ.succAbove j)) <
        ordUnit K (W.normGeneratorUnit (k.succ.succAbove j)) := by
      rw [← hscale, ← hnorm]
      exact hstrict
    rw [W.mergeAdjacentAt_component_of_ne k heq j hjk]
    exact hW (k.succ.succAbove j) hold

/-- Repeated amalgamation can be carried out while retaining the
improper-even-rank invariant. -/
theorem exists_strict_with_improperEvenRank :
    ∀ (t : Nat) (W : WeakJordanDecomposition q L t),
      W.HasImproperEvenRank →
      ∃ (s : Nat) (S : WeakJordanDecomposition q L s),
        StrictMono (fun i ↦ ordUnit K (S.scaleGenerator i)) ∧
          S.HasImproperEvenRank := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro W hparity
      let f : Fin t → Int := fun i ↦ ordUnit K (W.scaleGenerator i)
      by_cases hstrict : StrictMono f
      · exact ⟨t, W, hstrict, hparity⟩
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
            | succ n =>
                have hadj : ¬∀ k : Fin (n + 1),
                    f k.castSucc < f k.succ := by
                  intro h
                  exact hstrict ((Fin.strictMono_iff_lt_succ).2 h)
                push Not at hadj
                obtain ⟨k, hk⟩ := hadj
                have hle : f k.castSucc ≤ f k.succ :=
                  W.scaleOrder_mono k.castSucc_lt_succ.le
                have heq : ordUnit K (W.scaleGenerator k.castSucc) =
                    ordUnit K (W.scaleGenerator k.succ) :=
                  le_antisymm hle hk
                let W' := W.mergeAdjacent k heq
                have hparity' : W'.HasImproperEvenRank := by
                  change (W.mergeAdjacentAt k heq).HasImproperEvenRank
                  exact HasImproperEvenRank.mergeAdjacentAt W hparity k heq
                exact ih (n + 1) (by omega) W' hparity'

/-- A chosen strict refinement together with the parity invariant used by
the Section 5 exceptional unary case. -/
noncomputable def strictParityWitness {t : Nat}
    (W : WeakJordanDecomposition q L t)
    (hparity : W.HasImproperEvenRank) :
    Σ s : Nat, {S : WeakJordanDecomposition q L s //
      StrictMono (fun i ↦ ordUnit K (S.scaleGenerator i)) ∧
        S.HasImproperEvenRank} := by
  let h := exists_strict_with_improperEvenRank t W hparity
  exact ⟨h.choose, ⟨h.choose_spec.choose,
    h.choose_spec.choose_spec⟩⟩

/-- Passing a strict weak decomposition to a Jordan decomposition preserves
its effective norm order. -/
theorem effectiveNormOrderAt_toJordan {t : Nat}
    (W : WeakJordanDecomposition q L t)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (anchor : Fin t) (r : Int) :
    BONG.jordanEffectiveNormOrderAt (W.toJordan hstrict) anchor r =
      W.effectiveNormOrderAt anchor r := by
  rfl

/-- The Jordan profile of a strict weak decomposition is the generic local
alternating order built from its scale and effective norm orders. -/
theorem jordanExpectedOrder_toJordan {t : Nat}
    (W : WeakJordanDecomposition q L t)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (k : Fin t)
    (i : Fin ((W.toJordan hstrict).toOrthogonalDecomposition.componentRank k)) :
    BONG.jordanExpectedOrder (W.toJordan hstrict) k i =
      JordanProfileOrder.localOrder
        (ordUnit K (W.scaleGenerator k))
        (W.effectiveNormOrderAt k (ordUnit K (W.scaleGenerator k)))
        i.val := by
  rfl

/-- The scale-order family after an adjacent merge is the generic
`mergeScale` family. -/
theorem scaleOrderFamily_mergeAdjacentAt {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    (W.mergeAdjacentAt k heq).scaleOrderFamily =
      JordanProfileOrder.mergeScale W.scaleOrderFamily k := by
  funext j
  simp [scaleOrderFamily, JordanProfileOrder.mergeScale]

/-- The norm-order family after an adjacent merge replaces the two old
orders by their minimum. -/
theorem normOrderFamily_mergeAdjacentAt {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    (W.mergeAdjacentAt k heq).normOrderFamily =
      JordanProfileOrder.mergeNorm W.normOrderFamily k := by
  funext j
  by_cases hjk : j = k
  · subst j
    simpa [normOrderFamily, JordanProfileOrder.mergeNorm] using
      W.ordUnit_normGeneratorUnit_mergeAdjacentAt_self k heq
  · simpa [normOrderFamily, JordanProfileOrder.mergeNorm, hjk] using
      W.ordUnit_normGeneratorUnit_mergeAdjacentAt_of_ne k heq j hjk

/-- Equal-scale amalgamation preserves the norm of every scale truncation. -/
theorem effectiveNormOrderAt_mergeAdjacentAt {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (anchor : Fin t) (oldAnchor : Fin (t + 1)) (r : Int) :
    (W.mergeAdjacentAt k heq).effectiveNormOrderAt anchor r =
      W.effectiveNormOrderAt oldAnchor r := by
  rw [effectiveNormOrderAt, effectiveNormOrderAt,
    W.scaleOrderFamily_mergeAdjacentAt k heq,
    W.normOrderFamily_mergeAdjacentAt k heq]
  exact JordanProfileOrder.effectiveAt_merge
    W.scaleOrderFamily W.normOrderFamily k heq anchor oldAnchor r

/-- At the merged component, the strict Jordan profile uses exactly the old
global effective norm at the common scale. -/
theorem jordanExpectedOrder_mergeAdjacentAt {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hstrict : StrictMono (fun i ↦
      ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator i)))
    (oldAnchor : Fin (t + 1))
    (j : Fin (finrank K ((W.mergeAdjacentAt k heq).component k).carrier)) :
    BONG.jordanExpectedOrder ((W.mergeAdjacentAt k heq).toJordan hstrict) k j =
      JordanProfileOrder.localOrder
        (ordUnit K (W.scaleGenerator k.castSucc))
        (W.effectiveNormOrderAt oldAnchor
          (ordUnit K (W.scaleGenerator k.castSucc))) j.val := by
  rw [jordanExpectedOrder_toJordan]
  simp only [W.mergeAdjacentAt_scaleGenerator]
  rw [W.effectiveNormOrderAt_mergeAdjacentAt k heq k oldAnchor]
  rw [Fin.succAbove_succ_self]

/-- Away from the retained position, the merged strict Jordan profile is
the unchanged old component profile at the index skipping the removed
second neighbor. -/
theorem jordanExpectedOrder_mergeAdjacentAt_of_ne {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hstrict : StrictMono (fun i ↦
      ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator i)))
    (p : Fin t)
    (j : Fin (finrank K ((W.mergeAdjacentAt k heq).component p).carrier)) :
    BONG.jordanExpectedOrder ((W.mergeAdjacentAt k heq).toJordan hstrict) p j =
      JordanProfileOrder.localOrder
        (ordUnit K (W.scaleGenerator (k.succ.succAbove p)))
        (W.effectiveNormOrderAt (k.succ.succAbove p)
          (ordUnit K (W.scaleGenerator (k.succ.succAbove p)))) j.val := by
  rw [jordanExpectedOrder_toJordan]
  simp only [W.mergeAdjacentAt_scaleGenerator]
  rw [W.effectiveNormOrderAt_mergeAdjacentAt k heq p
    (k.succ.succAbove p)]

/-- The first old component occupies the initial segment of the merged
Jordan profile without any parity shift. -/
theorem jordanExpectedOrder_mergeAdjacentAt_left {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hstrict : StrictMono (fun i ↦
      ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator i)))
    (oldAnchor : Fin (t + 1))
    (j : Fin (finrank K (W.component k.castSucc).carrier)) :
    BONG.jordanExpectedOrder ((W.mergeAdjacentAt k heq).toJordan hstrict) k
        ⟨j.val, by
          change j.val < finrank K
            ((W.mergeAdjacentAt k heq).component k).carrier
          rw [W.mergeAdjacentAt_componentRank_self k heq]
          omega⟩ =
      JordanProfileOrder.localOrder
        (ordUnit K (W.scaleGenerator k.castSucc))
        (W.effectiveNormOrderAt oldAnchor
          (ordUnit K (W.scaleGenerator k.castSucc))) j.val := by
  exact W.jordanExpectedOrder_mergeAdjacentAt k heq hstrict oldAnchor _

/-- Under the improper-even-rank invariant, the second old component starts
at the correct parity inside the merged Jordan profile. -/
theorem HasImproperEvenRank.jordanExpectedOrder_mergeAdjacentAt_right {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hstrict : StrictMono (fun i ↦
      ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator i)))
    (oldAnchor : Fin (t + 1))
    (j : Fin (finrank K (W.component k.succ).carrier)) :
    BONG.jordanExpectedOrder ((W.mergeAdjacentAt k heq).toJordan hstrict) k
        ⟨finrank K (W.component k.castSucc).carrier + j.val, by
          change finrank K (W.component k.castSucc).carrier + j.val <
            finrank K ((W.mergeAdjacentAt k heq).component k).carrier
          rw [W.mergeAdjacentAt_componentRank_self k heq]
          omega⟩ =
      JordanProfileOrder.localOrder
        (ordUnit K (W.scaleGenerator k.succ))
        (W.effectiveNormOrderAt oldAnchor
          (ordUnit K (W.scaleGenerator k.succ))) j.val := by
  rw [W.jordanExpectedOrder_mergeAdjacentAt k heq hstrict oldAnchor]
  rw [hW.localOrder_add_componentRank W oldAnchor k.castSucc j.val]
  rw [heq]

end Lattice.WeakJordanDecomposition

namespace Lattice.JordanDecomposition

/-- For a property-A Jordan decomposition, the norm of the intrinsic
scale layer at the scale of a component is generated by that component's
chosen norm generator.  Components to the left acquire twice the scale
difference, while components to the right already have strictly larger norm
order; the two inequalities in property A say precisely that neither can
lower the minimum. -/
theorem HasPropertyA.jordanEffectiveNormOrder_eq_normGenerator
    {t : Nat} (J : JordanDecomposition q L t) (hA : J.HasPropertyA)
    (k : Fin t) :
    BONG.jordanEffectiveNormOrder J k =
      ordUnit K (J.normGenerator k) := by
  unfold BONG.jordanEffectiveNormOrder
    BONG.jordanEffectiveNormOrderAt
  apply le_antisymm
  · calc
      JordanProfileOrder.effectiveAt
            (fun j ↦ ordUnit K (J.scaleGenerator j))
            (fun j ↦ ordUnit K (J.normGenerator j)) k
            (ordUnit K (J.scaleGenerator k)) ≤
          JordanProfileOrder.adjustedAt
            (fun j ↦ ordUnit K (J.scaleGenerator j))
            (fun j ↦ ordUnit K (J.normGenerator j))
            (ordUnit K (J.scaleGenerator k)) k :=
        JordanProfileOrder.effectiveAt_le _ _ k k _
      _ = ordUnit K (J.normGenerator k) := by
        simp [JordanProfileOrder.adjustedAt]
  · apply JordanProfileOrder.le_effectiveAt
    intro j
    rcases lt_trichotomy j k with hj | hj | hj
    · have hscale := J.scaleOrder_strict hj
      have hgap := hA.2 hj
      simp only [JordanProfileOrder.adjustedAt, if_pos hscale]
      omega
    · subst j
      simp [JordanProfileOrder.adjustedAt]
    · have hscale := J.scaleOrder_strict hj
      have hgap := hA.2 hj
      simp only [JordanProfileOrder.adjustedAt,
        if_neg (not_lt_of_ge hscale.le)]
      omega

end Lattice.JordanDecomposition

end Bong
