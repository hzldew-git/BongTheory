/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma715
import Bong.Bong.Beli2019Lemma79NormOrder
import Bong.Bong.Beli2019ExtremalDifference

/-!
# Beli (2019), Lemma 7.16: the elementary order ranges

This module proves the parts of representation condition 2.1(i) which use
only Lemma 7.15, the alternating plateau of Lemma 7.14, and the strict
norm-ideal inequality.  The two exceptional coordinates in type I and the
single exceptional coordinate in type II are deliberately not assumed here.

The paper uses one-based indices.  Thus its unchanged tail `i ≥ s + 1` is
the zero-based range `s ≤ i.val`, while the elementary shifted prefix is
`i.val < s - 2`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Condition 2.1(i) transfers at every coordinate where the new target has
the same current and next orders as the old target. -/
theorem lemma716_orderClause_of_tail_order_eq
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (s : Nat)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (i : Fin (n + 3)) (hsi : s ≤ i.val) :
    b.order i ≤ c.order i ∨
      ∃ (hi0 : 0 < i.val) (hiLarge : i.val + 1 < n + 3),
        b.order i + b.order ⟨i.val + 1, hiLarge⟩ ≤
          c.order ⟨i.val - 1, by omega⟩ + c.order i := by
  rcases hac i with hcurrent | ⟨hi0, hiLarge, hpair⟩
  · left
    change a.order i ≤ c.order i at hcurrent
    simpa only [horders i hsi] using hcurrent
  · right
    refine ⟨hi0, hiLarge, ?_⟩
    change a.order i + a.order ⟨i.val + 1, hiLarge⟩ ≤
      c.order ⟨i.val - 1, by omega⟩ + c.order i at hpair
    have hnextS : s ≤ i.val + 1 := hsi.trans (Nat.le_add_right _ _)
    have hnext := horders ⟨i.val + 1, hiLarge⟩ hnextS
    simpa only [horders i hsi, hnext] using hpair

/-- Strict containment of norm ideals raises the first comparison order by
at least one, written relative to the paper's integer `R`. -/
theorem lemma716_comparison_order_zero_ge
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (hfirst : a.order 0 = R)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    R + 1 ≤ c.order 0 := by
  have h := a.toBONG.order_zero_add_one_le_of_normIdeal_lt c.toBONG hnorm
  change a.order 0 + 1 ≤ c.order 0 at h
  simpa only [hfirst] using h

/-- The strict norm-ideal lower bound propagates along every even
zero-based coordinate of a good BONG. -/
theorem lemma716_comparison_even_order_ge
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (hfirst : a.order 0 = R)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : Fin (n + 3)) (hiEven : Even i.val) :
    R + 1 ≤ c.order i := by
  have hzero := lemma716_comparison_order_zero_ge a c R hfirst hnorm
  have hmono := c.orderSequence.entryOrZero_le_of_evenGap
    0 i.val (Nat.zero_le _) i.isLt hiEven
  rw [c.orderSequence_entryOrZero_eq_order ⟨0, by omega⟩,
    c.orderSequence_entryOrZero_eq_order i] at hmono
  exact hzero.trans hmono

/-- The adjacent-gap bound and two-step monotonicity give the companion
lower bound on every odd zero-based coordinate. -/
theorem lemma716_comparison_odd_order_ge
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (hfirst : a.order 0 = R)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : Fin (n + 3)) (hiOdd : Odd i.val) :
    R - 2 * (ramificationIndex K : Int) + 1 ≤ c.order i := by
  have hzero := lemma716_comparison_order_zero_ge a c R hfirst hnorm
  have hgap := c.orderGap_ge_neg_two_mul_e (0 : Fin (n + 2))
  change -(2 * (ramificationIndex K : Int)) ≤
    c.order 1 - c.order 0 at hgap
  have hiOne : 1 ≤ i.val := by
    rcases hiOdd with ⟨d, hd⟩
    omega
  have hiGapEven : Even (i.val - 1) := by
    rcases hiOdd with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hmono := c.orderSequence.entryOrZero_le_of_evenGap
    1 i.val hiOne i.isLt hiGapEven
  rw [c.orderSequence_entryOrZero_eq_order ⟨1, by omega⟩,
    c.orderSequence_entryOrZero_eq_order i] at hmono
  change c.order 1 ≤ c.order i at hmono
  omega

/-- A coefficient shifted two places to the left has order `R + 1` on the
even part of the Lemma 7.14 plateau. -/
theorem lemma716_shiftedPrefix_order_eq_high
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (i : Fin (n + 3)) (hiPrefix : i.val < s - 2)
    (hiEven : Even i.val)
    (hshift : b.valueUnit i = a.valueUnit ⟨i.val + 2, by
      have := D.le_rank
      omega⟩) :
    b.order i = R + 1 := by
  have hsRank := D.le_rank
  have hsFour : 4 ≤ s := by
    rcases D.even with ⟨d, hd⟩
    rcases hiEven with ⟨e, he⟩
    omega
  have hiShiftEven : Even (i.val + 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d + 1, by omega⟩
  have hiShiftLe : i.val + 2 ≤ s - 2 := by
    rcases D.even with ⟨d, hd⟩
    rcases hiEven with ⟨e, he⟩
    omega
  have P := a.beli2019Lemma714_i R s D.toLemma714MinimalityData
    hsFour hthird
  calc
    b.order i = ordUnit K (b.valueUnit i) := b.toBONG.order_eq_ordUnit i
    _ = ordUnit K (a.valueUnit ⟨i.val + 2, by omega⟩) :=
      congrArg (ordUnit K) hshift
    _ = a.order ⟨i.val + 2, by omega⟩ :=
      (a.toBONG.order_eq_ordUnit ⟨i.val + 2, by omega⟩).symm
    _ = R + 1 := P.high_positions (i.val + 2) (by omega)
      hiShiftLe hiShiftEven

/-- A coefficient shifted two places to the left has order `R - 2e + 1`
on the odd part of the Lemma 7.14 plateau. -/
theorem lemma716_shiftedPrefix_order_eq_low
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (i : Fin (n + 3)) (hiPrefix : i.val < s - 2)
    (hiOdd : Odd i.val)
    (hshift : b.valueUnit i = a.valueUnit ⟨i.val + 2, by
      have := D.le_rank
      omega⟩) :
    b.order i = R - 2 * (ramificationIndex K : Int) + 1 := by
  have hsRank := D.le_rank
  have hsFour : 4 ≤ s := by
    rcases D.even with ⟨d, hd⟩
    rcases hiOdd with ⟨e, he⟩
    omega
  have hiShiftOdd : Odd (i.val + 2) := by
    rcases hiOdd with ⟨d, hd⟩
    exact ⟨d + 1, by omega⟩
  have hiShiftThree : 3 ≤ i.val + 2 := by
    rcases hiOdd with ⟨d, hd⟩
    omega
  have hiShiftLe : i.val + 2 ≤ s - 1 := by omega
  have P := a.beli2019Lemma714_i R s D.toLemma714MinimalityData
    hsFour hthird
  calc
    b.order i = ordUnit K (b.valueUnit i) := b.toBONG.order_eq_ordUnit i
    _ = ordUnit K (a.valueUnit ⟨i.val + 2, by omega⟩) :=
      congrArg (ordUnit K) hshift
    _ = a.order ⟨i.val + 2, by omega⟩ :=
      (a.toBONG.order_eq_ordUnit ⟨i.val + 2, by omega⟩).symm
    _ = R - 2 * (ramificationIndex K : Int) + 1 :=
      P.low_positions (i.val + 2) hiShiftThree hiShiftLe hiShiftOdd

/-- The type-I replacement has the high plateau order at every elementary
even prefix coordinate. -/
theorem lemma716_typeI_prefix_order_eq_high
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (i : Fin (n + 3)) (hiPrefix : i.val < s - 2)
    (hiEven : Even i.val) : b.order i = R + 1 := by
  apply lemma716_shiftedPrefix_order_eq_high a b R s D hthird i
    hiPrefix hiEven
  calc
    b.valueUnit i = lemma714TypeITargetValues a s D.two_le D.le_rank i :=
      hvalues i
    _ = a.valueUnit ⟨i.val + 2, by
        have := D.le_rank
        omega⟩ :=
      lemma714TypeITargetValues_prefix a s D.two_le D.le_rank i hiPrefix

/-- The type-I replacement has the low plateau order at every elementary
odd prefix coordinate. -/
theorem lemma716_typeI_prefix_order_eq_low
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (i : Fin (n + 3)) (hiPrefix : i.val < s - 2)
    (hiOdd : Odd i.val) :
    b.order i = R - 2 * (ramificationIndex K : Int) + 1 := by
  apply lemma716_shiftedPrefix_order_eq_low a b R s D hthird i
    hiPrefix hiOdd
  calc
    b.valueUnit i = lemma714TypeITargetValues a s D.two_le D.le_rank i :=
      hvalues i
    _ = a.valueUnit ⟨i.val + 2, by
        have := D.le_rank
        omega⟩ :=
      lemma714TypeITargetValues_prefix a s D.two_le D.le_rank i hiPrefix

/-- The elementary type-I prefix already satisfies the direct alternative
of condition 2.1(i). -/
theorem lemma716_typeI_prefix_order_le
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (i : Fin (n + 3)) (hiPrefix : i.val < s - 2) :
    b.order i ≤ c.order i := by
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · rw [lemma716_typeI_prefix_order_eq_high a b R s D hthird hvalues
      i hiPrefix hiEven]
    exact lemma716_comparison_even_order_ge a c R hfirst hnorm i hiEven
  · rw [lemma716_typeI_prefix_order_eq_low a b R s D hthird hvalues
      i hiPrefix hiOdd]
    exact lemma716_comparison_odd_order_ge a c R hfirst hnorm i hiOdd

/-- The first exceptional type-I coefficient has order `R + 2`. -/
theorem lemma716_typeI_leftBoundary_order_eq
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j) :
    b.order ⟨s - 2, by
      have := D.le_rank
      omega⟩ = R + 2 := by
  have hpi : ordUnit K (uniformizerUnit K) = 1 := by
    simpa [uniformizerPowerUnit] using
      (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
  let left : Fin (n + 3) := ⟨s - 2, by
    have := D.le_rank
    omega⟩
  calc
    b.order left = ordUnit K (b.valueUnit left) :=
      b.toBONG.order_eq_ordUnit left
    _ = ordUnit K (lemma714TypeITargetValues a s D.two_le
        D.le_rank left) := congrArg (ordUnit K) (hvalues left)
    _ = ordUnit K (uniformizerUnit K ^ 2 * a.valueUnit 0) := by
      congr 1
      simpa only [left] using
        lemma714TypeITargetValues_zero a s D.two_le D.le_rank
    _ = 2 + a.order 0 := by
      have ha0 : ordUnit K (a.valueUnit (0 : Fin (n + 3))) =
          a.order (0 : Fin (n + 3)) :=
        (a.toBONG.order_eq_ordUnit (0 : Fin (n + 3))).symm
      rw [ordUnit_mul, ordUnit_pow, hpi, ha0]
      norm_num
    _ = R + 2 := by omega

/-- The second exceptional type-I coefficient has order `R - 2e + 2`. -/
theorem lemma716_typeI_rightBoundary_order_eq
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j) :
    b.order ⟨s - 1, by
      have := D.le_rank
      omega⟩ = R - 2 * (ramificationIndex K : Int) + 2 := by
  have hpi : ordUnit K (uniformizerUnit K) = 1 := by
    simpa [uniformizerPowerUnit] using
      (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
  let right : Fin (n + 3) := ⟨s - 1, by
    have := D.le_rank
    omega⟩
  calc
    b.order right = ordUnit K (b.valueUnit right) :=
      b.toBONG.order_eq_ordUnit right
    _ = ordUnit K (lemma714TypeITargetValues a s D.two_le
        D.le_rank right) := congrArg (ordUnit K) (hvalues right)
    _ = ordUnit K (uniformizerUnit K ^ 2 * a.valueUnit 1) := by
      congr 1
      simpa only [right] using
        lemma714TypeITargetValues_one a s D.two_le D.le_rank
    _ = 2 + a.order 1 := by
      have ha1 : ordUnit K (a.valueUnit (1 : Fin (n + 3))) =
          a.order (1 : Fin (n + 3)) :=
        (a.toBONG.order_eq_ordUnit (1 : Fin (n + 3))).symm
      rw [ordUnit_mul, ordUnit_pow, hpi, ha1]
      norm_num
    _ = R - 2 * (ramificationIndex K : Int) + 2 := by omega

variable [DyadicDiscriminantClassLaws K]

/-- The type-II replacement has the same shifted prefix as type I, hence the
same high plateau order at even coordinates. -/
theorem lemma716_typeII_prefix_order_eq_high
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hII : Lemma714IsTypeII a R s) (ε η : Kˣ)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) ε η j)
    (i : Fin (n + 3)) (hiPrefix : i.val < s - 2)
    (hiEven : Even i.val) : b.order i = R + 1 := by
  apply lemma716_shiftedPrefix_order_eq_high a b R s D hthird i
    hiPrefix hiEven
  calc
    b.valueUnit i = lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) ε η i := hvalues i
    _ = a.valueUnit ⟨i.val + 2, by
        have := D.le_rank
        omega⟩ :=
      lemma714TypeIITargetValues_prefix a s D.two_le
        (Classical.choose hII) ε η i hiPrefix

/-- The type-II replacement has the low plateau order at odd shifted-prefix
coordinates. -/
theorem lemma716_typeII_prefix_order_eq_low
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hII : Lemma714IsTypeII a R s) (ε η : Kˣ)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) ε η j)
    (i : Fin (n + 3)) (hiPrefix : i.val < s - 2)
    (hiOdd : Odd i.val) :
    b.order i = R - 2 * (ramificationIndex K : Int) + 1 := by
  apply lemma716_shiftedPrefix_order_eq_low a b R s D hthird i
    hiPrefix hiOdd
  calc
    b.valueUnit i = lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) ε η i := hvalues i
    _ = a.valueUnit ⟨i.val + 2, by
        have := D.le_rank
        omega⟩ :=
      lemma714TypeIITargetValues_prefix a s D.two_le
        (Classical.choose hII) ε η i hiPrefix

/-- The type-II replacement has order `R + 1` at zero-based coordinate
`s - 2`, the first entry of its exceptional ternary block. -/
theorem lemma716_typeII_leftBoundary_order_eq
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hII : Lemma714IsTypeII a R s) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) ε η j) :
    b.order ⟨s - 2, by
      have := D.le_rank
      omega⟩ = R + 1 := by
  let left : Fin (n + 3) := ⟨s - 2, by
    have := D.le_rank
    omega⟩
  calc
    b.order left = ordUnit K (b.valueUnit left) :=
      b.toBONG.order_eq_ordUnit left
    _ = ordUnit K (lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) ε η left) :=
      congrArg (ordUnit K) (hvalues left)
    _ = R + 1 := by
      simpa only [left] using
        ordUnit_lemma714TypeIITargetValues_zero a R s D.two_le
          (Classical.choose hII) (Classical.choose_spec hII)
          ε η hεUnit hηUnit

/-- The middle entry of the exceptional type-II ternary block has order
`R - 2e + 3`. -/
theorem lemma716_typeII_rightBoundary_order_eq
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hII : Lemma714IsTypeII a R s) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) ε η j) :
    b.order ⟨s - 1, by
      have := D.le_rank
      omega⟩ = R - 2 * (ramificationIndex K : Int) + 3 := by
  let right : Fin (n + 3) := ⟨s - 1, by
    have := D.le_rank
    omega⟩
  calc
    b.order right = ordUnit K (b.valueUnit right) :=
      b.toBONG.order_eq_ordUnit right
    _ = ordUnit K (lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) ε η right) :=
      congrArg (ordUnit K) (hvalues right)
    _ = R - 2 * (ramificationIndex K : Int) + 3 := by
      simpa only [right] using
        ordUnit_lemma714TypeIITargetValues_one a R s D.two_le
          (Classical.choose hII) (Classical.choose_spec hII)
          ε η hεUnit hηUnit

/-- The last entry of the exceptional type-II ternary block has order
`R + 1`. -/
theorem lemma716_typeII_tailBoundary_order_eq
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hII : Lemma714IsTypeII a R s) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) ε η j) :
    b.order ⟨s, Classical.choose hII⟩ = R + 1 := by
  let tail : Fin (n + 3) := ⟨s, Classical.choose hII⟩
  calc
    b.order tail = ordUnit K (b.valueUnit tail) :=
      b.toBONG.order_eq_ordUnit tail
    _ = ordUnit K (lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) ε η tail) :=
      congrArg (ordUnit K) (hvalues tail)
    _ = R + 1 := by
      simpa only [tail] using
        ordUnit_lemma714TypeIITargetValues_two a R s D.two_le
          (Classical.choose hII) (Classical.choose_spec hII)
          ε η hεUnit hηUnit

/-- The direct order alternative holds throughout the full elementary
type-II prefix `i.val < s - 1`, including the first ternary-block entry. -/
theorem lemma716_typeII_early_order_le
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hII : Lemma714IsTypeII a R s) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) ε η j)
    (i : Fin (n + 3)) (hiEarly : i.val < s - 1) :
    b.order i ≤ c.order i := by
  by_cases hiPrefix : i.val < s - 2
  · rcases Nat.even_or_odd i.val with hiEven | hiOdd
    · rw [lemma716_typeII_prefix_order_eq_high a b R s D hthird hII
        ε η hvalues i hiPrefix hiEven]
      exact lemma716_comparison_even_order_ge a c R hfirst hnorm i hiEven
    · rw [lemma716_typeII_prefix_order_eq_low a b R s D hthird hII
        ε η hvalues i hiPrefix hiOdd]
      exact lemma716_comparison_odd_order_ge a c R hfirst hnorm i hiOdd
  · have hiEq : i.val = s - 2 := by omega
    have hiEven : Even i.val := by
      rcases D.even with ⟨d, hd⟩
      exact ⟨d - 1, by omega⟩
    let left : Fin (n + 3) := ⟨s - 2, by
      have := D.le_rank
      omega⟩
    have hiLeft : i = left := Fin.ext hiEq
    have hleftEven : Even left.val := by
      change Even (s - 2)
      rw [← hiEq]
      exact hiEven
    rw [hiLeft]
    rw [lemma716_typeII_leftBoundary_order_eq a b R s D hII ε η
      hεUnit hηUnit hvalues]
    exact lemma716_comparison_even_order_ge a c R hfirst hnorm left hleftEven

end BONG.GoodBONG

end Bong
