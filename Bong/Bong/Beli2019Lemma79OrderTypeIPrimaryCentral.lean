/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIFromConditions
import Bong.Bong.Beli2019Lemma79OrderTypeISecondary

/-!
# Beli (2019), Lemma 7.9(i): the central type-I primary candidate

Lemma 7.7 places the alternating source prefix strictly above the cut forced
by a nonpositive primary candidate.  Sharp capped-defect multiplication then
identifies the preceding third self-prefix with the mixed prefix.  Lemma
7.4(i) converts that defect bound into the required adjacent-pair inequality.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- In the central type-I interval, the source prefix from Lemma 7.7 is
strictly above the coefficient cut occurring in the primary candidate. -/
theorem lemma79_typeI_even_sourcePrefix_gt_primaryCut
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (k : Nat) (hkNext : k + 1 < n + 2) (hkTwo : k + 2 < n + 2)
    (hkEven : Even k) (hleft : C.leftSwitch ≤ k)
    (hright : k < C.rightSwitch) :
    (((a.order (0 : Fin (n + 2)) + 1 -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) : WithTop ℚ) <
      a.truncatedPrefixDefect a ((-1) ^ ((k + 2) / 2)) 0 (k + 2) := by
  let current : Fin (n + 1) := ⟨k, by omega⟩
  let next : Fin (n + 1) := ⟨k + 1, by omega⟩
  have hkPlusTwoEven : Even (k + 2) := by
    rcases hkEven with ⟨d, hd⟩
    exact ⟨d + 1, by omega⟩
  have hweight := a.beli2019Lemma69_v_typeI_of_rightSwitch_lt_last
    b D C hfirst hrightLast horder hdefect k hleft hright
  have halphaCurrent : 2 ≤ a.alphaValue current := by
    have h := lemma69_v_typeI_alpha_ge_two_of_leftEndpoint_eq
      a b D C hfirst (k + 2) (by omega) (by omega) hkPlusTwoEven
        hleft hright.le (by
          simpa only [current, show k + 2 - 2 = k by omega] using hweight)
    simpa only [current, show k + 2 - 2 = k by omega] using h
  have hendpoint := a.alphaLeftEndpoint_monotone
    (show current ≤ next by
      change k ≤ k + 1
      omega)
  have hcurrentCast : current.castSucc =
      (⟨k, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hnextCast : next.castSucc = ⟨k + 1, hkNext⟩ := by
    apply Fin.ext
    rfl
  have hcapQ :
      ((a.order ⟨k, by omega⟩ - a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) + 2 ≤
        a.alphaValue next := by
    unfold alphaLeftEndpoint at hendpoint
    rw [hcurrentCast, hnextCast] at hendpoint
    push_cast at hendpoint ⊢
    linarith
  have hcap :
      ((((a.order ⟨k, by omega⟩ -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) + 2 : ℚ) : WithTop ℚ) ≤
        a.prefixAlphaCap (k + 2) := by
    rw [a.prefixAlphaCap_of_internal (by omega) hkTwo]
    simpa only [next, show k + 2 - 1 = k + 1 by omega] using
      WithTop.coe_le_coe.mpr hcapQ
  have hraw :=
    a.beli2019Lemma77_typeI_of_rightSwitch_lt_last_from_conditions
      b D C hfirst hrightLast horder hdefect (k + 2) (by omega)
        (by omega) hkPlusTwoEven hleft (by omega)
  have hself :
      ((((a.order ⟨k, by omega⟩ -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) + 2 : ℚ) : WithTop ℚ) ≤
        a.truncatedPrefixDefect a ((-1) ^ ((k + 2) / 2)) 0 (k + 2) := by
    unfold truncatedPrefixDefect
    rw [a.prefixAlphaCap_zero]
    simp only [min_top_left]
    apply le_min
    · simpa only [alternatingPrefixDefect, GoodBONG.prefixProduct,
        BONG.prefixProduct_zero, mul_one,
        show k + 2 - 2 = k by omega,
        show k + 2 - 1 = k + 1 by omega] using hraw
    · exact hcap
  have hplateau := lemma77_typeI_source_plateau
    a b D C hfirst (k + 2) (by omega) (by omega) hkPlusTwoEven hright.le
  have hplateau' : a.order (0 : Fin (n + 2)) =
      a.order ⟨k, by omega⟩ := by
    simpa only [show k + 2 - 2 = k by omega] using hplateau
  have hstrict :
      (((a.order (0 : Fin (n + 2)) + 1 -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) : WithTop ℚ) <
        ((((a.order ⟨k, by omega⟩ -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) + 2 : ℚ) : WithTop ℚ) := by
    norm_cast
    push_cast
    linarith [hplateau']
  exact hstrict.trans_le hself

/-- A nonpositive primary candidate bounds the mixed prefix defect by the
order cut at the next source coordinate. -/
theorem lemma79_typeI_even_primary_mixed_le_cut
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (hkEven : Even k)
    (hleft : C.leftSwitch ≤ k) (hlast : k ≤ D.profile.last)
    (hnot : ¬ b.orderSequence.entry k hk ≤
      c.orderSequence.entry k hk)
    (hprimary : a.representationPrimaryDefect c {
      val := k + 1
      pos := by omega
      lt_large := hkNext
      le_small := hkNext.le } ≤ 0) :
    a.truncatedPrefixDefect c (-1) (k + 2) k ≤
      (((a.order (0 : Fin (n + 2)) + 1 -
        a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) : WithTop ℚ) := by
  let idx : RepresentationIndex (n + 2) (n + 2) := {
    val := k + 1
    pos := by omega
    lt_large := hkNext
    le_small := hkNext.le }
  rcases lemma79_typeI_even_failure_orders
      a b c D C hfirst hnorm k hk hkEven hleft hlast hnot with
    ⟨_, _, hcCurrent⟩
  have hcCurrentOrder : c.order ⟨k, hk⟩ =
      a.order (0 : Fin (n + 2)) + 1 := by
    rw [← c.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact hcCurrent
  let mixed := a.truncatedPrefixDefect c (-1) (k + 2) k
  have hprimary' : a.representationPrimaryDefect c idx ≤ 0 := by
    simpa only [idx] using hprimary
  unfold representationPrimaryDefect at hprimary'
  have hmixedNe : mixed ≠ ⊤ := by
    intro htop
    rw [show a.truncatedPrefixDefect c (-1) (idx.val + 1)
        (idx.val - 1) = mixed by
          simp only [idx, mixed, Nat.add_sub_cancel],
      htop] at hprimary'
    simp at hprimary'
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hmixedNe
  rw [show a.truncatedPrefixDefect c (-1) (idx.val + 1)
      (idx.val - 1) = mixed by
        simp only [idx, mixed, Nat.add_sub_cancel],
    ← hd] at hprimary'
  change mixed ≤ _
  rw [← hd]
  norm_cast at hprimary' ⊢
  push_cast at hprimary' ⊢
  have haIndex : a.order ⟨idx.val, idx.lt_large⟩ =
      a.order ⟨k + 1, hkNext⟩ := by
    apply congrArg a.order
    apply Fin.ext
    rfl
  have hcIndex : c.order ⟨idx.val - 1, by
      have := idx.le_small
      omega⟩ = c.order ⟨k, hk⟩ := by
    apply congrArg c.order
    apply Fin.ext
    simp only [idx, Nat.add_sub_cancel]
  rw [haIndex, hcIndex, hcCurrentOrder] at hprimary'
  push_cast at hprimary'
  linarith

/-- The defect-theoretic core of the type-I primary branch.  Besides the
order inequality extracted below, the terminal-switch equality case needs
the sharp multiplication identity and the precise Lemma 7.4 lower bound;
they are kept together here so that no information is lost at the boundary. -/
theorem lemma79_typeI_even_primary_defect_core_of_sourcePrefix
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (hkEven : Even k)
    (hleft : C.leftSwitch ≤ k) (hlast : k ≤ D.profile.last)
    (hnot : ¬ b.orderSequence.entry k hk ≤
      c.orderSequence.entry k hk)
    (hsource :
      (((a.order (0 : Fin (n + 2)) + 1 -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) : WithTop ℚ) <
        a.truncatedPrefixDefect a ((-1) ^ ((k + 2) / 2)) 0 (k + 2))
    (hprimary : a.representationPrimaryDefect c {
      val := k + 1
      pos := by omega
      lt_large := hkNext
      le_small := hkNext.le } ≤ 0) :
    2 ≤ k ∧
      c.orderSequence.entryOrZero (k - 2) =
        a.orderSequence.entryOrZero 0 + 1 ∧
      c.truncatedPrefixDefect c ((-1) ^ (k / 2)) 0 k =
        a.truncatedPrefixDefect c (-1) (k + 2) k ∧
      ((((c.order ⟨k - 2, by omega⟩ -
          c.order ⟨k - 1, by omega⟩ : Int) : ℚ) +
        c.alphaValue ⟨k - 2, by omega⟩ : ℚ) : WithTop ℚ) ≤
        c.truncatedPrefixDefect c ((-1) ^ (k / 2)) 0 k ∧
      c.truncatedPrefixDefect c ((-1) ^ (k / 2)) 0 k ≤
        (((a.order (0 : Fin (n + 2)) + 1 -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) : WithTop ℚ) := by
  rcases lemma79_typeI_even_failure_orders
      a b c D C hfirst hnorm k hk hkEven hleft hlast hnot with
    ⟨_, hcFirst, _⟩
  let mixed := a.truncatedPrefixDefect c (-1) (k + 2) k
  have hmixedLe := lemma79_typeI_even_primary_mixed_le_cut
    a b c D C hfirst hnorm k hk hkNext hkEven hleft hlast hnot hprimary
  have hseparation :
      c.truncatedPrefixDefect a (-1) k (k + 2) <
        a.truncatedPrefixDefect a ((-1) ^ ((k + 2) / 2)) (k + 2) 0 := by
    rw [c.truncatedPrefixDefect_comm a (-1) k (k + 2),
      a.truncatedPrefixDefect_comm a ((-1) ^ ((k + 2) / 2))
        (k + 2) 0]
    exact hmixedLe.trans_lt hsource
  have hsharp := c.truncatedPrefixDefect_mul_eq_left_of_lt_right
    a a (-1) ((-1) ^ ((k + 2) / 2)) k (k + 2) 0 hseparation
  have hsign :
      (-1 : Kˣ) * ((-1) ^ ((k + 2) / 2)) = (-1) ^ (k / 2) := by
    rcases hkEven with ⟨d, hd⟩
    have hkHalf : k / 2 = d := by omega
    have hkTwoHalf : (k + 2) / 2 = d + 1 := by omega
    rw [hkHalf, hkTwoHalf, pow_succ]
    calc
      (-1 : Kˣ) * ((-1) ^ d * (-1)) =
          ((-1) * (-1)) * ((-1) ^ d) := by ac_rfl
      _ = (-1) ^ d := by norm_num
  have hthirdEq :
      c.truncatedPrefixDefect c ((-1) ^ (k / 2)) 0 k = mixed := by
    calc
      c.truncatedPrefixDefect c ((-1) ^ (k / 2)) 0 k =
          c.truncatedPrefixDefect c ((-1) ^ (k / 2)) k 0 :=
        c.truncatedPrefixDefect_comm c ((-1) ^ (k / 2)) 0 k
      _ = c.truncatedPrefixDefect a ((-1) ^ (k / 2)) k 0 :=
        (c.truncatedPrefixDefect_zero_right_eq_self
          a ((-1) ^ (k / 2)) k).symm
      _ = c.truncatedPrefixDefect a
          ((-1) * ((-1) ^ ((k + 2) / 2))) k 0 := by rw [hsign]
      _ = c.truncatedPrefixDefect a (-1) k (k + 2) := hsharp
      _ = a.truncatedPrefixDefect c (-1) (k + 2) k :=
        c.truncatedPrefixDefect_comm a (-1) k (k + 2)
      _ = mixed := rfl
  have hthirdUpper :
      c.truncatedPrefixDefect c ((-1) ^ (k / 2)) 0 k ≤
        (((a.order (0 : Fin (n + 2)) + 1 -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) : WithTop ℚ) := by
    rw [hthirdEq]
    exact hmixedLe
  have hkTwoLower : 2 ≤ k := by
    by_contra hnotTwo
    have hkZero : k = 0 := by
      rcases hkEven with ⟨d, hd⟩
      omega
    subst k
    simp [truncatedPrefixDefect, GoodBONG.prefixProduct,
      BONG.prefixProduct_zero, defectOrder_one] at hthirdUpper
  have hcPrevious : c.orderSequence.entryOrZero (k - 2) =
      a.orderSequence.entryOrZero 0 + 1 := by
    have hzeroPrevious := c.orderSequence.entryOrZero_le_of_evenGap
      0 (k - 2) (Nat.zero_le _) (by omega) (by
        rcases hkEven with ⟨d, hd⟩
        exact ⟨d - 1, by omega⟩)
    have hpreviousCurrent := c.orderSequence.entryOrZero_le_of_evenGap
      (k - 2) k (by omega) hk (by exact ⟨1, by omega⟩)
    omega
  let first : Fin (n + 1) := ⟨0, by omega⟩
  let last : Fin (n + 1) := ⟨k - 2, by omega⟩
  have horders : c.order first.castSucc = c.order last.castSucc := by
    rw [← c.orderSequence_entryOrZero_eq_order,
      ← c.orderSequence_entryOrZero_eq_order]
    change c.orderSequence.entryOrZero 0 =
      c.orderSequence.entryOrZero (k - 2)
    exact hcFirst.trans hcPrevious.symm
  have h74 := c.beli2019Lemma74_i first last (by
      change 0 ≤ k - 2
      omega) (by
        rcases hkEven with ⟨d, hd⟩
        exact ⟨d - 1, by simp only [first, last]; omega⟩) horders
  have hlastCast : last.castSucc =
      (⟨k - 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hlastSucc : last.succ =
      (⟨k - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [last, Fin.val_succ]
    omega
  rw [hlastCast, hlastSucc] at h74
  have hlower :
      ((((c.order ⟨k - 2, by omega⟩ -
          c.order ⟨k - 1, by omega⟩ : Int) : ℚ) +
        c.alphaValue ⟨k - 2, by omega⟩ : ℚ) : WithTop ℚ) ≤
        c.truncatedPrefixDefect c ((-1) ^ (k / 2)) 0 k := by
    simpa only [first, last, Nat.sub_zero,
      show k - 2 + 2 = k by omega,
      show (k - 2 + 2) / 2 = k / 2 by omega] using h74
  exact ⟨hkTwoLower, hcPrevious, by simpa only [mixed] using hthirdEq,
    hlower, hthirdUpper⟩

/-- The common core of the type-I primary branch: strict source-prefix
separation forces the next source order below the preceding comparison order. -/
theorem lemma79_typeI_even_primary_sourceNext_le_previous_of_sourcePrefix
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (hkEven : Even k)
    (hleft : C.leftSwitch ≤ k) (hlast : k ≤ D.profile.last)
    (hnot : ¬ b.orderSequence.entry k hk ≤
      c.orderSequence.entry k hk)
    (hsource :
      (((a.order (0 : Fin (n + 2)) + 1 -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) : WithTop ℚ) <
        a.truncatedPrefixDefect a ((-1) ^ ((k + 2) / 2)) 0 (k + 2))
    (hprimary : a.representationPrimaryDefect c {
      val := k + 1
      pos := by omega
      lt_large := hkNext
      le_small := hkNext.le } ≤ 0) :
    2 ≤ k ∧
      a.orderSequence.entryOrZero (k + 1) ≤
        c.orderSequence.entryOrZero (k - 1) := by
  rcases lemma79_typeI_even_failure_orders
      a b c D C hfirst hnorm k hk hkEven hleft hlast hnot with
    ⟨_, hcFirst, _⟩
  let mixed := a.truncatedPrefixDefect c (-1) (k + 2) k
  have hmixedLe := lemma79_typeI_even_primary_mixed_le_cut
    a b c D C hfirst hnorm k hk hkNext hkEven hleft hlast hnot hprimary
  have hseparation :
      c.truncatedPrefixDefect a (-1) k (k + 2) <
        a.truncatedPrefixDefect a ((-1) ^ ((k + 2) / 2)) (k + 2) 0 := by
    rw [c.truncatedPrefixDefect_comm a (-1) k (k + 2),
      a.truncatedPrefixDefect_comm a ((-1) ^ ((k + 2) / 2))
        (k + 2) 0]
    exact hmixedLe.trans_lt hsource
  have hsharp := c.truncatedPrefixDefect_mul_eq_left_of_lt_right
    a a (-1) ((-1) ^ ((k + 2) / 2)) k (k + 2) 0 hseparation
  have hsign :
      (-1 : Kˣ) * ((-1) ^ ((k + 2) / 2)) = (-1) ^ (k / 2) := by
    rcases hkEven with ⟨d, hd⟩
    have hkHalf : k / 2 = d := by omega
    have hkTwoHalf : (k + 2) / 2 = d + 1 := by omega
    rw [hkHalf, hkTwoHalf, pow_succ]
    calc
      (-1 : Kˣ) * ((-1) ^ d * (-1)) =
          ((-1) * (-1)) * ((-1) ^ d) := by ac_rfl
      _ = (-1) ^ d := by norm_num
  have hthirdEq :
      c.truncatedPrefixDefect c ((-1) ^ (k / 2)) 0 k = mixed := by
    calc
      c.truncatedPrefixDefect c ((-1) ^ (k / 2)) 0 k =
          c.truncatedPrefixDefect c ((-1) ^ (k / 2)) k 0 :=
        c.truncatedPrefixDefect_comm c ((-1) ^ (k / 2)) 0 k
      _ = c.truncatedPrefixDefect a ((-1) ^ (k / 2)) k 0 :=
        (c.truncatedPrefixDefect_zero_right_eq_self
          a ((-1) ^ (k / 2)) k).symm
      _ = c.truncatedPrefixDefect a
          ((-1) * ((-1) ^ ((k + 2) / 2))) k 0 := by rw [hsign]
      _ = c.truncatedPrefixDefect a (-1) k (k + 2) := hsharp
      _ = a.truncatedPrefixDefect c (-1) (k + 2) k :=
        c.truncatedPrefixDefect_comm a (-1) k (k + 2)
      _ = mixed := rfl
  have hthirdUpper :
      c.truncatedPrefixDefect c ((-1) ^ (k / 2)) 0 k ≤
        (((a.order (0 : Fin (n + 2)) + 1 -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) : WithTop ℚ) := by
    rw [hthirdEq]
    exact hmixedLe
  have hkTwoLower : 2 ≤ k := by
    by_contra hnotTwo
    have hkZero : k = 0 := by
      rcases hkEven with ⟨d, hd⟩
      omega
    subst k
    simp [truncatedPrefixDefect, GoodBONG.prefixProduct,
      BONG.prefixProduct_zero, defectOrder_one] at hthirdUpper
  have hcPrevious : c.orderSequence.entryOrZero (k - 2) =
      a.orderSequence.entryOrZero 0 + 1 := by
    have hzeroPrevious := c.orderSequence.entryOrZero_le_of_evenGap
      0 (k - 2) (Nat.zero_le _) (by omega) (by
        rcases hkEven with ⟨d, hd⟩
        exact ⟨d - 1, by omega⟩)
    have hpreviousCurrent := c.orderSequence.entryOrZero_le_of_evenGap
      (k - 2) k (by omega) hk (by exact ⟨1, by omega⟩)
    omega
  let first : Fin (n + 1) := ⟨0, by omega⟩
  let last : Fin (n + 1) := ⟨k - 2, by omega⟩
  have horders : c.order first.castSucc = c.order last.castSucc := by
    rw [← c.orderSequence_entryOrZero_eq_order,
      ← c.orderSequence_entryOrZero_eq_order]
    change c.orderSequence.entryOrZero 0 =
      c.orderSequence.entryOrZero (k - 2)
    exact hcFirst.trans hcPrevious.symm
  have h74 := c.beli2019Lemma74_i first last (by
      change 0 ≤ k - 2
      omega) (by
        rcases hkEven with ⟨d, hd⟩
        exact ⟨d - 1, by simp only [first, last]; omega⟩) horders
  have hlastCast : last.castSucc =
      (⟨k - 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hlastSucc : last.succ =
      (⟨k - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [last, Fin.val_succ]
    omega
  rw [hlastCast, hlastSucc] at h74
  have hlower :
      ((((c.order ⟨k - 2, by omega⟩ -
          c.order ⟨k - 1, by omega⟩ : Int) : ℚ) +
        c.alphaValue ⟨k - 2, by omega⟩ : ℚ) : WithTop ℚ) ≤
        c.truncatedPrefixDefect c ((-1) ^ (k / 2)) 0 k := by
    simpa only [first, last, Nat.sub_zero,
      show k - 2 + 2 = k by omega,
      show (k - 2 + 2) / 2 = k / 2 by omega] using h74
  have hcoefficientTop := hlower.trans hthirdUpper
  norm_cast at hcoefficientTop
  push_cast at hcoefficientTop
  have halphaNonnegative := (c.alpha_p2 ⟨k - 2, by omega⟩).1
  have hsourceNextLePreviousQ :
      (a.order ⟨k + 1, hkNext⟩ : ℚ) ≤
        (c.order ⟨k - 1, by omega⟩ : ℚ) := by
    have haZero : a.order (0 : Fin (n + 2)) =
        (a.orderSequence.entryOrZero 0) := by
      exact (a.orderSequence_entryOrZero_eq_order
        (0 : Fin (n + 2))).symm
    have hcPreviousOrder : c.order ⟨k - 2, by omega⟩ =
        a.orderSequence.entryOrZero 0 + 1 := by
      rw [← c.orderSequence_entryOrZero_eq_order]
      exact hcPrevious
    rw [haZero, hcPreviousOrder] at hcoefficientTop
    push_cast at hcoefficientTop
    linarith
  have hsourceNextLePrevious :
      a.orderSequence.entryOrZero (k + 1) ≤
        c.orderSequence.entryOrZero (k - 1) := by
    rw [a.orderSequence_entryOrZero_eq_order ⟨k + 1, hkNext⟩,
      c.orderSequence_entryOrZero_eq_order ⟨k - 1, by omega⟩]
    exact_mod_cast hsourceNextLePreviousQ
  exact ⟨hkTwoLower, hsourceNextLePrevious⟩

/-- A strict source-prefix separation and a one-unit source-target shift turn
a nonpositive primary candidate into the adjacent-pair alternative. -/
theorem lemma79_typeI_even_primary_data_of_sourcePrefix
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (_hkTwo : k + 2 < n + 2) (hkEven : Even k)
    (hleft : C.leftSwitch ≤ k) (hlast : k ≤ D.profile.last)
    (hnot : ¬ b.orderSequence.entry k hk ≤
      c.orderSequence.entry k hk)
    (hsource :
      (((a.order (0 : Fin (n + 2)) + 1 -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) : WithTop ℚ) <
        a.truncatedPrefixDefect a ((-1) ^ ((k + 2) / 2)) 0 (k + 2))
    (hsourceTargetNextLower :
      b.orderSequence.entryOrZero (k + 1) + 1 ≤
        a.orderSequence.entryOrZero (k + 1))
    (hprimary : a.representationPrimaryDefect c {
      val := k + 1
      pos := by omega
      lt_large := hkNext
      le_small := hkNext.le } ≤ 0) :
    2 ≤ k ∧
      b.orderSequence.entry k hk +
          b.orderSequence.entry (k + 1) hkNext ≤
        c.orderSequence.entry (k - 1) (by omega) +
          c.orderSequence.entry k hk := by
  rcases lemma79_typeI_even_primary_sourceNext_le_previous_of_sourcePrefix
      a b c D C hfirst hnorm k hk hkNext hkEven hleft hlast
        hnot hsource hprimary with
    ⟨hkTwoLower, hsourceNextLePrevious⟩
  rcases lemma79_typeI_even_failure_orders
      a b c D C hfirst hnorm k hk hkEven hleft hlast hnot with
    ⟨hbCurrent, _, hcCurrent⟩
  have hbCurrent' : b.orderSequence.entry k hk =
      a.orderSequence.entryOrZero 0 + 2 := by
    rw [← b.orderSequence.entryOrZero_of_lt hk]
    exact hbCurrent
  have hcCurrent' : c.orderSequence.entry k hk =
      a.orderSequence.entryOrZero 0 + 1 := by
    rw [← c.orderSequence.entryOrZero_of_lt hk]
    exact hcCurrent
  have hsourceNextLePrevious' :
      a.orderSequence.entryOrZero (k + 1) ≤
        c.orderSequence.entry (k - 1) (by omega) := by
    rw [← c.orderSequence.entryOrZero_of_lt (by omega)]
    exact hsourceNextLePrevious
  have hsourceTargetNextLower' :
      b.orderSequence.entry (k + 1) hkNext + 1 ≤
        a.orderSequence.entryOrZero (k + 1) := by
    rw [← b.orderSequence.entryOrZero_of_lt hkNext]
    exact hsourceTargetNextLower
  exact ⟨hkTwoLower, by omega⟩

/-- A nonpositive primary candidate gives the adjacent-pair alternative at
every nonterminal even coordinate strictly before the right switch. -/
theorem lemma79_typeI_even_primary_data_central
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (hkTwo : k + 2 < n + 2) (hkEven : Even k)
    (hleft : C.leftSwitch ≤ k) (hlast : k ≤ D.profile.last)
    (hright : k < C.rightSwitch)
    (hnot : ¬ b.orderSequence.entry k hk ≤
      c.orderSequence.entry k hk)
    (hprimary : a.representationPrimaryDefect c {
      val := k + 1
      pos := by omega
      lt_large := hkNext
      le_small := hkNext.le } ≤ 0) :
    2 ≤ k ∧
      b.orderSequence.entry k hk +
          b.orderSequence.entry (k + 1) hkNext ≤
        c.orderSequence.entry (k - 1) (by omega) +
          c.orderSequence.entry k hk := by
  have hsource := lemma79_typeI_even_sourcePrefix_gt_primaryCut
    a b D C hfirst hrightLast horder hdefect k hkNext hkTwo hkEven
      hleft hright
  have hnextOdd : Odd (k + 1) := by
    rcases hkEven with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hsourceTargetNext := lemma69_v_typeI_odd_entry_gap_two
    a b D C hfirst (k + 1) hnextOdd (by omega) (by omega)
  have hsourceTargetNextLower :
      b.orderSequence.entryOrZero (k + 1) + 1 ≤
        a.orderSequence.entryOrZero (k + 1) := by
    omega
  exact lemma79_typeI_even_primary_data_of_sourcePrefix
    a b c D C hfirst hnorm k hk hkNext hkTwo hkEven hleft hlast
      hnot hsource hsourceTargetNextLower hprimary

end BONG.GoodBONG

end Bong
