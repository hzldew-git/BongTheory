/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralEndpointTowers
import Bong.Bong.Beli2019Lemma79CentralTypeIMiddleEven
import Bong.Bong.Beli2019Lemma69TypeILeft
import Bong.Bong.Beli2019Lemma79EvenTypeIBoundaryAlpha

/-!
# Beli (2019), Lemma 7.9(iii): arithmetic for the early region

Cases 1 and 5 begin with two common reductions.  An alpha strictly above
`2e - 1` is at least `2e`; at an odd type-I early index this forces the
preceding gap to be exactly `2e`.  At an even early index the order trigger
forces the index to be the first canonical switch.  The latter reduction is
the zero-based form of the contradiction

`R + 1 ≤ T₁ ≤ T_(i-1) < S_(i+1) = R + 1`

in the printed proof.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Corollary 2.8(iii) excludes an alpha strictly between the consecutive
integers `2e - 1` and `2e`. -/
theorem alphaValue_ge_twoE_of_gt_twoE_sub_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (x : GoodBONG q L (n + 1)) (p : Fin n)
    (hstrict : 2 * (ramificationIndex K : ℚ) - 1 < x.alphaValue p) :
    2 * (ramificationIndex K : ℚ) ≤ x.alphaValue p := by
  rcases x.beli2009Corollary28_iii p with
    ⟨_, _, hintegral⟩ | ⟨hlarge, _⟩
  · rcases hintegral with ⟨z, hz⟩
    have hstep : 2 * (ramificationIndex K : Int) ≤ z := by
      have hlt : 2 * (ramificationIndex K : Int) - 1 < z := by
        have hcast :
            ((2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) =
              2 * (ramificationIndex K : ℚ) - 1 := by
          norm_num
        exact_mod_cast (show
          ((2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) <
            (z : ℚ) by
          rw [hcast]
          simpa only [← hz] using hstrict)
      omega
    rw [hz]
    exact_mod_cast hstep
  · exact hlarge.le

/-- The alpha lower bound `alpha ≥ 2e` forces the same lower bound on its
order gap. -/
theorem orderGap_ge_twoE_of_alphaValue_ge_twoE_early
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (x : GoodBONG q L (n + 1)) (p : Fin n)
    (halpha : 2 * (ramificationIndex K : ℚ) ≤ x.alphaValue p) :
    2 * (ramificationIndex K : Int) ≤ x.orderGap p := by
  by_contra hnot
  have hgap : x.orderGap p < 2 * (ramificationIndex K : Int) :=
    lt_of_not_ge hnot
  have halphaStrict : x.alphaValue p <
      2 * (ramificationIndex K : ℚ) :=
    (x.beli2009Corollary28_ii p).1.mpr hgap
  exact (not_lt_of_ge halpha) halphaStrict

/-- At an odd type-I early index, an alpha above `2e - 1` makes the
preceding target gap exactly `2e`.  Lemma 6.6 supplies the upper bound all
the way down to the first possible central index. -/
theorem lemma79Central_typeIEarly_odd_previousGap_eq_twoE
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hearly : i.val ≤ C.leftSwitch) (hiOdd : Odd i.val)
    (halpha : 2 * (ramificationIndex K : ℚ) - 1 <
      b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩) :
    b.orderGap ⟨i.val - 2, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ =
      2 * (ramificationIndex K : Int) := by
  have hleftEven := C.left_even
  have hiStrict : i.val < C.leftSwitch := by
    rcases hiOdd with ⟨d, hd⟩
    rcases hleftEven with ⟨e, he⟩
    omega
  have hleftFour : 4 ≤ C.leftSwitch := by
    rcases hiOdd with ⟨d, hd⟩
    rcases hleftEven with ⟨e, he⟩
    have := i.one_lt
    omega
  let right : Fin (n + 2) := ⟨C.leftSwitch - 2, by
    have hbound := C.left_le_anchor.trans_lt D.anchor_bound
    omega⟩
  have hrightEven : Even right.val := by
    rcases C.left_even with ⟨d, hd⟩
    exact ⟨d - 1, by simp only [right]; omega⟩
  have hzeroEntry := C.target_before_left 0 (by omega) ⟨0, by omega⟩
  have hrightEntry := C.target_before_left (C.leftSwitch - 2)
    (by omega) hrightEven
  have horders : b.order (0 : Fin (n + 2)) = b.order right := by
    rw [← b.orderSequence_entryOrZero_eq_order (0 : Fin (n + 2)),
      ← b.orderSequence_entryOrZero_eq_order right]
    exact hzeroEntry.trans hrightEntry.symm
  have hinterval := b.beli2019Lemma66_i (0 : Fin (n + 2)) right
    (Fin.zero_le _) (by
      simpa only [right, Fin.val_zero, Nat.sub_zero] using hrightEven) horders
  let gap : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  have hgapUpper : b.orderGap gap ≤
      2 * (ramificationIndex K : Int) :=
    hinterval.gap_le gap (by
      change 0 ≤ i.val - 2
      omega) (by
        change i.val - 2 < C.leftSwitch - 2
        omega)
  have halphaLower : 2 * (ramificationIndex K : ℚ) ≤
      b.alphaValue gap := by
    apply b.alphaValue_ge_twoE_of_gt_twoE_sub_one gap
    simpa only [gap] using halpha
  have hgapLower : 2 * (ramificationIndex K : Int) ≤ b.orderGap gap :=
    b.orderGap_ge_twoE_of_alphaValue_ge_twoE_early gap halphaLower
  simpa only [gap] using (show b.orderGap gap =
    2 * (ramificationIndex K : Int) by omega)

/-- An even type-I early trigger can occur only at the first canonical
switch. -/
theorem lemma79Central_typeIEarly_even_eq_leftSwitch
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hearly : i.val ≤ C.leftSwitch) (hiEven : Even i.val)
    (hcross : c.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ <
      b.order ⟨i.val, i.lt_large⟩) :
    i.val = C.leftSwitch := by
  by_contra hne
  have hiLeft : i.val < C.leftSwitch := lt_of_le_of_ne hearly hne
  have hleftPos : 0 < C.leftSwitch := by omega
  have hiPreviousEven : Even (i.val - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hsourceZero := C.source_to_anchor 0 (Nat.zero_le D.anchor)
    ⟨0, by omega⟩
  have htargetZero := C.target_before_left 0 hleftPos ⟨0, by omega⟩
  have htargetCurrent := C.target_before_left i.val hiLeft hiEven
  have hbZero : b.order 0 = a.order 0 + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    calc
      b.orderSequence.entryOrZero 0 =
          a.orderSequence.entryOrZero D.anchor + 1 := htargetZero
      _ = a.orderSequence.entryOrZero 0 + 1 := by rw [hsourceZero]
  have hbCurrent : b.order ⟨i.val, i.lt_large⟩ = b.order 0 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact htargetCurrent.trans htargetZero.symm
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  change a.order 0 + 1 ≤ c.order 0 at hnormOrder
  have hcMonotoneRaw := c.orderSequence.entryOrZero_le_of_evenGap
    0 (i.val - 2) (Nat.zero_le _) (by
      have := i.lt_large
      omega) hiPreviousEven
  have hcMonotone : c.order 0 ≤ c.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ := by
    rw [← c.orderSequence_entryOrZero_eq_order,
      ← c.orderSequence_entryOrZero_eq_order]
    exact hcMonotoneRaw
  rw [hbCurrent, hbZero] at hcross
  omega

/-- At the first type-I switch, the target order rises by one while the
first and the `(i-2)`-nd comparison orders both equal the old target
order. -/
theorem lemma79Central_typeIEarly_leftSwitch_baseOrders
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch)
    (hcross : c.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ < b.order ⟨i.val, i.lt_large⟩) :
    b.order ⟨i.val, i.lt_large⟩ = b.order 0 + 1 ∧
      c.order 0 = b.order 0 ∧
      c.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ = b.order 0 := by
  have hleftPos : 0 < C.leftSwitch := by
    have := i.one_lt
    omega
  have hiEven : Even i.val := by simpa only [hleft] using C.left_even
  have hiPreviousEven : Even (i.val - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hsourceZero := C.source_to_anchor 0 (Nat.zero_le D.anchor)
    ⟨0, by omega⟩
  have htargetZero := C.target_before_left 0 hleftPos ⟨0, by omega⟩
  have htargetCurrent := C.target_from_left C.leftSwitch le_rfl
    C.left_le_anchor C.left_even
  have htargetCurrent' : b.orderSequence.entryOrZero i.val =
      a.orderSequence.entryOrZero D.anchor + 2 := by
    simpa only [hleft] using htargetCurrent
  have hbZero : b.order 0 = a.order 0 + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    calc
      b.orderSequence.entryOrZero 0 =
          a.orderSequence.entryOrZero D.anchor + 1 := htargetZero
      _ = a.orderSequence.entryOrZero 0 + 1 := by rw [hsourceZero]
  have hbCurrent : b.order ⟨i.val, i.lt_large⟩ = b.order 0 + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    change b.orderSequence.entryOrZero i.val =
      b.orderSequence.entryOrZero 0 + 1
    omega
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  change a.order 0 + 1 ≤ c.order 0 at hnormOrder
  have hcMonotoneRaw := c.orderSequence.entryOrZero_le_of_evenGap
    0 (i.val - 2) (Nat.zero_le _) (by
      have := i.lt_large
      omega) hiPreviousEven
  have hcMonotone : c.order 0 ≤ c.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ := by
    rw [← c.orderSequence_entryOrZero_eq_order,
      ← c.orderSequence_entryOrZero_eq_order]
    exact hcMonotoneRaw
  refine ⟨hbCurrent, ?_, ?_⟩
  · omega
  · omega

/-- An alpha above `2e - 1` at the first type-I switch forces its unique
odd gap to be `2e + 1`. -/
theorem lemma79Central_typeIEarly_leftSwitch_gap_eq_twoE_add_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch)
    (halpha : 2 * (ramificationIndex K : ℚ) - 1 <
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩) :
    b.orderGap ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ = 2 * (ramificationIndex K : Int) + 1 := by
  have hleftPos : 0 < C.leftSwitch := by
    have := i.one_lt
    omega
  let gap : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  have halphaLower : 2 * (ramificationIndex K : ℚ) ≤
      b.alphaValue gap := by
    apply b.alphaValue_ge_twoE_of_gt_twoE_sub_one gap
    simpa only [gap] using halpha
  have hgapLower : 2 * (ramificationIndex K : Int) ≤ b.orderGap gap :=
    b.orderGap_ge_twoE_of_alphaValue_ge_twoE_early gap halphaLower
  have hgapUpper : b.orderGap gap ≤
      2 * (ramificationIndex K : Int) + 1 := by
    simpa only [gap, hleft] using
      lemma79_typeI_leftSwitch_gap_le_twoE_add_one a b D C hleftPos
  have hgapOdd : Odd (b.orderGap gap) := by
    simpa only [gap, hleft] using
      lemma76_leftSwitch_gap_odd a b D C hfirst hleftPos
  rcases hgapOdd with ⟨z, hz⟩
  simpa only [gap] using (show b.orderGap gap =
    2 * (ramificationIndex K : Int) + 1 by omega)

/-- The switch gap gives the low endpoint of the longer target tower. -/
theorem lemma79Central_typeIEarly_leftSwitch_targetLowOrder
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch)
    (hgap : b.orderGap ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ = 2 * (ramificationIndex K : Int) + 1) :
    b.order ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ = b.order 0 - 2 * (ramificationIndex K : Int) := by
  have hleftPos : 0 < C.leftSwitch := by
    have := i.one_lt
    omega
  have htargetZero := C.target_before_left 0 hleftPos ⟨0, by omega⟩
  have htargetCurrent := C.target_from_left C.leftSwitch le_rfl
    C.left_le_anchor C.left_even
  have htargetCurrent' : b.orderSequence.entryOrZero i.val =
      a.orderSequence.entryOrZero D.anchor + 2 := by
    simpa only [hleft] using htargetCurrent
  have hbCurrent : b.order ⟨i.val, i.lt_large⟩ = b.order 0 + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    change b.orderSequence.entryOrZero i.val =
      b.orderSequence.entryOrZero 0 + 1
    omega
  let gap : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  have hsucc : gap.succ = (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [gap, Fin.val_succ]
    omega
  have hcast : gap.castSucc = (⟨i.val - 1, by
      have := i.lt_large
      omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  unfold orderGap at hgap
  rw [hsucc, hcast, hbCurrent] at hgap
  omega

/-- The primary candidate for `B_(i-1)`, followed by the right alpha cap,
is the endpoint-average upper bound used in cases 1 and 5:

`B_(i-1) ≤ S_(i-1) - (T_(i-2) + T_(i-1))/2 + e`.
-/
theorem lemma79Central_previousAlpha_le_endpointAverage
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hiThree : 3 ≤ i.val) :
    (b.representationAlphaValue c i.previous : WithTop ℚ) ≤
      (((b.order ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : ℚ) -
          ((c.order ⟨i.val - 3, by
              have := i.lt_large
              omega⟩ : ℚ) +
            (c.order ⟨i.val - 2, by
              have := i.lt_large
              omega⟩ : ℚ)) / 2 +
            (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
  have hiBound := i.lt_large
  let sourcePrevious : Fin (n + 2) := ⟨i.val - 1, by omega⟩
  let comparisonFar : Fin (n + 2) := ⟨i.val - 3, by omega⟩
  let comparisonNear : Fin (n + 2) := ⟨i.val - 2, by omega⟩
  let p : Fin (n + 1) := ⟨i.val - 3, by omega⟩
  have hpSucc : p.succ = comparisonNear := by
    apply Fin.ext
    simp only [p, comparisonNear, Fin.val_succ]
    omega
  have hpCast : p.castSucc = comparisonFar := by
    apply Fin.ext
    rfl
  have hcap := b.truncatedPrefixDefect_le_rightCap c (-1)
    i.val (i.val - 2)
  rw [c.prefixAlphaCap_of_internal (i := i.val - 2) (by omega) (by
    have := i.lt_large
    omega)] at hcap
  have hpAlpha : (⟨i.val - 2 - 1, by
      have := i.lt_large
      omega⟩ : Fin (n + 1)) = p := by
    apply Fin.ext
    simp only [p]
    omega
  rw [hpAlpha] at hcap
  have halphaHalf : (c.alphaValue p : WithTop ℚ) ≤
      (c.halfGapValue p : WithTop ℚ) := by
    exact_mod_cast c.alphaValue_le_halfGapValue p
  have hdefectHalf : b.truncatedPrefixDefect c (-1)
      i.val (i.val - 2) ≤ (c.halfGapValue p : WithTop ℚ) :=
    hcap.trans halphaHalf
  have hprimary := b.representationAlpha_le_primary c i.previous
  have hprimaryBound : b.representationPrimaryDefect c i.previous ≤
      ((((b.order sourcePrevious - c.order comparisonNear : Int) : ℚ) :
          WithTop ℚ) +
        (c.halfGapValue p : WithTop ℚ)) := by
    simp only [representationPrimaryDefect,
      CentralRepresentationIndex.previous, sourcePrevious, comparisonNear,
      show i.val - 1 + 1 = i.val by omega,
      show i.val - 1 - 1 = i.val - 2 by omega]
    gcongr
  have hhalf : c.halfGapValue p =
      ((c.order comparisonNear : ℚ) -
          (c.order comparisonFar : ℚ)) / 2 +
        (ramificationIndex K : ℚ) := by
    unfold halfGapValue orderGap
    rw [hpSucc, hpCast]
    push_cast
    ring
  have hshift :
      ((b.order sourcePrevious - c.order comparisonNear : Int) : ℚ) =
        (b.order sourcePrevious : ℚ) -
          (c.order comparisonNear : ℚ) := by
    push_cast
    rfl
  have hresult : (b.representationAlphaValue c i.previous : WithTop ℚ) ≤
      (((b.order sourcePrevious : ℚ) -
          ((c.order comparisonFar : ℚ) +
            (c.order comparisonNear : ℚ)) / 2 +
          (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    calc
      (b.representationAlphaValue c i.previous : WithTop ℚ) =
          b.representationAlpha c i.previous := by
        rw [b.coe_representationAlphaValue c i.previous]
      _ ≤ b.representationPrimaryDefect c i.previous := hprimary
      _ ≤ ((((b.order sourcePrevious - c.order comparisonNear : Int) : ℚ) :
            WithTop ℚ) + (c.halfGapValue p : WithTop ℚ)) := hprimaryBound
      _ = (((b.order sourcePrevious : ℚ) -
            ((c.order comparisonFar : ℚ) +
              (c.order comparisonNear : ℚ)) / 2 +
            (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
        rw [hshift, hhalf]
        change ((((b.order sourcePrevious : ℚ) -
              (c.order comparisonNear : ℚ)) +
            (((c.order comparisonNear : ℚ) -
                (c.order comparisonFar : ℚ)) / 2 +
              (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) = _
        congr 1
        ring
  simpa only [sourcePrevious, comparisonFar, comparisonNear] using hresult

/-- The first alternative supplied by Lemma 2.18 is the strict adjacent
target-alpha sum `beta_(i-1) + beta_i > 2e`.  This named form keeps the
subsequent case analysis independent of the capped-defect encoding. -/
theorem lemma79Central_firstAlternative_targetAlphaSum
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (hdefect : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hprevious :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.representationAlpha c i.previous) :
    2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ +
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ := by
  have hcomparison : b.representationAlpha c i.previous ≤
      b.prefixAlphaCap (i.val - 1) := by
    calc
      b.representationAlpha c i.previous =
          b.representationAlphaValue c i.previous := by
        rw [b.coe_representationAlphaValue c i.previous]
      _ ≤ b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1) := by
        simpa only [CentralRepresentationIndex.previous] using
          hdefect i.previous
      _ ≤ b.prefixAlphaCap (i.val - 1) :=
        b.truncatedPrefixDefect_le_leftCap c 1
          (i.val - 1) (i.val - 1)
  have hcap := hprevious.trans_le (add_le_add le_rfl hcomparison)
  rw [b.prefixAlphaCap_of_internal (by
        have := i.one_lt
        omega) i.lt_large,
    b.prefixAlphaCap_of_internal (by
        have := i.one_lt
        omega) (by
        have := i.lt_large
        omega)] at hcap
  have hsum : 2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ +
      b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ := by
    exact_mod_cast hcap
  simpa only [add_comm] using hsum

/-- Before capping the comparison defect, the first Lemma 2.18 alternative
also gives the lower bound on `B_(i-1)` used in the endpoint arithmetic. -/
theorem lemma79Central_firstAlternative_previousAlphaLower
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hprevious :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.representationAlpha c i.previous) :
    2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ + b.representationAlphaValue c i.previous := by
  rw [b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) i.lt_large,
    ← b.coe_representationAlphaValue c i.previous] at hprevious
  exact_mod_cast hprevious

end BONG.GoodBONG

end Bong
