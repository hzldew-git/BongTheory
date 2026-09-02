/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006SectionTwo
import Bong.Bong.Beli2009AlphaMonotonicity
import Bong.Bong.BeliUniversalAlpha
import Bong.Bong.Beli2019MainTheorem
import Bong.Bong.BinaryEndpointModel
import Bong.Bong.Beli2019Lemma75
import Bong.Bong.Beli2019Lemma75PrefixClass
import Bong.Bong.BeliCorollary44LawsProof
import Bong.Bong.AlternatingEndpointOddNormalForm

/-!
# He--Hu (2024), Section 2

This file gives direct Lean endpoints for the reusable results in Section 2
of Zilong He and Yong Hu, *On n-universal quadratic forms over dyadic local
fields*, Sci. China Math. 67 (2024), 1481--1506.

The paper uses one-based indices.  A Lean index `i : Fin n` below denotes the
paper index `i + 1`.  In particular, `a.orderGap i`, `a.alphaValue i`, and
`a.heHuAdjacentCappedDefect i` are respectively
`R_(i+2) - R_(i+1)`, `alpha_(i+1)`, and
`d[-a_(i+1) a_(i+2)]`.
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

namespace BONG.OrthogonalBasisData

/-- The two displayed numerical conditions (2.2)--(2.3) in He--Hu,
Lemma 2.2.  The absolute-defect predicate is precisely
`ord(-a) + d(-a) >= 0`, expressed without subtraction in `Nat.infinity`. -/
def HeHuGoodBONGCriteria {n : Nat} (X : OrthogonalBasisData q n) : Prop :=
  X.HasWeakTwoStepOrder ∧
    ∀ (i : Fin n) (hi : i.1 + 1 < n),
      0 ≤ ordUnit K (X.adjacentParameter i hi) +
          2 * (ramificationIndex K : Int) ∧
        HasNonnegativeAbsoluteQuadraticDefect
          (-(X.adjacentParameter i hi))

/-- He--Hu, Lemma 2.2: the explicit order-and-defect criterion for an
orthogonal basis to be a good BONG of a lattice. -/
theorem heHu2022Lemma22 {n : Nat} (X : OrthogonalBasisData q n) :
    X.HasGoodRealization ↔ X.HeHuGoodBONGCriteria := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  rw [X.hasGoodRealization_iff_beli2006Criteria]
  unfold SatisfiesGoodBONGCriteria HeHuGoodBONGCriteria
  apply and_congr Iff.rfl
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  exact isBinaryParameterAdmissible_iff_order_add_two_e_and_defect
    (X.adjacentParameter i hi)

end BONG.OrthogonalBasisData

namespace BONG.GoodBONG

noncomputable local instance heHuDiscriminantClassLaws :
    DyadicDiscriminantClassLaws K :=
  dyadicDiscriminantClassLawsProved

/-- Definition 2.4: He--Hu's `alpha_i`, in zero-based indexing. -/
noncomputable abbrev heHuAlpha {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n) : WithTop ℚ :=
  a.alpha i

/-- Definition 2.4 and equation (2.5): `d[c a_i ... a_j]`, retaining
the source convention that missing endpoint alpha caps are ignored. -/
noncomputable abbrev heHuTruncatedSegmentDefect {n : Nat}
    (a : GoodBONG q L (n + 1)) (c : Kˣ) (i j : Nat) : WithTop ℚ :=
  a.truncatedSegmentDefect c i j

/-- Definition 2.4 and equation (2.5): the capped adjacent defect
`d[-a_i a_(i+1)]`, with `i` zero-based. -/
noncomputable def heHuAdjacentCappedDefect {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n) : WithTop ℚ :=
  a.truncatedPrefixDefect a (-1) i.val (i.val + 2)

/-- Corollary 2.3(i): an odd adjacent gap is positive, equivalently every
nonpositive adjacent gap is even. -/
theorem heHu2022Corollary23i {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n) :
    (Odd (a.orderGap i) → 0 < a.orderGap i) ∧
      (a.orderGap i ≤ 0 → Even (a.orderGap i)) := by
  constructor
  · intro hodd
    have hadmissible :=
      a.toBONG.adjacentParameter_isBinaryParameterAdmissible
        i.castSucc (Nat.add_lt_add_right i.isLt 1)
    have hnonnegative := hadmissible.ordUnit_nonneg_of_odd (by
      rw [a.toBONG.ordUnit_adjacentParameter i.castSucc
        (Nat.add_lt_add_right i.isLt 1)]
      exact hodd)
    rw [a.toBONG.ordUnit_adjacentParameter i.castSucc
      (Nat.add_lt_add_right i.isLt 1)] at hnonnegative
    have hindex :
        (⟨i.castSucc.val + 1, by
          change i.val + 1 < n + 1
          exact Nat.add_lt_add_right i.isLt 1⟩ : Fin (n + 1)) =
          i.succ := by
      apply Fin.ext
      rfl
    rw [hindex] at hnonnegative
    have hnonnegative' : 0 ≤ a.orderGap i := by
      exact hnonnegative
    have hne : a.orderGap i ≠ 0 := by
      intro hzero
      rw [hzero] at hodd
      exact (Int.not_odd_iff_even.mpr Even.zero) hodd
    exact lt_of_le_of_ne hnonnegative' hne.symm
  · exact a.orderGap_even_of_nonpositive i

/-- Corollary 2.3(ii), including the raw adjacent-defect bound and the two
concrete endpoint lattice models.  The two branches are the coordinate-free
versions of the paper's scaled `A(0,0)` and `A(2,2rho)` lattices. -/
structure HeHuCorollary23iiConclusions [DyadicDiscriminantClassLaws K]
    {n : Nat} (a : GoodBONG q L (n + 1)) (i : Fin n) : Prop where
  rawDefectLower :
    ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤ a.adjacentDefect i
  endpointModels :
    let w := a.toBONG.segmentWitness i.val 2 (by omega)
    (∃ s : Kˣ, IsValuationUnit K (s : K) ∧
        Lattice.IsIsometric
          (q.restrict w.carrier w.nondegenerate)
          (w.bong.squareClassRepresentativeModelSpace
            (negativeQuarterUnit K) s)
          w.lattice (binaryModelLattice (K := K))) ∨
      (∃ s : Kˣ, IsValuationUnit K (s : K) ∧
        Lattice.IsIsometric
          (q.restrict w.carrier w.nondegenerate)
          (w.bong.squareClassRepresentativeModelSpace
            (negativeQuarterUnit K *
              (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit) s)
          w.lattice (binaryModelLattice (K := K)))

/-- He--Hu, Corollary 2.3(ii). -/
theorem heHu2022Corollary23ii [DyadicDiscriminantClassLaws K]
    {n : Nat} (a : GoodBONG q L (n + 1)) (i : Fin n)
    (hgap : a.orderGap i =
      -(2 * (ramificationIndex K : Int))) :
    HeHuCorollary23iiConclusions a i := by
  let w := a.toBONG.segmentWitness i.val 2 (by omega)
  have hraw := a.zero_le_orderGap_add_adjacentDefect i
  have hraw' :
      ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
        a.adjacentDefect i := by
    rw [hgap] at hraw
    apply (WithTop.add_le_add_iff_left
      (x := ((-(2 * ramificationIndex K : ℚ) : ℚ) : WithTop ℚ))
      WithTop.coe_ne_top).mp
    have hzero :
        ((-(2 * ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) +
            ((2 * ramificationIndex K : ℚ) : WithTop ℚ) = 0 := by
      rw [← WithTop.coe_add]
      norm_num
    rw [hzero]
    norm_num at hraw ⊢
    exact hraw
  have hzero : w.sourceIndex 0 = i.castSucc := by
    apply Fin.ext
    rfl
  have hone : w.sourceIndex 1 = i.succ := by
    apply Fin.ext
    rfl
  have hmodelGap : w.bong.binaryOrderGap =
      -(2 * (ramificationIndex K : Int)) := by
    change w.bong.order 1 - w.bong.order 0 = _
    rw [w.order_eq, w.order_eq, hzero, hone]
    exact hgap
  refine ⟨hraw', ?_⟩
  exact w.bong.endpointModel_cases hmodelGap

/-- Proposition 2.5, with the paper's two conclusions bundled together. -/
structure HeHuProposition25Conclusions {n : Nat}
    (a : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) : Prop where
  leftEndpoint_le : a.alphaLeftEndpoint i ≤ a.alphaLeftEndpoint j
  rightEndpoint_le : a.alphaRightEndpoint j ≤ a.alphaRightEndpoint i
  constantSum : a.adjacentOrderSum i = a.adjacentOrderSum j →
    ∀ k : Fin (n + 1), i ≤ k → k ≤ j →
      a.alphaLeftEndpoint k = a.alphaLeftEndpoint i

/-- He--Hu, Proposition 2.5. -/
theorem heHu2022Proposition25 {n : Nat}
    (a : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) (hij : i ≤ j) :
    HeHuProposition25Conclusions a i j := by
  refine
    { leftEndpoint_le := a.alphaLeftEndpoint_monotone hij
      rightEndpoint_le := a.alphaRightEndpoint_antitone hij
      constantSum := ?_ }
  intro hsum
  exact (a.beli2009Corollary23 i j hij hsum).leftEndpoint_eq

/-- Proposition 2.6(i)--(vii).  The clauses retain the paper's order:
arithmetic shape and alpha zero; comparison with `2e`; the lower bound and
equality cases; the half-gap cases; the alpha-zero defect bound; and the two
alpha-one assertions. -/
structure HeHuProposition26Conclusions {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n) : Prop where
  arithmeticShape :
    (0 ≤ a.alphaValue i ∧
        a.alphaValue i ≤ 2 * (ramificationIndex K : ℚ) ∧
        IsRationalInteger (a.alphaValue i)) ∨
      (2 * (ramificationIndex K : ℚ) < a.alphaValue i ∧
        IsRationalHalfInteger (a.alphaValue i))
  alphaZero : a.alphaValue i = 0 ↔
    a.orderGap i = -(2 * (ramificationIndex K : Int))
  compareTwoE :
    (a.alphaValue i < 2 * (ramificationIndex K : ℚ) ↔
      a.orderGap i < 2 * (ramificationIndex K : Int)) ∧
    (a.alphaValue i = 2 * (ramificationIndex K : ℚ) ↔
      a.orderGap i = 2 * (ramificationIndex K : Int)) ∧
    (2 * (ramificationIndex K : ℚ) < a.alphaValue i ↔
      2 * (ramificationIndex K : Int) < a.orderGap i)
  lowerBound (hgap : a.orderGap i ≤
      2 * (ramificationIndex K : Int)) :
    (a.orderGap i : ℚ) ≤ a.alphaValue i ∧
      (a.alphaValue i = (a.orderGap i : ℚ) ↔
        a.orderGap i = 2 * (ramificationIndex K : Int) ∨
          Odd (a.orderGap i))
  halfGap (hcase :
      2 * (ramificationIndex K : Int) ≤ a.orderGap i ∨
      a.orderGap i = -(2 * (ramificationIndex K : Int)) ∨
      a.orderGap i = 2 - 2 * (ramificationIndex K : Int) ∨
      a.orderGap i = 2 * (ramificationIndex K : Int) - 2) :
    a.alphaValue i = a.halfGapValue i
  alphaZeroDefect (halpha : a.alphaValue i = 0) :
    ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.heHuAdjacentCappedDefect i
  alphaOne (halpha : a.alphaValue i = 1) :
    (a.orderGap i = 1 ∨
      (Even (a.orderGap i) ∧
        2 - 2 * (ramificationIndex K : Int) ≤ a.orderGap i ∧
        a.orderGap i ≤ 0)) ∧
    ((((1 : ℚ) - (a.orderGap i : ℚ)) : ℚ) : WithTop ℚ) ≤
      a.heHuAdjacentCappedDefect i ∧
    (a.orderGap i ≠ 2 - 2 * (ramificationIndex K : Int) →
      a.heHuAdjacentCappedDefect i =
        ((((1 : ℚ) - (a.orderGap i : ℚ)) : ℚ) : WithTop ℚ))
  alphaOneIff (hlower :
      2 - 2 * (ramificationIndex K : Int) < a.orderGap i)
      (hupper : a.orderGap i ≤ 0) :
    a.alphaValue i = 1 ↔
      a.heHuAdjacentCappedDefect i =
        ((((1 : ℚ) - (a.orderGap i : ℚ)) : ℚ) : WithTop ℚ)

/-- He--Hu, Proposition 2.6. -/
theorem heHu2022Proposition26 {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n) :
    HeHuProposition26Conclusions a i := by
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  letI : Beli2009AlphaParityLaws.{u, v} K :=
    beliUniversalAlphaParityLaws
  refine
    { arithmeticShape := a.beli2009Corollary28_iii i
      alphaZero := (a.beli2009Lemma27_i i).2
      compareTwoE := a.beli2009Corollary28_ii i
      lowerBound := a.beli2009Lemma27_iii i
      halfGap := a.beli2009Corollary29_i i
      alphaZeroDefect := ?_
      alphaOne := ?_
      alphaOneIff := ?_ }
  · intro halpha
    simpa only [heHuAdjacentCappedDefect] using
      a.cappedAdjacent_ge_two_e_of_alphaValue_eq_zero i halpha
  · intro halpha
    have h := a.alphaValue_eq_one_consequences i halpha
    exact ⟨h.2.1, by simpa only [heHuAdjacentCappedDefect] using h.2.2⟩
  · intro hlower hupper
    simpa only [heHuAdjacentCappedDefect] using
      a.alphaValue_eq_one_iff_cappedAdjacent i hlower hupper

/-- Proposition 2.7(i), with paper-odd indices represented by even
zero-based indices and paper-even indices by odd zero-based indices. -/
structure HeHuProposition27iConclusions {n : Nat}
    (a : GoodBONG q L (n + 1)) : Prop where
  oddIndexed (i j : Fin (n + 1)) (hij : i ≤ j)
      (hi : Even i.val) (hj : Even j.val) :
    0 ≤ a.order i ∧ a.order i ≤ a.order j
  evenIndexed (i j : Fin (n + 1)) (hij : i ≤ j)
      (hi : Odd i.val) (hj : Odd j.val) :
    -(2 * (ramificationIndex K : Int)) ≤ a.order i ∧
      a.order i ≤ a.order j

/-- He--Hu, Proposition 2.7(i). -/
theorem heHu2022Proposition27i {n : Nat}
    (a : GoodBONG q L (n + 1)) (hIntegral : Lattice.IsIntegral q L) :
    HeHuProposition27iConclusions a := by
  have hzero : 0 ≤ a.order (0 : Fin (n + 1)) :=
    (a.toBONG.beliUniversalLemma22).1 hIntegral
  refine ⟨?_, ?_⟩
  · intro i j hij hi hj
    have hzi : Even (i.val - 0) := by simpa using hi
    have hijEven : Even (j.val - i.val) := by
      rcases hi with ⟨p, hp⟩
      rcases hj with ⟨r, hr⟩
      refine ⟨r - p, ?_⟩
      omega
    constructor
    · exact hzero.trans (a.order_le_of_le_of_even_sub 0 i
        (Fin.zero_le i) hzi)
    · exact a.order_le_of_le_of_even_sub i j hij hijEven
  · intro i j hij hi hj
    have hijEven : Even (j.val - i.val) := by
      rcases hi with ⟨p, hp⟩
      rcases hj with ⟨r, hr⟩
      refine ⟨r - p, ?_⟩
      omega
    have hiPositive : 0 < i.val := by
      rcases hi with ⟨p, hp⟩
      omega
    let previous : Fin (n + 1) := ⟨i.val - 1, by omega⟩
    let gapIndex : Fin n := ⟨i.val - 1, by omega⟩
    have hpreviousEven : Even previous.val := by
      rcases hi with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      simp only [previous]
      omega
    have hpreviousNonnegative : 0 ≤ a.order previous :=
      hzero.trans (a.order_le_of_le_of_even_sub 0 previous
        (Fin.zero_le previous) (by simpa using hpreviousEven))
    have hgap := a.orderGap_ge_neg_two_mul_e gapIndex
    have hindices :
        gapIndex.castSucc = previous ∧ gapIndex.succ = i := by
      constructor
      · apply Fin.ext
        rfl
      · apply Fin.ext
        simp only [Fin.val_succ, gapIndex]
        omega
    rcases hindices with ⟨hleft, hright⟩
    unfold orderGap at hgap
    rw [hleft, hright] at hgap
    constructor
    · omega
    · exact a.order_le_of_le_of_even_sub i j hij hijEven

/-- Proposition 2.7(ii), expressed with zero-based parity. -/
structure HeHuProposition27iiConclusions {n : Nat}
    (a : GoodBONG q L (n + 1)) (j : Fin (n + 1)) : Prop where
  precedingPaperOddOrders (i : Fin (n + 1)) (hij : i ≤ j)
      (hi : Even i.val) : a.order i = 0
  precedingOrdersEven (i : Fin (n + 1)) (hij : i ≤ j) :
    Even (a.order i)

/-- He--Hu, Proposition 2.7(ii). -/
theorem heHu2022Proposition27ii {n : Nat}
    (a : GoodBONG q L (n + 1)) (hIntegral : Lattice.IsIntegral q L)
    (j : Fin (n + 1)) (hj : Even j.val) (hjOrder : a.order j = 0) :
    HeHuProposition27iiConclusions a j := by
  let C := a.heHu2022Proposition27i hIntegral
  have hzeroOrders (i : Fin (n + 1)) (hij : i ≤ j)
      (hi : Even i.val) : a.order i = 0 := by
    have h := C.oddIndexed i j hij hi hj
    omega
  refine ⟨hzeroOrders, ?_⟩
  intro i hij
  rcases Int.even_or_odd (a.order i) with horderEven | horderOdd
  · exact horderEven
  · rcases Nat.even_or_odd i.val with hiEven | hiOdd
    · have hiZero := hzeroOrders i hij hiEven
      rw [hiZero] at horderOdd
      exact (Int.not_odd_iff_even.mpr Even.zero horderOdd).elim
    · have hiPositive : 0 < i.val := by
        rcases hiOdd with ⟨p, hp⟩
        omega
      have hiStrict : i.val < j.val := by
        have hle : i.val ≤ j.val := hij
        rcases hiOdd with ⟨p, hp⟩
        rcases hj with ⟨r, hr⟩
        omega
      let previous : Fin (n + 1) := ⟨i.val - 1, by omega⟩
      let next : Fin (n + 1) := ⟨i.val + 1, by omega⟩
      let leftGap : Fin n := ⟨i.val - 1, by omega⟩
      let rightGap : Fin n := ⟨i.val, by omega⟩
      have hpreviousEven : Even previous.val := by
        rcases hiOdd with ⟨p, hp⟩
        refine ⟨p, ?_⟩
        simp only [previous]
        omega
      have hnextEven : Even next.val := by
        rcases hiOdd with ⟨p, hp⟩
        refine ⟨p + 1, ?_⟩
        simp only [next]
        omega
      have hpreviousLe : previous ≤ j := by
        exact Fin.mk_le_mk.mpr (by omega)
      have hnextLe : next ≤ j := by
        exact Fin.mk_le_mk.mpr (by omega)
      have hpreviousZero := hzeroOrders previous hpreviousLe hpreviousEven
      have hnextZero := hzeroOrders next hnextLe hnextEven
      have hleftIndices :
          leftGap.castSucc = previous ∧ leftGap.succ = i := by
        constructor
        · apply Fin.ext
          rfl
        · apply Fin.ext
          simp only [Fin.val_succ, leftGap]
          omega
      have hrightIndices :
          rightGap.castSucc = i ∧ rightGap.succ = next := by
        constructor <;> apply Fin.ext <;> rfl
      have hleftGap : a.orderGap leftGap = a.order i := by
        unfold orderGap
        rw [hleftIndices.1, hleftIndices.2, hpreviousZero]
        omega
      have hrightGap : a.orderGap rightGap = -a.order i := by
        unfold orderGap
        rw [hrightIndices.1, hrightIndices.2, hnextZero]
        omega
      have hleftPositive : 0 < a.orderGap leftGap :=
        (a.heHu2022Corollary23i leftGap).1 (by
          rw [hleftGap]
          exact horderOdd)
      have hrightPositive : 0 < a.orderGap rightGap :=
        (a.heHu2022Corollary23i rightGap).1 (by
          rw [hrightGap]
          exact horderOdd.neg)
      rw [hleftGap] at hleftPositive
      rw [hrightGap] at hrightPositive
      omega

/-- Proposition 2.7(iii)--(iv).  Besides the displayed order and defect
claims, `alternatingDecomposition` records actual orthogonal binary blocks
and their two endpoint-space models.  `prefixEndpointClass` is the invariant
form of the paper's `H^(j/2)` versus
`H^((j-2)/2) ⊥ [1,-Delta]` alternative. -/
structure HeHuProposition27iiiivConclusions {n : Nat}
    (a : GoodBONG q L (n + 2)) (j : Fin (n + 2)) : Prop where
  pairOrdersAndDefects (i : Fin (n + 2)) (hij : i ≤ j)
      (hi : Odd i.val) :
    let gap : Fin (n + 1) := ⟨i.val - 1, by omega⟩
    let previous : Fin (n + 2) := ⟨i.val - 1, by omega⟩
    a.order previous = 0 ∧
      a.order i = -(2 * (ramificationIndex K : Int)) ∧
      ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
        a.heHuAdjacentCappedDefect gap ∧
      ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
        a.adjacentDefect gap
  alternatingPrefixDefect :
    let lastGap : Fin (n + 1) := ⟨j.val - 1, by omega⟩
    ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect a
        ((-1) ^ ((lastGap.val + 2) / 2)) 0 (lastGap.val + 2)
  alternatingDecomposition :
    let first : Fin (n + 1) := ⟨0, by omega⟩
    let lastGap : Fin (n + 1) := ⟨j.val - 1, by omega⟩
    Lemma75Consequences a first lastGap 0
  prefixEndpointClass :
    ∃ pairs : Nat, 2 * pairs = j.val + 1 ∧
      (IsSquare (a.toBONG.signedEvenPrefixProduct pairs) ∨
        IsSquare (a.toBONG.signedEvenPrefixProduct pairs *
          (heHuDiscriminantClassLaws (K := K)).discriminantUnit))

/-- He--Hu, Proposition 2.7(iii)--(iv). -/
theorem heHu2022Proposition27iiiiv {n : Nat}
    (a : GoodBONG q L (n + 2)) (hIntegral : Lattice.IsIntegral q L)
    (j : Fin (n + 2)) (hj : Odd j.val)
    (hjOrder : a.order j = -(2 * (ramificationIndex K : Int))) :
    HeHuProposition27iiiivConclusions a j := by
  have hjPositive : 0 < j.val := by
    rcases hj with ⟨p, hp⟩
    omega
  let first : Fin (n + 1) := ⟨0, by omega⟩
  let lastGap : Fin (n + 1) := ⟨j.val - 1, by omega⟩
  let previous : Fin (n + 2) := ⟨j.val - 1, by omega⟩
  have hlastEven : Even lastGap.val := by
    rcases hj with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    simp only [lastGap]
    omega
  have hlastGapIndices :
      lastGap.castSucc = previous ∧ lastGap.succ = j := by
    constructor
    · apply Fin.ext
      rfl
    · apply Fin.ext
      simp only [Fin.val_succ, lastGap]
      omega
  have hpreviousNonnegative : 0 ≤ a.order previous := by
    let C := a.heHu2022Proposition27i hIntegral
    have h := C.oddIndexed 0 previous (Fin.zero_le previous)
      Even.zero (by simpa [previous, lastGap] using hlastEven)
    exact h.1.trans h.2
  have hlastGapLower := a.orderGap_ge_neg_two_mul_e lastGap
  unfold orderGap at hlastGapLower
  rw [hlastGapIndices.1, hlastGapIndices.2, hjOrder] at hlastGapLower
  have hpreviousOrder : a.order previous = 0 := by omega
  have hfirstOrder : a.order (0 : Fin (n + 2)) = 0 := by
    let C := a.heHu2022Proposition27i hIntegral
    have h := C.oddIndexed 0 previous (Fin.zero_le previous)
      Even.zero (by simpa [previous, lastGap] using hlastEven)
    omega
  have hfirstCast : first.castSucc = (0 : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hlastTerminal :
      a.order lastGap.succ = 0 - 2 * (ramificationIndex K : Int) := by
    rw [hlastGapIndices.2, hjOrder]
    ring
  have hfirstLe : first ≤ lastGap := Fin.zero_le lastGap
  have hsegmentEven : Even (lastGap.val - first.val) := by
    simpa only [first, Fin.val_mk, Nat.sub_zero] using hlastEven
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  let D := a.beli2019Lemma75 first lastGap 0 hfirstLe hsegmentEven
    (by simpa only [hfirstCast] using hfirstOrder) hlastTerminal
  refine ⟨?_, D.arithmetic.defect_ge_two_mul_e, D, ?_⟩
  · intro i hij hi
    have hiPositive : 0 < i.val := by
      rcases hi with ⟨p, hp⟩
      omega
    let gap : Fin (n + 1) := ⟨i.val - 1, by omega⟩
    let iprevious : Fin (n + 2) := ⟨i.val - 1, by omega⟩
    have hgapEven : Even (gap.val - first.val) := by
      rcases hi with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      simp only [gap, first, Nat.sub_zero]
      omega
    have hgapLe : gap ≤ lastGap := by
      exact Fin.mk_le_mk.mpr (by
        exact Nat.sub_le_sub_right hij 1)
    have hgapIndices :
        gap.castSucc = iprevious ∧ gap.succ = i := by
      constructor
      · apply Fin.ext
        rfl
      · apply Fin.ext
        simp only [Fin.val_succ, gap]
        omega
    have hpreviousOrder' : a.order iprevious = 0 := by
      have h := D.arithmetic.even_order gap (Fin.zero_le gap)
        hgapLe hgapEven
      rw [hgapIndices.1] at h
      exact h
    have hiOrder :
        a.order i = -(2 * (ramificationIndex K : Int)) := by
      have h := D.arithmetic.odd_order gap.succ (by
          simp only [Fin.val_succ, gap, first]
          omega) (by
          simp only [Fin.val_succ, gap, lastGap]
          omega) (by
          rcases hi with ⟨p, hp⟩
          refine ⟨p, ?_⟩
          simp only [Fin.val_succ, gap, first]
          omega)
      rw [hgapIndices.2] at h
      simpa using h
    have hgapValue : a.orderGap gap =
        -(2 * (ramificationIndex K : Int)) := by
      unfold orderGap
      rw [hgapIndices.1, hgapIndices.2, hpreviousOrder', hiOrder]
      omega
    have hcor := a.heHu2022Corollary23ii gap hgapValue
    have halpha : a.alphaValue gap = 0 :=
      (a.beli2009Lemma27_i gap).2.mpr hgapValue
    have hcapped := a.cappedAdjacent_ge_two_e_of_alphaValue_eq_zero
      gap halpha
    exact ⟨hpreviousOrder', hiOrder, by
      simpa only [heHuAdjacentCappedDefect] using hcapped,
      hcor.rawDefectLower⟩
  · rcases a.beli2019Lemma75_signedPrefixProduct_endpoint_cases
        lastGap 0 hlastEven (by simpa only [hfirstCast] using hfirstOrder)
        hlastTerminal with ⟨pairs, hpairs, hclass⟩
    refine ⟨pairs, ?_, hclass⟩
    simp only [lastGap] at hpairs
    omega

/-- Proposition 2.7(v), retaining the exact hyperbolic-plus-line isometry
and the two possible square classes of the final valuation-unit line. -/
structure HeHuProposition27vWitness {n : Nat}
    (a : GoodBONG q L (n + 2)) (j : Fin (n + 2)) where
  pairs : Nat
  pairCount : 2 * pairs = j.val + 1
  extendedPrefixBound : 2 * pairs + 1 ≤ n + 2
  epsilon : Kˣ
  squareFactor : Kˣ
  epsilonIsValuationUnit : IsValuationUnit K (epsilon : K)
  epsilonClass :
    let next : Fin (n + 2) := ⟨2 * pairs, by omega⟩
    epsilon = a.valueUnit next * squareFactor ^ 2 ∨
      epsilon =
        (heHuDiscriminantClassLaws (K := K)).discriminantUnit *
          a.valueUnit next * squareFactor ^ 2
  prefixNormalForm :
    (a.prefixDiagonalSpace (2 * pairs + 1) extendedPrefixBound).IsIsometric
      (AlternatingEndpointTower.hyperbolicEndpointTowerWithLineSpace
        (K := K) pairs epsilon)

/-- The proposition-valued wrapper for the explicit normal-form witness. -/
def HeHuProposition27vConclusions {n : Nat}
    (a : GoodBONG q L (n + 2)) (j : Fin (n + 2)) : Prop :=
  Nonempty (HeHuProposition27vWitness a j)

/-- He--Hu, Proposition 2.7(v).  In zero-based notation `j` is the
paper's even index minus one, and `next` is the coefficient `a_(j+1)` in
the displayed odd-dimensional prefix. -/
theorem heHu2022Proposition27v {n : Nat}
    (a : GoodBONG q L (n + 2)) (hIntegral : Lattice.IsIntegral q L)
    (j : Fin (n + 2)) (hj : Odd j.val)
    (hjOrder : a.order j = -(2 * (ramificationIndex K : Int)))
    (hnext : j.val + 1 < n + 2)
    (hnextEven : Even (a.order ⟨j.val + 1, hnext⟩)) :
    HeHuProposition27vConclusions a j := by
  rcases hj with ⟨p, hp⟩
  let pairs := p + 1
  have hpairCount : 2 * pairs = j.val + 1 := by
    simp only [pairs]
    omega
  have hprefixBound : 2 * pairs ≤ n + 2 := by omega
  have hextendedBound : 2 * pairs + 1 ≤ n + 2 := by omega
  let source := a.prefixValueUnits (2 * pairs) hprefixBound
  let next : Fin (n + 2) := ⟨2 * pairs, by omega⟩
  have hnextEq : next = ⟨j.val + 1, hnext⟩ := by
    apply Fin.ext
    exact hpairCount
  have hnextOrderEven : Even (ordUnit K (a.valueUnit next)) := by
    change Even (ordUnit K (a.toBONG.valueUnit next))
    rw [← a.toBONG.order_eq_ordUnit]
    rw [hnextEq]
    exact hnextEven
  let C := a.heHu2022Proposition27iiiiv hIntegral j
    (by exact ⟨p, hp⟩) hjOrder
  have hpairOrders (t : Fin pairs) :
      a.order ⟨2 * t.val, by omega⟩ = 0 ∧
        a.order ⟨2 * t.val + 1, by omega⟩ =
          -(2 * (ramificationIndex K : Int)) := by
    let oddIndex : Fin (n + 2) := ⟨2 * t.val + 1, by omega⟩
    have hoddIndex : Odd oddIndex.val := by
      refine ⟨t.val, ?_⟩
      simp only [oddIndex]
    have hle : oddIndex ≤ j := by
      apply Fin.mk_le_mk.mpr
      omega
    have h := C.pairOrdersAndDefects oddIndex hle hoddIndex
    constructor
    · simpa only [oddIndex, Nat.add_sub_cancel] using h.1
    · simpa only [oddIndex] using h.2.1
  have hsourceClasses : AlternatingEndpointPairClasses source := by
    intro t
    let evenIndex : Fin (n + 2) := ⟨2 * t.val, by omega⟩
    have hevenNext : evenIndex.val + 1 < n + 2 := by
      simp only [evenIndex]
      omega
    have hindexNext :
        (⟨evenIndex.val + 1, hevenNext⟩ : Fin (n + 2)) =
          ⟨2 * t.val + 1, by omega⟩ := by
      apply Fin.ext
      rfl
    have horders := hpairOrders t
    have hgap :
        a.order ⟨evenIndex.val + 1, hevenNext⟩ -
            a.order evenIndex =
          -(2 * (ramificationIndex K : Int)) := by
      rw [hindexNext, horders.2]
      change -(2 * (ramificationIndex K : Int)) -
          a.order ⟨2 * t.val, by omega⟩ = _
      rw [horders.1]
      omega
    have hpClass := a.toBONG.adjacentUnitSquareClass_endpoint_cases
      evenIndex hevenNext hgap
    have hpSigned := a.toBONG.adjacentSignedProduct_endpoint_cases
      evenIndex hevenNext hpClass
    simpa [source, AlternatingEndpointPairClasses,
      prefixValueUnits, GoodBONG.valueUnit, evenIndex, hindexNext] using hpSigned
  have hsourceOrders : AlternatingEndpointLeadingOrdersAt source (1 : Kˣ) := by
    intro t
    change ordUnit K (a.toBONG.valueUnit ⟨2 * t.val, by omega⟩) =
      ordUnit K (1 : Kˣ)
    rw [← a.toBONG.order_eq_ordUnit]
    change a.order ⟨2 * t.val, by omega⟩ = ordUnit K (1 : Kˣ)
    rw [(hpairOrders t).1]
    have hone : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    exact hone.symm
  rcases AlternatingEndpointTower.oddNormalForm_of_even_order
      source (a.valueUnit next) hsourceClasses hsourceOrders hnextOrderEven with
    ⟨epsilon, squareFactor, hepsilonUnit, hepsilonClass, hnormal⟩
  refine ⟨{
    pairs := pairs
    pairCount := hpairCount
    extendedPrefixBound := hextendedBound
    epsilon := epsilon
    squareFactor := squareFactor
    epsilonIsValuationUnit := hepsilonUnit
    epsilonClass := ?_
    prefixNormalForm := ?_ }⟩
  · simpa only [next] using hepsilonClass
  · have hsnoc := a.prefixValueUnits_succ_eq_snoc
      (2 * pairs) hextendedBound
    rw [← hsnoc] at hnormal
    simpa only [source, prefixDiagonalSpace,
      diagonalUnitCoefficients_prefixValueUnits] using hnormal

/-- He--Hu, Theorem 2.8.  `RepresentationConditions` unfolds to the four
displayed conditions (i)--(iv), including the exceptional terminal-index
convention in condition (iv). -/
theorem heHu2022Theorem28 {m n : Nat}
    (hRank : n ≤ m) (ambient : q.Represents r)
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1)) :
    Lattice.Represents q r L M ↔ RepresentationConditions a b hRank :=
  beli2019Theorem21 hRank ambient a b

end BONG.GoodBONG

end Bong
