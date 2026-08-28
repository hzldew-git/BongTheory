/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanIdeals

/-!
# Beli (2009/2010), Lemmas 2.13--2.16 and Corollary 2.17

Jordan blocks are represented by checked half-open intervals in a good BONG.
The alternating order pattern is concrete, so both orientations of Lemma 2.13
and the adjacent-sum identity are proved arithmetically.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n N : Nat}

namespace BONG.GoodBONG

/-- A Jordan block occupying the half-open interval `[start, stop)` of a
good BONG.  Its orders alternate between `u` and `2r-u`. -/
structure JordanBlockCoordinates (b : GoodBONG q L N) where
  start : Nat
  stop : Nat
  start_lt_stop : start < stop
  stop_le : stop ≤ N
  scaleOrder : Int
  normOrder : Int
  order_eq : ∀ (j : Nat) (_hstart : start ≤ j) (hstop : j < stop),
    b.order ⟨j, hstop.trans_le stop_le⟩ =
      if (j - start) % 2 = 0 then normOrder else 2 * scaleOrder - normOrder
  proper_or_even : normOrder = scaleOrder ∨ Even (stop - start)

namespace JordanBlockCoordinates

variable {b : GoodBONG q L N}

/-- A checked global BONG index in the block. -/
def index (C : JordanBlockCoordinates b) (j : Nat)
    (hstop : j < C.stop) : Fin N :=
  ⟨j, hstop.trans_le C.stop_le⟩

/-- The first global BONG index of the block. -/
def firstIndex (C : JordanBlockCoordinates b) : Fin N :=
  C.index C.start C.start_lt_stop

/-- The last global BONG index of the block. -/
def lastIndex (C : JordanBlockCoordinates b) : Fin N :=
  C.index (C.stop - 1) (by
    have hpos : 0 < C.stop := C.start_lt_stop.trans_le' (Nat.zero_le _)
    omega)

@[simp]
theorem index_val (C : JordanBlockCoordinates b) (j : Nat)
    (hstop : j < C.stop) : (C.index j hstop).1 = j :=
  rfl

/-- Beli (2009/2010), Lemma 2.13(i), in zero-based coordinates. -/
theorem beli2009Lemma213_i (C : JordanBlockCoordinates b)
    (j : Nat) (hstart : C.start ≤ j) (hstop : j < C.stop) :
    ((j - C.start) % 2 = 0 →
      b.order (C.index j hstop) = C.normOrder) ∧
    ((j - C.start) % 2 = 1 →
      b.order (C.index j hstop) = 2 * C.scaleOrder - C.normOrder) := by
  constructor <;> intro hparity
  · simpa [index, hparity] using C.order_eq j hstart hstop
  · have hne : (j - C.start) % 2 ≠ 0 := by omega
    simpa [index, hne] using C.order_eq j hstart hstop

/-- Beli (2009/2010), Lemma 2.13(ii), oriented from the right endpoint. -/
theorem beli2009Lemma213_ii (C : JordanBlockCoordinates b)
    (j : Nat) (hstart : C.start ≤ j) (hstop : j < C.stop) :
    ((C.stop - j) % 2 = 0 →
      b.order (C.index j hstop) = C.normOrder) ∧
    ((C.stop - j) % 2 = 1 →
      b.order (C.index j hstop) = 2 * C.scaleOrder - C.normOrder) := by
  rcases C.proper_or_even with hproper | heven
  · have hparity : (j - C.start) % 2 = 0 ∨
        (j - C.start) % 2 = 1 := by omega
    have hnorm : b.order (C.index j hstop) = C.normOrder := by
      rcases hparity with hzero | hone
      · exact (C.beli2009Lemma213_i j hstart hstop).1 hzero
      · have halt := (C.beli2009Lemma213_i j hstart hstop).2 hone
        omega
    constructor
    · intro _
      exact hnorm
    · intro _
      omega
  · rcases heven with ⟨d, hd⟩
    have hsplit : C.stop - C.start =
        (j - C.start) + (C.stop - j) := by omega
    constructor
    · intro hright
      have hleft : (j - C.start) % 2 = 0 := by omega
      exact (C.beli2009Lemma213_i j hstart hstop).1 hleft
    · intro hright
      have hleft : (j - C.start) % 2 = 1 := by omega
      exact (C.beli2009Lemma213_i j hstart hstop).2 hleft

/-- Consecutive orders inside a Jordan block sum to twice the scale order. -/
theorem adjacent_order_sum (C : JordanBlockCoordinates b)
    (j : Nat) (hstart : C.start ≤ j) (hnext : j + 1 < C.stop) :
    b.order (C.index j (by omega)) +
        b.order (C.index (j + 1) hnext) = 2 * C.scaleOrder := by
  have hzero_or_one : (j - C.start) % 2 = 0 ∨
      (j - C.start) % 2 = 1 := by omega
  rcases hzero_or_one with hzero | hone
  · have hnextParity : (j + 1 - C.start) % 2 = 1 := by omega
    rw [(C.beli2009Lemma213_i j hstart (by omega)).1 hzero,
      (C.beli2009Lemma213_i (j + 1) (by omega) hnext).2 hnextParity]
    ring
  · have hnextParity : (j + 1 - C.start) % 2 = 0 := by omega
    rw [(C.beli2009Lemma213_i j hstart (by omega)).2 hone,
      (C.beli2009Lemma213_i (j + 1) (by omega) hnext).1 hnextParity]
    ring

end JordanBlockCoordinates

/-- A Jordan block together with its component and its associated scale
layer. -/
structure JordanBlockLatticeData (b : GoodBONG q L N)
    extends JordanBlockCoordinates b where
  component : Lattice.QuadraticSublattice q
  scaleLayer : Lattice.QuadraticSublattice q

namespace JordanBlockLatticeData

variable {b : GoodBONG q L N}

/-- The first BONG value in a Jordan block. -/
noncomputable def firstNormValue (C : JordanBlockLatticeData b) : Kˣ :=
  b.valueUnit C.firstIndex

/-- The rescaled last BONG value in Lemma 2.13(iii). -/
noncomputable def terminalNormValue (C : JordanBlockLatticeData b) : Kˣ :=
  uniformizerPowerUnit K (2 * C.normOrder - 2 * C.scaleOrder) *
    b.valueUnit C.lastIndex

end JordanBlockLatticeData

end BONG.GoodBONG

namespace Lattice

/-- Both signs of `a` are norm-generator values. -/
def BothSignsNormGeneratorValue (q : QuadraticSpace K V)
    (L : Lattice K V) (a : Kˣ) : Prop :=
  IsNormGeneratorValue q L a ∧ IsNormGeneratorValue q L (-a)

end Lattice

/-- The norm-generator bridge in Lemma 2.13(iii).
This class intentionally has no default instance. -/
class Beli2009JordanBlockLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  lemma213_iii
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}
    {b : BONG.GoodBONG q L N}
    (C : b.JordanBlockLatticeData) :
    Lattice.BothSignsNormGeneratorValue
        C.component.space C.component.lattice C.firstNormValue ∧
      Lattice.BothSignsNormGeneratorValue
        C.scaleLayer.space C.scaleLayer.lattice C.firstNormValue ∧
      Lattice.BothSignsNormGeneratorValue
        C.component.space C.component.lattice C.terminalNormValue ∧
      Lattice.BothSignsNormGeneratorValue
        C.scaleLayer.space C.scaleLayer.lattice C.terminalNormValue

namespace BONG.GoodBONG.JordanBlockLatticeData

variable {b : BONG.GoodBONG q L N} [Beli2009JordanBlockLaws.{u, v} K]

/-- Beli (2009/2010), Lemma 2.13(iii). -/
theorem beli2009Lemma213_iii (C : JordanBlockLatticeData b) :
    Lattice.BothSignsNormGeneratorValue
        C.component.space C.component.lattice C.firstNormValue ∧
      Lattice.BothSignsNormGeneratorValue
        C.scaleLayer.space C.scaleLayer.lattice C.firstNormValue ∧
      Lattice.BothSignsNormGeneratorValue
        C.component.space C.component.lattice C.terminalNormValue ∧
      Lattice.BothSignsNormGeneratorValue
        C.scaleLayer.space C.scaleLayer.lattice C.terminalNormValue :=
  Beli2009JordanBlockLaws.lemma213_iii C

end BONG.GoodBONG.JordanBlockLatticeData

/-- The weight-order formulas requiring the Jordan decomposition.
This class intentionally has no default instance. -/
class Beli2009JordanWeightOrderLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  lemma214_unary
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    [Beli2009WeightIdealData.{u, v} K]
    (b : BONG.GoodBONG q L 1) :
    Lattice.weightIdealOrder q L =
      b.order 0 + (ramificationIndex K : Int)
  lemma214
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    [Beli2009WeightIdealData.{u, v} K]
    (b : BONG.GoodBONG q L (n + 2)) :
    (Lattice.weightIdealOrder q L : ℚ) =
      min ((b.order 0 : ℚ) + b.alphaValue 0)
        ((b.order 0 : ℚ) + (ramificationIndex K : ℚ))

namespace BONG.GoodBONG

variable [Beli2009WeightIdealData.{u, v} K]
  [Beli2009JordanWeightOrderLaws.{u, v} K]

/-- Beli (2009/2010), Lemma 2.14 in rank one. -/
theorem beli2009Lemma214_unary (b : GoodBONG q L 1) :
    Lattice.weightIdealOrder q L =
      b.order 0 + (ramificationIndex K : Int) :=
  Beli2009JordanWeightOrderLaws.lemma214_unary b

/-- Beli (2009/2010), Lemma 2.14. -/
theorem beli2009Lemma214 (b : GoodBONG q L (n + 2)) :
    (Lattice.weightIdealOrder q L : ℚ) =
      min ((b.order 0 : ℚ) + b.alphaValue 0)
        ((b.order 0 : ℚ) + (ramificationIndex K : ℚ)) :=
  Beli2009JordanWeightOrderLaws.lemma214 b

/-- Lemma 2.14's final assertion when the first Jordan component is not
unary, expressed by its first descending order step. -/
theorem beli2009Lemma214_of_firstBlock_not_unary
    (b : GoodBONG q L (n + 2))
    (hdescending : b.order 1 ≤ b.order 0) :
    (Lattice.weightIdealOrder q L : ℚ) =
      (b.order 0 : ℚ) + b.alphaValue 0 := by
  rw [b.beli2009Lemma214]
  apply min_eq_left
  have halpha := b.alphaValue_le_halfGapValue 0
  change b.alphaValue 0 ≤
    ((b.order 1 - b.order 0 : Int) : ℚ) / 2 +
      (ramificationIndex K : ℚ) at halpha
  push_cast at halpha
  have hcast : (b.order 1 : ℚ) ≤ (b.order 0 : ℚ) := by
    exact_mod_cast hdescending
  linarith

end BONG.GoodBONG

namespace Lattice

/-- Ideal data for a unary Jordan component.  Missing neighboring
fundamental ideals encode the endpoint conventions of Lemma 2.15. -/
structure UnaryJordanIdealData
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] where
  scaleGenerator : Kˣ
  weight : OrderedFractionalIdeal K
  previousFundamental : Option (OrderedFractionalIdeal K)
  nextFundamental : Option (OrderedFractionalIdeal K)

namespace UnaryJordanIdealData

variable (U : UnaryJordanIdealData K)

/-- An absent neighboring fundamental ideal contributes the zero ideal. -/
noncomputable def optionalIdeal :
    Option (OrderedFractionalIdeal K) → CoefficientIdeal (K := K)
  | none => ⊥
  | some I => I.carrier

/-- The right-hand side of Lemma 2.15. -/
noncomputable def weightExpression : CoefficientIdeal (K := K) :=
  scalarIdeal (U.scaleGenerator : K)
    (optionalIdeal U.previousFundamental ⊔
      optionalIdeal U.nextFundamental ⊔ twiceIdeal unitIdeal)

/-- The order of `a_k⁻¹ w_k`; for a unary component `a_k O = s_k`. -/
noncomputable def normalizedWeightOrder : ℚ :=
  (U.weight.order - ordUnit K U.scaleGenerator : Int)

/-- The minimum of the existing neighboring fundamental orders and `e`. -/
noncomputable def neighboringFundamentalMinimum : ℚ :=
  let left := U.previousFundamental.map fun I => (I.order : ℚ)
  let right := U.nextFundamental.map fun I => (I.order : ℚ)
  min (left.getD (ramificationIndex K : ℚ))
    (min (right.getD (ramificationIndex K : ℚ))
      (ramificationIndex K : ℚ))

end UnaryJordanIdealData

end Lattice

/-- The unary-component calculation in Lemma 2.15.
This class intentionally has no default instance. -/
class Beli2009UnaryJordanIdealLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  lemma215 (U : Lattice.UnaryJordanIdealData K) :
    U.weight.carrier = U.weightExpression
  lemma215_order (U : Lattice.UnaryJordanIdealData K) :
    U.normalizedWeightOrder = U.neighboringFundamentalMinimum

namespace Lattice.UnaryJordanIdealData

variable [Beli2009UnaryJordanIdealLaws.{u} K]

/-- Beli (2009/2010), Lemma 2.15. -/
theorem beli2009Lemma215 (U : UnaryJordanIdealData K) :
    U.weight.carrier = U.weightExpression :=
  Beli2009UnaryJordanIdealLaws.lemma215 U

theorem beli2009Lemma215_order (U : UnaryJordanIdealData K) :
    U.normalizedWeightOrder = U.neighboringFundamentalMinimum :=
  Beli2009UnaryJordanIdealLaws.lemma215_order U

end Lattice.UnaryJordanIdealData

namespace BONG.GoodBONG

/-- Data for an adjacent index strictly inside one Jordan block. -/
structure InternalJordanAlphaData (b : GoodBONG q L (n + 1)) where
  block : JordanBlockCoordinates b
  index : Nat
  start_le : block.start ≤ index
  next_lt_stop : index + 1 < block.stop
  weight : Lattice.OrderedFractionalIdeal K
  dualWeight : Lattice.OrderedFractionalIdeal K
  dualWeightOrder_eq :
    dualWeight.order = weight.order - 2 * block.scaleOrder

namespace InternalJordanAlphaData

variable {b : GoodBONG q L (n + 1)}

def alphaIndex (D : InternalJordanAlphaData b) : Fin n :=
  ⟨D.index, by
    have hnext := D.next_lt_stop
    have hstop := D.block.stop_le
    omega⟩

def leftIndex (D : InternalJordanAlphaData b) : Fin (n + 1) :=
  D.block.index D.index (by
    have hnext := D.next_lt_stop
    omega)

def rightIndex (D : InternalJordanAlphaData b) : Fin (n + 1) :=
  D.block.index (D.index + 1) D.next_lt_stop

end InternalJordanAlphaData

/-- Data for an index at a boundary between two Jordan components. -/
structure BoundaryJordanAlphaData (b : GoodBONG q L (n + 1)) where
  index : Fin n
  fundamental : Lattice.OrderedFractionalIdeal K

end BONG.GoodBONG

/-- The remaining Jordan-to-alpha comparisons in Lemma 2.16.
This class intentionally has no default instance. -/
class Beli2009JordanAlphaLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  lemma216_i_left
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    {b : BONG.GoodBONG q L (n + 1)}
    (D : b.InternalJordanAlphaData) :
    (b.order D.leftIndex : ℚ) + b.alphaValue D.alphaIndex = D.weight.order
  lemma216_ii_even
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    {b : BONG.GoodBONG q L (n + 1)}
    (D : b.BoundaryJordanAlphaData) (heven : Even (b.orderGap D.index)) :
    (D.fundamental.order : ℚ) = b.alphaValue D.index
  lemma216_ii_odd
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    {b : BONG.GoodBONG q L (n + 1)}
    (D : b.BoundaryJordanAlphaData) (hodd : Odd (b.orderGap D.index)) :
    D.fundamental.order = b.orderGap D.index

namespace BONG.GoodBONG.InternalJordanAlphaData

variable {b : BONG.GoodBONG q L (n + 1)}
  [Beli2009JordanAlphaLaws.{u, v} K]

/-- Beli (2009/2010), Lemma 2.16(i). -/
theorem beli2009Lemma216_i (D : InternalJordanAlphaData b) :
    ((b.order D.leftIndex : ℚ) + b.alphaValue D.alphaIndex =
        (D.weight.order : ℚ)) ∧
      (-(b.order D.rightIndex : ℚ) + b.alphaValue D.alphaIndex =
        (D.dualWeight.order : ℚ)) := by
  have hleft := Beli2009JordanAlphaLaws.lemma216_i_left D
  refine ⟨hleft, ?_⟩
  have hsum := D.block.adjacent_order_sum D.index D.start_le D.next_lt_stop
  have hsumQ :
      (b.order D.leftIndex : ℚ) + (b.order D.rightIndex : ℚ) =
        2 * (D.block.scaleOrder : ℚ) := by
    exact_mod_cast hsum
  have hdual : (D.dualWeight.order : ℚ) =
      (D.weight.order : ℚ) - 2 * (D.block.scaleOrder : ℚ) := by
    exact_mod_cast D.dualWeightOrder_eq
  linarith

end BONG.GoodBONG.InternalJordanAlphaData

namespace BONG.GoodBONG.BoundaryJordanAlphaData

variable {b : BONG.GoodBONG q L (n + 1)}
  [Beli2006AlphaLaws.{u, v} K]
  [Beli2009AlphaParityLaws.{u, v} K]
  [Beli2009JordanAlphaLaws.{u, v} K]

/-- Beli (2009/2010), Lemma 2.16(ii), with both branches explicit. -/
theorem beli2009Lemma216_ii (D : BoundaryJordanAlphaData b) :
    ((Even (b.orderGap D.index) ∨
        b.orderGap D.index ≤ 2 * (ramificationIndex K : Int)) →
      b.alphaValue D.index = (D.fundamental.order : ℚ)) ∧
    (¬(Even (b.orderGap D.index) ∨
        b.orderGap D.index ≤ 2 * (ramificationIndex K : Int)) →
      b.alphaValue D.index = b.halfGapValue D.index ∧
      D.fundamental.order = b.orderGap D.index ∧
      (D.fundamental.order : ℚ) =
        2 * b.alphaValue D.index -
          2 * (ramificationIndex K : ℚ) ∧
      2 * (ramificationIndex K : ℚ) < b.alphaValue D.index ∧
      2 * (ramificationIndex K : ℚ) < (D.fundamental.order : ℚ)) := by
  constructor
  · rintro (heven | hgap)
    · exact (Beli2009JordanAlphaLaws.lemma216_ii_even D heven).symm
    · rcases Int.even_or_odd (b.orderGap D.index) with heven | hodd
      · exact (Beli2009JordanAlphaLaws.lemma216_ii_even D heven).symm
      · have halpha :=
          (b.beli2009Lemma27_iii D.index hgap).2.mpr (Or.inr hodd)
        have hfund := Beli2009JordanAlphaLaws.lemma216_ii_odd D hodd
        rw [halpha, hfund]
  · intro hexceptional
    have hnotEven : ¬Even (b.orderGap D.index) := by
      intro heven
      exact hexceptional (Or.inl heven)
    have hgap : 2 * (ramificationIndex K : Int) <
        b.orderGap D.index := by
      omega
    have hodd : Odd (b.orderGap D.index) := by
      rcases Int.even_or_odd (b.orderGap D.index) with heven | hodd
      · exact False.elim (hnotEven heven)
      · exact hodd
    have halpha := b.beli2009Lemma27_ii D.index hgap.le
    have hfund := Beli2009JordanAlphaLaws.lemma216_ii_odd D hodd
    have halphaLarge : 2 * (ramificationIndex K : ℚ) <
        b.alphaValue D.index :=
      (b.beli2009Corollary28_ii D.index).2.2.mpr hgap
    have hfundLarge : 2 * (ramificationIndex K : ℚ) <
        (D.fundamental.order : ℚ) := by
      rw [hfund]
      exact_mod_cast hgap
    refine ⟨halpha, hfund, ?_, halphaLarge, hfundLarge⟩
    rw [hfund, halpha]
    unfold halfGapValue
    ring

/-- A boundary fundamental order and its alpha have the same minimum with
the ramification index. -/
theorem fundamentalOrder_min_e_eq_alpha_min_e
    (D : BoundaryJordanAlphaData b) :
    min (D.fundamental.order : ℚ) (ramificationIndex K : ℚ) =
      min (b.alphaValue D.index) (ramificationIndex K : ℚ) := by
  rcases D.beli2009Lemma216_ii with ⟨hregular, hexceptional⟩
  by_cases hcase : Even (b.orderGap D.index) ∨
      b.orderGap D.index ≤ 2 * (ramificationIndex K : Int)
  · rw [hregular hcase]
  · have h := hexceptional hcase
    have he : (ramificationIndex K : ℚ) <
        2 * (ramificationIndex K : ℚ) := by
      have hpos := ramificationIndex_pos (K := K)
      exact_mod_cast (show (ramificationIndex K : Int) <
        2 * (ramificationIndex K : Int) by omega)
    rw [min_eq_right (le_of_lt (he.trans h.2.2.2.2)),
      min_eq_right (le_of_lt (he.trans h.2.2.2.1))]

end BONG.GoodBONG.BoundaryJordanAlphaData

namespace BONG.GoodBONG.InternalJordanAlphaData

variable {b : BONG.GoodBONG q L (n + 1)}
  [Beli2009JordanAlphaLaws.{u, v} K]

/-- Beli (2009/2010), Corollary 2.17(i), in order form. -/
theorem beli2009Corollary217_i (D : InternalJordanAlphaData b)
    (ak : Kˣ) (hak : ordUnit K ak = b.order D.leftIndex) :
    ((D.weight.order - ordUnit K ak : Int) : ℚ) =
      b.alphaValue D.alphaIndex := by
  have hleft := (D.beli2009Lemma216_i).1
  have hakQ : (ordUnit K ak : ℚ) = (b.order D.leftIndex : ℚ) := by
    exact_mod_cast hak
  push_cast
  linarith

end BONG.GoodBONG.InternalJordanAlphaData

namespace Lattice

/-- The endpoint-aware minimum used in Corollary 2.17(ii).  `none` means
that the corresponding term is to be ignored. -/
def neighboringMinimum (left right : Option ℚ) (e : ℚ) : ℚ :=
  min (left.getD e) (min (right.getD e) e)

/-- Replacing existing neighboring values by values with the same cap at `e`
does not change the endpoint-aware minimum. -/
theorem neighboringMinimum_congr
    {left right left' right' : Option ℚ} {e : ℚ}
    (hleft : (left.map (fun x => min x e)).getD e =
      (left'.map (fun x => min x e)).getD e)
    (hright : (right.map (fun x => min x e)).getD e =
      (right'.map (fun x => min x e)).getD e) :
    neighboringMinimum left right e =
      neighboringMinimum left' right' e := by
  have hformula (x y : Option ℚ) :
      neighboringMinimum x y e =
        min ((x.map fun z => min z e).getD e)
          ((y.map fun z => min z e).getD e) := by
    cases x <;> cases y <;>
      simp [neighboringMinimum, min_left_comm, min_comm]
  rw [hformula left right, hformula left' right', hleft, hright]

/-- Beli (2009/2010), Corollary 2.17(ii), including both endpoint
conventions through optional neighbors. -/
theorem beli2009Corollary217_ii
    (U : UnaryJordanIdealData K)
    (previousAlpha nextAlpha : Option ℚ)
    (hprevious : previousAlpha.map
        (fun x => min x (ramificationIndex K : ℚ)) =
      U.previousFundamental.map
        (fun I => min (I.order : ℚ) (ramificationIndex K : ℚ)))
    (hnext : nextAlpha.map
        (fun x => min x (ramificationIndex K : ℚ)) =
      U.nextFundamental.map
        (fun I => min (I.order : ℚ) (ramificationIndex K : ℚ)))
    [Beli2009UnaryJordanIdealLaws.{u} K] :
    U.normalizedWeightOrder =
      neighboringMinimum previousAlpha nextAlpha
        (ramificationIndex K : ℚ) := by
  rw [U.beli2009Lemma215_order]
  change neighboringMinimum
      (U.previousFundamental.map fun I => (I.order : ℚ))
      (U.nextFundamental.map fun I => (I.order : ℚ))
      (ramificationIndex K : ℚ) = _
  apply neighboringMinimum_congr
  · have h := congrArg
        (fun x : Option ℚ => x.getD (ramificationIndex K : ℚ))
        hprevious.symm
    have hmap :
        (U.previousFundamental.map fun I => (I.order : ℚ)).map
            (fun x => min x (ramificationIndex K : ℚ)) =
          U.previousFundamental.map
            (fun I => min (I.order : ℚ) (ramificationIndex K : ℚ)) := by
      cases U.previousFundamental <;> rfl
    rw [hmap]
    exact h
  · have h := congrArg
        (fun x : Option ℚ => x.getD (ramificationIndex K : ℚ))
        hnext.symm
    have hmap :
        (U.nextFundamental.map fun I => (I.order : ℚ)).map
            (fun x => min x (ramificationIndex K : ℚ)) =
          U.nextFundamental.map
            (fun I => min (I.order : ℚ) (ramificationIndex K : ℚ)) := by
      cases U.nextFundamental <;> rfl
    rw [hmap]
    exact h

end Lattice

end Bong
