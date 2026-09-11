/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022SectionTwo

/-!
# He (2025), Section 3: BONG preliminaries

The published ADC paper recalls the same BONG criterion, alpha arithmetic,
integral-order constraints, and representation theorem already proved in the
He--Hu development.  This file supplies ADC-numbered endpoints rather than
counting an import as paper coverage.  Paper indices are one-based; Lean
indices below are zero-based.
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

/-- He, Lemma 3.1: the good-BONG realization criterion. -/
theorem heADC2025Lemma31 {n : Nat} (X : OrthogonalBasisData q n) :
    X.HasGoodRealization ↔ X.HeHuGoodBONGCriteria :=
  X.heHu2022Lemma22

end BONG.OrthogonalBasisData

namespace BONG.GoodBONG

/-- He, Corollary 3.2(i): an odd adjacent order gap is positive. -/
theorem heADC2025Corollary32i {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n) :
    Odd (a.orderGap i) → 0 < a.orderGap i :=
  (a.heHu2022Corollary23i i).1

/-- He, Corollary 3.2(ii), including the two endpoint lattice models. -/
theorem heADC2025Corollary32ii {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n)
    (hgap : a.orderGap i =
      -(2 * (ramificationIndex K : Int))) :
    HeHuCorollary23iiConclusions a i :=
  a.heHu2022Corollary23ii i hgap

/-- The three clauses of He, Proposition 3.3. -/
structure HeADCProposition33Conclusions {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n) : Prop where
  compareTwoE :
    (2 * (ramificationIndex K : Int) < a.orderGap i ↔
      2 * (ramificationIndex K : ℚ) < a.alphaValue i) ∧
    (a.orderGap i = 2 * (ramificationIndex K : Int) ↔
      a.alphaValue i = 2 * (ramificationIndex K : ℚ)) ∧
    (a.orderGap i < 2 * (ramificationIndex K : Int) ↔
      a.alphaValue i < 2 * (ramificationIndex K : ℚ))
  halfGap (hcase :
      2 * (ramificationIndex K : Int) ≤ a.orderGap i ∨
      a.orderGap i = -(2 * (ramificationIndex K : Int)) ∨
      a.orderGap i = 2 - 2 * (ramificationIndex K : Int) ∨
      a.orderGap i = 2 * (ramificationIndex K : Int) - 2) :
    a.alphaValue i = a.halfGapValue i
  lowerBound (hgap : a.orderGap i ≤
      2 * (ramificationIndex K : Int)) :
    (a.orderGap i : ℚ) ≤ a.alphaValue i ∧
      (a.alphaValue i = (a.orderGap i : ℚ) ↔
        a.orderGap i = 2 * (ramificationIndex K : Int) ∨
          Odd (a.orderGap i))

/-- He, Proposition 3.3. -/
theorem heADC2025Proposition33 {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n) :
    HeADCProposition33Conclusions a i := by
  let C := a.heHu2022Proposition26 i
  refine ⟨?_, C.halfGap, C.lowerBound⟩
  exact ⟨C.compareTwoE.2.2.symm, C.compareTwoE.2.1.symm,
    C.compareTwoE.1.symm⟩

/-- The capped defect `d[-a_i a_(i+1)]` used in He, Proposition 3.4. -/
noncomputable abbrev heADCAdjacentCappedDefect {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n) : WithTop ℚ :=
  a.heHuAdjacentCappedDefect i

/-- The five clauses of He, Proposition 3.4. -/
structure HeADCProposition34Conclusions {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n) : Prop where
  arithmeticShape :
    (0 ≤ a.alphaValue i ∧
        a.alphaValue i ≤ 2 * (ramificationIndex K : ℚ) ∧
        IsRationalInteger (a.alphaValue i)) ∨
      (2 * (ramificationIndex K : ℚ) < a.alphaValue i ∧
        IsRationalHalfInteger (a.alphaValue i))
  alphaZero : a.alphaValue i = 0 ↔
    a.orderGap i = -(2 * (ramificationIndex K : Int))
  alphaOne : a.alphaValue i = 1 ↔
    (a.orderGap i = 2 - 2 * (ramificationIndex K : Int) ∨
      a.orderGap i = 1) ∨
    (Even (a.orderGap i) ∧
      4 - 2 * (ramificationIndex K : Int) ≤ a.orderGap i ∧
      a.orderGap i ≤ 0 ∧
      a.heADCAdjacentCappedDefect i =
        ((((1 : ℚ) - (a.orderGap i : ℚ)) : ℚ) : WithTop ℚ))
  alphaZeroDefect (halpha : a.alphaValue i = 0) :
    ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.heADCAdjacentCappedDefect i
  alphaOneDefect (halpha : a.alphaValue i = 1) :
    ((((1 : ℚ) - (a.orderGap i : ℚ)) : ℚ) : WithTop ℚ) ≤
      a.heADCAdjacentCappedDefect i ∧
    (a.orderGap i ≠ 2 - 2 * (ramificationIndex K : Int) →
      a.heADCAdjacentCappedDefect i =
        ((((1 : ℚ) - (a.orderGap i : ℚ)) : ℚ) : WithTop ℚ))

/-- He, Proposition 3.4. -/
theorem heADC2025Proposition34 {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n) :
    HeADCProposition34Conclusions a i := by
  let C := a.heHu2022Proposition26 i
  refine
    { arithmeticShape := C.arithmeticShape
      alphaZero := C.alphaZero
      alphaOne := ?_
      alphaZeroDefect := C.alphaZeroDefect
      alphaOneDefect := fun halpha => ⟨(C.alphaOne halpha).2.1,
        (C.alphaOne halpha).2.2⟩ }
  constructor
  · intro halpha
    have h := C.alphaOne halpha
    rcases h.1 with hone | heven
    · exact Or.inl (Or.inr hone)
    · by_cases hendpoint :
        a.orderGap i = 2 - 2 * (ramificationIndex K : Int)
      · exact Or.inl (Or.inl hendpoint)
      · right
        refine ⟨heven.1, ?_, heven.2.2, h.2.2 hendpoint⟩
        rcases heven.1 with ⟨z, hz⟩
        omega
  · rintro (hendpoint | hmiddle)
    · exact a.alphaValue_eq_one_of_orderGap_eq_endpoint i hendpoint
    · have hlower :
          2 - 2 * (ramificationIndex K : Int) < a.orderGap i := by
        omega
      exact (C.alphaOneIff hlower hmiddle.2.2.1).2 hmiddle.2.2.2

/-- He, Proposition 3.5.  Each field is the already checked corresponding
clause of He--Hu, Proposition 2.7, now exposed under the ADC numbering. -/
structure HeADCProposition35Conclusions {n : Nat}
    (a : GoodBONG q L (n + 2)) : Prop where
  clauseI : HeHuProposition27iConclusions a
  clauseII (j : Fin (n + 2)) (hj : Even j.val)
      (hjOrder : a.order j = 0) :
    HeHuProposition27iiConclusions a j
  clausesIIIIV (j : Fin (n + 2)) (hj : Odd j.val)
      (hjOrder : a.order j =
        -(2 * (ramificationIndex K : Int))) :
    HeHuProposition27iiiivConclusions a j
  clauseV (j : Fin (n + 2)) (hj : Odd j.val)
      (hjOrder : a.order j =
        -(2 * (ramificationIndex K : Int)))
      (hnext : j.val + 1 < n + 2)
      (hnextEven : Even (a.order ⟨j.val + 1, by omega⟩)) :
    HeHuProposition27vConclusions a j

/-- He, Proposition 3.5. -/
theorem heADC2025Proposition35 {n : Nat}
    (a : GoodBONG q L (n + 2)) (hIntegral : Lattice.IsIntegral q L) :
    HeADCProposition35Conclusions a := by
  refine
    { clauseI := a.heHu2022Proposition27i hIntegral
      clauseII := ?_
      clausesIIIIV := ?_
      clauseV := ?_ }
  · intro j hj hjOrder
    exact a.heHu2022Proposition27ii hIntegral j hj hjOrder
  · intro j hj hjOrder
    exact a.heHu2022Proposition27iiiiv hIntegral j hj hjOrder
  · intro j hj hjOrder hnext hnextEven
    exact a.heHu2022Proposition27v hIntegral j hj hjOrder hnext hnextEven

/-- He, Theorem 3.6: Beli's four-condition representation theorem. -/
theorem heADC2025Theorem36 {m n : Nat}
    (hRank : n ≤ m) (ambient : q.Represents r)
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1)) :
    Lattice.Represents q r L M ↔ RepresentationConditions a b hRank :=
  heHu2022Theorem28 hRank ambient a b

end BONG.GoodBONG

end Bong
