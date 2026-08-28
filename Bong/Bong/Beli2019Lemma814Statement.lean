/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma813

/-!
# Beli (2019), Lemma 8.14: exact statement

This file records the three exceptional cases in Lemma 8.14 and the exact
meaning of its conclusion.  The target rank is `N + 3`, since the statement
uses `R_3`.  The paper's qualifications "if `n >= 4`" and "if `n >= 5`"
are retained as dependent hypotheses, so no value is assigned to a missing
`R_i` or `alpha_i`.

The printed statement says that the prescribed first value exists unless one
of the exceptions occurs.  The proof also establishes the converse.  Thus
`Beli2019Lemma814Claim` is the equivalence proved by the lemma.  We expose both
the literal lattice-representation statement and a noncircular statement
whose representation hypothesis is the explicit conclusion of Lemma 8.13.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

/-- The bracketed defect `d[-a_(1,3)b_1]` in Lemmas 8.13--8.14. -/
noncomputable def lemma814FirstThirdCappedDefect
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) : WithTop ℚ :=
  a.truncatedPrefixDefect b (-1) 3 1

/-- The bracketed defect `d[a_(1,4)]`, available from target rank four. -/
noncomputable def lemma814FirstFourCappedDefect
    (a : GoodBONG q L (N + 3)) (_hfour : 4 ≤ N + 3) : WithTop ℚ :=
  a.truncatedPrefixDefect a 1 4 0

/-- The quantity `e - (R_4 - R_3) / 2` occurring in exception (c). -/
noncomputable def lemma814ThirdComplementaryDefect
    (a : GoodBONG q L (N + 3)) (hfour : 4 ≤ N + 3) : ℚ :=
  (ramificationIndex K : ℚ) -
    (a.orderGap (⟨2, by omega⟩ : Fin (N + 2)) : ℚ) / 2

/-- The ternary diagonal prefix `[a_1,a_2,a_3]`. -/
noncomputable def lemma814FirstThreeValues
    (a : GoodBONG q L (N + 3)) : Fin 3 → K :=
  a.prefixValues 3 (by omega)

/-- The ternary prefix `[a_1,a_2,a_3]` is isotropic. -/
def Lemma814FirstThreeIsotropic
    (a : GoodBONG q L (N + 3)) : Prop :=
  ∃ x : Fin 3 → K,
    x ≠ 0 ∧ diagonalQuadratic a.lemma814FirstThreeValues x = 0

/-- The ternary prefix `[a_1,a_2,a_3]` is anisotropic. -/
def Lemma814FirstThreeAnisotropic
    (a : GoodBONG q L (N + 3)) : Prop :=
  ∀ x : Fin 3 → K,
    diagonalQuadratic a.lemma814FirstThreeValues x = 0 → x = 0

/-- The ternary complement
`[a_1,a_2,a_3,a_4] \top [b_1]` in the notation of the paper.

Here `V \top W` means a quadratic space `U` with `V ≅ W ⊥ U`; it is
not an orthogonal sum of `V` and `W`.  We therefore quantify a ternary
diagonal complement whose extension by `[b_1]` is represented by the
quaternary prefix.  Equal dimension makes that representation an isometry.
The rank proof is retained because the quaternary prefix is unavailable in
target rank three.
-/
def Lemma814FirstFourComplementAnisotropic
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfour : 4 ≤ N + 3) : Prop :=
  ∃ complement : Fin 3 → K,
    DiagonalRepresents
        (Fin.cons (b.value (0 : Fin 1)) complement)
        (a.prefixValues 4 hfour) ∧
      ∀ x : Fin 3 → K,
        diagonalQuadratic complement x = 0 → x = 0

/-- Lemma 8.14(a): the ternary prefix is anisotropic beyond the strict
`alpha_2 + d[-a_(1,3)b_1]` boundary. -/
structure Beli2019Lemma814ExceptionA
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) : Prop where
  firstThirdOrders_eq :
    a.order (0 : Fin (N + 3)) = a.order (2 : Fin (N + 3))
  defectSum_strict :
    (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) <
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) +
        a.lemma814FirstThirdCappedDefect b
  firstThree_anisotropic : a.Lemma814FirstThreeAnisotropic

/-- Lemma 8.14(b), including the additional `alpha_2 + alpha_3 > 2e`
condition only when the target rank is at least four. -/
structure Beli2019Lemma814ExceptionB
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) : Prop where
  firstThirdOrders_eq :
    a.order (0 : Fin (N + 3)) = a.order (2 : Fin (N + 3))
  residueTwo : ¬HasResidueFieldMoreThanTwoElements (K := K)
  firstAlpha_strict :
    a.alphaValue (0 : Fin (N + 2)) <
      a.halfGapValue (0 : Fin (N + 2))
  defectSum_eq :
    (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) +
        a.lemma814FirstThirdCappedDefect b =
      (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ)
  firstThree_isotropic : a.Lemma814FirstThreeIsotropic
  laterAlphaSum_strict : ∀ hfour : 4 ≤ N + 3,
    2 * (ramificationIndex K : ℚ) <
      a.alphaValue (1 : Fin (N + 2)) +
        a.alphaValue (⟨2, by omega⟩ : Fin (N + 2))

/-- Lemma 8.14(c).  The field `rank_four` makes the whole exception
unavailable in rank three; `laterAlpha_strict` is required only from rank
five onward. -/
structure Beli2019Lemma814ExceptionC
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) : Prop where
  rank_four : 4 ≤ N + 3
  firstThirdOrders_eq :
    a.order (0 : Fin (N + 3)) = a.order (2 : Fin (N + 3))
  residueTwo : ¬HasResidueFieldMoreThanTwoElements (K := K)
  secondFourthOrders_lt :
    a.order (1 : Fin (N + 3)) < a.order (⟨3, by omega⟩ : Fin (N + 3))
  firstThirdDefect_eq_alpha :
    a.lemma814FirstThirdCappedDefect b =
      (a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) : WithTop ℚ)
  thirdAlpha_eq_halfGap :
    a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) =
      a.halfGapValue (⟨2, by omega⟩ : Fin (N + 2))
  firstFourDefect_eq_secondAlpha :
    a.lemma814FirstFourCappedDefect rank_four =
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ)
  secondAlpha_eq_complement :
    a.alphaValue (1 : Fin (N + 2)) =
      a.lemma814ThirdComplementaryDefect rank_four
  firstFourComplement_anisotropic :
    a.Lemma814FirstFourComplementAnisotropic b rank_four
  laterAlpha_strict : ∀ hfive : 5 ≤ N + 3,
    a.lemma814ThirdComplementaryDefect rank_four <
      a.alphaValue (⟨3, by omega⟩ : Fin (N + 2))

/-- The disjunction of the three exceptional cases in Lemma 8.14. -/
def Beli2019Lemma814Exceptional
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) : Prop :=
  a.Beli2019Lemma814ExceptionA b ∨
    a.Beli2019Lemma814ExceptionB b ∨
      a.Beli2019Lemma814ExceptionC b

/-- A good BONG of the same target lattice whose first scalar value is the
prescribed unary value `b_1`. -/
structure Beli2019PrescribedFirstValueTransform
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) where
  transformed : GoodBONG q L (N + 3)
  firstValue_eq :
    transformed.valueUnit (0 : Fin (N + 3)) =
      b.valueUnit (0 : Fin 1)

/-- The equivalence established in the proof of Lemma 8.14. -/
def Beli2019Lemma814Claim
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) : Prop :=
  Nonempty (a.Beli2019PrescribedFirstValueTransform b) ↔
    ¬a.Beli2019Lemma814Exceptional b

/-- The literal paper-facing statement: equal first orders and
`[b_1] <= M` imply the Lemma 8.14 equivalence. -/
def Beli2019Lemma814Statement
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) : Prop :=
  a.order (0 : Fin (N + 3)) = b.order (0 : Fin 1) →
    Lattice.Represents q r L M →
      a.Beli2019Lemma814Claim b

/-- The noncircular proof target used before the final representation
theorem: replace `[b_1] <= M` by the explicit clauses of Lemma 8.13. -/
def Beli2019Lemma814ExplicitStatement
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) : Prop :=
  a.order (0 : Fin (N + 3)) = b.order (0 : Fin 1) →
    Lemma813Conditions a b →
      a.Beli2019Lemma814Claim b

/-- The explicit Section 8 proof target yields the literal statement once
the main-theorem equivalence is supplied.  Keeping the equivalence as an
argument exposes, rather than hides, the final Section 9 dependency. -/
theorem lemma814Statement_of_explicit
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (ambient : q.Represents r)
    (mainTheorem :
      Lattice.Represents q r L M ↔
        RepresentationConditions a b (Nat.zero_le (N + 2)))
    (explicit : a.Beli2019Lemma814ExplicitStatement b) :
    a.Beli2019Lemma814Statement b := by
  intro hfirst represented
  apply explicit hfirst
  exact (a.beli2019Lemma813 b hfirst ambient mainTheorem).mp represented

/-- Isotropy and anisotropy of the ternary prefix cannot occur together. -/
theorem not_firstThreeIsotropic_of_anisotropic
    (a : GoodBONG q L (N + 3))
    (han : a.Lemma814FirstThreeAnisotropic) :
    ¬a.Lemma814FirstThreeIsotropic := by
  rintro ⟨x, hx, hzero⟩
  exact hx (han x hzero)

/-- Conversely, absence of a nonzero isotropic vector is exactly the
anisotropy predicate used in exception (a). -/
theorem not_firstThreeIsotropic_iff_anisotropic
    (a : GoodBONG q L (N + 3)) :
    ¬a.Lemma814FirstThreeIsotropic ↔
      a.Lemma814FirstThreeAnisotropic := by
  constructor
  · intro h x hzero
    by_contra hx
    exact h ⟨x, hx, hzero⟩
  · exact a.not_firstThreeIsotropic_of_anisotropic

/-- Exceptions (a) and (b) are disjoint, independently of their numerical
strict/equality boundary. -/
theorem lemma814_exceptionA_not_exceptionB
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (A : a.Beli2019Lemma814ExceptionA b) :
    ¬a.Beli2019Lemma814ExceptionB b := by
  intro B
  exact a.not_firstThreeIsotropic_of_anisotropic A.firstThree_anisotropic
    B.firstThree_isotropic

/-- Exception (c) is definitionally unavailable in target rank three. -/
theorem not_lemma814ExceptionC_of_rank_three
    (a : GoodBONG q L 3) (b : GoodBONG r M 1) :
    ¬Beli2019Lemma814ExceptionC (N := 0) a b := by
  intro C
  exact (by omega : ¬4 ≤ 0 + 3) C.rank_four

/-- The last inequality in exception (b) is vacuous in target rank three. -/
theorem lemma814_exceptionB_rankThree_tail_vacuous
    (a : GoodBONG q L 3) (b : GoodBONG r M 1)
    (_B : Beli2019Lemma814ExceptionB (N := 0) a b) :
    ∀ hfour : 4 ≤ 3,
      2 * (ramificationIndex K : ℚ) <
        a.alphaValue (1 : Fin 2) +
          a.alphaValue (⟨2, by omega⟩ : Fin 2) := by
  intro hfour
  omega

/-- The last inequality in exception (c) is vacuous in target rank four. -/
theorem lemma814_exceptionC_rankFour_tail_vacuous
    (a : GoodBONG q L 4) (b : GoodBONG r M 1)
    (C : Beli2019Lemma814ExceptionC (N := 1) a b) :
    ∀ hfive : 5 ≤ 4,
      a.lemma814ThirdComplementaryDefect C.rank_four <
        a.alphaValue (⟨3, by omega⟩ : Fin 3) := by
  intro hfive
  omega

end BONG.GoodBONG

end Bong
