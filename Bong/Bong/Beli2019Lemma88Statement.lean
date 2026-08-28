/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Remark87
import Bong.Bong.Beli2019CanonicalApproximation

/-!
# Beli (2019), Lemma 8.8: exact statement

This file gives a literal, zero-based formulation of the first-element
transformation theorem.  In particular, the qualifications "if `n ≥ 3`"
and "if `n ≥ 4`" in exceptions (b) and (c) are retained as dependent
hypotheses rather than being hidden by default values at missing indices.

The actual theorem is the equivalence `Beli2019Lemma88Claim`: a first-value
transformation exists exactly when the half-gap equality and one of the three
listed exceptions do not occur.  Subsequent files prove the two directions.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- The complementary boundary value
`e - (R₂ - R₁) / 2` occurring in exceptions (b) and (c). -/
noncomputable def lemma88ComplementaryDefect
    (b : GoodBONG q L (N + 2)) : ℚ :=
  (ramificationIndex K : ℚ) - (b.orderGap (0 : Fin (N + 1)) : ℚ) / 2

/-- The bracketed defect `d[-a₁a₂]` in Lemma 8.8. -/
noncomputable def lemma88FirstCappedDefect
    (b : GoodBONG q L (N + 2)) : WithTop ℚ :=
  b.truncatedPrefixDefect b (-1) 0 2

/-- The first alpha/adjacent-pair index in Lemma 8.8. -/
def lemma88FirstAlphaIndex : Fin (N + 1) :=
  ⟨0, by omega⟩

/-- The second alpha/adjacent-pair index, available in rank at least three.
-/
def lemma88SecondAlphaIndex (hthree : 3 ≤ N + 2) : Fin (N + 1) :=
  ⟨1, by omega⟩

/-- A rational defect value occurs on a nonzero valuation unit.  In the
paper this is the condition `d ∈ d(𝒪)`: order invariance of the transformed
first BONG value forces the multiplier to have valuation zero. -/
def IsValuationUnitDefect (d : ℚ) : Prop :=
  ∃ ε : Kˣ,
    IsValuationUnit K (ε : K) ∧
      defectOrder (K := K) ε = (d : WithTop ℚ)

/-- The first three diagonal coefficients, available only when the rank is
at least three. -/
noncomputable def lemma88FirstThreeValues
    (b : GoodBONG q L (N + 2)) (hthree : 3 ≤ N + 2) : Fin 3 → K :=
  fun i => b.value ⟨i.1, i.2.trans_le hthree⟩

/-- The diagonal ternary prefix `[a₁,a₂,a₃]` is anisotropic. -/
def Lemma88FirstThreeAnisotropic
    (b : GoodBONG q L (N + 2)) (hthree : 3 ≤ N + 2) : Prop :=
  ∀ x : Fin 3 → K,
    diagonalQuadratic (b.lemma88FirstThreeValues hthree) x = 0 → x = 0

/-- Exception (a): `α₁` does not occur as the defect of a valuation unit. -/
def Beli2019Lemma88ExceptionA (b : GoodBONG q L (N + 2)) : Prop :=
  ¬IsValuationUnitDefect (K := K) (b.alphaValue 0)

/-- Exception (b), including the paper's terminal rank-two convention. -/
structure Beli2019Lemma88ExceptionB
    (b : GoodBONG q L (N + 2)) : Prop where
  residueTwo : ¬HasResidueFieldMoreThanTwoElements (K := K)
  cappedDefect_eq :
    b.lemma88FirstCappedDefect =
      (b.lemma88ComplementaryDefect : WithTop ℚ)
  nextAlpha_strict : ∀ hthree : 3 ≤ N + 2,
    b.lemma88ComplementaryDefect <
      b.alphaValue ⟨1, by omega⟩

/-- Exception (c), with `R₁ = R₃` and anisotropy present only from rank
three onward, and the additional `α₃` inequality required only from rank
four onward. -/
structure Beli2019Lemma88ExceptionC
    (b : GoodBONG q L (N + 2)) : Prop where
  residueTwo : ¬HasResidueFieldMoreThanTwoElements (K := K)
  rank_three : 3 ≤ N + 2
  outerOrders_eq :
    b.order (0 : Fin (N + 2)) = b.order ⟨2, by omega⟩
  laterAlpha_strict : ∀ hfour : 4 ≤ N + 2,
    b.halfGapValue (0 : Fin (N + 1)) <
      b.alphaValue ⟨2, by omega⟩
  firstThree_anisotropic : b.Lemma88FirstThreeAnisotropic rank_three

/-- The complete exceptional alternative in Lemma 8.8: the first alpha
attains the half-gap bound and at least one of (a)--(c) occurs. -/
def Beli2019Lemma88Exceptional (b : GoodBONG q L (N + 2)) : Prop :=
  b.AttainsHalfGap 0 ∧
    (b.Beli2019Lemma88ExceptionA ∨
      Nonempty b.Beli2019Lemma88ExceptionB ∨
      Nonempty b.Beli2019Lemma88ExceptionC)

/-- A concrete realization of the conclusion of Lemma 8.8.  The new good
BONG belongs to the same lattice, its first value is multiplied by `ε`, and
`ε` has exactly the prescribed first alpha defect. -/
structure Beli2019FirstValueTransform
    (b : GoodBONG q L (N + 2)) where
  epsilon : Kˣ
  epsilon_isValuationUnit : IsValuationUnit K (epsilon : K)
  epsilon_defect :
    defectOrder (K := K) epsilon = (b.alphaValue 0 : WithTop ℚ)
  transformed : GoodBONG q L (N + 2)
  firstValue_eq :
    transformed.valueUnit 0 = epsilon * b.valueUnit 0

/-- The exact proposition asserted by Beli (2019), Lemma 8.8(i). -/
def Beli2019Lemma88Claim (b : GoodBONG q L (N + 2)) : Prop :=
  Nonempty b.Beli2019FirstValueTransform ↔
    ¬b.Beli2019Lemma88Exceptional

/-- Every realized first-value transformation supplies the unit-defect
witness that rules out exception (a). -/
theorem Beli2019FirstValueTransform.isValuationUnitDefect
    {b : GoodBONG q L (N + 2)}
    (T : b.Beli2019FirstValueTransform) :
    IsValuationUnitDefect (K := K) (b.alphaValue 0) :=
  ⟨T.epsilon, T.epsilon_isValuationUnit, T.epsilon_defect⟩

/-- Consequently exception (a) is impossible whenever the conclusion of
Lemma 8.8 is realized. -/
theorem Beli2019FirstValueTransform.not_exceptionA
    {b : GoodBONG q L (N + 2)}
    (T : b.Beli2019FirstValueTransform) :
    ¬b.Beli2019Lemma88ExceptionA :=
  fun h => h T.isValuationUnitDefect

/-- Exception (c) is definitionally unavailable in rank two, as required by
the parenthetical convention in the paper. -/
theorem not_lemma88ExceptionC_of_rank_two
    (b : GoodBONG q L 2) :
    ¬Nonempty (Beli2019Lemma88ExceptionC (N := 0) b) := by
  rintro ⟨C⟩
  exact (by omega : ¬3 ≤ 0 + 2) C.rank_three

/-- The two boundary quantities in Lemma 8.8 add to `2e`. -/
theorem halfGap_add_lemma88ComplementaryDefect
    (b : GoodBONG q L (N + 2)) :
    b.halfGapValue (0 : Fin (N + 1)) +
        b.lemma88ComplementaryDefect =
      2 * (ramificationIndex K : ℚ) := by
  unfold halfGapValue lemma88ComplementaryDefect
  ring

/-- The same identity with the summands in the order used in the induction
proof of Lemma 8.8. -/
theorem lemma88ComplementaryDefect_add_halfGap
    (b : GoodBONG q L (N + 2)) :
    b.lemma88ComplementaryDefect +
        b.halfGapValue (0 : Fin (N + 1)) =
      2 * (ramificationIndex K : ℚ) := by
  rw [add_comm, b.halfGap_add_lemma88ComplementaryDefect]

end BONG.GoodBONG

end Bong
