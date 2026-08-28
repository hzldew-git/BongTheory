/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma88Binary
import Bong.Bong.Beli2019GoodTailReplacement

/-!
# Beli (2019), Lemma 8.8: lifting the induction hypothesis from the tail

The induction proof first changes the first value of the projected tail and
then prepends the unchanged head.  This file packages that operation and
proves the exact defect-domination calculation which returns the proof to the
binary-prefix branch.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- The result of changing the first value of the projected tail while
retaining the original head. -/
structure Beli2019TailReplacementData (b : GoodBONG q L (N + 3)) where
  epsilon : Kˣ
  epsilon_isValuationUnit : IsValuationUnit K (epsilon : K)
  epsilon_defect :
    defectOrder (K := K) epsilon =
      (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ)
  transformed : GoodBONG q L (N + 3)
  firstValue_eq :
    transformed.valueUnit (0 : Fin (N + 3)) =
      b.valueUnit (0 : Fin (N + 3))
  secondValue_eq :
    transformed.valueUnit (1 : Fin (N + 3)) =
      epsilon * b.valueUnit (1 : Fin (N + 3))

/-- A first-value transformation of the projected tail lifts to the original
lattice with the head fixed. -/
theorem tailReplacementData_of_firstValueTransform
    [GoodBONGClassificationLaws.{u, v, v} K]
    [BeliLemma47Laws.{u, v} K]
    (b : GoodBONG q L (N + 3))
    (T : b.tail.Beli2019FirstValueTransform) :
    Nonempty b.Beli2019TailReplacementData := by
  let c := b.replaceTailGood T.transformed
  have hfirst : c.valueUnit (0 : Fin (N + 3)) =
      b.valueUnit (0 : Fin (N + 3)) := by
    apply Units.ext
    change (b.replaceTailGood T.transformed).toBONG.value 0 =
      b.toBONG.value 0
    rw [(b.replaceTailGood T.transformed).toBONG.value_zero_eq_quadratic_head,
      b.toBONG.value_zero_eq_quadratic_head,
      b.replaceTailGood_head]
  have htailValue : b.tail.valueUnit (0 : Fin (N + 2)) =
      b.valueUnit (1 : Fin (N + 3)) := by
    apply Units.ext
    change b.toBONG.tail.value 0 = b.toBONG.value 1
    rw [b.toBONG.value_tail]
    congr 1
  have hsecond : c.valueUnit (1 : Fin (N + 3)) =
      T.epsilon * b.valueUnit (1 : Fin (N + 3)) := by
    calc
      c.valueUnit (1 : Fin (N + 3)) =
          T.transformed.valueUnit (0 : Fin (N + 2)) := by
        apply Units.ext
        rw [c.coe_valueUnit, T.transformed.coe_valueUnit]
        change c.toBONG.value (1 : Fin (N + 3)) =
          T.transformed.toBONG.value (0 : Fin (N + 2))
        have hindex : (1 : Fin (N + 3)) =
            (0 : Fin (N + 2)).succ := by
          apply Fin.ext
          simp
        rw [hindex, ← c.toBONG.value_tail (0 : Fin (N + 2))]
        rfl
      _ = T.epsilon * b.tail.valueUnit (0 : Fin (N + 2)) :=
        T.firstValue_eq
      _ = T.epsilon * b.valueUnit (1 : Fin (N + 3)) :=
        congrArg (T.epsilon * ·) htailValue
  exact ⟨{
    epsilon := T.epsilon
    epsilon_isValuationUnit := T.epsilon_isValuationUnit
    epsilon_defect := T.epsilon_defect
    transformed := c
    firstValue_eq := hfirst
    secondValue_eq := hsecond
  }⟩

namespace Beli2019TailReplacementData

variable {b : GoodBONG q L (N + 3)}

/-- A first-value transformation performed after a tail replacement is also
a first-value transformation of the original good BONG.  The replacement
keeps the head fixed, while alpha invariance transports the prescribed
defect back to the original lattice. -/
noncomputable def compose_firstValueTransform
    [GoodBONGClassificationLaws.{u, v, v} K]
    (D : b.Beli2019TailReplacementData)
    (S : D.transformed.Beli2019FirstValueTransform) :
    b.Beli2019FirstValueTransform := by
  have halphas := b.alpha_invariant D.transformed
  refine {
    epsilon := S.epsilon
    epsilon_isValuationUnit := S.epsilon_isValuationUnit
    epsilon_defect := ?_
    transformed := S.transformed
    firstValue_eq := ?_
  }
  · exact S.epsilon_defect.trans
      (congrArg (fun x : ℚ => (x : WithTop ℚ))
        (halphas (0 : Fin (N + 2))).symm)
  · calc
      S.transformed.valueUnit (0 : Fin (N + 3)) =
          S.epsilon * D.transformed.valueUnit (0 : Fin (N + 3)) :=
        S.firstValue_eq
      _ = S.epsilon * b.valueUnit (0 : Fin (N + 3)) :=
        congrArg (S.epsilon * ·) D.firstValue_eq

/-- The first adjacent product is multiplied by the tail multiplier. -/
theorem firstAdjacentProduct_eq (D : b.Beli2019TailReplacementData) :
    D.transformed.adjacentProduct (0 : Fin (N + 2)) =
      D.epsilon * b.adjacentProduct (0 : Fin (N + 2)) := by
  unfold adjacentProduct
  have hfirst :
      D.transformed.valueUnit (0 : Fin (N + 2)).castSucc =
        b.valueUnit (0 : Fin (N + 2)).castSucc := by
    simpa using D.firstValue_eq
  have hsecond :
      D.transformed.valueUnit (0 : Fin (N + 2)).succ =
        D.epsilon * b.valueUnit (0 : Fin (N + 2)).succ := by
    simpa using D.secondValue_eq
  rw [hfirst, hsecond]
  apply Units.ext
  simp only [Units.val_neg, Units.val_mul]
  ring

/-- If the tail alpha is strictly smaller than the original first adjacent
defect, exact defect domination makes it the defect after tail replacement.
-/
theorem firstAdjacentDefect_eq_tailAlpha
    (D : b.Beli2019TailReplacementData)
    (hstrict :
      (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) <
        b.adjacentDefect (0 : Fin (N + 2))) :
    D.transformed.adjacentDefect (0 : Fin (N + 2)) =
      (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
  unfold adjacentDefect
  rw [D.firstAdjacentProduct_eq]
  have hstrict' :
      defectOrder (K := K) D.epsilon <
        defectOrder (K := K)
          (b.adjacentProduct (0 : Fin (N + 2))) := by
    rw [D.epsilon_defect]
    simpa only [adjacentDefect] using hstrict
  have hdom := defectOrder_mul_eq_left_of_lt_right (K := K)
    (a := D.epsilon) (b := b.adjacentProduct (0 : Fin (N + 2)))
  rw [hdom hstrict', D.epsilon_defect]

/-- The strict-tail branch of the induction returns to the binary-prefix
case: after replacement the first binary alpha is the original global alpha.
-/
theorem firstBinaryAlpha_eq_of_strict_tail
    [GoodBONGClassificationLaws.{u, v, v} K]
    (D : b.Beli2019TailReplacementData)
    (hstrict :
      (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) <
        b.adjacentDefect (0 : Fin (N + 2)))
    (hglobal :
      (b.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) =
        (((b.orderGap (0 : Fin (N + 2)) : Int) : ℚ) : WithTop ℚ) +
          (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ)) :
    D.transformed.firstBinaryAlpha =
      (b.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
  have horders := b.order_invariant D.transformed
  have hhalf :
      D.transformed.halfGapCandidate (0 : Fin (N + 2)) =
        b.halfGapCandidate (0 : Fin (N + 2)) := by
    unfold halfGapCandidate
    rw [← horders (0 : Fin (N + 2)).succ,
      ← horders (0 : Fin (N + 2)).castSucc]
  have hadjacent := D.firstAdjacentDefect_eq_tailAlpha hstrict
  have hleft :
      D.transformed.leftDefectCandidate
          (0 : Fin (N + 2)) (0 : Fin (N + 2)) =
        (b.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
    unfold leftDefectCandidate
    rw [← horders (0 : Fin (N + 2)).succ,
      ← horders (0 : Fin (N + 2)).castSucc,
      hadjacent]
    simpa only [orderGap] using hglobal.symm
  unfold firstBinaryAlpha
  rw [hhalf, hleft]
  apply min_eq_right
  rw [b.coe_alphaValue]
  exact b.alpha_le_halfGapCandidate (0 : Fin (N + 2))

end Beli2019TailReplacementData

end BONG.GoodBONG

end Bong
