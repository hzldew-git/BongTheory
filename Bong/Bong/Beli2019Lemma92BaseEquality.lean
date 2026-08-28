/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma92Propagation
import Bong.Bong.DiagonalTernaryScaling

/-!
# Beli (2019), Lemma 9.2: the two base equalities

The explicit coefficient changes in ranks four and five are only needed to
make the final adjacent defect of a short initial block equal to the preceding
alpha.  The local formula for alpha then gives the head-deletion equality at
the last boundary of that block.  This file isolates that common argument and
records faithful certificates for the two scaling patterns in the paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n N : Nat}

/-- If the next adjacent defect equals `alpha_p` and
`alpha_(p+1) = orderGap_(p+1) + alpha_p`, then deleting the head does not
change `alpha_(p+1)`. -/
theorem alphaValue_shift_eq_tail_of_nextAdjacentDefect
    (c : GoodBONG q L (n + 3)) (p : Fin (n + 1))
    (hrelation : c.alphaValue p.succ =
      (c.orderGap p.succ : ℚ) + c.alphaValue p.castSucc)
    (hdefect : c.adjacentDefect p.succ =
      (c.alphaValue p.castSucc : WithTop ℚ)) :
    c.alphaValue p.succ = c.tail.alphaValue p := by
  have htailCandidate := c.tail.alpha_le_leftDefectCandidate
    (i := p) (j := p) le_rfl
  rw [c.leftDefectCandidate_tail] at htailCandidate
  have hcandidate :
      c.leftDefectCandidate p.succ p.succ =
        (c.alphaValue p.succ : WithTop ℚ) := by
    unfold leftDefectCandidate
    change ((c.orderGap p.succ : ℚ) : WithTop ℚ) +
      c.adjacentDefect p.succ = (c.alphaValue p.succ : WithTop ℚ)
    rw [hdefect, ← WithTop.coe_add, hrelation]
  have htailLe : c.tail.alpha p ≤ c.alpha p.succ := by
    exact htailCandidate.trans_eq
      (hcandidate.trans (c.coe_alphaValue p.succ))
  apply WithTop.coe_injective
  rw [c.coe_alphaValue, c.tail.coe_alphaValue]
  exact le_antisymm (c.alpha_shift_le_tail p) htailLe

/-- Same-lattice alpha and order invariance transports the numerical relation
from the original good BONG to a transformed one. -/
theorem alphaValue_shift_eq_tail_of_invariant_nextAdjacentDefect
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a c : GoodBONG q L (n + 3)) (p : Fin (n + 1))
    (hrelation : a.alphaValue p.succ =
      (a.orderGap p.succ : ℚ) + a.alphaValue p.castSucc)
    (hdefect : c.adjacentDefect p.succ =
      (a.alphaValue p.castSucc : WithTop ℚ)) :
    c.alphaValue p.succ = c.tail.alphaValue p := by
  have horders := a.order_invariant c
  have halphas := a.alpha_invariant c
  have hgap : a.orderGap p.succ = c.orderGap p.succ := by
    unfold orderGap
    rw [horders p.succ.succ, horders p.succ.castSucc]
  have hrelationC : c.alphaValue p.succ =
      (c.orderGap p.succ : ℚ) + c.alphaValue p.castSucc := by
    rw [← halphas p.succ, ← halphas p.castSucc, ← hgap]
    exact hrelation
  have hdefectC : c.adjacentDefect p.succ =
      (c.alphaValue p.castSucc : WithTop ℚ) := by
    rw [← halphas p.castSucc]
    exact hdefect
  exact c.alphaValue_shift_eq_tail_of_nextAdjacentDefect
    p hrelationC hdefectC

/-- The rank-four coefficient pattern
`[a₁,a₂,a₃,a₄] -> [a₁,εa₂,εηa₃,ηa₄]`,
realized by a good BONG of the same full lattice. -/
structure Lemma92EarlyScalingData
    (a : GoodBONG q L (N + 4)) (ε η : Kˣ) where
  transformed : GoodBONG q L (N + 4)
  firstValue_eq : transformed.valueUnit (0 : Fin (N + 4)) =
    a.valueUnit (0 : Fin (N + 4))
  secondValue_eq : transformed.valueUnit (1 : Fin (N + 4)) =
    ε * a.valueUnit (1 : Fin (N + 4))
  thirdValue_eq : transformed.valueUnit (2 : Fin (N + 4)) =
    ε * η * a.valueUnit (2 : Fin (N + 4))
  fourthValue_eq : transformed.valueUnit (3 : Fin (N + 4)) =
    η * a.valueUnit (3 : Fin (N + 4))

namespace Lemma92EarlyScalingData

/-- The square factor `η²` drops out of the final adjacent defect of the
scaled initial quaternary block. -/
theorem adjacentDefect_two
    [QuadraticDefectLaws K]
    {a : GoodBONG q L (N + 4)} {ε η : Kˣ}
    (D : Lemma92EarlyScalingData a ε η) :
    D.transformed.adjacentDefect (2 : Fin (N + 3)) =
      defectOrder (K := K)
        (-(ε * a.valueUnit (2 : Fin (N + 4)) *
          a.valueUnit (3 : Fin (N + 4)))) := by
  unfold adjacentDefect adjacentProduct
  change defectOrder
      (-(D.transformed.valueUnit (2 : Fin (N + 4)) *
        D.transformed.valueUnit (3 : Fin (N + 4)))) = _
  rw [D.thirdValue_eq, D.fourthValue_eq]
  have hproduct :
      -((ε * η * a.valueUnit (2 : Fin (N + 4))) *
          (η * a.valueUnit (3 : Fin (N + 4)))) =
        (- (ε * a.valueUnit (2 : Fin (N + 4)) *
          a.valueUnit (3 : Fin (N + 4)))) * η ^ 2 := by
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hproduct, defectOrder_mul_square]

/-- The early scaling certificate, the paper's alpha recursion, and the
chosen defect of `ε` give the rank-four base equality and hence all of
Lemma 9.2's required equalities. -/
theorem exists_lemma92Transform
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L (N + 4)} {ε η : Kˣ}
    (D : Lemma92EarlyScalingData a ε η)
    (hrelation : a.alphaValue (2 : Fin (N + 3)) =
      (a.orderGap (2 : Fin (N + 3)) : ℚ) +
        a.alphaValue (1 : Fin (N + 3)))
    (hdefect : defectOrder (K := K)
        (-(ε * a.valueUnit (2 : Fin (N + 4)) *
          a.valueUnit (3 : Fin (N + 4)))) =
      (a.alphaValue (1 : Fin (N + 3)) : WithTop ℚ)) :
    Nonempty (Beli2019Lemma92Transform a) := by
  have hbase : D.transformed.alphaValue (2 : Fin (N + 3)) =
      D.transformed.tail.alphaValue (1 : Fin (N + 2)) := by
    apply alphaValue_shift_eq_tail_of_invariant_nextAdjacentDefect
      (a := a) (c := D.transformed) (p := (1 : Fin (N + 2)))
    · exact hrelation
    · have hnext : Fin.succ (1 : Fin (N + 2)) =
          (2 : Fin (N + 3)) := Fin.ext rfl
      have hprevious : Fin.castSucc (1 : Fin (N + 2)) =
          (1 : Fin (N + 3)) := Fin.ext rfl
      rw [hnext, hprevious, D.adjacentDefect_two]
      exact hdefect
  exact exists_lemma92Transform_of_earlyBaseAgreement
    a D.transformed D.firstValue_eq hbase

end Lemma92EarlyScalingData

/-- The rank-five coefficient pattern
`[a₁,a₂,a₃,a₄,a₅] -> [a₁,a₂,εa₃,εηa₄,ηa₅]`,
realized by a good BONG of the same full lattice. -/
structure Lemma92LaterScalingData
    (a : GoodBONG q L (N + 5)) (ε η : Kˣ) where
  transformed : GoodBONG q L (N + 5)
  firstValue_eq : transformed.valueUnit (0 : Fin (N + 5)) =
    a.valueUnit (0 : Fin (N + 5))
  secondValue_eq : transformed.valueUnit (1 : Fin (N + 5)) =
    a.valueUnit (1 : Fin (N + 5))
  thirdValue_eq : transformed.valueUnit (2 : Fin (N + 5)) =
    ε * a.valueUnit (2 : Fin (N + 5))
  fourthValue_eq : transformed.valueUnit (3 : Fin (N + 5)) =
    ε * η * a.valueUnit (3 : Fin (N + 5))
  fifthValue_eq : transformed.valueUnit (4 : Fin (N + 5)) =
    η * a.valueUnit (4 : Fin (N + 5))

namespace Lemma92LaterScalingData

/-- The square factor `η²` drops out of the final adjacent defect of the
scaled initial quinary block. -/
theorem adjacentDefect_three
    [QuadraticDefectLaws K]
    {a : GoodBONG q L (N + 5)} {ε η : Kˣ}
    (D : Lemma92LaterScalingData a ε η) :
    D.transformed.adjacentDefect (3 : Fin (N + 4)) =
      defectOrder (K := K)
        (-(ε * a.valueUnit (3 : Fin (N + 5)) *
          a.valueUnit (4 : Fin (N + 5)))) := by
  unfold adjacentDefect adjacentProduct
  change defectOrder
      (-(D.transformed.valueUnit (3 : Fin (N + 5)) *
        D.transformed.valueUnit (4 : Fin (N + 5)))) = _
  rw [D.fourthValue_eq, D.fifthValue_eq]
  have hproduct :
      -((ε * η * a.valueUnit (3 : Fin (N + 5))) *
          (η * a.valueUnit (4 : Fin (N + 5)))) =
        (- (ε * a.valueUnit (3 : Fin (N + 5)) *
          a.valueUnit (4 : Fin (N + 5)))) * η ^ 2 := by
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hproduct, defectOrder_mul_square]

/-- The later scaling certificate gives the rank-five base equality and all
later equalities in the branch where the early alternatives are absent. -/
theorem exists_lemma92Transform
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L (N + 5)} {ε η : Kˣ}
    (D : Lemma92LaterScalingData a ε η)
    (hnotEarly : ¬a.Lemma92EarlyAlternative)
    (hrelation : a.alphaValue (3 : Fin (N + 4)) =
      (a.orderGap (3 : Fin (N + 4)) : ℚ) +
        a.alphaValue (2 : Fin (N + 4)))
    (hdefect : defectOrder (K := K)
        (-(ε * a.valueUnit (3 : Fin (N + 5)) *
          a.valueUnit (4 : Fin (N + 5)))) =
      (a.alphaValue (2 : Fin (N + 4)) : WithTop ℚ)) :
    Nonempty (Beli2019Lemma92Transform a) := by
  have hbase : D.transformed.alphaValue (3 : Fin (N + 4)) =
      D.transformed.tail.alphaValue (2 : Fin (N + 3)) := by
    apply alphaValue_shift_eq_tail_of_invariant_nextAdjacentDefect
      (a := a) (c := D.transformed) (p := (2 : Fin (N + 3)))
    · exact hrelation
    · have hnext : Fin.succ (2 : Fin (N + 3)) =
          (3 : Fin (N + 4)) := Fin.ext rfl
      have hprevious : Fin.castSucc (2 : Fin (N + 3)) =
          (2 : Fin (N + 4)) := Fin.ext rfl
      rw [hnext, hprevious, D.adjacentDefect_three]
      exact hdefect
  exact exists_lemma92Transform_of_laterBaseAgreement
    a D.transformed D.firstValue_eq hnotEarly hbase

end Lemma92LaterScalingData

end BONG.GoodBONG

end Bong
