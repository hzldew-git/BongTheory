/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019IndexPOrderJordanBlock

/-!
# Beli (2019), Section 5: an inspectable certificate for condition 2.1(i)

The proof of condition 2.1(i) has two outcomes at each coordinate.  Either
the source order is directly at most the target order, or both coordinates
lie in alternating Jordan pairs of a common scale.  In the latter case the
two adjacent sums are equal.  These constructors expose the exact arithmetic
used in Section 5.4 rather than storing the desired order relation itself.
-/

namespace Bong

/-- A single coordinate of the Section 5.4 order calculation. -/
inductive Beli2019IndexPOrderCoordinateCertificate
    {n : Nat} (x y : BeliOrderSequence n Int)
    (i : Nat) (hi : i < n) : Prop
  | direct (bound : x.entry i hi ≤ y.entry i hi)
  | jordanPair
      (positive : 0 < i)
      (nextBound : i + 1 < n)
      (scale sourceNorm targetNorm : Int)
      (normBound : sourceNorm ≤ targetNorm)
      (sourceCurrent : x.entry i hi = 2 * scale - sourceNorm)
      (sourceNext : x.entry (i + 1) nextBound = sourceNorm)
      (targetPrevious : y.entry (i - 1) (by omega) = targetNorm)
      (targetCurrent : y.entry i hi = 2 * scale - targetNorm)

namespace Beli2019IndexPOrderCoordinateCertificate

/-- Every coordinate certificate gives the corresponding alternative in
Beli's order relation. -/
theorem compare {n : Nat} {x y : BeliOrderSequence n Int}
    {i : Nat} {hi : i < n}
    (C : Beli2019IndexPOrderCoordinateCertificate x y i hi) :
    x.entry i hi ≤ y.entry i hi ∨
      ∃ (positive : 0 < i) (nextBound : i + 1 < n),
        x.entry i hi + x.entry (i + 1) nextBound ≤
          y.entry (i - 1) (by omega) + y.entry i hi := by
  cases C with
  | direct bound => exact Or.inl bound
  | jordanPair positive nextBound scale sourceNorm targetNorm normBound
      sourceCurrent sourceNext targetPrevious targetCurrent =>
      refine Or.inr ⟨positive, nextBound, ?_⟩
      rw [sourceCurrent, sourceNext, targetPrevious, targetCurrent]
      omega

end Beli2019IndexPOrderCoordinateCertificate

/-- One explicit Section 5.4 coordinate certificate at every index. -/
structure Beli2019IndexPOrderCertificate
    {n : Nat} (x y : BeliOrderSequence n Int) : Prop where
  coordinate (i : Nat) (hi : i < n) :
    Beli2019IndexPOrderCoordinateCertificate x y i hi

namespace Beli2019IndexPOrderCertificate

/-- A complete Section 5.4 certificate proves condition 2.1(i)'s order
relation. -/
theorem orderLE {n : Nat} {x y : BeliOrderSequence n Int}
    (C : Beli2019IndexPOrderCertificate x y) : BeliOrderLE x y where
  rank := le_rfl
  compare := by
    intro i hi
    exact (C.coordinate i hi).compare

end Beli2019IndexPOrderCertificate

namespace BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- The Section 5.4 order certificate specialized to the two good BONGs of
an index-uniformizer inclusion. -/
structure Beli2019SectionFiveOrderData
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1)) : Prop where
  certificate : Beli2019IndexPOrderCertificate
    a.orderSequence b.orderSequence

namespace Beli2019SectionFiveOrderData

/-- The explicit Section 5.4 certificate discharges condition 2.1(i). -/
theorem orderCondition
    {a : GoodBONG q M (n + 1)} {b : GoodBONG q N (n + 1)}
    (D : Beli2019SectionFiveOrderData a b) :
    a.RepresentationOrderCondition b (Nat.le_refl n) :=
  (a.representationOrderCondition_iff b (Nat.le_refl n)).mpr
    D.certificate.orderLE

end Beli2019SectionFiveOrderData

end BONG.GoodBONG

end Bong
