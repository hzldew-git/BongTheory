/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.AlphaValueExt
import Bong.Bong.Beli2019Lemma92SegmentLift
import Bong.Bong.Beli2019Corollary811

/-!
# Beli (2019), Lemma 9.2: local-to-global reduction

The printed proof first solves rank four or rank five and then inserts that
change into the initial segment of a BONG of arbitrary rank.  A local alpha
identity is not literally a global alpha identity: the global candidate set
also sees the remaining suffix.  This file performs the missing comparison.

The projected-tail global alpha is bounded by the alpha of its initial local
segment.  The local transform identifies that segment alpha with the alpha of
the full initial block, and the latter is bounded by the one left-defect
candidate lost after deleting the head.  The general propagation lemma then
turns this bound into equality at every later index.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- The initial ternary segment of the projected tail of a rank `N + 4`
BONG. -/
noncomputable def lemma92TailInitialThreeIndex :
    AlphaLocalizationIndex (N + 2) :=
  prefixPairLocalization (N := N + 1) (⟨1, by omega⟩ : Fin (N + 2))

noncomputable def lemma92TailInitialThreeSegment
    (a : GoodBONG q L (N + 4)) :
    BONG.SegmentWitness a.tail.toBONG
      (lemma92TailInitialThreeIndex (N := N)).start
      (lemma92TailInitialThreeIndex (N := N)).length
      (lemma92TailInitialThreeIndex (N := N)).bound :=
  a.tail.toBONG.segmentWitness _ _ _

noncomputable def lemma92TailInitialThree
    (a : GoodBONG q L (N + 4)) :
    GoodBONG
      ((q.orthogonalSpace a.toBONG.head a.toBONG.head_isAnisotropic).restrict
        a.lemma92TailInitialThreeSegment.carrier
        a.lemma92TailInitialThreeSegment.nondegenerate)
      a.lemma92TailInitialThreeSegment.lattice 3 :=
  a.lemma92TailInitialThreeSegment.toGoodBONG a.tail.good

/-- Values of the preceding ternary segment are the second through fourth
ambient values. -/
theorem lemma92TailInitialThree_valueUnit_eq
    (a : GoodBONG q L (N + 4)) (i : Fin 3) :
    a.lemma92TailInitialThree.valueUnit i =
      a.valueUnit ⟨i.1 + 1, by omega⟩ := by
  let s := lemma92TailInitialThreeIndex (N := N)
  let w := a.lemma92TailInitialThreeSegment
  change w.bong.valueUnit i = a.valueUnit ⟨i.1 + 1, by omega⟩
  calc
    w.bong.valueUnit i = a.tail.toBONG.valueUnit (w.sourceIndex i) :=
      w.valueUnit_eq i
    _ = a.tail.valueUnit ⟨i.1, by omega⟩ := by
      congr 1
      apply Fin.ext
      simp only [BONG.SegmentWitness.sourceIndex_val]
      dsimp [w, lemma92TailInitialThreeSegment, s,
        lemma92TailInitialThreeIndex, prefixPairLocalization]
      omega
    _ = a.valueUnit ⟨i.1 + 1, by omega⟩ := by
      rw [a.valueUnit_goodTail]
      congr 1

/-- Lemma 2.1 bounds the projected-tail alpha by the corresponding alpha of
its initial ternary segment. -/
theorem tailAlpha_one_le_initialThree
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (N + 4)) :
    a.tail.alpha (1 : Fin (N + 2)) ≤
      a.lemma92TailInitialThree.alpha (1 : Fin 2) := by
  have h := a.tail.beli2009Lemma21_le_segmentAlpha
    (lemma92TailInitialThreeIndex (N := N))
    a.lemma92TailInitialThreeSegment
  have hpivot : (lemma92TailInitialThreeIndex (N := N)).pivotFin =
      (1 : Fin (N + 2)) := by
    apply Fin.ext
    change (lemma92TailInitialThreeIndex (N := N)).pivot =
      (1 : Fin (N + 2)).1
    dsimp [lemma92TailInitialThreeIndex, prefixPairLocalization]
  have hlocal : (lemma92TailInitialThreeIndex (N := N)).localPivot =
      (1 : Fin 2) := by
    apply Fin.ext
    change (lemma92TailInitialThreeIndex (N := N)).pivot -
        (lemma92TailInitialThreeIndex (N := N)).start = (1 : Fin 2).1
    dsimp [lemma92TailInitialThreeIndex, prefixPairLocalization]
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [hpivot, hlocal] at h
  exact h

/-- The initial quaternary segment of the projected tail of a rank `N + 5`
BONG. -/
noncomputable def lemma92TailInitialFourIndex :
    AlphaLocalizationIndex (N + 3) :=
  prefixPairLocalization (N := N + 2) (⟨2, by omega⟩ : Fin (N + 3))

noncomputable def lemma92TailInitialFourSegment
    (a : GoodBONG q L (N + 5)) :
    BONG.SegmentWitness a.tail.toBONG
      (lemma92TailInitialFourIndex (N := N)).start
      (lemma92TailInitialFourIndex (N := N)).length
      (lemma92TailInitialFourIndex (N := N)).bound :=
  a.tail.toBONG.segmentWitness _ _ _

noncomputable def lemma92TailInitialFour
    (a : GoodBONG q L (N + 5)) :
    GoodBONG
      ((q.orthogonalSpace a.toBONG.head a.toBONG.head_isAnisotropic).restrict
        a.lemma92TailInitialFourSegment.carrier
        a.lemma92TailInitialFourSegment.nondegenerate)
      a.lemma92TailInitialFourSegment.lattice 4 :=
  a.lemma92TailInitialFourSegment.toGoodBONG a.tail.good

theorem lemma92TailInitialFour_valueUnit_eq
    (a : GoodBONG q L (N + 5)) (i : Fin 4) :
    a.lemma92TailInitialFour.valueUnit i =
      a.valueUnit ⟨i.1 + 1, by omega⟩ := by
  let s := lemma92TailInitialFourIndex (N := N)
  let w := a.lemma92TailInitialFourSegment
  change w.bong.valueUnit i = a.valueUnit ⟨i.1 + 1, by omega⟩
  calc
    w.bong.valueUnit i = a.tail.toBONG.valueUnit (w.sourceIndex i) :=
      w.valueUnit_eq i
    _ = a.tail.valueUnit ⟨i.1, by omega⟩ := by
      congr 1
      apply Fin.ext
      simp only [BONG.SegmentWitness.sourceIndex_val]
      dsimp [w, lemma92TailInitialFourSegment, s,
        lemma92TailInitialFourIndex, prefixPairLocalization]
      omega
    _ = a.valueUnit ⟨i.1 + 1, by omega⟩ := by
      rw [a.valueUnit_goodTail]
      congr 1

/-- Orders of the initial quaternary segment are the first four ambient
orders. -/
theorem lemma92InitialFour_order_eq
    (a : GoodBONG q L (N + 4)) (i : Fin 4) :
    a.lemma92InitialFour.order i = a.order ⟨i.1, by omega⟩ := by
  change a.lemma92InitialFour.toBONG.order i =
    a.toBONG.order ⟨i.1, by omega⟩
  rw [BONG.order_eq_ordUnit, BONG.order_eq_ordUnit]
  exact congrArg (ordUnit K) (a.lemma92InitialFour_valueUnit_eq i)

/-- Orders of the initial rank-five segment are the first five ambient
orders. -/
theorem lemma92InitialFive_order_eq
    (a : GoodBONG q L (N + 5)) (i : Fin 5) :
    a.lemma92InitialFive.order i = a.order ⟨i.1, by omega⟩ := by
  change a.lemma92InitialFive.toBONG.order i =
    a.toBONG.order ⟨i.1, by omega⟩
  rw [BONG.order_eq_ordUnit, BONG.order_eq_ordUnit]
  exact congrArg (ordUnit K) (a.lemma92InitialFive_valueUnit_eq i)

/-- The early alternative only refers to the first four orders and therefore
is preserved by passage to the initial quaternary segment. -/
theorem lemma92InitialFour_earlyAlternative_iff
    (a : GoodBONG q L (N + 4)) :
    a.lemma92InitialFour.Lemma92EarlyAlternative ↔
      a.Lemma92EarlyAlternative := by
  have horder (i : Fin 4) := a.lemma92InitialFour_order_eq i
  have hgap : a.lemma92InitialFour.orderGap (0 : Fin 3) =
      a.orderGap (0 : Fin (N + 3)) := by
    unfold orderGap
    have hzero := horder (0 : Fin 4)
    have hone := horder (1 : Fin 4)
    change a.lemma92InitialFour.order (0 : Fin 4) =
      a.order (0 : Fin (N + 4)) at hzero
    change a.lemma92InitialFour.order (1 : Fin 4) =
      a.order (1 : Fin (N + 4)) at hone
    have hlocalSucc : Fin.succ (0 : Fin 3) = (1 : Fin 4) := Fin.ext rfl
    have hlocalCast : Fin.castSucc (0 : Fin 3) = (0 : Fin 4) := Fin.ext rfl
    have hglobalSucc : Fin.succ (0 : Fin (N + 3)) =
        (1 : Fin (N + 4)) := Fin.ext rfl
    have hglobalCast : Fin.castSucc (0 : Fin (N + 3)) =
        (0 : Fin (N + 4)) := Fin.ext rfl
    rw [hlocalSucc, hlocalCast, hglobalSucc, hglobalCast, hzero, hone]
  unfold Lemma92EarlyAlternative
  have hzero := horder (0 : Fin 4)
  have hone := horder (1 : Fin 4)
  have htwo := horder (2 : Fin 4)
  have hthree := horder (3 : Fin 4)
  change a.lemma92InitialFour.order (0 : Fin 4) =
    a.order (0 : Fin (N + 4)) at hzero
  change a.lemma92InitialFour.order (1 : Fin 4) =
    a.order (1 : Fin (N + 4)) at hone
  change a.lemma92InitialFour.order (2 : Fin 4) =
    a.order (2 : Fin (N + 4)) at htwo
  change a.lemma92InitialFour.order (3 : Fin 4) =
    a.order (3 : Fin (N + 4)) at hthree
  rw [hzero, hone, htwo, hthree, hgap]

/-- The same early alternative is preserved by the initial rank-five
segment. -/
theorem lemma92InitialFive_earlyAlternative_iff
    (a : GoodBONG q L (N + 5)) :
    a.lemma92InitialFive.Lemma92EarlyAlternative ↔
      a.Lemma92EarlyAlternative := by
  have horder (i : Fin 5) := a.lemma92InitialFive_order_eq i
  have hgap : a.lemma92InitialFive.orderGap (0 : Fin 4) =
      a.orderGap (0 : Fin (N + 4)) := by
    unfold orderGap
    have hzero := horder (0 : Fin 5)
    have hone := horder (1 : Fin 5)
    change a.lemma92InitialFive.order (0 : Fin 5) =
      a.order (0 : Fin (N + 5)) at hzero
    change a.lemma92InitialFive.order (1 : Fin 5) =
      a.order (1 : Fin (N + 5)) at hone
    have hlocalSucc : Fin.succ (0 : Fin 4) = (1 : Fin 5) := Fin.ext rfl
    have hlocalCast : Fin.castSucc (0 : Fin 4) = (0 : Fin 5) := Fin.ext rfl
    have hglobalSucc : Fin.succ (0 : Fin (N + 4)) =
        (1 : Fin (N + 5)) := Fin.ext rfl
    have hglobalCast : Fin.castSucc (0 : Fin (N + 4)) =
        (0 : Fin (N + 5)) := Fin.ext rfl
    rw [hlocalSucc, hlocalCast, hglobalSucc, hglobalCast, hzero, hone]
  unfold Lemma92EarlyAlternative
  have hzero := horder (0 : Fin 5)
  have hone := horder (1 : Fin 5)
  have htwo := horder (2 : Fin 5)
  have hthree := horder (3 : Fin 5)
  change a.lemma92InitialFive.order (0 : Fin 5) =
    a.order (0 : Fin (N + 5)) at hzero
  change a.lemma92InitialFive.order (1 : Fin 5) =
    a.order (1 : Fin (N + 5)) at hone
  change a.lemma92InitialFive.order (2 : Fin 5) =
    a.order (2 : Fin (N + 5)) at htwo
  change a.lemma92InitialFive.order (3 : Fin 5) =
    a.order (3 : Fin (N + 5)) at hthree
  rw [hzero, hone, htwo, hthree, hgap]

theorem tailAlpha_two_le_initialFour
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (N + 5)) :
    a.tail.alpha (2 : Fin (N + 3)) ≤
      a.lemma92TailInitialFour.alpha (2 : Fin 3) := by
  have h := a.tail.beli2009Lemma21_le_segmentAlpha
    (lemma92TailInitialFourIndex (N := N))
    a.lemma92TailInitialFourSegment
  have hpivot : (lemma92TailInitialFourIndex (N := N)).pivotFin =
      (2 : Fin (N + 3)) := by
    apply Fin.ext
    change (lemma92TailInitialFourIndex (N := N)).pivot =
      (2 : Fin (N + 3)).1
    dsimp [lemma92TailInitialFourIndex, prefixPairLocalization]
    rw [Nat.mod_eq_of_lt (by omega)]
  have hlocal : (lemma92TailInitialFourIndex (N := N)).localPivot =
      (2 : Fin 3) := by
    apply Fin.ext
    change (lemma92TailInitialFourIndex (N := N)).pivot -
        (lemma92TailInitialFourIndex (N := N)).start = (2 : Fin 3).1
    dsimp [lemma92TailInitialFourIndex, prefixPairLocalization]
  rw [hpivot, hlocal] at h
  exact h

/-- Beli (2003), Lemma 4.9(ii), inserts an arbitrary replacement of the
initial quaternary segment and records its scalar values. -/
theorem exists_initialFourReplacement
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L (N + 4))
    (c : GoodBONG
      (q.restrict a.lemma92InitialFourSegment.carrier
        a.lemma92InitialFourSegment.nondegenerate)
      a.lemma92InitialFourSegment.lattice 4) :
    ∃ d : GoodBONG q L (N + 4), ∀ i : Fin 4,
      d.valueUnit ⟨i.1, by omega⟩ = c.valueUnit i := by
  rcases a.toBONG.beliLemma49_ii a.good a.lemma92InitialFourSegment
      c.toBONG c.good with ⟨replacement⟩
  let d : GoodBONG q L (N + 4) := ⟨replacement.bong, replacement.good⟩
  refine ⟨d, ?_⟩
  intro i
  apply Units.ext
  change replacement.bong.value ⟨i.1, by omega⟩ = c.toBONG.value i
  rw [← replacement.bong.quadratic_ambientVector,
    ← c.toBONG.quadratic_ambientVector]
  have hinside := replacement.inside_eq i
  have hindex : (⟨0 + i.1, by omega⟩ : Fin (N + 4)) =
      ⟨i.1, by omega⟩ := Fin.ext (by simp)
  rw [hindex] at hinside
  exact congrArg q.quadratic hinside

/-- The analogous insertion theorem for the initial rank-five segment. -/
theorem exists_initialFiveReplacement
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L (N + 5))
    (c : GoodBONG
      (q.restrict a.lemma92InitialFiveSegment.carrier
        a.lemma92InitialFiveSegment.nondegenerate)
      a.lemma92InitialFiveSegment.lattice 5) :
    ∃ d : GoodBONG q L (N + 5), ∀ i : Fin 5,
      d.valueUnit ⟨i.1, by omega⟩ = c.valueUnit i := by
  rcases a.toBONG.beliLemma49_ii a.good a.lemma92InitialFiveSegment
      c.toBONG c.good with ⟨replacement⟩
  let d : GoodBONG q L (N + 5) := ⟨replacement.bong, replacement.good⟩
  refine ⟨d, ?_⟩
  intro i
  apply Units.ext
  change replacement.bong.value ⟨i.1, by omega⟩ = c.toBONG.value i
  rw [← replacement.bong.quadratic_ambientVector,
    ← c.toBONG.quadratic_ambientVector]
  have hinside := replacement.inside_eq i
  have hindex : (⟨0 + i.1, by omega⟩ : Fin (N + 5)) =
      ⟨i.1, by omega⟩ := Fin.ext (by simp)
  rw [hindex] at hinside
  exact congrArg q.quadratic hinside

/-- The lost first left-defect candidate is unchanged when an initial
quaternary replacement is inserted. -/
theorem initialFour_leftCandidate_eq
    {a d : GoodBONG q L (N + 4)}
    (c : GoodBONG
      (q.restrict a.lemma92InitialFourSegment.carrier
        a.lemma92InitialFourSegment.nondegenerate)
      a.lemma92InitialFourSegment.lattice 4)
    (hvalues : ∀ i : Fin 4, d.valueUnit ⟨i.1, by omega⟩ = c.valueUnit i) :
    d.leftDefectCandidate (2 : Fin (N + 3)) (0 : Fin (N + 3)) =
      c.leftDefectCandidate (2 : Fin 3) (0 : Fin 3) := by
  have horder (i : Fin 4) :
      d.order ⟨i.1, by omega⟩ = c.order i := by
    change d.toBONG.order ⟨i.1, by omega⟩ = c.toBONG.order i
    rw [BONG.order_eq_ordUnit, BONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) (hvalues i)
  have hadjacent :
      d.adjacentDefect (0 : Fin (N + 3)) =
        c.adjacentDefect (0 : Fin 3) := by
    unfold adjacentDefect
    congr 1
    unfold adjacentProduct
    change
      -(d.valueUnit (⟨0, by omega⟩ : Fin (N + 4)) *
          d.valueUnit (⟨1, by omega⟩ : Fin (N + 4))) =
        -(c.valueUnit (0 : Fin 4) * c.valueUnit (1 : Fin 4))
    have hvzero := hvalues (0 : Fin 4)
    have hvone := hvalues (1 : Fin 4)
    change d.valueUnit (⟨0, by omega⟩ : Fin (N + 4)) =
      c.valueUnit (0 : Fin 4) at hvzero
    change d.valueUnit (⟨1, by omega⟩ : Fin (N + 4)) =
      c.valueUnit (1 : Fin 4) at hvone
    rw [hvzero, hvone]
  unfold leftDefectCandidate
  change
    (((d.order (⟨3, by omega⟩ : Fin (N + 4)) -
        d.order (⟨0, by omega⟩ : Fin (N + 4)) : Int) : ℚ) : WithTop ℚ) +
        d.adjacentDefect (0 : Fin (N + 3)) =
      ((((c.order (3 : Fin 4) - c.order (0 : Fin 4) : Int) : ℚ) :
        WithTop ℚ) + c.adjacentDefect (0 : Fin 3))
  have hothree := horder (3 : Fin 4)
  have hozero := horder (0 : Fin 4)
  change d.order (⟨3, by omega⟩ : Fin (N + 4)) =
    c.order (3 : Fin 4) at hothree
  change d.order (⟨0, by omega⟩ : Fin (N + 4)) =
    c.order (0 : Fin 4) at hozero
  rw [hothree, hozero, hadjacent]

/-- Rank-five version of the preceding candidate identity. -/
theorem initialFive_leftCandidate_eq
    {a d : GoodBONG q L (N + 5)}
    (c : GoodBONG
      (q.restrict a.lemma92InitialFiveSegment.carrier
        a.lemma92InitialFiveSegment.nondegenerate)
      a.lemma92InitialFiveSegment.lattice 5)
    (hvalues : ∀ i : Fin 5, d.valueUnit ⟨i.1, by omega⟩ = c.valueUnit i) :
    d.leftDefectCandidate (3 : Fin (N + 4)) (0 : Fin (N + 4)) =
      c.leftDefectCandidate (3 : Fin 4) (0 : Fin 4) := by
  have horder (i : Fin 5) :
      d.order ⟨i.1, by omega⟩ = c.order i := by
    change d.toBONG.order ⟨i.1, by omega⟩ = c.toBONG.order i
    rw [BONG.order_eq_ordUnit, BONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) (hvalues i)
  have hadjacent :
      d.adjacentDefect (0 : Fin (N + 4)) =
        c.adjacentDefect (0 : Fin 4) := by
    unfold adjacentDefect
    congr 1
    unfold adjacentProduct
    change
      -(d.valueUnit (⟨0, by omega⟩ : Fin (N + 5)) *
          d.valueUnit (⟨1, by omega⟩ : Fin (N + 5))) =
        -(c.valueUnit (0 : Fin 5) * c.valueUnit (1 : Fin 5))
    have hvzero := hvalues (0 : Fin 5)
    have hvone := hvalues (1 : Fin 5)
    change d.valueUnit (⟨0, by omega⟩ : Fin (N + 5)) =
      c.valueUnit (0 : Fin 5) at hvzero
    change d.valueUnit (⟨1, by omega⟩ : Fin (N + 5)) =
      c.valueUnit (1 : Fin 5) at hvone
    rw [hvzero, hvone]
  unfold leftDefectCandidate
  change
    (((d.order (⟨4, by omega⟩ : Fin (N + 5)) -
        d.order (⟨0, by omega⟩ : Fin (N + 5)) : Int) : ℚ) : WithTop ℚ) +
        d.adjacentDefect (0 : Fin (N + 4)) =
      ((((c.order (4 : Fin 5) - c.order (0 : Fin 5) : Int) : ℚ) :
        WithTop ℚ) + c.adjacentDefect (0 : Fin 4))
  have hofour := horder (4 : Fin 5)
  have hozero := horder (0 : Fin 5)
  change d.order (⟨4, by omega⟩ : Fin (N + 5)) =
    c.order (4 : Fin 5) at hofour
  change d.order (⟨0, by omega⟩ : Fin (N + 5)) =
    c.order (0 : Fin 5) at hozero
  rw [hofour, hozero, hadjacent]

set_option maxHeartbeats 800000 in
-- Several segment index transports and two finite-candidate comparisons are
-- elaborated in this proof.
/-- A completed rank-four transform of the initial segment gives the full
Lemma 9.2 transform in every higher rank. -/
theorem exists_lemma92Transform_of_initialFourTransform
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L (N + 4))
    (T : Beli2019Lemma92Transform a.lemma92InitialFour)
    (hlocalEarly : a.lemma92InitialFour.Lemma92EarlyAlternative) :
    Nonempty (Beli2019Lemma92Transform a) := by
  rcases a.exists_initialFourReplacement T.transformed with ⟨d, hvalues⟩
  have hfirst : d.valueUnit (0 : Fin (N + 4)) =
      a.valueUnit (0 : Fin (N + 4)) := by
    calc
      d.valueUnit (0 : Fin (N + 4)) =
          T.transformed.valueUnit (0 : Fin 4) := hvalues 0
      _ = a.lemma92InitialFour.valueUnit (0 : Fin 4) := T.firstValue_eq
      _ = a.valueUnit (0 : Fin (N + 4)) :=
        a.lemma92InitialFour_valueUnit_eq 0
  have htailValues (i : Fin 3) :
      d.lemma92TailInitialThree.valueUnit i =
        T.transformed.tail.valueUnit i := by
    calc
      d.lemma92TailInitialThree.valueUnit i =
          d.valueUnit ⟨i.1 + 1, by omega⟩ :=
        d.lemma92TailInitialThree_valueUnit_eq i
      _ = T.transformed.valueUnit i.succ := by
        have hindex : (⟨i.1 + 1, by omega⟩ : Fin (N + 4)) =
            ⟨i.succ.1, by omega⟩ := Fin.ext (by simp)
        rw [hindex]
        exact hvalues i.succ
      _ = T.transformed.tail.valueUnit i :=
        (T.transformed.valueUnit_goodTail i).symm
  have htailAlpha :
      d.lemma92TailInitialThree.alpha (1 : Fin 2) =
        T.transformed.tail.alpha (1 : Fin 2) :=
    d.lemma92TailInitialThree.alpha_eq_of_valueUnits_eq
      T.transformed.tail htailValues (1 : Fin 2)
  have hlocalEquality :
      T.transformed.alpha (2 : Fin 3) =
        T.transformed.tail.alpha (1 : Fin 2) := by
    have hq : T.transformed.alphaValue (2 : Fin 3) =
        T.transformed.tail.alphaValue (1 : Fin 2) := by
      calc
        T.transformed.alphaValue (2 : Fin 3) =
            a.lemma92InitialFour.alphaValue (2 : Fin 3) :=
          (a.lemma92InitialFour.alpha_invariant T.transformed
            (2 : Fin 3)).symm
        _ = T.transformed.tail.alphaValue (1 : Fin 2) :=
          T.earlyAlpha_eq_tail hlocalEarly
    rw [← T.transformed.coe_alphaValue, ← T.transformed.tail.coe_alphaValue]
    exact congrArg (fun x : ℚ => (x : WithTop ℚ)) hq
  have hlocalBound :
      T.transformed.alpha (2 : Fin 3) ≤
        T.transformed.leftDefectCandidate (2 : Fin 3) (0 : Fin 3) :=
    T.transformed.alpha_le_leftDefectCandidate (Fin.zero_le _)
  have hcandidate := initialFour_leftCandidate_eq
    (a := a) (d := d) T.transformed hvalues
  have hfirstBound : d.tail.alpha (1 : Fin (N + 2)) ≤
      d.leftDefectCandidate (2 : Fin (N + 3)) (0 : Fin (N + 3)) := by
    calc
      d.tail.alpha (1 : Fin (N + 2)) ≤
          d.lemma92TailInitialThree.alpha (1 : Fin 2) :=
        d.tailAlpha_one_le_initialThree
      _ = T.transformed.tail.alpha (1 : Fin 2) := htailAlpha
      _ = T.transformed.alpha (2 : Fin 3) := hlocalEquality.symm
      _ ≤ T.transformed.leftDefectCandidate (2 : Fin 3) (0 : Fin 3) :=
        hlocalBound
      _ = d.leftDefectCandidate (2 : Fin (N + 3))
          (0 : Fin (N + 3)) := hcandidate.symm
  have hbase : d.alphaValue (2 : Fin (N + 3)) =
      d.tail.alphaValue (1 : Fin (N + 2)) := by
    apply WithTop.coe_injective
    rw [d.coe_alphaValue, d.tail.coe_alphaValue]
    exact le_antisymm (d.alpha_shift_le_tail (1 : Fin (N + 2)))
      (d.tailAlpha_le_shift_of_firstLeftDefectBound
        (1 : Fin (N + 2)) hfirstBound)
  exact exists_lemma92Transform_of_earlyBaseAgreement a d hfirst hbase

set_option maxHeartbeats 800000 in
-- The rank-five proof has the same dependent segment transports at one more
-- coefficient.
/-- A completed rank-five transform of the initial segment gives the full
Lemma 9.2 transform when the early alternative is absent. -/
theorem exists_lemma92Transform_of_initialFiveTransform
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L (N + 5))
    (T : Beli2019Lemma92Transform a.lemma92InitialFive)
    (hnotEarly : ¬a.Lemma92EarlyAlternative) :
    Nonempty (Beli2019Lemma92Transform a) := by
  rcases a.exists_initialFiveReplacement T.transformed with ⟨d, hvalues⟩
  have hfirst : d.valueUnit (0 : Fin (N + 5)) =
      a.valueUnit (0 : Fin (N + 5)) := by
    calc
      d.valueUnit (0 : Fin (N + 5)) =
          T.transformed.valueUnit (0 : Fin 5) := hvalues 0
      _ = a.lemma92InitialFive.valueUnit (0 : Fin 5) := T.firstValue_eq
      _ = a.valueUnit (0 : Fin (N + 5)) :=
        a.lemma92InitialFive_valueUnit_eq 0
  have htailValues (i : Fin 4) :
      d.lemma92TailInitialFour.valueUnit i =
        T.transformed.tail.valueUnit i := by
    calc
      d.lemma92TailInitialFour.valueUnit i =
          d.valueUnit ⟨i.1 + 1, by omega⟩ :=
        d.lemma92TailInitialFour_valueUnit_eq i
      _ = T.transformed.valueUnit i.succ := by
        have hindex : (⟨i.1 + 1, by omega⟩ : Fin (N + 5)) =
            ⟨i.succ.1, by omega⟩ := Fin.ext (by simp)
        rw [hindex]
        exact hvalues i.succ
      _ = T.transformed.tail.valueUnit i :=
        (T.transformed.valueUnit_goodTail i).symm
  have htailAlpha :
      d.lemma92TailInitialFour.alpha (2 : Fin 3) =
        T.transformed.tail.alpha (2 : Fin 3) :=
    d.lemma92TailInitialFour.alpha_eq_of_valueUnits_eq
      T.transformed.tail htailValues (2 : Fin 3)
  have hlocalEquality :
      T.transformed.alpha (3 : Fin 4) =
        T.transformed.tail.alpha (2 : Fin 3) := by
    have hq : T.transformed.alphaValue (3 : Fin 4) =
        T.transformed.tail.alphaValue (2 : Fin 3) := by
      calc
        T.transformed.alphaValue (3 : Fin 4) =
            a.lemma92InitialFive.alphaValue (3 : Fin 4) :=
          (a.lemma92InitialFive.alpha_invariant T.transformed
            (3 : Fin 4)).symm
        _ = T.transformed.tail.alphaValue (2 : Fin 3) :=
          T.laterAlpha_eq_tail (2 : Fin 3) (by norm_num)
    rw [← T.transformed.coe_alphaValue, ← T.transformed.tail.coe_alphaValue]
    exact congrArg (fun x : ℚ => (x : WithTop ℚ)) hq
  have hlocalBound :
      T.transformed.alpha (3 : Fin 4) ≤
        T.transformed.leftDefectCandidate (3 : Fin 4) (0 : Fin 4) :=
    T.transformed.alpha_le_leftDefectCandidate (Fin.zero_le _)
  have hcandidate := initialFive_leftCandidate_eq
    (a := a) (d := d) T.transformed hvalues
  have hfirstBound : d.tail.alpha (2 : Fin (N + 3)) ≤
      d.leftDefectCandidate (3 : Fin (N + 4)) (0 : Fin (N + 4)) := by
    calc
      d.tail.alpha (2 : Fin (N + 3)) ≤
          d.lemma92TailInitialFour.alpha (2 : Fin 3) :=
        d.tailAlpha_two_le_initialFour
      _ = T.transformed.tail.alpha (2 : Fin 3) := htailAlpha
      _ = T.transformed.alpha (3 : Fin 4) := hlocalEquality.symm
      _ ≤ T.transformed.leftDefectCandidate (3 : Fin 4) (0 : Fin 4) :=
        hlocalBound
      _ = d.leftDefectCandidate (3 : Fin (N + 4))
          (0 : Fin (N + 4)) := hcandidate.symm
  have hbase : d.alphaValue (3 : Fin (N + 4)) =
      d.tail.alphaValue (2 : Fin (N + 3)) := by
    apply WithTop.coe_injective
    rw [d.coe_alphaValue, d.tail.coe_alphaValue]
    exact le_antisymm (d.alpha_shift_le_tail (2 : Fin (N + 3)))
      (d.tailAlpha_le_shift_of_firstLeftDefectBound
        (2 : Fin (N + 3)) hfirstBound)
  exact exists_lemma92Transform_of_laterBaseAgreement
    a d hfirst hnotEarly hbase

/-- For every rank at least five, the full theorem is reduced exactly to the
rank-four solver in the early branch and the rank-five solver in its
complement. -/
theorem exists_lemma92Transform_of_initialLowRankTransforms
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L (N + 5))
    (Tfour : Nonempty
      (Beli2019Lemma92Transform a.lemma92InitialFour))
    (Tfive : Nonempty
      (Beli2019Lemma92Transform a.lemma92InitialFive)) :
    Nonempty (Beli2019Lemma92Transform a) := by
  by_cases hearly : a.Lemma92EarlyAlternative
  · rcases Tfour with ⟨T⟩
    exact a.exists_lemma92Transform_of_initialFourTransform T
      (a.lemma92InitialFour_earlyAlternative_iff.mpr hearly)
  · rcases Tfive with ⟨T⟩
    exact a.exists_lemma92Transform_of_initialFiveTransform T hearly

end BONG.GoodBONG

end Bong
