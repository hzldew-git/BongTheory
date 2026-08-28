/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019ApproximationDual

/-!
# Beli (2019), Definition 10 and Lemma 3.8

The alpha-sum triggers are proved invariant under a change of good BONG.
The remaining two local representation equivalences are isolated as explicit
per-boundary data; no new global law or default instance is introduced.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The left alpha-sum trigger in Definition 10 is independent of the good
BONG. -/
theorem leftApproximationTrigger_changeBONG_iff
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a a' : GoodBONG q L (n + 1)) (i : Fin n) :
    a.leftApproximationTrigger i ↔ a'.leftApproximationTrigger i := by
  have halpha : a.SameAlphas a' := (a.order_alpha_invariant a').2
  unfold leftApproximationTrigger
  constructor
  · rintro (hzero | ⟨hi, hsum⟩)
    · exact Or.inl hzero
    · refine Or.inr ⟨hi, ?_⟩
      simpa only [← halpha ⟨i.1 - 1, by omega⟩, ← halpha i] using hsum
  · rintro (hzero | ⟨hi, hsum⟩)
    · exact Or.inl hzero
    · refine Or.inr ⟨hi, ?_⟩
      simpa only [halpha ⟨i.1 - 1, by omega⟩, halpha i] using hsum

/-- The right alpha-sum trigger in Definition 10 is independent of the good
BONG. -/
theorem rightApproximationTrigger_changeBONG_iff
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a a' : GoodBONG q L (n + 1)) (i : Fin n) :
    a.rightApproximationTrigger i ↔ a'.rightApproximationTrigger i := by
  have halpha : a.SameAlphas a' := (a.order_alpha_invariant a').2
  unfold rightApproximationTrigger
  constructor
  · rintro (hlast | ⟨hi, hsum⟩)
    · exact Or.inl hlast
    · refine Or.inr ⟨hi, ?_⟩
      simpa only [← halpha i, ← halpha ⟨i.1 + 1, by omega⟩] using hsum
  · rintro (hlast | ⟨hi, hsum⟩)
    · exact Or.inl hlast
    · refine Or.inr ⟨hi, ?_⟩
      simpa only [halpha i, halpha ⟨i.1 + 1, by omega⟩] using hsum

/-- The two representation equivalences required in the proof of Lemma 3.8
at one boundary.  In the paper they are supplied by Lemma 1.5 and the
Hilbert-symbol defect estimates. -/
structure SpaceApproximationRepresentationBridge
    (a a' : GoodBONG q L (n + 1)) (i : Fin n)
    (c : Fin (i.1 + 1) → Kˣ) : Prop where
  left_iff :
    a.leftApproximationTrigger i →
      (DiagonalRepresents
          (a.prefixValues i.1 (by omega)) (diagonalUnitCoefficients c) ↔
        DiagonalRepresents
          (a'.prefixValues i.1 (by omega)) (diagonalUnitCoefficients c))
  right_iff :
    a.rightApproximationTrigger i →
      (DiagonalRepresents (diagonalUnitCoefficients c)
          (a.prefixValues (i.1 + 2) (by omega)) ↔
        DiagonalRepresents (diagonalUnitCoefficients c)
          (a'.prefixValues (i.1 + 2) (by omega)))

namespace SpaceApproximationRepresentationBridge

variable {a a' : GoodBONG q L (n + 1)} {i : Fin n}
  {c : Fin (i.1 + 1) → Kˣ}

/-- Left-space approximation is invariant once the left representation
bridge has been established. -/
theorem isLeftSpaceApproximation_iff
    [GoodBONGClassificationLaws.{u, v, v} K]
    (D : SpaceApproximationRepresentationBridge a a' i c) :
    a.IsLeftSpaceApproximation i c ↔
      a'.IsLeftSpaceApproximation i c := by
  have htrigger := a.leftApproximationTrigger_changeBONG_iff a' i
  constructor
  · rintro ⟨hdet, hrep⟩
    refine ⟨(a.isPrefixApproximation_changeBONG_iff a'
      (i.1 + 1) (diagonalUnitDeterminant c)).1 hdet, ?_⟩
    intro ht
    exact (D.left_iff (htrigger.2 ht)).1 (hrep (htrigger.2 ht))
  · rintro ⟨hdet, hrep⟩
    refine ⟨(a.isPrefixApproximation_changeBONG_iff a'
      (i.1 + 1) (diagonalUnitDeterminant c)).2 hdet, ?_⟩
    intro ht
    exact (D.left_iff ht).2 (hrep (htrigger.1 ht))

/-- Right-space approximation is invariant once the right representation
bridge has been established. -/
theorem isRightSpaceApproximation_iff
    [GoodBONGClassificationLaws.{u, v, v} K]
    (D : SpaceApproximationRepresentationBridge a a' i c) :
    a.IsRightSpaceApproximation i c ↔
      a'.IsRightSpaceApproximation i c := by
  have htrigger := a.rightApproximationTrigger_changeBONG_iff a' i
  constructor
  · rintro ⟨hdet, hrep⟩
    refine ⟨(a.isPrefixApproximation_changeBONG_iff a'
      (i.1 + 1) (diagonalUnitDeterminant c)).1 hdet, ?_⟩
    intro ht
    exact (D.right_iff (htrigger.2 ht)).1 (hrep (htrigger.2 ht))
  · rintro ⟨hdet, hrep⟩
    refine ⟨(a.isPrefixApproximation_changeBONG_iff a'
      (i.1 + 1) (diagonalUnitDeterminant c)).2 hdet, ?_⟩
    intro ht
    exact (D.right_iff ht).2 (hrep (htrigger.1 ht))

/-- Beli (2019), Lemma 3.8 for Definition 10, reduced to its two explicit
local representation bridges. -/
theorem isSpaceApproximation_iff
    [GoodBONGClassificationLaws.{u, v, v} K]
    (D : SpaceApproximationRepresentationBridge a a' i c) :
    a.IsSpaceApproximation i c ↔ a'.IsSpaceApproximation i c := by
  unfold IsSpaceApproximation
  exact and_congr D.isLeftSpaceApproximation_iff
    D.isRightSpaceApproximation_iff

end SpaceApproximationRepresentationBridge

end BONG.GoodBONG

end Bong
