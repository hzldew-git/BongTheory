/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIIPrefix
import Bong.Bong.Beli2019Lemma214Previous

/-!
# Beli (2019), Lemma 9.12: the exceptional third central boundary

At the central index three the type-III image has not yet reached the fully
unchanged order tail.  The auxiliary invariant at the preceding ordinary
boundary can nevertheless rise by at most one.  This is the formal version
of the paper's estimate `B'_2 <= C'_2 + 1`.
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
  {L : Lattice K V} {M : Lattice K W} {T : Nat}

variable [BeliCorollary44Laws.{u, v} K]

/-- At the second ordinary boundary, the type-III auxiliary comparison
invariant is bounded by the source auxiliary invariant plus one. -/
theorem beli2019Lemma912_typeIII_secondAlphaPrime_le_source_add_one
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3) (hT : 0 < T) :
    let second : RepresentationIndex (T + 3) (T + 3) :=
      secondRepresentationIndex T (T + 1)
    (I.bong.castLength hlength).representationAlphaPrime c second ≤
      (a.castLength hlength).representationAlphaPrime c second + 1 := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  let second : RepresentationIndex (T + 3) (T + 3) := {
    val := 2
    pos := by omega
    lt_large := by omega
    le_small := by omega }
  have hinterior : 1 < second.val ∧ second.val + 1 < T + 3 := by
    simp only [second, secondRepresentationIndex]
    omega
  have htwo : target.order (⟨2, by omega⟩ : Fin (T + 3)) =
      source.order (⟨2, by omega⟩ : Fin (T + 3)) + 1 := by
    convert beli2019Lemma912TypeIIIIndexPData_order_castLength_two
      a D I hlength using 1 <;> congr 1 <;> apply Fin.ext <;>
        simp [Nat.mod_eq_of_lt (by omega)]
  have hthree : target.order (⟨3, by omega⟩ : Fin (T + 3)) =
      source.order (⟨3, by omega⟩ : Fin (T + 3)) :=
    beli2019Lemma912TypeIIIIndexPData_order_castLength_eq_source_of_three_le
      a D I hlength ⟨3, by omega⟩ (by simp)
  have hprimary : target.representationPrimaryDefect c second ≤
      source.representationPrimaryDefect c second + 1 := by
    unfold representationPrimaryDefect
    change
      (((((target.order (⟨2, by omega⟩ : Fin (T + 3)) -
          c.order (⟨1, by omega⟩ : Fin (T + 3)) : Int) : ℚ)) : WithTop ℚ) +
        target.truncatedPrefixDefect c (-1) 3 1) ≤
      (((((source.order (⟨2, by omega⟩ : Fin (T + 3)) -
          c.order (⟨1, by omega⟩ : Fin (T + 3)) : Int) : ℚ)) : WithTop ℚ) +
        source.truncatedPrefixDefect c (-1) 3 1) + 1
    rw [htwo]
    have hprefix : target.truncatedPrefixDefect c (-1) 3 1 ≤
        source.truncatedPrefixDefect c (-1) 3 1 :=
      beli2019Lemma912_typeIII_mixedPrefixDefect_le_source_at
        a c D I hlength 3 (by omega) (by omega) (-1) 1
    have hshift :
        (((((source.order (⟨2, by omega⟩ : Fin (T + 3)) + 1 -
            c.order (⟨1, by omega⟩ : Fin (T + 3)) : Int) : ℚ)) :
              WithTop ℚ)) =
          (((((source.order (⟨2, by omega⟩ : Fin (T + 3)) -
            c.order (⟨1, by omega⟩ : Fin (T + 3)) : Int) : ℚ)) :
              WithTop ℚ)) + 1 := by
      norm_cast
      push_cast
      ring
    rw [hshift]
    calc
      _ ≤ (((((source.order (⟨2, by omega⟩ : Fin (T + 3)) -
              c.order (⟨1, by omega⟩ : Fin (T + 3)) : Int) : ℚ)) :
                WithTop ℚ) + 1) +
            source.truncatedPrefixDefect c (-1) 3 1 :=
          add_le_add_right hprefix _
      _ = _ := by ac_rfl
  have hsecondary : target.representationSecondaryDefect c second hinterior ≤
      source.representationSecondaryDefect c second hinterior + 1 := by
    unfold representationSecondaryDefect
    simp only [second, Nat.reduceAdd, Nat.reduceSub]
    change
      (((((target.order (⟨2, by omega⟩ : Fin (T + 3)) +
          target.order (⟨3, by omega⟩ : Fin (T + 3)) -
          c.order (⟨0, by omega⟩ : Fin (T + 3)) -
          c.order (⟨1, by omega⟩ : Fin (T + 3)) : Int) : ℚ)) : WithTop ℚ) +
        target.truncatedPrefixDefect c 1 4 0) ≤
      (((((source.order (⟨2, by omega⟩ : Fin (T + 3)) +
          source.order (⟨3, by omega⟩ : Fin (T + 3)) -
          c.order (⟨0, by omega⟩ : Fin (T + 3)) -
          c.order (⟨1, by omega⟩ : Fin (T + 3)) : Int) : ℚ)) : WithTop ℚ) +
        source.truncatedPrefixDefect c 1 4 0) + 1
    rw [htwo, hthree]
    have hprefix : target.truncatedPrefixDefect c 1 4 0 ≤
        source.truncatedPrefixDefect c 1 4 0 :=
      beli2019Lemma912_typeIII_mixedPrefixDefect_le_source_at
        a c D I hlength 4 (by omega) (by omega) 1 0
    have hshift :
        (((((source.order (⟨2, by omega⟩ : Fin (T + 3)) + 1 +
            source.order (⟨3, by omega⟩ : Fin (T + 3)) -
            c.order (⟨0, by omega⟩ : Fin (T + 3)) -
            c.order (⟨1, by omega⟩ : Fin (T + 3)) : Int) : ℚ)) :
              WithTop ℚ)) =
          (((((source.order (⟨2, by omega⟩ : Fin (T + 3)) +
            source.order (⟨3, by omega⟩ : Fin (T + 3)) -
            c.order (⟨0, by omega⟩ : Fin (T + 3)) -
            c.order (⟨1, by omega⟩ : Fin (T + 3)) : Int) : ℚ)) :
              WithTop ℚ)) + 1 := by
      norm_cast
      push_cast
      ring
    rw [hshift]
    calc
      _ ≤ (((((source.order (⟨2, by omega⟩ : Fin (T + 3)) +
              source.order (⟨3, by omega⟩ : Fin (T + 3)) -
              c.order (⟨0, by omega⟩ : Fin (T + 3)) -
              c.order (⟨1, by omega⟩ : Fin (T + 3)) : Int) : ℚ)) :
                WithTop ℚ) + 1) +
            source.truncatedPrefixDefect c 1 4 0 :=
          add_le_add_right hprefix _
      _ = _ := by ac_rfl
  have hresult : target.representationAlphaPrime c second ≤
      source.representationAlphaPrime c second + 1 := by
    rw [target.representationAlphaPrime_eq_min_primary_secondary
        c second hinterior,
      source.representationAlphaPrime_eq_min_primary_secondary
        c second hinterior]
    simpa only [min_add] using min_le_min hprimary hsecondary
  simpa only [source, target, second, secondRepresentationIndex] using hresult

end BONG.GoodBONG

end Bong
