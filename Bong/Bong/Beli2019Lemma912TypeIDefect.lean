/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma912TypeI
import Bong.Bong.Beli2019Lemma63Right
import Bong.Bong.Beli2019Remark616RightMixedGeneral

/-!
# Beli (2019), Lemma 9.12: type-I prefix-defect transfer

After the Lemma 9.10 construction, the source and target order sequences
agree from the third coefficient onward.  Lemma 6.3 therefore identifies
every later comparison invariant with the target alpha.  Remark 6.16 then
gives the exact minimum formula for arbitrary mixed prefixes.  These are the
two scalar identities used in the CLAIM inside Lemma 9.12.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {M : Lattice K V} {P : Lattice K W} {Q : Lattice K U}
  {N : Nat}

namespace Beli2019Lemma910Data

/-- For every boundary at or after the second one, the Lemma 9.10
comparison invariant is the alpha invariant of the new BONG.  This is the
paper's identity `A_i = β_i` for `i ≥ 2`. -/
theorem representationAlphaValue_eq_targetAlpha
    [Beli2006AlphaLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefect : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength))
    (i : RepresentationIndex (N + 3) (N + 3)) (hi : 2 ≤ i.val) :
    (a.castLength hlength).representationAlphaValue
        (E.bong.castLength hlength) i =
      (E.bong.castLength hlength).alphaValue
        ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ := by
  apply (a.castLength hlength).beli2019Lemma63_sameRank_right_value
    (E.bong.castLength hlength) hdefect i
  intro k hik hkn
  rw [BeliOrderSequence.entryOrZero_of_lt
      (a.castLength hlength).orderSequence hkn,
    BeliOrderSequence.entryOrZero_of_lt
      (E.bong.castLength hlength).orderSequence hkn]
  exact (E.order_castLength_eq_source_of_two_le a D horders hlength
    ⟨k, hkn⟩ (hi.trans hik)).symm

/-- The diagonal prefix defect between the old and new BONG is exactly the
new alpha invariant: `d[a_(1,i)b_(1,i)] = β_i` for `i ≥ 2`. -/
theorem diagonalPrefixDefect_eq_targetAlpha
    [Beli2006AlphaLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefect : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength))
    (i : RepresentationIndex (N + 3) (N + 3)) (hi : 2 ≤ i.val) :
    (a.castLength hlength).truncatedPrefixDefect
        (E.bong.castLength hlength) 1 i.val i.val =
      ((E.bong.castLength hlength).alphaValue
        ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : WithTop ℚ) := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  let beta : WithTop ℚ :=
    (target.alphaValue ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ : WithTop ℚ)
  have hvalue := E.representationAlphaValue_eq_targetAlpha
    a D horders hlength hdefect i hi
  have hlower : beta ≤ source.truncatedPrefixDefect target 1 i.val i.val := by
    dsimp only [beta, source, target]
    simpa only [hvalue] using hdefect i
  have hupper : source.truncatedPrefixDefect target 1 i.val i.val ≤ beta := by
    dsimp only [beta, source, target]
    calc
      (a.castLength hlength).truncatedPrefixDefect
          (E.bong.castLength hlength) 1 i.val i.val ≤
          (E.bong.castLength hlength).prefixAlphaCap i.val :=
        (a.castLength hlength).truncatedPrefixDefect_le_rightCap
          (E.bong.castLength hlength) 1 i.val i.val
      _ = ((E.bong.castLength hlength).alphaValue
          ⟨i.val - 1, by
            have := i.lt_large
            omega⟩ : WithTop ℚ) :=
        (E.bong.castLength hlength).prefixAlphaCap_of_internal
          i.pos i.lt_large
  exact le_antisymm hupper hlower

/-- Remark 6.16 in the exact form used by Lemma 9.12:
`d[ε b_(1,i)c_(1,j)] = min {d[ε a_(1,i)c_(1,j)], β_i}`. -/
theorem mixedPrefixDefect_eq_min
    [Beli2006AlphaLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefect : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength))
    (i : RepresentationIndex (N + 3) (N + 3)) (hi : 2 ≤ i.val)
    (epsilon : Kˣ) (j : Nat) :
    (E.bong.castLength hlength).truncatedPrefixDefect c epsilon i.val j =
      min ((a.castLength hlength).truncatedPrefixDefect c epsilon i.val j)
        ((E.bong.castLength hlength).alphaValue
          ⟨i.val - 1, by
            have := i.lt_large
            omega⟩ : WithTop ℚ) := by
  apply (a.castLength hlength).beli2019Remark616_rightMixedPrefix_at
    (E.bong.castLength hlength) c hdefect i
  exact E.representationAlphaValue_eq_targetAlpha
    a D horders hlength hdefect i hi

/-- Consequently every such mixed defect for the new BONG is bounded by
the corresponding mixed defect for the old BONG. -/
theorem mixedPrefixDefect_le_source
    [Beli2006AlphaLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefect : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength))
    (i : RepresentationIndex (N + 3) (N + 3)) (hi : 2 ≤ i.val)
    (epsilon : Kˣ) (j : Nat) :
    (E.bong.castLength hlength).truncatedPrefixDefect c epsilon i.val j ≤
      (a.castLength hlength).truncatedPrefixDefect c epsilon i.val j := by
  rw [E.mixedPrefixDefect_eq_min a c D horders hlength hdefect
    i hi epsilon j]
  exact min_le_left _ _

/-- The same comparison, including the complete-prefix endpoint.  The
internal case is Remark 6.16; at full rank, changing between two good BONGs
of the same quadratic space multiplies the complete value product by a
square and hence leaves the mixed defect unchanged. -/
theorem mixedPrefixDefect_le_source_at
    [Beli2006AlphaLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefect : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength))
    (p : Nat) (hpTwo : 2 ≤ p) (hpRank : p ≤ N + 3)
    (epsilon : Kˣ) (j : Nat) :
    (E.bong.castLength hlength).truncatedPrefixDefect c epsilon p j ≤
      (a.castLength hlength).truncatedPrefixDefect c epsilon p j := by
  by_cases hpFull : p = N + 3
  · subst p
    exact le_of_eq (
      (a.castLength hlength).truncatedPrefixDefect_fullLeft_invariant
        (E.bong.castLength hlength) c epsilon j)
  · let i : RepresentationIndex (N + 3) (N + 3) := {
      val := p
      pos := by omega
      lt_large := by omega
      le_small := hpRank }
    exact E.mixedPrefixDefect_le_source a c D horders hlength hdefect
      i hpTwo epsilon j

end Beli2019Lemma910Data

end BONG.GoodBONG

end Bong
