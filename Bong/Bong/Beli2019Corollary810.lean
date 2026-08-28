/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma88Sufficiency

/-!
# Beli (2019), Corollary 8.10

After changing only the projected tail, the global first alpha can be made
equal to the alpha of the literal first binary segment.  This is the normal
form used repeatedly in Lemmas 8.11, 8.14, and Section 9.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- The concrete output of Corollary 8.10.  The head value is unchanged and
the first binary segment realizes the global first alpha. -/
structure Beli2019Corollary810Data (b : GoodBONG q L (N + 2)) where
  transformed : GoodBONG q L (N + 2)
  headValue_eq :
    transformed.valueUnit (0 : Fin (N + 2)) =
      b.valueUnit (0 : Fin (N + 2))
  firstBinaryAlpha_eq :
    transformed.firstBinaryAlpha =
      (transformed.alphaValue (0 : Fin (N + 1)) : WithTop ℚ)

/-- Corollary 8.10: a change of the projected-tail BONG makes the first
global alpha occur already on the first binary segment. -/
theorem beli2019Corollary810
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (b : GoodBONG q L (N + 2)) :
    Nonempty b.Beli2019Corollary810Data := by
  cases N with
  | zero =>
      have hbinary : b.firstBinaryAlpha =
          (b.alphaValue (0 : Fin 1) : WithTop ℚ) := by
        unfold firstBinaryAlpha
        exact b.binary_alpha_eq_min_candidates.symm
      exact ⟨{
        transformed := b
        headValue_eq := rfl
        firstBinaryAlpha_eq := hbinary
      }⟩
  | succ N =>
      by_cases hbinary : b.firstBinaryAlpha =
          (b.alphaValue (0 : Fin (N + 2)) : WithTop ℚ)
      · exact ⟨{
          transformed := b
          headValue_eq := rfl
          firstBinaryAlpha_eq := hbinary
        }⟩
      · have hhalfNe :
            ¬b.AttainsHalfGap (0 : Fin (N + 2)) := by
          intro hhalf
          exact hbinary (b.firstBinaryAlpha_eq_alpha_of_halfGap hhalf)
        have hstrict : b.alphaValue (0 : Fin (N + 2)) <
            b.halfGapValue (0 : Fin (N + 2)) :=
          lt_of_le_of_ne (b.alphaValue_le_halfGapValue 0) hhalfNe
        have hadjacentNotLe : ¬b.adjacentDefect (0 : Fin (N + 2)) ≤
            (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
          intro hle
          exact hbinary
            (b.firstBinaryAlpha_eq_alpha_of_adjacentDefect_le_tailAlpha hle)
        have htail :
            (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) <
              b.adjacentDefect (0 : Fin (N + 2)) :=
          lt_of_not_ge hadjacentNotLe
        have htailStrict :=
          b.tailAlpha_lt_halfGap_of_global_strict htail hstrict
        have htailNotExceptional :
            ¬b.tail.Beli2019Lemma88Exceptional := by
          rintro ⟨htailHalf, _⟩
          exact (ne_of_lt htailStrict) htailHalf
        rcases b.tail.beli2019Lemma88_sufficiency htailNotExceptional with
          ⟨T⟩
        rcases b.tailReplacementData_of_firstValueTransform T with ⟨D⟩
        have hglobal :=
          b.alpha_zero_eq_orderGap_add_tailAlpha_of_tailAlpha_lt_adjacentDefect
            htail hstrict
        have hbinaryOriginal :=
          D.firstBinaryAlpha_eq_of_strict_tail htail hglobal
        have halphas := b.alpha_invariant D.transformed
        have hbinaryTransformed : D.transformed.firstBinaryAlpha =
            (D.transformed.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
          calc
            D.transformed.firstBinaryAlpha =
                (b.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) :=
              hbinaryOriginal
            _ = (D.transformed.alphaValue
                (0 : Fin (N + 2)) : WithTop ℚ) :=
              congrArg (fun x : ℚ => (x : WithTop ℚ))
                (halphas (0 : Fin (N + 2)))
        exact ⟨{
          transformed := D.transformed
          headValue_eq := D.firstValue_eq
          firstBinaryAlpha_eq := hbinaryTransformed
        }⟩

end BONG.GoodBONG

end Bong
