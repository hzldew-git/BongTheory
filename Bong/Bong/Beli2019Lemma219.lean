/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma96
import Bong.Bong.Beli2019Lemma216Complete
import Bong.Bong.Beli2019Reflexivity
import Bong.Bong.Beli2019RepresentationTransitivity

/-!
# Beli (2019), Lemma 2.19: the unary--ternary instance

Lemma 2.19 enlarges condition 2.1(iv): if `R_l - S_j > 2e`, then the
source prefix through `b_j` is represented by the target prefix through
`a_(l-1)`.  Lemma 9.6 uses the instance `l = 4`, `j = 1`.

For that instance the proof has a particularly transparent v2 form.  If
`R_4 <= S_2`, condition (iv) applies directly.  Otherwise condition (iii')
at the next central index applies: its preceding defect is exactly
`d[-a_(1,3)b_1]`, while the current defect is nonnegative.  This file proves
that instance from the four representation conditions and Lemma 2.16; it
does not add a representation-theoretic trust boundary.
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

/-- The condition-(iv) index used by the `l = 4`, `j = 1` instance of
Lemma 2.19. -/
def lemma219UnaryTernaryLongIndex :
    LongRepresentationIndex (N + 4) (N + 4) where
  val := 2
  one_lt := by omega
  succ_lt_large := by omega
  le_small_succ := by omega

/-- The condition-(iii') index immediately following the preceding long
index. -/
def lemma219UnaryTernaryCentralIndex :
    CentralRepresentationIndex (N + 4) (N + 4) where
  val := 3
  one_lt := by omega
  lt_large := by omega
  le_small_succ := by omega

/-- Beli (2019), Lemma 2.19 in the exact instance used in Lemma 9.6:
`R_4 > S_1 + 2e` and `R_3 = S_1` imply
`[b_1] rep [a_1,a_2,a_3]`.

The hypothesis on the truncated defect is the one already present in
Lemma 9.6.  It is only used in the condition-(iii') branch; the other branch
is condition (iv) verbatim. -/
theorem beli2019Lemma219_unaryTernary
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hconditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (hthirdSource : a.order (2 : Fin (N + 4)) = b.order (0 : Fin (N + 4)))
    (hstrict :
      b.order (0 : Fin (N + 4)) + 2 * (ramificationIndex K : Int) <
        a.order (3 : Fin (N + 4)))
    (hdefect : a.Beli2019Lemma96DefectBound b) :
    DiagonalRepresents
      (b.prefixValues 1 (by omega))
      (a.prefixValues 3 (by omega)) := by
  by_cases hlong :
      a.order (3 : Fin (N + 4)) <= b.order (1 : Fin (N + 4))
  · let i : LongRepresentationIndex (N + 4) (N + 4) :=
      lemma219UnaryTernaryLongIndex (N := N)
    have htrigger : a.longRepresentationTrigger b i := by
      unfold longRepresentationTrigger
      dsimp only [i, lemma219UnaryTernaryLongIndex]
      constructor
      · rw [dif_pos (show 2 <= N + 4 by omega)]
        convert hlong using 1 <;> congr
      · constructor
        · convert hstrict using 1 <;> congr
        · have hlast :
              a.order (2 : Fin (N + 4)) +
                    2 * (ramificationIndex K : Int) <=
                b.order (0 : Fin (N + 4)) +
                    2 * (ramificationIndex K : Int) := by
            rw [hthirdSource]
          convert hlast using 1 <;> congr
    exact hconditions.longRepresentations i htrigger
  · have hcross :
        b.order (1 : Fin (N + 4)) < a.order (3 : Fin (N + 4)) :=
      lt_of_not_ge hlong
    let i : CentralRepresentationIndex (N + 4) (N + 4) :=
      lemma219UnaryTernaryCentralIndex (N := N)
    have hthreshold :
        ((2 * (ramificationIndex K : ℚ) +
            (b.order (1 : Fin (N + 4)) : ℚ) -
            (a.order (3 : Fin (N + 4)) : ℚ) : ℚ) : WithTop ℚ) <
          (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      norm_cast
      push_cast
      have hcrossQ :
          (b.order (1 : Fin (N + 4)) : ℚ) <
            (a.order (3 : Fin (N + 4)) : ℚ) := by
        exact_mod_cast hcross
      linarith
    have hcurrentNonneg : (0 : WithTop ℚ) <=
        a.truncatedPrefixDefect b (-1) 4 2 :=
      a.truncatedPrefixDefect_nonneg
        (alphaV := sourceLaws) (alphaW := targetLaws) b (-1) 4 2
    have hsumLower :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <=
          a.truncatedPrefixDefect b (-1) 3 1 +
            a.truncatedPrefixDefect b (-1) 4 2 := by
      have hadd := add_le_add hdefect hcurrentNonneg
      simpa only [add_zero] using hadd
    have hdefectTrigger : a.centralDefectTrigger b i := by
      unfold centralDefectTrigger
      dsimp only [i, lemma219UnaryTernaryCentralIndex]
      constructor
      · exact hcross
      · exact hthreshold.trans_le hsumLower
    have htriggers : a.CentralTriggerEquivalence b :=
      a.beli2019Lemma216
        (sourceLaws := sourceLaws) (targetLaws := targetLaws)
        b (Nat.le_refl (N + 3))
        hconditions.orderCondition hconditions.defectCondition
    have hsourceTwoTargetThree :=
      hconditions.centralRepresentations i ((htriggers i).mpr hdefectTrigger)
    have hsourceOneSourceTwo :=
      b.prefixValues_represents_of_le 1 2 (by omega) (by omega)
    exact hsourceOneSourceTwo.trans hsourceTwoTargetThree

end BONG.GoodBONG

end Bong
