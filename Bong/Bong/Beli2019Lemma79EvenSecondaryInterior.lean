/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenAlphaCloseLeftOuter
import Bong.Bong.Beli2019Lemma69TypeIISourceLeftValue
import Bong.Bong.Beli2019Lemma69TypeIIILeftValue
import Bong.Bong.Beli2019Remark616LeftMixed

/-!
# Beli (2019), Lemma 7.9(ii), case 3: interior secondary candidate

At boundary `i + 2`, Lemma 6.9(ii) selects the source alpha.  The
neighboring-alpha estimate and Remark 6.16 then compare the mixed prefixes
within two units.  Equality of adjacent order sums finishes the secondary
candidate at every strict type-II or type-III left-interior point.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Remark 6.16 converts a source-alpha equality and neighboring-alpha
closeness into the mixed-prefix estimate needed by the third candidate. -/
theorem lemma79_even_secondaryPrefix_le_add_two_of_leftAlpha
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hfar : i.val + 2 < n + 2)
    (hAlpha : a.representationAlphaValue b
        ⟨i.val + 2, by omega, hfar, hfar.le⟩ =
      a.alphaValue ⟨i.val + 1, by omega⟩)
    (hclose : b.alphaValue ⟨i.val + 1, by omega⟩ ≤
      a.alphaValue ⟨i.val + 1, by omega⟩ + 2) :
    b.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) ≤
      a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) +
        ((2 : ℚ) : WithTop ℚ) := by
  let farIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 2, by omega, hfar, hfar.le⟩
  have hraw := beli2019Remark616_leftMixedPrefix_right_le_add_two
    a b c hdefect farIdx (by
      simpa only [farIdx,
        show i.val + 2 - 1 = i.val + 1 by omega] using hAlpha)
      (by simpa only [farIdx,
        show i.val + 2 - 1 = i.val + 1 by omega] using hclose)
      1 (i.val - 2)
  simpa only [farIdx] using hraw

set_option maxHeartbeats 2000000 in
-- The dependent boundary `i + 2` is transported through Lemma 6.9(ii).
/-- The type-II strict left interior satisfies the shifted secondary
candidate comparison. -/
theorem beli2019Lemma79_typeII_even_left_secondary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hfarLeft : i.val + 2 ≤ D.outer.transition.lastZero) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((2 : ℚ) : WithTop ℚ) := by
  have hfarBound : i.val + 2 < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    have hlong := D.long
    omega
  let farIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 2, by omega, hfarBound, hfarBound.le⟩
  have hfarEven : Even farIdx.val := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d + 1, by simp only [farIdx]; omega⟩
  have hAlpha : a.representationAlphaValue b farIdx =
      a.alphaValue ⟨farIdx.val - 1, by
        have hb := farIdx.lt_large
        omega⟩ := by
    simpa only [farIdx] using
      (a.beli2019Lemma69_ii_typeII_sourceLeftValue
        b D hfirst hdefect (i.val + 2) (by omega)
          hfarLeft hfarEven)
  have hclose := beli2019Lemma79_typeII_even_left_alphaClose
    a b D hfirst farIdx (by simp only [farIdx]; omega)
      hfarEven hfarLeft
  have hprefix := lemma79_even_secondaryPrefix_le_add_two_of_leftAlpha
    a b c hdefect i hfarBound
      (by simpa only [farIdx,
        show i.val + 2 - 1 = i.val + 1 by omega] using hAlpha)
      (by simpa only [farIdx,
        show i.val + 2 - 1 = i.val + 1 by omega] using hclose)
  exact lemma79_even_leftOuter_secondary_le_add_two_of_prefix
    a b c D.outer hfirst i hi hiEven hfarLeft hprefix

set_option maxHeartbeats 3000000 in
-- Type III carries the hypotheses needed by Lemmas 7.8 and 6.9(ii).
/-- The type-III strict left interior satisfies the shifted secondary
candidate comparison. -/
theorem beli2019Lemma79_typeIII_even_left_secondary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hfarLeft : i.val + 2 ≤ D.outer.transition.lastZero) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((2 : ℚ) : WithTop ℚ) := by
  have hfarBound : i.val + 2 < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  let farIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 2, by omega, hfarBound, hfarBound.le⟩
  have hfarEven : Even farIdx.val := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d + 1, by simp only [farIdx]; omega⟩
  have hAlpha : a.representationAlphaValue b farIdx =
      a.alphaValue ⟨farIdx.val - 1, by
        have hb := farIdx.lt_large
        omega⟩ := by
    simpa only [farIdx] using
      (a.beli2019Lemma69_ii_typeIII_sourceLeftValue
        b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
          (i.val + 2) (by omega) hfarLeft hfarEven)
  have hclose := beli2019Lemma79_typeIII_even_left_alphaClose
    a b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
      farIdx (by simp only [farIdx]; omega) hfarEven hfarLeft
  have hprefix := lemma79_even_secondaryPrefix_le_add_two_of_leftAlpha
    a b c hdefect i hfarBound
      (by simpa only [farIdx,
        show i.val + 2 - 1 = i.val + 1 by omega] using hAlpha)
      (by simpa only [farIdx,
        show i.val + 2 - 1 = i.val + 1 by omega] using hclose)
  exact lemma79_even_leftOuter_secondary_le_add_two_of_prefix
    a b c D.outer hfirst i hi hiEven hfarLeft hprefix

end BONG.GoodBONG

end Bong
