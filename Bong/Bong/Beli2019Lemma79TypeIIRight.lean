/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeIIRightSource
import Bong.Bong.Beli2019Lemma79RightProfileBeta
import Bong.Bong.Beli2019Lemma79TypeIIRightComparison
import Bong.Bong.Beli2019Lemma79MixedAssembly

/-!
# Beli (2019), Lemma 7.9(ii): type-II case 7

This assembles both order subcases of the alternating right interval.  The
non-strict subcase uses the target-alpha recursion; in the strict subcase,
both source/comparison and target/comparison prefix defects vanish by the
type-II parity calculation.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 3000000 in
-- The strict branch combines the source comparison with two parity zeros.
/-- Lemma 7.9(ii), case 7, for a normalized full-span type-II pair. -/
theorem beli2019Lemma79_ii_typeII_caseSeven
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (hodd : Odd (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hAlpha : a.representationAlphaValue b i =
      b.alphaValue ⟨i.val - 1, by omega⟩ := by
    simpa only using
      (a.beli2019Lemma69_ii_typeII_targetRightValue
        b D hlast horderAB hdefectAB htotal i.val hright hodd i.lt_large)
  by_cases hcurrent : b.order ⟨i.val - 1, by omega⟩ ≤
      c.order ⟨i.val - 1, by omega⟩
  · apply lemma79_ii_of_rightMixedPrefix_branches
      a b c hdefectAB hdefectAC i hAlpha
    · intro _
      exact lemma79_typeII_right_alpha_le_sourceAlpha
        a b c D hlast horderAB hdefectAB htotal i hright hbeforeLast hodd
    · intro _
      exact lemma79_rightProfile_beta_bound_of_target_le_comparison
        a b c D.outer i hright hbeforeLast hodd hcurrent
  · have hstrict : c.order ⟨i.val - 1, by omega⟩ <
        b.order ⟨i.val - 1, by omega⟩ := lt_of_not_ge hcurrent
    have heq :=
      lemma79_typeII_right_comparisonPrefixes_eq_of_comparison_lt_target
        a b c D hfirst hnorm i hright hbeforeLast hodd hstrict
    calc
      (b.representationAlphaValue c i : WithTop ℚ) ≤
          (a.representationAlphaValue c i : WithTop ℚ) :=
        lemma79_typeII_right_alpha_le_sourceAlpha
          a b c D hlast horderAB hdefectAB htotal i hright hbeforeLast
            hodd
      _ ≤ a.truncatedPrefixDefect c 1 i.val i.val := hdefectAC i
      _ = b.truncatedPrefixDefect c 1 i.val i.val := heq.symm

end BONG.GoodBONG

end Bong
