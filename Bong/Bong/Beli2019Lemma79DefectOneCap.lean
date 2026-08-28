/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79DefectOne

/-!
# Beli (2019), Lemma 7.9(ii): the defect-one cap

If the comparison alpha is at most one, both adjacent alpha caps are at
least one, and the comparison square class has even order, then the
truncated prefix defect bounds the comparison alpha.  This is the common
arithmetic conclusion used in cases 5 and 6 of the proof.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The common defect-one closing argument in Lemma 7.9(ii). -/
theorem lemma79_ii_of_alpha_le_one_and_even
    [PerfectResidueFieldLaws K]
    (b : GoodBONG q L (n + 1)) (c : GoodBONG q M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hAlpha : b.representationAlphaValue c i ≤ 1)
    (hb : (1 : ℚ) ≤ b.alphaValue ⟨i.val - 1, by
      have := i.lt_large
      have := i.pos
      omega⟩)
    (hc : (1 : ℚ) ≤ c.alphaValue ⟨i.val - 1, by
      have := i.lt_large
      have := i.pos
      omega⟩)
    (heven : Even
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hraw : (1 : WithTop ℚ) ≤ defectOrder (K := K)
      (1 * b.prefixProduct i.val * c.prefixProduct i.val) := by
    simpa only [one_mul] using defectOrder_one_le_of_even
      (b.prefixProduct i.val * c.prefixProduct i.val) heven
  have hbCap : (1 : WithTop ℚ) ≤ b.prefixAlphaCap i.val := by
    rw [b.prefixAlphaCap_of_internal i.pos i.lt_large]
    exact_mod_cast hb
  have hcCap : (1 : WithTop ℚ) ≤ c.prefixAlphaCap i.val := by
    rw [c.prefixAlphaCap_of_internal i.pos i.lt_large]
    exact_mod_cast hc
  have htruncated : (1 : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
    unfold truncatedPrefixDefect
    exact le_min hraw (le_min hbCap hcCap)
  exact (show (b.representationAlphaValue c i : WithTop ℚ) ≤ 1 by
    exact_mod_cast hAlpha).trans htruncated

end BONG.GoodBONG

end Bong
