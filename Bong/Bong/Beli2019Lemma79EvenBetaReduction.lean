/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenLeftAssembly
import Bong.Bong.Beli2019KeyLemma

/-!
# Beli (2019), Lemma 7.9(ii), case 3: reducing the beta estimate

The source estimate `B_i <= beta_i` has two numerical branches.  A source
gap at least `2e` is handled by the half-gap candidate and P5.  Below `2e`,
the paper proves `beta_i = alpha_i + 2` and compares `B_i` with `C_i + 2`.
This file isolates both reductions without profile-specific assumptions.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- If the cross order gap is at most `2e`, the half-gap candidate bounds
the representation alpha by `2e`. -/
theorem representationAlphaValue_le_twoE_of_crossGap_le
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
      c.order ⟨i.val - 1, by
        have hp := i.pos
        have hb := i.lt_large
        omega⟩ ≤
        2 * (ramificationIndex K : Int)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
  rw [b.coe_representationAlphaValue c i]
  calc
    b.representationAlpha c i ≤ b.representationHalfGap c i :=
      b.representationAlpha_le_halfGap c i
    _ ≤ ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
      unfold representationHalfGap
      norm_cast
      have hcrossQ :
          ((b.order ⟨i.val, i.lt_large⟩ -
            c.order ⟨i.val - 1, by
              have hp := i.pos
              have hb := i.lt_large
              omega⟩ : Int) : ℚ) ≤
            2 * (ramificationIndex K : ℚ) := by
        exact_mod_cast hcross
      simp only [Rat.divInt_eq_div]
      push_cast
      push_cast at hcrossQ
      linarith

/-- Property P5 turns a source gap at least `2e` into the same lower bound
for the corresponding alpha value. -/
theorem twoE_le_alphaValue_of_orderGap_ge
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (p : Fin (n + 1))
    (hgap : 2 * (ramificationIndex K : Int) ≤ b.orderGap p) :
    2 * (ramificationIndex K : ℚ) ≤ b.alphaValue p := by
  by_contra hnot
  have halphaLt : b.alphaValue p <
      2 * (ramificationIndex K : ℚ) := lt_of_not_ge hnot
  have hgapLt := (b.alpha_p5 p).1.mp halphaLt
  exact (not_lt_of_ge hgap) hgapLt

/-- The large-source-gap branch of the scalar estimate `B_i <= beta_i`. -/
theorem lemma79_even_beta_bound_of_large_sourceGap
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
      c.order ⟨i.val - 1, by
        have hp := i.pos
        have hb := i.lt_large
        omega⟩ ≤
        2 * (ramificationIndex K : Int))
    (hsource : 2 * (ramificationIndex K : Int) ≤
      b.orderGap ⟨i.val - 1, by
        have hp := i.pos
        have hb := i.lt_large
        omega⟩) :
    b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by
        have hp := i.pos
        have hb := i.lt_large
        omega⟩ := by
  apply WithTop.coe_le_coe.mp
  exact (representationAlphaValue_le_twoE_of_crossGap_le
    b c i hcross).trans (by
      exact_mod_cast (b.twoE_le_alphaValue_of_orderGap_ge
        ⟨i.val - 1, by
          have hp := i.pos
          have hb := i.lt_large
          omega⟩ hsource))

/-- In the small-source-gap branch, `B_i <= C_i + 2`, condition 2.1(ii)
for the old pair, and `beta_i = alpha_i + 2` imply `B_i <= beta_i`. -/
theorem lemma79_even_beta_bound_of_comparison_shift
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hdefectAC : a.RepresentationDefectCondition c)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hshift : (b.representationAlphaValue c i : WithTop ℚ) ≤
      (a.representationAlphaValue c i : WithTop ℚ) +
        ((2 : ℚ) : WithTop ℚ))
    (halpha : b.alphaValue ⟨i.val - 1, by
        have hp := i.pos
        have hb := i.lt_large
        omega⟩ =
      a.alphaValue ⟨i.val - 1, by
        have hp := i.pos
        have hb := i.lt_large
        omega⟩ + 2) :
    b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by
        have hp := i.pos
        have hb := i.lt_large
        omega⟩ := by
  apply WithTop.coe_le_coe.mp
  calc
    (b.representationAlphaValue c i : WithTop ℚ) ≤
        (a.representationAlphaValue c i : WithTop ℚ) +
          ((2 : ℚ) : WithTop ℚ) := hshift
    _ = a.representationAlpha c i + ((2 : ℚ) : WithTop ℚ) := by
      rw [a.coe_representationAlphaValue c i]
    _ ≤ (a.alphaValue ⟨i.val - 1, by
            have hp := i.pos
            have hb := i.lt_large
            omega⟩ : WithTop ℚ) +
          ((2 : ℚ) : WithTop ℚ) := by
      have h := add_le_add_right
        (a.representationAlpha_le_leftAlpha c hdefectAC i)
        ((2 : ℚ) : WithTop ℚ)
      simpa only [add_comm] using h
    _ = (b.alphaValue ⟨i.val - 1, by
          have hp := i.pos
          have hb := i.lt_large
          omega⟩ : WithTop ℚ) := by
      exact_mod_cast halpha.symm

end BONG.GoodBONG

end Bong
