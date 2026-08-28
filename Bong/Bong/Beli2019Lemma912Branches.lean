/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIIISourceAlpha
import Bong.Bong.Beli2019Lemma912TypeIReduction
/-!
# Beli (2019), Lemma 9.12: exhaustive residual branches

After the type-I claim has reduced the representation conditions to two scalar
inequalities, Beli's proof splits the residual parameter profile into five
cases. This file proves that split from the initial profile. In particular,
the second alpha is nonzero and hence at least one; this uses Corollary 2.8(iii)
to cover the possible half-integral range.
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

/-- The five mutually exhaustive parameter branches used after the type-I
claim in Beli's proof of Lemma 9.12. -/
inductive Beli2019Lemma912ParameterBranch
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5)) : Prop
  | equalSecondLarge
      (fullDefect_eq : a.truncatedPrefixDefect c (-1) 3 1 =
        (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ))
      (firstAlpha_eq : a.alphaValue (0 : Fin (N + 4)) =
        c.alphaValue (0 : Fin (N + 4)))
      (secondAlpha_large : 1 < a.alphaValue (1 : Fin (N + 4)))
  | equalSecondOne
      (fullDefect_eq : a.truncatedPrefixDefect c (-1) 3 1 =
        (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ))
      (firstAlpha_eq : a.alphaValue (0 : Fin (N + 4)) =
        c.alphaValue (0 : Fin (N + 4)))
      (secondAlpha_eq_one : a.alphaValue (1 : Fin (N + 4)) = 1)
  | strictBelowHalfGap
      (fullDefect_strict :
        (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) <
          a.truncatedPrefixDefect c (-1) 3 1)
      (firstAlpha_below_halfGap :
        a.alphaValue (0 : Fin (N + 4)) <
          a.halfGapValue (0 : Fin (N + 4)))
  | strictAtHalfGapIsotropic
      (fullDefect_strict :
        (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) <
          a.truncatedPrefixDefect c (-1) 3 1)
      (firstAlpha_eq_halfGap :
        a.alphaValue (0 : Fin (N + 4)) =
          a.halfGapValue (0 : Fin (N + 4)))
      (firstThree_isotropic : a.Lemma814FirstThreeIsotropic)
  | strictAtHalfGapAnisotropic
      (fullDefect_strict :
        (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) <
          a.truncatedPrefixDefect c (-1) 3 1)
      (firstAlpha_eq_halfGap :
        a.alphaValue (0 : Fin (N + 4)) =
          a.halfGapValue (0 : Fin (N + 4)))
      (firstThree_anisotropic : a.Lemma814FirstThreeAnisotropic)

/-- Under the residual profile, the second alpha in the paper is nonzero
and hence at least one. -/
theorem beli2019Lemma912_secondAlpha_one_le
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c) :
    1 ≤ a.alphaValue (1 : Fin (N + 4)) := by
  have hgapReverse : a.orderGap (1 : Fin (N + 4)) =
      -a.orderGap (0 : Fin (N + 4)) := by
    change a.order (2 : Fin (N + 5)) - a.order (1 : Fin (N + 5)) =
      -(a.order (1 : Fin (N + 5)) - a.order (0 : Fin (N + 5)))
    rw [← profile.firstThird_eq]
    ring
  have hne : a.alphaValue (1 : Fin (N + 4)) ≠ 0 := by
    intro hzero
    have hgapZero := (a.alpha_p2 (1 : Fin (N + 4))).2.mp hzero
    have hbound := profile.firstGap_le_twoE_sub_two
    omega
  exact a.one_le_alphaValue_of_ne_zero (1 : Fin (N + 4)) hne

/-- The five branches above exhaust the residual profile exactly as in the
case split following the type-I claim. -/
theorem beli2019Lemma912_parameterBranches
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c) :
    Beli2019Lemma912ParameterBranch a c := by
  rcases profile.fullDefectAlternative with hstrict | hequal
  · have hhalf := a.alphaValue_le_halfGapValue
      (0 : Fin (N + 4))
    rcases eq_or_lt_of_le hhalf with hhalfEq | hhalfLt
    · by_cases hisotropic : a.Lemma814FirstThreeIsotropic
      · exact .strictAtHalfGapIsotropic hstrict hhalfEq hisotropic
      · have hanisotropic : a.Lemma814FirstThreeAnisotropic := by
          intro x hx
          by_contra hxne
          exact hisotropic ⟨x, hxne, hx⟩
        exact .strictAtHalfGapAnisotropic hstrict hhalfEq hanisotropic
    · exact .strictBelowHalfGap hstrict hhalfLt
  · rcases hequal with ⟨hfull, hfirstAlpha⟩
    have hone := a.beli2019Lemma912_secondAlpha_one_le c profile
    rcases eq_or_lt_of_le hone with honeEq | honeLt
    · exact .equalSecondOne hfull hfirstAlpha honeEq.symm
    · exact .equalSecondLarge hfull hfirstAlpha honeLt

end BONG.GoodBONG

end Bong
