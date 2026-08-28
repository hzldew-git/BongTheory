/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OddPrefixDefect
import Bong.Bong.Beli2019ApproximationInvariants

/-!
# Beli (2019), the two branches of condition 2.1(ii)

After Lemma 5.13, the proof of condition 2.1(ii) has two recurring forms.
If the scalar prefix approximations can be chosen equal, the capped defect
is the minimum of the two alpha caps.  If their cumulative orders differ by
one, M169 shows that the capped defect is zero.  This file packages both
branches and their pointwise-to-global assembly.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- Equal scalar approximations make the uncapped defect infinite, leaving
exactly the minimum of the two alpha caps. -/
theorem truncatedPrefixDefect_eq_min_caps_of_common_approximation
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : Nat) (X : Kˣ)
    (hX : a.IsPrefixApproximation i X)
    (hY : b.IsPrefixApproximation i X) :
    a.truncatedPrefixDefect b 1 i i =
      min (a.prefixAlphaCap i) (b.prefixAlphaCap i) := by
  rw [a.truncatedPrefixDefect_eq_of_approximations b 1 i i X X hX hY]
  unfold truncatedApproximationDefect
  have hsquare : IsSquare ((1 : Kˣ) * X * X) := ⟨X, by simp⟩
  rw [defectOrder_eq_top_of_isSquare hsquare]
  simp

/-- The common-approximation branch proves condition 2.1(ii) at one
ordinary boundary. -/
theorem representationDefect_at_of_common_approximation
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) (X : Kˣ)
    (hX : a.IsPrefixApproximation i.val X)
    (hY : b.IsPrefixApproximation i.val X)
    (hbound : a.representationAlpha b i ≤
      min (a.prefixAlphaCap i.val) (b.prefixAlphaCap i.val)) :
    (a.representationAlphaValue b i : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
  rw [a.coe_representationAlphaValue b i,
    a.truncatedPrefixDefect_eq_min_caps_of_common_approximation
      b i.val X hX hY]
  exact hbound

/-- The odd cumulative-order branch proves condition 2.1(ii) at one
ordinary boundary once the paper's case analysis has established `A_i ≤ 0`.
-/
theorem representationDefect_at_of_prefixSum_succ
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hsum : b.orderSequence.prefixSum i.val =
      a.orderSequence.prefixSum i.val + 1)
    (hbound : a.representationAlpha b i ≤ 0) :
    (a.representationAlphaValue b i : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
  rw [a.coe_representationAlphaValue b i,
    truncatedPrefixDefect_eq_zero_of_prefixSum_succ
      (alphaV := alphaV) (alphaW := alphaW) a b i.val
      i.lt_large.le i.le_small hsum]
  exact hbound

/-- The two-branch assembly used by the rest of the Section 5 proof.  The
remaining Jordan analysis only has to supply one of the two certificates at
each boundary. -/
theorem representationDefectCondition_of_common_or_odd_branches
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hbranches : ∀ i : RepresentationIndex (m + 1) (n + 1),
      (∃ X : Kˣ,
        a.IsPrefixApproximation i.val X ∧
        b.IsPrefixApproximation i.val X ∧
        a.representationAlpha b i ≤
          min (a.prefixAlphaCap i.val) (b.prefixAlphaCap i.val)) ∨
      (b.orderSequence.prefixSum i.val =
          a.orderSequence.prefixSum i.val + 1 ∧
        a.representationAlpha b i ≤ 0)) :
    a.RepresentationDefectCondition b := by
  intro i
  rcases hbranches i with ⟨X, hX, hY, hbound⟩ | ⟨hsum, hbound⟩
  · exact a.representationDefect_at_of_common_approximation
      b i X hX hY hbound
  · exact representationDefect_at_of_prefixSum_succ
      (alphaV := alphaV) (alphaW := alphaW) a b i hsum hbound

end BONG.GoodBONG

end Bong
