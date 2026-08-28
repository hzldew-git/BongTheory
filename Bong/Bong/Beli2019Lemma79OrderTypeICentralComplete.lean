/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeITerminalBoundary
import Bong.Bong.Beli2019Lemma79OrderTypeIPrimaryCentral

/-!
# Beli (2019), Lemma 7.9(i): endpoint-complete central source separation

The earlier central source-prefix theorem used the nonterminal form of
Lemma 6.9(v), and consequently carried the unnecessary hypothesis that the
right switch precedes the last unequal coordinate.  The terminal-boundary
completion of Lemma 6.9(v) removes that restriction.  This is the form needed
at the exceptional predecessor of the first type-I switch.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- In the central type-I interval, including when the right switch is the
last unequal coordinate, the source prefix lies strictly above the primary
coefficient cut used in Lemma 7.9(i). -/
theorem lemma79_typeI_even_sourcePrefix_gt_primaryCut_completeCentral
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (k : Nat) (hkNext : k + 1 < n + 2) (hkTwo : k + 2 < n + 2)
    (hkEven : Even k) (hleft : C.leftSwitch ≤ k)
    (hright : k < C.rightSwitch) :
    (((a.order (0 : Fin (n + 2)) + 1 -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) : WithTop ℚ) <
      a.truncatedPrefixDefect a ((-1) ^ ((k + 2) / 2)) 0 (k + 2) := by
  let current : Fin (n + 1) := ⟨k, by omega⟩
  let next : Fin (n + 1) := ⟨k + 1, by omega⟩
  have hkPlusTwoEven : Even (k + 2) := by
    rcases hkEven with ⟨d, hd⟩
    exact ⟨d + 1, by omega⟩
  have hweight := a.beli2019Lemma69_v_typeI_from_conditions
    b D C hfirst horder hdefect k hleft hright
  have halphaCurrent : 2 ≤ a.alphaValue current := by
    have h := lemma69_v_typeI_alpha_ge_two_of_leftEndpoint_eq
      a b D C hfirst (k + 2) (by omega) (by omega) hkPlusTwoEven
        hleft hright.le (by
          simpa only [current, show k + 2 - 2 = k by omega] using hweight)
    simpa only [current, show k + 2 - 2 = k by omega] using h
  have hendpoint := a.alphaLeftEndpoint_monotone
    (show current ≤ next by
      change k ≤ k + 1
      omega)
  have hcurrentCast : current.castSucc =
      (⟨k, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hnextCast : next.castSucc = ⟨k + 1, hkNext⟩ := by
    apply Fin.ext
    rfl
  have hcapQ :
      ((a.order ⟨k, by omega⟩ - a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) + 2 ≤
        a.alphaValue next := by
    unfold alphaLeftEndpoint at hendpoint
    rw [hcurrentCast, hnextCast] at hendpoint
    push_cast at hendpoint ⊢
    linarith
  have hcap :
      ((((a.order ⟨k, by omega⟩ -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) + 2 : ℚ) : WithTop ℚ) ≤
        a.prefixAlphaCap (k + 2) := by
    rw [a.prefixAlphaCap_of_internal (by omega) hkTwo]
    simpa only [next, show k + 2 - 1 = k + 1 by omega] using
      WithTop.coe_le_coe.mpr hcapQ
  have hraw := a.beli2019Lemma77_typeI_of_leftEndpoint_eq
    b D C hfirst (k + 2) (by omega) (by omega) hkPlusTwoEven
      hleft hright.le (by
        simpa only [show k + 2 - 2 = k by omega] using hweight)
  have hself :
      ((((a.order ⟨k, by omega⟩ -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) + 2 : ℚ) : WithTop ℚ) ≤
        a.truncatedPrefixDefect a ((-1) ^ ((k + 2) / 2)) 0 (k + 2) := by
    unfold truncatedPrefixDefect
    rw [a.prefixAlphaCap_zero]
    simp only [min_top_left]
    apply le_min
    · simpa only [alternatingPrefixDefect, GoodBONG.prefixProduct,
        BONG.prefixProduct_zero, mul_one,
        show k + 2 - 2 = k by omega,
        show k + 2 - 1 = k + 1 by omega] using hraw
    · exact hcap
  have hplateau := lemma77_typeI_source_plateau
    a b D C hfirst (k + 2) (by omega) (by omega) hkPlusTwoEven hright.le
  have hplateau' : a.order (0 : Fin (n + 2)) =
      a.order ⟨k, by omega⟩ := by
    simpa only [show k + 2 - 2 = k by omega] using hplateau
  have hstrict :
      (((a.order (0 : Fin (n + 2)) + 1 -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) : WithTop ℚ) <
        ((((a.order ⟨k, by omega⟩ -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) + 2 : ℚ) : WithTop ℚ) := by
    norm_cast
    linarith [hplateau']
  exact hstrict.trans_le hself

end BONG.GoodBONG

end Bong
