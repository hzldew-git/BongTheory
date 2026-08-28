/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006SectionFourInvariants

/-!
# Beli (2019), Lemma 7.16: composing capped prefix defects

The proof of condition 2.1(i) repeatedly combines two signed prefix defects.
This file records the paper-independent capped-defect bookkeeping.  The raw
quadratic defects combine by the multiplicative defect inequality, while the
two surviving endpoint caps are inherited from the two self-prefix bounds.
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
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- Two capped self-prefix defects give the corresponding mixed-prefix
defect.  The signs are kept explicit so the result can be reused for both
type-I and type-II blocks. -/
theorem mixedPrefixDefect_ge_of_selfPrefixDefects
    (a : GoodBONG q L (m + 1)) (c : GoodBONG r M (n + 1))
    (delta : WithTop ℚ) (epsilon eta zeta : Kˣ) (i j : Nat)
    (ha : delta ≤ a.truncatedPrefixDefect a epsilon 0 i)
    (hc : delta ≤ c.truncatedPrefixDefect c eta 0 j)
    (hsign : epsilon * eta = zeta) :
    delta ≤ a.truncatedPrefixDefect c zeta i j := by
  have haRaw : delta ≤
      defectOrder (K := K) (epsilon * a.prefixProduct i) := by
    simpa only [GoodBONG.prefixProduct, BONG.prefixProduct_zero, one_mul,
      mul_one] using
      ha.trans (a.truncatedPrefixDefect_le_defect a epsilon 0 i)
  have hcRaw : delta ≤
      defectOrder (K := K) (eta * c.prefixProduct j) := by
    simpa only [GoodBONG.prefixProduct, BONG.prefixProduct_zero, one_mul,
      mul_one] using
      hc.trans (c.truncatedPrefixDefect_le_defect c eta 0 j)
  have hraw : delta ≤ defectOrder (K := K)
      (zeta * a.prefixProduct i * c.prefixProduct j) := by
    calc
      delta ≤ min
          (defectOrder (K := K) (epsilon * a.prefixProduct i))
          (defectOrder (K := K) (eta * c.prefixProduct j)) :=
        le_min haRaw hcRaw
      _ ≤ defectOrder (K := K)
          ((epsilon * a.prefixProduct i) *
            (eta * c.prefixProduct j)) :=
        defectOrder_mul_ge_min _ _
      _ = defectOrder (K := K)
          (zeta * a.prefixProduct i * c.prefixProduct j) := by
        apply congrArg (defectOrder (K := K))
        rw [← hsign]
        ac_rfl
  have haCap : delta ≤ a.prefixAlphaCap i :=
    ha.trans (a.truncatedPrefixDefect_le_rightCap a epsilon 0 i)
  have hcCap : delta ≤ c.prefixAlphaCap j :=
    hc.trans (c.truncatedPrefixDefect_le_rightCap c eta 0 j)
  unfold truncatedPrefixDefect
  exact le_min hraw (le_min haCap hcCap)

/-- Concatenation of two consecutive capped segments in one BONG.  This is
the specialized form of Beli's domination principle used to join the
initial binary block to the later alternating block. -/
theorem selfPrefixDefect_ge_of_split
    (a : GoodBONG q L (m + 1)) (delta : WithTop ℚ)
    (epsilon eta zeta : Kˣ) (i j : Nat)
    (hleft : delta ≤ a.truncatedPrefixDefect a epsilon 0 i)
    (hright : delta ≤ a.truncatedPrefixDefect a eta i j)
    (hsign : epsilon * eta = zeta) :
    delta ≤ a.truncatedPrefixDefect a zeta 0 j := by
  calc
    delta ≤ min (a.truncatedPrefixDefect a epsilon 0 i)
        (a.truncatedPrefixDefect a eta i j) := le_min hleft hright
    _ ≤ a.truncatedPrefixDefect a (epsilon * eta) 0 j :=
      a.truncatedPrefixDefect_domination a a epsilon eta 0 i j
    _ = a.truncatedPrefixDefect a zeta 0 j := by rw [hsign]

end BONG.GoodBONG

end Bong
