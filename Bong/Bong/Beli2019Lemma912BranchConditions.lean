/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912Lemma99Conditions

/-!
# Beli (2019), Lemma 9.12: exact branch conditions

This file combines the five parameter branches with the exact beta choices
and the shifted Lemma 9.9 conditions needed by the type-I construction.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {X : Type v} [AddCommGroup X] [Module K X]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {s : QuadraticSpace K X}
  {r : QuadraticSpace K W}
  {L : Lattice K V} {P : Lattice K X} {M : Lattice K W} {N : Nat}

set_option maxHeartbeats 1200000 in
-- The anisotropic branch reconstructs the discrete Lemma 9.6 boundary bound.
/-- The five paper branches give either the type-III parameters or exact
type-I beta data together with the shifted Lemma 9.9 conditions. -/
theorem beli2019Lemma912_typeIIIParameters_or_exists_typeIBetaConditions
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [parityW : Beli2009AlphaParityLaws.{u, w} K]
    (reference : GoodBONG s P 3)
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (R₁ R₂ A₁ : Int)
    (C : Beli2019Lemma99Conditions reference R₁ R₂ A₁)
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (hR₁ : a.order (0 : Fin (N + 5)) = R₁)
    (hR₂ : a.order (1 : Fin (N + 5)) = R₂)
    (hA₁ : a.alphaValue (0 : Fin (N + 4)) = (A₁ : ℚ))
    (hrefIsotropy : reference.Lemma814FirstThreeIsotropic ↔
      a.Lemma814FirstThreeIsotropic) :
    Beli2019Lemma912TypeIIIParameters a c ∨
      ∃ β₁ : Int,
        Beli2019Lemma912TypeIBetaData a c A₁ β₁ ∧
          Beli2019Lemma99Conditions reference R₁ (R₂ + 2) β₁ := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  rcases a.beli2019Lemma912_parameterBranches c profile with
    ⟨_, hfirstAlpha, hlarge⟩ |
    ⟨hfull, hfirstAlpha, hone⟩ |
    ⟨hstrict, hbelow⟩ |
    ⟨hstrict, hhalf, hisotropic⟩ |
    ⟨hstrict, hhalf, hanisotropic⟩
  · right
    rcases exists_beli2019Lemma912TypeIBetaData_of_equalSecondLarge
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
        a c profile hfirst hfirstAlpha hlarge with ⟨A, data⟩
    have hA : A = A₁ := by
      exact_mod_cast data.firstAlpha.symm.trans hA₁
    subst A
    refine ⟨A₁, data, ?_⟩
    letI : Beli2009AlphaParityLaws.{u, w} K := parityW
    exact Beli2019Lemma99Conditions.ofEqualSecondLarge
      (alphaV := alphaV) (alphaW := alphaW) reference a c profile
        R₁ R₂ A₁ C hfirst hR₁ hR₂ hA₁ hfirstAlpha hlarge
  · left
    exact ⟨hfull, hfirstAlpha, hone⟩
  · right
    rcases exists_beli2019Lemma912TypeIBetaData_of_belowHalfGap
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
        a c profile hfirst hstrict hbelow with ⟨A, data⟩
    have hA : A = A₁ := by
      exact_mod_cast data.firstAlpha.symm.trans hA₁
    subst A
    refine ⟨A₁ + 2, data, ?_⟩
    exact C.ofBelowHalfGap reference a c profile R₁ R₂ A₁
      hR₁ hR₂ hA₁ hbelow
  · right
    rcases exists_beli2019Lemma912TypeIBetaData_of_halfGapIsotropic
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
        a c profile hfirst hstrict hhalf with ⟨A, data⟩
    have hA : A = A₁ := by
      exact_mod_cast data.firstAlpha.symm.trans hA₁
    subst A
    refine ⟨A₁ + 1, data, ?_⟩
    exact C.ofHalfGapIsotropic reference a c profile R₁ R₂ A₁
      hR₁ hR₂ hA₁ hhalf (hrefIsotropy.mpr hisotropic)
  · right
    rcases exists_beli2019Lemma912TypeIBetaData_of_halfGapAnisotropic
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
        a c profile hfirst hstrict with ⟨A, data⟩
    have hA : A = A₁ := by
      exact_mod_cast data.firstAlpha.symm.trans hA₁
    subst A
    have hgapSharp :=
      a.beli2019Lemma912_firstGap_le_twoE_sub_four_of_strict_anisotropic
        (alphaV := alphaV) (parityV := parityV)
        (alphaW := alphaW) (parityW := parityW)
        c profile hstrict hhalf hanisotropic
    have hrefAnisotropic : reference.Lemma814FirstThreeAnisotropic := by
      apply (reference.not_firstThreeIsotropic_iff_anisotropic).mp
      intro hrefIsotropic
      exact a.not_firstThreeIsotropic_of_anisotropic hanisotropic
        (hrefIsotropy.mp hrefIsotropic)
    refine ⟨A₁, data, ?_⟩
    exact C.ofHalfGapAnisotropic reference a R₁ R₂ A₁ hR₁ hR₂
      hA₁ hhalf hgapSharp hrefAnisotropic

end BONG.GoodBONG

end Bong
