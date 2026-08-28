/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912AnisotropicDefect
import Bong.Bong.Beli2019Lemma79DefectOdd
import Bong.Bong.Beli2019Lemma74RightEndpointComplete

/-!
# Beli (2019), Lemma 9.12: anisotropic defect propagation

This file propagates the two complementary mixed-prefix defect bounds from
an anisotropic scalar-failure index down to every intermediate prefix. It
also proves the parity needed to strictify the two bounds and obtains the
strict defect-sum inequality used by prefix-representation descent.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {Q : Lattice K U}

/-- Simultaneously replace both factors while retaining the two independent
segment signs. -/
theorem defectOrder_replace_both_signed
    (ε δ η a a' b b' : Kˣ) (x : WithTop ℚ)
    (htop : x ≤ defectOrder (K := K) (ε * a * b))
    (hleft : x ≤ defectOrder (K := K) (δ * a * a'))
    (hright : x ≤ defectOrder (K := K) (η * b * b')) :
    x ≤ defectOrder (K := K) ((ε * δ * η) * a' * b') := by
  have hleft' : x ≤ defectOrder (K := K) (a * (δ * a')) := by
    convert hleft using 1
    ac_rfl
  have hmid : x ≤ defectOrder (K := K) (ε * (δ * a') * b) :=
    (le_min htop hleft').trans
      (defectOrder_replace_left (K := K) ε a (δ * a') b)
  have hright' : x ≤ defectOrder (K := K) (b * (η * b')) := by
    convert hright using 1
    ac_rfl
  have hout : x ≤ defectOrder (K := K) (ε * (δ * a') * (η * b')) :=
    (le_min hmid hright').trans
      (defectOrder_replace_right (K := K) ε (δ * a') b (η * b'))
  convert hout using 1 <;> ac_rfl

end BONG.GoodBONG

namespace BONG.GoodBONG.Beli2019Lemma910Data

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {Q : Lattice K U} {N : Nat}

theorem comparisonAlpha_eq_failureThreshold
    (c : GoodBONG r M (N + 3)) (A₁ : Int)
    (i : RepresentationIndex (N + 3) (N + 3))
    (C : Beli2019Lemma912ComparisonAlphaAlternation c A₁ i)
    (k : Fin (N + 2)) (hk : k.val + 2 ≤ i.val) :
    c.alphaValue k =
      ((failureThreshold (K := K) A₁ k.val : Int) : ℚ) := by
  rcases Nat.mod_two_eq_zero_or_one k.val with hmod | hmod
  · rw [C.even k hk hmod,
      failureThreshold_of_even (K := K) A₁ k.val hmod]
  · rw [C.odd k hk hmod,
      failureThreshold_of_odd (K := K) A₁ k.val hmod]

theorem failureThreshold_eq_of_modEq (A₁ : Int) (k l : Nat)
    (hmod : k % 2 = l % 2) :
    failureThreshold (K := K) A₁ k =
      failureThreshold (K := K) A₁ l := by
  unfold failureThreshold
  rw [hmod]

theorem sourceAlpha_eq_failureThreshold
    (source : GoodBONG q L (N + 3)) (A₁ : Int)
    (i : RepresentationIndex (N + 3) (N + 3))
    (S : Beli2019Lemma912SourceAlphaAlternation source A₁ i)
    (k : Fin (N + 2)) (hkTwo : 2 ≤ k.val)
    (hki : k.val + 1 ≤ i.val) :
    source.alphaValue k =
      ((failureThreshold (K := K) A₁ k.val : Int) : ℚ) := by
  rcases Nat.mod_two_eq_zero_or_one k.val with hmod | hmod
  · rw [S.even k hkTwo hki hmod,
      failureThreshold_of_even (K := K) A₁ k.val hmod]
  · rw [S.odd k hkTwo hki hmod,
      failureThreshold_of_odd (K := K) A₁ k.val hmod]

theorem sourceOrder_eq_of_evenPrefixGap
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (h l : Nat) (hh : 3 ≤ h) (hhl : h ≤ l) (hli : l ≤ i.val + 1)
    (heven : Even (l - h)) :
    (a.castLength hlength).order ⟨h - 1, by have := i.lt_large; omega⟩ =
      (a.castLength hlength).order ⟨l - 1, by have := i.lt_large; omega⟩ := by
  have hiLarge := i.lt_large
  rcases hhl.eq_or_lt with hEq | hlt
  · subst l
    rfl
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  let left : Fin (N + 3) := ⟨h - 1, by omega⟩
  let right : Fin (N + 3) := ⟨l - 1, by omega⟩
  have hleftAgreement : target.order left = source.order left :=
    E.order_castLength_eq_source_of_two_le a D horders hlength left
      (by simp only [left]; omega)
  have hrightAgreement : target.order right = source.order right :=
    E.order_castLength_eq_source_of_two_le a D horders hlength right
      (by simp only [right]; omega)
  change source.order left = source.order right
  rw [← hleftAgreement, ← hrightAgreement]
  rcases Nat.mod_two_eq_zero_or_one (h - 1) with hmod | hmod
  · have hrightMod : (l - 1) % 2 = 0 := by
      rcases heven with ⟨d, hd⟩
      omega
    rw [O.target_even left (by simp only [left]; omega)
        (by simpa only [left] using hmod),
      O.target_even right (by simp only [right]; omega)
        (by simpa only [right] using hrightMod)]
  · have hrightMod : (l - 1) % 2 = 1 := by
      rcases heven with ⟨d, hd⟩
      omega
    rw [O.target_odd left (by simp only [left]; omega)
        (by simpa only [left] using hmod),
      O.target_odd right (by simp only [right]; omega)
        (by simpa only [right] using hrightMod)]

theorem comparisonOrder_eq_of_evenPrefixGap
    {R₁ R₂ : Int}
    (target : GoodBONG q L (N + 3))
    (c : GoodBONG r M (N + 3))
    (i : RepresentationIndex (N + 3) (N + 3))
    (O : Beli2019Lemma912FailureAlternatingOrders target c R₁ R₂ i)
    (h l : Nat) (hh : 1 ≤ h) (hhl : h ≤ l) (hli : l ≤ i.val)
    (heven : Even (l - h)) :
    c.order ⟨h - 1, by have := i.lt_large; omega⟩ =
      c.order ⟨l - 1, by have := i.lt_large; omega⟩ := by
  have hiLarge := i.lt_large
  rcases hhl.eq_or_lt with hEq | hlt
  · subst l
    rfl
  let left : Fin (N + 3) := ⟨h - 1, by omega⟩
  let right : Fin (N + 3) := ⟨l - 1, by omega⟩
  change c.order left = c.order right
  rcases Nat.mod_two_eq_zero_or_one (h - 1) with hmod | hmod
  · have hrightMod : (l - 1) % 2 = 0 := by
      rcases heven with ⟨d, hd⟩
      omega
    rw [O.comparison_even left (by simp only [left]; omega)
        (by simpa only [left] using hmod),
      O.comparison_even right (by simp only [right]; omega)
        (by simpa only [right] using hrightMod)]
  · have hrightMod : (l - 1) % 2 = 1 := by
      rcases heven with ⟨d, hd⟩
      omega
    rw [O.comparison_odd left (by simp only [left]; omega)
        (by simpa only [left] using hmod),
      O.comparison_odd right (by simp only [right]; omega)
        (by simpa only [right] using hrightMod)]

theorem sourceSelfDefect_ge_failureThreshold
    [Beli2006AlphaLaws.{u, v} K]
    (source : GoodBONG q L (N + 3)) (A₁ : Int)
    (i : RepresentationIndex (N + 3) (N + 3))
    (S : Beli2019Lemma912SourceAlphaAlternation source A₁ i)
    (h l : Nat) (hh : 3 ≤ h) (hhl : h < l)
    (hli : l ≤ i.val + 1) (heven : Even (l - h))
    (horder : source.order ⟨h - 1, by have := i.lt_large; omega⟩ =
      source.order ⟨l - 1, by have := i.lt_large; omega⟩) :
    (((failureThreshold (K := K) A₁ (h - 1) : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K)
        (((-1 : Kˣ) ^ ((l - h) / 2)) *
          source.prefixProduct h * source.prefixProduct l) := by
  let first : Fin (N + 2) := ⟨h - 1, by
    have := i.lt_large
    omega⟩
  let endpoint : RepresentationIndex (N + 3) (N + 3) := {
    val := l - 1
    pos := by omega
    lt_large := by
      have := i.lt_large
      omega
    le_small := by
      have := i.lt_large
      omega
  }
  have hfirstEndpoint : first.val < endpoint.val := by
    simp only [first, endpoint]
    omega
  have hdifference : Even (endpoint.val - first.val) := by
    simpa only [first, endpoint,
      show l - 1 - (h - 1) = l - h by omega] using heven
  have hfirstCast : first.castSucc =
      (⟨h - 1, by have := i.lt_large; omega⟩ : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  have hendpointValue :
      (⟨endpoint.val, endpoint.lt_large⟩ : Fin (N + 3)) =
        ⟨l - 1, by have := i.lt_large; omega⟩ := by
    apply Fin.ext
    simp only [endpoint]
  have horder' : source.order first.castSucc =
      source.order ⟨endpoint.val, endpoint.lt_large⟩ := by
    rw [hfirstCast, hendpointValue]
    exact horder
  have htruncatedRaw :=
    source.beli2019Lemma74_iii_rightEndpoint_complete
      first endpoint hfirstEndpoint hdifference horder'
  have htruncated :
      source.truncatedPrefixDefect source
          ((-1 : Kˣ) ^ ((l - h) / 2)) h l =
        (source.alphaValue first : WithTop ℚ) := by
    simpa only [first, endpoint,
      show l - 1 - (h - 1) = l - h by omega,
      show h - 1 + 1 = h by omega,
      show l - 1 + 1 = l by omega] using htruncatedRaw
  have halpha := sourceAlpha_eq_failureThreshold
    source A₁ i S first (by simp only [first]; omega)
      (by simp only [first]; omega)
  calc
    (((failureThreshold (K := K) A₁ (h - 1) : Int) : ℚ) : WithTop ℚ) =
        (source.alphaValue first : WithTop ℚ) := by
          exact congrArg (fun x : ℚ => (x : WithTop ℚ)) halpha.symm
    _ = source.truncatedPrefixDefect source
          ((-1 : Kˣ) ^ ((l - h) / 2)) h l := htruncated.symm
    _ ≤ defectOrder (K := K)
        (((-1 : Kˣ) ^ ((l - h) / 2)) *
          source.prefixProduct h * source.prefixProduct l) :=
      source.truncatedPrefixDefect_le_defect source
        ((-1 : Kˣ) ^ ((l - h) / 2)) h l

theorem le_defectOrder_selfSquare (x : WithTop ℚ) (b : Kˣ) :
    x ≤ defectOrder (K := K) ((1 : Kˣ) * b * b) := by
  calc
    x ≤ ⊤ := le_top
    _ = defectOrder (K := K) ((1 : Kˣ) * b * b) := by
      rw [show (1 : Kˣ) * b * b = 1 * b ^ 2 by simp only [one_mul, pow_two],
        defectOrder_mul_square, defectOrder_one]

theorem sourceSelfDefect_ge_failureThreshold_of_le
    [Beli2006AlphaLaws.{u, v} K]
    (source : GoodBONG q L (N + 3)) (A₁ : Int)
    (i : RepresentationIndex (N + 3) (N + 3))
    (S : Beli2019Lemma912SourceAlphaAlternation source A₁ i)
    (h l : Nat) (hh : 3 ≤ h) (hhl : h ≤ l)
    (hli : l ≤ i.val + 1) (heven : Even (l - h))
    (horder : source.order ⟨h - 1, by have := i.lt_large; omega⟩ =
      source.order ⟨l - 1, by have := i.lt_large; omega⟩) :
    (((failureThreshold (K := K) A₁ (h - 1) : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K)
        (((-1 : Kˣ) ^ ((l - h) / 2)) *
          source.prefixProduct h * source.prefixProduct l) := by
  by_cases heq : h = l
  · subst l
    simpa only [Nat.sub_self, Nat.zero_div, pow_zero] using
      le_defectOrder_selfSquare
        (K := K)
        ((((failureThreshold (K := K) A₁ (h - 1) : Int) : ℚ) : WithTop ℚ))
        (source.prefixProduct h)
  · exact sourceSelfDefect_ge_failureThreshold
      source A₁ i S h l hh (lt_of_le_of_ne hhl heq)
        hli heven horder

theorem comparisonSelfDefect_ge_failureThreshold
    [Beli2006AlphaLaws.{u, w} K]
    (c : GoodBONG r M (N + 3)) (A₁ : Int)
    (i : RepresentationIndex (N + 3) (N + 3))
    (C : Beli2019Lemma912ComparisonAlphaAlternation c A₁ i)
    (h l : Nat) (hh : 1 ≤ h) (hhl : h < l)
    (hli : l ≤ i.val)
    (heven : Even (l - h))
    (horder : c.order ⟨h - 1, by have := i.lt_large; omega⟩ =
      c.order ⟨l - 1, by have := i.lt_large; omega⟩) :
    (((failureThreshold (K := K) A₁ (h - 1) : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K)
        (((-1 : Kˣ) ^ ((l - h) / 2)) *
          c.prefixProduct h * c.prefixProduct l) := by
  let first : Fin (N + 2) := ⟨h - 1, by have := i.lt_large; omega⟩
  let last : Fin (N + 2) := ⟨l - 1, by have := i.lt_large; omega⟩
  have hfirstLast : first < last := by
    change h - 1 < l - 1
    omega
  have hdifference : Even (last.val - first.val) := by
    simpa only [first, last, show l - 1 - (h - 1) = l - h by omega] using heven
  have hfirstCast : first.castSucc =
      (⟨h - 1, by have := i.lt_large; omega⟩ : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  have hlastCast : last.castSucc =
      (⟨l - 1, by have := i.lt_large; omega⟩ : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  have horder' : c.order first.castSucc = c.order last.castSucc := by
    rw [hfirstCast, hlastCast]
    exact horder
  have h74 := c.beli2019Lemma74_iii first last
    hfirstLast hdifference horder'
  dsimp only at h74
  have htruncated := h74.2.1.trans
    (congrArg (fun x : ℚ => (x : WithTop ℚ)) h74.2.2)
  have htruncated' :
      c.truncatedPrefixDefect c
          ((-1 : Kˣ) ^ ((l - h) / 2)) h l =
        (c.alphaValue first : WithTop ℚ) := by
    simpa only [first, last,
      show l - 1 - (h - 1) = l - h by omega,
      show h - 1 + 1 = h by omega,
      show l - 1 + 1 = l by omega] using htruncated
  have halpha := comparisonAlpha_eq_failureThreshold
    c A₁ i C first (by simp only [first]; omega)
  calc
    (((failureThreshold (K := K) A₁ (h - 1) : Int) : ℚ) : WithTop ℚ) =
        (c.alphaValue first : WithTop ℚ) := by
          exact congrArg (fun x : ℚ => (x : WithTop ℚ)) halpha.symm
    _ = c.truncatedPrefixDefect c
          ((-1 : Kˣ) ^ ((l - h) / 2)) h l := htruncated'.symm
    _ ≤ defectOrder (K := K)
        (((-1 : Kˣ) ^ ((l - h) / 2)) *
          c.prefixProduct h * c.prefixProduct l) :=
      c.truncatedPrefixDefect_le_defect c
        ((-1 : Kˣ) ^ ((l - h) / 2)) h l

theorem comparisonSelfDefect_ge_failureThreshold_of_le
    [Beli2006AlphaLaws.{u, w} K]
    (c : GoodBONG r M (N + 3)) (A₁ : Int)
    (i : RepresentationIndex (N + 3) (N + 3))
    (C : Beli2019Lemma912ComparisonAlphaAlternation c A₁ i)
    (h l : Nat) (hh : 1 ≤ h) (hhl : h ≤ l)
    (hli : l ≤ i.val)
    (heven : Even (l - h))
    (horder : c.order ⟨h - 1, by have := i.lt_large; omega⟩ =
      c.order ⟨l - 1, by have := i.lt_large; omega⟩) :
    (((failureThreshold (K := K) A₁ (h - 1) : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K)
        (((-1 : Kˣ) ^ ((l - h) / 2)) *
          c.prefixProduct h * c.prefixProduct l) := by
  by_cases heq : h = l
  · subst l
    simpa only [Nat.sub_self, Nat.zero_div, pow_zero] using
      le_defectOrder_selfSquare
        (K := K)
        ((((failureThreshold (K := K) A₁ (h - 1) : Int) : ℚ) : WithTop ℚ))
        (c.prefixProduct h)
  · exact comparisonSelfDefect_ge_failureThreshold
      c A₁ i C h l hh (lt_of_le_of_ne hhl heq)
        hli heven horder

theorem diagonalMixedDefect_ge_failureThreshold
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [comparisonLaws : Beli2006AlphaLaws.{u, w} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (S : Beli2019Lemma912SourceAlphaAlternation
      (a.castLength hlength) A₁ i)
    (C : Beli2019Lemma912ComparisonAlphaAlternation c A₁ i)
    (T : Beli2019Lemma912TopMixedDefectBounds
      (a.castLength hlength) c A₁ i)
    (j : Nat) (hjThree : 3 ≤ j) (hji : j ≤ i.val) :
    (((failureThreshold (K := K) A₁ (j - 1) : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K)
        ((1 : Kˣ) * (a.castLength hlength).prefixProduct j *
          c.prefixProduct j) := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  have htopDiagonal :
      (((failureThreshold (K := K) A₁ (i.val - 1) : Int) : ℚ) : WithTop ℚ) ≤
        defectOrder (K := K)
          ((1 : Kˣ) * source.prefixProduct i.val * c.prefixProduct i.val) :=
    T.diagonal.trans
      (source.truncatedPrefixDefect_le_defect c 1 i.val i.val)
  have htopShifted :
      (((failureThreshold (K := K) A₁ (i.val - 2) : Int) : ℚ) : WithTop ℚ) ≤
        defectOrder (K := K)
          ((-1 : Kˣ) * source.prefixProduct (i.val + 1) *
            c.prefixProduct (i.val - 1)) :=
    T.shifted.trans
      (source.truncatedPrefixDefect_le_defect c (-1)
        (i.val + 1) (i.val - 1))
  change
    (((failureThreshold (K := K) A₁ (j - 1) : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K)
        ((1 : Kˣ) * source.prefixProduct j * c.prefixProduct j)
  by_cases hjiEq : j = i.val
  · subst j
    exact htopDiagonal
  have hjiLt : j < i.val := lt_of_le_of_ne hji hjiEq
  by_cases hgapEven : Even (i.val - j)
  · have hgapMod : (i.val - j) % 2 = 0 := Nat.even_iff.mp hgapEven
    have hthresholdMod : (j - 1) % 2 = (i.val - 1) % 2 := by omega
    have hthreshold := failureThreshold_eq_of_modEq
      (K := K) A₁ (j - 1) (i.val - 1) hthresholdMod
    have htop :
        (((failureThreshold (K := K) A₁ (j - 1) : Int) : ℚ) : WithTop ℚ) ≤
          defectOrder (K := K)
            ((1 : Kˣ) * source.prefixProduct i.val * c.prefixProduct i.val) := by
      rw [hthreshold]
      exact htopDiagonal
    have hsourceOrder := sourceOrder_eq_of_evenPrefixGap
      a c D E horders hlength i O j i.val hjThree hji (by omega) hgapEven
    have hcomparisonOrder := comparisonOrder_eq_of_evenPrefixGap
      target c i O j i.val (by omega) hji (by omega) hgapEven
    have hsourceSelf := by
      letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
      exact sourceSelfDefect_ge_failureThreshold_of_le
        source A₁ i S j i.val hjThree hji (by omega)
          hgapEven hsourceOrder
    have hcomparisonSelf := by
      letI : Beli2006AlphaLaws.{u, w} K := comparisonLaws
      exact comparisonSelfDefect_ge_failureThreshold_of_le
        c A₁ i C j i.val (by omega) hji (by omega)
          hgapEven hcomparisonOrder
    have hsourceSelf' :
        (((failureThreshold (K := K) A₁ (j - 1) : Int) : ℚ) : WithTop ℚ) ≤
          defectOrder (K := K)
            (((-1 : Kˣ) ^ ((i.val - j) / 2)) *
              source.prefixProduct i.val * source.prefixProduct j) := by
      convert hsourceSelf using 1 <;> ac_rfl
    have hcomparisonSelf' :
        (((failureThreshold (K := K) A₁ (j - 1) : Int) : ℚ) : WithTop ℚ) ≤
          defectOrder (K := K)
            (((-1 : Kˣ) ^ ((i.val - j) / 2)) *
              c.prefixProduct i.val * c.prefixProduct j) := by
      convert hcomparisonSelf using 1 <;> ac_rfl
    exact defectOrder_replace_both
      (K := K) 1 ((-1 : Kˣ) ^ ((i.val - j) / 2))
        (source.prefixProduct i.val) (source.prefixProduct j)
        (c.prefixProduct i.val) (c.prefixProduct j)
        ((((failureThreshold (K := K) A₁ (j - 1) : Int) : ℚ) : WithTop ℚ))
        htop hsourceSelf' hcomparisonSelf'
  · have hgapMod : (i.val - j) % 2 = 1 := Nat.not_even_iff.mp hgapEven
    have hsourceGap : Even ((i.val + 1) - j) :=
      Nat.even_iff.mpr (by omega)
    have hcomparisonGap : Even ((i.val - 1) - j) :=
      Nat.even_iff.mpr (by omega)
    have hthresholdMod : (j - 1) % 2 = (i.val - 2) % 2 := by omega
    have hthreshold := failureThreshold_eq_of_modEq
      (K := K) A₁ (j - 1) (i.val - 2) hthresholdMod
    have htop :
        (((failureThreshold (K := K) A₁ (j - 1) : Int) : ℚ) : WithTop ℚ) ≤
          defectOrder (K := K)
            ((-1 : Kˣ) * source.prefixProduct (i.val + 1) *
              c.prefixProduct (i.val - 1)) := by
      rw [hthreshold]
      exact htopShifted
    have hsourceOrder := sourceOrder_eq_of_evenPrefixGap
      a c D E horders hlength i O j (i.val + 1) hjThree
        (by omega) le_rfl hsourceGap
    have hcomparisonOrder := comparisonOrder_eq_of_evenPrefixGap
      target c i O j (i.val - 1) (by omega) (by omega) (by omega)
        hcomparisonGap
    have hsourceSelf := by
      letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
      exact sourceSelfDefect_ge_failureThreshold_of_le
        source A₁ i S j (i.val + 1) hjThree (by omega)
          le_rfl hsourceGap hsourceOrder
    have hcomparisonSelf := by
      letI : Beli2006AlphaLaws.{u, w} K := comparisonLaws
      exact comparisonSelfDefect_ge_failureThreshold_of_le
        c A₁ i C j (i.val - 1) (by omega) (by omega)
          (by omega) hcomparisonGap hcomparisonOrder
    let δ : Kˣ := (-1 : Kˣ) ^ (((i.val + 1) - j) / 2)
    let η : Kˣ := (-1 : Kˣ) ^ (((i.val - 1) - j) / 2)
    have hsourceSelf' :
        (((failureThreshold (K := K) A₁ (j - 1) : Int) : ℚ) : WithTop ℚ) ≤
          defectOrder (K := K)
            (δ * source.prefixProduct (i.val + 1) * source.prefixProduct j) := by
      dsimp only [δ]
      convert hsourceSelf using 1 <;> ac_rfl
    have hcomparisonSelf' :
        (((failureThreshold (K := K) A₁ (j - 1) : Int) : ℚ) : WithTop ℚ) ≤
          defectOrder (K := K)
            (η * c.prefixProduct (i.val - 1) * c.prefixProduct j) := by
      dsimp only [η]
      convert hcomparisonSelf using 1 <;> ac_rfl
    have hsum :
        ((i.val + 1 - j) / 2) + ((i.val - 1 - j) / 2) =
          i.val - j := by omega
    have hgapOdd : Odd (i.val - j) := Nat.not_even_iff_odd.mp hgapEven
    have hsign : ((-1 : Kˣ) * δ * η) = 1 := by
      dsimp only [δ, η]
      calc
        (-1 : Kˣ) * (-1 : Kˣ) ^ ((i.val + 1 - j) / 2) *
              (-1 : Kˣ) ^ ((i.val - 1 - j) / 2) =
            (-1 : Kˣ) * (-1 : Kˣ) ^
              (((i.val + 1 - j) / 2) + ((i.val - 1 - j) / 2)) := by
                rw [pow_add]
                ac_rfl
        _ = (-1 : Kˣ) * (-1 : Kˣ) ^ (i.val - j) := by rw [hsum]
        _ = 1 := by rw [hgapOdd.neg_one_pow]; simp
    have hout := defectOrder_replace_both_signed
      (K := K) (-1) δ η
        (source.prefixProduct (i.val + 1)) (source.prefixProduct j)
        (c.prefixProduct (i.val - 1)) (c.prefixProduct j)
        ((((failureThreshold (K := K) A₁ (j - 1) : Int) : ℚ) : WithTop ℚ))
        htop hsourceSelf' hcomparisonSelf'
    rw [hsign] at hout
    exact hout

theorem shiftedMixedDefect_ge_failureThreshold
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [comparisonLaws : Beli2006AlphaLaws.{u, w} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (S : Beli2019Lemma912SourceAlphaAlternation
      (a.castLength hlength) A₁ i)
    (C : Beli2019Lemma912ComparisonAlphaAlternation c A₁ i)
    (T : Beli2019Lemma912TopMixedDefectBounds
      (a.castLength hlength) c A₁ i)
    (j : Nat) (hjTwo : 2 ≤ j) (hji : j ≤ i.val) :
    (((failureThreshold (K := K) A₁ (j - 2) : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K)
        ((-1 : Kˣ) * (a.castLength hlength).prefixProduct (j + 1) *
          c.prefixProduct (j - 1)) := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  have htopDiagonal :
      (((failureThreshold (K := K) A₁ (i.val - 1) : Int) : ℚ) : WithTop ℚ) ≤
        defectOrder (K := K)
          ((1 : Kˣ) * source.prefixProduct i.val * c.prefixProduct i.val) :=
    T.diagonal.trans
      (source.truncatedPrefixDefect_le_defect c 1 i.val i.val)
  have htopShifted :
      (((failureThreshold (K := K) A₁ (i.val - 2) : Int) : ℚ) : WithTop ℚ) ≤
        defectOrder (K := K)
          ((-1 : Kˣ) * source.prefixProduct (i.val + 1) *
            c.prefixProduct (i.val - 1)) :=
    T.shifted.trans
      (source.truncatedPrefixDefect_le_defect c (-1)
        (i.val + 1) (i.val - 1))
  change
    (((failureThreshold (K := K) A₁ (j - 2) : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K)
        ((-1 : Kˣ) * source.prefixProduct (j + 1) *
          c.prefixProduct (j - 1))
  by_cases hjiEq : j = i.val
  · subst j
    exact htopShifted
  have hjiLt : j < i.val := lt_of_le_of_ne hji hjiEq
  by_cases hgapEven : Even (i.val - j)
  · have hgapMod : (i.val - j) % 2 = 0 := Nat.even_iff.mp hgapEven
    have hthresholdMod : (j - 2) % 2 = (i.val - 2) % 2 := by omega
    have hthreshold := failureThreshold_eq_of_modEq
      (K := K) A₁ (j - 2) (i.val - 2) hthresholdMod
    have htop :
        (((failureThreshold (K := K) A₁ (j - 2) : Int) : ℚ) : WithTop ℚ) ≤
          defectOrder (K := K)
            ((-1 : Kˣ) * source.prefixProduct (i.val + 1) *
              c.prefixProduct (i.val - 1)) := by
      rw [hthreshold]
      exact htopShifted
    have hsourceGap : Even ((i.val + 1) - (j + 1)) := by
      simpa only [show i.val + 1 - (j + 1) = i.val - j by omega] using hgapEven
    have hcomparisonGap : Even ((i.val - 1) - (j - 1)) := by
      simpa only [show i.val - 1 - (j - 1) = i.val - j by omega] using hgapEven
    have hsourceOrder := sourceOrder_eq_of_evenPrefixGap
      a c D E horders hlength i O (j + 1) (i.val + 1) (by omega)
        (by omega) le_rfl hsourceGap
    have hcomparisonOrder := comparisonOrder_eq_of_evenPrefixGap
      target c i O (j - 1) (i.val - 1) (by omega) (by omega)
        (by omega) hcomparisonGap
    have hsourceSelfRaw := by
      letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
      exact sourceSelfDefect_ge_failureThreshold_of_le
        source A₁ i S (j + 1) (i.val + 1) (by omega)
          (by omega) le_rfl hsourceGap hsourceOrder
    have hsourceThresholdMod : j % 2 = (j - 2) % 2 := by omega
    have hsourceThreshold := failureThreshold_eq_of_modEq
      (K := K) A₁ j (j - 2) hsourceThresholdMod
    have hsourceSelf :
        (((failureThreshold (K := K) A₁ (j - 2) : Int) : ℚ) : WithTop ℚ) ≤
          defectOrder (K := K)
            (((-1 : Kˣ) ^ ((i.val - j) / 2)) *
              source.prefixProduct (j + 1) *
                source.prefixProduct (i.val + 1)) := by
      simpa only [hsourceThreshold,
        show j + 1 - 1 = j by omega,
        show i.val + 1 - (j + 1) = i.val - j by omega] using hsourceSelfRaw
    have hcomparisonSelf := by
      letI : Beli2006AlphaLaws.{u, w} K := comparisonLaws
      exact comparisonSelfDefect_ge_failureThreshold_of_le
        c A₁ i C (j - 1) (i.val - 1) (by omega)
          (by omega) (by omega) hcomparisonGap hcomparisonOrder
    have hsourceSelf' :
        (((failureThreshold (K := K) A₁ (j - 2) : Int) : ℚ) : WithTop ℚ) ≤
          defectOrder (K := K)
            (((-1 : Kˣ) ^ ((i.val - j) / 2)) *
              source.prefixProduct (i.val + 1) *
                source.prefixProduct (j + 1)) := by
      convert hsourceSelf using 1 <;> ac_rfl
    have hcomparisonSelf' :
        (((failureThreshold (K := K) A₁ (j - 2) : Int) : ℚ) : WithTop ℚ) ≤
          defectOrder (K := K)
            (((-1 : Kˣ) ^ ((i.val - j) / 2)) *
              c.prefixProduct (i.val - 1) * c.prefixProduct (j - 1)) := by
      have hnormalized :
          (((failureThreshold (K := K) A₁ (j - 2) : Int) : ℚ) : WithTop ℚ) ≤
            defectOrder (K := K)
              (((-1 : Kˣ) ^ ((i.val - j) / 2)) *
                c.prefixProduct (j - 1) * c.prefixProduct (i.val - 1)) := by
        simpa only [show j - 1 - 1 = j - 2 by omega,
          show i.val - 1 - (j - 1) = i.val - j by omega] using hcomparisonSelf
      convert hnormalized using 1 <;> ac_rfl
    exact defectOrder_replace_both
      (K := K) (-1) ((-1 : Kˣ) ^ ((i.val - j) / 2))
        (source.prefixProduct (i.val + 1)) (source.prefixProduct (j + 1))
        (c.prefixProduct (i.val - 1)) (c.prefixProduct (j - 1))
        ((((failureThreshold (K := K) A₁ (j - 2) : Int) : ℚ) : WithTop ℚ))
        htop hsourceSelf' hcomparisonSelf'
  · have hgapMod : (i.val - j) % 2 = 1 := Nat.not_even_iff.mp hgapEven
    have hsourceGap : Even (i.val - (j + 1)) :=
      Nat.even_iff.mpr (by omega)
    have hcomparisonGap : Even (i.val - (j - 1)) :=
      Nat.even_iff.mpr (by omega)
    have hthresholdMod : (j - 2) % 2 = (i.val - 1) % 2 := by omega
    have hthreshold := failureThreshold_eq_of_modEq
      (K := K) A₁ (j - 2) (i.val - 1) hthresholdMod
    have htop :
        (((failureThreshold (K := K) A₁ (j - 2) : Int) : ℚ) : WithTop ℚ) ≤
          defectOrder (K := K)
            ((1 : Kˣ) * source.prefixProduct i.val * c.prefixProduct i.val) := by
      rw [hthreshold]
      exact htopDiagonal
    have hsourceOrder := sourceOrder_eq_of_evenPrefixGap
      a c D E horders hlength i O (j + 1) i.val (by omega)
        (by omega) (by omega) hsourceGap
    have hcomparisonOrder := comparisonOrder_eq_of_evenPrefixGap
      target c i O (j - 1) i.val (by omega) (by omega) le_rfl
        hcomparisonGap
    have hsourceSelfRaw := by
      letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
      exact sourceSelfDefect_ge_failureThreshold_of_le
        source A₁ i S (j + 1) i.val (by omega) (by omega)
          (by omega) hsourceGap hsourceOrder
    have hsourceThresholdMod : j % 2 = (j - 2) % 2 := by omega
    have hsourceThreshold := failureThreshold_eq_of_modEq
      (K := K) A₁ j (j - 2) hsourceThresholdMod
    have hsourceSelf :
        (((failureThreshold (K := K) A₁ (j - 2) : Int) : ℚ) : WithTop ℚ) ≤
          defectOrder (K := K)
            (((-1 : Kˣ) ^ ((i.val - (j + 1)) / 2)) *
              source.prefixProduct (j + 1) * source.prefixProduct i.val) := by
      simpa only [show j + 1 - 1 = j by omega, hsourceThreshold] using hsourceSelfRaw
    have hcomparisonSelf := by
      letI : Beli2006AlphaLaws.{u, w} K := comparisonLaws
      exact comparisonSelfDefect_ge_failureThreshold_of_le
        c A₁ i C (j - 1) i.val (by omega) (by omega)
          le_rfl hcomparisonGap hcomparisonOrder
    let δ : Kˣ := (-1 : Kˣ) ^ ((i.val - (j + 1)) / 2)
    let η : Kˣ := (-1 : Kˣ) ^ ((i.val - (j - 1)) / 2)
    have hsourceSelf' :
        (((failureThreshold (K := K) A₁ (j - 2) : Int) : ℚ) : WithTop ℚ) ≤
          defectOrder (K := K)
            (δ * source.prefixProduct i.val * source.prefixProduct (j + 1)) := by
      dsimp only [δ]
      convert hsourceSelf using 1 <;> ac_rfl
    have hcomparisonSelf' :
        (((failureThreshold (K := K) A₁ (j - 2) : Int) : ℚ) : WithTop ℚ) ≤
          defectOrder (K := K)
            (η * c.prefixProduct i.val * c.prefixProduct (j - 1)) := by
      dsimp only [η]
      convert hcomparisonSelf using 1 <;> ac_rfl
    have hsum :
        ((i.val - (j + 1)) / 2) + ((i.val - (j - 1)) / 2) =
          i.val - j := by omega
    have hgapOdd : Odd (i.val - j) := Nat.not_even_iff_odd.mp hgapEven
    have hsign : ((1 : Kˣ) * δ * η) = -1 := by
      dsimp only [δ, η]
      calc
        (1 : Kˣ) * (-1 : Kˣ) ^ ((i.val - (j + 1)) / 2) *
              (-1 : Kˣ) ^ ((i.val - (j - 1)) / 2) =
            (-1 : Kˣ) ^
              (((i.val - (j + 1)) / 2) + ((i.val - (j - 1)) / 2)) := by
                rw [pow_add]
                simp only [one_mul]
        _ = (-1 : Kˣ) ^ (i.val - j) := by rw [hsum]
        _ = -1 := hgapOdd.neg_one_pow
    have hout := defectOrder_replace_both_signed
      (K := K) 1 δ η
        (source.prefixProduct i.val) (source.prefixProduct (j + 1))
        (c.prefixProduct i.val) (c.prefixProduct (j - 1))
        ((((failureThreshold (K := K) A₁ (j - 2) : Int) : ℚ) : WithTop ℚ))
        htop hsourceSelf' hcomparisonSelf'
    rw [hsign] at hout
    exact hout

theorem prefixSum_modEq_of_entryOrZero_modEq
    {m n : Nat} (x : BeliOrderSequence m Int)
    (y : BeliOrderSequence n Int) (j : Nat)
    (hentry : ∀ k : Nat, k < j →
      Int.ModEq 2 (x.entryOrZero k) (y.entryOrZero k)) :
    Int.ModEq 2 (x.prefixSum j) (y.prefixSum j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show j + 1 = j + 1 by rfl, x.prefixSum_succ, y.prefixSum_succ]
      exact (ih (fun k hk ↦ hentry k (by omega))).add
        (hentry j (by omega))

theorem sourceComparisonOrder_modEq_two
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiThree : 3 ≤ i.val)
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (k : Nat) (hk : k < i.val) :
    Int.ModEq 2
      ((a.castLength hlength).orderSequence.entryOrZero k)
      (c.orderSequence.entryOrZero k) := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  have hiLarge := i.lt_large
  have hkRank : k < N + 3 := hk.trans i.lt_large
  rw [source.orderSequence.entryOrZero_of_lt hkRank,
    c.orderSequence.entryOrZero_of_lt hkRank]
  simp only [orderSequence_at]
  by_cases hkZero : k = 0
  · subst k
    let zero : Fin 3 := ⟨0, by omega⟩
    have hsourceZero : source.order (⟨0, by omega⟩ : Fin (N + 3)) = R₁ := by
      rw [GoodBONG.order_castLength]
      have hindex : (⟨0, by omega⟩ : Fin (3 + N)) =
          Fin.castAdd N zero := by
        apply Fin.ext
        rfl
      rw [hindex, horders zero]
      rfl
    have hcomparisonZero : c.order (⟨0, by omega⟩ : Fin (N + 3)) = R₁ :=
      O.comparison_even (0 : Fin (N + 3))
        (by change 0 + 1 ≤ i.val; omega) (by norm_num)
    rw [hsourceZero, hcomparisonZero]
  by_cases hkOne : k = 1
  · subst k
    let one : Fin 3 := ⟨1, by omega⟩
    have hsourceOne : source.order (⟨1, by omega⟩ : Fin (N + 3)) = R₂ := by
      rw [GoodBONG.order_castLength]
      have hindex : (⟨1, by omega⟩ : Fin (3 + N)) =
          Fin.castAdd N one := by
        apply Fin.ext
        rfl
      rw [hindex, horders one]
      rfl
    have hcomparisonOne : c.order (⟨1, by omega⟩ : Fin (N + 3)) = R₂ + 2 :=
      O.comparison_odd (1 : Fin (N + 3))
        (by change 1 + 1 ≤ i.val; omega) (by norm_num)
    rw [hsourceOne, hcomparisonOne, Int.modEq_iff_dvd]
    norm_num
  have hkTwo : 2 ≤ k := by omega
  let index : Fin (N + 3) := ⟨k, hkRank⟩
  have hagreement : target.order index = source.order index :=
    E.order_castLength_eq_source_of_two_le a D horders hlength index
      (by simp only [index]; omega)
  rcases Nat.mod_two_eq_zero_or_one k with hmod | hmod
  · have htarget := O.target_even index (by simp only [index]; omega)
      (by simpa only [index] using hmod)
    have hcomparison := O.comparison_even index
      (by simp only [index]; omega) (by simpa only [index] using hmod)
    have heq : source.order index = c.order index :=
      hagreement.symm.trans (htarget.trans hcomparison.symm)
    rw [show (⟨k, hkRank⟩ : Fin (N + 3)) = index by rfl, heq]
  · have htarget := O.target_odd index (by simp only [index]; omega)
      (by simpa only [index] using hmod)
    have hcomparison := O.comparison_odd index
      (by simp only [index]; omega) (by simpa only [index] using hmod)
    have heq : source.order index = c.order index :=
      hagreement.symm.trans (htarget.trans hcomparison.symm)
    rw [show (⟨k, hkRank⟩ : Fin (N + 3)) = index by rfl, heq]

theorem sourceComparisonPrefixSum_modEq_two
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (j : Nat) (hjThree : 3 ≤ j) (hji : j ≤ i.val) :
    Int.ModEq 2
      ((a.castLength hlength).orderSequence.prefixSum j)
      (c.orderSequence.prefixSum j) := by
  apply prefixSum_modEq_of_entryOrZero_modEq
  intro k hk
  exact sourceComparisonOrder_modEq_two
    a c D E horders hlength i (by omega) O k (by omega)

theorem diagonalMixedProduct_order_even
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (j : Nat) (hjThree : 3 ≤ j) (hji : j ≤ i.val) :
    Even (ordUnit K
      ((1 : Kˣ) * (a.castLength hlength).prefixProduct j *
        c.prefixProduct j)) := by
  have hparity := sourceComparisonPrefixSum_modEq_two
    a c D E horders hlength i O j hjThree hji
  have heven := comparisonPrefixProduct_order_even_of_prefixSum_modEq
    (a.castLength hlength) c j (by have := i.lt_large; omega)
      (by have := i.lt_large; omega) hparity
  simpa only [one_mul] using heven

theorem baselineAdjacentSum_even_of_modEq
    {R₁ R₂ : Int} (horderParity : Int.ModEq 2 R₁ R₂) :
    Even (R₁ + R₂ + 2) := by
  have hdiffEven : Even (R₂ - R₁) := by
    rw [Int.modEq_iff_dvd] at horderParity
    rcases horderParity with ⟨t, ht⟩
    exact ⟨t, by omega⟩
  rcases hdiffEven with ⟨t, ht⟩
  refine ⟨R₁ + t + 1, ?_⟩
  omega

theorem sourceAdjacentOrderSum_eq_baseline
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (j : Nat) (hjThree : 3 ≤ j) (hji : j ≤ i.val) :
    (a.castLength hlength).order ⟨j - 1, by have := i.lt_large; omega⟩ +
        (a.castLength hlength).order ⟨j, by have := i.lt_large; omega⟩ =
      R₁ + R₂ + 2 := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  let boundary : Fin (N + 2) := ⟨j - 1, by have := i.lt_large; omega⟩
  let left : Fin (N + 3) := ⟨j - 1, by have := i.lt_large; omega⟩
  let right : Fin (N + 3) := ⟨j, by have := i.lt_large; omega⟩
  have hleftAgreement : target.order left = source.order left :=
    E.order_castLength_eq_source_of_two_le a D horders hlength left
      (by simp only [left]; omega)
  have hrightAgreement : target.order right = source.order right :=
    E.order_castLength_eq_source_of_two_le a D horders hlength right
      (by simp only [right]; omega)
  change source.order left + source.order right = R₁ + R₂ + 2
  rw [← hleftAgreement, ← hrightAgreement]
  have hpair := targetAdjacentSum_eq_of_alternatingOrders
    target c i O boundary (by simp only [boundary]; omega)
  have hboundaryLeft : boundary.castSucc = left := by
    apply Fin.ext
    rfl
  have hboundaryRight : boundary.succ = right := by
    apply Fin.ext
    simp only [boundary, right, Fin.val_succ]
    omega
  rwa [hboundaryLeft, hboundaryRight] at hpair

theorem shiftedMixedProduct_order_even
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (horderParity : Int.ModEq 2 R₁ R₂)
    (j : Nat) (hjThree : 3 ≤ j) (hji : j ≤ i.val) :
    Even (ordUnit K
      ((-1 : Kˣ) * (a.castLength hlength).prefixProduct (j + 1) *
        c.prefixProduct (j - 1))) := by
  let source := a.castLength hlength
  have hiThree : 3 ≤ i.val := hjThree.trans hji
  have hprefixParity : Int.ModEq 2
      (source.orderSequence.prefixSum (j - 1))
      (c.orderSequence.prefixSum (j - 1)) := by
    apply prefixSum_modEq_of_entryOrZero_modEq
    intro k hk
    exact sourceComparisonOrder_modEq_two
      a c D E horders hlength i hiThree O k (by omega)
  have hprefixEven : Even
      (source.orderSequence.prefixSum (j - 1) +
        c.orderSequence.prefixSum (j - 1)) := by
    rw [Int.modEq_iff_dvd] at hprefixParity
    rcases hprefixParity with ⟨z, hz⟩
    refine ⟨c.orderSequence.prefixSum (j - 1) - z, ?_⟩
    omega
  have hbaselineEven : Even (R₁ + R₂ + 2) :=
    baselineAdjacentSum_even_of_modEq horderParity
  have hsourcePair := sourceAdjacentOrderSum_eq_baseline
    a c D E horders hlength i O j hjThree hji
  have hentryPair :
      source.orderSequence.entryOrZero (j - 1) +
          source.orderSequence.entryOrZero j = R₁ + R₂ + 2 := by
    rw [source.orderSequence.entryOrZero_of_lt (by have := i.lt_large; omega),
      source.orderSequence.entryOrZero_of_lt (by have := i.lt_large; omega)]
    simpa only [orderSequence_at] using hsourcePair
  have hsourcePrefix := source.orderSequence.prefixSum_add_two (j - 1)
  have hsourcePrefix' :
      source.orderSequence.prefixSum (j + 1) =
        source.orderSequence.prefixSum (j - 1) +
          (source.orderSequence.entryOrZero (j - 1) +
            source.orderSequence.entryOrZero j) := by
    simpa only [show j - 1 + 2 = j + 1 by omega,
      show j - 1 + 1 = j by omega] using hsourcePrefix
  have htotalEven : Even
      (source.orderSequence.prefixSum (j + 1) +
        c.orderSequence.prefixSum (j - 1)) := by
    rw [hsourcePrefix', hentryPair]
    have hadd := hprefixEven.add hbaselineEven
    simpa only [add_assoc, add_left_comm, add_comm] using hadd
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have hneg : ordUnit K (-1 : Kˣ) = 0 := by
    rw [ordUnit_neg, hone]
  rw [ordUnit_mul, ordUnit_mul, hneg, zero_add,
    source.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (j + 1) (by have := i.lt_large; omega),
    c.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (j - 1) (by have := i.lt_large; omega)]
  exact htotalEven

theorem mixedDefectSum_strict
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [comparisonLaws : Beli2006AlphaLaws.{u, w} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (P : Beli2019Lemma912ComparisonFirstAlphaProfile c A₁)
    (S : Beli2019Lemma912SourceAlphaAlternation
      (a.castLength hlength) A₁ i)
    (C : Beli2019Lemma912ComparisonAlphaAlternation c A₁ i)
    (T : Beli2019Lemma912TopMixedDefectBounds
      (a.castLength hlength) c A₁ i)
    (horderParity : Int.ModEq 2 R₁ R₂)
    (j : Nat) (hjThree : 3 ≤ j) (hji : j ≤ i.val) :
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
      defectOrder (K := K)
          ((a.castLength hlength).prefixProduct j * c.prefixProduct j) +
        defectOrder (K := K)
          (-(a.castLength hlength).prefixProduct (j + 1) *
            c.prefixProduct (j - 1)) := by
  let source := a.castLength hlength
  let first := failureThreshold (K := K) A₁ (j - 1)
  let second := failureThreshold (K := K) A₁ (j - 2)
  have hdiagonalWeak := diagonalMixedDefect_ge_failureThreshold
    (sourceLaws := sourceLaws) (comparisonLaws := comparisonLaws)
    a c D E horders hlength i O S C T j hjThree hji
  have hshiftedWeak := shiftedMixedDefect_ge_failureThreshold
    (sourceLaws := sourceLaws) (comparisonLaws := comparisonLaws)
    a c D E horders hlength i O S C T j (by omega) hji
  have hdiagonalOrderEven := diagonalMixedProduct_order_even
    a c D E horders hlength i O j hjThree hji
  have hshiftedOrderEven := shiftedMixedProduct_order_even
    a c D E horders hlength i O horderParity j hjThree hji
  have hdiagonalStrictRaw := evenThreshold_lt_defectOrder_of_le
    (K := K)
    ((1 : Kˣ) * source.prefixProduct j * c.prefixProduct j) first
    (failureThreshold_even P (j - 1))
    (failureThreshold_lt_twoE P (j - 1))
    hdiagonalOrderEven (by simpa only [first] using hdiagonalWeak)
  have hshiftedStrictRaw := evenThreshold_lt_defectOrder_of_le
    (K := K)
    ((-1 : Kˣ) * source.prefixProduct (j + 1) * c.prefixProduct (j - 1)) second
    (failureThreshold_even P (j - 2))
    (failureThreshold_lt_twoE P (j - 2))
    hshiftedOrderEven (by simpa only [second] using hshiftedWeak)
  have hdiagonalStrict :
      (((first : Int) : ℚ) : WithTop ℚ) <
        defectOrder (K := K)
          (source.prefixProduct j * c.prefixProduct j) := by
    simpa only [one_mul] using hdiagonalStrictRaw
  have hshiftedStrict :
      (((second : Int) : ℚ) : WithTop ℚ) <
        defectOrder (K := K)
          (-source.prefixProduct (j + 1) * c.prefixProduct (j - 1)) := by
    simpa only [neg_one_mul] using hshiftedStrictRaw
  have hsumInt : first + second =
      2 * (ramificationIndex K : Int) := by
    have h := failureThreshold_add_next (K := K) A₁ (j - 2)
    dsimp only [first, second]
    rw [show j - 2 + 1 = j - 1 by omega] at h
    omega
  have hsumQ :
      (((2 * ramificationIndex K : Nat) : ℚ)) =
        ((first : Int) : ℚ) + ((second : Int) : ℚ) := by
    exact_mod_cast hsumInt.symm
  have hadd := WithTop.add_lt_add hdiagonalStrict hshiftedStrict
  rw [← WithTop.coe_add, ← hsumQ] at hadd
  exact hadd

end BONG.GoodBONG.Beli2019Lemma910Data

end Bong
