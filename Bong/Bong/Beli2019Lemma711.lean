/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009ClassificationPropagation
import Bong.Bong.Beli2019PrefixChange
import Bong.Bong.GoodMap

/-!
# Beli (2019), Lemma 7.11

Two ternary lattices in the same quadratic space, with identical good-BONG
orders and equal first and third orders, are isometric exactly when their
first alpha invariants agree.  The proof verifies all four conditions of
Beli's 2009 classification theorem.
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
  {L : Lattice K V} {M : Lattice K W}

/-- Cross-space form of Beli (2019), Lemma 7.11.  The paper writes both
lattices over the same quadratic space; an explicit ambient isometry is the
equivalent coordinate-free hypothesis needed by later normal-form models. -/
theorem beli2019Lemma711_of_ambient_isometry
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [GoodBONGClassificationLaws.{u, v, w} K]
    (ambient : q.IsIsometric r)
    (a : GoodBONG q L 3) (b : GoodBONG r M 3)
    (horders : a.SameOrders b)
    (houter : a.order 0 = a.order 2) :
    Lattice.IsIsometric q r L M ↔ a.alphaValue 0 = b.alphaValue 0 := by
  rcases ambient with ⟨F⟩
  constructor
  · intro hisometric
    have H := (isometric_iff_classificationConditions ⟨F⟩ a b).mp
      hisometric
    exact H.sameAlphas 0
  · intro halphaZero
    have houterB : b.order 0 = b.order 2 := by
      calc
        b.order 0 = a.order 0 := (horders 0).symm
        _ = a.order 2 := houter
        _ = b.order 2 := horders 2
    have hsumA : a.adjacentOrderSum 0 = a.adjacentOrderSum 1 := by
      unfold adjacentOrderSum
      change a.order 0 + a.order 1 = a.order 1 + a.order 2
      rw [houter]
      ring
    have hsumB : b.adjacentOrderSum 0 = b.adjacentOrderSum 1 := by
      unfold adjacentOrderSum
      change b.order 0 + b.order 1 = b.order 1 + b.order 2
      rw [houterB]
      ring
    let CA := by
      letI : Beli2006AlphaLaws.{u, v} K := alphaV
      exact a.beli2009Corollary23 (0 : Fin 2) (1 : Fin 2)
        (by decide) hsumA
    let CB := by
      letI : Beli2006AlphaLaws.{u, w} K := alphaW
      exact b.beli2009Corollary23 (0 : Fin 2) (1 : Fin 2)
        (by decide) hsumB
    have haEndpoints := CA.leftEndpoint_eq (1 : Fin 2) (by decide) le_rfl
    have hbEndpoints := CB.leftEndpoint_eq (1 : Fin 2) (by decide) le_rfl
    have halphaOne : a.alphaValue 1 = b.alphaValue 1 := by
      unfold alphaLeftEndpoint at haEndpoints hbEndpoints
      norm_num at haEndpoints hbEndpoints
      have horderZero : (a.order 0 : ℚ) = b.order 0 := by
        exact_mod_cast horders (0 : Fin 3)
      have horderOne : (a.order 1 : ℚ) = b.order 1 := by
        exact_mod_cast horders (1 : Fin 3)
      linarith [haEndpoints, hbEndpoints, horderZero, horderOne,
        halphaZero]
    have halphas : a.SameAlphas b := by
      intro i
      fin_cases i
      · exact halphaZero
      · exact halphaOne
    have hbaseZero : comparisonPrefixDefect a b 0 = ⊤ :=
      comparisonPrefixDefect_zero a b
    have hfullSquare : IsSquare (a.comparisonPrefixUnit b 3) := by
      unfold comparisonPrefixUnit
      rw [a.prefixProduct_eq_valueProduct_of_rank_le 3 le_rfl,
        b.prefixProduct_eq_valueProduct_of_rank_le 3 le_rfl]
      let b' := b.map F.symm
      have hsquare := isSquare_valueProduct_mul a b'
      simpa [b', BONG.valueProduct, BONG.prefixProduct,
        BONG.valueUnit, GoodBONG.map, BONG.value_map] using hsquare
    have hbaseFull : comparisonPrefixDefect a b 3 = ⊤ := by
      unfold comparisonPrefixDefect
      exact defectOrder_eq_top_of_isSquare hfullSquare
    have hlocalA := by
      letI : Beli2006AlphaLaws.{u, v} K := alphaV
      exact a.alpha_pair_le_adjacentDefects 0 (by omega) houter
    have hlocalB := by
      letI : Beli2006AlphaLaws.{u, w} K := alphaW
      exact b.alpha_pair_le_adjacentDefects 0 (by omega) houterB
    have hprefixTwo :
        (a.alphaValue 1 : WithTop ℚ) ≤ comparisonPrefixDefect a b 2 := by
      have hzero : (a.alphaValue 1 : WithTop ℚ) ≤
          comparisonPrefixDefect a b 0 := by
        rw [hbaseZero]
        exact le_top
      have htarget : (a.alphaValue 1 : WithTop ℚ) ≤
          b.adjacentDefect 0 := by
        rw [halphaOne]
        exact hlocalB.1
      exact (le_min hzero (le_min hlocalA.1 htarget)).trans
        (comparisonPrefixDefect_add_two a b 0 (by omega))
    have hprefixOne :
        (a.alphaValue 0 : WithTop ℚ) ≤ comparisonPrefixDefect a b 1 := by
      have hfull : (a.alphaValue 0 : WithTop ℚ) ≤
          comparisonPrefixDefect a b 3 := by
        rw [hbaseFull]
        exact le_top
      have htarget : (a.alphaValue 0 : WithTop ℚ) ≤
          b.adjacentDefect 1 := by
        rw [halphaZero]
        exact hlocalB.2
      exact (le_min hfull (le_min hlocalA.2 htarget)).trans
        (comparisonPrefixDefect_reverse_add_two a b 1 (by omega))
    have hprefix : a.PrefixDefectBounds b := by
      intro i
      change (a.alphaValue i : WithTop ℚ) ≤
        comparisonPrefixDefect a b (i.val + 1)
      fin_cases i
      · simpa using hprefixOne
      · simpa using hprefixTwo
    have halphaSum := by
      letI : Beli2006AlphaLaws.{u, v} K := alphaV
      exact a.beli2009Lemma34 (l := 0) (r := 0) houter
    have hinternal : a.InternalRepresentationConditions b := by
      intro i hi htrigger
      fin_cases i
      · norm_num at hi
      · have hstrict :
            2 * (ramificationIndex K : ℚ) <
              a.alphaValue 0 + a.alphaValue 1 := by
          simpa using htrigger
        exact (not_lt_of_ge halphaSum hstrict).elim
    apply (isometric_iff_classificationConditions ⟨F⟩ a b).mpr
    exact {
      sameOrders := horders
      sameAlphas := halphas
      prefixDefectBounds := hprefix
      internalRepresentations := hinternal }

/-- Beli (2019), Lemma 7.11 in the paper's same-space presentation. -/
theorem beli2019Lemma711
    [Beli2006AlphaLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    {M : Lattice K V}
    (a : GoodBONG q L 3) (b : GoodBONG q M 3)
    (horders : a.SameOrders b)
    (houter : a.order 0 = a.order 2) :
    Lattice.IsIsometric q q L M ↔ a.alphaValue 0 = b.alphaValue 0 :=
  a.beli2019Lemma711_of_ambient_isometry
    (QuadraticSpace.isIsometric_refl q) b horders houter

end BONG.GoodBONG

end Bong
