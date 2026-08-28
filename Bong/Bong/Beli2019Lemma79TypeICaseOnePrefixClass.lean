/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeICaseOneProfile
import Bong.Bong.Beli2019Lemma75PrefixClass

/-!
# Beli (2019), Lemma 7.9(ii), case 1: prefix square classes

Lemma 7.5 gives the two endpoint alternatives for both exceptional prefixes.
Their product is therefore either a square or a discriminant-twisted square.
The remaining representation argument in case 1 only has to exclude the
second alternative.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The two prefixes in case 1 have equal or opposite endpoint type.  At the
determinant level these are precisely the square and discriminant-twisted
square alternatives. -/
theorem beli2019Lemma79_typeI_caseOne_prefixProduct_cases
    [Beli2006AlphaLaws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch)
    (hgap : b.orderGap ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = 2 * (ramificationIndex K : Int) + 1)
    (hprevious : c.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = b.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩) :
    IsSquare (b.prefixProduct i.val * c.prefixProduct i.val) ∨
      IsSquare (b.prefixProduct i.val * c.prefixProduct i.val *
        laws.discriminantUnit) := by
  have hiEven : Even i.val := by
    simpa only [hleft] using C.left_even
  have hiTwo : 2 ≤ i.val := by
    have hiPos := i.pos
    rcases hiEven with ⟨d, hd⟩
    omega
  let lastPair : Fin (n + 1) := ⟨i.val - 2, by
    have hiBound := i.lt_large
    omega⟩
  have hlastEven : Even lastPair.val := by
    simp only [lastPair]
    rcases hiEven with ⟨d, hd⟩
    refine ⟨d - 1, ?_⟩
    omega
  have hlastSucc : lastPair.succ =
      (⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [lastPair, Fin.val_succ]
    omega
  rcases beli2019Lemma79_typeI_caseOne_endpointOrders
      a b c D C hnorm i hleft hgap hprevious with
    ⟨hfirstOrders, hbLast, hcLast⟩
  have hbTerminal : b.order lastPair.succ =
      b.order 0 - 2 * (ramificationIndex K : Int) := by
    rw [hlastSucc]
    exact hbLast
  have hcTerminal : c.order lastPair.succ =
      b.order 0 - 2 * (ramificationIndex K : Int) := by
    rw [hlastSucc, hcLast, ← hfirstOrders]
  rcases b.beli2019Lemma75_signedPrefixProduct_endpoint_cases
      lastPair (b.order 0) hlastEven rfl hbTerminal with
    ⟨bPairs, hbLength, hbCases⟩
  rcases c.beli2019Lemma75_signedPrefixProduct_endpoint_cases
      lastPair (b.order 0) hlastEven hfirstOrders.symm hcTerminal with
    ⟨cPairs, hcLength, hcCases⟩
  have hpairs : cPairs = bPairs := by omega
  subst cPairs
  have hlength : 2 * bPairs = i.val := by
    simp only [lastPair] at hbLength
    omega
  have hcases := b.toBONG.signedEvenPrefixProduct_comparison_cases
    c.toBONG bPairs hbCases hcCases
  simpa only [hlength, GoodBONG.prefixProduct] using hcases

end BONG.GoodBONG

end Bong
