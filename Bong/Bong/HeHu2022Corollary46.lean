/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.SplitQuaternaryPrefixDeterminant
import Bong.Bong.HeHu2022Theorem41
import Bong.Bong.BeliUniversalHalfTower
import Bong.Bong.BeliUniversalTheorem31
import Bong.Bong.Beli2009AmbientDeterminantProof
import Bong.Lattice.OMaximalUniqueness

/-!
# He--Hu 2022, Corollary 4.6

This file proves the exceptional quaternary case in the exact three forms
printed in Corollary 4.6: binary universality, the split-space/order
criterion, and integral isometry to `2^-1 A(0,0) ⊥ 2^-1 A(0,0)`.
-/

namespace Bong

open Dyadic Module

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Condition (ii) of He--Hu, Corollary 4.6, in zero-based BONG indices. -/
structure HeHuCorollary46Invariants (a : GoodBONG q L 4) : Prop where
  splitSpace :
    q.IsIsometric
      ((QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ)).orthogonalSum
        (QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ)))
  order0 : a.order 0 = 0
  order2 : a.order 2 = 0
  order1 : a.order 1 = -(2 * (ramificationIndex K : Int))
  order3 : a.order 3 = -(2 * (ramificationIndex K : Int))

/-- Condition (iii) of He--Hu, Corollary 4.6.  The target is the literal
standard lattice `2^-1 A(0,0) ⊥ 2^-1 A(0,0)` used throughout the Beli
universal-form formalization. -/
noncomputable def HeHuCorollary46StandardModel
    (q : QuadraticSpace K V) (L : Lattice K V) : Prop := by
  let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) 2
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  exact Lattice.IsIsometric q T.form L T.lattice

/-- The first equivalence in He--Hu, Corollary 4.6. -/
theorem heHu2022Corollary46_universal_iff_invariants
    (a : GoodBONG q L 4) (hIntegral : Lattice.IsIntegral q L) :
    Lattice.IsNUniversal.{u, v, u} q L 2 ↔
      a.HeHuCorollary46Invariants := by
  letI : Module.Finite K V := L.moduleFinite
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  constructor
  · intro hUniversal
    have h41 :=
      (a.heHu2022Theorem41Even (m := 1) (k := 0) (by omega) hIntegral).mp
        hUniversal
    have hrank : finrank K V = 4 := a.toBONG.length_eq_finrank.symm
    have hsplit :
        q.IsIsometric
          ((QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ)).orthogonalSum
            (QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ))) := by
      rcases
          (Lattice.ambientlyEvenUniversal_rank_classification
            (q := q) 0).mp h41.2.1 with hstable | hexceptional
      · omega
      · exact hexceptional.2.2
    have hI1 := h41.2.2.i1
    have horder0 : a.order 0 = 0 := by
      exact hI1.oddOrder 0 ⟨0, by norm_num⟩
    have horder1 : a.order 1 = -(2 * (ramificationIndex K : Int)) := by
      exact hI1.evenOrder 1 ⟨1, by norm_num⟩
    have horder2 : a.order 2 = 0 := by
      exact hI1.oddOrder 2 ⟨1, by norm_num⟩
    have halpha2 : a.alphaValue (2 : Fin 3) = 0 := by
      have hI2 := h41.2.2.i2
      unfold HeHuI2E at hI2
      dsimp only at hI2
      rcases hI2 with hzero | ⟨hone, hcapped⟩
      · exact hzero
      · exfalso
        let boundary : Fin 3 := 2
        have hgapFormula : a.orderGap boundary = a.order 3 := by
          unfold orderGap
          rw [show boundary.succ = (3 : Fin 4) by ext; rfl]
          rw [show boundary.castSucc = (2 : Fin 4) by ext; rfl]
          rw [horder2, sub_zero]
        have hgapNe : a.orderGap boundary ≠
            -(2 * (ramificationIndex K : Int)) := by
          intro hgap
          have hz := (a.heHu2022Proposition26 boundary).alphaZero.mpr hgap
          have honeBoundary : a.alphaValue boundary = 1 := by
            simpa [boundary] using hone
          rw [honeBoundary] at hz
          norm_num at hz
        have hgapLower := a.orderGap_ge_neg_two_mul_e_for_properties boundary
        have hlastStrict : -(2 * (ramificationIndex K : Int)) < a.order 3 := by
          rw [← hgapFormula]
          omega
        let idx : LongRepresentationIndex 4 2 :=
          { val := 2
            one_lt := by omega
            succ_lt_large := by omega
            le_small_succ := by omega }
        have hlocal :
            a.truncatedPrefixDefect a (-1) idx.val (idx.val + 2) =
              (((1 - a.order ⟨idx.val + 1, idx.succ_lt_large⟩ : Int) : ℚ) :
                WithTop ℚ) := by
          simpa [heHuAdjacentCappedDefect, idx] using hcapped
        have hprevious :
            a.order ⟨idx.val - 1, by norm_num [idx]⟩ =
              -(2 * (ramificationIndex K : Int)) := by
          simpa [idx] using horder1
        have hcurrent : a.order ⟨idx.val, by norm_num [idx]⟩ = 0 := by
          simpa [idx] using horder2
        have hnext :
            -(2 * (ramificationIndex K : Int)) <
              a.order ⟨idx.val + 1, idx.succ_lt_large⟩ := by
          simpa [idx] using hlastStrict
        have hfull :=
          (a.heHu2022Lemma210ii hIntegral idx (by norm_num)
            hprevious hcurrent hnext).mp hlocal
        have hprefixSquare := a.splitQuaternary_fullPrefix_isSquare hsplit
        have hprefixSquareRaw :
            IsSquare (a.toBONG.prefixProduct 4) := by
          simpa only [GoodBONG.prefixProduct] using hprefixSquare
        have hfullTop :
            a.truncatedPrefixDefect a ((-1 : Kˣ) ^ 2) 0 4 = ⊤ := by
          unfold truncatedPrefixDefect
          rw [a.prefixAlphaCap_zero]
          have hcap : a.prefixAlphaCap 4 = ⊤ := by
            simpa using a.prefixAlphaCap_last
          rw [hcap]
          simp only [min_top_right, GoodBONG.prefixProduct,
            BONG.prefixProduct_zero]
          rw [show (-1 : Kˣ) ^ 2 = 1 by norm_num]
          simpa only [one_mul] using
            (defectOrder_eq_top_of_isSquare hprefixSquareRaw)
        rw [show (idx.val + 2) / 2 = 2 by norm_num [idx]] at hfull
        rw [hfullTop] at hfull
        exact WithTop.top_ne_coe hfull
    have horder3 : a.order 3 = -(2 * (ramificationIndex K : Int)) :=
      a.boundaryOrder_eq_neg_two_e_of_i1E_alpha_zero
        (n := 2) (by omega) (by norm_num) hI1 halpha2
    exact ⟨hsplit, horder0, horder2, horder1, horder3⟩
  · intro h
    have hAmbient : Lattice.AmbientlyNUniversal.{u, v, u} q 2 := by
      intro W _ _ r M hrank hM
      rcases h.splitSpace with ⟨split⟩
      have hqRepPair : q.Represents
          ((QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ)).orthogonalSum
            (QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ))) :=
        ⟨split.symm.toRepresentation⟩
      exact hqRepPair.trans
        (Lattice.ambientlyTwoUniversal_hyperbolicPair r M hrank hM)
    have hI1 : a.HeHuI1E 2 (by omega) := by
      constructor
      · intro i hi
        fin_cases i
        · exact h.order0
        · norm_num at hi
        · exact h.order2
      · intro i hi
        fin_cases i
        · norm_num at hi
        · exact h.order1
    have halpha2 : a.alphaValue (2 : Fin 3) = 0 := by
      apply (a.heHu2022Proposition26 (2 : Fin 3)).alphaZero.mpr
      unfold orderGap
      rw [show (2 : Fin 3).succ = (3 : Fin 4) by ext; rfl]
      rw [show (2 : Fin 3).castSucc = (2 : Fin 4) by ext; rfl]
      rw [h.order3, h.order2]
      omega
    have hSection : a.HeHuEvenSectionConditions 2 (by omega) :=
      { i1 := hI1
        i2 := by
          unfold HeHuI2E
          dsimp only
          exact Or.inl halpha2
        i3 := by
          unfold HeHuI3E
          intro hmStable
          omega }
    exact
      (a.heHu2022Theorem41Even (m := 1) (k := 0) (by omega) hIntegral).mpr
        ⟨hIntegral, hAmbient, hSection⟩

/-- The second equivalence in He--Hu, Corollary 4.6: the four displayed
orders on the split quaternary space characterize the standard double
half-hyperbolic lattice. -/
theorem heHu2022Corollary46_invariants_iff_standardModel
    (a : GoodBONG q L 4) (hIntegral : Lattice.IsIntegral q L) :
    a.HeHuCorollary46Invariants ↔
      HeHuCorollary46StandardModel q L := by
  let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) 2
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  let b := standardHalfHyperbolicTowerBONG (K := K) 2
  constructor
  · intro h
    have hpattern : HasHalfModularOrderPattern (k := 2) a := by
      intro j
      by_cases hj : j = (0 : Fin 2)
      · subst j
        have hzero :
            halfModularPairIndexEquiv 2
                ((0 : Fin 2), (0 : Fin 2)) = (0 : Fin 4) := by
          apply Fin.ext
          simpa using halfModularPairIndexEquiv_zero_val 2 (0 : Fin 2)
        have hone :
            halfModularPairIndexEquiv 2
                ((0 : Fin 2), (1 : Fin 2)) = (1 : Fin 4) := by
          apply Fin.ext
          simpa using halfModularPairIndexEquiv_one_val 2 (0 : Fin 2)
        rw [hzero, hone]
        exact ⟨h.order0, by simpa [neg_mul] using h.order1⟩
      · have hj1 : j = (1 : Fin 2) := by
          apply Fin.ext
          omega
        subst j
        have htwo :
            halfModularPairIndexEquiv 2
                ((1 : Fin 2), (0 : Fin 2)) = (2 : Fin 4) := by
          apply Fin.ext
          simpa using halfModularPairIndexEquiv_zero_val 2 (1 : Fin 2)
        have hthree :
            halfModularPairIndexEquiv 2
                ((1 : Fin 2), (1 : Fin 2)) = (3 : Fin 4) := by
          apply Fin.ext
          simpa using halfModularPairIndexEquiv_one_val 2 (1 : Fin 2)
        rw [htwo, hthree]
        exact ⟨h.order2, by simpa [neg_mul] using h.order3⟩
    have hhalf : Lattice.IsHalfModularWithUnitNorm q L :=
      a.isHalfModularWithUnitNorm_of_orderPattern (k := 2) (by omega)
        hpattern
    have hLmax : Lattice.IsOMaximal q L :=
      Lattice.isOMaximal_of_isModular_of_integral_of_order_eq_neg_ramification
        hhalf.1 hIntegral ordUnit_dyadicHalfUnit
    have hTintegral : Lattice.IsIntegral T.form T.lattice :=
      Lattice.QuadraticLatticeModel.halfHyperbolicTower_isIntegral
        (K := K) 2
    have hThalf : Lattice.IsHalfModularWithUnitNorm T.form T.lattice :=
      Lattice.halfHyperbolicTower_isHalfModularWithUnitNorm
        (K := K) (k := 2) (by omega)
    have hTmax : Lattice.IsOMaximal T.form T.lattice :=
      Lattice.isOMaximal_of_isModular_of_integral_of_order_eq_neg_ramification
        hThalf.1 hTintegral ordUnit_dyadicHalfUnit
    have hambient : q.IsIsometric T.form := by
      rcases h.splitSpace with ⟨f⟩
      exact ⟨f.trans
        (QuadraticSpace.halfHyperbolicTowerTwoToHyperbolicPairIsometry
          (K := K)).symm⟩
    exact Lattice.oMaximal_isIsometric_of_isometric hLmax hTmax hambient
  · intro hModel
    change Lattice.IsIsometric q T.form L T.lattice at hModel
    rcases hModel with ⟨f⟩
    have horders : a.SameOrders b :=
      a.sameOrders_of_latticeIsometry b f
    have hbPattern : b.HasHalfModularOrderPattern :=
      standardHalfHyperbolicTowerBONG_orderPattern (K := K)
        (k := 2) (by omega)
    have hpair0 := hbPattern (0 : Fin 2)
    have hpair1 := hbPattern (1 : Fin 2)
    have hzero :
        halfModularPairIndexEquiv 2
            ((0 : Fin 2), (0 : Fin 2)) = (0 : Fin 4) := by
      apply Fin.ext
      simpa using halfModularPairIndexEquiv_zero_val 2 (0 : Fin 2)
    have hone :
        halfModularPairIndexEquiv 2
            ((0 : Fin 2), (1 : Fin 2)) = (1 : Fin 4) := by
      apply Fin.ext
      simpa using halfModularPairIndexEquiv_one_val 2 (0 : Fin 2)
    have htwo :
        halfModularPairIndexEquiv 2
            ((1 : Fin 2), (0 : Fin 2)) = (2 : Fin 4) := by
      apply Fin.ext
      simpa using halfModularPairIndexEquiv_zero_val 2 (1 : Fin 2)
    have hthree :
        halfModularPairIndexEquiv 2
            ((1 : Fin 2), (1 : Fin 2)) = (3 : Fin 4) := by
      apply Fin.ext
      simpa using halfModularPairIndexEquiv_one_val 2 (1 : Fin 2)
    have hb0 : b.order (0 : Fin 4) = 0 := by
      simpa only [hzero] using hpair0.1
    have hb1 : b.order (1 : Fin 4) =
        -(2 * (ramificationIndex K : Int)) := by
      simpa [hone, neg_mul] using hpair0.2
    have hb2 : b.order (2 : Fin 4) = 0 := by
      simpa only [htwo] using hpair1.1
    have hb3 : b.order (3 : Fin 4) =
        -(2 * (ramificationIndex K : Int)) := by
      simpa [hthree, neg_mul] using hpair1.2
    exact
      { splitSpace := ⟨f.toQuadraticSpaceIsometry.trans
          (QuadraticSpace.halfHyperbolicTowerTwoToHyperbolicPairIsometry
            (K := K))⟩
        order0 := (horders 0).trans hb0
        order2 := (horders 2).trans hb2
        order1 := (horders 1).trans hb1
        order3 := (horders 3).trans hb3 }

/-- He--Hu, Corollary 4.6, as the exact three-way equivalence printed in
the paper. -/
theorem heHu2022Corollary46
    (a : GoodBONG q L 4) (hIntegral : Lattice.IsIntegral q L) :
    (Lattice.IsNUniversal.{u, v, u} q L 2 ↔
      a.HeHuCorollary46Invariants) ∧
    (a.HeHuCorollary46Invariants ↔
      HeHuCorollary46StandardModel q L) :=
  ⟨a.heHu2022Corollary46_universal_iff_invariants hIntegral,
    a.heHu2022Corollary46_invariants_iff_standardModel hIntegral⟩

end BONG.GoodBONG

end Bong
