/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenSecondEndpointOrders
import Bong.Bong.He2023ADCEvenCorankTwoGenericTests

/-!
# Actual maximal tests for the exceptional second ambient columns

The complementary endpoint parameter must define a smaller second-column
test. Thus the square ambient column includes n=2, while the discriminant
ambient column is presently treated here only for n>=4.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Actual complementary endpoint tests and a derived kappa test force all second-column orders. -/
theorem heADCSecondEndpoint_orders (k : Nat) (a : GoodBONG q L (2 * k + 4))
    (c μ : Kˣ)
    (hc : c = 1 ∨ c = (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (hμ : μ = 1 ∨ μ = (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (hdefined : HeHuEvenSecondDefined k μ) (hnot : ¬ IsSquare (μ * c))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace
      (heADCW2Even (k + 1) c (Or.inl (by omega))))) :
    (∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int))) ∧
      a.order ⟨2 * k + 2, by omega⟩ = 1 ∧
        a.order ⟨2 * k + 3, by omega⟩ = 1 - 2 * (ramificationIndex K : Int) := by
  let w := heADCW2Even (k + 1) c (Or.inl (by omega))
  have hclass : IsSquare (diagonalUnitDeterminant w * ((-1 : Kˣ) ^ (k + 2) * c)) := by
    simpa only [Nat.add_assoc] using
      heADCEvenSecond_determinantClass (k + 1) c (Or.inl (by omega))
  have lift (source : Fin (2 * k + 2) → Kˣ) (d : Kˣ)
      (hsource : IsSquare (diagonalUnitDeterminant source * ((-1 : Kˣ) ^ (k + 1) * d)))
      (hd : ¬ IsSquare (d * c)) :
      Lattice.Represents q (BONG.coefficientDiagonalSpace source) L (heHuOMaximalLattice source) :=
    Lattice.heADCMaximal_represents_of_ambient_model hADC source w ambient
      (heADCEvenCodimensionTwo_represents_of_parameter_not_square k (by omega) source w d c
        hsource hclass hd)
  have hfirst := lift (heADCW1Even k μ) μ (heADCEvenFirst_determinantClass k μ) hnot
  have hsecond := lift (heADCW2Even k μ hdefined) μ
    (heADCEvenSecond_determinantClass k μ hdefined) hnot
  obtain ⟨_, hhead, _⟩ := a.heADC2025Lemma64i k μ hμ hADC.isIntegral hfirst
  have he := ramificationIndex_pos (K := K)
  obtain ⟨κ, hunit, hκ⟩ := exists_unit_quadraticDefect_eq_odd (K := K)
    (2 * ramificationIndex K - 1) (by omega) ⟨ramificationIndex K - 1, by omega⟩ (by omega)
  have hκnot : ¬ IsSquare (κ * c) := by
    rcases hc with hOne | hDelta
    · simpa only [hOne, mul_one] using (heADCKappaSharpDomain κ hκ).notSquare
    · simpa only [hDelta] using
        heADCSharp_mul_discriminant_not_square κ (heADCKappaSharpDomain κ hκ)
  have hκrep := lift (heADCW1Even k κ) κ (heADCEvenFirst_determinantClass k κ) hκnot
  have hbase :
      Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k (1 : Kˣ)))
        L (heADCN1Even k (1 : Kˣ)).lattice ∨
      Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k
        (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit))
        L (heADCN1Even k
          (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit).lattice := by
    rcases hμ with rfl | rfl
    · exact Or.inl hfirst
    · exact Or.inr hfirst
  obtain ⟨_, hnext⟩ := a.heADC2025Lemma64iv k κ hunit hκ hADC.isIntegral
    (hbase.imp_right Or.inl) (Or.inl hκrep)
  have hfull : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) (a.toBONG.signedEvenPrefixProduct (k + 2)) := by
    rw [a.heADC_signedFullDefectOrder_of_ambient w (by omega) (k + 2) (by omega) c
      ambient hclass]
    rcases hc with hOne | hDelta
    · rw [hOne, defectOrder_one]
      exact le_top
    · rw [hDelta]
      have H : ((2 * ramificationIndex K : Nat) : ℕ∞) ≤ quadraticDefect K
          (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit := by
        rw [(dyadicDiscriminantClassLawsProved (K := K)).discriminant_defect]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (natCast_le_defectOrder_iff _ (2 * ramificationIndex K)).mpr H
  have hAlpha : 2 - 2 * (ramificationIndex K : Int) ≤ a.order ⟨2 * k + 3, by omega⟩ →
      a.HeADCEvenCentralAlphaAlternatives k := by
    intro hR
    apply a.heADC2025Lemma67_endpoint k hADC.isIntegral hhead hR μ hdefined hμ _ hsecond
    by_cases hnEven : Even (a.order ⟨2 * k + 2, by omega⟩)
    · exact Or.inl hnEven
    · right
      have hnzero : a.order ⟨2 * k + 2, by omega⟩ ≠ 0 := by
        intro hz
        apply hnEven
        rw [hz]
        exact Even.zero
      have hpos : 0 < a.order ⟨2 * k + 2, by omega⟩ := by omega
      simpa only [BONG.signedEvenPrefixProduct,
        show 2 * (k + 1) = 2 * k + 2 by omega, GoodBONG.prefixProduct] using
          a.heADCEvenFirstTest_signedPrefixDefect k μ hμ hfirst (by omega) hpos
  exact ⟨hhead, a.heADCSecondEndpoint_terminal_pair k hADC.isIntegral c hc
    (Or.inl (by omega)) ambient hhead hnext hfull hAlpha⟩

/-- Reassemble the alternating head and final raised pair into the published full profile. -/
theorem heADCSecondEndpoint_full_profile (k : Nat) (a : GoodBONG q L (2 * k + 4))
    (hhead : ∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hnext : a.order ⟨2 * k + 2, by omega⟩ = 1)
    (hlast : a.order ⟨2 * k + 3, by omega⟩ = 1 - 2 * (ramificationIndex K : Int)) :
    ∀ i, a.order i = heADCMaximalOrderProfile (K := K) (k + 1)
      ![1, 1 - 2 * (ramificationIndex K : Int)] ⟨i.val, by omega⟩ := by
  intro i
  by_cases hi : i.val < 2 * k + 2
  · simp only [heADCMaximalOrderProfile, dif_pos (show i.val < 2 * (k + 1) by omega)]
    exact hhead ⟨i.val, hi⟩
  · have hcases : i.val = 2 * k + 2 ∨ i.val = 2 * k + 3 := by omega
    rcases hcases with hprevious | hterminal
    · have hiEq : i = ⟨2 * k + 2, by omega⟩ := Fin.ext hprevious
      rw [hiEq]
      simpa [heADCMaximalOrderProfile, show 2 * (k + 1) = 2 * k + 2 by omega] using hnext
    · have hiEq : i = ⟨2 * k + 3, by omega⟩ := Fin.ext hterminal
      rw [hiEq]
      simpa [heADCMaximalOrderProfile, show 2 * (k + 1) = 2 * k + 2 by omega,
        show ¬ 2 * k + 3 < 2 * k + 2 by omega,
        show 2 * k + 3 - (2 * k + 2) = 1 by omega] using hlast

end BONG.GoodBONG

end Bong
