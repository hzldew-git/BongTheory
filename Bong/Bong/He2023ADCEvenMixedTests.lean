/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenFirstDefects
import Bong.Bong.He2023ADCEvenSecondTests
import Bong.Bong.He2023ADCGenericProfiles

/-!
# The mixed testing bound in He (2025), Lemma 6.4(iv)

The five tests are the actual maximal lattices of Definition 4.1.
Their last orders and determinant classes, including the kappa rows,
are derived from the already proved published profiles.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A finite defect of depth `2e-1` puts kappa in the sharp domain. -/
theorem heADCKappaSharpDomain (κ : Kˣ)
    (hκ : quadraticDefect K κ = ((2 * ramificationIndex K - 1 : Nat) : ℕ∞)) :
    HeHuSharpDomain κ := by
  have hd := Beli2009FinalRemarksProof.defectOrder_eq_natCast_of_quadraticDefect_eq
    (K := K) κ (2 * ramificationIndex K - 1) hκ
  apply heHuLemma45_sharpDomain_of_defect_lt_twoE κ
    ((2 * ramificationIndex K - 1 : Nat) : Int)
  · simpa only [Int.cast_natCast] using hd
  · have he := ramificationIndex_pos (K := K); omega

/-- Both actual kappa test lattices have last order `2-2e`. -/
theorem heADCKappaTest_lastOrders (k : Nat) (κ : Kˣ)
    (hunit : IsValuationUnit K (κ : K))
    (hκ : quadraticDefect K κ = ((2 * ramificationIndex K - 1 : Nat) : ℕ∞)) :
    (heADCMaximalGoodBONG (heADCW1Even k κ)).order ⟨2 * k + 1, by omega⟩ =
        2 - 2 * (ramificationIndex K : Int) ∧
      (heADCMaximalGoodBONG (heADCW2Even k κ
        (Or.inr (heADCKappaSharpDomain κ hκ).notSquare))).order ⟨2 * k + 1, by omega⟩ =
        2 - 2 * (ramificationIndex K : Int) := by
  let hs := heADCKappaSharpDomain κ hκ
  let bOne := (heADCMaximalGoodBONG (heADCW1Even k κ)).castLength
    (by omega : 2 * k + 2 = 2 + 2 * k)
  let bTwo := (heADCMaximalGoodBONG (heADCW2Even k κ (Or.inr hs.notSquare))).castLength
    (by omega : 2 * k + 2 = 2 + 2 * k)
  have hOne := (heADC2025Lemma411iiiUnitFirstPublished κ hunit hs k bOne
    (heHuOMaximalLattice_isOMaximal _).isIntegral
    (QuadraticSpace.isIsometric_refl _)).mp (Lattice.isIsometric_refl _ _)
  have hTwo := (heADC2025Lemma411iiiUnitSecondPublished κ hunit hs k bTwo
    (heHuOMaximalLattice_isOMaximal _).isIntegral
    (QuadraticSpace.isIsometric_refl _)).mp (Lattice.isIsometric_refl _ _)
  have hprofile : heADCMaximalOrderProfile (K := K) k
      ![0, 1 - ((quadraticDefect K κ).toNat : Int)] ⟨2 * k + 1, by omega⟩ =
        2 - 2 * (ramificationIndex K : Int) := by
    rw [heADCMaximalOrderProfile, dif_neg (show ¬ 2 * k + 1 < 2 * k by omega)]
    simp only [show 2 * k + 1 - 2 * k = 1 by omega]
    change 1 - ((quadraticDefect K κ).toNat : Int) =
      2 - 2 * (ramificationIndex K : Int)
    rw [hκ]
    change 1 - ((2 * ramificationIndex K - 1 : Nat) : Int) =
      2 - 2 * (ramificationIndex K : Int)
    have he := ramificationIndex_pos (K := K)
    omega
  constructor
  · simpa only [bOne, order_castLength] using
      (hOne ⟨2 * k + 1, by omega⟩).trans hprofile
  · simpa only [bTwo, order_castLength] using
      (hTwo ⟨2 * k + 1, by omega⟩).trans hprofile

/-- Ordinary determinants of first-column spaces carry the signed parameter. -/
theorem heADCEvenFirst_determinantClass (k : Nat) (c : Kˣ) :
    IsSquare (diagonalUnitDeterminant (heADCW1Even k c) * ((-1 : Kˣ) ^ (k + 1) * c)) := by
  rw [diagonalUnitDeterminant_heHuEvenFirst]
  exact ⟨_, rfl⟩

/-- Second-column spaces have the same determinant class as their first column. -/
theorem heADCEvenSecond_determinantClass (k : Nat) (c : Kˣ)
    (hdefined : HeHuEvenSecondDefined k c) :
    IsSquare (diagonalUnitDeterminant (heADCW2Even k c hdefined) *
      ((-1 : Kˣ) ^ (k + 1) * c)) := by
  have h := (heHu2022Definition34Proposition35Even k c hdefined).determinantSquare
  simpa only [diagonalUnitDeterminant_heHuEvenFirst] using h

/-- Different parameter defects force different determinant classes for
any two displayed even-dimensional rows carrying those parameters. -/
theorem heADCEvenTests_determinants_not_square (k : Nat) (c d : Kˣ)
    (w w' : Fin (2 * k + 2) → Kˣ)
    (hc : IsSquare (diagonalUnitDeterminant w * ((-1 : Kˣ) ^ (k + 1) * c)))
    (hd : IsSquare (diagonalUnitDeterminant w' * ((-1 : Kˣ) ^ (k + 1) * d)))
    (hne : quadraticDefect K c ≠ quadraticDefect K d) :
    ¬ IsSquare (diagonalUnitDeterminant w * diagonalUnitDeterminant w') := by
  intro h
  let s : Kˣ := (-1 : Kˣ) ^ (k + 1)
  have hcd : IsSquare ((s * c) * (s * d)) :=
    isSquare_mul_trans _ (diagonalUnitDeterminant w) _
      (by simpa only [mul_comm] using hc)
      (isSquare_mul_trans _ (diagonalUnitDeterminant w') _ h hd)
  have hs : IsSquare (s ^ 2) := ⟨s, pow_two s⟩
  have hquot := hcd.div hs
  have hcancel : ((s * c) * (s * d)) / s ^ 2 = c * d := by
    simp [pow_two, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  rw [hcancel] at hquot
  exact hne (heADCQuadraticDefect_eq_of_squareProduct c d hquot)

namespace BONG.GoodBONG

variable {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Two actual maximal tests of distinct determinant classes and with
last orders at most `2-2e` force a next order in `{0,1,2}`. The strict
rank inequality is derived from their representations. -/
theorem heADCEvenMixedTest_bound {m : Nat} (a : GoodBONG q L (m + 2)) (k : Nat)
    (w w' : Fin (2 * k + 2) → Kˣ) (hL : Lattice.IsIntegral q L)
    (hrep : Lattice.Represents q (BONG.coefficientDiagonalSpace w) L (heHuOMaximalLattice w))
    (hrep' : Lattice.Represents q (BONG.coefficientDiagonalSpace w') L (heHuOMaximalLattice w'))
    (hclasses : ¬ IsSquare (diagonalUnitDeterminant w * diagonalUnitDeterminant w'))
    (hlast : (heADCMaximalGoodBONG w).order ⟨2 * k + 1, by omega⟩ ≤
      2 - 2 * (ramificationIndex K : Int))
    (hlast' : (heADCMaximalGoodBONG w').order ⟨2 * k + 1, by omega⟩ ≤
      2 - 2 * (ramificationIndex K : Int)) :
    ∃ hrank : 2 * k < m,
      a.order ⟨2 * k + 2, by omega⟩ = 0 ∨ a.order ⟨2 * k + 2, by omega⟩ = 1 ∨
        a.order ⟨2 * k + 2, by omega⟩ = 2 := by
  letI : Module.Finite K V := L.moduleFinite
  have hrank : 2 * k < m := by
    obtain ⟨f⟩ := hrep
    obtain ⟨f'⟩ := hrep'
    have hle := f.toLinearMap.finrank_le_finrank_of_injective f.injective
    have haRank := a.toBONG.length_eq_finrank
    rw [finrank_fin_fun, ← haRank] at hle
    by_contra hnot
    have hsame : finrank K (Fin (2 * k + 2) → K) = finrank K V := by
      rw [finrank_fin_fun, ← haRank]; omega
    let g := (f.toQuadraticSpaceIsometryOfFinrankEq hsame).trans
      (f'.toQuadraticSpaceIsometryOfFinrankEq hsame).symm
    have H := (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents w w').mp
      ⟨g.toRepresentation⟩
    exact hclasses (DiagonalIsometryInvariantLaws.determinant_square w w' H)
  have heven : Even (2 * k + 2) := ⟨k + 1, by omega⟩
  have hnonneg := ((a.heHu2022Proposition27i hL).oddIndexed
    ⟨2 * k + 2, by omega⟩ ⟨2 * k + 2, by omega⟩ le_rfl heven heven).1
  refine ⟨hrank, ?_⟩
  suffices a.order ⟨2 * k + 2, by omega⟩ ≤ 2 by omega
  by_contra hnot
  let b := heADCMaximalGoodBONG w
  let b' := heADCMaximalGoodBONG w'
  have h := a.heADCComparisonPrefix_isSquare_of_strict_crossGap b hrank hrep
    (by dsimp only [b]; omega)
  have h' := a.heADCComparisonPrefix_isSquare_of_strict_crossGap b' hrank hrep'
    (by dsimp only [b']; omega)
  have hprefix := targetPrefixProduct_isSquare_of_common_source _ _ _ h h'
  have hb := heADCMaximalGoodBONG_prefixProduct_det_square w
  have hb' := heADCMaximalGoodBONG_prefixProduct_det_square w'
  exact hclasses (isSquare_mul_trans _ (b.prefixProduct (2 * k + 2)) _
    (by simpa only [mul_comm] using hb)
    (isSquare_mul_trans _ (b'.prefixProduct (2 * k + 2)) _ hprefix hb'))

/-- He (2025), Lemma 6.4(iv). All five named tests are retained, and
their required profile and class data are proved internally. -/
theorem heADC2025Lemma64iv {m : Nat} (a : GoodBONG q L (m + 2)) (k : Nat)
    (κ : Kˣ) (hunit : IsValuationUnit K (κ : K))
    (hκ : quadraticDefect K κ = ((2 * ramificationIndex K - 1 : Nat) : ℕ∞))
    (hL : Lattice.IsIntegral q L)
    (hbase :
      Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k (1 : Kˣ)))
        L (heADCN1Even k (1 : Kˣ)).lattice ∨
      Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit))
        L (heADCN1Even k
          (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit).lattice ∨
      Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW2Even k
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) k)))
        L (heADCN2Even k (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
          (heHuLemma43_evenSecondDefined (K := K) k)).lattice)
    (hsharp :
      Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k κ))
        L (heADCN1Even k κ).lattice ∨
      Lattice.Represents q (BONG.coefficientDiagonalSpace
        (heADCW2Even k κ (Or.inr (heADCKappaSharpDomain κ hκ).notSquare)))
        L (heADCN2Even k κ (Or.inr (heADCKappaSharpDomain κ hκ).notSquare)).lattice) :
    ∃ hrank : 2 * k < m,
      a.order ⟨2 * k + 2, by omega⟩ = 0 ∨ a.order ⟨2 * k + 2, by omega⟩ = 1 ∨
        a.order ⟨2 * k + 2, by omega⟩ = 2 := by
  let δ := (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
  have Hbase : ∃ c : Kˣ, ∃ w : Fin (2 * k + 2) → Kˣ,
      (c = 1 ∨ c = δ) ∧
      Lattice.Represents q (BONG.coefficientDiagonalSpace w) L (heHuOMaximalLattice w) ∧
      IsSquare (diagonalUnitDeterminant w * ((-1 : Kˣ) ^ (k + 1) * c)) ∧
      (heADCMaximalGoodBONG w).order ⟨2 * k + 1, by omega⟩ ≤
        2 - 2 * (ramificationIndex K : Int) := by
    rcases hbase with hOne | hDelta | hSecond
    · refine ⟨1, heADCW1Even k 1, Or.inl rfl, hOne,
        heADCEvenFirst_determinantClass k 1, ?_⟩
      have h := heADCEvenFirstTest_orders (K := K) k 1 (Or.inl rfl) ⟨2 * k + 1, by omega⟩
      simp only [if_neg (Nat.not_even_iff_odd.mpr hodd)] at h
      omega
    · refine ⟨δ, heADCW1Even k δ, Or.inr rfl, hDelta,
        heADCEvenFirst_determinantClass k δ, ?_⟩
      have h := heADCEvenFirstTest_orders (K := K) k δ (Or.inr rfl) ⟨2 * k + 1, by omega⟩
      simp only [if_neg (Nat.not_even_iff_odd.mpr hodd)] at h
      omega
    · refine ⟨δ, heADCW2Even k δ (heHuLemma43_evenSecondDefined (K := K) k), Or.inr rfl,
        hSecond, heADCEvenSecond_determinantClass k δ _, ?_⟩
      have h := heADCEvenSecondTest_orders (K := K) k δ
        (heHuLemma43_evenSecondDefined (K := K) k) (Or.inr rfl) ⟨2 * k + 1, by omega⟩
      simp [heADCMaximalOrderProfile, show ¬ 2 * k + 1 < 2 * k by omega,
        show 2 * k + 1 - 2 * k = 1 by omega] at h
      omega
  have Hsharp : ∃ w : Fin (2 * k + 2) → Kˣ,
      Lattice.Represents q (BONG.coefficientDiagonalSpace w) L (heHuOMaximalLattice w) ∧
      IsSquare (diagonalUnitDeterminant w * ((-1 : Kˣ) ^ (k + 1) * κ)) ∧
      (heADCMaximalGoodBONG w).order ⟨2 * k + 1, by omega⟩ ≤
        2 - 2 * (ramificationIndex K : Int) := by
    have H := heADCKappaTest_lastOrders k κ hunit hκ
    rcases hsharp with hOne | hTwo
    · exact ⟨heADCW1Even k κ, hOne, heADCEvenFirst_determinantClass k κ, H.1.le⟩
    · exact ⟨heADCW2Even k κ (Or.inr (heADCKappaSharpDomain κ hκ).notSquare),
        hTwo, heADCEvenSecond_determinantClass k κ _, H.2.le⟩
  obtain ⟨c, w, hc, hrep, hdet, hlast⟩ := Hbase
  obtain ⟨w', hrep', hdet', hlast'⟩ := Hsharp
  have hne : quadraticDefect K c ≠ quadraticDefect K κ := by
    intro h
    rcases hc with hOne | hDelta
    · subst c
      have htop : quadraticDefect K (1 : Kˣ) = ⊤ :=
        quadraticDefect_eq_top_of_isSquare (K := K) ⟨1, by simp⟩
      rw [htop, hκ] at h
      exact ENat.coe_ne_top _ h.symm
    · have hd : quadraticDefect K c = ((2 * ramificationIndex K : Nat) : ℕ∞) := by
        rw [hDelta]
        exact (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminant_defect
      rw [hd, hκ] at h
      have hnat := ENat.coe_inj.mp h
      have he := ramificationIndex_pos (K := K)
      omega
  exact a.heADCEvenMixedTest_bound k w w' hL hrep hrep'
    (heADCEvenTests_determinants_not_square k c κ w w' hdet hdet' hne) hlast hlast'

end BONG.GoodBONG

end Bong
