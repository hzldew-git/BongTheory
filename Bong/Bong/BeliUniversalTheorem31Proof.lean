/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalTheorem31
import Bong.Bong.Beli2019Lemma34Complete
import Bong.Bong.DiagonalCodimensionOneCancellationProof

/-!
# Proof of Beli's universal Jordan criterion

This file proves the arbitrary-Jordan-decomposition endpoint corresponding to
Theorem 3.1 of C. N. Beli, *Universal integral quadratic forms over dyadic
local fields*.  It transports the good-BONG criterion of Theorem 2.1 to the
prescribed Jordan components using Beli's approximation lemma and
codimension-one cancellation.

The theorem `isUniversal_iff_universalTheorem31DirectConditions` records the
normalization obtained by direct substitution into Theorem 2.1.  The two
printed subcases (3.2.1) and (3.2.2) agree with that normalization when the
first fundamental scale order is zero; this comparison is exposed separately
by `isUniversal_iff_universalTheorem31Conditions_of_firstScaleOrder_eq_zero`.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice.JordanDecomposition

/-- Regard a strict Jordan decomposition as a weak one, forgetting only its
chosen norm generators. -/
noncomputable def toWeakForUniversalApproximation {t : Nat}
    (J : JordanDecomposition q L t) : WeakJordanDecomposition q L t where
  toOrthogonalDecomposition := J.toOrthogonalDecomposition
  scaleGenerator := J.scaleGenerator
  modular := J.modular
  component_finrank_pos := J.component_finrank_pos
  scaleOrder_mono := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact (J.scaleOrder_strict hlt).le

/-- O'Meara 93:15 supplies the improper-even-rank invariant after forgetting
the norm-generator choices of a strict Jordan decomposition. -/
theorem toWeakForUniversalApproximation_hasImproperEvenRank {t : Nat}
    (J : JordanDecomposition q L t) :
    J.toWeakForUniversalApproximation.HasImproperEvenRank := by
  let W := J.toWeakForUniversalApproximation
  intro i hstrict
  by_contra hnotEven
  have hodd : Odd (finrank K (W.component i).carrier) :=
    Nat.not_even_iff_odd.mp hnotEven
  have hproper := Lattice.normIdeal_eq_scaleIdeal_of_modular_of_odd_rank
    (W.component i).space (W.component i).lattice (W.scaleGenerator i)
      (W.modular i) hodd
  have hideal : Lattice.principalIdeal (K := K)
        ((W.normGeneratorUnit i : K)) =
      Lattice.principalIdeal (K := K) ((W.scaleGenerator i : K)) := by
    calc
      Lattice.principalIdeal (K := K) ((W.normGeneratorUnit i : K)) =
          Lattice.normIdeal (W.component i).space
            (W.component i).lattice :=
        (W.normIdeal_eq_normGeneratorUnit i).symm
      _ = Lattice.scaleIdeal (W.component i).space
            (W.component i).lattice := hproper
      _ = Lattice.principalIdeal (K := K)
            ((W.scaleGenerator i : K)) :=
        (W.modular i).scaleIdeal_eq_principal (W.component_finrank_pos i)
  have horders :=
    (Lattice.principalIdeal_eq_iff_ordUnit_eq
      (W.normGeneratorUnit i) (W.scaleGenerator i)).mp hideal
  exact hstrict.ne horders.symm

end Lattice.JordanDecomposition

namespace BONG.JordanOrderProfileWitness

open BONG.GoodBONG

set_option maxHeartbeats 0 in
-- Approximation, determinant transport, and cancellation produce a long proof term.
/-- At a strict Jordan boundary whose good-BONG alpha exceeds `2e`, the
prescribed Jordan prefix and the corresponding good-BONG prefix have the
same quadratic space.  This is the geometric transport needed by Beli's
Theorem 3.1 for an arbitrary prescribed Jordan decomposition. -/
theorem boundaryPrefix_diagonalIsotropic_iff_of_two_e_lt_alpha
    {n t : Nat} (a : GoodBONG q L (n + 2))
    (J : Lattice.JordanDecomposition q L (t + 1))
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (hAlpha : 2 * (ramificationIndex K : ℚ) <
      a.alphaValue (P.boundaryIndex z)) :
    DiagonalIsotropic
        (a.prefixValues ((P.boundaryIndex z).val + 1) (by omega)) ↔
      ¬(J.prefixSpace (z.val + 1)).IsAnisotropicSpace := by
  let W := J.toWeakForUniversalApproximation
  have hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)) := by
    intro i j hij
    exact J.scaleOrder_strict hij
  let H := W.toJordan hstrict
  let Q : JordanOrderProfileWitness a.toBONG H :=
    Classical.choice (a.toBONG.beliLemma47_profile a.good H)
  have hindex : Q.boundaryIndex z = P.boundaryIndex z := by
    apply Fin.ext
    have hQ := Q.boundaryIndex_succ_val_eq_componentRankPrefix z
    have hP := P.boundaryIndex_succ_val_eq_componentRankPrefix z
    change (Q.boundaryIndex z).val + 1 =
      ∑ k ∈ Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex z),
          J.componentRank k at hQ
    have hsucc : (Q.boundaryIndex z).val + 1 =
        (P.boundaryIndex z).val + 1 := hQ.trans hP.symm
    exact Nat.add_right_cancel hsucc
  have hspace : a.IsSpaceApproximation (Q.boundaryIndex z)
      (Q.boundaryPrefixDiagonalUnits z) := by
    apply PrescribedJordanComparison.beli2019Lemma34_i a W
      (J.toWeakForUniversalApproximation_hasImproperEvenRank) hstrict Q z
  let i := Q.boundaryIndex z
  let candidate := Q.boundaryPrefixDiagonalUnits z
  have hAlphaQ : 2 * (ramificationIndex K : ℚ) < a.alphaValue i := by
    simpa only [i, hindex] using hAlpha
  have hcap : a.prefixAlphaCap (i.val + 1) =
      (a.alphaValue i : WithTop ℚ) := by
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
    congr 2
  have hdetBound :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        defectOrder (K := K)
          (diagonalUnitDeterminant candidate *
            a.prefixProduct (i.val + 1)) := by
    have hAlphaTop :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          (a.alphaValue i : WithTop ℚ) := by
      exact_mod_cast hAlphaQ
    apply hAlphaTop.trans_le
    rw [← hcap]
    exact hspace.1.1
  have hsquareRaw : IsSquare
      (diagonalUnitDeterminant candidate *
        a.prefixProduct (i.val + 1)) :=
    GoodBONG.isSquare_of_two_mul_e_lt_defectOrder _ hdetBound
  have hrightCaps :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        a.prefixAlphaCap (i.val + 1) +
          a.prefixAlphaCap (i.val + 2) := by
    have hfirst :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          a.prefixAlphaCap (i.val + 1) := by
      rw [hcap]
      exact_mod_cast hAlphaQ
    exact hfirst.trans_le
      (le_add_of_nonneg_right (a.prefixAlphaCap_nonneg (i.val + 2)))
  have hright : a.rightApproximationTrigger i :=
    a.rightApproximationTrigger_of_prefixCaps i hrightCaps
  let base := a.prefixValueUnits (i.val + 1) (by omega)
  let extended := a.prefixValueUnits (i.val + 2) (by omega)
  have hrepExtended : DiagonalRepresents
      (diagonalUnitCoefficients candidate)
      (diagonalUnitCoefficients extended) := by
    simpa only [i, candidate, extended,
      diagonalUnitCoefficients_prefixValueUnits] using
        hspace.2.2 hright
  have hprefix : diagonalUnitPrefix extended = base := by
    simpa only [extended, base] using
      a.diagonalUnitPrefix_prefixValueUnits (i.val + 1) (by omega)
  have hsquare : IsSquare
      (diagonalUnitDeterminant candidate *
        diagonalUnitDeterminant base) := by
    simpa only [base, diagonalUnitDeterminant_prefixValueUnits] using
      hsquareRaw
  let cancellationLaws : DiagonalCodimensionOneCancellationLaws K :=
    diagonalCodimensionOneCancellationLawsProved K
  have hCandidateBase : DiagonalRepresents
      (diagonalUnitCoefficients candidate)
      (diagonalUnitCoefficients base) :=
    cancellationLaws.cancel base candidate extended hprefix
      hrepExtended hsquare
  have hBaseCandidate : DiagonalRepresents
      (diagonalUnitCoefficients base)
      (diagonalUnitCoefficients candidate) :=
    DiagonalRepresents.symm_of_sameRank hCandidateBase
  have hbaseIffCandidate :
      DiagonalIsotropic (diagonalUnitCoefficients base) ↔
        DiagonalIsotropic (diagonalUnitCoefficients candidate) := by
    constructor
    · exact hBaseCandidate.isotropic_of
    · exact hCandidateBase.isotropic_of
  have hdiag := Q.boundaryPrefixDiagonalizationIsometry z
  change QuadraticSpace.Isometry (J.prefixSpace (z.val + 1))
    (QuadraticSpace.finiteDiagonal
      (diagonalUnitCoefficients candidate)
      (QuadraticSpace.diagonalUnitCoefficients_ne_zero candidate)) at hdiag
  have htransport := hdiag.isAnisotropicSpace_iff_general
  have hcandidateIff :
      DiagonalIsotropic (diagonalUnitCoefficients candidate) ↔
        ¬(J.prefixSpace (z.val + 1)).IsAnisotropicSpace :=
    (QuadraticSpace.not_finiteDiagonal_isAnisotropicSpace_iff
      (diagonalUnitCoefficients candidate)
      (QuadraticSpace.diagonalUnitCoefficients_ne_zero candidate)).symm.trans
        (not_congr htransport).symm
  have hresult := hbaseIffCandidate.trans hcandidateIff
  have hresultQ :
      DiagonalIsotropic
          (a.prefixValues ((Q.boundaryIndex z).val + 1) (by omega)) ↔
        ¬(J.prefixSpace (z.val + 1)).IsAnisotropicSpace := by
    simpa only [base, diagonalUnitCoefficients_prefixValueUnits, i] using
      hresult
  have hprefixCongr := a.diagonalIsotropic_prefixValues_congr
    (k := (P.boundaryIndex z).val + 1)
    (l := (Q.boundaryIndex z).val + 1) (by omega) (by omega)
      (congrArg (fun j : Fin (n + 1) ↦ j.val + 1) hindex.symm)
  exact hprefixCongr.trans hresultQ

/-- Intrinsic Jordan norm/scale data force a high-alpha good-BONG boundary. -/
theorem two_e_lt_alphaValue_boundary_of_normScaleGap
    {n t : Nat} (a : GoodBONG q L (n + 2))
    (J : Lattice.JordanDecomposition q L (t + 1))
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (hgap : 2 * (ramificationIndex K : Int) <
      J.UniversalNormOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex z) +
        J.UniversalNormOrder
          (Lattice.JordanDecomposition.boundaryRightIndex z) -
        2 * J.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex z)) :
    2 * (ramificationIndex K : ℚ) <
      a.alphaValue (P.boundaryIndex z) := by
  apply (a.alpha_p5 (P.boundaryIndex z)).2.2.mpr
  rw [P.orderGap_boundaryIndex_eq_boundaryNormOrderSum_sub_twoScale]
  unfold Lattice.JordanDecomposition.boundaryNormOrderSum
  rw [J.fundamentalNormGenerator_order_eq_effective,
    J.fundamentalNormGenerator_order_eq_effective]
  exact hgap

/-- High-alpha transport for a prescribed binary first Jordan component. -/
theorem universalFirstTwoIsotropic_iff_firstComponentIsIsotropic
    {n t : Nat} (a : GoodBONG q L (n + 2))
    (J : Lattice.JordanDecomposition q L (t + 1))
    (P : JordanOrderProfileWitness a.toBONG J) (ht : 0 < t)
    (hrank : J.componentRank 0 = 2)
    (hAlpha : 2 * (ramificationIndex K : ℚ) <
      a.alphaValue (P.boundaryIndex (⟨0, ht⟩ : Fin t))) :
    a.UniversalFirstTwoIsotropic ↔ J.ComponentIsIsotropic 0 := by
  let z : Fin t := ⟨0, ht⟩
  have hj : (P.boundaryIndex z).val + 1 = 2 := by
    have hraw := P.boundaryIndex_succ_val_eq_componentRankPrefix z
    have hIio :
        Finset.Iio (Lattice.JordanDecomposition.boundaryRightIndex z) =
          {(⟨0, by omega⟩ : Fin (t + 1))} := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_singleton, Fin.ext_iff]
      change k.val < 1 ↔ k.val = 0
      omega
    change (P.boundaryIndex z).val + 1 =
      ∑ k ∈ Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex z),
          J.componentRank k at hraw
    rw [hIio, Finset.sum_singleton] at hraw
    have hzero : (⟨0, by omega⟩ : Fin (t + 1)) = 0 := Fin.ext rfl
    rwa [hzero, hrank] at hraw
  have hboundary :=
    P.boundaryPrefix_diagonalIsotropic_iff_of_two_e_lt_alpha
      a J z (by simpa only [z] using hAlpha)
  have hdiag := a.diagonalIsotropic_prefixValues_congr
    (k := 2) (l := (P.boundaryIndex z).val + 1)
      (by omega) (by omega) hj.symm
  have hboundary' :
      DiagonalIsotropic (a.prefixValues 2 (by omega)) ↔
        ¬(J.prefixSpace 1).IsAnisotropicSpace := by
    simpa only [z] using hdiag.trans hboundary
  have hfirst :=
    J.toOrthogonalDecomposition.firstComponentPrefixLatticeIsometry
      |>.toQuadraticSpaceIsometry
      |>.isAnisotropicSpace_iff_general
  change a.UniversalFirstTwoIsotropic ↔
    ¬(J.component 0).space.IsAnisotropicSpace
  unfold GoodBONG.UniversalFirstTwoIsotropic
  exact hboundary'.trans (not_congr hfirst).symm

/-- High-alpha transport for a prescribed ternary first Jordan component. -/
theorem universalFirstThreeIsotropic_iff_firstComponentIsIsotropic
    {n t : Nat} (a : GoodBONG q L (n + 2))
    (J : Lattice.JordanDecomposition q L (t + 1))
    (P : JordanOrderProfileWitness a.toBONG J) (ht : 0 < t)
    (hrank : J.componentRank 0 = 3)
    (hAlpha : 2 * (ramificationIndex K : ℚ) <
      a.alphaValue (P.boundaryIndex (⟨0, ht⟩ : Fin t))) :
    a.UniversalFirstThreeIsotropic (by
      have hsum := P.sum_componentRank_eq_length
      change (∑ k, J.componentRank k) = n + 2 at hsum
      have hle : J.componentRank 0 ≤ ∑ k, J.componentRank k :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_univ (0 : Fin (t + 1)))
      rw [hrank, hsum] at hle
      omega) ↔ J.ComponentIsIsotropic 0 := by
  let z : Fin t := ⟨0, ht⟩
  have hj : (P.boundaryIndex z).val + 1 = 3 := by
    have hraw := P.boundaryIndex_succ_val_eq_componentRankPrefix z
    have hIio :
        Finset.Iio (Lattice.JordanDecomposition.boundaryRightIndex z) =
          {(⟨0, by omega⟩ : Fin (t + 1))} := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_singleton, Fin.ext_iff]
      change k.val < 1 ↔ k.val = 0
      omega
    change (P.boundaryIndex z).val + 1 =
      ∑ k ∈ Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex z),
          J.componentRank k at hraw
    rw [hIio, Finset.sum_singleton] at hraw
    have hzero : (⟨0, by omega⟩ : Fin (t + 1)) = 0 := Fin.ext rfl
    rwa [hzero, hrank] at hraw
  have hboundary :=
    P.boundaryPrefix_diagonalIsotropic_iff_of_two_e_lt_alpha
      a J z (by simpa only [z] using hAlpha)
  have hdiag := a.diagonalIsotropic_prefixValues_congr
    (k := 3) (l := (P.boundaryIndex z).val + 1)
      (by omega) (by omega) hj.symm
  have hboundary' :
      DiagonalIsotropic (a.prefixValues 3 (by omega)) ↔
        ¬(J.prefixSpace 1).IsAnisotropicSpace := by
    simpa only [z] using hdiag.trans hboundary
  have hfirst :=
    J.toOrthogonalDecomposition.firstComponentPrefixLatticeIsometry
      |>.toQuadraticSpaceIsometry
      |>.isAnisotropicSpace_iff_general
  change a.UniversalFirstThreeIsotropic _ ↔
    ¬(J.component 0).space.IsAnisotropicSpace
  unfold GoodBONG.UniversalFirstThreeIsotropic
  exact hboundary'.trans (not_congr hfirst).symm

/-- High-alpha transport for a prescribed rank-two/rank-one initial pair. -/
theorem universalFirstThreeIsotropic_iff_firstTwoComponentsIsotropic
    {n t : Nat} (a : GoodBONG q L (n + 2))
    (J : Lattice.JordanDecomposition q L (t + 1))
    (P : JordanOrderProfileWitness a.toBONG J) (ht : 1 < t)
    (hrank0 : J.componentRank 0 = 2)
    (hrank1 : J.componentRank (⟨1, by omega⟩ : Fin (t + 1)) = 1)
    (hAlpha : 2 * (ramificationIndex K : ℚ) <
      a.alphaValue (P.boundaryIndex (⟨1, ht⟩ : Fin t))) :
    a.UniversalFirstThreeIsotropic (by
      have hsum := P.sum_componentRank_eq_length
      change (∑ k, J.componentRank k) = n + 2 at hsum
      have hzeroMem : (0 : Fin (t + 1)) ∈
          (Finset.univ : Finset (Fin (t + 1))) := Finset.mem_univ _
      have honeMem : (⟨1, by omega⟩ : Fin (t + 1)) ∈
          (Finset.univ.erase (0 : Fin (t + 1))) := by simp
      have hle1 := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) honeMem
        (f := fun k ↦ J.componentRank k)
      rw [← Finset.sum_erase_add _ _ hzeroMem] at hsum
      rw [hrank0] at hsum
      rw [hrank1] at hle1
      omega) ↔ J.ComponentPrefixIsIsotropic 2 := by
  let z : Fin t := ⟨1, ht⟩
  have hj : (P.boundaryIndex z).val + 1 = 3 := by
    have hraw := P.boundaryIndex_succ_val_eq_componentRankPrefix z
    let kZero : Fin (t + 1) := ⟨0, by omega⟩
    let kOne : Fin (t + 1) := ⟨1, by omega⟩
    have hIio :
        Finset.Iio (Lattice.JordanDecomposition.boundaryRightIndex z) =
          {kZero, kOne} := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_insert,
        Finset.mem_singleton, Fin.ext_iff]
      change k.val < 2 ↔ k.val = kZero.val ∨ k.val = kOne.val
      simp only [kZero, kOne]
      omega
    change (P.boundaryIndex z).val + 1 =
      ∑ k ∈ Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex z),
          J.componentRank k at hraw
    rw [hIio] at hraw
    have hne : kZero ≠ kOne := by
      intro h
      have := congrArg Fin.val h
      simp only [kZero, kOne] at this
      omega
    rw [Finset.sum_insert (by simpa only [Finset.mem_singleton] using hne),
      Finset.sum_singleton] at hraw
    have hz : kZero = (0 : Fin (t + 1)) := Fin.ext rfl
    have ho : kOne = (⟨1, by omega⟩ : Fin (t + 1)) := Fin.ext rfl
    rwa [hz, ho, hrank0, hrank1] at hraw
  have hboundary :=
    P.boundaryPrefix_diagonalIsotropic_iff_of_two_e_lt_alpha
      a J z (by simpa only [z] using hAlpha)
  have hdiag := a.diagonalIsotropic_prefixValues_congr
    (k := 3) (l := (P.boundaryIndex z).val + 1)
      (by omega) (by omega) hj.symm
  have hresult := hdiag.trans hboundary
  change DiagonalIsotropic (a.prefixValues 3 (by omega)) ↔
    ¬(J.toOrthogonalDecomposition.prefixQuadraticSublattice 2).space.IsAnisotropicSpace
  simpa only [z] using hresult

end BONG.JordanOrderProfileWitness

namespace BONG.JordanOrderProfileWitness

variable {n : Nat} {a : GoodBONG q L (n + 2)}

theorem universalTheorem21Conditions_iff_sourceCase1
    {t : Nat} (J : Lattice.JordanDecomposition q L (t + 1))
    (P : JordanOrderProfileWitness a.toBONG J)
    (hrank : 4 ≤ J.componentRank 0) :
    a.UniversalTheorem21Conditions ↔
      J.UniversalNormOrder 0 = 0 ∧ J.UniversalJordanCase1 := by
  have hsum := P.sum_componentRank_eq_length
  change (∑ k, J.componentRank k) = n + 2 at hsum
  have hle : J.componentRank 0 ≤ ∑ k, J.componentRank k :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ (0 : Fin (t + 1)))
  have hn : 2 ≤ n := by
    rw [hsum] at hle
    omega
  have horder0 : a.order 0 = J.UniversalNormOrder 0 := by
    exact P.order_zero_eq_firstUniversalNormOrder
  constructor
  · rintro ⟨hzero, hcase⟩
    have hnorm : J.UniversalNormOrder 0 = 0 := by
      rw [← horder0]
      exact hzero
    refine ⟨hnorm, hrank, ?_⟩
    apply (P.p_le_first_fundamentalWeightIdeal_iff_alpha_le_one
      (by omega) hzero).2
    rcases hcase with hI | hII
    · rw [hI.alphaOne]
      norm_num
    · rw [hII.alphaOne]
  · rintro ⟨hnorm, hcase⟩
    have hnormRaw : BONG.jordanEffectiveNormOrder J 0 = 0 := hnorm
    have hzero : a.order 0 = 0 := by rw [horder0, hnorm]
    have halphaLe : a.alphaValue 0 ≤ 1 :=
      (P.p_le_first_fundamentalWeightIdeal_iff_alpha_le_one
        (by omega) hzero).1 hcase.2
    refine ⟨hzero, ?_⟩
    by_cases halphaZero : a.alphaValue 0 = 0
    · left
      refine
        { alphaOne := halphaZero
          binaryRankTwo := ?_
          binaryAboveOne := ?_
          binaryAtOne := ?_ }
      · intro htail
        omega
      · intro hthree hlarge
        have horder2 : a.order (⟨2, by omega⟩ : Fin (n + 2)) =
            J.UniversalNormOrder 0 :=
          P.order_two_eq_firstUniversalNormOrder (by omega) (by omega)
        rw [horder2, hnorm] at hlarge
        omega
      · intro hthree hone htrigger
        have horder2 : a.order (⟨2, by omega⟩ : Fin (n + 2)) =
            J.UniversalNormOrder 0 :=
          P.order_two_eq_firstUniversalNormOrder (by omega) (by omega)
        rw [horder2, hnorm] at hone
        omega
    · right
      have halphaOne : a.alphaValue 0 = 1 := by
        have halphaGe := a.one_le_alphaValue_of_ne_zero 0 halphaZero
        linarith
      have hscaleLe : J.fundamentalScaleOrder 0 ≤ J.UniversalNormOrder 0 :=
        J.fundamentalScaleOrder_le_universalNormOrder 0
      have hscale : J.fundamentalScaleOrder 0 ≤ 0 := by
        rw [hnorm] at hscaleLe
        exact hscaleLe
      have horder1 : a.order (⟨1, by omega⟩ : Fin (n + 2)) =
          2 * J.fundamentalScaleOrder 0 := by
        rw [P.order_one_eq_two_firstScale_sub_norm (by omega) (by omega),
          hnormRaw, sub_zero]
      have horder2 : a.order (⟨2, by omega⟩ : Fin (n + 2)) = 0 := by
        rw [P.order_two_eq_firstUniversalNormOrder (by omega) (by omega), hnormRaw]
      have horder3 : a.order (⟨3, by omega⟩ : Fin (n + 2)) =
          2 * J.fundamentalScaleOrder 0 := by
        rw [P.order_three_eq_two_firstScale_sub_norm (by omega) (by omega),
          hnormRaw, sub_zero]
      refine
        { rankAtLeastThree := by omega
          alphaOne := halphaOne
          alphaThreeBound := ?_
          ternaryBoundary := ?_ }
      · intro hbranch
        rcases hbranch with hone | hlarge
        · rw [horder1] at hone
          omega
        · rw [horder2] at hlarge
          omega
      · intro hsecond hthird htrigger
        rcases htrigger with htail | hfour
        · omega
        · rcases hfour with ⟨hfour, hgap⟩
          rw [horder3, horder2] at hgap
          have he := ramificationIndex_pos (K := K)
          omega

theorem universalTheorem21Conditions_iff_sourceCase2
    {t : Nat} (J : Lattice.JordanDecomposition q L (t + 1))
    (P : JordanOrderProfileWitness a.toBONG J)
    (hrank : J.componentRank 0 = 3) :
    a.UniversalTheorem21Conditions ↔
      J.UniversalNormOrder 0 = 0 ∧ J.UniversalJordanCase2 := by
  have hsum := P.sum_componentRank_eq_length
  change (∑ k, J.componentRank k) = n + 2 at hsum
  have hle : J.componentRank 0 ≤ ∑ k, J.componentRank k :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ (0 : Fin (t + 1)))
  have hn : 1 ≤ n := by
    rw [hsum, hrank] at hle
    omega
  have horder0 : a.order 0 = J.UniversalNormOrder 0 :=
    P.order_zero_eq_firstUniversalNormOrder
  constructor
  · rintro ⟨hzero, hcases⟩
    have hnorm : J.UniversalNormOrder 0 = 0 := by
      rw [← horder0]
      exact hzero
    have hnormRaw : BONG.jordanEffectiveNormOrder J 0 = 0 := hnorm
    have hscaleEq := J.universalNormOrder_eq_scaleOrder_of_odd_componentRank
      0 (by rw [hrank]; exact ⟨1, by omega⟩)
    have hscale : J.fundamentalScaleOrder 0 = 0 := by
      rw [← hscaleEq]
      exact hnormRaw
    have horder1 : a.order (⟨1, by omega⟩ : Fin (n + 2)) = 0 := by
      rw [P.order_one_eq_two_firstScale_sub_norm (by omega) (by omega),
        hscale, hnormRaw]
      norm_num
    have horder2 : a.order (⟨2, by omega⟩ : Fin (n + 2)) = 0 := by
      rw [P.order_two_eq_firstUniversalNormOrder (by omega) (by omega), hnormRaw]
    have hII : a.UniversalCaseII := by
      rcases hcases with hI | hII
      · have hgap := (a.alpha_p2 (0 : Fin (n + 1))).2.mp hI.alphaOne
        unfold GoodBONG.orderGap at hgap
        have hzeroCast :
            a.order (Fin.castSucc (0 : Fin (n + 1))) = 0 := by
          simpa using hzero
        have honeIndex : Fin.succ (0 : Fin (n + 1)) =
            (⟨1, by omega⟩ : Fin (n + 2)) := Fin.ext rfl
        rw [hzeroCast, honeIndex, horder1] at hgap
        have he := ramificationIndex_pos (K := K)
        omega
      · exact hII
    refine ⟨hnorm, hrank, ?_, ?_⟩
    · exact (P.first_fundamentalWeightIdeal_eq_p_iff_alpha_eq_one
        (by omega) hzero).2 hII.alphaOne
    · by_cases ht : t = 0
      · subst t
        right
        have hnEq : n = 1 := by
          have hsum' := hsum
          rw [Fin.sum_univ_one] at hsum'
          rw [hrank] at hsum'
          omega
        subst n
        have hisoAmbient : ¬q.IsAnisotropicSpace :=
          (Bong.BONG.StrictJordanAdaptedAlignment.GoodBONG.universalFirstThreeIsotropic_iff_ambientIsotropic a).1
            (hII.ternaryBoundary (by simpa using horder1.le)
              (by rw [horder2]; omega) (Or.inl rfl))
        exact (J.componentIsIsotropic_zero_iff_ambientIsotropic).2
          hisoAmbient
      · have htpos : 0 < t := by omega
        let k : Fin (t + 1) := ⟨1, by omega⟩
        by_cases hu : J.UniversalNormOrder k ≤
            2 * (ramificationIndex K : Int)
        · left
          exact ⟨k, rfl, hu⟩
        · right
          have huGt : 2 * (ramificationIndex K : Int) <
              J.UniversalNormOrder k := by omega
          have hstart : (P.componentFirstGlobalIndex k).val = 3 := by
            simpa only [k, hrank] using P.componentFirstGlobalIndex_one_val htpos
          have hnTwo : 2 ≤ n := by
            have hkpos : 0 < J.componentRank k := J.component_finrank_pos k
            have hle' : J.componentRank 0 + J.componentRank k ≤
                ∑ z, J.componentRank z := by
              have hzeroMem : (0 : Fin (t + 1)) ∈
                  (Finset.univ : Finset (Fin (t + 1))) := Finset.mem_univ _
              have hkMem : k ∈
                  (Finset.univ.erase (0 : Fin (t + 1))) := by
                simp [k]
              have hkLe := Finset.single_le_sum
                (fun _ _ ↦ Nat.zero_le _) hkMem
                (f := fun z ↦ J.componentRank z)
              rw [← Finset.sum_erase_add _ _ hzeroMem]
              omega
            rw [hsum, hrank] at hle'
            omega
          have horder3 : a.order (⟨3, by omega⟩ : Fin (n + 2)) =
              J.UniversalNormOrder k :=
            (P.universalNormOrder_eq_order_of_componentFirst_val k
              (⟨3, by omega⟩ : Fin (n + 2)) hstart).symm
          have hprefixIso := hII.ternaryBoundary
            (by simpa using horder1.le) (by rw [horder2]; omega)
            (Or.inr ⟨by omega, by rw [horder3, horder2]; omega⟩)
          let z : Fin t := ⟨0, htpos⟩
          have hAlpha :=
            P.two_e_lt_alphaValue_boundary_of_normScaleGap a J z (by
              change 2 * (ramificationIndex K : Int) <
                J.UniversalNormOrder 0 + J.UniversalNormOrder k -
                  2 * J.fundamentalScaleOrder 0
              rw [hnorm, hscale]
              omega)
          exact (P.universalFirstThreeIsotropic_iff_firstComponentIsIsotropic
            a J htpos hrank (by simpa only [z] using hAlpha)).1 hprefixIso
  · rintro ⟨hnorm, hcase⟩
    have hnormRaw : BONG.jordanEffectiveNormOrder J 0 = 0 := hnorm
    have hzero : a.order 0 = 0 := by rw [horder0, hnorm]
    have hscaleEq := J.universalNormOrder_eq_scaleOrder_of_odd_componentRank
      0 (by rw [hrank]; exact ⟨1, by omega⟩)
    have hscale : J.fundamentalScaleOrder 0 = 0 := by
      rw [← hscaleEq]
      exact hnormRaw
    have horder1 : a.order (⟨1, by omega⟩ : Fin (n + 2)) = 0 := by
      rw [P.order_one_eq_two_firstScale_sub_norm (by omega) (by omega),
        hscale, hnormRaw]
      norm_num
    have horder2 : a.order (⟨2, by omega⟩ : Fin (n + 2)) = 0 := by
      rw [P.order_two_eq_firstUniversalNormOrder (by omega) (by omega), hnormRaw]
    have halpha : a.alphaValue 0 = 1 :=
      (P.first_fundamentalWeightIdeal_eq_p_iff_alpha_eq_one
        (by omega) hzero).1 hcase.2.1
    refine ⟨hzero, Or.inr ?_⟩
    refine
      { rankAtLeastThree := by omega
        alphaOne := halpha
        alphaThreeBound := ?_
        ternaryBoundary := ?_ }
    · intro hbranch
      rcases hbranch with hone | hlarge
      · rw [horder1] at hone
        omega
      · rw [horder2] at hlarge
        omega
    · intro hsecond hthird htrigger
      rcases hcase.2.2 with hu | hiso
      · rcases hu with ⟨i, hi, hui⟩
        have htpos : 0 < t := by omega
        let k : Fin (t + 1) := ⟨1, by omega⟩
        have hik : i = k := Fin.ext hi
        rw [hik] at hui
        have hstart : (P.componentFirstGlobalIndex k).val = 3 := by
          simpa only [k, hrank] using P.componentFirstGlobalIndex_one_val htpos
        have horder3 : a.order (⟨3, by omega⟩ : Fin (n + 2)) =
            J.UniversalNormOrder k :=
          (P.universalNormOrder_eq_order_of_componentFirst_val k
            (⟨3, by omega⟩ : Fin (n + 2)) hstart).symm
        rcases htrigger with hnOne | hfour
        · have hkpos : 0 < J.componentRank k := J.component_finrank_pos k
          have hle' : J.componentRank 0 + J.componentRank k ≤
              ∑ z, J.componentRank z := by
            have hzeroMem : (0 : Fin (t + 1)) ∈
                (Finset.univ : Finset (Fin (t + 1))) := Finset.mem_univ _
            have hkMem : k ∈
                (Finset.univ.erase (0 : Fin (t + 1))) := by
              simp [k]
            have hkLe := Finset.single_le_sum
              (fun _ _ ↦ Nat.zero_le _) hkMem
              (f := fun z ↦ J.componentRank z)
            rw [← Finset.sum_erase_add _ _ hzeroMem]
            omega
          rw [hsum, hrank, hnOne] at hle'
          omega
        · rcases hfour with ⟨hfour, hgap⟩
          rw [horder3, horder2] at hgap
          omega
      · by_cases ht : t = 0
        · subst t
          have hnEq : n = 1 := by
            have hsum' := hsum
            rw [Fin.sum_univ_one] at hsum'
            rw [hrank] at hsum'
            omega
          subst n
          apply (Bong.BONG.StrictJordanAdaptedAlignment.GoodBONG.universalFirstThreeIsotropic_iff_ambientIsotropic a).2
          exact (J.componentIsIsotropic_zero_iff_ambientIsotropic).1 hiso
        · have htpos : 0 < t := by omega
          let k : Fin (t + 1) := ⟨1, by omega⟩
          have hstart : (P.componentFirstGlobalIndex k).val = 3 := by
            simpa only [k, hrank] using
              P.componentFirstGlobalIndex_one_val htpos
          have horder3 : a.order (⟨3, by omega⟩ : Fin (n + 2)) =
              J.UniversalNormOrder k :=
            (P.universalNormOrder_eq_order_of_componentFirst_val k
              (⟨3, by omega⟩ : Fin (n + 2)) hstart).symm
          have huGt : 2 * (ramificationIndex K : Int) <
              J.UniversalNormOrder k := by
            rcases htrigger with hnOne | hfour
            · have hg := (P.componentFirstGlobalIndex k).isLt
              rw [hstart, hnOne] at hg
              omega
            · rcases hfour with ⟨hfour, hgap⟩
              rw [horder3, horder2] at hgap
              omega
          let z : Fin t := ⟨0, htpos⟩
          have hAlpha :=
            P.two_e_lt_alphaValue_boundary_of_normScaleGap a J z (by
              change 2 * (ramificationIndex K : Int) <
                J.UniversalNormOrder 0 + J.UniversalNormOrder k -
                  2 * J.fundamentalScaleOrder 0
              rw [hnorm, hscale]
              omega)
          exact (P.universalFirstThreeIsotropic_iff_firstComponentIsIsotropic
            a J htpos hrank (by simpa only [z] using hAlpha)).2 hiso

/-- Terminal binary counterpart of the source-boundary isotropy bridge. -/
theorem GoodBONG.universalFirstTwoIsotropic_iff_ambientIsotropic
    (a : GoodBONG q L 2) :
    a.UniversalFirstTwoIsotropic ↔ ¬q.IsAnisotropicSpace := by
  have hf := QuadraticSpace.Isometry.isAnisotropicSpace_iff_general
    a.toBONG.exactDiagonalizationIsometry
  have hd := QuadraticSpace.not_finiteDiagonal_isAnisotropicSpace_iff
    a.toBONG.value a.toBONG.value_ne_zero
  have hvalues : a.prefixValues 2 (by omega) = a.toBONG.value := by
    funext i
    rfl
  unfold GoodBONG.UniversalFirstTwoIsotropic
  rw [hvalues]
  exact hd.symm.trans (not_congr hf).symm

theorem universalCaseI_iff_sourceCase31
    {t : Nat} (J : Lattice.JordanDecomposition q L (t + 1))
    (P : JordanOrderProfileWitness a.toBONG J)
    (hrank : J.componentRank 0 = 2)
    (hnorm : J.UniversalNormOrder 0 = 0) :
    a.UniversalCaseI ↔
      J.UniversalJordanCase31 := by
  have hnormRaw : BONG.jordanEffectiveNormOrder J 0 = 0 := hnorm
  have hsum := P.sum_componentRank_eq_length
  change (∑ k, J.componentRank k) = n + 2 at hsum
  have horder0 : a.order 0 = 0 := by
    rw [P.order_zero_eq_firstUniversalNormOrder, hnormRaw]
  have hscaleLe : J.fundamentalScaleOrder 0 ≤ 0 := by
    have h := J.fundamentalScaleOrder_le_universalNormOrder 0
    change J.fundamentalScaleOrder 0 ≤
      BONG.jordanEffectiveNormOrder J 0 at h
    rw [hnormRaw] at h
    exact h
  have horder1 : a.order (⟨1, by omega⟩ : Fin (n + 2)) =
      2 * J.fundamentalScaleOrder 0 := by
    rw [P.order_one_eq_two_firstScale_sub_norm (by omega) (by omega),
      hnormRaw, sub_zero]
  have halphaZero_iff : a.alphaValue 0 = 0 ↔
      J.fundamentalScaleOrder 0 = -(ramificationIndex K : Int) := by
    rw [(a.alpha_p2 (0 : Fin (n + 1))).2]
    unfold GoodBONG.orderGap
    have hzeroCast : a.order (Fin.castSucc (0 : Fin (n + 1))) = 0 := by
      simpa using horder0
    have honeIndex : Fin.succ (0 : Fin (n + 1)) =
        (⟨1, by omega⟩ : Fin (n + 2)) := Fin.ext rfl
    rw [hzeroCast, honeIndex, horder1]
    constructor <;> intro h <;> omega
  have hcomponentToBinary
      (hscale : J.fundamentalScaleOrder 0 =
        -(ramificationIndex K : Int))
      (ht : 0 < t)
      (huPos : 0 < J.UniversalNormOrder (⟨1, by omega⟩ : Fin (t + 1)))
      (hiso : J.ComponentIsIsotropic 0) : a.UniversalFirstTwoIsotropic := by
    let k : Fin (t + 1) := ⟨1, by omega⟩
    let z : Fin t := ⟨0, ht⟩
    have hAlpha :=
      P.two_e_lt_alphaValue_boundary_of_normScaleGap a J z (by
        change 2 * (ramificationIndex K : Int) <
          J.UniversalNormOrder 0 + J.UniversalNormOrder k -
            2 * J.fundamentalScaleOrder 0
        rw [hnorm, hscale]
        change 0 < J.UniversalNormOrder k at huPos
        omega)
    exact (P.universalFirstTwoIsotropic_iff_firstComponentIsIsotropic
      a J ht hrank (by simpa only [z] using hAlpha)).2 hiso
  have hbinaryToHalf
      (hscale : J.fundamentalScaleOrder 0 = -(ramificationIndex K : Int))
      (ht : 0 < t)
      (huPos : 0 < J.UniversalNormOrder (⟨1, by omega⟩ : Fin (t + 1)))
      (hiso : a.UniversalFirstTwoIsotropic) :
      J.FirstComponentIsHalfHyperbolic := by
    apply (_root_.Bong.Lattice.JordanDecomposition.componentIsIsotropic_iff_firstComponentIsHalfHyperbolic J hrank hscale hnorm).1
    let k : Fin (t + 1) := ⟨1, by omega⟩
    let z : Fin t := ⟨0, ht⟩
    have hAlpha :=
      P.two_e_lt_alphaValue_boundary_of_normScaleGap a J z (by
        change 2 * (ramificationIndex K : Int) <
          J.UniversalNormOrder 0 + J.UniversalNormOrder k -
            2 * J.fundamentalScaleOrder 0
        rw [hnorm, hscale]
        change 0 < J.UniversalNormOrder k at huPos
        omega)
    exact (P.universalFirstTwoIsotropic_iff_firstComponentIsIsotropic
      a J ht hrank (by simpa only [z] using hAlpha)).1 hiso
  constructor
  · intro hI
    have hscale : J.fundamentalScaleOrder 0 =
        -(ramificationIndex K : Int) := halphaZero_iff.mp hI.alphaOne
    refine ⟨hscale, ?_⟩
    by_cases ht : t = 0
    · subst t
      have hnEq : n = 0 := by
        have hsum' := hsum
        rw [Fin.sum_univ_one, hrank] at hsum'
        omega
      subst n
      right
      right
      have hbinary := hI.binaryRankTwo rfl
      have hambient :=
        (Bong.BONG.JordanOrderProfileWitness.GoodBONG.universalFirstTwoIsotropic_iff_ambientIsotropic a).1 hbinary
      have hcomponent :=
        (J.componentIsIsotropic_zero_iff_ambientIsotropic).2 hambient
      exact (_root_.Bong.Lattice.JordanDecomposition.componentIsIsotropic_iff_firstComponentIsHalfHyperbolic J hrank hscale hnorm).1 hcomponent
    · have htpos : 0 < t := by omega
      let k : Fin (t + 1) := ⟨1, by omega⟩
      have hstart : (P.componentFirstGlobalIndex k).val = 2 := by
        simpa only [k, hrank] using P.componentFirstGlobalIndex_one_val htpos
      have hnPos : 0 < n := by
        have hg := (P.componentFirstGlobalIndex k).isLt
        rw [hstart] at hg
        omega
      have horder2 : a.order (⟨2, by omega⟩ : Fin (n + 2)) =
          J.UniversalNormOrder k :=
        (P.universalNormOrder_eq_order_of_componentFirst_val k
          (⟨2, by omega⟩ : Fin (n + 2)) hstart).symm
      have huNonneg : 0 ≤ J.UniversalNormOrder k := by
        have hmono := a.order_le_of_le_of_even_sub
          (0 : Fin (n + 2)) (⟨2, by omega⟩ : Fin (n + 2))
          (by norm_num) (by exact ⟨1, rfl⟩)
        rw [horder0, horder2] at hmono
        exact hmono
      by_cases huZero : J.UniversalNormOrder k = 0
      · left
        exact ⟨k, rfl, huZero⟩
      · by_cases huOne : J.UniversalNormOrder k = 1
        · have hrankPos : 0 < J.componentRank k := J.component_finrank_pos k
          by_cases hrankTwo : 2 ≤ J.componentRank k
          · right
            left
            exact ⟨k, rfl, huOne, Or.inl hrankTwo⟩
          · have hrankOne : J.componentRank k = 1 := by omega
            by_cases htOne : t = 1
            · subst t
              have hnEq : n = 1 := by
                have hsum' := hsum
                rw [Fin.sum_univ_two, hrank] at hsum'
                change J.componentRank (1 : Fin 2) = 1 at hrankOne
                rw [hrankOne] at hsum'
                omega
              have hbinary := hI.binaryAtOne (by omega)
                (by rw [horder2, huOne]) (Or.inl hnEq)
              right
              right
              exact hbinaryToHalf hscale (by omega)
                (by simpa only [k] using
                  (show 0 < J.UniversalNormOrder k by omega)) hbinary
            · have htTwo : 1 < t := by omega
              let j : Fin (t + 1) := ⟨2, by omega⟩
              have hstartJ : (P.componentFirstGlobalIndex j).val = 3 := by
                simpa only [j, k, hrank, hrankOne] using
                  P.componentFirstGlobalIndex_two_val htTwo
              have hnTwo : 1 < n := by
                have hg := (P.componentFirstGlobalIndex j).isLt
                rw [hstartJ] at hg
                omega
              have horder3 : a.order (⟨3, by omega⟩ : Fin (n + 2)) =
                  J.UniversalNormOrder j :=
                (P.universalNormOrder_eq_order_of_componentFirst_val j
                  (⟨3, by omega⟩ : Fin (n + 2)) hstartJ).symm
              by_cases huJ : J.UniversalNormOrder j ≤
                  2 * (ramificationIndex K : Int) + 1
              · right
                left
                exact ⟨k, rfl, huOne, Or.inr ⟨hrankOne, j, rfl, huJ⟩⟩
              · have hbinary := hI.binaryAtOne (by omega)
                  (by rw [horder2, huOne])
                  (Or.inr ⟨by omega, by rw [horder3]; omega⟩)
                right
                right
                exact hbinaryToHalf hscale htpos
                  (by simpa only [k] using
                    (show 0 < J.UniversalNormOrder k by omega)) hbinary
        · have huLarge : 1 < J.UniversalNormOrder k := by omega
          have hbinary := hI.binaryAboveOne (by omega) (by
            rw [horder2]
            exact huLarge)
          right
          right
          exact hbinaryToHalf hscale htpos
            (by simpa only [k] using
              (show 0 < J.UniversalNormOrder k by omega)) hbinary
  · rintro ⟨hscale, hcases⟩
    have halpha : a.alphaValue 0 = 0 := halphaZero_iff.mpr hscale
    rcases hcases with h311 | h312 | hhalf
    · rcases h311 with ⟨i, hi, hui⟩
      have htpos : 0 < t := by omega
      let k : Fin (t + 1) := ⟨1, by omega⟩
      have hik : i = k := Fin.ext hi
      rw [hik] at hui
      have hstart : (P.componentFirstGlobalIndex k).val = 2 := by
        simpa only [k, hrank] using P.componentFirstGlobalIndex_one_val htpos
      have hnPos : 0 < n := by
        have hg := (P.componentFirstGlobalIndex k).isLt
        rw [hstart] at hg
        omega
      have horder2 : a.order (⟨2, by omega⟩ : Fin (n + 2)) =
          J.UniversalNormOrder k :=
        (P.universalNormOrder_eq_order_of_componentFirst_val k
          (⟨2, by omega⟩ : Fin (n + 2)) hstart).symm
      refine
        { alphaOne := halpha
          binaryRankTwo := by intro h; omega
          binaryAboveOne := ?_
          binaryAtOne := ?_ }
      · intro hthree hlarge
        rw [horder2, hui] at hlarge
        omega
      · intro hthree hone htrigger
        rw [horder2, hui] at hone
        omega
    · rcases h312 with ⟨i, hi, hui, hrankCases⟩
      have htpos : 0 < t := by omega
      let k : Fin (t + 1) := ⟨1, by omega⟩
      have hik : i = k := Fin.ext hi
      rw [hik] at hui hrankCases
      have hstart : (P.componentFirstGlobalIndex k).val = 2 := by
        simpa only [k, hrank] using P.componentFirstGlobalIndex_one_val htpos
      have hnPos : 0 < n := by
        have hg := (P.componentFirstGlobalIndex k).isLt
        rw [hstart] at hg
        omega
      have horder2 : a.order (⟨2, by omega⟩ : Fin (n + 2)) =
          J.UniversalNormOrder k :=
        (P.universalNormOrder_eq_order_of_componentFirst_val k
          (⟨2, by omega⟩ : Fin (n + 2)) hstart).symm
      refine
        { alphaOne := halpha
          binaryRankTwo := by intro h; omega
          binaryAboveOne := ?_
          binaryAtOne := ?_ }
      · intro hthree hlarge
        rw [horder2, hui] at hlarge
        omega
      · intro hthree hone htrigger
        rcases hrankCases with hrankTwo | ⟨hrankOne, j, hj, huj⟩
        · have hkLocal : 1 < J.componentRank k := by omega
          let ell : Fin (J.componentRank k) := ⟨1, hkLocal⟩
          let g : Fin (n + 2) := P.indexEquiv.symm ⟨k, ell⟩
          have hg : g.val = 3 := by
            calc
              g.val = (∑ z ∈ Finset.Iio k, J.componentRank z) + ell.val :=
                P.inverse_index_val k ell
              _ = (∑ z ∈ Finset.Iio k, J.componentRank z) + 1 := by rfl
              _ = (P.componentFirstGlobalIndex k).val + 1 := by
                rw [P.componentFirstGlobalIndex_val]
              _ = 3 := by rw [hstart]
          have hnTwo : 1 < n := by
            have := g.isLt
            rw [hg] at this
            omega
          have hscaleK : J.fundamentalScaleOrder k ≤
              J.UniversalNormOrder k :=
            J.fundamentalScaleOrder_le_universalNormOrder k
          have horder3 : a.order (⟨3, by omega⟩ : Fin (n + 2)) =
              2 * J.fundamentalScaleOrder k - J.UniversalNormOrder k := by
            apply P.order_eq_two_scale_sub_norm_of_componentLocalOne_val
              k hrankTwo
            rw [hstart]
          rcases htrigger with hnOne | hfour
          · omega
          · rcases hfour with ⟨hfour, hlarge⟩
            rw [horder3, hui] at hlarge
            rw [hui] at hscaleK
            have he := ramificationIndex_pos (K := K)
            omega
        · have htTwo : 1 < t := by omega
          let k2 : Fin (t + 1) := ⟨2, by omega⟩
          have hjk : j = k2 := Fin.ext hj
          rw [hjk] at huj
          have hstart2 : (P.componentFirstGlobalIndex k2).val = 3 := by
            simpa only [k2, k, hrank, hrankOne] using
              P.componentFirstGlobalIndex_two_val htTwo
          have hnTwo : 1 < n := by
            have hg := (P.componentFirstGlobalIndex k2).isLt
            rw [hstart2] at hg
            omega
          have horder3 : a.order (⟨3, by omega⟩ : Fin (n + 2)) =
              J.UniversalNormOrder k2 :=
            (P.universalNormOrder_eq_order_of_componentFirst_val k2
              (⟨3, by omega⟩ : Fin (n + 2)) hstart2).symm
          rcases htrigger with hnOne | hfour
          · omega
          · rcases hfour with ⟨hfour, hlarge⟩
            rw [horder3] at hlarge
            omega
    · have hcomponent : J.ComponentIsIsotropic 0 :=
        (_root_.Bong.Lattice.JordanDecomposition.componentIsIsotropic_iff_firstComponentIsHalfHyperbolic J hrank hscale hnorm).2 hhalf
      refine
        { alphaOne := halpha
          binaryRankTwo := ?_
          binaryAboveOne := ?_
          binaryAtOne := ?_ }
      · intro hnZero
        have htZero : t = 0 := by
          by_contra ht
          have htpos : 0 < t := by omega
          let k : Fin (t + 1) := ⟨1, by omega⟩
          have hstart : (P.componentFirstGlobalIndex k).val = 2 := by
            simpa only [k, hrank] using P.componentFirstGlobalIndex_one_val htpos
          have hg := (P.componentFirstGlobalIndex k).isLt
          rw [hstart, hnZero] at hg
          omega
        subst t
        have hnEq : n = 0 := by omega
        subst n
        apply (Bong.BONG.JordanOrderProfileWitness.GoodBONG.universalFirstTwoIsotropic_iff_ambientIsotropic a).2
        exact (J.componentIsIsotropic_zero_iff_ambientIsotropic).1 hcomponent
      · intro hthree hlarge
        have htpos : 0 < t := by
          apply P.componentTail_pos_of_firstRank_lt_length
          rw [hrank]
          omega
        let k : Fin (t + 1) := ⟨1, by omega⟩
        have hstart : (P.componentFirstGlobalIndex k).val = 2 := by
          simpa only [k, hrank] using P.componentFirstGlobalIndex_one_val htpos
        have horder2 : a.order (⟨2, by omega⟩ : Fin (n + 2)) =
            J.UniversalNormOrder k :=
          (P.universalNormOrder_eq_order_of_componentFirst_val k
            (⟨2, by omega⟩ : Fin (n + 2)) hstart).symm
        exact hcomponentToBinary hscale htpos
          (by simpa only [k] using
            (show 0 < J.UniversalNormOrder k by rw [← horder2]; omega))
          hcomponent
      · intro hthree hone htrigger
        have htpos : 0 < t := by
          apply P.componentTail_pos_of_firstRank_lt_length
          rw [hrank]
          omega
        let k : Fin (t + 1) := ⟨1, by omega⟩
        have hstart : (P.componentFirstGlobalIndex k).val = 2 := by
          simpa only [k, hrank] using P.componentFirstGlobalIndex_one_val htpos
        have horder2 : a.order (⟨2, by omega⟩ : Fin (n + 2)) =
            J.UniversalNormOrder k :=
          (P.universalNormOrder_eq_order_of_componentFirst_val k
            (⟨2, by omega⟩ : Fin (n + 2)) hstart).symm
        exact hcomponentToBinary hscale htpos
          (by simpa only [k] using
            (show 0 < J.UniversalNormOrder k by rw [← horder2, hone]; omega))
          hcomponent

theorem universalCaseII_iff_sourceCase32Direct
    {t : Nat} (J : Lattice.JordanDecomposition q L (t + 1))
    (P : JordanOrderProfileWitness a.toBONG J)
    (hrank : J.componentRank 0 = 2)
    (hnorm : J.UniversalNormOrder 0 = 0) :
    a.UniversalCaseII ↔
      J.UniversalJordanCase32Direct := by
  have hnormRaw : BONG.jordanEffectiveNormOrder J 0 = 0 := hnorm
  have hsum := P.sum_componentRank_eq_length
  change (∑ k, J.componentRank k) = n + 2 at hsum
  have horder0 : a.order 0 = 0 := by
    rw [P.order_zero_eq_firstUniversalNormOrder, hnormRaw]
  have hscaleLe : J.fundamentalScaleOrder 0 ≤ 0 := by
    have h := J.fundamentalScaleOrder_le_universalNormOrder 0
    change J.fundamentalScaleOrder 0 ≤
      BONG.jordanEffectiveNormOrder J 0 at h
    rw [hnormRaw] at h
    exact h
  have horder1 : a.order (⟨1, by omega⟩ : Fin (n + 2)) =
      2 * J.fundamentalScaleOrder 0 := by
    rw [P.order_one_eq_two_firstScale_sub_norm (by omega) (by omega),
      hnormRaw, sub_zero]
  constructor
  · intro hII
    have ht : 0 < t := by
      have hnPos := hII.rankAtLeastThree
      apply P.componentTail_pos_of_firstRank_lt_length
      rw [hrank]
      omega
    let k : Fin (t + 1) := ⟨1, by omega⟩
    have hstart : (P.componentFirstGlobalIndex k).val = 2 := by
      simpa only [k, hrank] using P.componentFirstGlobalIndex_one_val ht
    have horder2 : a.order (⟨2, by omega⟩ : Fin (n + 2)) =
        J.UniversalNormOrder k :=
      (P.universalNormOrder_eq_order_of_componentFirst_val k
        (⟨2, by omega⟩ : Fin (n + 2)) hstart).symm
    have huNonneg : 0 ≤ J.UniversalNormOrder k := by
      have hmono := a.order_le_of_le_of_even_sub
        (0 : Fin (n + 2)) (⟨2, by omega⟩ : Fin (n + 2))
        (by norm_num) (by exact ⟨1, rfl⟩)
      rw [horder0, horder2] at hmono
      exact hmono
    refine ⟨?_, ?_, ?_⟩
    · exact (P.first_fundamentalWeightIdeal_eq_p_iff_alpha_eq_one
        (by omega) horder0).2 hII.alphaOne
    · rw [← a.toBONG.length_eq_finrank]
      omega
    · by_cases huLarge : 1 < J.UniversalNormOrder k
      · obtain ⟨hfour, halpha⟩ := hII.alphaThreeBound (Or.inr (by
          rw [horder2]
          exact huLarge))
        have hrankPos : 0 < J.componentRank k := J.component_finrank_pos k
        by_cases hrankTwo : 2 ≤ J.componentRank k
        · left
          refine ⟨k, rfl, huLarge, hrankTwo, ?_⟩
          exact (P.alphaThreeUpperBound_iff_secondWeightIdeal_direct
            hfour ht hnorm hrank hrankTwo).1 halpha
        · have hrankOne : J.componentRank k = 1 := by omega
          have htTwo : 1 < t := by
            apply P.one_lt_componentTail_of_firstTwoRanks_lt_length ht
            rw [hrank, hrankOne]
            omega
          right
          left
          let z : Fin t := ⟨1, by omega⟩
          refine ⟨k, rfl, huLarge, hrankOne, z, rfl, ?_⟩
          exact (P.alphaThreeUpperBound_iff_secondFundamentalIdeal_direct
            hfour htTwo hnorm hrank hrankOne huLarge).1 halpha
      · have huSmall : J.UniversalNormOrder k ≤ 1 := by omega
        have hrankPos : 0 < J.componentRank k := J.component_finrank_pos k
        by_cases hrankTwo : 2 ≤ J.componentRank k
        · right
          right
          left
          exact ⟨k, rfl, huSmall, hrankTwo⟩
        · have hrankOne : J.componentRank k = 1 := by omega
          by_cases htOne : t = 1
          · subst t
            have hnEq : n = 1 := by
              have hsum' := hsum
              rw [Fin.sum_univ_two, hrank] at hsum'
              change J.componentRank (1 : Fin 2) = 1 at hrankOne
              rw [hrankOne] at hsum'
              omega
            have hprefixBONG := hII.ternaryBoundary
              (by rw [horder1]; omega) (by rw [horder2]; exact huSmall)
              (Or.inl hnEq)
            subst n
            right
            right
            right
            right
            refine ⟨k, rfl, huSmall, hrankOne, ?_⟩
            have hambient :=
              (Bong.BONG.StrictJordanAdaptedAlignment.GoodBONG.universalFirstThreeIsotropic_iff_ambientIsotropic a).1
                hprefixBONG
            exact (J.componentPrefixIsIsotropic_two_iff_ambientIsotropic).2
              hambient
          · have htTwo : 1 < t := by omega
            let j : Fin (t + 1) := ⟨2, by omega⟩
            have hstartJ : (P.componentFirstGlobalIndex j).val = 3 := by
              simpa only [j, k, hrank, hrankOne] using
                P.componentFirstGlobalIndex_two_val htTwo
            have hnTwo : 1 < n := by
              have hg := (P.componentFirstGlobalIndex j).isLt
              rw [hstartJ] at hg
              omega
            have horder3 : a.order (⟨3, by omega⟩ : Fin (n + 2)) =
                J.UniversalNormOrder j :=
              (P.universalNormOrder_eq_order_of_componentFirst_val j
                (⟨3, by omega⟩ : Fin (n + 2)) hstartJ).symm
            by_cases huJ : J.UniversalNormOrder j ≤
                J.UniversalNormOrder k + 2 * (ramificationIndex K : Int)
            · right
              right
              right
              left
              exact ⟨k, rfl, huSmall, hrankOne, j, rfl, huJ⟩
            · have hprefixBONG := hII.ternaryBoundary
                (by rw [horder1]; omega) (by rw [horder2]; exact huSmall)
                (Or.inr ⟨by omega, by rw [horder3, horder2]; omega⟩)
              right
              right
              right
              right
              refine ⟨k, rfl, huSmall, hrankOne, ?_⟩
              let z : Fin t := ⟨1, htTwo⟩
              have hscaleK : J.fundamentalScaleOrder k ≤
                  J.UniversalNormOrder k :=
                J.fundamentalScaleOrder_le_universalNormOrder k
              have hAlpha :=
                P.two_e_lt_alphaValue_boundary_of_normScaleGap a J z (by
                  change 2 * (ramificationIndex K : Int) <
                    J.UniversalNormOrder k + J.UniversalNormOrder j -
                      2 * J.fundamentalScaleOrder k
                  omega)
              exact (P.universalFirstThreeIsotropic_iff_firstTwoComponentsIsotropic
                a J htTwo hrank hrankOne
                  (by simpa only [z] using hAlpha)).1 hprefixBONG
  · rintro ⟨hweight, hfinrank, hcases⟩
    have halpha : a.alphaValue 0 = 1 :=
      (P.first_fundamentalWeightIdeal_eq_p_iff_alpha_eq_one
        (by omega) horder0).1 hweight
    have hnPos : 0 < n := by
      rw [← a.toBONG.length_eq_finrank] at hfinrank
      omega
    have ht : 0 < t := by
      apply P.componentTail_pos_of_firstRank_lt_length
      rw [hrank]
      omega
    let k : Fin (t + 1) := ⟨1, by omega⟩
    have hstart : (P.componentFirstGlobalIndex k).val = 2 := by
      simpa only [k, hrank] using P.componentFirstGlobalIndex_one_val ht
    have horder2 : a.order (⟨2, by omega⟩ : Fin (n + 2)) =
        J.UniversalNormOrder k :=
      (P.universalNormOrder_eq_order_of_componentFirst_val k
        (⟨2, by omega⟩ : Fin (n + 2)) hstart).symm
    refine
      { rankAtLeastThree := hnPos
        alphaOne := halpha
        alphaThreeBound := ?_
        ternaryBoundary := ?_ }
    · intro hbranch
      rcases hbranch with hsecondOne | hthirdLarge
      · rw [horder1] at hsecondOne
        omega
      · have huLarge : 1 < J.UniversalNormOrder k := by
          rw [horder2] at hthirdLarge
          exact hthirdLarge
        rcases hcases with h321 | h322 | h323 | h324 | h325
        · rcases h321 with ⟨i, hi, hui, hrankI, hideal⟩
          have hik : i = k := Fin.ext hi
          rw [hik] at hui hrankI hideal
          have hfour : 1 < n := by
            have hkLocal : 1 < J.componentRank k := by omega
            let ell : Fin (J.componentRank k) := ⟨1, hkLocal⟩
            let g : Fin (n + 2) := P.indexEquiv.symm ⟨k, ell⟩
            have hg : g.val = 3 := by
              calc
                g.val = (∑ z ∈ Finset.Iio k, J.componentRank z) + ell.val :=
                  P.inverse_index_val k ell
                _ = (∑ z ∈ Finset.Iio k, J.componentRank z) + 1 := by rfl
                _ = (P.componentFirstGlobalIndex k).val + 1 := by
                  rw [P.componentFirstGlobalIndex_val]
                _ = 3 := by rw [hstart]
            have hglt := g.isLt
            rw [hg] at hglt
            omega
          exact ⟨hfour,
            (P.alphaThreeUpperBound_iff_secondWeightIdeal_direct
              hfour ht hnorm hrank hrankI).2 hideal⟩
        · rcases h322 with ⟨i, hi, hui, hrankI, z, hz, hideal⟩
          have hik : i = k := Fin.ext hi
          rw [hik] at hui hrankI hideal
          have htTwo : 1 < t := by omega
          have hfour : 1 < n := by
            have hb := P.boundaryIndex_one_val_of_firstTwoRanks
              htTwo hrank hrankI
            have hlt := (P.boundaryIndex (⟨1, by omega⟩ : Fin t)).isLt
            rw [hb] at hlt
            omega
          have hzStd : z = (⟨1, by omega⟩ : Fin t) := Fin.ext hz
          rw [hzStd] at hideal
          exact ⟨hfour,
            (P.alphaThreeUpperBound_iff_secondFundamentalIdeal_direct
              hfour htTwo hnorm hrank hrankI huLarge).2 hideal⟩
        · rcases h323 with ⟨i, hi, hui, hrankI⟩
          have hik : i = k := Fin.ext hi
          rw [hik] at hui
          omega
        · rcases h324 with ⟨i, hi, hui, hrankI, j, hj, huj⟩
          have hik : i = k := Fin.ext hi
          rw [hik] at hui
          omega
        · rcases h325 with ⟨i, hi, hui, hrankI, hiso⟩
          have hik : i = k := Fin.ext hi
          rw [hik] at hui
          omega
    · intro hsecond hthird htrigger
      rcases hcases with h321 | h322 | h323 | h324 | h325
      · rcases h321 with ⟨i, hi, hui, hrankI, hideal⟩
        have hik : i = k := Fin.ext hi
        rw [hik, ← horder2] at hui
        omega
      · rcases h322 with ⟨i, hi, hui, hrankI, z, hz, hideal⟩
        have hik : i = k := Fin.ext hi
        rw [hik, ← horder2] at hui
        omega
      · rcases h323 with ⟨i, hi, hui, hrankI⟩
        have hik : i = k := Fin.ext hi
        rw [hik] at hui hrankI
        have hscaleK : J.fundamentalScaleOrder k ≤
            J.UniversalNormOrder k :=
          J.fundamentalScaleOrder_le_universalNormOrder k
        have hkLocal : 1 < J.componentRank k := by omega
        let ell : Fin (J.componentRank k) := ⟨1, hkLocal⟩
        let g : Fin (n + 2) := P.indexEquiv.symm ⟨k, ell⟩
        have hg : g.val = 3 := by
          calc
            g.val = (∑ z ∈ Finset.Iio k, J.componentRank z) + ell.val :=
              P.inverse_index_val k ell
            _ = (∑ z ∈ Finset.Iio k, J.componentRank z) + 1 := by rfl
            _ = (P.componentFirstGlobalIndex k).val + 1 := by
              rw [P.componentFirstGlobalIndex_val]
            _ = 3 := by rw [hstart]
        have hnTwo : 1 < n := by
          have hglt := g.isLt
          rw [hg] at hglt
          omega
        have horder3 : a.order (⟨3, by omega⟩ : Fin (n + 2)) =
            2 * J.fundamentalScaleOrder k - J.UniversalNormOrder k := by
          apply P.order_eq_two_scale_sub_norm_of_componentLocalOne_val
            k hrankI
          rw [hstart]
        rcases htrigger with hnOne | hfour
        · omega
        · rcases hfour with ⟨hfour, hgap⟩
          rw [horder3, horder2] at hgap
          have he := ramificationIndex_pos (K := K)
          omega
      · rcases h324 with ⟨i, hi, hui, hrankI, j, hj, huj⟩
        have hik : i = k := Fin.ext hi
        rw [hik] at hui hrankI huj
        have htTwo : 1 < t := by omega
        let k2 : Fin (t + 1) := ⟨2, by omega⟩
        have hjk : j = k2 := Fin.ext hj
        rw [hjk] at huj
        have hstart2 : (P.componentFirstGlobalIndex k2).val = 3 := by
          simpa only [k2, k, hrank, hrankI] using
            P.componentFirstGlobalIndex_two_val htTwo
        have horder3 : a.order (⟨3, by omega⟩ : Fin (n + 2)) =
            J.UniversalNormOrder k2 :=
          (P.universalNormOrder_eq_order_of_componentFirst_val k2
            (⟨3, by omega⟩ : Fin (n + 2)) hstart2).symm
        rcases htrigger with hnOne | hfour
        · have hg := (P.componentFirstGlobalIndex k2).isLt
          rw [hstart2, hnOne] at hg
          omega
        · rcases hfour with ⟨hfour, hgap⟩
          rw [horder3, horder2] at hgap
          omega
      · rcases h325 with ⟨i, hi, hui, hrankI, hiso⟩
        have hik : i = k := Fin.ext hi
        rw [hik] at hui hrankI
        by_cases htOne : t = 1
        · subst t
          have hnEq : n = 1 := by
            have hsum' := hsum
            rw [Fin.sum_univ_two, hrank] at hsum'
            change J.componentRank (1 : Fin 2) = 1 at hrankI
            rw [hrankI] at hsum'
            omega
          subst n
          apply (Bong.BONG.StrictJordanAdaptedAlignment.GoodBONG.universalFirstThreeIsotropic_iff_ambientIsotropic a).2
          exact (J.componentPrefixIsIsotropic_two_iff_ambientIsotropic).1 hiso
        · have htTwo : 1 < t := by omega
          let k2 : Fin (t + 1) := ⟨2, by omega⟩
          have hstart2 : (P.componentFirstGlobalIndex k2).val = 3 := by
            simpa only [k2, k, hrank, hrankI] using
              P.componentFirstGlobalIndex_two_val htTwo
          have horder3 : a.order (⟨3, by omega⟩ : Fin (n + 2)) =
              J.UniversalNormOrder k2 :=
            (P.universalNormOrder_eq_order_of_componentFirst_val k2
              (⟨3, by omega⟩ : Fin (n + 2)) hstart2).symm
          have huGap : J.UniversalNormOrder k +
                2 * (ramificationIndex K : Int) <
              J.UniversalNormOrder k2 := by
            rcases htrigger with hnOne | hfour
            · have hg := (P.componentFirstGlobalIndex k2).isLt
              rw [hstart2, hnOne] at hg
              omega
            · rcases hfour with ⟨hfour, hgap⟩
              rw [horder3, horder2] at hgap
              omega
          let z : Fin t := ⟨1, htTwo⟩
          have hscaleK : J.fundamentalScaleOrder k ≤
              J.UniversalNormOrder k :=
            J.fundamentalScaleOrder_le_universalNormOrder k
          have hAlpha :=
            P.two_e_lt_alphaValue_boundary_of_normScaleGap a J z (by
              change 2 * (ramificationIndex K : Int) <
                J.UniversalNormOrder k + J.UniversalNormOrder k2 -
                  2 * J.fundamentalScaleOrder k
              omega)
          exact (P.universalFirstThreeIsotropic_iff_firstTwoComponentsIsotropic
            a J htTwo hrank hrankI (by simpa only [z] using hAlpha)).2 hiso

theorem universalTheorem21Conditions_iff_sourceCase3Direct
    {t : Nat} (J : Lattice.JordanDecomposition q L (t + 1))
    (P : JordanOrderProfileWitness a.toBONG J)
    (hrank : J.componentRank 0 = 2) :
    a.UniversalTheorem21Conditions ↔
      J.UniversalNormOrder 0 = 0 ∧ J.UniversalJordanCase3Direct := by
  have horder0 : a.order 0 = J.UniversalNormOrder 0 :=
    P.order_zero_eq_firstUniversalNormOrder
  constructor
  · rintro ⟨hzero, hcases⟩
    have hnorm : J.UniversalNormOrder 0 = 0 := by
      rw [← horder0]
      exact hzero
    refine ⟨hnorm, hrank, ?_⟩
    rcases hcases with hI | hII
    · exact Or.inl ((universalCaseI_iff_sourceCase31
        J P hrank hnorm).1 hI)
    · exact Or.inr ((universalCaseII_iff_sourceCase32Direct
        J P hrank hnorm).1 hII)
  · rintro ⟨hnorm, hrank', hcases⟩
    have hzero : a.order 0 = 0 := by rw [horder0, hnorm]
    refine ⟨hzero, ?_⟩
    rcases hcases with h31 | h32
    · exact Or.inl ((universalCaseI_iff_sourceCase31
        J P hrank hnorm).2 h31)
    · exact Or.inr ((universalCaseII_iff_sourceCase32Direct
        J P hrank hnorm).2 h32)

theorem sourceSecondScaleOrder_eq_one
    {t : Nat} {J : Lattice.JordanDecomposition q L (t + 1)}
    (ht : 0 < t)
    (hrank0 : J.componentRank 0 = 1)
    (hnorm0 : J.UniversalNormOrder 0 = 0)
    (hnorm1 : J.UniversalNormOrder
      (⟨1, by omega⟩ : Fin (t + 1)) = 1) :
    J.fundamentalScaleOrder (⟨1, by omega⟩ : Fin (t + 1)) = 1 := by
  let k : Fin (t + 1) := ⟨1, by omega⟩
  change J.UniversalNormOrder k = 1 at hnorm1
  change J.fundamentalScaleOrder k = 1
  have hodd : Odd (J.componentRank 0) := by
    rw [hrank0]
    exact ⟨0, by omega⟩
  have hscale0Raw :=
    J.universalNormOrder_eq_scaleOrder_of_odd_componentRank 0 hodd
  have hscale0 : J.fundamentalScaleOrder 0 = 0 := by
    change BONG.jordanEffectiveNormOrder J 0 =
      J.fundamentalScaleOrder 0 at hscale0Raw
    change BONG.jordanEffectiveNormOrder J 0 = 0 at hnorm0
    omega
  have hstrict := J.scaleOrder_strict
    (i := (0 : Fin (t + 1))) (j := k) (by
      change 0 < k.val
      simp [k])
  have hle := J.fundamentalScaleOrder_le_universalNormOrder k
  have hnorm1Raw : BONG.jordanEffectiveNormOrder J k = 1 := hnorm1
  change J.fundamentalScaleOrder 0 < J.fundamentalScaleOrder k at hstrict
  change J.fundamentalScaleOrder k ≤
    BONG.jordanEffectiveNormOrder J k at hle
  rw [hscale0] at hstrict
  rw [hnorm1Raw] at hle
  omega

theorem sourceCase41_alphaThreeBound
    {t : Nat} {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J)
    (hfour : 1 < n) (ht : 0 < t)
    (hrank0 : J.componentRank 0 = 1)
    (hnorm0 : J.UniversalNormOrder 0 = 0)
    (hnorm1 : J.UniversalNormOrder
      (⟨1, by omega⟩ : Fin (t + 1)) = 1)
    (hrank1 : 3 ≤ J.componentRank
      (⟨1, by omega⟩ : Fin (t + 1))) :
    a.alphaValue (⟨2, by omega⟩ : Fin (n + 1)) ≤
      a.universalAlphaThreeUpperBound hfour := by
  let k : Fin (t + 1) := ⟨1, by omega⟩
  change J.UniversalNormOrder k = 1 at hnorm1
  change 3 ≤ J.componentRank k at hrank1
  have hnorm1Raw : BONG.jordanEffectiveNormOrder J k = 1 := hnorm1
  have hstart : (P.componentFirstGlobalIndex k).val = 1 := by
    simpa only [k, hrank0] using P.componentFirstGlobalIndex_one_val ht
  have hscale1 : J.fundamentalScaleOrder k = 1 := by
    exact sourceSecondScaleOrder_eq_one ht hrank0 hnorm0 hnorm1
  have horder1 : a.order (⟨1, by omega⟩ : Fin (n + 2)) = 1 := by
    exact (P.universalNormOrder_eq_order_of_componentFirst_val k
      (⟨1, by omega⟩ : Fin (n + 2)) hstart).symm.trans hnorm1
  have horder2 : a.order (⟨2, by omega⟩ : Fin (n + 2)) = 1 := by
    rw [P.order_eq_two_scale_sub_norm_of_componentLocalOne_val
      k (by omega) (⟨2, by omega⟩ : Fin (n + 2)) (by rw [hstart]),
      hscale1, hnorm1Raw]
    norm_num
  have horder3 : a.order (⟨3, by omega⟩ : Fin (n + 2)) = 1 := by
    rw [P.order_eq_norm_of_componentLocalTwo_val
      k hrank1 (⟨3, by omega⟩ : Fin (n + 2)) (by rw [hstart]), hnorm1Raw]
  have halphaOneNe : a.alphaValue (⟨1, by omega⟩ : Fin (n + 1)) ≠ 0 := by
    intro hzero
    have hgap := (a.alpha_p2 (⟨1, by omega⟩ : Fin (n + 1))).2.mp hzero
    unfold GoodBONG.orderGap at hgap
    have hcast : (⟨1, by omega⟩ : Fin (n + 1)).castSucc =
        (⟨1, by omega⟩ : Fin (n + 2)) := Fin.ext rfl
    have hsucc : (⟨1, by omega⟩ : Fin (n + 1)).succ =
        (⟨2, by omega⟩ : Fin (n + 2)) := Fin.ext rfl
    rw [hcast, hsucc, horder1, horder2] at hgap
    have he := ramificationIndex_pos (K := K)
    omega
  have halphaOneLower : (1 : ℚ) ≤
      a.alphaValue (⟨1, by omega⟩ : Fin (n + 1)) :=
    a.one_le_alphaValue_of_ne_zero _ halphaOneNe
  have hp6 := a.alpha_p6 (⟨1, by omega⟩ : Fin (n + 1))
    (by norm_num; omega) (by
      have hleft : (⟨1, by omega⟩ : Fin (n + 1)).castSucc =
          (⟨1, by omega⟩ : Fin (n + 2)) := Fin.ext rfl
      have hright : (⟨1 + 1, by omega⟩ : Fin (n + 1)).succ =
          (⟨3, by omega⟩ : Fin (n + 2)) := Fin.ext rfl
      rw [hleft, hright, horder1, horder3])
  unfold GoodBONG.universalAlphaThreeUpperBound
  rw [horder1, horder2]
  norm_num
  linarith

theorem sourceCase42_alphaThreeBound_iff
    {t : Nat} {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J)
    (hfour : 1 < n) (ht : 1 < t)
    (hrank0 : J.componentRank 0 = 1)
    (hnorm0 : J.UniversalNormOrder 0 = 0)
    (hnorm1 : J.UniversalNormOrder
      (⟨1, by omega⟩ : Fin (t + 1)) = 1)
    (hrank1 : J.componentRank
      (⟨1, by omega⟩ : Fin (t + 1)) = 2) :
    a.alphaValue (⟨2, by omega⟩ : Fin (n + 1)) ≤
        a.universalAlphaThreeUpperBound hfour ↔
      J.UniversalNormOrder (⟨2, by omega⟩ : Fin (t + 1)) ≤
        2 * (ramificationIndex K : Int) := by
  let k1 : Fin (t + 1) := ⟨1, by omega⟩
  let k2 : Fin (t + 1) := ⟨2, by omega⟩
  change J.UniversalNormOrder k1 = 1 at hnorm1
  change J.componentRank k1 = 2 at hrank1
  have hnorm1Raw : BONG.jordanEffectiveNormOrder J k1 = 1 := hnorm1
  have hstart1 : (P.componentFirstGlobalIndex k1).val = 1 := by
    simpa only [k1, hrank0] using P.componentFirstGlobalIndex_one_val (by omega)
  have hstart2 : (P.componentFirstGlobalIndex k2).val = 3 := by
    simpa only [k2, k1, hrank0, hrank1] using
      P.componentFirstGlobalIndex_two_val ht
  have hscale1 : J.fundamentalScaleOrder k1 = 1 :=
    sourceSecondScaleOrder_eq_one (by omega) hrank0 hnorm0 hnorm1
  have horder1 : a.order (⟨1, by omega⟩ : Fin (n + 2)) = 1 := by
    exact (P.universalNormOrder_eq_order_of_componentFirst_val k1
      (⟨1, by omega⟩ : Fin (n + 2)) hstart1).symm.trans hnorm1
  have horder2 : a.order (⟨2, by omega⟩ : Fin (n + 2)) = 1 := by
    rw [P.order_eq_two_scale_sub_norm_of_componentLocalOne_val
      k1 (by omega) (⟨2, by omega⟩ : Fin (n + 2)) (by rw [hstart1]),
      hscale1, hnorm1Raw]
    norm_num
  have horder3 : a.order (⟨3, by omega⟩ : Fin (n + 2)) =
      J.UniversalNormOrder k2 :=
    (P.universalNormOrder_eq_order_of_componentFirst_val k2
      (⟨3, by omega⟩ : Fin (n + 2)) hstart2).symm
  unfold GoodBONG.universalAlphaThreeUpperBound
  rw [horder1, horder2]
  norm_num
  have hgap := a.alphaValue_le_two_e_sub_one_iff_orderGap_lt_two_e
    (⟨2, by omega⟩ : Fin (n + 1))
  unfold GoodBONG.orderGap at hgap
  have hcast : (⟨2, by omega⟩ : Fin (n + 1)).castSucc =
      (⟨2, by omega⟩ : Fin (n + 2)) := Fin.ext rfl
  have hsucc : (⟨2, by omega⟩ : Fin (n + 1)).succ =
      (⟨3, by omega⟩ : Fin (n + 2)) := Fin.ext rfl
  rw [hcast, hsucc, horder2, horder3] at hgap
  have harith : J.UniversalNormOrder k2 - 1 <
        2 * (ramificationIndex K : Int) ↔
      J.UniversalNormOrder k2 ≤ 2 * (ramificationIndex K : Int) := by
    omega
  have hresult := hgap.trans harith
  simpa [k2] using hresult

theorem sourceCase431_alphaThreeBound_iff
    {t : Nat} {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J)
    (hfour : 1 < n) (ht : 1 < t)
    (hrank0 : J.componentRank 0 = 1)
    (hnorm1 : J.UniversalNormOrder
      (⟨1, by omega⟩ : Fin (t + 1)) = 1)
    (hrank1 : J.componentRank
      (⟨1, by omega⟩ : Fin (t + 1)) = 1)
    (hrank2 : 2 ≤ J.componentRank
      (⟨2, by omega⟩ : Fin (t + 1))) :
    a.alphaValue (⟨2, by omega⟩ : Fin (n + 1)) ≤
        a.universalAlphaThreeUpperBound hfour ↔
      Lattice.powerIdeal (K := K)
          (2 * (ramificationIndex K : Int) +
            J.UniversalNormOrder (⟨2, by omega⟩ : Fin (t + 1)) -
            2 * ((J.UniversalNormOrder
              (⟨2, by omega⟩ : Fin (t + 1)) - 1) / 2)) <
        J.fundamentalWeightIdeal
          (⟨2, by omega⟩ : Fin (t + 1)) := by
  let k1 : Fin (t + 1) := ⟨1, by omega⟩
  let k2 : Fin (t + 1) := ⟨2, by omega⟩
  change J.UniversalNormOrder k1 = 1 at hnorm1
  change J.componentRank k1 = 1 at hrank1
  change 2 ≤ J.componentRank k2 at hrank2
  have hstart1 : (P.componentFirstGlobalIndex k1).val = 1 := by
    simpa only [k1, hrank0] using P.componentFirstGlobalIndex_one_val (by omega)
  have hstart2 : (P.componentFirstGlobalIndex k2).val = 2 := by
    simpa only [k2, k1, hrank0, hrank1] using
      P.componentFirstGlobalIndex_two_val ht
  have horder1 : a.order (⟨1, by omega⟩ : Fin (n + 2)) = 1 := by
    exact (P.universalNormOrder_eq_order_of_componentFirst_val k1
      (⟨1, by omega⟩ : Fin (n + 2)) hstart1).symm.trans hnorm1
  have horder2 : a.order (⟨2, by omega⟩ : Fin (n + 2)) =
      J.UniversalNormOrder k2 :=
    (P.universalNormOrder_eq_order_of_componentFirst_val k2
      (⟨2, by omega⟩ : Fin (n + 2)) hstart2).symm
  have hweightRaw :=
    P.componentStart_fundamentalWeightOrder_eq_order_add_alpha
      k2 hrank2 (by rw [hstart2]; omega)
  dsimp only at hweightRaw
  have halphaIndex :
      (⟨(P.componentFirstGlobalIndex k2).val, by omega⟩ : Fin (n + 1)) =
        (⟨2, by omega⟩ : Fin (n + 1)) := Fin.ext hstart2
  rw [halphaIndex] at hweightRaw
  change (J.fundamentalWeightOrder k2 : ℚ) =
    (a.order (⟨2, by omega⟩ : Fin (n + 2)) : ℚ) +
      a.alphaValue (⟨2, by omega⟩ : Fin (n + 1)) at hweightRaw
  rw [horder2] at hweightRaw
  have halphaInteger : IsRationalInteger
      (a.alphaValue (⟨2, by omega⟩ : Fin (n + 1))) := by
    refine ⟨J.fundamentalWeightOrder k2 - J.UniversalNormOrder k2, ?_⟩
    push_cast
    linarith
  have harith := BONG.alphaUpperBound_iff_weightOrder_lt_shift
    (ramificationIndex K : Int) (J.UniversalNormOrder k2) 1
    (J.fundamentalWeightOrder k2)
    (a.alphaValue (⟨2, by omega⟩ : Fin (n + 1)))
    hweightRaw halphaInteger
  unfold GoodBONG.universalAlphaThreeUpperBound
  rw [horder1, horder2]
  unfold Lattice.JordanDecomposition.fundamentalWeightOrder at harith
  change _ ↔ Lattice.powerIdeal (K := K) _ < _
  rw [Lattice.JordanDecomposition.fundamentalWeightIdeal,
    Lattice.weightIdeal_eq_powerIdeal, Lattice.powerIdeal_lt_iff]
  norm_num at harith ⊢
  simpa only [k2] using harith

theorem boundaryIndex_two_val_of_firstThreeRanks
    {t : Nat} {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (ht : 2 < t)
    (hrank0 : J.componentRank 0 = 1)
    (hrank1 : J.componentRank
      (⟨1, by omega⟩ : Fin (t + 1)) = 1)
    (hrank2 : J.componentRank
      (⟨2, by omega⟩ : Fin (t + 1)) = 1) :
    (P.boundaryIndex (⟨2, by omega⟩ : Fin t)).val = 2 := by
  let z : Fin t := ⟨2, by omega⟩
  let k0 : Fin (t + 1) := ⟨0, by omega⟩
  let k1 : Fin (t + 1) := ⟨1, by omega⟩
  let k2 : Fin (t + 1) := ⟨2, by omega⟩
  have hIio :
      Finset.Iio (Lattice.JordanDecomposition.boundaryRightIndex z) =
        {k0, k1, k2} := by
    ext k
    simp only [Finset.mem_Iio, Finset.mem_insert, Finset.mem_singleton,
      Fin.ext_iff]
    change k.val < 3 ↔
      k.val = k0.val ∨ k.val = k1.val ∨ k.val = k2.val
    simp only [k0, k1, k2]
    omega
  have hb := P.boundaryIndex_succ_val_eq_componentRankPrefix z
  change (P.boundaryIndex z).val + 1 =
    ∑ k ∈ Finset.Iio
      (Lattice.JordanDecomposition.boundaryRightIndex z), J.componentRank k at hb
  rw [hIio] at hb
  have hk0 : k0 = (0 : Fin (t + 1)) := Fin.ext rfl
  have hk1 : k1 = (⟨1, by omega⟩ : Fin (t + 1)) := Fin.ext rfl
  have hk2 : k2 = (⟨2, by omega⟩ : Fin (t + 1)) := Fin.ext rfl
  have hk0Not : k0 ∉ ({k1, k2} : Finset (Fin (t + 1))) := by
    simp [k0, k1, k2]
  have hk1Not : k1 ∉ ({k2} : Finset (Fin (t + 1))) := by
    simp [k1, k2]
  rw [Finset.sum_insert hk0Not, Finset.sum_insert hk1Not,
    Finset.sum_singleton] at hb
  rw [hk0, hk1, hk2, hrank0, hrank1, hrank2] at hb
  simpa only [z] using (show (P.boundaryIndex z).val = 2 by omega)

theorem sourceCase432_alphaThreeBound_iff
    {t : Nat} {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J)
    (hfour : 1 < n) (ht : 2 < t)
    (hrank0 : J.componentRank 0 = 1)
    (hnorm0 : J.UniversalNormOrder 0 = 0)
    (hnorm1 : J.UniversalNormOrder
      (⟨1, by omega⟩ : Fin (t + 1)) = 1)
    (hrank1 : J.componentRank
      (⟨1, by omega⟩ : Fin (t + 1)) = 1)
    (hrank2 : J.componentRank
      (⟨2, by omega⟩ : Fin (t + 1)) = 1) :
    a.alphaValue (⟨2, by omega⟩ : Fin (n + 1)) ≤
        a.universalAlphaThreeUpperBound hfour ↔
      Lattice.powerIdeal (K := K)
          (2 * (ramificationIndex K : Int) -
            2 * ((J.UniversalNormOrder
              (⟨2, by omega⟩ : Fin (t + 1)) - 1) / 2)) <
        J.fundamentalIdeal (⟨2, by omega⟩ : Fin t) := by
  let k1 : Fin (t + 1) := ⟨1, by omega⟩
  let k2 : Fin (t + 1) := ⟨2, by omega⟩
  let z : Fin t := ⟨2, by omega⟩
  let i : Fin (n + 1) := ⟨2, by omega⟩
  change J.UniversalNormOrder k1 = 1 at hnorm1
  change J.componentRank k1 = 1 at hrank1
  change J.componentRank k2 = 1 at hrank2
  have hstart1 : (P.componentFirstGlobalIndex k1).val = 1 := by
    simpa only [k1, hrank0] using P.componentFirstGlobalIndex_one_val (by omega)
  have hstart2 : (P.componentFirstGlobalIndex k2).val = 2 := by
    simpa only [k2, k1, hrank0, hrank1] using
      P.componentFirstGlobalIndex_two_val (by omega)
  have horder1 : a.order (⟨1, by omega⟩ : Fin (n + 2)) = 1 := by
    exact (P.universalNormOrder_eq_order_of_componentFirst_val k1
      (⟨1, by omega⟩ : Fin (n + 2)) hstart1).symm.trans hnorm1
  have horder2 : a.order (⟨2, by omega⟩ : Fin (n + 2)) =
      J.UniversalNormOrder k2 :=
    (P.universalNormOrder_eq_order_of_componentFirst_val k2
      (⟨2, by omega⟩ : Fin (n + 2)) hstart2).symm
  have hscale1 : J.fundamentalScaleOrder k1 = 1 :=
    sourceSecondScaleOrder_eq_one (by omega) hrank0 hnorm0 hnorm1
  have hstrict := J.scaleOrder_strict
    (i := k1) (j := k2) (by
      change k1.val < k2.val
      simp [k1, k2])
  change J.fundamentalScaleOrder k1 <
    J.fundamentalScaleOrder k2 at hstrict
  have hscale2Le := J.fundamentalScaleOrder_le_universalNormOrder k2
  change J.fundamentalScaleOrder k2 ≤
    BONG.jordanEffectiveNormOrder J k2 at hscale2Le
  have hu2 : 2 ≤ J.UniversalNormOrder k2 := by
    have hu2Raw : 2 ≤ BONG.jordanEffectiveNormOrder J k2 := by
      rw [hscale1] at hstrict
      omega
    exact hu2Raw
  let B : Int := 2 * (ramificationIndex K : Int) -
    2 * ((J.UniversalNormOrder k2 - 1) / 2)
  have hB : B ≤ 2 * (ramificationIndex K : Int) := by
    dsimp only [B]
    omega
  have hboundaryVal : (P.boundaryIndex z).val = 2 := by
    simpa only [z] using
      boundaryIndex_two_val_of_firstThreeRanks P ht hrank0 hrank1 hrank2
  have hboundary : P.boundaryIndex z = i := Fin.ext hboundaryVal
  have htranslate := P.alphaUpperBound_iff_powerIdeal_lt_fundamentalIdeal
    z i hboundary B hB
  unfold GoodBONG.universalAlphaThreeUpperBound
  rw [horder1, horder2]
  have hupperEq :
      2 * ((ramificationIndex K : ℚ) -
          (((J.UniversalNormOrder k2 - 1) / 2 : Int) : ℚ)) - 1 =
        ((B - 1 : Int) : ℚ) := by
    dsimp only [B]
    push_cast
    ring
  rw [hupperEq]
  simpa only [z, i, k2, B] using htranslate

theorem universalTheorem21Conditions_iff_sourceCase4
    {t : Nat} (J : Lattice.JordanDecomposition q L (t + 1))
    (P : JordanOrderProfileWitness a.toBONG J)
    (hrank : J.componentRank 0 = 1) :
    a.UniversalTheorem21Conditions ↔
      J.UniversalNormOrder 0 = 0 ∧ J.UniversalJordanCase4 := by
  have hsum := P.sum_componentRank_eq_length
  change (∑ k, J.componentRank k) = n + 2 at hsum
  have horder0eq : a.order 0 = J.UniversalNormOrder 0 :=
    P.order_zero_eq_firstUniversalNormOrder
  constructor
  · rintro ⟨hzero, hcases⟩
    have hnorm : J.UniversalNormOrder 0 = 0 := by
      rw [← horder0eq]
      exact hzero
    have hnormRaw : BONG.jordanEffectiveNormOrder J 0 = 0 := hnorm
    have ht : 0 < t := by
      apply P.componentTail_pos_of_firstRank_lt_length
      rw [hrank]
      omega
    let k1 : Fin (t + 1) := ⟨1, by omega⟩
    have hstart1 : (P.componentFirstGlobalIndex k1).val = 1 := by
      simpa only [k1, hrank] using P.componentFirstGlobalIndex_one_val ht
    have horder1 : a.order (⟨1, by omega⟩ : Fin (n + 2)) =
        J.UniversalNormOrder k1 :=
      (P.universalNormOrder_eq_order_of_componentFirst_val k1
        (⟨1, by omega⟩ : Fin (n + 2)) hstart1).symm
    have hodd0 : Odd (J.componentRank 0) := by
      rw [hrank]
      exact ⟨0, by omega⟩
    have hscale0Raw :=
      J.universalNormOrder_eq_scaleOrder_of_odd_componentRank 0 hodd0
    have hscale0 : J.fundamentalScaleOrder 0 = 0 := by
      change BONG.jordanEffectiveNormOrder J 0 =
        J.fundamentalScaleOrder 0 at hscale0Raw
      omega
    have hstrict := J.scaleOrder_strict
      (i := (0 : Fin (t + 1))) (j := k1) (by
        change 0 < k1.val
        simp [k1])
    change J.fundamentalScaleOrder 0 <
      J.fundamentalScaleOrder k1 at hstrict
    have hscale1Le := J.fundamentalScaleOrder_le_universalNormOrder k1
    change J.fundamentalScaleOrder k1 ≤
      BONG.jordanEffectiveNormOrder J k1 at hscale1Le
    have huPos : 0 < J.UniversalNormOrder k1 := by
      have huPosRaw : 0 < BONG.jordanEffectiveNormOrder J k1 := by
        rw [hscale0] at hstrict
        omega
      exact huPosRaw
    have hII : a.UniversalCaseII := by
      rcases hcases with hI | hII
      · have hgap := (a.alpha_p2 (0 : Fin (n + 1))).2.mp hI.alphaOne
        unfold GoodBONG.orderGap at hgap
        have hzeroCast : a.order (Fin.castSucc (0 : Fin (n + 1))) = 0 := by
          simpa using hzero
        have honeIndex : Fin.succ (0 : Fin (n + 1)) =
            (⟨1, by omega⟩ : Fin (n + 2)) := Fin.ext rfl
        rw [hzeroCast, honeIndex, horder1] at hgap
        have he := ramificationIndex_pos (K := K)
        omega
      · exact hII
    have huOne : J.UniversalNormOrder k1 = 1 := by
      have hconsequences :=
        a.alphaValue_eq_one_consequences (0 : Fin (n + 1)) hII.alphaOne
      have hgapUpper := hconsequences.1.2
      unfold GoodBONG.orderGap at hgapUpper
      have hzeroCast : a.order (Fin.castSucc (0 : Fin (n + 1))) = 0 := by
        simpa using hzero
      have honeIndex : Fin.succ (0 : Fin (n + 1)) =
          (⟨1, by omega⟩ : Fin (n + 2)) := Fin.ext rfl
      rw [hzeroCast, honeIndex, horder1] at hgapUpper
      omega
    obtain ⟨hfour, halpha⟩ := hII.alphaThreeBound (Or.inl (by
      rw [horder1, huOne]))
    refine ⟨hnorm, hrank, ⟨k1, rfl, huOne⟩, ?_, ?_⟩
    · rw [← a.toBONG.length_eq_finrank]
      omega
    · have hrank1Pos : 0 < J.componentRank k1 := J.component_finrank_pos k1
      by_cases hrankThree : 3 ≤ J.componentRank k1
      · left
        exact ⟨k1, rfl, hrankThree⟩
      · by_cases hrankTwo : J.componentRank k1 = 2
        · have htTwo : 1 < t := by
            apply P.one_lt_componentTail_of_firstTwoRanks_lt_length ht
            rw [hrank, hrankTwo]
            omega
          let k2 : Fin (t + 1) := ⟨2, by omega⟩
          have hu2 := (sourceCase42_alphaThreeBound_iff P
            hfour htTwo hrank hnorm huOne hrankTwo).1 halpha
          right
          left
          exact ⟨k1, rfl, hrankTwo, k2, rfl, hu2⟩
        · have hrankOne : J.componentRank k1 = 1 := by omega
          have htTwo : 1 < t := by
            apply P.one_lt_componentTail_of_firstTwoRanks_lt_length ht
            rw [hrank, hrankOne]
            omega
          let k2 : Fin (t + 1) := ⟨2, by omega⟩
          have hrank2Pos : 0 < J.componentRank k2 := J.component_finrank_pos k2
          by_cases hrank2Two : 2 ≤ J.componentRank k2
          · have hideal := (sourceCase431_alphaThreeBound_iff P
              hfour htTwo hrank huOne hrankOne hrank2Two).1 halpha
            right
            right
            left
            exact ⟨k1, rfl, hrankOne, k2, rfl, hrank2Two, hideal⟩
          · have hrank2One : J.componentRank k2 = 1 := by omega
            have htThree : 2 < t := by
              by_contra hnot
              have htEq : t = 2 := by omega
              subst t
              have hsum' := hsum
              rw [Fin.sum_univ_three, hrank] at hsum'
              change J.componentRank (1 : Fin 3) = 1 at hrankOne
              change J.componentRank (2 : Fin 3) = 1 at hrank2One
              rw [hrankOne, hrank2One] at hsum'
              omega
            let z : Fin t := ⟨2, by omega⟩
            have hideal := (sourceCase432_alphaThreeBound_iff P
              hfour htThree hrank hnorm huOne hrankOne hrank2One).1 halpha
            right
            right
            right
            exact ⟨k1, rfl, hrankOne, k2, rfl, hrank2One, z, rfl, hideal⟩
  · rintro ⟨hnorm, hrank', huWitness, hfinrank, hcases⟩
    have hnormRaw : BONG.jordanEffectiveNormOrder J 0 = 0 := hnorm
    rcases huWitness with ⟨i, hi, hui⟩
    have ht : 0 < t := by omega
    let k1 : Fin (t + 1) := ⟨1, by omega⟩
    have hik : i = k1 := Fin.ext hi
    rw [hik] at hui
    have hstart1 : (P.componentFirstGlobalIndex k1).val = 1 := by
      simpa only [k1, hrank] using P.componentFirstGlobalIndex_one_val ht
    have horder0 : a.order 0 = 0 := by rw [horder0eq, hnorm]
    have huiRaw : BONG.jordanEffectiveNormOrder J k1 = 1 := hui
    have horder1 : a.order (⟨1, by omega⟩ : Fin (n + 2)) = 1 := by
      exact (P.universalNormOrder_eq_order_of_componentFirst_val k1
        (⟨1, by omega⟩ : Fin (n + 2)) hstart1).symm.trans huiRaw
    have halpha : a.alphaValue 0 = 1 := by
      have hgap : a.orderGap (0 : Fin (n + 1)) = 1 := by
        unfold GoodBONG.orderGap
        have hzeroCast : a.order (Fin.castSucc (0 : Fin (n + 1))) = 0 := by
          simpa using horder0
        have honeIndex : Fin.succ (0 : Fin (n + 1)) =
            (⟨1, by omega⟩ : Fin (n + 2)) := Fin.ext rfl
        rw [hzeroCast, honeIndex, horder1]
        norm_num
      have hgapLe : a.orderGap (0 : Fin (n + 1)) ≤
          2 * (ramificationIndex K : Int) := by
        rw [hgap]
        have he := ramificationIndex_pos (K := K)
        omega
      have hodd : Odd (a.orderGap (0 : Fin (n + 1))) := by
        rw [hgap]
        exact ⟨0, by omega⟩
      have hEq := (a.alpha_p3 (0 : Fin (n + 1)) hgapLe).2.mpr
        (Or.inr hodd)
      rw [hgap] at hEq
      exact_mod_cast hEq
    have hnTwo : 1 < n := by
      rw [← a.toBONG.length_eq_finrank] at hfinrank
      omega
    refine ⟨horder0, Or.inr ?_⟩
    refine
      { rankAtLeastThree := by omega
        alphaOne := halpha
        alphaThreeBound := ?_
        ternaryBoundary := ?_ }
    · intro hbranch
      rcases hcases with h41 | h42 | h431 | h432
      · rcases h41 with ⟨j, hj, hrank1⟩
        have hjk : j = k1 := Fin.ext hj
        rw [hjk] at hrank1
        exact ⟨hnTwo, sourceCase41_alphaThreeBound P
          hnTwo ht hrank hnorm hui hrank1⟩
      · rcases h42 with ⟨j, hj, hrank1, k, hk, huk⟩
        have hjk : j = k1 := Fin.ext hj
        rw [hjk] at hrank1
        have htTwo : 1 < t := by omega
        let k2 : Fin (t + 1) := ⟨2, by omega⟩
        have hkk : k = k2 := Fin.ext hk
        rw [hkk] at huk
        exact ⟨hnTwo, (sourceCase42_alphaThreeBound_iff P
          hnTwo htTwo hrank hnorm hui hrank1).2 huk⟩
      · rcases h431 with ⟨j, hj, hrank1, k, hk, hrank2, hideal⟩
        have hjk : j = k1 := Fin.ext hj
        rw [hjk] at hrank1
        have htTwo : 1 < t := by omega
        let k2 : Fin (t + 1) := ⟨2, by omega⟩
        have hkk : k = k2 := Fin.ext hk
        rw [hkk] at hrank2 hideal
        exact ⟨hnTwo, (sourceCase431_alphaThreeBound_iff P
          hnTwo htTwo hrank hui hrank1 hrank2).2 hideal⟩
      · rcases h432 with ⟨j, hj, hrank1, k, hk, hrank2, z, hz, hideal⟩
        have hjk : j = k1 := Fin.ext hj
        rw [hjk] at hrank1
        have htThree : 2 < t := by omega
        let k2 : Fin (t + 1) := ⟨2, by omega⟩
        have hkk : k = k2 := Fin.ext hk
        rw [hkk] at hrank2 hideal
        have hzz : z = (⟨2, by omega⟩ : Fin t) := Fin.ext hz
        rw [hzz] at hideal
        exact ⟨hnTwo, (sourceCase432_alphaThreeBound_iff P
          hnTwo htThree hrank hnorm hui hrank1 hrank2).2 hideal⟩
    · intro hsecond hthird htrigger
      rw [horder1] at hsecond
      omega

theorem universalTheorem21Conditions_iff_sourceDirectConditions
    {t : Nat} (J : Lattice.JordanDecomposition q L (t + 1)) :
    a.UniversalTheorem21Conditions ↔
      J.UniversalTheorem31DirectConditions := by
  let P : JordanOrderProfileWitness a.toBONG J :=
    Classical.choice (a.toBONG.beliLemma47_profile a.good J)
  have hrankPos : 0 < J.componentRank 0 := J.component_finrank_pos 0
  have hfinrank : 2 ≤ finrank K V := by
    rw [← a.toBONG.length_eq_finrank]
    omega
  constructor
  · intro h21
    by_cases hfour : 4 ≤ J.componentRank 0
    · obtain ⟨hnorm, hcase⟩ :=
        (universalTheorem21Conditions_iff_sourceCase1
          J P hfour).1 h21
      exact ⟨hfinrank, hnorm, Or.inl hcase⟩
    · by_cases hthree : J.componentRank 0 = 3
      · obtain ⟨hnorm, hcase⟩ :=
          (universalTheorem21Conditions_iff_sourceCase2
            J P hthree).1 h21
        exact ⟨hfinrank, hnorm, Or.inr (Or.inl hcase)⟩
      · by_cases htwo : J.componentRank 0 = 2
        · obtain ⟨hnorm, hcase⟩ :=
            (universalTheorem21Conditions_iff_sourceCase3Direct
              J P htwo).1 h21
          exact ⟨hfinrank, hnorm, Or.inr (Or.inr (Or.inl hcase))⟩
        · have hone : J.componentRank 0 = 1 := by omega
          obtain ⟨hnorm, hcase⟩ :=
            (universalTheorem21Conditions_iff_sourceCase4
              J P hone).1 h21
          exact ⟨hfinrank, hnorm, Or.inr (Or.inr (Or.inr hcase))⟩
  · rintro ⟨hfin, hnorm, hcases⟩
    rcases hcases with hcase1 | hcase2 | hcase3 | hcase4
    · exact (universalTheorem21Conditions_iff_sourceCase1
        J P hcase1.1).2 ⟨hnorm, hcase1⟩
    · exact (universalTheorem21Conditions_iff_sourceCase2
        J P hcase2.1).2 ⟨hnorm, hcase2⟩
    · exact (universalTheorem21Conditions_iff_sourceCase3Direct
        J P hcase3.1).2 ⟨hnorm, hcase3⟩
    · exact (universalTheorem21Conditions_iff_sourceCase4
        J P hcase4.1).2 ⟨hnorm, hcase4⟩

end BONG.JordanOrderProfileWitness

/-- Line universality forces dimension at least two over a dyadic local
field: in dimension one the represented square classes form a singleton. -/
theorem Lattice.IsUniversal.two_le_finrank
    (h : Lattice.IsUniversal q L) : 2 ≤ finrank K V := by
  letI : FiniteDimensional K V :=
    L.ambientBasis.finiteDimensional_of_finite
  have hline : q.IsLineUniversal := h.isLineUniversal
  have hone : 1 ≤ finrank K V := by
    rcases hline (1 : Kˣ) with ⟨f⟩
    simpa using
      f.toLinearMap.finrank_le_finrank_of_injective f.injective
  by_contra hnotTwo
  have hrank : finrank K V = 1 := by omega
  let e : Fin 1 ≃ Fin (finrank K V) := finCongr hrank.symm
  let c : Kˣ := q.diagonalUnits (e 0)
  obtain ⟨A, hnotSquare⟩ := Bong.exists_nonsquare_multiplier c
  have hscaled : q.Represents (QuadraticSpace.scaledLine A) :=
    (QuadraticSpace.represents_rescaleLine_iff_scaledLine q A).1 (hline A)
  let targetIso := q.diagonalizationIsometry.trans
    (QuadraticSpace.finiteDiagonalReindexIsometry
      (fun i ↦ (q.diagonalUnits i : K))
      (fun i ↦ Units.ne_zero (q.diagonalUnits i)) e)
  have hfinite :
      (QuadraticSpace.finiteDiagonal (fun i : Fin 1 ↦
          (q.diagonalUnits (e i) : K))
        (fun i ↦ Units.ne_zero (q.diagonalUnits (e i)))).Represents
        (QuadraticSpace.finiteDiagonal (fun _ : Fin 1 ↦ (A : K))
          (fun _ ↦ Units.ne_zero A)) :=
    (QuadraticSpace.represents_iff_of_isometries
      (QuadraticSpace.scaledLineDiagonalizationIsometry A) targetIso).1 hscaled
  have hdiag : DiagonalRepresents (fun _ : Fin 1 ↦ (A : K))
      (fun i : Fin 1 ↦ (q.diagonalUnits (e i) : K)) :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      (fun _ : Fin 1 ↦ A) (fun i : Fin 1 ↦ q.diagonalUnits (e i))).1 hfinite
  rcases DiagonalRepresents.exists_prod_eq_mul_square_of_sameRank hdiag with
    ⟨p, hp⟩
  have hpOne : (A : K) = (c : K) * (p : K) ^ 2 := by
    simpa only [Fin.prod_univ_one, c] using hp
  apply hnotSquare
  refine ⟨c * p, ?_⟩
  apply Units.ext
  simp only [Units.val_mul]
  rw [hpOne]
  ring

namespace BONG.JordanOrderProfileWitness

/-- Beli's Theorem 3.1 in the normalization obtained by direct substitution
into Theorem 2.1, for an arbitrary prescribed Jordan decomposition. -/
theorem isUniversal_iff_universalTheorem31DirectConditions
    {t : Nat} (J : Lattice.JordanDecomposition q L (t + 1)) :
    Lattice.IsUniversal q L ↔
      J.UniversalTheorem31DirectConditions := by
  constructor
  · intro hUniversal
    have hfinrank : 2 ≤ finrank K V := hUniversal.two_le_finrank
    obtain ⟨n, hn⟩ : ∃ n, finrank K V = n + 2 :=
      ⟨finrank K V - 2, by omega⟩
    let raw : GoodBONG q L (finrank K V) :=
      Classical.choice (Bong.exists_good_bong q L)
    let a : GoodBONG q L (n + 2) := raw.castLength hn
    exact
      (universalTheorem21Conditions_iff_sourceDirectConditions
        (a := a) J).1
        ((a.isUniversal_iff_universalTheorem21Conditions
          hUniversal.isIntegral).1 hUniversal)
  · intro hDirect
    obtain ⟨n, hn⟩ : ∃ n, finrank K V = n + 2 := by
      have hfinrank := hDirect.1
      exact ⟨finrank K V - 2, by omega⟩
    let raw : GoodBONG q L (finrank K V) :=
      Classical.choice (Bong.exists_good_bong q L)
    let a : GoodBONG q L (n + 2) := raw.castLength hn
    have h21 : a.UniversalTheorem21Conditions :=
      (universalTheorem21Conditions_iff_sourceDirectConditions
        (a := a) J).2 hDirect
    exact
      (a.isUniversal_iff_universalTheorem21Conditions h21.isIntegral).2 h21

/-- Under the additional zero-scale normalization, the direct criterion is
literally the criterion printed in Theorem 3.1. -/
theorem isUniversal_iff_universalTheorem31Conditions_of_firstScaleOrder_eq_zero
    {t : Nat} (J : Lattice.JordanDecomposition q L (t + 1))
    (hscale : J.fundamentalScaleOrder 0 = 0) :
    Lattice.IsUniversal q L ↔ J.UniversalTheorem31Conditions :=
  (isUniversal_iff_universalTheorem31DirectConditions J).trans
    (J.universalTheorem31DirectConditions_iff_of_firstScaleOrder_eq_zero hscale)

end BONG.JordanOrderProfileWitness

namespace Lattice.JordanDecomposition

/-- Public arbitrary-Jordan form of Beli's Theorem 3.1, using the two
exponents obtained by direct substitution into Theorem 2.1. -/
theorem isUniversal_iff_universalTheorem31DirectConditions
    {t : Nat} (J : JordanDecomposition q L (t + 1)) :
    Lattice.IsUniversal q L ↔ J.UniversalTheorem31DirectConditions :=
  BONG.JordanOrderProfileWitness.isUniversal_iff_universalTheorem31DirectConditions J

/-- Public literal-paper form in the normalization where the first
fundamental scale has order zero. -/
theorem isUniversal_iff_universalTheorem31Conditions_of_firstScaleOrder_eq_zero
    {t : Nat} (J : JordanDecomposition q L (t + 1))
    (hscale : J.fundamentalScaleOrder 0 = 0) :
    Lattice.IsUniversal q L ↔ J.UniversalTheorem31Conditions :=
  BONG.JordanOrderProfileWitness.isUniversal_iff_universalTheorem31Conditions_of_firstScaleOrder_eq_zero
    J hscale

end Lattice.JordanDecomposition

end Bong
