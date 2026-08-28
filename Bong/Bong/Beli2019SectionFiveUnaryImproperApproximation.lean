/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveUnaryImproperAlpha

/-!
# Beli (2019), Section 5: approximations in the improper unary interval

This file completes case 4 following Lemma 5.13.  The original unary norm
generator is transported through the enlarged block in the ordinary field
square-class group.  Internal boundaries use the alternating seeds of
Lemma 3.2.  At the right endpoint the source approximation is supplied by
Corollary 3.3(ii).  Both arguments resolve the possible equal-scale merge on
the large side and the possible collision on the small side.

Together with the alpha-cap calculation in
`Beli2019SectionFiveUnaryImproperAlpha`, the final theorem supplies the
pointwise Section 5 defect certificate for the whole exceptional interval.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {x : V}

theorem enlargedDeterminant_squareClass_eq_scaleGenerator
    (D : Lattice.Beli2019Lemma51BlockData q L x)
    (hfin : finrank K D.component.carrier = 1) :
    squareClass K
        (Lattice.determinantUnit D.component.space D.enlargedLattice) =
      squareClass K D.scaleGenerator := by
  cases D with
  | unary z hz hcongruent hanisotropic hpairing =>
      let b := Lattice.unarySpanBasis (K := K) z hanisotropic.ne_zero
      let c := Lattice.uniformizerInvScaleBasisAt b 0
      have hhead :
          (Lattice.Beli2019Lemma51BlockData.carrierRepresentative
              (.unary z hz hcongruent hanisotropic hpairing) : K ∙ z) = b 0 := by
        apply Subtype.ext
        exact (Lattice.coe_unarySpanBasis (K := K) z
          hanisotropic.ne_zero 0).symm
      have hlattice :
          (Lattice.Beli2019Lemma51BlockData.unary z hz hcongruent
              hanisotropic hpairing).enlargedLattice =
            Lattice.basisLattice c := by
        unfold Lattice.Beli2019Lemma51BlockData.enlargedLattice
        unfold Lattice.Beli2019Lemma51BlockData.component
        rw [hhead]
        change Lattice.adjoinVector (Lattice.basisLattice b)
            ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • b 0) =
          Lattice.basisLattice c
        rw [Lattice.adjoin_basisLattice_uniformizerInv_eq]
      rw [hlattice]
      change squareClass K
          (Lattice.determinantUnit
            (q.restrict (K ∙ z)
              (Lattice.unarySpan_restrict_nondegenerate hanisotropic))
            (Lattice.basisLattice c)) =
        squareClass K (Units.mk0 (q.quadratic z)
          (show q.quadratic z ≠ 0 from hanisotropic))
      have hgram :
          Lattice.gramUnitOfBasis
              (q.restrict (K ∙ z)
                (Lattice.unarySpan_restrict_nondegenerate hanisotropic)) c =
            (uniformizerUnit K)⁻¹ ^ 2 *
              Units.mk0 (q.quadratic z)
                (show q.quadratic z ≠ 0 from hanisotropic) := by
        apply Units.ext
        change (LinearMap.BilinForm.toMatrix c
            (q.restrict (K ∙ z)
              (Lattice.unarySpan_restrict_nondegenerate hanisotropic)).bilin).det = _
        rw [Matrix.det_fin_one]
        simp only [LinearMap.BilinForm.toMatrix_apply]
        rw [Lattice.uniformizerInvScaleBasisAt_apply_same]
        change q.bilin
            ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • (b 0 : K ∙ z) : K ∙ z)
            ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • (b 0 : K ∙ z) : K ∙ z) = _
        change q.bilin
            ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • ((b 0 : K ∙ z) : V))
            ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • ((b 0 : K ∙ z) : V)) = _
        rw [Lattice.coe_unarySpanBasis (K := K) z hanisotropic.ne_zero]
        change q.quadratic
            ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • z) = _
        rw [q.quadratic_smul]
        rfl
      have hunit :=
        Lattice.unitSquareClass_gramUnitOfBasis_eq_determinantClass
          (q.restrict (K ∙ z)
            (Lattice.unarySpan_restrict_nondegenerate hanisotropic)) c
      have hsq := congrArg (unitSquareClassToSquareClass K) hunit
      change squareClass K
          (Lattice.gramUnitOfBasis
            (q.restrict (K ∙ z)
              (Lattice.unarySpan_restrict_nondegenerate hanisotropic)) c) =
        squareClass K
          (Lattice.determinantUnit
            (q.restrict (K ∙ z)
              (Lattice.unarySpan_restrict_nondegenerate hanisotropic))
            (Lattice.basisLattice c)) at hsq
      rw [← hsq, hgram]
      simpa only [mul_comm] using
        squareClass_mul_square K
          (Units.mk0 (q.quadratic z)
            (show q.quadratic z ≠ 0 from hanisotropic))
          (uniformizerUnit K)⁻¹
  | binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY =>
      have hactual : finrank K (BONG.binaryPairSpan (K := K) z y) = 2 := by
        simpa using Module.finrank_eq_card_basis
          (BONG.binaryPairBasis (K := K) z y
            (Lattice.binaryPair_linearIndependent_of_left_strict hzy hleft hright))
      change finrank K (BONG.binaryPairSpan (K := K) z y) = 1 at hfin
      omega

theorem scaleGenerator_eq_quadratic_representative_of_rank_one
    (D : Lattice.Beli2019Lemma51BlockData q L x)
    (hfin : finrank K D.component.carrier = 1) :
    (D.scaleGenerator : K) = q.quadratic D.representative := by
  cases D with
  | unary z hz hcongruent hanisotropic hpairing => rfl
  | binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY =>
      have hactual : finrank K (BONG.binaryPairSpan (K := K) z y) = 2 := by
        simpa using Module.finrank_eq_card_basis
          (BONG.binaryPairBasis (K := K) z y
            (Lattice.binaryPair_linearIndependent_of_left_strict hzy hleft hright))
      change finrank K (BONG.binaryPairSpan (K := K) z y) = 1 at hfin
      omega

namespace Lattice.Beli2019Lemma51Data

variable {M N : Lattice K V}

theorem unaryShift_common_scaleGenerator
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (heffective : D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
      ordUnit K (D.complementStrictWeak.scaleGenerator i₀) + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2)) :
    Lattice.IsNormGeneratorValue q
      (Lattice.scaleTruncation q N
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)))
      D.input.block.scaleGenerator := by
  let target := ordUnit K (D.complementStrictWeak.scaleGenerator i₀)
  let A := D.input.block.scaleGenerator
  have hselectedScale : ordUnit K A = target + 1 := by
    have hshift : ordUnit K D.input.block.enlargedScaleGenerator =
        ordUnit K D.input.block.scaleGenerator - 2 := by
      rcases D.input.block.componentRank_and_enlargedScaleOrder with
        hOne | hTwo
      · exact hOne.2
      · omega
    dsimp only [A, target]
    omega
  let z := D.input.block.representative
  have hzN : z ∈ N := D.input.block.representative_mem
  have hzTrunc : z ∈ Lattice.scaleTruncation q N target := by
    apply Lattice.mem_scaleTruncation_of_pairing_mem_powerIdeal hzN
    intro w hw
    have hpair := D.input.block.component_pairing
      D.input.block.carrierRepresentative
      D.input.block.carrierRepresentative_mem w hw
    have hpair' : q.bilin z w ∈
        Lattice.principalIdeal (K := K) (A : K) := by
      simpa only [z, A,
        Lattice.Beli2019Lemma51BlockData.coe_carrierRepresentative] using hpair
    rw [Lattice.principalIdeal_eq_powerIdeal] at hpair'
    exact ((Lattice.powerIdeal_le_iff (K := K) (ordUnit K A) target).2
      (by omega)) hpair'
  have hAvalue : (A : K) = q.quadratic z := by
    exact scaleGenerator_eq_quadratic_representative_of_rank_one D.input.block hfin
  have hgroup : (A : K) ∈
      Lattice.normGroupSet q (Lattice.scaleTruncation q N target) := by
    refine ⟨z, hzTrunc, 0, Submodule.zero_mem _, ?_⟩
    rw [add_zero]
    exact hAvalue
  have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
  let I : Fin (n + 2) := ⟨D.largeSelectedStart, by
    change D.largeSelectedStart +
        (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤
      n + 2 at hbound
    have hpos := D.complementStrictWeak.component_finrank_pos i₀
    omega⟩
  let y := D.smallWeakProfileWitness b
  have hweakRaw := D.weakUnaryShift_smallCommon_indexEquiv
    hfin i₀ hi₀ a b 0 (D.complementStrictWeak.component_finrank_pos i₀)
  have hweak : y.indexEquiv I =
      ⟨D.largeSelectedPosition,
        ⟨0, by
          rw [D.weakUnaryShift_smallComponentRank_at_largeSelected
            hfin i₀ hi₀]
          exact D.complementStrictWeak.component_finrank_pos i₀⟩⟩ := by
    change (D.smallWeakProfileWitness b).indexEquiv
      ⟨D.largeSelectedStart + 0, _⟩ = _ at hweakRaw
    simpa only [add_zero, I, y] using hweakRaw
  have hcomponent : (y.indexEquiv I).1 = D.largeSelectedPosition :=
    congrArg Sigma.fst hweak
  have hposCommon : D.largeSelectedPosition < D.smallSelectedPosition := by
    have hadj := D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
      hfin i₀ hi₀
    change D.largeSelectedPosition.val < D.smallSelectedPosition.val
    omega
  have hle : (y.indexEquiv I).1 ≤ D.smallSelectedPosition := by
    rw [hcomponent]
    exact hposCommon.le
  let R := D.smallStrictCoordinateResolution b I hle
  have hfund : R.fundamentalLattice =
      Lattice.scaleTruncation q N target := by
    rw [R.fundamentalLattice_eq_scaleTruncation]
    change Lattice.scaleTruncation q N
        (ordUnit K (D.smallAlmostJordan.scaleGenerator
          (y.indexEquiv I).1)) = _
    rw [hcomponent,
      ← D.smallCommonPosition_eq_largeSelectedPosition_of_intermediate
        hfin i₀ hi₀,
      D.smallAlmostJordan_scaleGenerator_common]
  have heffectiveSmall : D.smallAlmostJordan.effectiveNormOrderAt
      (D.smallCommonPosition i₀) target = target + 1 := by
    exact (D.unaryShift_commonEffectiveNormOrder_eq hfin i₀ hi₀).symm.trans
      heffective
  have hnormRaw := R.normIdeal_fundamentalLattice_eq_powerIdeal
  have hnorm : Lattice.normIdeal q
      (Lattice.scaleTruncation q N target) =
        Lattice.powerIdeal (K := K) (target + 1) := by
    rw [hfund] at hnormRaw
    change Lattice.normIdeal q (Lattice.scaleTruncation q N target) =
      Lattice.powerIdeal (K := K)
        (D.smallAlmostJordan.effectiveNormOrderAt
          (y.indexEquiv I).1
          (ordUnit K (D.smallAlmostJordan.scaleGenerator
            (y.indexEquiv I).1))) at hnormRaw
    rw [hcomponent,
      ← D.smallCommonPosition_eq_largeSelectedPosition_of_intermediate
        hfin i₀ hi₀,
      D.smallAlmostJordan_scaleGenerator_common,
      heffectiveSmall] at hnormRaw
    exact hnormRaw
  refine ⟨hgroup, ?_⟩
  rw [hnorm, Lattice.principalIdeal_eq_powerIdeal, hselectedScale]

/-- Before the intermediate common component, the large weak prefix is the
small weak prefix with the enlarged unary component appended, up to a unit
square. -/
theorem unaryShift_prefixDeterminant_bridge
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    ∃ s : Kˣ,
      (D.smallAlmostJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice D.largeSelectedPosition.val
          |>.refinedDeterminantUnit) *
          D.input.enlargedComponent.refinedDeterminantUnit * s ^ 2 =
        (D.largeAlmostJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice D.smallSelectedPosition.val
          |>.refinedDeterminantUnit) := by
  let P := D.largeAlmostJordan.toOrthogonalDecomposition
  let Q := D.smallAlmostJordan.toOrthogonalDecomposition
  let p := D.largeSelectedPosition
  have hadj : D.smallSelectedPosition.val = p.val + 1 := by
    exact D.smallSelectedPosition_val_eq_large_add_one_of_rank_one hfin i₀ hi₀
  have hprefixClass :
      unitSquareClass K
          ((P.prefixQuadraticSublattice p.val).refinedDeterminantUnit) =
        unitSquareClass K
          ((Q.prefixQuadraticSublattice p.val).refinedDeterminantUnit) := by
    by_cases hpzero : p.val = 0
    · have hPsub : Subsingleton
          (P.prefixQuadraticSublattice p.val).carrier := by
        rw [hpzero]
        exact Lattice.WeakJordanDecomposition.prefixCarrier_zero_subsingleton P
      have hQsub : Subsingleton
          (Q.prefixQuadraticSublattice p.val).carrier := by
        rw [hpzero]
        exact Lattice.WeakJordanDecomposition.prefixCarrier_zero_subsingleton Q
      have hPone := Lattice.determinantClass_eq_one_of_subsingleton
        (P.prefixQuadraticSublattice p.val).space
        (P.prefixQuadraticSublattice p.val).lattice hPsub
      have hQone := Lattice.determinantClass_eq_one_of_subsingleton
        (Q.prefixQuadraticSublattice p.val).space
        (Q.prefixQuadraticSublattice p.val).lattice hQsub
      change unitSquareClass K
          ((P.prefixQuadraticSublattice p.val).refinedDeterminantUnit) = 1
        at hPone
      change unitSquareClass K
          ((Q.prefixQuadraticSublattice p.val).refinedDeterminantUnit) = 1
        at hQone
      exact hPone.trans hQone.symm
    · let cut := p.val
      have hcut : cut - 1 + 1 = cut := by dsimp only [cut]; omega
      have hP : cut - 1 + 1 ≤ D.complementComponentCount + 1 := by
        rw [hcut]
        exact p.isLt.le
      have hQ : cut - 1 + 1 ≤ D.complementComponentCount + 1 := hP
      have hcomponent (z : Fin (cut - 1 + 1)) :
          P.component (P.prefixIndexEquiv (cut - 1 + 1) hP z).1 =
            Q.component (Q.prefixIndexEquiv (cut - 1 + 1) hQ z).1 := by
        let jP := (P.prefixIndexEquiv (cut - 1 + 1) hP z).1
        let jQ := (Q.prefixIndexEquiv (cut - 1 + 1) hQ z).1
        have hjPVal : jP.val = z.val :=
          P.prefixIndexEquiv_val (cut - 1 + 1) hP z
        have hjQVal : jQ.val = z.val :=
          Q.prefixIndexEquiv_val (cut - 1 + 1) hQ z
        have hjEq : jP = jQ := by
          apply Fin.ext
          rw [hjPVal, hjQVal]
        have hjBefore : jP < p := by
          change jP.val < p.val
          rw [hjPVal]
          have hz := z.isLt
          dsimp only [cut] at hz
          omega
        change D.largeAlmostJordan.component jP =
          D.smallAlmostJordan.component jQ
        rw [← hjEq]
        exact D.unaryShift_component_eq_before hfin i₀ hi₀ jP hjBefore
      let F := P.prefixComponentwiseIsometryOfDifferentCounts Q hP hQ
        (fun z ↦ by
          rw [hcomponent z]
          exact Lattice.Isometry.refl _ _)
      have hclass := Lattice.determinantClass_eq_of_isometry F
      change unitSquareClass K
          ((P.prefixQuadraticSublattice (cut - 1 + 1)).refinedDeterminantUnit) =
        unitSquareClass K
          ((Q.prefixQuadraticSublattice (cut - 1 + 1)).refinedDeterminantUnit)
        at hclass
      rw [hcut] at hclass
      simpa only [P, Q, p, cut] using hclass
  have happend := P.unitSquareClass_prefix_succ_eq_mul_component p
  rw [D.largeAlmostJordan_component_selected] at happend
  have htarget :
      unitSquareClass K
          ((Q.prefixQuadraticSublattice p.val).refinedDeterminantUnit *
            D.input.enlargedComponent.refinedDeterminantUnit) =
        unitSquareClass K
          ((P.prefixQuadraticSublattice (p.val + 1)).refinedDeterminantUnit) := by
    calc
      unitSquareClass K
          ((Q.prefixQuadraticSublattice p.val).refinedDeterminantUnit *
            D.input.enlargedComponent.refinedDeterminantUnit) =
          unitSquareClass K
              ((Q.prefixQuadraticSublattice p.val).refinedDeterminantUnit) *
            unitSquareClass K
              D.input.enlargedComponent.refinedDeterminantUnit := by
        rw [unitSquareClass_mul]
      _ = unitSquareClass K
              ((P.prefixQuadraticSublattice p.val).refinedDeterminantUnit) *
            unitSquareClass K
              D.input.enlargedComponent.refinedDeterminantUnit := by
        rw [hprefixClass]
      _ = unitSquareClass K
          ((P.prefixQuadraticSublattice p.val).refinedDeterminantUnit *
            D.input.enlargedComponent.refinedDeterminantUnit) := by
        rw [unitSquareClass_mul]
      _ = unitSquareClass K
          ((P.prefixQuadraticSublattice (p.val + 1)).refinedDeterminantUnit) := by
        exact happend.symm
  obtain ⟨s, hs⟩ :=
    BONG.GoodBONG.exists_square_mul_eq_of_unitSquareClass_eq
      ((Q.prefixQuadraticSublattice p.val).refinedDeterminantUnit *
        D.input.enlargedComponent.refinedDeterminantUnit)
      ((P.prefixQuadraticSublattice (p.val + 1)).refinedDeterminantUnit)
      htarget
  refine ⟨s, ?_⟩
  simpa only [P, Q, p, hadj] using hs

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
private theorem exists_mul_square_eq_of_squareClass_eq_local
    (a b : Kˣ) (h : squareClass K a = squareClass K b) :
    ∃ s : Kˣ, a * s ^ 2 = b := by
  change QuotientGroup.mk' (Subgroup.square Kˣ) a =
    QuotientGroup.mk' (Subgroup.square Kˣ) b at h
  rw [QuotientGroup.mk'_eq_mk'] at h
  rcases h with ⟨z, hz, haz⟩
  change IsSquare z at hz
  rcases hz with ⟨s, rfl⟩
  exact ⟨s, by simpa only [pow_two] using haz⟩

theorem unaryShift_weakPrefixDeterminant_relation
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    ∃ s : Kˣ,
      (D.largeAlmostJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice D.smallSelectedPosition.val
          |>.refinedDeterminantUnit) =
        D.input.block.scaleGenerator *
          (D.smallAlmostJordan.toOrthogonalDecomposition
            |>.prefixQuadraticSublattice D.largeSelectedPosition.val
            |>.refinedDeterminantUnit) * s ^ 2 := by
  obtain ⟨sPrefix, hsPrefix⟩ :=
    unaryShift_prefixDeterminant_bridge D hfin i₀ hi₀
  have hclass := enlargedDeterminant_squareClass_eq_scaleGenerator D.input.block hfin
  have hcomponent :
      D.input.enlargedComponent.refinedDeterminantUnit =
        Lattice.determinantUnit D.input.block.component.space
          D.input.block.enlargedLattice := by
    rfl
  obtain ⟨sBlock, hsBlock⟩ :=
    exists_mul_square_eq_of_squareClass_eq_local
      D.input.block.scaleGenerator
      D.input.enlargedComponent.refinedDeterminantUnit
      (by simpa only [hcomponent] using hclass.symm)
  refine ⟨sBlock * sPrefix, ?_⟩
  rw [mul_pow, ← hsPrefix, ← hsBlock]
  ac_rfl

theorem unaryShift_weakPrefixThroughDeterminant_relation
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    ∃ s : Kˣ,
      (D.largeAlmostJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice
            (D.smallSelectedPosition.val + 1)
          |>.refinedDeterminantUnit) =
        D.input.block.scaleGenerator *
          (D.smallAlmostJordan.toOrthogonalDecomposition
            |>.prefixQuadraticSublattice D.smallSelectedPosition.val
            |>.refinedDeterminantUnit) * s ^ 2 := by
  let P := D.largeAlmostJordan.toOrthogonalDecomposition
  let Q := D.smallAlmostJordan.toOrthogonalDecomposition
  let p := D.smallSelectedPosition
  let r := D.largeSelectedPosition
  let A := D.input.block.scaleGenerator
  obtain ⟨sPrefix, hsPrefix⟩ :=
    unaryShift_weakPrefixDeterminant_relation D hfin i₀ hi₀
  have hadj : p.val = r.val + 1 :=
    D.smallSelectedPosition_val_eq_large_add_one_of_rank_one hfin i₀ hi₀
  have hcomponent : P.component p = Q.component r := by
    change D.largeAlmostJordan.component D.smallSelectedPosition =
      D.smallAlmostJordan.component D.largeSelectedPosition
    rw [← D.largeCommonPosition_eq_smallSelectedPosition_of_intermediate
        hfin i₀ hi₀,
      D.largeAlmostJordan_component_common,
      ← D.smallCommonPosition_eq_largeSelectedPosition_of_intermediate
        hfin i₀ hi₀,
      D.smallAlmostJordan_component_common]
  have hPstepUnit := P.unitSquareClass_prefix_succ_eq_mul_component p
  have hPstepMap := congrArg (unitSquareClassToSquareClass K) hPstepUnit
  have hPstep :
      squareClass K
          ((P.prefixQuadraticSublattice (p.val + 1)).refinedDeterminantUnit) =
        squareClass K
          ((P.prefixQuadraticSublattice p.val).refinedDeterminantUnit *
            (P.component p).refinedDeterminantUnit) := by
    simpa only [unitSquareClassToSquareClass_apply] using hPstepMap
  have hQstepUnit := Q.unitSquareClass_prefix_succ_eq_mul_component r
  have hQstepMap := congrArg (unitSquareClassToSquareClass K) hQstepUnit
  have hQstep :
      squareClass K
          ((Q.prefixQuadraticSublattice (r.val + 1)).refinedDeterminantUnit) =
        squareClass K
          ((Q.prefixQuadraticSublattice r.val).refinedDeterminantUnit *
            (Q.component r).refinedDeterminantUnit) := by
    simpa only [unitSquareClassToSquareClass_apply] using hQstepMap
  have hprefixClass :
      squareClass K
          ((P.prefixQuadraticSublattice p.val).refinedDeterminantUnit) =
        squareClass K
          (A * (Q.prefixQuadraticSublattice r.val).refinedDeterminantUnit) := by
    calc
      squareClass K
          ((P.prefixQuadraticSublattice p.val).refinedDeterminantUnit) =
          squareClass K
            ((A * (Q.prefixQuadraticSublattice r.val).refinedDeterminantUnit) *
              sPrefix ^ 2) := by
        simpa only [P, Q, p, r, A] using congrArg (squareClass K) hsPrefix
      _ = squareClass K
          (A * (Q.prefixQuadraticSublattice r.val).refinedDeterminantUnit) :=
        squareClass_mul_square K _ sPrefix
  have hclass :
      squareClass K
          ((P.prefixQuadraticSublattice (p.val + 1)).refinedDeterminantUnit) =
        squareClass K
          (A * (Q.prefixQuadraticSublattice p.val).refinedDeterminantUnit) := by
    calc
      squareClass K
          ((P.prefixQuadraticSublattice (p.val + 1)).refinedDeterminantUnit) =
          squareClass K
            ((P.prefixQuadraticSublattice p.val).refinedDeterminantUnit *
              (P.component p).refinedDeterminantUnit) := hPstep
      _ = squareClass K
            ((P.prefixQuadraticSublattice p.val).refinedDeterminantUnit) *
          squareClass K ((P.component p).refinedDeterminantUnit) := rfl
      _ = squareClass K
            (A * (Q.prefixQuadraticSublattice r.val).refinedDeterminantUnit) *
          squareClass K ((Q.component r).refinedDeterminantUnit) := by
        rw [hprefixClass, hcomponent]
      _ = squareClass K A *
          squareClass K
            ((Q.prefixQuadraticSublattice r.val).refinedDeterminantUnit *
              (Q.component r).refinedDeterminantUnit) := by
        change (squareClass K A *
            squareClass K
              ((Q.prefixQuadraticSublattice r.val).refinedDeterminantUnit)) *
            squareClass K ((Q.component r).refinedDeterminantUnit) = _
        ac_rfl
      _ = squareClass K A *
          squareClass K
            ((Q.prefixQuadraticSublattice (r.val + 1)).refinedDeterminantUnit) := by
        rw [hQstep]
      _ = squareClass K
          (A * (Q.prefixQuadraticSublattice p.val).refinedDeterminantUnit) := by
        rw [hadj]
        rfl
  obtain ⟨s, hs⟩ := exists_mul_square_eq_of_squareClass_eq_local
    (A * (Q.prefixQuadraticSublattice p.val).refinedDeterminantUnit)
    ((P.prefixQuadraticSublattice (p.val + 1)).refinedDeterminantUnit)
    hclass.symm
  refine ⟨s, ?_⟩
  simpa only [P, Q, p, A] using hs.symm

theorem exists_mergeAdjacentAt_nextPrefix_mul_square
    {t : Nat} (W : Lattice.WeakJordanDecomposition q M (t + 1))
    (k p : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hkp : k < p) (hpVal : p.val = k.val + 1) :
    ∃ s : Kˣ,
      (W.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (p.val + 2)
          |>.refinedDeterminantUnit) * s ^ 2 =
        ((W.mergeAdjacentAt k heq).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (p.val + 1)
          |>.refinedDeterminantUnit) := by
  let P := (W.mergeAdjacentAt k heq).toOrthogonalDecomposition
  let Q := W.toOrthogonalDecomposition
  have hcomponent : P.component p = Q.component p.succ := by
    dsimp only [P, Q]
    rw [W.mergeAdjacentAt_component_of_ne k heq p (Fin.ne_of_gt hkp),
      Fin.succAbove_of_le_castSucc]
    exact Fin.succ_le_castSucc_iff.mpr hkp
  have hbase := W.unitSquareClass_mergeAdjacentAt_prefixThrough k heq
  have hPstep := P.unitSquareClass_prefix_succ_eq_mul_component p
  have hQstep := Q.unitSquareClass_prefix_succ_eq_mul_component p.succ
  have hclass :
      unitSquareClass K
          ((Q.prefixQuadraticSublattice (p.val + 2)).refinedDeterminantUnit) =
        unitSquareClass K
          ((P.prefixQuadraticSublattice (p.val + 1)).refinedDeterminantUnit) := by
    calc
      unitSquareClass K
          ((Q.prefixQuadraticSublattice (p.val + 2)).refinedDeterminantUnit) =
          unitSquareClass K
            ((Q.prefixQuadraticSublattice (p.val + 1)).refinedDeterminantUnit *
              (Q.component p.succ).refinedDeterminantUnit) := by
        simpa only [Fin.val_succ] using hQstep
      _ = unitSquareClass K
            ((Q.prefixQuadraticSublattice (p.val + 1)).refinedDeterminantUnit) *
          unitSquareClass K ((Q.component p.succ).refinedDeterminantUnit) :=
        by rw [unitSquareClass_mul]
      _ = unitSquareClass K
            ((P.prefixQuadraticSublattice p.val).refinedDeterminantUnit) *
          unitSquareClass K ((P.component p).refinedDeterminantUnit) := by
        rw [hcomponent]
        rw [hpVal]
        exact congrArg (fun z ↦ z *
          unitSquareClass K ((Q.component p.succ).refinedDeterminantUnit))
            hbase.symm
      _ = unitSquareClass K
          ((P.prefixQuadraticSublattice (p.val + 1)).refinedDeterminantUnit) := by
        rw [← unitSquareClass_mul]
        exact hPstep.symm
  exact BONG.GoodBONG.exists_square_mul_eq_of_unitSquareClass_eq _ _ hclass

theorem shiftedCommonApproximation
    [Beli2006AlphaLaws.{u, v} K]
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    {C : a.JordanBlockCoordinates} {E : b.JordanBlockCoordinates}
    (S : a.JordanApproximationSeeds C)
    (T : b.JordanApproximationSeeds E)
    (A : Kˣ)
    (hstart : C.start = E.start + 1)
    (hdet : ∃ s : Kˣ, S.leftDet = A * T.leftDet * s ^ 2)
    (hsourceNorm : S.normGenerator = -A)
    (htargetNorm : T.normGenerator = A)
    (i : Nat) (hleft : E.start < i)
    (hC : i < C.stop) (hE : i < E.stop) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i X ∧ b.IsPrefixApproximation i X := by
  obtain ⟨s, hs⟩ := hdet
  rcases Nat.even_or_odd (i - E.start) with heven | hodd
  · rcases heven with ⟨k, hk⟩
    have hkpos : 0 < k := by omega
    obtain ⟨ell, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    let X : Kˣ := (-1 : Kˣ) ^ (ell + 1) * T.leftDet
    have htarget := T.evenApproximation (ell + 1) (by omega)
    have hsource := S.oddApproximation ell (by omega)
    have hiTarget : i = E.start + 2 * (ell + 1) := by omega
    have hiSource : i = C.start + 1 + 2 * ell := by omega
    have hmul :
        (-1 : Kˣ) ^ ell * (S.normGenerator * S.leftDet) =
          X * (A * s) ^ 2 := by
      have hneg : (-A : Kˣ) = (-1 : Kˣ) * A := by simp
      have hsign : (-1 : Kˣ) ^ (ell + 1) =
          (-1 : Kˣ) ^ ell * (-1 : Kˣ) := by
        exact pow_succ (-1 : Kˣ) ell
      rw [hsourceNorm, hneg, hs]
      dsimp only [X]
      rw [hsign]
      simp only [pow_two]
      ac_rfl
    refine ⟨X, ?_, ?_⟩
    · rw [← hiSource, hmul] at hsource
      exact (a.isPrefixApproximation_mul_square_iff i X (A * s)).mp hsource
    · simpa only [X, ← hiTarget] using htarget
  · rcases hodd with ⟨k, hk⟩
    let X : Kˣ := (-1 : Kˣ) ^ k * (A * T.leftDet)
    have hsource := S.evenApproximation k (by omega)
    have htarget := T.oddApproximation k (by omega)
    have hiTarget : i = E.start + 1 + 2 * k := by omega
    have hiSource : i = C.start + 2 * k := by omega
    have hmul :
        (-1 : Kˣ) ^ k * S.leftDet = X * s ^ 2 := by
      rw [hs]
      simp only [X]
      ac_rfl
    refine ⟨X, ?_, ?_⟩
    · rw [← hiSource, hmul] at hsource
      exact (a.isPrefixApproximation_mul_square_iff i X s).mp hsource
    · rw [htargetNorm] at htarget
      simpa only [X, ← hiTarget] using htarget

set_option maxHeartbeats 0 in
theorem weakUnaryShift_improper_internal_commonApproximation
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (heffective : D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
      ordUnit K (D.complementStrictWeak.scaleGenerator i₀) + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (j : Nat) (hjpos : 0 < j)
    (hjlt : j < finrank K
      (D.complementStrictWeak.component i₀).carrier) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation (D.largeSelectedStart + j) X ∧
        b.IsPrefixApproximation (D.largeSelectedStart + j) X := by
  classical
  let target := ordUnit K (D.complementStrictWeak.scaleGenerator i₀)
  let A := D.input.block.scaleGenerator
  let I : Fin (n + 2) := ⟨D.largeSelectedStart + j, by
    have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
    change D.largeSelectedStart +
        (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤
      n + 2 at hbound
    omega⟩
  have hAN : Lattice.IsNormGeneratorValue q
      (Lattice.scaleTruncation q N target) A := by
    exact unaryShift_common_scaleGenerator D hfin i₀ hi₀ heffective a b
  have hAM : Lattice.IsNormGeneratorValue q
      (Lattice.scaleTruncation q M target) A := by
    have heq := D.unaryShift_intermediate_scaleTruncation_eq hfin i₀ hi₀
    rw [heq]
    exact hAN
  let y := D.smallWeakProfileWitness b
  have hweakSmallRaw := D.weakUnaryShift_smallCommon_indexEquiv
    hfin i₀ hi₀ a b j hjlt
  have hweakSmall : y.indexEquiv I =
      ⟨D.largeSelectedPosition,
        ⟨j, by
          rw [D.weakUnaryShift_smallComponentRank_at_largeSelected
            hfin i₀ hi₀]
          exact hjlt⟩⟩ := by
    simpa only [I, y] using hweakSmallRaw
  have hsmallComponent : (y.indexEquiv I).1 =
      D.largeSelectedPosition := congrArg Sigma.fst hweakSmall
  have hcommonBeforeSelected :
      D.largeSelectedPosition < D.smallSelectedPosition := by
    have hadj := D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
      hfin i₀ hi₀
    change D.largeSelectedPosition.val < D.smallSelectedPosition.val
    omega
  have hleSmall : (y.indexEquiv I).1 ≤ D.smallSelectedPosition := by
    rw [hsmallComponent]
    exact hcommonBeforeSelected.le
  let Rsmall := D.smallStrictCoordinateResolution b I hleSmall
  have hoffSmall : Rsmall.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b I hleSmall
  have hlocalSmall : (Rsmall.profile.indexEquiv I).2.val = j := by
    rw [Rsmall.localCoordinate_eq, hoffSmall, Nat.zero_add]
    exact congrArg (fun z ↦ z.2.val) hweakSmall
  have hfundSmall : Rsmall.fundamentalLattice =
      Lattice.scaleTruncation q N target := by
    rw [Rsmall.fundamentalLattice_eq_scaleTruncation]
    change Lattice.scaleTruncation q N
        (ordUnit K (D.smallAlmostJordan.scaleGenerator
          (y.indexEquiv I).1)) = _
    rw [hsmallComponent,
      ← D.smallCommonPosition_eq_largeSelectedPosition_of_intermediate
        hfin i₀ hi₀,
      D.smallAlmostJordan_scaleGenerator_common]
  have hASmall : Lattice.IsNormGeneratorValue q
      Rsmall.fundamentalLattice A := by
    rw [hfundSmall]
    exact hAN
  let dSmall := Rsmall.determinantSeedData
  let T := Rsmall.approximationSeedsWith dSmall A hASmall
  obtain ⟨sSmall, hsSmallRaw⟩ :=
    Rsmall.exists_determinantSeedData_eq_weakPrefix_mul_square hoffSmall
  have hsSmall :
      (D.smallAlmostJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice D.largeSelectedPosition.val
          |>.refinedDeterminantUnit) =
        dSmall.leftDet * sSmall ^ 2 := by
    rw [hsmallComponent] at hsSmallRaw
    simpa only [dSmall] using hsSmallRaw
  obtain ⟨sWeak, hsWeak⟩ :=
    unaryShift_weakPrefixDeterminant_relation D hfin i₀ hi₀
  let x := D.largeWeakProfileWitness a
  have hweakLargeRaw := D.weakUnaryShift_largeCommon_indexEquiv
    hfin i₀ hi₀ a (j - 1) (by omega)
  have hweakLarge : x.indexEquiv I =
      ⟨D.smallSelectedPosition,
        ⟨j - 1, by
          rw [D.weakUnaryShift_largeComponentRank_at_smallSelected
            hfin i₀ hi₀]
          omega⟩⟩ := by
    let I' : Fin (n + 2) :=
      ⟨D.largeSelectedStart + ((j - 1) + 1), by
        have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
        change D.largeSelectedStart +
            (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤
          n + 2 at hbound
        omega⟩
    have hI : I = I' := by
      apply Fin.ext
      dsimp only [I, I', Fin.val_mk]
      omega
    rw [hI]
    simpa only [I', x] using hweakLargeRaw
  by_cases hcollision : D.LargeScaleCollision
  · let cCollision := Classical.choose hcollision
    have hscale := Classical.choose_spec hcollision
    let hadj := D.largeCollision_adjacent cCollision hscale
    let k := Classical.choose hadj
    have hk := Classical.choose_spec hadj
    have heq : ordUnit K
          (D.largeAlmostJordan.scaleGenerator k.castSucc) =
        ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
      rw [hk.1, hk.2]
      simpa only [D.largeAlmostJordan_scaleGenerator_selected,
        D.largeAlmostJordan_scaleGenerator_common] using hscale
    let Wmerge := D.largeAlmostJordan.mergeAdjacentAt k heq
    have hstrict : StrictMono
        (fun z ↦ ordUnit K (Wmerge.scaleGenerator z)) :=
      Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
        D.largeAlmostJordan k heq
          (D.largeOnlyScaleCollisionAt cCollision hscale k hk)
    let P : BONG.JordanOrderProfileWitness a.toBONG
        (Wmerge.toJordan hstrict) :=
      Classical.choice
        (a.toBONG.beliLemma47_profile a.good (Wmerge.toJordan hstrict))
    have hafter : k.succ < (x.indexEquiv I).1 := by
      rw [congrArg Sigma.fst hweakLarge, hk.2]
      exact hcommonBeforeSelected
    obtain ⟨p, hkp, hpOld, hpCoordinate, hpLocal⟩ :=
      x.strict_coordinates_of_after
        D.largeAlmostJordan_hasImproperEvenRank k heq hstrict P I hafter
    have hweakComponent : (x.indexEquiv I).1 =
        D.smallSelectedPosition := congrArg Sigma.fst hweakLarge
    have hcomponent : Wmerge.component p =
        D.largeAlmostJordan.component D.smallSelectedPosition := by
      dsimp only [Wmerge]
      rw [D.largeAlmostJordan.mergeAdjacentAt_component_of_ne
        k heq p (Fin.ne_of_gt hkp), Fin.succAbove_of_le_castSucc]
      · rw [hpOld, hweakComponent]
      · exact Fin.succ_le_castSucc_iff.mpr hkp
    have hlocal : (P.indexEquiv I).2.val = j - 1 := by
      rw [hpLocal]
      exact congrArg (fun z ↦ z.2.val) hweakLarge
    have hposition :=
      D.largeCommonPosition_eq_smallSelectedPosition_of_intermediate
        hfin i₀ hi₀
    have hfundScale :
        (Wmerge.toJordan hstrict).fundamentalScaleOrder p = target := by
      unfold Lattice.JordanDecomposition.fundamentalScaleOrder
      rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator]
      change ordUnit K
        ((D.largeAlmostJordan.mergeAdjacentAt k heq).scaleGenerator p) =
          target
      rw [Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleGenerator,
        Fin.succAbove_of_le_castSucc]
      · rw [hpOld, hweakComponent, ← hposition,
          D.largeAlmostJordan_scaleGenerator_common]
      · exact Fin.succ_le_castSucc_iff.mpr hkp
    have hALarge : Lattice.IsNormGeneratorValue q
        ((Wmerge.toJordan hstrict).fundamentalLattice p) A := by
      unfold Lattice.JordanDecomposition.fundamentalLattice
      rw [hfundScale]
      exact hAM
    let w := BONG.WeakJordanOrderProfileWitness.ofStrict Wmerge hstrict P
    let C := w.jordanBlockCoordinates
      (D.largeAlmostJordan_hasImproperEvenRank.mergeAdjacentAt
        D.largeAlmostJordan k heq) p
    let dLarge :=
      BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedDataAny
        Wmerge
          (D.largeAlmostJordan_hasImproperEvenRank.mergeAdjacentAt
            D.largeAlmostJordan k heq)
          hstrict P p
    let S :=
      BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWithAny
        Wmerge
          (D.largeAlmostJordan_hasImproperEvenRank.mergeAdjacentAt
            D.largeAlmostJordan k heq)
          hstrict P p dLarge (-A) hALarge.neg
    have hpne : p.val ≠ 0 := by
      have hkval := k.isLt
      have hkpval : k.val < p.val := hkp
      omega
    have hpVal : p.val = k.val + 1 := by
      have hpSmall : p.succ = D.smallSelectedPosition :=
        hpOld.trans hweakComponent
      have hpSmallVal := congrArg Fin.val hpSmall
      have hsmallVal' : D.smallSelectedPosition.val = k.val + 2 := by
        calc
          D.smallSelectedPosition.val =
              D.largeSelectedPosition.val + 1 :=
            D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
              hfin i₀ hi₀
          _ = k.succ.val + 1 := by rw [hk.2]
          _ = k.val + 2 := by rfl
      rw [hsmallVal'] at hpSmallVal
      change p.val + 1 = k.val + 2 at hpSmallVal
      omega
    have hsmallVal : D.smallSelectedPosition.val = k.val + 2 := by
      calc
        D.smallSelectedPosition.val =
            D.largeSelectedPosition.val + 1 :=
          D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
            hfin i₀ hi₀
        _ = k.succ.val + 1 := by rw [hk.2]
        _ = k.val + 2 := by rfl
    obtain ⟨sMerge, hsMergeRaw⟩ :=
      D.largeAlmostJordan.exists_mergeAdjacentAt_prefixThrough_mul_square
        k heq
    have hsMerge :
        (D.largeAlmostJordan.toOrthogonalDecomposition
            |>.prefixQuadraticSublattice D.smallSelectedPosition.val
            |>.refinedDeterminantUnit) * sMerge ^ 2 =
          dLarge.leftDet := by
      rw [BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedDataAny_leftDet_of_component_ne_zero
        Wmerge
          (D.largeAlmostJordan_hasImproperEvenRank.mergeAdjacentAt
            D.largeAlmostJordan k heq)
          hstrict P p hpne]
      rw [hsmallVal, hpVal]
      unfold Lattice.WeakJordanDecomposition.toJordan
      exact hsMergeRaw
    have hdet : ∃ s : Kˣ,
        S.leftDet = A * T.leftDet * s ^ 2 := by
      refine ⟨sSmall * sWeak * sMerge, ?_⟩
      rw [BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWithAny_leftDet,
        BONG.StrictCoordinateResolution.approximationSeedsWith_leftDet,
        ← hsMerge, hsWeak, hsSmall]
      simp only [mul_pow]
      dsimp only [A]
      ac_rfl
    have hiSource : I.val = C.start + (j - 1) := by
      have hglobal := w.index_val_eq_componentStart_add_local I
      change I.val = w.componentStart p + (j - 1)
      have hwPosition : (w.indexEquiv I).1 = p := by
        change (P.indexEquiv I).1 = p
        exact hpCoordinate
      have hwLocal : (w.indexEquiv I).2.val = j - 1 := by
        change (P.indexEquiv I).2.val = j - 1
        exact hlocal
      have hstartEq : w.componentStart (w.indexEquiv I).1 =
          w.componentStart p := congrArg w.componentStart hwPosition
      calc
        I.val = w.componentStart (w.indexEquiv I).1 +
            (w.indexEquiv I).2.val := hglobal
        _ = w.componentStart p + (j - 1) :=
          congrArg₂ (· + ·) hstartEq hwLocal
    have hiSmall : I.val = Rsmall.coordinates.start + j := by
      have hglobal := Rsmall.index_val_eq_coordinates_start_add_local
      rw [hlocalSmall] at hglobal
      exact hglobal
    have hstart : C.start = Rsmall.coordinates.start + 1 := by
      omega
    have hiC : I.val < C.stop := by
      rw [hiSource]
      change C.start + (j - 1) < C.start +
        finrank K (Wmerge.component p).carrier
      apply Nat.add_lt_add_left
      rw [hcomponent,
        D.weakUnaryShift_largeComponentRank_at_smallSelected hfin i₀ hi₀]
      omega
    have hiSmallStop : I.val < Rsmall.coordinates.stop :=
      Rsmall.index_val_lt_coordinates_stop
    have hsourceNorm : S.normGenerator = -A := by
      simpa only [S] using
        BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWithAny_normGenerator
          Wmerge
            (D.largeAlmostJordan_hasImproperEvenRank.mergeAdjacentAt
              D.largeAlmostJordan k heq)
            hstrict P p dLarge (-A) hALarge.neg
    have htargetNorm : T.normGenerator = A := by
      simpa only [T] using
        BONG.StrictCoordinateResolution.approximationSeedsWith_normGenerator
          Rsmall dSmall A hASmall
    have hresult := shiftedCommonApproximation a b S T A hstart hdet
      hsourceNorm htargetNorm I.val (by omega) hiC hiSmallStop
    simpa only [I] using hresult

  · let hstrict := D.largeAlmostJordan_scaleOrder_strict_of_noCollision
      hcollision
    let P : BONG.JordanOrderProfileWitness a.toBONG
        (D.largeAlmostJordan.toJordan hstrict) :=
      Classical.choice
        (a.toBONG.beliLemma47_profile a.good
          (D.largeAlmostJordan.toJordan hstrict))
    let w := BONG.WeakJordanOrderProfileWitness.ofStrict
      D.largeAlmostJordan hstrict P
    have hcoordinates := x.indexEquiv_eq_ofStrict hstrict P I
    have hp : (P.indexEquiv I).1 = D.smallSelectedPosition := by
      calc
        (P.indexEquiv I).1 = (x.indexEquiv I).1 :=
          congrArg Sigma.fst hcoordinates.symm
        _ = D.smallSelectedPosition := congrArg Sigma.fst hweakLarge
    have hlocal : (P.indexEquiv I).2.val = j - 1 := by
      calc
        (P.indexEquiv I).2.val = (x.indexEquiv I).2.val :=
          congrArg (fun z ↦ z.2.val) hcoordinates.symm
        _ = j - 1 := congrArg (fun z ↦ z.2.val) hweakLarge
    let p := (P.indexEquiv I).1
    let C := w.jordanBlockCoordinates
      D.largeAlmostJordan_hasImproperEvenRank p
    have hfundScale :
        (D.largeAlmostJordan.toJordan hstrict).fundamentalScaleOrder p =
          target := by
      unfold Lattice.JordanDecomposition.fundamentalScaleOrder
      rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
        show p = D.smallSelectedPosition by exact hp,
        ← D.largeCommonPosition_eq_smallSelectedPosition_of_intermediate
          hfin i₀ hi₀,
        D.largeAlmostJordan_scaleGenerator_common]
    have hALarge : Lattice.IsNormGeneratorValue q
        ((D.largeAlmostJordan.toJordan hstrict).fundamentalLattice p) A := by
      unfold Lattice.JordanDecomposition.fundamentalLattice
      rw [hfundScale]
      exact hAM
    let dLarge :=
      BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedDataAny
        D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
          hstrict P p
    let S :=
      BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWithAny
        D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
          hstrict P p dLarge (-A) hALarge.neg
    have hpne : p.val ≠ 0 := by
      rw [show p = D.smallSelectedPosition by exact hp]
      have hadj := D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
        hfin i₀ hi₀
      omega
    have hdLarge : dLarge.leftDet =
        (D.largeAlmostJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice D.smallSelectedPosition.val
          |>.refinedDeterminantUnit) := by
      rw [BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedDataAny_leftDet_of_component_ne_zero
          D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
            hstrict P p hpne]
      rw [show p = D.smallSelectedPosition by exact hp]
      unfold Lattice.WeakJordanDecomposition.toJordan
      rfl
    have hdet : ∃ s : Kˣ,
        S.leftDet = A * T.leftDet * s ^ 2 := by
      refine ⟨sSmall * sWeak, ?_⟩
      rw [BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWithAny_leftDet,
        BONG.StrictCoordinateResolution.approximationSeedsWith_leftDet,
        hdLarge, hsWeak, hsSmall, mul_pow]
      dsimp only [A]
      ac_rfl
    have hiSource : I.val = C.start + (j - 1) := by
      have hglobal := w.index_val_eq_componentStart_add_local I
      change I.val = w.componentStart p + (j - 1)
      rw [← hlocal]
      exact hglobal
    have hiSmall : I.val = Rsmall.coordinates.start + j := by
      have hglobal := Rsmall.index_val_eq_coordinates_start_add_local
      rw [hlocalSmall] at hglobal
      exact hglobal
    have hstart : C.start = Rsmall.coordinates.start + 1 := by
      omega
    have hiC : I.val < C.stop := by
      rw [hiSource]
      change C.start + (j - 1) < C.start +
        finrank K (D.largeAlmostJordan.component p).carrier
      apply Nat.add_lt_add_left
      rw [show p = D.smallSelectedPosition by exact hp,
        D.weakUnaryShift_largeComponentRank_at_smallSelected hfin i₀ hi₀]
      omega
    have hiSmallStop : I.val < Rsmall.coordinates.stop :=
      Rsmall.index_val_lt_coordinates_stop
    have hsourceNorm : S.normGenerator = -A := by
      simpa only [S] using
        BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWithAny_normGenerator
          D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
            hstrict P p dLarge (-A) hALarge.neg
    have htargetNorm : T.normGenerator = A := by
      simpa only [T] using
        BONG.StrictCoordinateResolution.approximationSeedsWith_normGenerator
          Rsmall dSmall A hASmall
    have hresult := shiftedCommonApproximation a b S T A hstart hdet
      hsourceNorm htargetNorm
      I.val (by omega) hiC hiSmallStop
    simpa only [I] using hresult
set_option maxHeartbeats 0 in
theorem weakUnaryShift_improper_endpoint_commonApproximation
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (heffective : D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
      ordUnit K (D.complementStrictWeak.scaleGenerator i₀) + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2)) :
    let c := finrank K (D.complementStrictWeak.component i₀).carrier
    ∃ X : Kˣ,
      a.IsPrefixApproximation (D.largeSelectedStart + c) X ∧
        b.IsPrefixApproximation (D.largeSelectedStart + c) X := by
  classical
  let c := finrank K (D.complementStrictWeak.component i₀).carrier
  let target := ordUnit K (D.complementStrictWeak.scaleGenerator i₀)
  let A := D.input.block.scaleGenerator
  have hcpos : 0 < c := by
    exact D.complementStrictWeak.component_finrank_pos i₀
  have hposition :=
    D.largeCommonPosition_eq_smallSelectedPosition_of_intermediate
      hfin i₀ hi₀
  have hcevenRaw := D.largeCommon_componentRank_even_of_scale_lt_effective
    i₀ (by omega)
  have hceven : Even c := by
    rw [hposition,
      D.weakUnaryShift_largeComponentRank_at_smallSelected hfin i₀ hi₀]
      at hcevenRaw
    exact hcevenRaw
  have hcrank : 2 ≤ c := by
    rcases hceven with ⟨d, hd⟩
    omega
  let I : Fin (n + 2) := ⟨D.largeSelectedStart + c, by
    have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
    change D.largeSelectedStart + (c + 1) ≤ n + 2 at hbound
    omega⟩
  have hAN : Lattice.IsNormGeneratorValue q
      (Lattice.scaleTruncation q N target) A := by
    exact unaryShift_common_scaleGenerator D hfin i₀ hi₀ heffective a b
  have hAM : Lattice.IsNormGeneratorValue q
      (Lattice.scaleTruncation q M target) A := by
    have heq := D.unaryShift_intermediate_scaleTruncation_eq hfin i₀ hi₀
    rw [heq]
    exact hAN
  let y := D.smallWeakProfileWitness b
  let zero : Fin
      (finrank K (D.smallAlmostJordan.component
        D.smallSelectedPosition).carrier) :=
    ⟨0, by rw [D.weakUnaryShift_smallComponentRank_selected hfin]; omega⟩
  have hprefixSmall := D.weakUnaryShift_smallPrefixRank_at_smallSelected
    hfin i₀ hi₀
  have hIselected : I = y.indexEquiv.symm
      ⟨D.smallSelectedPosition, zero⟩ := by
    apply Fin.ext
    have hinverse := y.inverse_index_val D.smallSelectedPosition zero
    dsimp only [I, zero, Fin.val_mk]
    rw [hinverse, hprefixSmall]
    rfl
  have hweakSmall : y.indexEquiv I =
      ⟨D.smallSelectedPosition, zero⟩ := by
    rw [hIselected, y.indexEquiv.apply_symm_apply]
  have hsmallComponent : (y.indexEquiv I).1 =
      D.smallSelectedPosition := congrArg Sigma.fst hweakSmall
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallComponent.le
  have hoffSmall : Rsmall.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b I hsmallComponent.le
  have hlocalSmall : (Rsmall.profile.indexEquiv I).2.val = 0 := by
    rw [Rsmall.localCoordinate_eq, hoffSmall, Nat.zero_add]
    exact congrArg (fun z ↦ z.2.val) hweakSmall
  let dSmall := Rsmall.determinantSeedData
  let T := Rsmall.approximationSeedsWith dSmall
    Rsmall.fundamentalNormGenerator Rsmall.fundamentalNormGenerator_spec
  have hiSmall : I.val = Rsmall.coordinates.start := by
    have hglobal := Rsmall.index_val_eq_coordinates_start_add_local
    have hlocalSmall' :
        (Rsmall.profile.indexEquiv I).2.val = 0 := hlocalSmall
    omega
  have htargetRaw := T.evenApproximation 0 (by
    simpa only [Nat.mul_zero, add_zero, ← hiSmall] using
      Rsmall.index_val_lt_coordinates_stop)
  have htarget : b.IsPrefixApproximation I.val dSmall.leftDet := by
    rw [hiSmall]
    simpa only [Nat.mul_zero, add_zero, pow_zero, one_mul, T,
      BONG.StrictCoordinateResolution.approximationSeedsWith_leftDet] using
        htargetRaw
  obtain ⟨sSmall, hsSmallRaw⟩ :=
    Rsmall.exists_determinantSeedData_eq_weakPrefix_mul_square hoffSmall
  have hsSmall :
      (D.smallAlmostJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice D.smallSelectedPosition.val
          |>.refinedDeterminantUnit) =
        dSmall.leftDet * sSmall ^ 2 := by
    rw [hsmallComponent] at hsSmallRaw
    simpa only [dSmall] using hsSmallRaw
  obtain ⟨sWeak, hsWeak⟩ :=
    unaryShift_weakPrefixThroughDeterminant_relation D hfin i₀ hi₀
  let x := D.largeWeakProfileWitness a
  have hweakLargeRaw := D.weakUnaryShift_largeCommon_indexEquiv
    hfin i₀ hi₀ a (c - 1) (by omega)
  have hweakLarge : x.indexEquiv I =
      ⟨D.smallSelectedPosition,
        ⟨c - 1, by
          rw [D.weakUnaryShift_largeComponentRank_at_smallSelected
            hfin i₀ hi₀]
          omega⟩⟩ := by
    let I' : Fin (n + 2) :=
      ⟨D.largeSelectedStart + ((c - 1) + 1), by
        have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
        change D.largeSelectedStart + (c + 1) ≤ n + 2 at hbound
        omega⟩
    have hI : I = I' := by
      apply Fin.ext
      dsimp only [I, I', Fin.val_mk]
      omega
    rw [hI]
    simpa only [I', x] using hweakLargeRaw
  by_cases hcollision : D.LargeScaleCollision
  · let cCollision := Classical.choose hcollision
    have hscale := Classical.choose_spec hcollision
    let hadj := D.largeCollision_adjacent cCollision hscale
    let k := Classical.choose hadj
    have hk := Classical.choose_spec hadj
    have heq : ordUnit K
          (D.largeAlmostJordan.scaleGenerator k.castSucc) =
        ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
      rw [hk.1, hk.2]
      simpa only [D.largeAlmostJordan_scaleGenerator_selected,
        D.largeAlmostJordan_scaleGenerator_common] using hscale
    let Wmerge := D.largeAlmostJordan.mergeAdjacentAt k heq
    have hstrict : StrictMono
        (fun z ↦ ordUnit K (Wmerge.scaleGenerator z)) :=
      Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
        D.largeAlmostJordan k heq
          (D.largeOnlyScaleCollisionAt cCollision hscale k hk)
    let P : BONG.JordanOrderProfileWitness a.toBONG
        (Wmerge.toJordan hstrict) :=
      Classical.choice
        (a.toBONG.beliLemma47_profile a.good (Wmerge.toJordan hstrict))
    have hafter : k.succ < (x.indexEquiv I).1 := by
      rw [congrArg Sigma.fst hweakLarge, hk.2]
      have hadjSelected :=
        D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
          hfin i₀ hi₀
      change D.largeSelectedPosition.val < D.smallSelectedPosition.val
      omega
    obtain ⟨p, hkp, hpOld, hpCoordinate, hpLocal⟩ :=
      x.strict_coordinates_of_after
        D.largeAlmostJordan_hasImproperEvenRank k heq hstrict P I hafter
    have hweakComponent : (x.indexEquiv I).1 =
        D.smallSelectedPosition := congrArg Sigma.fst hweakLarge
    have hcomponent : Wmerge.component p =
        D.largeAlmostJordan.component D.smallSelectedPosition := by
      dsimp only [Wmerge]
      rw [D.largeAlmostJordan.mergeAdjacentAt_component_of_ne
        k heq p (Fin.ne_of_gt hkp), Fin.succAbove_of_le_castSucc]
      · rw [hpOld, hweakComponent]
      · exact Fin.succ_le_castSucc_iff.mpr hkp
    have hlocal : (P.indexEquiv I).2.val = c - 1 := by
      rw [hpLocal]
      exact congrArg (fun z ↦ z.2.val) hweakLarge
    have hfundScale :
        (Wmerge.toJordan hstrict).fundamentalScaleOrder p = target := by
      unfold Lattice.JordanDecomposition.fundamentalScaleOrder
      rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator]
      change ordUnit K
        ((D.largeAlmostJordan.mergeAdjacentAt k heq).scaleGenerator p) =
          target
      rw [Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleGenerator,
        Fin.succAbove_of_le_castSucc]
      · rw [hpOld, hweakComponent, ← hposition,
          D.largeAlmostJordan_scaleGenerator_common]
      · exact Fin.succ_le_castSucc_iff.mpr hkp
    have hALarge : Lattice.IsNormGeneratorValue q
        ((Wmerge.toJordan hstrict).fundamentalLattice p) A := by
      unfold Lattice.JordanDecomposition.fundamentalLattice
      rw [hfundScale]
      exact hAM
    have hrank : 2 ≤ (Wmerge.toJordan hstrict).componentRank p := by
      change 2 ≤ finrank K (Wmerge.component p).carrier
      rw [hcomponent,
        D.weakUnaryShift_largeComponentRank_at_smallSelected hfin i₀ hi₀]
      exact hcrank
    let w := BONG.WeakJordanOrderProfileWitness.ofStrict Wmerge hstrict P
    let C := w.jordanBlockCoordinates
      (D.largeAlmostJordan_hasImproperEvenRank.mergeAdjacentAt
        D.largeAlmostJordan k heq) p
    have hsource :=
      BONG.WeakJordanOrderProfileWitness.corollary33_prescribedPrefixApproximation
        a Wmerge
          (D.largeAlmostJordan_hasImproperEvenRank.mergeAdjacentAt
            D.largeAlmostJordan k heq)
          hstrict P p A hALarge hrank
    let dThrough : Kˣ :=
      ((Wmerge.toJordan hstrict).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (p.val + 1)
        |>.refinedDeterminantUnit)
    change a.IsPrefixApproximation (C.stop - 1) (A * dThrough) at hsource
    have hiSource : I.val = C.start + (c - 1) := by
      have hglobal := w.index_val_eq_componentStart_add_local I
      change I.val = w.componentStart p + (c - 1)
      have hwPosition : (w.indexEquiv I).1 = p := by
        change (P.indexEquiv I).1 = p
        exact hpCoordinate
      have hwLocal : (w.indexEquiv I).2.val = c - 1 := by
        change (P.indexEquiv I).2.val = c - 1
        exact hlocal
      have hstartEq : w.componentStart (w.indexEquiv I).1 =
          w.componentStart p := congrArg w.componentStart hwPosition
      calc
        I.val = w.componentStart (w.indexEquiv I).1 +
            (w.indexEquiv I).2.val := hglobal
        _ = w.componentStart p + (c - 1) :=
          congrArg₂ (· + ·) hstartEq hwLocal
    have hCstop : C.stop = C.start + c := by
      change C.start + finrank K (Wmerge.component p).carrier =
        C.start + c
      rw [hcomponent,
        D.weakUnaryShift_largeComponentRank_at_smallSelected hfin i₀ hi₀]
    have hiEnd : C.stop - 1 = I.val := by omega
    rw [hiEnd] at hsource
    have hpVal : p.val = k.val + 1 := by
      have hpSmall : p.succ = D.smallSelectedPosition :=
        hpOld.trans hweakComponent
      have hpSmallVal := congrArg Fin.val hpSmall
      have hsmallVal' : D.smallSelectedPosition.val = k.val + 2 := by
        calc
          D.smallSelectedPosition.val =
              D.largeSelectedPosition.val + 1 :=
            D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
              hfin i₀ hi₀
          _ = k.succ.val + 1 := by rw [hk.2]
          _ = k.val + 2 := by rfl
      rw [hsmallVal'] at hpSmallVal
      change p.val + 1 = k.val + 2 at hpSmallVal
      omega
    obtain ⟨sMerge, hsMergeRaw⟩ :=
      exists_mergeAdjacentAt_nextPrefix_mul_square
        D.largeAlmostJordan k p heq hkp hpVal
    have hsMerge :
        (D.largeAlmostJordan.toOrthogonalDecomposition
            |>.prefixQuadraticSublattice
              (D.smallSelectedPosition.val + 1)
            |>.refinedDeterminantUnit) * sMerge ^ 2 =
          dThrough := by
      have hpSmall : p.succ = D.smallSelectedPosition :=
        hpOld.trans hweakComponent
      have hpSmallVal := congrArg Fin.val hpSmall
      dsimp only [dThrough]
      rw [← hpSmallVal]
      change
        (D.largeAlmostJordan.toOrthogonalDecomposition
            |>.prefixQuadraticSublattice (p.val + 2)
            |>.refinedDeterminantUnit) * sMerge ^ 2 =
          ((Wmerge.toJordan hstrict).toOrthogonalDecomposition
            |>.prefixQuadraticSublattice (p.val + 1)
            |>.refinedDeterminantUnit)
      unfold Lattice.WeakJordanDecomposition.toJordan
      exact hsMergeRaw
    have hmul : A * dThrough =
        dSmall.leftDet * (A * sSmall * sWeak * sMerge) ^ 2 := by
      rw [← hsMerge, hsWeak, hsSmall]
      simp only [pow_two]
      dsimp only [A]
      ac_rfl
    rw [hmul] at hsource
    have hsource' :=
      (a.isPrefixApproximation_mul_square_iff I.val dSmall.leftDet
        (A * sSmall * sWeak * sMerge)).mp hsource
    refine ⟨dSmall.leftDet, ?_, ?_⟩
    · simpa only [I] using hsource'
    · simpa only [I] using htarget

  · let hstrict := D.largeAlmostJordan_scaleOrder_strict_of_noCollision
      hcollision
    let P : BONG.JordanOrderProfileWitness a.toBONG
        (D.largeAlmostJordan.toJordan hstrict) :=
      Classical.choice
        (a.toBONG.beliLemma47_profile a.good
          (D.largeAlmostJordan.toJordan hstrict))
    let w := BONG.WeakJordanOrderProfileWitness.ofStrict
      D.largeAlmostJordan hstrict P
    have hcoordinates := x.indexEquiv_eq_ofStrict hstrict P I
    have hp : (P.indexEquiv I).1 = D.smallSelectedPosition := by
      calc
        (P.indexEquiv I).1 = (x.indexEquiv I).1 :=
          congrArg Sigma.fst hcoordinates.symm
        _ = D.smallSelectedPosition := congrArg Sigma.fst hweakLarge
    have hlocal : (P.indexEquiv I).2.val = c - 1 := by
      calc
        (P.indexEquiv I).2.val = (x.indexEquiv I).2.val :=
          congrArg (fun z ↦ z.2.val) hcoordinates.symm
        _ = c - 1 := congrArg (fun z ↦ z.2.val) hweakLarge
    let p := (P.indexEquiv I).1
    let C := w.jordanBlockCoordinates
      D.largeAlmostJordan_hasImproperEvenRank p
    have hfundScale :
        (D.largeAlmostJordan.toJordan hstrict).fundamentalScaleOrder p =
          target := by
      unfold Lattice.JordanDecomposition.fundamentalScaleOrder
      rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
        show p = D.smallSelectedPosition by exact hp,
        ← hposition, D.largeAlmostJordan_scaleGenerator_common]
    have hALarge : Lattice.IsNormGeneratorValue q
        ((D.largeAlmostJordan.toJordan hstrict).fundamentalLattice p) A := by
      unfold Lattice.JordanDecomposition.fundamentalLattice
      rw [hfundScale]
      exact hAM
    have hrank : 2 ≤
        (D.largeAlmostJordan.toJordan hstrict).componentRank p := by
      change 2 ≤ finrank K (D.largeAlmostJordan.component p).carrier
      rw [show p = D.smallSelectedPosition by exact hp,
        D.weakUnaryShift_largeComponentRank_at_smallSelected hfin i₀ hi₀]
      exact hcrank
    have hsource :=
      BONG.WeakJordanOrderProfileWitness.corollary33_prescribedPrefixApproximation
        a D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
          hstrict P p A hALarge hrank
    let dThrough : Kˣ :=
      ((D.largeAlmostJordan.toJordan hstrict).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (p.val + 1)
        |>.refinedDeterminantUnit)
    change a.IsPrefixApproximation (C.stop - 1) (A * dThrough) at hsource
    have hiSource : I.val = C.start + (c - 1) := by
      have hglobal := w.index_val_eq_componentStart_add_local I
      change I.val = w.componentStart p + (c - 1)
      rw [← hlocal]
      exact hglobal
    have hCstop : C.stop = C.start + c := by
      change C.start + finrank K (D.largeAlmostJordan.component p).carrier =
        C.start + c
      rw [show p = D.smallSelectedPosition by exact hp,
        D.weakUnaryShift_largeComponentRank_at_smallSelected hfin i₀ hi₀]
    have hiEnd : C.stop - 1 = I.val := by omega
    rw [hiEnd] at hsource
    have hdThrough : dThrough =
        (D.largeAlmostJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice
            (D.smallSelectedPosition.val + 1)
          |>.refinedDeterminantUnit) := by
      dsimp only [dThrough]
      rw [show p = D.smallSelectedPosition by exact hp]
      unfold Lattice.WeakJordanDecomposition.toJordan
      rfl
    have hmul : A * dThrough =
        dSmall.leftDet * (A * sSmall * sWeak) ^ 2 := by
      rw [hdThrough, hsWeak, hsSmall]
      simp only [pow_two]
      dsimp only [A]
      ac_rfl
    rw [hmul] at hsource
    have hsource' :=
      (a.isPrefixApproximation_mul_square_iff I.val dSmall.leftDet
        (A * sSmall * sWeak)).mp hsource
    refine ⟨dSmall.leftDet, ?_, ?_⟩
    · simpa only [I] using hsource'
    · simpa only [I] using htarget
theorem weakUnaryShift_improper_commonApproximation
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (heffective : D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
      ordUnit K (D.complementStrictWeak.scaleGenerator i₀) + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (j : Nat) (hjpos : 0 < j)
    (hjle : j ≤ finrank K
      (D.complementStrictWeak.component i₀).carrier) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation (D.largeSelectedStart + j) X ∧
        b.IsPrefixApproximation (D.largeSelectedStart + j) X := by
  by_cases hjlt : j <
      finrank K (D.complementStrictWeak.component i₀).carrier
  · exact weakUnaryShift_improper_internal_commonApproximation
      D hfin i₀ hi₀ heffective a b j hjpos hjlt
  · have hjEq : j =
        finrank K (D.complementStrictWeak.component i₀).carrier := by
      omega
    subst j
    exact weakUnaryShift_improper_endpoint_commonApproximation
      D hfin i₀ hi₀ heffective a b

theorem weakUnaryShift_improper_defectCertificate
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (heffective : D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
      ordUnit K (D.complementStrictWeak.scaleGenerator i₀) + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.DefectReducedRange i)
    (hout : ¬D.Lemma517Range i) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  let c := finrank K (D.complementStrictWeak.component i₀).carrier
  have hstartEnd :=
    D.weakUnaryShift_smallSelectedStart_eq_intervalEnd hfin i₀ hi₀
  change D.smallSelectedStart = D.largeSelectedStart + c at hstartEnd
  have hleft : D.largeSelectedStart < i.val := by
    change ¬ i.val ≤ D.largeSelectedStart +
      finrank K
        (D.largeAlmostJordan.component D.largeSelectedPosition).carrier - 1
      at hout
    rw [D.largeAlmostJordan_finrank_selected, hfin] at hout
    omega
  have hright : i.val ≤ D.largeSelectedStart + c := by
    change i.val ≤ D.smallSelectedStart +
      finrank K
        (D.smallAlmostJordan.component D.smallSelectedPosition).carrier - 1
      at hi
    rw [D.smallAlmostJordan_finrank_selected, hfin, hstartEnd] at hi
    omega
  let j := i.val - D.largeSelectedStart
  have hjpos : 0 < j := by dsimp only [j]; omega
  have hjle : j ≤ c := by dsimp only [j]; omega
  obtain ⟨X, hsource, htarget⟩ :=
    weakUnaryShift_improper_commonApproximation
      D hfin i₀ hi₀ heffective a b j hjpos (by
        simpa only [c] using hjle)
  have hindex : D.largeSelectedStart + j = i.val := by
    dsimp only [j]
    exact Nat.add_sub_of_le hleft.le
  rw [hindex] at hsource htarget
  have hbound := D.weakUnaryShift_improper_commonBound
    hfin i₀ hi₀ heffective a b i hleft (by
      simpa only [c] using hright)
  exact BONG.GoodBONG.Beli2019SectionFiveDefectCertificate.common
    X hsource htarget hbound

end Lattice.Beli2019Lemma51Data

end Bong
