import Bong.Bong.Beli2019Lemma34Complete

namespace Bong

open Dyadic Module
open BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.JordanOrderProfileWitness

noncomputable def boundaryOneAfterDiagonalUnits
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t) (A : Kˣ) :
    Fin ((P.boundaryIndex z).val + 2) → Kˣ :=
  Fin.snoc (P.boundaryPrefixDiagonalUnits z) A

omit [DyadicDiscriminantClassLaws K] in
theorem boundaryIndex_succ_lt_of_rightComponentRank_gt_one
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex z)) :
    (P.boundaryIndex z).val + 1 < n + 1 := by
  let ri : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex z
  have hprefix := P.boundaryIndex_succ_val_eq_componentRankPrefix z
  have htotal := P.sum_componentRank_eq_length
  change (∑ k, J.componentRank k) = n + 2 at htotal
  change 1 < J.componentRank ri at hrank
  have hle :
      (∑ k ∈ insert ri (Finset.Iio ri), J.componentRank k) ≤
        ∑ k, J.componentRank k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · simp
    · intro k _ _
      exact Nat.zero_le _
  rw [Finset.sum_insert (by simp)] at hle
  change (P.boundaryIndex z).val + 1 =
    ∑ k ∈ Finset.Iio ri, J.componentRank k at hprefix
  omega

noncomputable def boundaryOneAfterIndex
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex z)) : Fin (n + 1) :=
  ⟨(P.boundaryIndex z).val + 1,
    P.boundaryIndex_succ_lt_of_rightComponentRank_gt_one z hrank⟩

namespace PrescribedJordanComparison

variable {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
  {J : Lattice.JordanDecomposition q L (t + 1)}

set_option maxHeartbeats 0 in
theorem oneAfter_leftRepresentation_of_conditionII
    (C : PrescribedJordanComparison a J)
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryRightIndex z)) A)
    (hcontainment :
      let Js := C.adapted.sourceJordanSucc C.componentCount_eq
      Js.fundamentalIdeal z < Js.fourNormOverWeightIdeal
        (Lattice.JordanDecomposition.boundaryRightIndex z)) :
    DiagonalRepresents
      (a.prefixValues ((P.boundaryIndex z).val + 1) (by omega))
      (diagonalUnitCoefficients
        (P.boundaryOneAfterDiagonalUnits z A)) := by
  let S := C.adapted
  let h := C.componentCount_eq
  let Js := S.sourceJordanSucc h
  let Ps := S.sourceProfileSucc h
  let ri : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex z
  have hAJs : Lattice.IsNormGeneratorValue q (Js.fundamentalLattice ri) A := by
    apply Lattice.JordanDecomposition.isNormGeneratorValue_of_normGroupSet_eq
      hA
    · have hg := C.sameType.normGroup_eq ri
      rw [C.sameType.indexEquiv_apply_eq_self] at hg
      simpa only [Lattice.JordanDecomposition.fundamentalNormGroup] using hg
    · exact Js.exists_fundamentalNormGenerator ri
  let As0 :=
    Lattice.JordanDecomposition.canonicalFundamentalNormGeneratorChoice Js
  let As := As0.replaceAt ri A hAJs
  have htrigger : Js.fundamentalIdeal z <
      Js.fourNormOverWeightIdealWith As ri := by
    rw [Js.fourNormOverWeightIdealWith_eq_canonical]
    exact hcontainment
  have hembedding := (C.conditionsFromAdapted As).2.1 z htrigger
  have hAvalue : As.value ri = A := by simp [As]
  rw [hAvalue] at hembedding
  have hdiag : DiagonalRepresents
      (diagonalUnitCoefficients
        (a.prefixValueUnits ((Ps.boundaryIndex z).val + 1) (by omega)))
      (diagonalUnitCoefficients
        (P.boundaryOneAfterDiagonalUnits z A)) := by
    have hgeometry := boundaryEmbedding_iff_diagonal
      (a.prefixValueUnits ((Ps.boundaryIndex z).val + 1) (by omega))
      (P.boundaryPrefixDiagonalUnits z) A
      ((S.sourcePrefixExactDiagonalIsometry h z).symm)
      (P.boundaryPrefixDiagonalizationIsometry z)
    apply hgeometry.1
    change Js.toOrthogonalDecomposition.prefixQuadraticSublattice
        (z.val + 1) |>.EmbedsIntoOrthogonalSum
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice
        (z.val + 1)) (QuadraticSpace.scaledLine A)
    exact hembedding
  have hdiag' : DiagonalRepresents
      (a.prefixValues ((Ps.boundaryIndex z).val + 1) (by omega))
      (diagonalUnitCoefficients
        (P.boundaryOneAfterDiagonalUnits z A)) := by
    simpa only [a.diagonalUnitCoefficients_prefixValueUnits] using hdiag
  have hboundary : Ps.boundaryIndex z = P.boundaryIndex z :=
    C.boundaryIndex_eq P z
  exact BONG.GoodBONG.sourcePrefixRepresents_cast a
    (diagonalUnitCoefficients (P.boundaryOneAfterDiagonalUnits z A))
    (by rw [hboundary]) hdiag'

set_option maxHeartbeats 0 in
theorem oneAfter_leftRepresentation
    (C : PrescribedJordanComparison a J)
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryRightIndex z)) A)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex z)) :
    a.leftApproximationTrigger (P.boundaryOneAfterIndex z hrank) →
      DiagonalRepresents
        (a.prefixValues (P.boundaryOneAfterIndex z hrank).val (by omega))
        (diagonalUnitCoefficients
          (P.boundaryOneAfterDiagonalUnits z A)) := by
  intro htrigger
  rcases htrigger with hzero | ⟨hpositive, hsum⟩
  · simp [boundaryOneAfterIndex] at hzero
  · let S := C.adapted
    let h := C.componentCount_eq
    let Js := S.sourceJordanSucc h
    let Ps := S.sourceProfileSucc h
    let i := P.boundaryOneAfterIndex z hrank
    have hboundary : Ps.boundaryIndex z = P.boundaryIndex z :=
      C.boundaryIndex_eq P z
    have hsum' : 2 * (ramificationIndex K : ℚ) <
        a.alphaValue ⟨i.val - 1, by omega⟩ + a.alphaValue i := by
      simpa only [i] using hsum
    rcases S.internalTrigger_has_adjacentContainment h i hpositive hsum' with
      ⟨z0, hindex, hcontainment⟩ | ⟨z0, hindex, _hcontainment⟩
    · have hz0 : z0 = z := by
        apply (boundaryIndex_strictMono Ps).injective
        apply Fin.ext
        have hvalue : (Ps.boundaryIndex z0).val =
            (P.boundaryIndex z).val := by
          change (P.boundaryIndex z).val + 1 =
              (Ps.boundaryIndex z0).val + 1 at hindex
          omega
        rw [hboundary]
        exact hvalue
      subst z0
      simpa only [i, boundaryOneAfterIndex] using
        C.oneAfter_leftRepresentation_of_conditionII P z A hA hcontainment
    · have hvalue : (Ps.boundaryIndex z).val + 1 =
          (Ps.boundaryIndex z0).val := by
        rw [hboundary]
        exact hindex
      have hzlt : z < z0 := by
        rcases lt_trichotomy z z0 with hlt | heq | hgt
        · exact hlt
        · subst z0
          omega
        · have hb := boundaryIndex_strictMono Ps hgt
          omega
      have hnext : z.val + 1 < t := by omega
      let next : Fin t := ⟨z.val + 1, hnext⟩
      let ri : Fin (t + 1) :=
        Lattice.JordanDecomposition.boundaryRightIndex z
      have hrankS : 1 < Js.componentRank ri := by
        have hrs := C.sameType.componentRank_eq ri
        rw [C.sameType.indexEquiv_apply_eq_self] at hrs
        rw [← hrs]
        exact hrank
      have hcurr := Ps.boundaryIndex_succ_val_eq_componentRankPrefix z
      have hnextBoundary :=
        Ps.boundaryIndex_succ_val_eq_componentRankPrefix next
      change (Ps.boundaryIndex z).val + 1 =
        ∑ k ∈ Finset.Iio
          (Lattice.JordanDecomposition.boundaryRightIndex z),
            Js.componentRank k at hcurr
      change (Ps.boundaryIndex next).val + 1 =
        ∑ k ∈ Finset.Iio
          (Lattice.JordanDecomposition.boundaryRightIndex next),
            Js.componentRank k at hnextBoundary
      have hIio : Finset.Iio
          (Lattice.JordanDecomposition.boundaryRightIndex next) =
        insert ri (Finset.Iio
          (Lattice.JordanDecomposition.boundaryRightIndex z)) := by
        ext k
        simp only [Finset.mem_Iio, Finset.mem_insert]
        change (k.val < z.val + 2 ↔ k = ri ∨ k.val < z.val + 1)
        constructor
        · intro hk
          by_cases heq : k.val = z.val + 1
          · exact Or.inl (Fin.ext heq)
          · exact Or.inr (by omega)
        · rintro (rfl | hk)
          · change z.val + 1 < z.val + 2
            omega
          · omega
      have hnot : ri ∉ Finset.Iio
          (Lattice.JordanDecomposition.boundaryRightIndex z) := by
        simp only [Finset.mem_Iio, not_lt]
        rfl
      rw [hIio, Finset.sum_insert hnot] at hnextBoundary
      have hmono : (Ps.boundaryIndex next).val ≤
          (Ps.boundaryIndex z0).val := by
        exact_mod_cast (boundaryIndex_strictMono Ps).monotone (by
          change next.val ≤ z0.val
          dsimp only [next]
          omega)
      omega

omit [DyadicDiscriminantClassLaws K] in
set_option maxHeartbeats 0 in
theorem boundaryOneAfterDiagonalUnits_isPrefixApproximation
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (z : Fin t) (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice
        (Lattice.JordanDecomposition.boundaryRightIndex z)) A)
    (hrank : 1 < (W.toJordan hstrict).componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex z)) :
    a.IsPrefixApproximation
      ((P.boundaryOneAfterIndex z hrank).val + 1)
      (diagonalUnitDeterminant
        (P.boundaryOneAfterDiagonalUnits z A)) := by
  let J := W.toJordan hstrict
  let p : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex z
  let w := BONG.WeakJordanOrderProfileWitness.ofStrict W hstrict P
  let Cb := w.jordanBlockCoordinates hW p
  have hstart : Cb.start = (P.boundaryIndex z).val + 1 := by
    have hb := P.boundaryIndex_succ_val_eq_componentRankPrefix z
    change w.componentStart p = (P.boundaryIndex z).val + 1
    change (P.boundaryIndex z).val + 1 =
      ∑ k ∈ Finset.Iio p, finrank K (W.component k).carrier at hb
    unfold BONG.WeakJordanOrderProfileWitness.componentStart
    exact hb.symm
  have hodd : Cb.start + 1 < Cb.stop := by
    change Cb.start + 1 < Cb.start + finrank K (W.component p).carrier
    change 1 < finrank K (W.component p).carrier at hrank
    omega
  let determinant :=
    BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedDataAny
      W hW hstrict P p
  let seeds :=
    BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWithAny
      W hW hstrict P p determinant A hA
  have hseed : a.IsPrefixApproximation (Cb.start + 1)
      (A * determinant.leftDet) := by
    have hraw := seeds.oddApproximation 0 hodd
    simpa only [seeds, Cb, w, Nat.mul_zero, add_zero, pow_zero, one_mul,
      BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWithAny_normGenerator,
      BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWithAny_leftDet]
      using hraw
  let dP : Kˣ :=
    (J.toOrthogonalDecomposition.prefixQuadraticSublattice
      (z.val + 1)).refinedDeterminantUnit
  have hleftDet : determinant.leftDet = dP := by
    have hp : p.val ≠ 0 := by
      simp [p, Lattice.JordanDecomposition.boundaryRightIndex]
    have hraw :=
      BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedDataAny_leftDet_of_component_ne_zero
        W hW hstrict P p hp
    have hpval : p.val = z.val + 1 := rfl
    dsimp only [dP, J]
    rw [← hpval]
    simpa only [determinant] using hraw
  have hbase : a.IsPrefixApproximation
      ((P.boundaryIndex z).val + 2) (A * dP) := by
    rw [hstart, hleftDet] at hseed
    exact hseed
  obtain ⟨s, hs⟩ :=
    P.boundaryPrefixDiagonalUnits_eq_refinedDeterminant_mul_square z
  have hdet : diagonalUnitDeterminant
      (P.boundaryOneAfterDiagonalUnits z A) = (A * dP) * s ^ 2 := by
    unfold boundaryOneAfterDiagonalUnits
    rw [diagonalUnitDeterminant_snoc, hs]
    dsimp only [dP, J]
    ac_rfl
  rw [hdet]
  apply (a.isPrefixApproximation_mul_square_iff
    ((P.boundaryOneAfterIndex z hrank).val + 1) (A * dP) s).2
  simpa only [boundaryOneAfterIndex] using hbase

set_option maxHeartbeats 0 in
/-- Beli (2019), Lemma 3.4(ii): one place after a full Jordan boundary,
the prefix space enlarged by a norm-generator line is a left space
approximation. -/
theorem beli2019Lemma34_ii
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (z : Fin t) (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice
        (Lattice.JordanDecomposition.boundaryRightIndex z)) A)
    (hrank : 1 < (W.toJordan hstrict).componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex z)) :
    a.IsLeftSpaceApproximation (P.boundaryOneAfterIndex z hrank)
      (P.boundaryOneAfterDiagonalUnits z A) := by
  let J := W.toJordan hstrict
  let C := PrescribedJordanComparison.ofProfile a J
  constructor
  · exact boundaryOneAfterDiagonalUnits_isPrefixApproximation
      a W hW hstrict P z A hA hrank
  · exact C.oneAfter_leftRepresentation P z A hA hrank

end PrescribedJordanComparison

end BONG.JordanOrderProfileWitness

end Bong
