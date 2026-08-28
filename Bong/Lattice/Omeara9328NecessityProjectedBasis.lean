/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328NecessityProjectionData
import Bong.Lattice.OrthogonalDecompositionVolume
import Bong.Lattice.VolumeRigidity

/-!
# O'Meara 93:28 necessity: the projected vectors form an integral basis

Let an integral basis of the normalized source rank-four head be embedded
in the complete residual product, carried across a residual isometry, and
projected to the target head.  The preceding projection calculation says
that the two normalized Gram matrices are entrywise congruent modulo the
maximal ideal.  The source determinant is a valuation unit, hence so is the
projected determinant.  The projected vectors are therefore a field basis.
They are integral and their basis lattice has the same volume as the
unimodular target head, so volume rigidity shows that they are an integral
basis of the target head.

The construction is parametrized by an arbitrary integral source basis.
This is important in the strict-order branch of 93:28, where the basis will
later be chosen in the paper's adapted form `A(a,0) ⊥ A(a',0)`.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- The four vectors obtained by projecting an integral source-head basis
through a residual-product isometry. -/
noncomputable def projectedHeadFamily
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    Fin 4 → (S.targetJordan.component 0).carrier :=
  fun i ↦ S.firstProjectionMap f (b i)

@[simp]
theorem projectedHeadFamily_apply
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin 4) :
    S.projectedHeadFamily b f i = S.firstProjectionMap f (b i) :=
  rfl

/-- The normalized Gram matrix of the chosen source-head basis. -/
noncomputable def sourceHeadNormalizedGramMatrix
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier) :
    Matrix (Fin 4) (Fin 4) K :=
  LinearMap.BilinForm.toMatrix b S.sourceFirstNormalized.bilin

/-- The normalized Gram matrix of the projected family in the target head. -/
noncomputable def projectedHeadNormalizedGramMatrix
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    Matrix (Fin 4) (Fin 4) K :=
  fun i j ↦ S.targetFirstNormalized.bilin
    (S.projectedHeadFamily b f i) (S.projectedHeadFamily b f j)

/-- A basis vector belongs to its basis lattice, transported across a
specified identification with the source-head lattice. -/
theorem sourceHeadBasis_mem
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier)
    (hb : Lattice.basisLattice b =
      (S.sourceJordan.component 0).lattice)
    (i : Fin 4) :
    b i ∈ (S.sourceJordan.component 0).lattice := by
  rw [← hb]
  change b i ∈ Submodule.span (IntegerRing K) (Set.range b)
  exact Submodule.subset_span ⟨i, rfl⟩

/-- Every source normalized Gram entry is integral. -/
theorem sourceHeadNormalizedGramMatrix_isIntegral
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier)
    (hb : Lattice.basisLattice b =
      (S.sourceJordan.component 0).lattice)
    (i j : Fin 4) :
    Dyadic.IsIntegral K (S.sourceHeadNormalizedGramMatrix b i j) := by
  apply (mem_integerRing_iff K).1
  apply Lattice.mem_integerRing_of_mul_mem_principalIdeal
    (one_ne_zero : (1 : K) ≠ 0)
  have hpair := Lattice.bilin_mem_scaleIdeal_of_mem
    S.sourceFirstNormalized (S.sourceJordan.component 0).lattice
    (S.sourceHeadBasis_mem b hb i) (S.sourceHeadBasis_mem b hb j)
  rw [S.sourceFirstNormalized_unimodular.scaleIdeal_eq_principal
    (by rw [S.sourceFirstNormalized_finrank]; omega)] at hpair
  have hpair' : (1 : K) * S.sourceHeadNormalizedGramMatrix b i j ∈
      Lattice.principalIdeal (K := K) (1 : K) := by
    convert hpair using 1 <;>
      simp [sourceHeadNormalizedGramMatrix]
  exact hpair'

/-- Every projected normalized Gram entry is integral. -/
theorem projectedHeadNormalizedGramMatrix_isIntegral
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier)
    (hb : Lattice.basisLattice b =
      (S.sourceJordan.component 0).lattice)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i j : Fin 4) :
    Dyadic.IsIntegral K (S.projectedHeadNormalizedGramMatrix b f i j) := by
  apply (mem_integerRing_iff K).1
  apply Lattice.mem_integerRing_of_mul_mem_principalIdeal
    (one_ne_zero : (1 : K) ≠ 0)
  have hi : S.projectedHeadFamily b f i ∈
      (S.targetJordan.component 0).lattice :=
    S.firstProjectionMap_mem f (S.sourceHeadBasis_mem b hb i)
  have hj : S.projectedHeadFamily b f j ∈
      (S.targetJordan.component 0).lattice :=
    S.firstProjectionMap_mem f (S.sourceHeadBasis_mem b hb j)
  have hpair := Lattice.bilin_mem_scaleIdeal_of_mem
    S.targetFirstNormalized (S.targetJordan.component 0).lattice hi hj
  rw [S.targetFirstNormalized_unimodular.scaleIdeal_eq_principal
    (by rw [S.targetFirstNormalized_finrank]; omega)] at hpair
  have hpair' : (1 : K) * S.projectedHeadNormalizedGramMatrix b f i j ∈
      Lattice.principalIdeal (K := K) (1 : K) := by
    convert hpair using 1 <;>
      simp [projectedHeadNormalizedGramMatrix]
  exact hpair'

/-- The projected and source Gram matrices are entrywise congruent modulo
the principal ideal of the relative second Jordan scale. -/
theorem projectedHeadNormalizedGramMatrix_sub_source_mem_relativeSecondScaleIdeal
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier)
    (hb : Lattice.basisLattice b =
      (S.sourceJordan.component 0).lattice)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i j : Fin 4) :
    S.projectedHeadNormalizedGramMatrix b f i j -
        S.sourceHeadNormalizedGramMatrix b i j ∈
      Lattice.principalIdeal (K := K) (S.relativeSecondScale : K) := by
  simpa only [projectedHeadNormalizedGramMatrix, projectedHeadFamily,
    sourceHeadNormalizedGramMatrix,
    LinearMap.BilinForm.toMatrix_apply] using
      S.normalizedFirstProjection_bilin_sub_mem_relativeSecondScaleIdeal f
        (S.sourceHeadBasis_mem b hb i) (S.sourceHeadBasis_mem b hb j)

/-- Consequently the normalized Gram determinants are congruent at the
same exact Jordan-scale depth. -/
theorem projectedHeadNormalizedGramDet_sub_source_mem_relativeSecondScaleIdeal
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier)
    (hb : Lattice.basisLattice b =
      (S.sourceJordan.component 0).lattice)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    (S.projectedHeadNormalizedGramMatrix b f).det -
        (S.sourceHeadNormalizedGramMatrix b).det ∈
      Lattice.principalIdeal (K := K) (S.relativeSecondScale : K) := by
  apply mem_coefficientIdeal_det_sub_det
  · exact S.projectedHeadNormalizedGramMatrix_isIntegral b hb f
  · exact S.sourceHeadNormalizedGramMatrix_isIntegral b hb
  · exact
      S.projectedHeadNormalizedGramMatrix_sub_source_mem_relativeSecondScaleIdeal
        b hb f

/-- The projected and source Gram matrices are entrywise congruent modulo
the maximal ideal. -/
theorem projectedHeadNormalizedGramMatrix_sub_source_isInMaximalIdeal
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier)
    (hb : Lattice.basisLattice b =
      (S.sourceJordan.component 0).lattice)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i j : Fin 4) :
    IsInMaximalIdeal K
      (S.projectedHeadNormalizedGramMatrix b f i j -
        S.sourceHeadNormalizedGramMatrix b i j) := by
  simpa only [projectedHeadNormalizedGramMatrix, projectedHeadFamily,
    sourceHeadNormalizedGramMatrix,
    LinearMap.BilinForm.toMatrix_apply] using
      S.normalizedFirstProjection_bilin_sub_isInMaximalIdeal f
        (S.sourceHeadBasis_mem b hb i) (S.sourceHeadBasis_mem b hb j)

/-- The two normalized Gram determinants are congruent modulo the maximal
ideal. -/
theorem projectedHeadNormalizedGramDet_sub_source_isInMaximalIdeal
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier)
    (hb : Lattice.basisLattice b =
      (S.sourceJordan.component 0).lattice)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    IsInMaximalIdeal K
      ((S.projectedHeadNormalizedGramMatrix b f).det -
        (S.sourceHeadNormalizedGramMatrix b).det) := by
  apply isInMaximalIdeal_det_sub_det
  · exact S.projectedHeadNormalizedGramMatrix_isIntegral b hb f
  · exact S.sourceHeadNormalizedGramMatrix_isIntegral b hb
  · exact S.projectedHeadNormalizedGramMatrix_sub_source_isInMaximalIdeal
      b hb f

/-- The normalized source Gram determinant of an integral basis is a
valuation unit. -/
theorem sourceHeadNormalizedGramDet_isValuationUnit
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier)
    (hb : Lattice.basisLattice b =
      (S.sourceJordan.component 0).lattice) :
    IsValuationUnit K (S.sourceHeadNormalizedGramMatrix b).det := by
  unfold IsValuationUnit
  change ord K
      (LinearMap.BilinForm.toMatrix b S.sourceFirstNormalized.bilin).det = 0
  rw [← Lattice.coe_volumeOrder_basisLattice_eq_ord_det_toMatrix,
    hb, S.sourceFirstNormalized_unimodular.volumeOrder_eq]
  simp

/-- Hence the projected normalized Gram determinant is a valuation unit. -/
theorem projectedHeadNormalizedGramDet_isValuationUnit
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier)
    (hb : Lattice.basisLattice b =
      (S.sourceJordan.component 0).lattice)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    IsValuationUnit K (S.projectedHeadNormalizedGramMatrix b f).det :=
  isValuationUnit_of_sub_isInMaximalIdeal
    (S.sourceHeadNormalizedGramDet_isValuationUnit b hb)
    (S.projectedHeadNormalizedGramDet_sub_source_isInMaximalIdeal b hb f)

/-- The four projected vectors are linearly independent. -/
theorem projectedHeadFamily_linearIndependent
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier)
    (hb : Lattice.basisLattice b =
      (S.sourceJordan.component 0).lattice)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    LinearIndependent K (S.projectedHeadFamily b f) := by
  apply Bong.linearIndependent_of_bilinMatrix_det_ne_zero
    S.targetFirstNormalized.bilin (S.projectedHeadFamily b f)
  change (S.projectedHeadNormalizedGramMatrix b f).det ≠ 0
  exact Lattice.ne_zero_of_isValuationUnit
    (S.projectedHeadNormalizedGramDet_isValuationUnit b hb f)

/-- The ambient field basis furnished by the projected family. -/
noncomputable def projectedHeadBasis
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier)
    (hb : Lattice.basisLattice b =
      (S.sourceJordan.component 0).lattice)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    Basis (Fin 4) K (S.targetJordan.component 0).carrier := by
  letI : Module.Finite K (S.targetJordan.component 0).carrier :=
    (S.targetJordan.component 0).lattice.moduleFinite
  exact basisOfLinearIndependentOfCardEqFinrank'
      (S.projectedHeadFamily b f)
      (S.projectedHeadFamily_linearIndependent b hb f)
      (by simpa using S.targetFirstNormalized_finrank.symm)

@[simp]
theorem projectedHeadBasis_apply
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier)
    (hb : Lattice.basisLattice b =
      (S.sourceJordan.component 0).lattice)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin 4) :
    S.projectedHeadBasis b hb f i = S.projectedHeadFamily b f i := by
  simp [projectedHeadBasis]

/-- Every projected basis vector is integral in the target head. -/
theorem projectedHeadBasis_mem
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier)
    (hb : Lattice.basisLattice b =
      (S.sourceJordan.component 0).lattice)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin 4) :
    S.projectedHeadBasis b hb f i ∈
      (S.targetJordan.component 0).lattice := by
  rw [S.projectedHeadBasis_apply b hb f]
  exact S.firstProjectionMap_mem f (S.sourceHeadBasis_mem b hb i)

/-- The lattice generated by the projected basis is contained in the
target head. -/
theorem projectedHeadBasisLattice_le
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier)
    (hb : Lattice.basisLattice b =
      (S.sourceJordan.component 0).lattice)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    Lattice.basisLattice (S.projectedHeadBasis b hb f) ≤
      (S.targetJordan.component 0).lattice := by
  change Submodule.span (IntegerRing K)
      (Set.range (S.projectedHeadBasis b hb f)) ≤
    (S.targetJordan.component 0).lattice.toSubmodule
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact S.projectedHeadBasis_mem b hb f i

/-- The projected basis lattice has volume order zero. -/
theorem projectedHeadBasisLattice_volumeOrder_eq_zero
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier)
    (hb : Lattice.basisLattice b =
      (S.sourceJordan.component 0).lattice)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    Lattice.volumeOrder S.targetFirstNormalized
      (Lattice.basisLattice (S.projectedHeadBasis b hb f)) = 0 := by
  apply WithTop.coe_injective
  rw [Lattice.coe_volumeOrder_basisLattice_eq_ord_det_toMatrix]
  have hmatrix :
      LinearMap.BilinForm.toMatrix (S.projectedHeadBasis b hb f)
          S.targetFirstNormalized.bilin =
        S.projectedHeadNormalizedGramMatrix b f := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply,
      projectedHeadNormalizedGramMatrix, projectedHeadBasis_apply]
  rw [hmatrix]
  exact S.projectedHeadNormalizedGramDet_isValuationUnit b hb f

/-- The projected vectors are an integral basis of the target head. -/
theorem projectedHeadBasisLattice_eq
    (b : Basis (Fin 4) K (S.sourceJordan.component 0).carrier)
    (hb : Lattice.basisLattice b =
      (S.sourceJordan.component 0).lattice)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    Lattice.basisLattice (S.projectedHeadBasis b hb f) =
      (S.targetJordan.component 0).lattice := by
  apply Lattice.eq_of_le_of_volumeOrder_eq S.targetFirstNormalized
    (Lattice.basisLattice (S.projectedHeadBasis b hb f))
    (S.targetJordan.component 0).lattice
    (S.projectedHeadBasisLattice_le b hb f)
  rw [S.projectedHeadBasisLattice_volumeOrder_eq_zero b hb f,
    S.targetFirstNormalized_unimodular.volumeOrder_eq]
  have honeOrder : ordUnit K (1 : Kˣ) = 0 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    simp
  rw [honeOrder]
  ring

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
