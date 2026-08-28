/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.MatrixCongruence
import Bong.Lattice.Omeara9328NecessityResidualIsometry
import Bong.Lattice.Omeara9328NormalizedFirstComponents

/-!
# O'Meara 93:28 necessity: projection to the first residual component

An integral isometry of the complete rank-four residual products need not
preserve their Jordan components.  We embed the source first component,
apply the isometry, and retain the first target coordinate.  The resulting
linear map is integral.  Its discarded coordinates are one scale deeper,
so normalized pairings change only by an element of the maximal ideal.
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

/-- Identify the displayed source first component with its raw residual
block. -/
noncomputable def sourceHeadToRawIsometry :
    Isometry (S.sourceJordan.component 0).space (S.sourceForm 0)
      (S.sourceJordan.component 0).lattice (S.sourceLattice 0) :=
  (BONG.blockProductComponentIsometry S.sourceCarrier S.sourceForm
    S.sourceLattice 0).symm

/-- Identify the raw target first residual block with the displayed target
first component. -/
noncomputable def targetRawToHeadIsometry :
    Isometry (S.targetForm 0) (S.targetJordan.component 0).space
      (S.targetLattice 0) (S.targetJordan.component 0).lattice :=
  BONG.blockProductComponentIsometry S.targetCarrier S.targetForm
    S.targetLattice 0

/-- Embed a source-head vector as the zeroth coordinate of the complete
source residual product. -/
noncomputable def sourceHeadEmbedding :
    (S.sourceJordan.component 0).carrier →ₗ[K]
      BONG.BlockProductSpace (n + 1) S.sourceCarrier where
  toFun := fun x ↦ Pi.single 0 (S.sourceHeadToRawIsometry.toLinearEquiv x)
  map_add' := by
    classical
    intro x y
    ext i
    by_cases hi : i = (0 : Fin (n + 2))
    · subst i
      simp
    · simp [Pi.single_eq_of_ne hi]
  map_smul' := by
    classical
    intro c x
    ext i
    by_cases hi : i = (0 : Fin (n + 2))
    · subst i
      simp
    · simp [Pi.single_eq_of_ne hi]

/-- Project an arbitrary residual-product isometry to its target first
coordinate. -/
noncomputable def firstProjectionMap
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    (S.sourceJordan.component 0).carrier →ₗ[K]
      (S.targetJordan.component 0).carrier where
  toFun := fun x ↦ S.targetRawToHeadIsometry.toLinearEquiv
    (f.toLinearEquiv (S.sourceHeadEmbedding x) 0)
  map_add' := by
    intro x y
    simp only [map_add, Pi.add_apply]
  map_smul' := by
    intro c x
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

@[simp]
theorem firstProjectionMap_apply
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (x : (S.sourceJordan.component 0).carrier) :
    S.firstProjectionMap f x =
      S.targetRawToHeadIsometry.toLinearEquiv
        (f.toLinearEquiv (S.sourceHeadEmbedding x) 0) :=
  rfl

/-- The zeroth-coordinate embedding carries the displayed source-head
lattice into the complete source product lattice. -/
theorem sourceHeadEmbedding_mem
    {x : (S.sourceJordan.component 0).carrier}
    (hx : x ∈ (S.sourceJordan.component 0).lattice) :
    S.sourceHeadEmbedding x ∈
      BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice := by
  classical
  rw [BONG.mem_blockProductLattice_iff]
  intro i
  by_cases hi : i = (0 : Fin (n + 2))
  · subst i
    simp only [sourceHeadEmbedding, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.single_eq_same]
    exact (S.sourceHeadToRawIsometry.map_mem x).mp hx
  · simp [sourceHeadEmbedding, Pi.single_eq_of_ne hi]

/-- The first projected coordinate of an integral source-head vector is
integral in the target head. -/
theorem firstProjectionMap_mem
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    {x : (S.sourceJordan.component 0).carrier}
    (hx : x ∈ (S.sourceJordan.component 0).lattice) :
    S.firstProjectionMap f x ∈ (S.targetJordan.component 0).lattice := by
  have hfull : f.toLinearEquiv (S.sourceHeadEmbedding x) ∈
      BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice :=
    (f.map_mem (S.sourceHeadEmbedding x)).mp (S.sourceHeadEmbedding_mem hx)
  have hraw : f.toLinearEquiv (S.sourceHeadEmbedding x) 0 ∈
      S.targetLattice 0 :=
    (BONG.mem_blockProductLattice_iff (n + 1) S.targetCarrier
      S.targetLattice _).mp hfull 0
  exact (S.targetRawToHeadIsometry.map_mem _).mp hraw

/-- Every coordinate of the image of an integral source-head vector is
integral in the corresponding raw target residual lattice. -/
theorem targetResidualCoordinate_mem
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    {x : (S.sourceJordan.component 0).carrier}
    (hx : x ∈ (S.sourceJordan.component 0).lattice)
    (i : Fin (n + 2)) :
    f.toLinearEquiv (S.sourceHeadEmbedding x) i ∈ S.targetLattice i := by
  have hfull : f.toLinearEquiv (S.sourceHeadEmbedding x) ∈
      BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice :=
    (f.map_mem (S.sourceHeadEmbedding x)).mp (S.sourceHeadEmbedding_mem hx)
  exact (BONG.mem_blockProductLattice_iff (n + 1) S.targetCarrier
    S.targetLattice _).mp hfull i

/-- The source-head pairing is the target projected pairing plus the
pairings of all discarded coordinates. -/
theorem firstProjection_bilin_add_tail
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (x y : (S.sourceJordan.component 0).carrier) :
    (S.targetJordan.component 0).space.bilin
        (S.firstProjectionMap f x) (S.firstProjectionMap f y) +
      ∑ i : Fin (n + 1),
        (S.targetForm i.succ).bilin
          (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ)
          (f.toLinearEquiv (S.sourceHeadEmbedding y) i.succ) =
      (S.sourceJordan.component 0).space.bilin x y := by
  classical
  calc
    (S.targetJordan.component 0).space.bilin
          (S.firstProjectionMap f x) (S.firstProjectionMap f y) +
        ∑ i : Fin (n + 1),
          (S.targetForm i.succ).bilin
            (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ)
            (f.toLinearEquiv (S.sourceHeadEmbedding y) i.succ) =
        (S.targetForm 0).bilin
            (f.toLinearEquiv (S.sourceHeadEmbedding x) 0)
            (f.toLinearEquiv (S.sourceHeadEmbedding y) 0) +
          ∑ i : Fin (n + 1),
            (S.targetForm i.succ).bilin
              (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ)
              (f.toLinearEquiv (S.sourceHeadEmbedding y) i.succ) := by
      simp only [firstProjectionMap, LinearMap.coe_mk, AddHom.coe_mk]
      rw [S.targetRawToHeadIsometry.map_bilin]
    _ = (BONG.blockOrthogonalForm (n + 1) S.targetCarrier
          S.targetForm).bilin
          (f.toLinearEquiv (S.sourceHeadEmbedding x))
          (f.toLinearEquiv (S.sourceHeadEmbedding y)) := by
      rw [BONG.blockOrthogonalForm_bilin_apply]
      exact (Fin.sum_univ_succ (fun i : Fin (n + 2) ↦
        (S.targetForm i).bilin
          (f.toLinearEquiv (S.sourceHeadEmbedding x) i)
          (f.toLinearEquiv (S.sourceHeadEmbedding y) i))).symm
    _ = (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier
          S.sourceForm).bilin
          (S.sourceHeadEmbedding x) (S.sourceHeadEmbedding y) :=
      f.map_bilin _ _
    _ = (S.sourceForm 0).bilin
          (S.sourceHeadToRawIsometry.toLinearEquiv x)
          (S.sourceHeadToRawIsometry.toLinearEquiv y) := by
      rw [BONG.blockOrthogonalForm_bilin_apply]
      apply Finset.sum_eq_single 0
      · intro i _ hi
        simp [sourceHeadEmbedding, Pi.single_eq_of_ne hi]
      · simp
    _ = (S.sourceJordan.component 0).space.bilin x y :=
      S.sourceHeadToRawIsometry.map_bilin x y

/-- A discarded target coordinate pairing, after normalizing by the first
Jordan scale, lies in the maximal ideal. -/
theorem normalizedTailPairing_isInMaximalIdeal
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    {x y : (S.sourceJordan.component 0).carrier}
    (hx : x ∈ (S.sourceJordan.component 0).lattice)
    (hy : y ∈ (S.sourceJordan.component 0).lattice)
    (i : Fin (n + 1)) :
    IsInMaximalIdeal K
      (((S.firstScale⁻¹ : Kˣ) : K) *
        (S.targetForm i.succ).bilin
          (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ)
          (f.toLinearEquiv (S.sourceHeadEmbedding y) i.succ)) := by
  let z := f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ
  let t := f.toLinearEquiv (S.sourceHeadEmbedding y) i.succ
  have hz : z ∈ S.targetLattice i.succ :=
    S.targetResidualCoordinate_mem f hx i.succ
  have ht : t ∈ S.targetLattice i.succ :=
    S.targetResidualCoordinate_mem f hy i.succ
  have hpair : (S.targetForm i.succ).bilin z t ∈
      principalIdeal (K := K) (J.scaleGenerator i.succ : K) := by
    rw [← S.target_scaleIdeal_eq i.succ]
    exact bilin_mem_scaleIdeal_of_mem (S.targetForm i.succ)
      (S.targetLattice i.succ) hz ht
  rw [principalIdeal_eq_powerIdeal, mem_powerIdeal_iff] at hpair
  have hscale : ordUnit K S.firstScale <
      ordUnit K (J.scaleGenerator i.succ) := by
    exact J.scaleOrder_strict (by simp)
  unfold IsInMaximalIdeal
  rw [ord_mul, ← coe_ordUnit, ordUnit_inv]
  have hpositive : (0 : Int) <
      -ordUnit K S.firstScale + ordUnit K (J.scaleGenerator i.succ) := by
    omega
  calc
    (0 : WithTop Int) <
        ((-ordUnit K S.firstScale +
          ordUnit K (J.scaleGenerator i.succ) : Int) : WithTop Int) :=
      WithTop.coe_lt_coe.mpr hpositive
    _ = ((-ordUnit K S.firstScale : Int) : WithTop Int) +
        ((ordUnit K (J.scaleGenerator i.succ) : Int) : WithTop Int) := by
      norm_cast
    _ ≤ ((-ordUnit K S.firstScale : Int) : WithTop Int) +
        ord K ((S.targetForm i.succ).bilin z t) :=
      by
        simpa only [add_comm] using
          add_le_add_right hpair
            ((-ordUnit K S.firstScale : Int) : WithTop Int)

/-- The preceding tail estimate before forgetting its exact depth: every
discarded normalized pairing lies in the principal ideal of the relative
second Jordan scale. -/
theorem normalizedTailPairing_mem_relativeSecondScaleIdeal
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    {x y : (S.sourceJordan.component 0).carrier}
    (hx : x ∈ (S.sourceJordan.component 0).lattice)
    (hy : y ∈ (S.sourceJordan.component 0).lattice)
    (i : Fin (n + 1)) :
    ((S.firstScale⁻¹ : Kˣ) : K) *
        (S.targetForm i.succ).bilin
          (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ)
          (f.toLinearEquiv (S.sourceHeadEmbedding y) i.succ) ∈
      principalIdeal (K := K) (S.relativeSecondScale : K) := by
  let z := f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ
  let t := f.toLinearEquiv (S.sourceHeadEmbedding y) i.succ
  have hz : z ∈ S.targetLattice i.succ :=
    S.targetResidualCoordinate_mem f hx i.succ
  have ht : t ∈ S.targetLattice i.succ :=
    S.targetResidualCoordinate_mem f hy i.succ
  have hpair : (S.targetForm i.succ).bilin z t ∈
      principalIdeal (K := K) (J.scaleGenerator i.succ : K) := by
    rw [← S.target_scaleIdeal_eq i.succ]
    exact bilin_mem_scaleIdeal_of_mem (S.targetForm i.succ)
      (S.targetLattice i.succ) hz ht
  rw [principalIdeal_eq_powerIdeal, mem_powerIdeal_iff] at hpair ⊢
  rw [ord_mul, ← coe_ordUnit, ordUnit_inv,
    relativeSecondScale, ordUnit_mul, ordUnit_inv]
  have hscale : ordUnit K (J.scaleGenerator 1) ≤
      ordUnit K (J.scaleGenerator i.succ) := by
    by_cases hi : i.succ = (1 : Fin (n + 2))
    · rw [hi]
    · exact (J.scaleOrder_strict (by
        have hone : (1 : Fin (n + 2)) ≤ i.succ := by
          rw [Fin.le_iff_val_le_val]
          simp
        exact lt_of_le_of_ne hone (Ne.symm hi))).le
  have hscaleTop :
      (ordUnit K (J.scaleGenerator 1) : WithTop Int) ≤
        ord K ((S.targetForm i.succ).bilin z t) := by
    exact (WithTop.coe_le_coe.mpr hscale).trans hpair
  dsimp only [z, t] at hscaleTop
  calc
    ((-ordUnit K S.firstScale +
        ordUnit K (J.scaleGenerator 1) : Int) : WithTop Int) =
        (ordUnit K (J.scaleGenerator 1) : WithTop Int) +
          ((-ordUnit K S.firstScale : Int) : WithTop Int) := by
      norm_cast
      ring
    _ ≤ ord K ((S.targetForm i.succ).bilin
          (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ)
          (f.toLinearEquiv (S.sourceHeadEmbedding y) i.succ)) +
        ((-ordUnit K S.firstScale : Int) : WithTop Int) :=
      by
        simpa only [add_comm] using
          add_le_add_right hscaleTop
            ((-ordUnit K S.firstScale : Int) : WithTop Int)
    _ = ((-ordUnit K S.firstScale : Int) : WithTop Int) +
        ord K ((S.targetForm i.succ).bilin
          (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ)
          (f.toLinearEquiv (S.sourceHeadEmbedding y) i.succ)) := by
      rw [add_comm]

/-- Exact ideal-valued version of the normalized Gram congruence. -/
theorem normalizedFirstProjection_bilin_sub_mem_relativeSecondScaleIdeal
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    {x y : (S.sourceJordan.component 0).carrier}
    (hx : x ∈ (S.sourceJordan.component 0).lattice)
    (hy : y ∈ (S.sourceJordan.component 0).lattice) :
    S.targetFirstNormalized.bilin
          (S.firstProjectionMap f x) (S.firstProjectionMap f y) -
        S.sourceFirstNormalized.bilin x y ∈
      principalIdeal (K := K) (S.relativeSecondScale : K) := by
  have htail :
      ∑ i : Fin (n + 1),
        ((S.firstScale⁻¹ : Kˣ) : K) *
          (S.targetForm i.succ).bilin
            (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ)
            (f.toLinearEquiv (S.sourceHeadEmbedding y) i.succ) ∈
        principalIdeal (K := K) (S.relativeSecondScale : K) := by
    apply Submodule.sum_mem
    intro i _
    exact S.normalizedTailPairing_mem_relativeSecondScaleIdeal f hx hy i
  have hneg :=
    (principalIdeal (K := K) (S.relativeSecondScale : K)).neg_mem htail
  have hsplit := S.firstProjection_bilin_add_tail f x y
  simp only [sourceFirstNormalized, targetFirstNormalized,
    QuadraticSpace.rescaleUnit_bilin_apply]
  convert hneg using 1
  rw [← Finset.mul_sum]
  linear_combination ((S.firstScale⁻¹ : Kˣ) : K) * hsplit

/-- The normalized target projected pairing is congruent to the normalized
source-head pairing modulo the maximal ideal. -/
theorem normalizedFirstProjection_bilin_sub_isInMaximalIdeal
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    {x y : (S.sourceJordan.component 0).carrier}
    (hx : x ∈ (S.sourceJordan.component 0).lattice)
    (hy : y ∈ (S.sourceJordan.component 0).lattice) :
    IsInMaximalIdeal K
      (S.targetFirstNormalized.bilin
          (S.firstProjectionMap f x) (S.firstProjectionMap f y) -
        S.sourceFirstNormalized.bilin x y) := by
  have htail : IsInMaximalIdeal K
      (∑ i : Fin (n + 1),
        ((S.firstScale⁻¹ : Kˣ) : K) *
          (S.targetForm i.succ).bilin
            (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ)
            (f.toLinearEquiv (S.sourceHeadEmbedding y) i.succ)) := by
    apply isInMaximalIdeal_finset_sum Finset.univ
    intro i _
    exact S.normalizedTailPairing_isInMaximalIdeal f hx hy i
  have hneg : IsInMaximalIdeal K
      (-∑ i : Fin (n + 1),
        ((S.firstScale⁻¹ : Kˣ) : K) *
          (S.targetForm i.succ).bilin
            (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ)
            (f.toLinearEquiv (S.sourceHeadEmbedding y) i.succ)) := by
    unfold IsInMaximalIdeal at htail ⊢
    rw [ord_neg]
    exact htail
  have hsplit := S.firstProjection_bilin_add_tail f x y
  simp only [sourceFirstNormalized, targetFirstNormalized,
    QuadraticSpace.rescaleUnit_bilin_apply]
  convert hneg using 1
  rw [← Finset.mul_sum]
  linear_combination ((S.firstScale⁻¹ : Kˣ) : K) * hsplit

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
