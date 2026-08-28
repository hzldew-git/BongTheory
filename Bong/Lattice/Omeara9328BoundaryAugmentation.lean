/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328BoundaryEnvelope
import Bong.Lattice.Omeara9328RankFourPrefixes
import Bong.Lattice.OrthogonalDecompositionAppend
import Bong.Lattice.OrthogonalProductDecomposition
import Bong.Lattice.ProjectionScaling
import Bong.Lattice.OmearaModularSingleTruncation
import Bong.Lattice.ScaleTruncationIsometry
import Bong.Lattice.OrthogonalPrefixSimultaneousSplitting
import Bong.Lattice.JordanInitialSegment
import Bong.Lattice.OrthogonalDecompositionScaleTruncationVolume
import Bong.Lattice.OrthogonalDecompositionRankSum
import Bong.Lattice.OrthogonalDecompositionVolumeSum
import Bong.Lattice.NormGroupRepresentation
import Bong.Lattice.Omeara9328IsometryReplacement
import Bong.Lattice.Omeara9328NecessityLastBoundary
import Bong.Lattice.OmearaFundamentalScaleNormAlgebra
import Bong.Lattice.Omeara9328ReverseDualCondition

/-!
# Boundary augmentation for O'Meara 93:28 necessity

This file implements Steps 2 and 3 of the necessity proof: a maximal
same-norm-group envelope turns an arbitrary boundary into the last boundary,
and reverse duality exchanges the two prefix-representation conditions.
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

/-- A modular lattice is unchanged by every scale truncation whose order is
at most its modular scale. -/
theorem scaleTruncation_eq_of_isModular_of_le
    {X : Type v} [AddCommGroup X] [Module K X]
    {p : QuadraticSpace K X} {A : Lattice K X} {s : Kˣ}
    (hA : IsModular p A s) (k : Int) (hk : k ≤ ordUnit K s) :
    scaleTruncation p A k = A := by
  rw [scaleTruncation_eq_rescale_of_isModular hA k]
  have hnonpos : ¬ 0 <
      ordUnit K (scaleTruncationUnit (K := K) k * s⁻¹) := by
    rw [ordUnit_mul, ordUnit_inv, scaleTruncationUnit,
      ordUnit_uniformizerPowerUnit]
    omega
  rw [positivePartUnit, if_neg hnonpos, rescale_one]

/-- Replacing either factor of an orthogonal product by a lattice with the
same scalar norm group preserves the norm group of the product. -/
theorem normGroupSet_orthogonalProduct_eq_of_factor_eq
    {X₁ X₂ Y₁ Y₂ : Type*}
    [AddCommGroup X₁] [Module K X₁]
    [AddCommGroup X₂] [Module K X₂]
    [AddCommGroup Y₁] [Module K Y₁]
    [AddCommGroup Y₂] [Module K Y₂]
    {p₁ : QuadraticSpace K X₁} {p₂ : QuadraticSpace K X₂}
    {s₁ : QuadraticSpace K Y₁} {s₂ : QuadraticSpace K Y₂}
    {A₁ : Lattice K X₁} {A₂ : Lattice K X₂}
    {B₁ : Lattice K Y₁} {B₂ : Lattice K Y₂}
    (hA : normGroupSet p₁ A₁ = normGroupSet p₂ A₂)
    (hB : normGroupSet s₁ B₁ = normGroupSet s₂ B₂) :
    normGroupSet (p₁.orthogonalSum s₁) (product A₁ B₁) =
      normGroupSet (p₂.orthogonalSum s₂) (product A₂ B₂) := by
  ext z
  rw [mem_normGroupSet_orthogonalProduct_iff,
    mem_normGroupSet_orthogonalProduct_iff, hA, hB]

/-- The one-boundary form of the reverse-dual determinant argument in
O'Meara 93:28.  Congruence for the complementary reverse-dual prefix implies
congruence for the original prefix. -/
theorem boundary_conditionI_of_reverseDual_boundary
    {J : JordanDecomposition q L (n + 2)}
    {H : JordanDecomposition r M (n + 2)}
    (f : Lattice.Isometry q r L M) (j : Fin (n + 1))
    (hrev : BONG.GoodBONG.UnitsCongruentModulo
      (H.reverseDual.prefixDeterminantUnit (Fin.rev j))
      (J.reverseDual.prefixDeterminantUnit (Fin.rev j))
      (J.reverseDual.fundamentalIdeal (Fin.rev j))) :
    BONG.GoodBONG.UnitsCongruentModulo
      (H.prefixDeterminantUnit j) (J.prefixDeterminantUnit j)
      (J.fundamentalIdeal j) := by
  let JP := J.toOrthogonalDecomposition
    |>.prefixQuadraticSublattice (j.val + 1)
  let HP := H.toOrthogonalDecomposition
    |>.prefixQuadraticSublattice (j.val + 1)
  let JS := J.toOrthogonalDecomposition
    |>.suffixQuadraticSublattice (j.val + 1)
  let HS := H.toOrthogonalDecomposition
    |>.suffixQuadraticSublattice (j.val + 1)
  let dJP : Kˣ := J.prefixDeterminantUnit j
  let dHP : Kˣ := H.prefixDeterminantUnit j
  let dJS : Kˣ := determinantUnit JS.space JS.lattice
  let dHS : Kˣ := determinantUnit HS.space HS.lattice
  rw [J.reverseDual_fundamentalIdeal, Fin.rev_rev] at hrev
  have hx : unitSquareClass K
        (H.reverseDual.prefixDeterminantUnit (Fin.rev j)) =
      unitSquareClass K dHS⁻¹ := by
    change determinantClass
        (H.reverseDual.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice ((Fin.rev j).val + 1)).space
        (H.reverseDual.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice ((Fin.rev j).val + 1)).lattice =
      (determinantClass HS.space HS.lattice)⁻¹
    exact H.reverseDualBoundaryPrefix_determinantClass j
  have hy : unitSquareClass K
        (J.reverseDual.prefixDeterminantUnit (Fin.rev j)) =
      unitSquareClass K dJS⁻¹ := by
    change determinantClass
        (J.reverseDual.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice ((Fin.rev j).val + 1)).space
        (J.reverseDual.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice ((Fin.rev j).val + 1)).lattice =
      (determinantClass JS.space JS.lattice)⁻¹
    exact J.reverseDualBoundaryPrefix_determinantClass j
  have hinv : BONG.GoodBONG.UnitsCongruentModulo
      dHS⁻¹ dJS⁻¹ (J.fundamentalIdeal j) :=
    BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
      (H.reverseDual.prefixDeterminantUnit (Fin.rev j)) dHS⁻¹
      (J.reverseDual.prefixDeterminantUnit (Fin.rev j)) dJS⁻¹
      (J.fundamentalIdeal j) hx hy hrev
  have hsuffix : BONG.GoodBONG.UnitsCongruentModulo
      dJS dHS (J.fundamentalIdeal j) :=
    (BONG.GoodBONG.unitsCongruentModulo_inv_swap_iff
      dHS dJS (J.fundamentalIdeal j)).1 hinv
  have hsplitJ : unitSquareClass K (dJP * dJS) =
      determinantClass q L := by
    rw [unitSquareClass_mul]
    change determinantClass JP.space JP.lattice *
      determinantClass JS.space JS.lattice = determinantClass q L
    have h := determinantClass_eq_of_isometry
      (J.toOrthogonalDecomposition.prefixSuffixLatticeIsometry
        (j.val + 1))
    rw [determinantClass_orthogonalProduct] at h
    exact h
  have hsplitH : unitSquareClass K (dHP * dHS) =
      determinantClass r M := by
    rw [unitSquareClass_mul]
    change determinantClass HP.space HP.lattice *
      determinantClass HS.space HS.lattice = determinantClass r M
    have h := determinantClass_eq_of_isometry
      (H.toOrthogonalDecomposition.prefixSuffixLatticeIsometry
        (j.val + 1))
    rw [determinantClass_orthogonalProduct] at h
    exact h
  have hwhole : unitSquareClass K (dJP * dJS) =
      unitSquareClass K (dHP * dHS) :=
    hsplitJ.trans ((determinantClass_eq_of_isometry f).trans hsplitH.symm)
  have hproduct : BONG.GoodBONG.UnitsCongruentModulo
      (dJP * dJS) (dJP * dHS) (J.fundamentalIdeal j) :=
    (BONG.GoodBONG.unitsCongruentModulo_mul_left_iff
      dJP dJS dHS (J.fundamentalIdeal j)).2 hsuffix
  have hreplaced : BONG.GoodBONG.UnitsCongruentModulo
      (dHP * dHS) (dJP * dHS) (J.fundamentalIdeal j) :=
    BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
      (dJP * dJS) (dHP * dHS) (dJP * dHS) (dJP * dHS)
      (J.fundamentalIdeal j) hwhole rfl hproduct
  have hcommon : BONG.GoodBONG.UnitsCongruentModulo
      (dHS * dHP) (dHS * dJP) (J.fundamentalIdeal j) := by
    simpa only [mul_comm] using hreplaced
  exact (BONG.GoodBONG.unitsCongruentModulo_mul_left_iff
    dHS dHP dJP (J.fundamentalIdeal j)).1 hcommon

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

noncomputable def liftNestedMapIsometry
    {X : Type v} [AddCommGroup X] [Module K X]
    {Y : Type v} [AddCommGroup Y] [Module K Y]
    {p : QuadraticSpace K X} {s : QuadraticSpace K Y}
    {A : Lattice K X}
    (P : QuadraticSublattice s)
    (f : Isometry p P.space A P.lattice)
    (C : QuadraticSublattice p) :
    Isometry C.space (P.liftNested (C.mapIsometry f)).space C.lattice
      (P.liftNested (C.mapIsometry f)).lattice :=
  (C.mapLatticeIsometry f).trans
    (P.liftNestedIsometry (C.mapIsometry f))

theorem boundaryPrefix_le
    (_S : Omeara9328RankFourReductionSystem J H)
    (i : Fin (n + 1)) :
    i.val + 1 ≤ n + 2 := by omega

abbrev boundaryPrefixCarrier (i : Fin (n + 1)) :=
  S.prefixSourceCarrier (S.boundaryPrefix_le i)

noncomputable abbrev boundaryPrefixForm (i : Fin (n + 1)) :=
  BONG.blockOrthogonalForm i.val (S.boundaryPrefixCarrier i)
    (S.prefixSourceForm (S.boundaryPrefix_le i))

noncomputable abbrev boundaryPrefixLattice (i : Fin (n + 1)) :=
  BONG.blockProductLattice i.val (S.boundaryPrefixCarrier i)
    (S.prefixSourceLattice (S.boundaryPrefix_le i))

/-- The source residual prefix, in the raw coordinate presentation already
used by the rank-four reduction. -/
noncomputable def boundaryPrefixJordan (i : Fin (n + 1)) :
    JordanDecomposition
      (S.boundaryPrefixForm i)
      (S.boundaryPrefixLattice i)
      (i.val + 1) :=
  BONG.blockProductJordanDecomposition
    (S.prefixSourceCarrier (S.boundaryPrefix_le i))
    (S.prefixSourceForm (S.boundaryPrefix_le i))
    (S.prefixSourceLattice (S.boundaryPrefix_le i))
    (fun j => J.scaleGenerator
      (S.prefixIndex (S.boundaryPrefix_le i) j))
    (fun j => S.sourceNormGenerator
      (S.prefixIndex (S.boundaryPrefix_le i) j))
    (fun j => S.source_modular
      (S.prefixIndex (S.boundaryPrefix_le i) j))
    (fun j => S.source_scaleIdeal_eq
      (S.prefixIndex (S.boundaryPrefix_le i) j))
    (fun j => S.source_normIdeal_eq
      (S.prefixIndex (S.boundaryPrefix_le i) j))
    (fun a b h => S.sourceJordan.scaleOrder_strict <| by
      change a.val < b.val at h
      show (S.prefixIndex (S.boundaryPrefix_le i) _).val <
        (S.prefixIndex (S.boundaryPrefix_le i) _).val
      simpa only [S.prefixIndex_val (S.boundaryPrefix_le i)] using h)

@[simp]
theorem boundaryPrefixJordan_scaleGenerator (i : Fin (n + 1))
    (j : Fin (i.val + 1)) :
    (S.boundaryPrefixJordan i).scaleGenerator j =
      J.scaleGenerator (S.prefixIndex (S.boundaryPrefix_le i) j) :=
  rfl

@[simp]
theorem boundaryPrefixJordan_normGenerator (i : Fin (n + 1))
    (j : Fin (i.val + 1)) :
    (S.boundaryPrefixJordan i).normGenerator j =
      S.sourceNormGenerator (S.prefixIndex (S.boundaryPrefix_le i) j) :=
  rfl

theorem boundarySuffix_finrank_pos (i : Fin (n + 1)) :
    0 < finrank K (S.boundarySuffix i).carrier := by
  have h := (S.boundarySuffixTowerIsometry i).toLinearEquiv.finrank_eq
  rw [QuadraticSpace.finrank_hyperbolicExtension_zero] at h
  rw [h]
  omega

abbrev boundarySuffixBlockCarrier (i : Fin (n + 1)) :=
  S.sourceJordan.toOrthogonalDecomposition.suffixBlockCarrier
    (S.boundarySuffix_cut_eq i)

noncomputable abbrev boundarySuffixBlockForm (i : Fin (n + 1)) :=
  S.sourceJordan.toOrthogonalDecomposition.suffixBlockSpace
    (S.boundarySuffix_cut_eq i)

noncomputable abbrev boundarySuffixBlockLattice (i : Fin (n + 1)) :=
  S.sourceJordan.toOrthogonalDecomposition.suffixBlockLattice
    (S.boundarySuffix_cut_eq i)

/-- The exact source suffix in standard block coordinates, retaining all
of its original Jordan components. -/
noncomputable def boundarySuffixJordan (i : Fin (n + 1)) :
    JordanDecomposition
      (BONG.blockOrthogonalForm (S.boundarySuffixPred i)
        (S.boundarySuffixBlockCarrier i) (S.boundarySuffixBlockForm i))
      (BONG.blockProductLattice (S.boundarySuffixPred i)
        (S.boundarySuffixBlockCarrier i) (S.boundarySuffixBlockLattice i))
      (S.boundarySuffixPred i + 1) := by
  let D := S.sourceJordan.toOrthogonalDecomposition
  let hcut := S.boundarySuffix_cut_eq i
  exact BONG.blockProductJordanDecomposition
    (D.suffixBlockCarrier hcut) (D.suffixBlockSpace hcut)
    (D.suffixBlockLattice hcut)
    (fun j => S.sourceJordan.scaleGenerator
      (D.suffixIndexEquiv hcut j).1)
    (fun j => S.sourceJordan.normGenerator
      (D.suffixIndexEquiv hcut j).1)
    (fun j => S.sourceJordan.modular (D.suffixIndexEquiv hcut j).1)
    (fun j => S.sourceJordan.scaleIdeal_eq (D.suffixIndexEquiv hcut j).1)
    (fun j => S.sourceJordan.normIdeal_eq (D.suffixIndexEquiv hcut j).1)
    (fun a b hab => S.sourceJordan.scaleOrder_strict <| by
      change a.val < b.val at hab
      change i.val + 1 + a.val < i.val + 1 + b.val
      omega)

@[simp]
theorem boundarySuffixJordan_scaleGenerator (i : Fin (n + 1))
    (j : Fin (S.boundarySuffixPred i + 1)) :
    (S.boundarySuffixJordan i).scaleGenerator j =
      J.scaleGenerator ⟨i.val + 1 + j.val, by
        have hcut := S.boundarySuffix_cut_eq i
        omega⟩ := by
  rfl

/-- Coordinate presentation of the exact source suffix. -/
noncomputable def boundarySuffixBlockIsometry (i : Fin (n + 1)) :
    Isometry
      (BONG.blockOrthogonalForm (S.boundarySuffixPred i)
        (S.boundarySuffixBlockCarrier i) (S.boundarySuffixBlockForm i))
      (S.boundarySuffix i).space
      (BONG.blockProductLattice (S.boundarySuffixPred i)
        (S.boundarySuffixBlockCarrier i) (S.boundarySuffixBlockLattice i))
      (S.boundarySuffix i).lattice :=
  S.sourceJordan.toOrthogonalDecomposition.suffixBlockProductIsometry
    (S.boundarySuffix_cut_eq i)

/-- Every component of the exact suffix has scale at least that of every
index at or before the selected boundary. -/
theorem boundaryScale_le_suffixScale (i : Fin (n + 1))
    (a : Fin (i.val + 2))
    (j : Fin (S.boundarySuffixPred i + 1)) :
    ordUnit K (J.scaleGenerator ⟨a.val, by omega⟩) ≤
      ordUnit K ((S.boundarySuffixJordan i).scaleGenerator j) := by
  rw [S.boundarySuffixJordan_scaleGenerator i j]
  let left : Fin (n + 2) := ⟨a.val, by omega⟩
  let right : Fin (n + 2) := ⟨i.val + 1 + j.val, by
    have hcut := S.boundarySuffix_cut_eq i
    omega⟩
  change ordUnit K (J.scaleGenerator left) ≤
    ordUnit K (J.scaleGenerator right)
  have hindex : left ≤ right := by
    change a.val ≤ i.val + 1 + j.val
    omega
  by_cases hEq : left = right
  · rw [hEq]
  · exact (J.scaleOrder_strict (lt_of_le_of_ne hindex hEq)).le

/-- Below the selected boundary scale the exact suffix is untouched by
scale truncation. -/
theorem boundarySuffixBlock_scaleTruncation_eq (i : Fin (n + 1))
    (a : Fin (i.val + 2)) :
    scaleTruncation
        (BONG.blockOrthogonalForm (S.boundarySuffixPred i)
          (S.boundarySuffixBlockCarrier i) (S.boundarySuffixBlockForm i))
        (BONG.blockProductLattice (S.boundarySuffixPred i)
          (S.boundarySuffixBlockCarrier i) (S.boundarySuffixBlockLattice i))
        (ordUnit K (J.scaleGenerator ⟨a.val, by omega⟩)) =
      BONG.blockProductLattice (S.boundarySuffixPred i)
        (S.boundarySuffixBlockCarrier i) (S.boundarySuffixBlockLattice i) := by
  let T := S.boundarySuffixJordan i
  rw [T.scaleTruncation_eq_componentwiseRescaleLattice]
  have hfactor : T.scaleTruncationFactor
      (ordUnit K (J.scaleGenerator ⟨a.val, by omega⟩)) = fun _ => 1 := by
    funext j
    unfold JordanDecomposition.scaleTruncationFactor positivePartUnit
    rw [if_neg]
    intro hpos
    rw [ordUnit_mul, ordUnit_inv, scaleTruncationUnit,
      ordUnit_uniformizerPowerUnit] at hpos
    have hle : ordUnit K (J.scaleGenerator ⟨a.val, by omega⟩) ≤
        ordUnit K (T.scaleGenerator j) := by
      simpa only [T] using S.boundaryScale_le_suffixScale i a j
    omega
  rw [hfactor, T.toOrthogonalDecomposition.componentwiseRescaleLattice_one]

/-- The intrinsic exact suffix is likewise unchanged below the boundary. -/
theorem boundarySuffix_scaleTruncation_eq (i : Fin (n + 1))
    (a : Fin (i.val + 2)) :
    scaleTruncation (S.boundarySuffix i).space
        (S.boundarySuffix i).lattice
        (ordUnit K (J.scaleGenerator ⟨a.val, by omega⟩)) =
      (S.boundarySuffix i).lattice := by
  let f := S.boundarySuffixBlockIsometry i
  have hmap := scaleTruncation_map_isometry f.toQuadraticSpaceIsometry
    (BONG.blockProductLattice (S.boundarySuffixPred i)
      (S.boundarySuffixBlockCarrier i) (S.boundarySuffixBlockLattice i))
    (ordUnit K (J.scaleGenerator ⟨a.val, by omega⟩))
  have hfmap : map f.toQuadraticSpaceIsometry.toLinearEquiv
      (BONG.blockProductLattice (S.boundarySuffixPred i)
        (S.boundarySuffixBlockCarrier i) (S.boundarySuffixBlockLattice i)) =
      (S.boundarySuffix i).lattice := by
    change map f.toLinearEquiv
      (BONG.blockProductLattice (S.boundarySuffixPred i)
        (S.boundarySuffixBlockCarrier i) (S.boundarySuffixBlockLattice i)) =
      (S.boundarySuffix i).lattice
    exact f.map_eq
  rw [hfmap, S.boundarySuffixBlock_scaleTruncation_eq i a, hfmap] at hmap
  exact hmap

theorem boundaryScale_le_rightScale (i : Fin (n + 1))
    (a : Fin (i.val + 2)) :
    ordUnit K (J.scaleGenerator ⟨a.val, by omega⟩) ≤
      ordUnit K (J.scaleGenerator (boundaryRightIndex i)) := by
  let left : Fin (n + 2) := ⟨a.val, by omega⟩
  let right : Fin (n + 2) := boundaryRightIndex i
  change ordUnit K (J.scaleGenerator left) ≤
    ordUnit K (J.scaleGenerator right)
  have hindex : left ≤ right := by
    change a.val ≤ i.val + 1
    omega
  by_cases hEq : left = right
  · rw [hEq]
  · exact (J.scaleOrder_strict (lt_of_le_of_ne hindex hEq)).le

/-- The modular 93:3 envelope is also untouched below the selected
boundary scale. -/
theorem boundarySuffixEnvelope_scaleTruncation_eq (i : Fin (n + 1))
    (a : Fin (i.val + 2)) :
    scaleTruncation (S.boundarySuffix i).space
        (S.boundarySuffixEnvelope i).lattice
        (ordUnit K (J.scaleGenerator ⟨a.val, by omega⟩)) =
      (S.boundarySuffixEnvelope i).lattice :=
  scaleTruncation_eq_of_isModular_of_le
    (S.boundarySuffixEnvelope i).modular _
      (boundaryScale_le_rightScale (J := J) i a)

noncomputable def boundaryEnvelopeNormVector (i : Fin (n + 1)) :
    (S.boundarySuffix i).carrier :=
  Classical.choose <| exists_isNormGenerator_of_finrank_pos
    (S.boundarySuffix i).space (S.boundarySuffixEnvelope i).lattice
      (S.boundarySuffix_finrank_pos i)

theorem boundaryEnvelopeNormVector_spec (i : Fin (n + 1)) :
    IsNormGenerator (S.boundarySuffix i).space
        (S.boundarySuffixEnvelope i).lattice
        (S.boundaryEnvelopeNormVector i) ∧
      (S.boundarySuffix i).space.IsAnisotropic
        (S.boundaryEnvelopeNormVector i) :=
  Classical.choose_spec <| exists_isNormGenerator_of_finrank_pos
    (S.boundarySuffix i).space (S.boundarySuffixEnvelope i).lattice
      (S.boundarySuffix_finrank_pos i)

noncomputable def boundaryEnvelopeNormGenerator (i : Fin (n + 1)) : Kˣ :=
  Units.mk0 ((S.boundarySuffix i).space.quadratic
      (S.boundaryEnvelopeNormVector i))
    (S.boundaryEnvelopeNormVector_spec i).2

/-- The canonical product splitting of the raw source prefix and the
norm-preserving modular suffix envelope. -/
noncomputable def boundaryAugmentedPair (i : Fin (n + 1)) :=
  orthogonalProductDecomposition
    (S.boundaryPrefixForm i)
    (S.boundarySuffix i).space
    (S.boundaryPrefixLattice i)
    (S.boundarySuffixEnvelope i).lattice

/-- The prefix Jordan decomposition transported to the left coordinate axis
of the augmented product. -/
noncomputable def boundaryAugmentedLeftJordan (i : Fin (n + 1)) :=
  (S.boundaryPrefixJordan i).mapIsometry <|
    orthogonalProductLeftComponentIsometry
      (S.boundaryPrefixForm i)
      (S.boundarySuffix i).space
      (S.boundaryPrefixLattice i)

/-- Orthogonal decomposition of the augmented product: the old prefix
components occur first and the modular envelope occurs last. -/
noncomputable def boundaryAugmentedOrthogonalDecomposition
    (i : Fin (n + 1)) :=
  (S.boundaryAugmentedPair i).appendNested
    (S.boundaryAugmentedLeftJordan i).toOrthogonalDecomposition

noncomputable def boundaryAugmentedScale (i : Fin (n + 1)) :
    Fin (i.val + 2) → Kˣ :=
  Fin.lastCases (J.scaleGenerator (boundaryRightIndex i))
    (fun j => J.scaleGenerator
      (S.prefixIndex (S.boundaryPrefix_le i) j))

noncomputable def boundaryAugmentedNorm (i : Fin (n + 1)) :
    Fin (i.val + 2) → Kˣ :=
  Fin.lastCases (S.boundaryEnvelopeNormGenerator i)
    (fun j => S.sourceNormGenerator
      (S.prefixIndex (S.boundaryPrefix_le i) j))

theorem boundaryAugmentedScale_eq_original (i : Fin (n + 1))
    (a : Fin (i.val + 2)) :
    S.boundaryAugmentedScale i a =
      J.scaleGenerator ⟨a.val, by omega⟩ := by
  refine Fin.lastCases ?_ (fun j => ?_) a
  · simp only [boundaryAugmentedScale, Fin.lastCases_last]
    congr 1
  · simp only [boundaryAugmentedScale, Fin.lastCases_castSucc]
    congr 1

theorem boundaryAugmentedScale_strict (i : Fin (n + 1))
    {a b : Fin (i.val + 2)} (hab : a < b) :
    ordUnit K (S.boundaryAugmentedScale i a) <
      ordUnit K (S.boundaryAugmentedScale i b) := by
  let idx : Fin (i.val + 2) → Fin (n + 2) :=
    fun j => ⟨j.val, by omega⟩
  have hidx : idx a < idx b := by simpa [idx] using hab
  have h := S.sourceJordan.scaleOrder_strict hidx
  rw [S.boundaryAugmentedScale_eq_original i,
    S.boundaryAugmentedScale_eq_original i]
  exact h

set_option synthInstance.maxHeartbeats 200000 in
/-- A prefix component is carried through the left-axis presentation and
the nested flattening without changing its integral quadratic lattice. -/
noncomputable def boundaryAugmentedPrefixComponentIsometry
    (i : Fin (n + 1)) (j : Fin (i.val + 1)) :
    Isometry
      ((S.boundaryPrefixJordan i).component j).space
      ((S.boundaryAugmentedOrthogonalDecomposition i).component
        j.castSucc).space
      ((S.boundaryPrefixJordan i).component j).lattice
      ((S.boundaryAugmentedOrthogonalDecomposition i).component
        j.castSucc).lattice := by
  let P := S.boundaryAugmentedPair i
  let left := orthogonalProductLeftComponentIsometry
    (S.boundaryPrefixForm i) (S.boundarySuffix i).space
    (S.boundaryPrefixLattice i)
  let combined := liftNestedMapIsometry (P.component 0) left
    ((S.boundaryPrefixJordan i).component j)
  rw [boundaryAugmentedOrthogonalDecomposition,
    OrthogonalDecomposition.appendNested_castSucc]
  change Isometry ((S.boundaryPrefixJordan i).component j).space
    ((P.component 0).liftNested
      (((S.boundaryPrefixJordan i).component j).mapIsometry left)).space
    ((S.boundaryPrefixJordan i).component j).lattice
    ((P.component 0).liftNested
      (((S.boundaryPrefixJordan i).component j).mapIsometry left)).lattice
  exact combined

/-- The final component of the augmented decomposition is exactly the
modular suffix envelope. -/
noncomputable def boundaryAugmentedLastComponentIsometry
    (i : Fin (n + 1)) :
    Isometry (S.boundarySuffix i).space
      ((S.boundaryAugmentedOrthogonalDecomposition i).component
        (Fin.last (i.val + 1))).space
      (S.boundarySuffixEnvelope i).lattice
      ((S.boundaryAugmentedOrthogonalDecomposition i).component
        (Fin.last (i.val + 1))).lattice := by
  let right := orthogonalProductRightComponentIsometry
    (S.boundaryPrefixForm i) (S.boundarySuffix i).space
    (S.boundarySuffixEnvelope i).lattice
  rw [boundaryAugmentedOrthogonalDecomposition,
    OrthogonalDecomposition.appendNested_last]
  exact right

theorem boundaryAugmented_modular (i : Fin (n + 1))
    (j : Fin (i.val + 2)) :
    IsModular
      ((S.boundaryAugmentedOrthogonalDecomposition i).component j).space
      ((S.boundaryAugmentedOrthogonalDecomposition i).component j).lattice
      (S.boundaryAugmentedScale i j) := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simpa only [boundaryAugmentedScale, Fin.lastCases_last] using
      (S.boundarySuffixEnvelope i).modular.mapLatticeIsometry
        (S.boundaryAugmentedLastComponentIsometry i)
  · simpa only [boundaryAugmentedScale, Fin.lastCases_castSucc,
      S.boundaryPrefixJordan_scaleGenerator i k] using
      ((S.boundaryPrefixJordan i).modular k).mapLatticeIsometry
        (S.boundaryAugmentedPrefixComponentIsometry i k)

theorem boundaryAugmented_scaleIdeal_eq (i : Fin (n + 1))
    (j : Fin (i.val + 2)) :
    scaleIdeal
        ((S.boundaryAugmentedOrthogonalDecomposition i).component j).space
        ((S.boundaryAugmentedOrthogonalDecomposition i).component j).lattice =
      principalIdeal (K := K) (S.boundaryAugmentedScale i j : K) := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · let g := S.boundaryAugmentedLastComponentIsometry i
    calc
      scaleIdeal
          ((S.boundaryAugmentedOrthogonalDecomposition i).component
            (Fin.last (i.val + 1))).space
          ((S.boundaryAugmentedOrthogonalDecomposition i).component
            (Fin.last (i.val + 1))).lattice =
          scaleIdeal (S.boundarySuffix i).space
            (S.boundarySuffixEnvelope i).lattice := by
        rw [← g.map_eq]
        exact scaleIdeal_map_isometry g.toQuadraticSpaceIsometry _
      _ = principalIdeal (K := K)
          (J.scaleGenerator (boundaryRightIndex i) : K) :=
        (S.boundarySuffixEnvelope i).modular.scaleIdeal_eq_principal
          (S.boundarySuffix_finrank_pos i)
      _ = principalIdeal (K := K)
          (S.boundaryAugmentedScale i (Fin.last (i.val + 1)) : K) := by
        simp [boundaryAugmentedScale]
  · let g := S.boundaryAugmentedPrefixComponentIsometry i k
    calc
      scaleIdeal
          ((S.boundaryAugmentedOrthogonalDecomposition i).component
            k.castSucc).space
          ((S.boundaryAugmentedOrthogonalDecomposition i).component
            k.castSucc).lattice =
          scaleIdeal ((S.boundaryPrefixJordan i).component k).space
            ((S.boundaryPrefixJordan i).component k).lattice := by
        rw [← g.map_eq]
        exact scaleIdeal_map_isometry g.toQuadraticSpaceIsometry _
      _ = principalIdeal (K := K)
          ((S.boundaryPrefixJordan i).scaleGenerator k : K) :=
        (S.boundaryPrefixJordan i).scaleIdeal_eq k
      _ = principalIdeal (K := K)
          (S.boundaryAugmentedScale i k.castSucc : K) := by
        simp [boundaryAugmentedScale]

theorem boundaryAugmented_normIdeal_eq (i : Fin (n + 1))
    (j : Fin (i.val + 2)) :
    normIdeal
        ((S.boundaryAugmentedOrthogonalDecomposition i).component j).space
        ((S.boundaryAugmentedOrthogonalDecomposition i).component j).lattice =
      principalIdeal (K := K) (S.boundaryAugmentedNorm i j : K) := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · let g := S.boundaryAugmentedLastComponentIsometry i
    calc
      normIdeal
          ((S.boundaryAugmentedOrthogonalDecomposition i).component
            (Fin.last (i.val + 1))).space
          ((S.boundaryAugmentedOrthogonalDecomposition i).component
            (Fin.last (i.val + 1))).lattice =
          normIdeal (S.boundarySuffix i).space
            (S.boundarySuffixEnvelope i).lattice := by
        rw [← g.map_eq]
        exact normIdeal_map_isometry g.toQuadraticSpaceIsometry _
      _ = principalIdeal (K := K)
          (S.boundaryEnvelopeNormGenerator i : K) :=
        (S.boundaryEnvelopeNormVector_spec i).1.normIdeal_eq
      _ = principalIdeal (K := K)
          (S.boundaryAugmentedNorm i (Fin.last (i.val + 1)) : K) := by
        simp [boundaryAugmentedNorm]
  · let g := S.boundaryAugmentedPrefixComponentIsometry i k
    calc
      normIdeal
          ((S.boundaryAugmentedOrthogonalDecomposition i).component
            k.castSucc).space
          ((S.boundaryAugmentedOrthogonalDecomposition i).component
            k.castSucc).lattice =
          normIdeal ((S.boundaryPrefixJordan i).component k).space
            ((S.boundaryPrefixJordan i).component k).lattice := by
        rw [← g.map_eq]
        exact normIdeal_map_isometry g.toQuadraticSpaceIsometry _
      _ = principalIdeal (K := K)
          ((S.boundaryPrefixJordan i).normGenerator k : K) :=
        (S.boundaryPrefixJordan i).normIdeal_eq k
      _ = principalIdeal (K := K)
          (S.boundaryAugmentedNorm i k.castSucc : K) := by
        simp [boundaryAugmentedNorm]

/-- The source Jordan splitting used in O'Meara 93:28, Step 2: all
components through the selected boundary are retained, while the whole
suffix is replaced by its norm-preserving modular envelope. -/
noncomputable def boundaryAugmentedJordan (i : Fin (n + 1)) :
    JordanDecomposition
      ((S.boundaryPrefixForm i).orthogonalSum (S.boundarySuffix i).space)
      (product (S.boundaryPrefixLattice i)
        (S.boundarySuffixEnvelope i).lattice)
      (i.val + 2) where
  toOrthogonalDecomposition := S.boundaryAugmentedOrthogonalDecomposition i
  scaleGenerator := S.boundaryAugmentedScale i
  normGenerator := S.boundaryAugmentedNorm i
  modular := S.boundaryAugmented_modular i
  scaleIdeal_eq := S.boundaryAugmented_scaleIdeal_eq i
  normIdeal_eq := S.boundaryAugmented_normIdeal_eq i
  scaleOrder_strict := S.boundaryAugmentedScale_strict i

/-- Compressing the whole suffix to its 93:3 envelope preserves every
fundamental norm group through the selected boundary. -/
theorem boundaryAugmented_fundamentalNormGroup_eq_source
    (i : Fin (n + 1)) (a : Fin (i.val + 2)) :
    (S.boundaryAugmentedJordan i).fundamentalNormGroup a =
      S.sourceJordan.fundamentalNormGroup ⟨a.val, by omega⟩ := by
  let idx : Fin (n + 2) := ⟨a.val, by omega⟩
  let order := ordUnit K (J.scaleGenerator idx)
  unfold fundamentalNormGroup fundamentalLattice fundamentalScaleOrder
  have haugOrder :
      ordUnit K ((S.boundaryAugmentedJordan i).scaleGenerator a) = order := by
    change ordUnit K (S.boundaryAugmentedScale i a) = order
    rw [S.boundaryAugmentedScale_eq_original i a]
  have hsourceOrder :
      ordUnit K (S.sourceJordan.scaleGenerator idx) = order := by
    simp only [S.sourceJordan_scaleGenerator, order]
  rw [haugOrder, hsourceOrder]
  rw [scaleTruncation_orthogonalProduct,
    S.boundarySuffixEnvelope_scaleTruncation_eq i a]
  let prefixMap := S.rawSourceResidualPrefixIsometry
    (S.boundaryPrefix_le i)
  have hprefix := normGroupSet_scaleTruncation_eq_of_isometry
    prefixMap order
  let split := S.sourceJordan.toOrthogonalDecomposition
    |>.prefixSuffixLatticeIsometry (i.val + 1)
  have hsplit := normGroupSet_scaleTruncation_eq_of_isometry split order
  have hsuffix : scaleTruncation (S.boundarySuffix i).space
      (S.boundarySuffix i).lattice order =
        (S.boundarySuffix i).lattice := by
    simpa only [order, idx] using S.boundarySuffix_scaleTruncation_eq i a
  rw [scaleTruncation_orthogonalProduct, hsuffix] at hsplit
  calc
    normGroupSet
        ((S.boundaryPrefixForm i).orthogonalSum (S.boundarySuffix i).space)
        (product
          (scaleTruncation (S.boundaryPrefixForm i)
            (S.boundaryPrefixLattice i) order)
          (S.boundarySuffixEnvelope i).lattice) =
      normGroupSet
        ((S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (i.val + 1)).space.orthogonalSum
            (S.boundarySuffix i).space)
        (product
          (scaleTruncation
            (S.sourceJordan.toOrthogonalDecomposition
              |>.prefixQuadraticSublattice (i.val + 1)).space
            (S.sourceJordan.toOrthogonalDecomposition
              |>.prefixQuadraticSublattice (i.val + 1)).lattice order)
          (S.boundarySuffix i).lattice) :=
      normGroupSet_orthogonalProduct_eq_of_factor_eq hprefix.symm
        (S.boundarySuffixEnvelope i).normGroup_eq
    _ = normGroupSet
        (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
        (scaleTruncation
          (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
          (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
          order) := hsplit.symm

/-- A retained prefix component has exactly the norm group of the
corresponding component of the full source Jordan decomposition. -/
theorem boundaryPrefixJordan_component_normGroup_eq_source
    (i : Fin (n + 1)) (j : Fin (i.val + 1)) :
    normGroupSet ((S.boundaryPrefixJordan i).component j).space
        ((S.boundaryPrefixJordan i).component j).lattice =
      normGroupSet
        (S.sourceJordan.component
          (S.prefixIndex (S.boundaryPrefix_le i) j)).space
        (S.sourceJordan.component
          (S.prefixIndex (S.boundaryPrefix_le i) j)).lattice := by
  let prefixComponent := BONG.blockProductComponentIsometry
    (S.prefixSourceCarrier (S.boundaryPrefix_le i))
    (S.prefixSourceForm (S.boundaryPrefix_le i))
    (S.prefixSourceLattice (S.boundaryPrefix_le i)) j
  let sourceComponent := BONG.blockProductComponentIsometry
    S.sourceCarrier S.sourceForm S.sourceLattice
      (S.prefixIndex (S.boundaryPrefix_le i) j)
  calc
    normGroupSet ((S.boundaryPrefixJordan i).component j).space
        ((S.boundaryPrefixJordan i).component j).lattice =
      normGroupSet (S.prefixSourceForm (S.boundaryPrefix_le i) j)
        (S.prefixSourceLattice (S.boundaryPrefix_le i) j) :=
      normGroupSet_eq_of_latticeIsometry prefixComponent
    _ = normGroupSet
        (S.sourceJordan.component
          (S.prefixIndex (S.boundaryPrefix_le i) j)).space
        (S.sourceJordan.component
          (S.prefixIndex (S.boundaryPrefix_le i) j)).lattice :=
      (normGroupSet_eq_of_latticeIsometry sourceComponent).symm

/-- The boundary component norm group embeds into the scalar norm group of
the exact suffix beginning at that component. -/
theorem boundaryRightComponent_normGroup_subset_suffix
    (i : Fin (n + 1)) :
    normGroupSet (S.sourceJordan.component (boundaryRightIndex i)).space
        (S.sourceJordan.component (boundaryRightIndex i)).lattice ⊆
      normGroupSet (S.boundarySuffix i).space
        (S.boundarySuffix i).lattice := by
  let D := S.sourceJordan.toOrthogonalDecomposition
  let hcut := S.boundarySuffix_cut_eq i
  let zero : Fin (S.boundarySuffixPred i + 1) := 0
  let suffixIndex : Fin (n + 2) := (D.suffixIndexEquiv hcut zero).1
  have hsuffixIndex : suffixIndex = boundaryRightIndex i := by
    apply Fin.ext
    rfl
  let blockD := BONG.blockProductOrthogonalDecomposition
    (S.boundarySuffixBlockCarrier i) (S.boundarySuffixBlockForm i)
    (S.boundarySuffixBlockLattice i)
  let componentMap := BONG.blockProductComponentIsometry
    (S.boundarySuffixBlockCarrier i) (S.boundarySuffixBlockForm i)
    (S.boundarySuffixBlockLattice i) zero
  have hcomponent :
      normGroupSet (blockD.component zero).space
          (blockD.component zero).lattice =
        normGroupSet
          (S.sourceJordan.component (boundaryRightIndex i)).space
          (S.sourceJordan.component (boundaryRightIndex i)).lattice := by
    have h : normGroupSet (blockD.component zero).space
          (blockD.component zero).lattice =
        normGroupSet (S.sourceJordan.component suffixIndex).space
          (S.sourceJordan.component suffixIndex).lattice := by
      exact normGroupSet_eq_of_latticeIsometry componentMap
    rw [hsuffixIndex] at h
    exact h
  have hwhole := normGroupSet_eq_of_latticeIsometry
    (S.boundarySuffixBlockIsometry i)
  intro z hz
  have hzComponent : z ∈
      normGroupSet (blockD.component zero).space
        (blockD.component zero).lattice := by
    rw [hcomponent]
    exact hz
  have hzBlock := blockD.component_normGroupSet_subset
    zero hzComponent
  rw [hwhole]
  exact hzBlock

/-- At the first suffix scale, source saturation identifies the norm group
of the whole exact suffix with the original fundamental norm group. -/
theorem boundarySuffix_normGroup_eq_sourceFundamental
    (i : Fin (n + 1)) :
    normGroupSet (S.boundarySuffix i).space
        (S.boundarySuffix i).lattice =
      S.sourceJordan.fundamentalNormGroup (boundaryRightIndex i) := by
  apply Set.Subset.antisymm
  · intro z hz
    let idx : Fin (i.val + 2) := Fin.last (i.val + 1)
    let order := ordUnit K (J.scaleGenerator (boundaryRightIndex i))
    let split := S.sourceJordan.toOrthogonalDecomposition
      |>.prefixSuffixLatticeIsometry (i.val + 1)
    have hsplit := normGroupSet_scaleTruncation_eq_of_isometry split order
    have hsuffix : scaleTruncation (S.boundarySuffix i).space
        (S.boundarySuffix i).lattice order =
          (S.boundarySuffix i).lattice := by
      have h := S.boundarySuffix_scaleTruncation_eq i idx
      let fullIdx : Fin (n + 2) := ⟨idx.val, by omega⟩
      have hfullIdx : fullIdx = boundaryRightIndex i := by
        apply Fin.ext
        simp [fullIdx, idx, boundaryRightIndex]
      change scaleTruncation (S.boundarySuffix i).space
          (S.boundarySuffix i).lattice
          (ordUnit K (J.scaleGenerator fullIdx)) =
        (S.boundarySuffix i).lattice at h
      rw [hfullIdx] at h
      exact h
    rw [scaleTruncation_orthogonalProduct, hsuffix] at hsplit
    unfold fundamentalNormGroup fundamentalLattice fundamentalScaleOrder
    rw [S.sourceJordan_scaleGenerator]
    rw [hsplit]
    rw [mem_normGroupSet_orthogonalProduct_iff]
    exact ⟨0, zero_mem_normGroupSet _ _, z, hz, by simp⟩
  · intro z hz
    have hzComponent : z ∈
        normGroupSet
          (S.sourceJordan.component (boundaryRightIndex i)).space
          (S.sourceJordan.component (boundaryRightIndex i)).lattice := by
      rw [S.sourceJordan_isSaturated (boundaryRightIndex i)]
      exact hz
    exact S.boundaryRightComponent_normGroup_subset_suffix i hzComponent

/-- Every displayed component of the compressed decomposition realizes the
corresponding original fundamental norm group. -/
theorem boundaryAugmented_componentNormGroup_eq_sourceFundamental
    (i : Fin (n + 1)) (a : Fin (i.val + 2)) :
    normGroupSet
        ((S.boundaryAugmentedJordan i).component a).space
        ((S.boundaryAugmentedJordan i).component a).lattice =
      S.sourceJordan.fundamentalNormGroup ⟨a.val, by omega⟩ := by
  refine Fin.lastCases ?_ (fun j => ?_) a
  · let g := S.boundaryAugmentedLastComponentIsometry i
    have hidx : boundaryRightIndex i =
        (⟨(Fin.last (i.val + 1)).val, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      simp [boundaryRightIndex]
    calc
      normGroupSet
          ((S.boundaryAugmentedJordan i).component
            (Fin.last (i.val + 1))).space
          ((S.boundaryAugmentedJordan i).component
            (Fin.last (i.val + 1))).lattice =
        normGroupSet (S.boundarySuffix i).space
          (S.boundarySuffixEnvelope i).lattice :=
        normGroupSet_eq_of_latticeIsometry g
      _ = normGroupSet (S.boundarySuffix i).space
          (S.boundarySuffix i).lattice :=
        (S.boundarySuffixEnvelope i).normGroup_eq
      _ = S.sourceJordan.fundamentalNormGroup (boundaryRightIndex i) :=
        S.boundarySuffix_normGroup_eq_sourceFundamental i
      _ = S.sourceJordan.fundamentalNormGroup
          ⟨(Fin.last (i.val + 1)).val, by omega⟩ := by rw [hidx]
  · let g := S.boundaryAugmentedPrefixComponentIsometry i j
    let idx := S.prefixIndex (S.boundaryPrefix_le i) j
    have hidx : idx = (⟨j.castSucc.val, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    calc
      normGroupSet
          ((S.boundaryAugmentedJordan i).component j.castSucc).space
          ((S.boundaryAugmentedJordan i).component j.castSucc).lattice =
        normGroupSet ((S.boundaryPrefixJordan i).component j).space
          ((S.boundaryPrefixJordan i).component j).lattice :=
        normGroupSet_eq_of_latticeIsometry g
      _ = normGroupSet (S.sourceJordan.component idx).space
          (S.sourceJordan.component idx).lattice :=
        S.boundaryPrefixJordan_component_normGroup_eq_source i j
      _ = S.sourceJordan.fundamentalNormGroup idx :=
        S.sourceJordan_isSaturated idx
      _ = S.sourceJordan.fundamentalNormGroup
          ⟨j.castSucc.val, by omega⟩ := by rw [hidx]

/-- The source compression used in O'Meara 93:28, Step 2 is a saturated
Jordan decomposition, derived from the original saturation and 93:3. -/
theorem boundaryAugmentedJordan_isSaturated (i : Fin (n + 1)) :
    (S.boundaryAugmentedJordan i).IsSaturated := by
  intro a
  calc
    normGroupSet ((S.boundaryAugmentedJordan i).component a).space
        ((S.boundaryAugmentedJordan i).component a).lattice =
      S.sourceJordan.fundamentalNormGroup ⟨a.val, by omega⟩ :=
        S.boundaryAugmented_componentNormGroup_eq_sourceFundamental i a
    _ = (S.boundaryAugmentedJordan i).fundamentalNormGroup a :=
      (S.boundaryAugmented_fundamentalNormGroup_eq_source i a).symm

/-- The enlarged lattice in the source residual ambient space, exposed
before the target-prefix splitting construction. -/
noncomputable def boundaryAugmentedAmbientLatticeCore (i : Fin (n + 1)) :
    Lattice K (BONG.BlockProductSpace (n + 1) S.sourceCarrier) :=
  let D := S.sourceJordan.toOrthogonalDecomposition
  let split := D.prefixSuffixLatticeIsometry (i.val + 1)
  map split.toLinearEquiv <|
    product (D.prefixQuadraticSublattice (i.val + 1)).lattice
      (S.boundarySuffixEnvelope i).lattice

/-- Pull the target residual Jordan decomposition back to the source
residual ambient space along an integral residual isometry. -/
noncomputable def boundaryMappedTargetJordan
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    JordanDecomposition
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (n + 2) :=
  S.targetJordan.mapIsometry f.symm

@[simp]
theorem boundaryMappedTargetJordan_scaleGenerator
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (j : Fin (n + 2)) :
    (S.boundaryMappedTargetJordan f).scaleGenerator j =
      J.scaleGenerator j :=
  rfl

set_option maxHeartbeats 0 in
/-- Every mapped target component before the boundary has the mixed
pairing required to split the enlarged source lattice.  The old-lattice
part is controlled by the target Jordan splitting; the envelope part is
controlled by its later modular scale. -/
theorem boundaryMappedTarget_pairing_augmented
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1))
    (j : (S.boundaryMappedTargetJordan f).toOrthogonalDecomposition.PrefixIndex
      (i.val + 1))
    (y : ((S.boundaryMappedTargetJordan f).component j.1).carrier)
    (hy : y ∈ ((S.boundaryMappedTargetJordan f).component j.1).lattice)
    (x : BONG.BlockProductSpace (n + 1) S.sourceCarrier)
    (hx : x ∈ S.boundaryAugmentedAmbientLatticeCore i) :
    (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm).bilin
        (y : BONG.BlockProductSpace (n + 1) S.sourceCarrier) x ∈
      principalIdeal (K := K)
        ((S.boundaryMappedTargetJordan f).scaleGenerator j.1 : K) := by
  let T := S.boundaryMappedTargetJordan f
  let D := S.sourceJordan.toOrthogonalDecomposition
  let split := D.prefixSuffixLatticeIsometry (i.val + 1)
  let z := split.toLinearEquiv.symm x
  have hz : z ∈ product
      (D.prefixQuadraticSublattice (i.val + 1)).lattice
      (S.boundarySuffixEnvelope i).lattice := by
    change x ∈ map split.toLinearEquiv
      (product (D.prefixQuadraticSublattice (i.val + 1)).lattice
        (S.boundarySuffixEnvelope i).lattice) at hx
    exact (mem_map_iff split.toLinearEquiv _ x).mp hx
  have hzParts := mem_product_iff.mp hz
  let xOld := split.toLinearEquiv (z.1, 0)
  let xEnvelope := split.toLinearEquiv (0, z.2)
  have hxOld : xOld ∈
      BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice := by
    apply (split.map_mem (z.1, 0)).mp
    rw [mem_product_iff]
    exact ⟨hzParts.1, zero_mem _⟩
  have hyOld : (y : BONG.BlockProductSpace (n + 1) S.sourceCarrier) ∈
      BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice :=
    T.toOrthogonalDecomposition.component_ambientSubmodule_le j.1
      ⟨y, hy, rfl⟩
  have hOldPair := T.component_pairing j.1 y hy xOld hxOld
  let ySplit := split.toLinearEquiv.symm
    (y : BONG.BlockProductSpace (n + 1) S.sourceCarrier)
  have hySplit : ySplit ∈ product
      (D.prefixQuadraticSublattice (i.val + 1)).lattice
      (S.boundarySuffix i).lattice := by
    exact (split.symm.map_mem (y :
      BONG.BlockProductSpace (n + 1) S.sourceCarrier)).mp hyOld
  have hySuffix : ySplit.2 ∈ (S.boundarySuffixEnvelope i).lattice :=
    (S.boundarySuffixEnvelope i).contains (mem_product_iff.mp hySplit).2
  have hEnvelopeScale :
      (S.boundarySuffix i).space.bilin ySplit.2 z.2 ∈
        principalIdeal (K := K)
          (J.scaleGenerator (boundaryRightIndex i) : K) := by
    rw [← (S.boundarySuffixEnvelope i).modular.scaleIdeal_eq_principal
      (S.boundarySuffix_finrank_pos i)]
    exact bilin_mem_scaleIdeal_of_mem (S.boundarySuffix i).space
      (S.boundarySuffixEnvelope i).lattice hySuffix hzParts.2
  have hscaleLe : principalIdeal (K := K)
        (J.scaleGenerator (boundaryRightIndex i) : K) ≤
      principalIdeal (K := K) (T.scaleGenerator j.1 : K) := by
    apply (principalIdeal_le_iff_ord_ge
      (Units.ne_zero (J.scaleGenerator (boundaryRightIndex i)))
      (Units.ne_zero (T.scaleGenerator j.1))).2
    rw [S.boundaryMappedTargetJordan_scaleGenerator f j.1]
    have hindex : j.1 < boundaryRightIndex i := by
      change j.1.val < i.val + 1
      exact j.2
    simpa only [coe_ordUnit] using
      WithTop.coe_le_coe.mpr (J.scaleOrder_strict hindex).le
  have hEnvelopeTarget :
      (S.boundarySuffix i).space.bilin ySplit.2 z.2 ∈
        principalIdeal (K := K) (T.scaleGenerator j.1 : K) :=
    hscaleLe hEnvelopeScale
  have hEnvelopePair :
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm).bilin
          (y : BONG.BlockProductSpace (n + 1) S.sourceCarrier) xEnvelope ∈
        principalIdeal (K := K) (T.scaleGenerator j.1 : K) := by
    have hmap := split.map_bilin ySplit (0, z.2)
    have hyMap : split.toLinearEquiv ySplit =
        (y : BONG.BlockProductSpace (n + 1) S.sourceCarrier) :=
      split.toLinearEquiv.apply_symm_apply _
    have hpairEq :
        (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm).bilin
            (y : BONG.BlockProductSpace (n + 1) S.sourceCarrier) xEnvelope =
          (S.boundarySuffix i).space.bilin ySplit.2 z.2 := by
      rw [← hyMap]
      change _ = _
      rw [hmap]
      change
        (D.prefixQuadraticSublattice (i.val + 1)).space.bilin ySplit.1 0 +
            (S.boundarySuffix i).space.bilin ySplit.2 z.2 =
          (S.boundarySuffix i).space.bilin ySplit.2 z.2
      have hzpair :
          (D.prefixQuadraticSublattice (i.val + 1)).space.bilin
              ySplit.1 0 = 0 :=
        LinearMap.map_zero
          ((D.prefixQuadraticSublattice (i.val + 1)).space.bilin ySplit.1)
      rw [hzpair, zero_add]
    rw [hpairEq]
    exact hEnvelopeTarget
  have hxDecomp : xOld + xEnvelope = x := by
    change split.toLinearEquiv (z.1, 0) +
        split.toLinearEquiv (0, z.2) = x
    rw [← map_add]
    have hcoords : (z.1, 0) + (0, z.2) = z := by
      apply Prod.ext
      · change z.1 + 0 = z.1
        exact add_zero z.1
      · change 0 + z.2 = z.2
        exact zero_add z.2
    rw [hcoords]
    exact split.toLinearEquiv.apply_symm_apply x
  rw [← hxDecomp, LinearMap.BilinForm.add_right]
  exact (principalIdeal (K := K) (T.scaleGenerator j.1 : K)).add_mem
    hOldPair hEnvelopePair

/-- The augmented lattice in the original source residual ambient space. -/
noncomputable def boundaryAugmentedAmbientLattice (i : Fin (n + 1)) :
    Lattice K (BONG.BlockProductSpace (n + 1) S.sourceCarrier) :=
  S.boundaryAugmentedAmbientLatticeCore i

/-- The old source residual lattice is contained in its Step-2 enlargement.
-/
theorem sourceLattice_le_boundaryAugmentedAmbientLattice
    (i : Fin (n + 1)) :
    BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice ≤
      S.boundaryAugmentedAmbientLattice i := by
  let D := S.sourceJordan.toOrthogonalDecomposition
  let split := D.prefixSuffixLatticeIsometry (i.val + 1)
  intro x hx
  change x ∈ map split.toLinearEquiv
    (product (D.prefixQuadraticSublattice (i.val + 1)).lattice
      (S.boundarySuffixEnvelope i).lattice)
  rw [mem_map_iff, mem_product_iff]
  have hold : split.toLinearEquiv.symm x ∈
      product (D.prefixQuadraticSublattice (i.val + 1)).lattice
        (D.suffixQuadraticSublattice (i.val + 1)).lattice := by
    exact (split.symm.map_mem x).mp hx
  exact ⟨(mem_product_iff.mp hold).1,
    (S.boundarySuffixEnvelope i).contains (mem_product_iff.mp hold).2⟩

/-- Integral realization of the enlarged prefix/suffix product in the
original source residual ambient space. -/
noncomputable def boundaryAugmentedSplitIsometry (i : Fin (n + 1)) :
    Isometry
      ((S.sourceJordan.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (i.val + 1)).space.orthogonalSum
        (S.boundarySuffix i).space)
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (product
        (S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (i.val + 1)).lattice
        (S.boundarySuffixEnvelope i).lattice)
      (S.boundaryAugmentedAmbientLattice i) := by
  let split := S.sourceJordan.toOrthogonalDecomposition
    |>.prefixSuffixLatticeIsometry (i.val + 1)
  exact Isometry.toMap _ split.toQuadraticSpaceIsometry _

/-- Change from raw residual prefix coordinates to the intrinsic prefix,
leaving the enlarged suffix fixed. -/
noncomputable def boundaryAugmentedCoordinateToSplitIsometry
    (i : Fin (n + 1)) :
    Isometry
      ((S.boundaryPrefixForm i).orthogonalSum (S.boundarySuffix i).space)
      ((S.sourceJordan.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (i.val + 1)).space.orthogonalSum
        (S.boundarySuffix i).space)
      (product (S.boundaryPrefixLattice i)
        (S.boundarySuffixEnvelope i).lattice)
      (product
        (S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (i.val + 1)).lattice
        (S.boundarySuffixEnvelope i).lattice) :=
  (S.rawSourceResidualPrefixIsometry (S.boundaryPrefix_le i)).orthogonalProductBasic
    (Isometry.refl (S.boundarySuffix i).space
      (S.boundarySuffixEnvelope i).lattice)

/-- The compressed source Jordan lattice is integrally isometric to the
actual enlarged lattice (L') in the original residual space. -/
noncomputable def boundaryAugmentedAmbientIsometry (i : Fin (n + 1)) :
    Isometry
      ((S.boundaryPrefixForm i).orthogonalSum (S.boundarySuffix i).space)
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (product (S.boundaryPrefixLattice i)
        (S.boundarySuffixEnvelope i).lattice)
      (S.boundaryAugmentedAmbientLattice i) :=
  (S.boundaryAugmentedCoordinateToSplitIsometry i).trans
    (S.boundaryAugmentedSplitIsometry i)

/-- The saturated source compression transported from prefix/suffix
coordinates to the actual enlarged lattice. -/
noncomputable def boundaryAugmentedAmbientJordan (i : Fin (n + 1)) :
    JordanDecomposition
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (S.boundaryAugmentedAmbientLattice i) (i.val + 2) :=
  (S.boundaryAugmentedJordan i).mapIsometry
    (S.boundaryAugmentedAmbientIsometry i)

@[simp]
theorem boundaryAugmentedAmbientJordan_scaleGenerator
    (i : Fin (n + 1)) (a : Fin (i.val + 2)) :
    (S.boundaryAugmentedAmbientJordan i).scaleGenerator a =
      J.scaleGenerator ⟨a.val, by omega⟩ := by
  exact S.boundaryAugmentedScale_eq_original i a

theorem boundaryPrefixJordan_componentRank
    (i : Fin (n + 1)) (a : Fin (i.val + 1)) :
    (S.boundaryPrefixJordan i).componentRank a = 4 := by
  rw [boundaryPrefixJordan,
    BONG.blockProductJordanDecomposition_componentRank,
    S.source_finrank]

@[simp]
theorem boundaryAugmentedAmbientJordan_componentRank_castSucc
    (i : Fin (n + 1)) (a : Fin (i.val + 1)) :
    (S.boundaryAugmentedAmbientJordan i).componentRank a.castSucc = 4 := by
  rw [boundaryAugmentedAmbientJordan, mapIsometry_componentRank]
  unfold componentRank
  let g := S.boundaryAugmentedPrefixComponentIsometry i a
  change finrank K
    ((S.boundaryAugmentedOrthogonalDecomposition i).component
      a.castSucc).carrier = 4
  rw [← g.toLinearEquiv.finrank_eq]
  exact S.boundaryPrefixJordan_componentRank i a

/-- The first target residual components split the Step-2 enlargement
simultaneously, by O'Meara 82:7. -/
noncomputable def boundaryMappedTargetPrefixSplitting
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    OrthogonalDecomposition
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (S.boundaryAugmentedAmbientLattice i) 2 := by
  letI : Module.Finite K
      (BONG.BlockProductSpace (n + 1) S.sourceCarrier) :=
    (S.boundaryAugmentedAmbientLattice i).moduleFinite
  exact (S.boundaryMappedTargetJordan f).prefixSplittingOfComponentPairing
    (i.val + 1)
    (S.sourceLattice_le_boundaryAugmentedAmbientLattice i)
    (S.boundaryMappedTarget_pairing_augmented f i)

/-- The displayed prefix block of the target-side 82:7 splitting retains
the original mapped target Jordan decomposition. -/
noncomputable def boundaryMappedTargetPrefixJordan
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    JordanDecomposition
      ((S.boundaryMappedTargetPrefixSplitting f i).component 0).space
      ((S.boundaryMappedTargetPrefixSplitting f i).component 0).lattice
      (i.val + 1) := by
  change JordanDecomposition
    ((S.boundaryMappedTargetJordan f).toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (i.val + 1)).space
    ((S.boundaryMappedTargetJordan f).toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (i.val + 1)).lattice
    (i.val + 1)
  exact (S.boundaryMappedTargetJordan f).initialSegment i.val (by omega)

@[simp]
theorem boundaryMappedTargetPrefixJordan_scaleGenerator
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) (a : Fin (i.val + 1)) :
    (S.boundaryMappedTargetPrefixJordan f i).scaleGenerator a =
      J.scaleGenerator ⟨a.val, by omega⟩ := by
  rfl

@[simp]
theorem boundaryMappedTargetPrefixJordan_componentRank
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) (a : Fin (i.val + 1)) :
    (S.boundaryMappedTargetPrefixJordan f i).componentRank a = 4 := by
  change ((S.boundaryMappedTargetJordan f).initialSegment i.val
    (by omega)).componentRank a = 4
  rw [initialSegment_componentRank]
  change (S.boundaryMappedTargetJordan f).componentRank
    ⟨a.val, by omega⟩ = 4
  rw [boundaryMappedTargetJordan, mapIsometry_componentRank,
    S.targetJordan_componentRank]

/-- At the first omitted target scale, the complete source enlargement and
the mapped target prefix have exactly the same scale-truncation volume
jump.  The final source envelope contributes zero at its own scale. -/
theorem boundaryAugmented_volumeJump_eq_targetPrefix
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    ∑ a : Fin (i.val + 2),
        ((S.boundaryAugmentedAmbientJordan i).componentRank a : Int) *
          max 0 (ordUnit K (J.scaleGenerator (boundaryRightIndex i)) -
            ordUnit K
              ((S.boundaryAugmentedAmbientJordan i).scaleGenerator a)) =
      ∑ a : Fin (i.val + 1),
        ((S.boundaryMappedTargetPrefixJordan f i).componentRank a : Int) *
          max 0 (ordUnit K (J.scaleGenerator (boundaryRightIndex i)) -
            ordUnit K
              ((S.boundaryMappedTargetPrefixJordan f i).scaleGenerator a)) := by
  rw [Fin.sum_univ_castSucc]
  have hlast :
      (S.boundaryAugmentedAmbientJordan i).scaleGenerator
          (Fin.last (i.val + 1)) =
        J.scaleGenerator (boundaryRightIndex i) := by
    rw [S.boundaryAugmentedAmbientJordan_scaleGenerator]
    congr 1
  rw [hlast, sub_self, max_eq_left (le_refl 0), mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro a _
  rw [S.boundaryAugmentedAmbientJordan_componentRank_castSucc,
    S.boundaryMappedTargetPrefixJordan_componentRank,
    S.boundaryAugmentedAmbientJordan_scaleGenerator,
    S.boundaryMappedTargetPrefixJordan_scaleGenerator]
  have hidx :
      (⟨a.castSucc.val, by omega⟩ : Fin (n + 2)) =
        ⟨a.val, by omega⟩ := by
    apply Fin.ext
    rfl
  rw [hidx]

/-- The target-side orthogonal complement has no volume jump under
truncation at the first omitted scale. -/
theorem boundaryMappedTargetComplement_scaleTruncation_volumeOrder_eq
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    let C := (S.boundaryMappedTargetPrefixSplitting f i).component 1
    volumeOrder C.space
        (scaleTruncation C.space C.lattice
          (ordUnit K (J.scaleGenerator (boundaryRightIndex i)))) =
      volumeOrder C.space C.lattice := by
  dsimp only
  let A := S.boundaryAugmentedAmbientJordan i
  let P := S.boundaryMappedTargetPrefixSplitting f i
  let T := S.boundaryMappedTargetPrefixJordan f i
  let s := ordUnit K (J.scaleGenerator (boundaryRightIndex i))
  have hA := A.volumeOrder_scaleTruncation s
  have hT := T.volumeOrder_scaleTruncation s
  have htrunc := P.volumeOrder_scaleTruncation_eq_add_components s
  have hbase := P.volumeOrder_eq_add_components
  have hjump := S.boundaryAugmented_volumeJump_eq_targetPrefix f i
  dsimp only [A, T, s] at hA hT
  dsimp only [P, s] at htrunc hbase
  omega

/-- Volume rigidity upgrades the absence of a truncation jump to literal
equality of the complement with its truncation. -/
theorem boundaryMappedTargetComplement_scaleTruncation_eq
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    let C := (S.boundaryMappedTargetPrefixSplitting f i).component 1
    scaleTruncation C.space C.lattice
        (ordUnit K (J.scaleGenerator (boundaryRightIndex i))) =
      C.lattice := by
  dsimp only
  let C := (S.boundaryMappedTargetPrefixSplitting f i).component 1
  apply eq_of_le_of_volumeOrder_eq C.space
  · intro x hx
    exact (mem_scaleTruncation_iff_inf C.space C.lattice _ x).mp hx |>.1
  · exact S.boundaryMappedTargetComplement_scaleTruncation_volumeOrder_eq
      f i

/-- Every pairing on the target-side complement lies in the first omitted
scale ideal. -/
theorem boundaryMappedTargetComplement_scaleIdeal_le
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    let C := (S.boundaryMappedTargetPrefixSplitting f i).component 1
    scaleIdeal C.space C.lattice ≤
      principalIdeal (K := K)
        (J.scaleGenerator (boundaryRightIndex i) : K) := by
  dsimp only
  let C := (S.boundaryMappedTargetPrefixSplitting f i).component 1
  apply scaleIdeal_le_of_bilin_mem C.space C.lattice
  intro x y hx hy
  rw [principalIdeal_eq_powerIdeal, mem_powerIdeal_iff]
  have hxTrunc : x ∈ scaleTruncation C.space C.lattice
      (ordUnit K (J.scaleGenerator (boundaryRightIndex i))) := by
    rw [S.boundaryMappedTargetComplement_scaleTruncation_eq f i]
    exact hx
  exact (mem_scaleTruncation_iff_ord_bilin_ge.mp hxTrunc).2 y hy

/-- The 82:7 complement has the same rank as the source envelope which it
replaces. -/
theorem boundaryMappedTargetComplement_rank_eq_lastSource
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    finrank K
        ((S.boundaryMappedTargetPrefixSplitting f i).component 1).carrier =
      (S.boundaryAugmentedAmbientJordan i).componentRank
        (Fin.last (i.val + 1)) := by
  change finrank K
      ((S.boundaryMappedTargetPrefixSplitting f i).component 1).carrier =
    finrank K
      ((S.boundaryAugmentedAmbientJordan i).component
        (Fin.last (i.val + 1))).carrier
  let A := S.boundaryAugmentedAmbientJordan i
  let P := S.boundaryMappedTargetPrefixSplitting f i
  let T := S.boundaryMappedTargetPrefixJordan f i
  have hA := A.toOrthogonalDecomposition.finrank_eq_sum_components
  have hP := P.finrank_eq_sum_components
  have hT := T.toOrthogonalDecomposition.finrank_eq_sum_components
  rw [Fin.sum_univ_castSucc] at hA
  rw [Fin.sum_univ_two] at hP
  have hprefix :
      (∑ a : Fin (i.val + 1),
          finrank K (A.component a.castSucc).carrier) =
        ∑ a : Fin (i.val + 1),
          finrank K (T.component a).carrier := by
    apply Finset.sum_congr rfl
    intro a _
    change A.componentRank a.castSucc = T.componentRank a
    dsimp only [A, T]
    rw [S.boundaryAugmentedAmbientJordan_componentRank_castSucc,
      S.boundaryMappedTargetPrefixJordan_componentRank]
  dsimp only [A, P, T] at hA hP hT hprefix ⊢
  omega

/-- The complement and the source envelope have the same volume order. -/
theorem boundaryMappedTargetComplement_volumeOrder_eq_lastSource
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    volumeOrder
        ((S.boundaryMappedTargetPrefixSplitting f i).component 1).space
        ((S.boundaryMappedTargetPrefixSplitting f i).component 1).lattice =
      volumeOrder
        ((S.boundaryAugmentedAmbientJordan i).component
          (Fin.last (i.val + 1))).space
        ((S.boundaryAugmentedAmbientJordan i).component
          (Fin.last (i.val + 1))).lattice := by
  let A := S.boundaryAugmentedAmbientJordan i
  let P := S.boundaryMappedTargetPrefixSplitting f i
  let T := S.boundaryMappedTargetPrefixJordan f i
  have hA := A.toOrthogonalDecomposition.volumeOrder_eq_sum_components
  have hP := P.volumeOrder_eq_add_components
  have hT := T.toOrthogonalDecomposition.volumeOrder_eq_sum_components
  rw [Fin.sum_univ_castSucc] at hA
  have hprefix :
      (∑ a : Fin (i.val + 1),
          volumeOrder (A.component a.castSucc).space
            (A.component a.castSucc).lattice) =
        ∑ a : Fin (i.val + 1),
          volumeOrder (T.component a).space (T.component a).lattice := by
    apply Finset.sum_congr rfl
    intro a _
    calc
      volumeOrder (A.component a.castSucc).space
          (A.component a.castSucc).lattice =
          (A.componentRank a.castSucc : Int) *
            ordUnit K (A.scaleGenerator a.castSucc) :=
        (A.modular a.castSucc).volumeOrder_eq
      _ = (T.componentRank a : Int) *
            ordUnit K (T.scaleGenerator a) := by
        dsimp only [A, T]
        rw [S.boundaryAugmentedAmbientJordan_componentRank_castSucc,
          S.boundaryMappedTargetPrefixJordan_componentRank,
          S.boundaryAugmentedAmbientJordan_scaleGenerator,
          S.boundaryMappedTargetPrefixJordan_scaleGenerator]
        congr 2
      _ = volumeOrder (T.component a).space (T.component a).lattice :=
        (T.modular a).volumeOrder_eq.symm
  dsimp only [A, P, T] at hA hP hT hprefix ⊢
  omega

theorem boundaryAugmentedAmbientLastComponent_finrank_pos
    (i : Fin (n + 1)) :
    0 < finrank K
      ((S.boundaryAugmentedAmbientJordan i).component
        (Fin.last (i.val + 1))).carrier := by
  change 0 < (S.boundaryAugmentedAmbientJordan i).componentRank
    (Fin.last (i.val + 1))
  rw [boundaryAugmentedAmbientJordan, mapIsometry_componentRank]
  unfold componentRank
  change 0 < finrank K
    ((S.boundaryAugmentedOrthogonalDecomposition i).component
      (Fin.last (i.val + 1))).carrier
  let g := S.boundaryAugmentedLastComponentIsometry i
  rw [← g.toLinearEquiv.finrank_eq]
  exact S.boundarySuffix_finrank_pos i

theorem boundaryMappedTargetComplement_finrank_pos
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    0 < finrank K
      ((S.boundaryMappedTargetPrefixSplitting f i).component 1).carrier := by
  rw [S.boundaryMappedTargetComplement_rank_eq_lastSource f i]
  exact S.boundaryAugmentedAmbientLastComponent_finrank_pos i

/-- The target-side complement has precisely the determinant order required
for modularity at the first omitted scale. -/
theorem boundaryMappedTargetComplement_volumeOrder_eq
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    let C := (S.boundaryMappedTargetPrefixSplitting f i).component 1
    volumeOrder C.space C.lattice =
      (finrank K C.carrier : Int) *
        ordUnit K (J.scaleGenerator (boundaryRightIndex i)) := by
  dsimp only
  let A := S.boundaryAugmentedAmbientJordan i
  let last := Fin.last (i.val + 1)
  calc
    volumeOrder
        ((S.boundaryMappedTargetPrefixSplitting f i).component 1).space
        ((S.boundaryMappedTargetPrefixSplitting f i).component 1).lattice =
        volumeOrder (A.component last).space (A.component last).lattice :=
      S.boundaryMappedTargetComplement_volumeOrder_eq_lastSource f i
    _ = (A.componentRank last : Int) *
          ordUnit K (A.scaleGenerator last) :=
      (A.modular last).volumeOrder_eq
    _ = (finrank K
          ((S.boundaryMappedTargetPrefixSplitting f i).component 1).carrier :
            Int) *
          ordUnit K (J.scaleGenerator (boundaryRightIndex i)) := by
      have hrank := S.boundaryMappedTargetComplement_rank_eq_lastSource f i
      have hscale : A.scaleGenerator last =
          J.scaleGenerator (boundaryRightIndex i) := by
        dsimp only [A, last]
        rw [S.boundaryAugmentedAmbientJordan_scaleGenerator]
        congr 1
      rw [hscale, hrank]

/-- The complement produced by simultaneous prefix splitting is modular at
the first omitted Jordan scale. -/
theorem boundaryMappedTargetComplement_isModular
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    let C := (S.boundaryMappedTargetPrefixSplitting f i).component 1
    IsModular C.space C.lattice
      (J.scaleGenerator (boundaryRightIndex i)) := by
  dsimp only
  let C := (S.boundaryMappedTargetPrefixSplitting f i).component 1
  exact isModular_of_scaleIdeal_le_of_volumeOrder_eq C.space C.lattice
    (J.scaleGenerator (boundaryRightIndex i))
    (S.boundaryMappedTargetComplement_scaleIdeal_le f i)
    (S.boundaryMappedTargetComplement_volumeOrder_eq f i)

/-- The first omitted mapped target component embeds integrally into the
82:7 complement. -/
noncomputable def boundaryMappedTargetRightToComplementRepresentation
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    let T := S.boundaryMappedTargetJordan f
    let C := (S.boundaryMappedTargetPrefixSplitting f i).component 1
    Representation
      (T.component (boundaryRightIndex i)).space C.space
      (T.component (boundaryRightIndex i)).lattice C.lattice := by
  dsimp only
  let T := S.boundaryMappedTargetJordan f
  let P := S.boundaryMappedTargetPrefixSplitting f i
  let right := boundaryRightIndex i
  let ambient := BONG.BlockProductSpace (n + 1) S.sourceCarrier
  let inclusion : (T.component right).carrier →ₗ[K] ambient :=
    (T.component right).carrier.subtype
  have hrange : ∀ y : (T.component right).carrier,
      inclusion y ∈ (P.component 1).carrier := by
    intro y
    change ∀ x : ambient,
      x ∈ T.toOrthogonalDecomposition.prefixCarrier (i.val + 1) →
        (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm).bilin
          x (y : ambient) = 0
    intro x hx
    apply T.toOrthogonalDecomposition.bilin_prefixCarrier_suffixCarrier_eq_zero
      (i.val + 1) hx
    apply le_iSup
      (fun j : T.toOrthogonalDecomposition.SuffixIndex (i.val + 1) ↦
        (T.component j.1).carrier)
      ⟨right, by simp [right, boundaryRightIndex]⟩
    exact y.property
  let lift : (T.component right).carrier →ₗ[K] (P.component 1).carrier :=
    LinearMap.codRestrict (P.component 1).carrier inclusion hrange
  refine {
    toLinearMap := lift
    injective := by
      intro x y hxy
      have hval : ((lift x : (P.component 1).carrier) : ambient) =
          ((lift y : (P.component 1).carrier) : ambient) :=
        congrArg (fun z : (P.component 1).carrier ↦ (z : ambient)) hxy
      apply Subtype.ext
      exact hval
    map_bilin := by
      intro x y
      change
        (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm).bilin
            (x : ambient) (y : ambient) =
          (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm).bilin
            (x : ambient) (y : ambient)
      rfl
    map_mem := ?_ }
  intro x hx
  have hxOld : (x : ambient) ∈
      BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice :=
    T.toOrthogonalDecomposition.component_ambientSubmodule_le right
      ⟨x, hx, rfl⟩
  have hxAug := S.sourceLattice_le_boundaryAugmentedAmbientLattice i hxOld
  change (x : ambient) ∈ S.boundaryAugmentedAmbientLattice i
  exact hxAug

theorem boundaryAugmentedAmbientJordan_isSaturated (i : Fin (n + 1)) :
    (S.boundaryAugmentedAmbientJordan i).IsSaturated :=
  (S.boundaryAugmentedJordan_isSaturated i).mapIsometry
    (S.boundaryAugmentedAmbientIsometry i)

/-- The first omitted mapped target component and the last component of the
source compression have the same scalar norm group. -/
theorem boundaryMappedTargetRight_normGroup_eq_lastSource
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    let T := S.boundaryMappedTargetJordan f
    let A := S.boundaryAugmentedAmbientJordan i
    let right := boundaryRightIndex i
    let last := Fin.last (i.val + 1)
    normGroupSet (T.component right).space (T.component right).lattice =
      normGroupSet (A.component last).space (A.component last).lattice := by
  dsimp only
  let T := S.boundaryMappedTargetJordan f
  let A := S.boundaryAugmentedAmbientJordan i
  let right := boundaryRightIndex i
  let last := Fin.last (i.val + 1)
  let targetMap := (S.targetJordan.component right).mapLatticeIsometry f.symm
  let sourceMap :=
    ((S.boundaryAugmentedJordan i).component last).mapLatticeIsometry
      (S.boundaryAugmentedAmbientIsometry i)
  have hindex : (⟨last.val, by omega⟩ : Fin (n + 2)) = right := by
    apply Fin.ext
    rfl
  have hfund := S.boundaryAugmented_fundamentalNormGroup_eq_source i last
  rw [hindex] at hfund
  calc
    normGroupSet (T.component right).space (T.component right).lattice =
        normGroupSet (S.targetJordan.component right).space
          (S.targetJordan.component right).lattice :=
      normGroupSet_eq_of_latticeIsometry targetMap
    _ = normGroupSet (S.sourceJordan.component right).space
          (S.sourceJordan.component right).lattice :=
      (S.targetJordan_component_normGroupSet right).trans
        (S.sourceJordan_component_normGroupSet right).symm
    _ = S.sourceJordan.fundamentalNormGroup right :=
      S.sourceJordan_isSaturated right
    _ = (S.boundaryAugmentedJordan i).fundamentalNormGroup last :=
      hfund.symm
    _ = normGroupSet ((S.boundaryAugmentedJordan i).component last).space
          ((S.boundaryAugmentedJordan i).component last).lattice :=
      (S.boundaryAugmentedJordan_isSaturated i last).symm
    _ = normGroupSet (A.component last).space (A.component last).lattice :=
      (normGroupSet_eq_of_latticeIsometry sourceMap).symm

/-- The source-envelope norm group is contained in the target complement,
because the first omitted mapped target component embeds there. -/
theorem boundaryLastSource_normGroup_subset_targetComplement
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    let A := S.boundaryAugmentedAmbientJordan i
    let C := (S.boundaryMappedTargetPrefixSplitting f i).component 1
    normGroupSet (A.component (Fin.last (i.val + 1))).space
        (A.component (Fin.last (i.val + 1))).lattice ⊆
      normGroupSet C.space C.lattice := by
  dsimp only
  have h := (S.boundaryMappedTargetRightToComplementRepresentation f i)
    |>.normGroupSet_subset
  rw [S.boundaryMappedTargetRight_normGroup_eq_lastSource f i] at h
  exact h

/-- The target complement embeds integrally into the intrinsic last scale
layer of the enlarged lattice. -/
noncomputable def boundaryMappedTargetComplementToFundamentalRepresentation
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    let A := S.boundaryAugmentedAmbientJordan i
    let C := (S.boundaryMappedTargetPrefixSplitting f i).component 1
    Representation C.space
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      C.lattice (A.fundamentalLattice (Fin.last (i.val + 1))) := by
  dsimp only
  let A := S.boundaryAugmentedAmbientJordan i
  let P := S.boundaryMappedTargetPrefixSplitting f i
  let C := P.component 1
  let last := Fin.last (i.val + 1)
  let ambient := BONG.BlockProductSpace (n + 1) S.sourceCarrier
  let ambientForm :=
    BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm
  let inclusion : C.carrier →ₗ[K] ambient := C.carrier.subtype
  have hscale : A.scaleGenerator last =
      J.scaleGenerator (boundaryRightIndex i) := by
    dsimp only [A, last]
    rw [S.boundaryAugmentedAmbientJordan_scaleGenerator]
    congr 1
  have hscaleLe : scaleIdeal C.space C.lattice ≤
      principalIdeal (K := K) (A.scaleGenerator last : K) := by
    rw [hscale]
    exact S.boundaryMappedTargetComplement_scaleIdeal_le f i
  refine {
    toLinearMap := inclusion
    injective := Subtype.val_injective
    map_bilin := by intro x y; rfl
    map_mem := ?_ }
  intro x hx
  change (x : ambient) ∈ scaleTruncation ambientForm
    (S.boundaryAugmentedAmbientLattice i)
      (ordUnit K (A.scaleGenerator last))
  rw [mem_scaleTruncation_iff_ord_bilin_ge]
  refine ⟨P.component_ambientSubmodule_le 1 ⟨x, hx, rfl⟩, ?_⟩
  intro y hy
  have hySum : y ∈ ⨆ j : Fin 2, (P.component j).ambientSubmodule := by
    rw [P.sum_eq]
    exact hy
  have hpairIdeal : ambientForm.bilin (x : ambient) y ∈
      principalIdeal (K := K) (A.scaleGenerator last : K) := by
    rw [OrthogonalDecomposition.iSup_fin_two_eq_sup_tail] at hySum
    change y ∈ (P.component 0).ambientSubmodule ⊔
      (P.component 1).ambientSubmodule at hySum
    rw [Submodule.mem_sup] at hySum
    rcases hySum with ⟨y₀, hy₀, y₁, hy₁, hdecomp⟩
    rcases hy₀ with ⟨z₀, hz₀, rfl⟩
    rcases hy₁ with ⟨z₁, hz₁, rfl⟩
    rw [← hdecomp, LinearMap.BilinForm.add_right]
    have horth : ambientForm.bilin (x : ambient)
        ((↑(P.component 0).carrier.subtype :
          (P.component 0).carrier →ₗ[IntegerRing K] ambient) z₀) = 0 := by
      change
        (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm).bilin
          (x : ambient) (z₀ : ambient) = 0
      exact P.orthogonal 1 0 (by decide) x z₀
    have hright : ambientForm.bilin (x : ambient)
        ((↑(P.component 1).carrier.subtype :
          (P.component 1).carrier →ₗ[IntegerRing K] ambient) z₁) ∈
          scaleIdeal C.space C.lattice := by
      change C.space.bilin x z₁ ∈ scaleIdeal C.space C.lattice
      exact bilin_mem_scaleIdeal_of_mem C.space C.lattice hx hz₁
    rw [horth, zero_add]
    exact hscaleLe hright
  rw [principalIdeal_eq_powerIdeal, mem_powerIdeal_iff] at hpairIdeal
  exact hpairIdeal

/-- The target complement norm group is contained in the source-envelope
norm group, since it lies in the intrinsic last scale layer. -/
theorem boundaryTargetComplement_normGroup_subset_lastSource
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    let A := S.boundaryAugmentedAmbientJordan i
    let C := (S.boundaryMappedTargetPrefixSplitting f i).component 1
    normGroupSet C.space C.lattice ⊆
      normGroupSet (A.component (Fin.last (i.val + 1))).space
        (A.component (Fin.last (i.val + 1))).lattice := by
  dsimp only
  have h :=
    (S.boundaryMappedTargetComplementToFundamentalRepresentation f i)
      |>.normGroupSet_subset
  change normGroupSet
      ((S.boundaryMappedTargetPrefixSplitting f i).component 1).space
      ((S.boundaryMappedTargetPrefixSplitting f i).component 1).lattice ⊆
    (S.boundaryAugmentedAmbientJordan i).fundamentalNormGroup
      (Fin.last (i.val + 1)) at h
  rw [← S.boundaryAugmentedAmbientJordan_isSaturated i
    (Fin.last (i.val + 1))] at h
  exact h

/-- The target-side complement has exactly the norm group of the modular
source envelope.  The two inclusions come respectively from the omitted
target component and from the intrinsic last scale layer of the enlargement.
-/
theorem boundaryMappedTargetComplement_normGroup_eq_lastSource
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    let A := S.boundaryAugmentedAmbientJordan i
    let C := (S.boundaryMappedTargetPrefixSplitting f i).component 1
    normGroupSet C.space C.lattice =
      normGroupSet (A.component (Fin.last (i.val + 1))).space
        (A.component (Fin.last (i.val + 1))).lattice := by
  dsimp only
  apply Set.Subset.antisymm
  · exact S.boundaryTargetComplement_normGroup_subset_lastSource f i
  · exact S.boundaryLastSource_normGroup_subset_targetComplement f i

/-- A chosen norm-generator vector on the target-side complement. -/
noncomputable def boundaryMappedTargetComplementNormVector
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    ((S.boundaryMappedTargetPrefixSplitting f i).component 1).carrier :=
  Classical.choose <| exists_isNormGenerator_of_finrank_pos
    ((S.boundaryMappedTargetPrefixSplitting f i).component 1).space
    ((S.boundaryMappedTargetPrefixSplitting f i).component 1).lattice
    (S.boundaryMappedTargetComplement_finrank_pos f i)

theorem boundaryMappedTargetComplementNormVector_spec
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    let C := (S.boundaryMappedTargetPrefixSplitting f i).component 1
    IsNormGenerator C.space C.lattice
        (S.boundaryMappedTargetComplementNormVector f i) ∧
      C.space.IsAnisotropic
        (S.boundaryMappedTargetComplementNormVector f i) :=
  Classical.choose_spec <| exists_isNormGenerator_of_finrank_pos
    ((S.boundaryMappedTargetPrefixSplitting f i).component 1).space
    ((S.boundaryMappedTargetPrefixSplitting f i).component 1).lattice
    (S.boundaryMappedTargetComplement_finrank_pos f i)

noncomputable def boundaryMappedTargetComplementNormGenerator
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) : Kˣ :=
  Units.mk0
    ((S.boundaryMappedTargetPrefixSplitting f i).component 1 |>.space.quadratic
      (S.boundaryMappedTargetComplementNormVector f i))
    (S.boundaryMappedTargetComplementNormVector_spec f i).2

/-- Flatten the target prefix retained by 82:7 and place its modular
orthogonal complement last. -/
noncomputable def boundaryMappedTargetAugmentedOrthogonalDecomposition
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    OrthogonalDecomposition
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (S.boundaryAugmentedAmbientLattice i) (i.val + 2) :=
  (S.boundaryMappedTargetPrefixSplitting f i).appendNested
    (S.boundaryMappedTargetPrefixJordan f i).toOrthogonalDecomposition

noncomputable def boundaryMappedTargetAugmentedNorm
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) : Fin (i.val + 2) → Kˣ :=
  Fin.lastCases (S.boundaryMappedTargetComplementNormGenerator f i)
    (fun a ↦ (S.boundaryMappedTargetPrefixJordan f i).normGenerator a)

/-- A retained target prefix component is unchanged by nested flattening. -/
noncomputable def boundaryMappedTargetAugmentedPrefixComponentIsometry
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) (a : Fin (i.val + 1)) :
    Isometry
      ((S.boundaryMappedTargetPrefixJordan f i).component a).space
      ((S.boundaryMappedTargetAugmentedOrthogonalDecomposition f i).component
        a.castSucc).space
      ((S.boundaryMappedTargetPrefixJordan f i).component a).lattice
      ((S.boundaryMappedTargetAugmentedOrthogonalDecomposition f i).component
        a.castSucc).lattice := by
  rw [boundaryMappedTargetAugmentedOrthogonalDecomposition,
    OrthogonalDecomposition.appendNested_castSucc]
  exact ((S.boundaryMappedTargetPrefixSplitting f i).component 0)
    |>.liftNestedIsometry
      ((S.boundaryMappedTargetPrefixJordan f i).component a)

theorem boundaryMappedTargetAugmented_modular
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) (a : Fin (i.val + 2)) :
    IsModular
      ((S.boundaryMappedTargetAugmentedOrthogonalDecomposition f i).component a).space
      ((S.boundaryMappedTargetAugmentedOrthogonalDecomposition f i).component a).lattice
      (S.boundaryAugmentedScale i a) := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) a
  · rw [boundaryMappedTargetAugmentedOrthogonalDecomposition,
      OrthogonalDecomposition.appendNested_last]
    simp only [boundaryAugmentedScale, Fin.lastCases_last]
    exact S.boundaryMappedTargetComplement_isModular f i
  · rw [S.boundaryAugmentedScale_eq_original i j.castSucc]
    have h :=
      ((S.boundaryMappedTargetPrefixJordan f i).modular j).mapLatticeIsometry
        (S.boundaryMappedTargetAugmentedPrefixComponentIsometry f i j)
    rw [S.boundaryMappedTargetPrefixJordan_scaleGenerator] at h
    simpa only [Fin.val_castSucc] using h

theorem boundaryMappedTargetAugmented_scaleIdeal_eq
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) (a : Fin (i.val + 2)) :
    scaleIdeal
        ((S.boundaryMappedTargetAugmentedOrthogonalDecomposition f i).component a).space
        ((S.boundaryMappedTargetAugmentedOrthogonalDecomposition f i).component a).lattice =
      principalIdeal (K := K) (S.boundaryAugmentedScale i a : K) := by
  exact (S.boundaryMappedTargetAugmented_modular f i a)
    |>.scaleIdeal_eq_principal <| by
      refine Fin.lastCases ?_ (fun j ↦ ?_) a
      · rw [boundaryMappedTargetAugmentedOrthogonalDecomposition,
          OrthogonalDecomposition.appendNested_last]
        exact S.boundaryMappedTargetComplement_finrank_pos f i
      · rw [boundaryMappedTargetAugmentedOrthogonalDecomposition,
          OrthogonalDecomposition.appendNested_castSucc,
          QuadraticSublattice.finrank_liftNested]
        change 0 < (S.boundaryMappedTargetPrefixJordan f i).componentRank j
        rw [S.boundaryMappedTargetPrefixJordan_componentRank]
        omega

theorem boundaryMappedTargetAugmented_normIdeal_eq
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) (a : Fin (i.val + 2)) :
    normIdeal
        ((S.boundaryMappedTargetAugmentedOrthogonalDecomposition f i).component a).space
        ((S.boundaryMappedTargetAugmentedOrthogonalDecomposition f i).component a).lattice =
      principalIdeal (K := K)
        (S.boundaryMappedTargetAugmentedNorm f i a : K) := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) a
  · rw [boundaryMappedTargetAugmentedOrthogonalDecomposition,
      OrthogonalDecomposition.appendNested_last]
    simp only [boundaryMappedTargetAugmentedNorm, Fin.lastCases_last]
    exact (S.boundaryMappedTargetComplementNormVector_spec f i).1.normIdeal_eq
  · let g := S.boundaryMappedTargetAugmentedPrefixComponentIsometry f i j
    calc
      normIdeal
          ((S.boundaryMappedTargetAugmentedOrthogonalDecomposition f i).component
            j.castSucc).space
          ((S.boundaryMappedTargetAugmentedOrthogonalDecomposition f i).component
            j.castSucc).lattice =
          normIdeal ((S.boundaryMappedTargetPrefixJordan f i).component j).space
            ((S.boundaryMappedTargetPrefixJordan f i).component j).lattice := by
        rw [← g.map_eq]
        exact normIdeal_map_isometry g.toQuadraticSpaceIsometry _
      _ = principalIdeal (K := K)
          ((S.boundaryMappedTargetPrefixJordan f i).normGenerator j : K) :=
        (S.boundaryMappedTargetPrefixJordan f i).normIdeal_eq j
      _ = principalIdeal (K := K)
          (S.boundaryMappedTargetAugmentedNorm f i j.castSucc : K) := by
        simp [boundaryMappedTargetAugmentedNorm]

/-- The target-side Jordan splitting of the same enlarged lattice. -/
noncomputable def boundaryMappedTargetAugmentedJordan
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    JordanDecomposition
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (S.boundaryAugmentedAmbientLattice i) (i.val + 2) where
  toOrthogonalDecomposition :=
    S.boundaryMappedTargetAugmentedOrthogonalDecomposition f i
  scaleGenerator := S.boundaryAugmentedScale i
  normGenerator := S.boundaryMappedTargetAugmentedNorm f i
  modular := S.boundaryMappedTargetAugmented_modular f i
  scaleIdeal_eq := S.boundaryMappedTargetAugmented_scaleIdeal_eq f i
  normIdeal_eq := S.boundaryMappedTargetAugmented_normIdeal_eq f i
  scaleOrder_strict := S.boundaryAugmentedScale_strict i

/-- Transporting the source compression to the ambient enlargement preserves
its fundamental norm groups. -/
theorem boundaryAugmentedAmbient_fundamentalNormGroup_eq_source
    (i : Fin (n + 1)) (a : Fin (i.val + 2)) :
    (S.boundaryAugmentedAmbientJordan i).fundamentalNormGroup a =
      S.sourceJordan.fundamentalNormGroup ⟨a.val, by omega⟩ := by
  calc
    (S.boundaryAugmentedAmbientJordan i).fundamentalNormGroup a =
        (S.boundaryAugmentedJordan i).fundamentalNormGroup a := by
      unfold fundamentalNormGroup fundamentalLattice fundamentalScaleOrder
      exact normGroupSet_scaleTruncation_eq_of_isometry
        (S.boundaryAugmentedAmbientIsometry i) _
    _ = S.sourceJordan.fundamentalNormGroup ⟨a.val, by omega⟩ :=
      S.boundaryAugmented_fundamentalNormGroup_eq_source i a

/-- The target augmented splitting has the same intrinsic fundamental norm
groups as the source augmented splitting, because both use the same lattice
and the same scale generators. -/
theorem boundaryMappedTargetAugmented_fundamentalNormGroup_eq_sourceAmbient
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) (a : Fin (i.val + 2)) :
    (S.boundaryMappedTargetAugmentedJordan f i).fundamentalNormGroup a =
      (S.boundaryAugmentedAmbientJordan i).fundamentalNormGroup a := by
  rfl

/-- A component of the mapped target initial segment is the corresponding
component of the full mapped target Jordan decomposition. -/
noncomputable def boundaryMappedTargetPrefixComponentIsometry
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) (a : Fin (i.val + 1)) :
    Isometry
      ((S.boundaryMappedTargetJordan f).component ⟨a.val, by omega⟩).space
      ((S.boundaryMappedTargetPrefixJordan f i).component a).space
      ((S.boundaryMappedTargetJordan f).component ⟨a.val, by omega⟩).lattice
      ((S.boundaryMappedTargetPrefixJordan f i).component a).lattice := by
  change Isometry
    ((S.boundaryMappedTargetJordan f).component ⟨a.val, by omega⟩).space
    (((S.boundaryMappedTargetJordan f).initialSegment i.val
      (by omega)).component a).space
    ((S.boundaryMappedTargetJordan f).component ⟨a.val, by omega⟩).lattice
    (((S.boundaryMappedTargetJordan f).initialSegment i.val
      (by omega)).component a).lattice
  let g := (S.boundaryMappedTargetJordan f).initialSegmentComponentIsometry
    i.val (by omega) a
  have hidx :
      ((S.boundaryMappedTargetJordan f).toOrthogonalDecomposition
        |>.prefixIndexEquiv (i.val + 1) (by omega) a).1 =
        (⟨a.val, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  rw [← hidx]
  exact g

/-- Every displayed target component in the Step-2 enlargement realizes the
same source fundamental norm group. -/
theorem boundaryMappedTargetAugmented_componentNormGroup_eq_sourceFundamental
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) (a : Fin (i.val + 2)) :
    normGroupSet
        ((S.boundaryMappedTargetAugmentedJordan f i).component a).space
        ((S.boundaryMappedTargetAugmentedJordan f i).component a).lattice =
      S.sourceJordan.fundamentalNormGroup ⟨a.val, by omega⟩ := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) a
  · let A := S.boundaryAugmentedAmbientJordan i
    change normGroupSet
        ((S.boundaryMappedTargetAugmentedOrthogonalDecomposition f i).component
          (Fin.last (i.val + 1))).space
        ((S.boundaryMappedTargetAugmentedOrthogonalDecomposition f i).component
          (Fin.last (i.val + 1))).lattice =
      S.sourceJordan.fundamentalNormGroup
        ⟨(Fin.last (i.val + 1)).val, by omega⟩
    rw [boundaryMappedTargetAugmentedOrthogonalDecomposition,
      OrthogonalDecomposition.appendNested_last]
    calc
      normGroupSet
          ((S.boundaryMappedTargetPrefixSplitting f i).component 1).space
          ((S.boundaryMappedTargetPrefixSplitting f i).component 1).lattice =
          normGroupSet (A.component (Fin.last (i.val + 1))).space
            (A.component (Fin.last (i.val + 1))).lattice :=
        S.boundaryMappedTargetComplement_normGroup_eq_lastSource f i
      _ = A.fundamentalNormGroup (Fin.last (i.val + 1)) :=
        S.boundaryAugmentedAmbientJordan_isSaturated i _
      _ = S.sourceJordan.fundamentalNormGroup
          ⟨(Fin.last (i.val + 1)).val, by omega⟩ :=
        S.boundaryAugmentedAmbient_fundamentalNormGroup_eq_source i _
  · let idx : Fin (n + 2) := ⟨j.val, by omega⟩
    let mapped := (S.targetJordan.component idx).mapLatticeIsometry f.symm
    let prefixIso := S.boundaryMappedTargetPrefixComponentIsometry f i j
    let lifted := S.boundaryMappedTargetAugmentedPrefixComponentIsometry f i j
    let total := mapped.trans (prefixIso.trans lifted)
    change normGroupSet
        ((S.boundaryMappedTargetAugmentedJordan f i).component j.castSucc).space
        ((S.boundaryMappedTargetAugmentedJordan f i).component j.castSucc).lattice =
      S.sourceJordan.fundamentalNormGroup ⟨j.castSucc.val, by omega⟩
    have hidx : idx = (⟨j.castSucc.val, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    calc
      normGroupSet
          ((S.boundaryMappedTargetAugmentedJordan f i).component j.castSucc).space
          ((S.boundaryMappedTargetAugmentedJordan f i).component j.castSucc).lattice =
          normGroupSet (S.targetJordan.component idx).space
            (S.targetJordan.component idx).lattice :=
        normGroupSet_eq_of_latticeIsometry total
      _ = normGroupSet (S.sourceJordan.component idx).space
          (S.sourceJordan.component idx).lattice :=
        (S.targetJordan_component_normGroupSet idx).trans
          (S.sourceJordan_component_normGroupSet idx).symm
      _ = S.sourceJordan.fundamentalNormGroup idx :=
        S.sourceJordan_isSaturated idx
      _ = S.sourceJordan.fundamentalNormGroup
          ⟨j.castSucc.val, by omega⟩ := by rw [hidx]

/-- The target Jordan splitting of the enlarged lattice is saturated. -/
theorem boundaryMappedTargetAugmentedJordan_isSaturated
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    (S.boundaryMappedTargetAugmentedJordan f i).IsSaturated := by
  intro a
  calc
    normGroupSet
        ((S.boundaryMappedTargetAugmentedJordan f i).component a).space
        ((S.boundaryMappedTargetAugmentedJordan f i).component a).lattice =
        S.sourceJordan.fundamentalNormGroup ⟨a.val, by omega⟩ :=
      S.boundaryMappedTargetAugmented_componentNormGroup_eq_sourceFundamental
        f i a
    _ = (S.boundaryAugmentedAmbientJordan i).fundamentalNormGroup a :=
      (S.boundaryAugmentedAmbient_fundamentalNormGroup_eq_source i a).symm
    _ = (S.boundaryMappedTargetAugmentedJordan f i).fundamentalNormGroup a :=
      (S.boundaryMappedTargetAugmented_fundamentalNormGroup_eq_sourceAmbient
        f i a).symm

theorem boundaryAugmentedAmbient_fundamentalScaleOrder_eq_source
    (i : Fin (n + 1)) (a : Fin (i.val + 2)) :
    (S.boundaryAugmentedAmbientJordan i).fundamentalScaleOrder a =
      S.sourceJordan.fundamentalScaleOrder ⟨a.val, by omega⟩ := by
  unfold fundamentalScaleOrder
  rw [S.boundaryAugmentedAmbientJordan_scaleGenerator,
    S.sourceJordan_scaleGenerator]

/-- Reuse the original source fundamental norm generators, index for index,
on the Step-2 compressed source lattice. -/
noncomputable def boundaryAugmentedAmbientFundamentalNormGeneratorChoice
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (i : Fin (n + 1)) :
    FundamentalNormGeneratorChoice (S.boundaryAugmentedAmbientJordan i) where
  value := fun a ↦ A.value ⟨a.val, by omega⟩
  spec := by
    intro a
    exact isNormGeneratorValue_of_normGroupSet_eq
      (A.spec ⟨a.val, by omega⟩)
      (S.boundaryAugmentedAmbient_fundamentalNormGroup_eq_source i a).symm
      ((S.boundaryAugmentedAmbientJordan i).exists_fundamentalNormGenerator a)

@[simp]
theorem boundaryAugmentedAmbientFundamentalNormGeneratorChoice_value
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (i : Fin (n + 1)) (a : Fin (i.val + 2)) :
    (S.boundaryAugmentedAmbientFundamentalNormGeneratorChoice A i).value a =
      A.value ⟨a.val, by omega⟩ :=
  rfl

/-- The last boundary ideal of the compressed source is the selected
boundary ideal of the original source chain. -/
theorem boundaryAugmentedAmbient_lastFundamentalIdeal_eq_source
    (i : Fin (n + 1)) :
    let j : Fin (i.val + 1) := Fin.last i.val
    (S.boundaryAugmentedAmbientJordan i).fundamentalIdeal j =
      S.sourceJordan.fundamentalIdeal i := by
  dsimp only
  let A := S.boundaryAugmentedAmbientJordan i
  let j : Fin (i.val + 1) := Fin.last i.val
  apply fundamentalIdeal_eq_of_boundaryData_eq
    (J := S.sourceJordan) (H := A) i j
  · have h :=
      S.boundaryAugmentedAmbient_fundamentalScaleOrder_eq_source i
        (boundaryLeftIndex j)
    convert h using 1 <;> apply congrArg <;> apply Fin.ext <;>
      simp [j, boundaryLeftIndex]
  · have h :=
      S.boundaryAugmentedAmbient_fundamentalNormGroup_eq_source i
        (boundaryLeftIndex j)
    convert h using 1 <;> apply congrArg <;> apply Fin.ext <;>
      simp [j, boundaryLeftIndex]
  · have h :=
      S.boundaryAugmentedAmbient_fundamentalNormGroup_eq_source i
        (boundaryRightIndex j)
    convert h using 1 <;> apply congrArg <;> apply Fin.ext <;>
      simp [j, boundaryRightIndex]

/-- The right-hand threshold at the last compressed boundary is exactly the
threshold at the selected original boundary, with the same scalar generator.
-/
theorem boundaryAugmentedAmbient_lastFourNormOverWeightIdealWith_eq_source
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (i : Fin (n + 1)) :
    let j : Fin (i.val + 1) := Fin.last i.val
    let C := S.boundaryAugmentedAmbientFundamentalNormGeneratorChoice A i
    (S.boundaryAugmentedAmbientJordan i).fourNormOverWeightIdealWith C
        (boundaryRightIndex j) =
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex i) := by
  dsimp only
  let B := S.boundaryAugmentedAmbientJordan i
  let j : Fin (i.val + 1) := Fin.last i.val
  have hscale := S.boundaryAugmentedAmbient_fundamentalScaleOrder_eq_source i
    (boundaryRightIndex j)
  have hnorm := S.boundaryAugmentedAmbient_fundamentalNormGroup_eq_source i
    (boundaryRightIndex j)
  have hweight := fundamentalWeightOrder_eq_of_scaleOrder_normGroup_eq_at
    (J := S.sourceJordan) (H := B)
    (boundaryRightIndex i) (boundaryRightIndex j)
    (by
      convert hscale using 1 <;> apply congrArg <;> apply Fin.ext <;>
        simp [j, boundaryRightIndex])
    (by
      convert hnorm using 1 <;> apply congrArg <;> apply Fin.ext <;>
        simp [j, boundaryRightIndex])
  unfold fourNormOverWeightIdealWith
  rw [hweight]
  congr 1

/-- The whole compressed suffix still has rank at least two. -/
theorem boundarySuffix_finrank_atLeastTwo (i : Fin (n + 1)) :
    2 ≤ finrank K (S.boundarySuffix i).carrier := by
  have h := (S.boundarySuffixTowerIsometry i).toLinearEquiv.finrank_eq
  rw [QuadraticSpace.finrank_hyperbolicExtension_zero] at h
  rw [h]
  omega

theorem boundaryAugmentedAmbient_componentRank_atLeastTwo
    (i : Fin (n + 1)) (a : Fin (i.val + 2)) :
    2 ≤ (S.boundaryAugmentedAmbientJordan i).componentRank a := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) a
  · rw [boundaryAugmentedAmbientJordan, mapIsometry_componentRank]
    unfold componentRank
    change 2 ≤ finrank K
      ((S.boundaryAugmentedOrthogonalDecomposition i).component
        (Fin.last (i.val + 1))).carrier
    let g := S.boundaryAugmentedLastComponentIsometry i
    rw [← g.toLinearEquiv.finrank_eq]
    exact S.boundarySuffix_finrank_atLeastTwo i
  · rw [S.boundaryAugmentedAmbientJordan_componentRank_castSucc]
    omega

/-- The source and target Step-2 splittings form a new rank-four reduction
problem on the same enlarged lattice. -/
noncomputable def boundaryAugmentedReductionSystem
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    Omeara9328RankFourReductionSystem
      (S.boundaryAugmentedAmbientJordan i)
      (S.boundaryMappedTargetAugmentedJordan f i) where
  sourceSaturated := S.boundaryAugmentedAmbientJordan_isSaturated i
  targetSaturated := S.boundaryMappedTargetAugmentedJordan_isSaturated f i
  fundamentalType := sameFundamentalTypeOfIsometry
    (S.boundaryAugmentedAmbientJordan i)
    (S.boundaryMappedTargetAugmentedJordan f i)
    (Isometry.refl
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (S.boundaryAugmentedAmbientLattice i))
  componentRank_atLeastTwo :=
    S.boundaryAugmentedAmbient_componentRank_atLeastTwo i

/-- A raw source residual component is carried to the corresponding prefix
component of the ambient Step-2 source splitting. -/
noncomputable def boundaryAugmentedSourcePrefixComponentIsometry
    (i : Fin (n + 1)) (a : Fin (i.val + 1)) :
    Isometry
      (S.prefixSourceForm (S.boundaryPrefix_le i) a)
      ((S.boundaryAugmentedAmbientJordan i).component a.castSucc).space
      (S.prefixSourceLattice (S.boundaryPrefix_le i) a)
      ((S.boundaryAugmentedAmbientJordan i).component a.castSucc).lattice := by
  let raw := BONG.blockProductComponentIsometry
    (S.prefixSourceCarrier (S.boundaryPrefix_le i))
    (S.prefixSourceForm (S.boundaryPrefix_le i))
    (S.prefixSourceLattice (S.boundaryPrefix_le i)) a
  let nested := S.boundaryAugmentedPrefixComponentIsometry i a
  let ambient := ((S.boundaryAugmentedJordan i).component a.castSucc)
    |>.mapLatticeIsometry (S.boundaryAugmentedAmbientIsometry i)
  exact raw.trans (nested.trans ambient)

/-- A raw target residual component is carried to the corresponding prefix
component of the target Step-2 splitting. -/
noncomputable def boundaryMappedTargetAugmentedPrefixRawComponentIsometry
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) (a : Fin (i.val + 1)) :
    Isometry
      (S.prefixTargetForm (S.boundaryPrefix_le i) a)
      ((S.boundaryMappedTargetAugmentedJordan f i).component a.castSucc).space
      (S.prefixTargetLattice (S.boundaryPrefix_le i) a)
      ((S.boundaryMappedTargetAugmentedJordan f i).component a.castSucc).lattice := by
  let idx := S.prefixIndex (S.boundaryPrefix_le i) a
  let raw := BONG.blockProductComponentIsometry
    S.targetCarrier S.targetForm S.targetLattice idx
  let mapped := (S.targetJordan.component idx).mapLatticeIsometry f.symm
  have hidx : idx = (⟨a.val, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    exact S.prefixIndex_val (S.boundaryPrefix_le i) a
  let initial := S.boundaryMappedTargetPrefixComponentIsometry f i a
  let lifted := S.boundaryMappedTargetAugmentedPrefixComponentIsometry f i a
  rw [hidx] at raw mapped
  exact raw.trans (mapped.trans (initial.trans lifted))

/-- The selected original source prefix is integrally isometric to the full
retained prefix of the compressed source splitting. -/
noncomputable def boundaryAugmentedSourcePrefixIsometry
    (i : Fin (n + 1)) :
    Isometry
      (S.sourceJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (i.val + 1)).space
      ((S.boundaryAugmentedAmbientJordan i).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (i.val + 1)).space
      (S.sourceJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (i.val + 1)).lattice
      ((S.boundaryAugmentedAmbientJordan i).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (i.val + 1)).lattice := by
  let hk := S.boundaryPrefix_le i
  let A := S.boundaryAugmentedAmbientJordan i
  let D := A.toOrthogonalDecomposition
  let hA : i.val + 1 ≤ i.val + 2 := by omega
  let component : ∀ a : Fin (i.val + 1), Isometry
      (S.prefixSourceForm hk a) (D.prefixBlockSpace hA a)
      (S.prefixSourceLattice hk a) (D.prefixBlockLattice hA a) := by
    intro a
    let g := S.boundaryAugmentedSourcePrefixComponentIsometry i a
    have hidx : (D.prefixIndexEquiv (i.val + 1) hA a).1 = a.castSucc := by
      apply Fin.ext
      rfl
    cases hidx
    exact g
  let coordinate := BONG.blockProductLatticeIsometry
    (S.prefixSourceForm hk) (D.prefixBlockSpace hA)
    (S.prefixSourceLattice hk) (D.prefixBlockLattice hA) component
  exact (S.rawSourceResidualPrefixIsometry hk).symm.trans <|
    coordinate.trans (D.prefixBlockProductIsometry hA)

/-- The selected original target prefix is integrally isometric to the full
retained prefix of the target Step-2 splitting. -/
noncomputable def boundaryMappedTargetAugmentedPrefixIsometry
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    Isometry
      (S.targetJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (i.val + 1)).space
      ((S.boundaryMappedTargetAugmentedJordan f i).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (i.val + 1)).space
      (S.targetJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (i.val + 1)).lattice
      ((S.boundaryMappedTargetAugmentedJordan f i).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (i.val + 1)).lattice := by
  let hk := S.boundaryPrefix_le i
  let A := S.boundaryMappedTargetAugmentedJordan f i
  let D := A.toOrthogonalDecomposition
  let hA : i.val + 1 ≤ i.val + 2 := by omega
  let component : ∀ a : Fin (i.val + 1), Isometry
      (S.prefixTargetForm hk a) (D.prefixBlockSpace hA a)
      (S.prefixTargetLattice hk a) (D.prefixBlockLattice hA a) := by
    intro a
    let g :=
      S.boundaryMappedTargetAugmentedPrefixRawComponentIsometry f i a
    have hidx : (D.prefixIndexEquiv (i.val + 1) hA a).1 = a.castSucc := by
      apply Fin.ext
      rfl
    cases hidx
    exact g
  let coordinate := BONG.blockProductLatticeIsometry
    (S.prefixTargetForm hk) (D.prefixBlockSpace hA)
    (S.prefixTargetLattice hk) (D.prefixBlockLattice hA) component
  exact (S.rawTargetResidualPrefixIsometry hk).symm.trans <|
    coordinate.trans (D.prefixBlockProductIsometry hA)

/-- O'Meara 93:28(ii) at an arbitrary boundary of the rank-four residual
system.  This is Step 2: enlarge the suffix by 93:3, split the target prefix
by 82:7, apply the already proved last-boundary theorem, and transport the
representation back to the original prefixes. -/
theorem boundary_conditionIIWith
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (i : Fin (n + 1)) :
    S.sourceJordan.fundamentalIdeal i <
        S.sourceJordan.fourNormOverWeightIdealWith A
          (boundaryRightIndex i) →
      QuadraticSublattice.EmbedsIntoOrthogonalSum
        (S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (i.val + 1))
        (S.targetJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (i.val + 1))
        (QuadraticSpace.scaledLine (A.value (boundaryRightIndex i))) := by
  intro htrigger
  let sourceAug := S.boundaryAugmentedAmbientJordan i
  let targetAug := S.boundaryMappedTargetAugmentedJordan f i
  let R := S.boundaryAugmentedReductionSystem f i
  let B := S.boundaryAugmentedAmbientFundamentalNormGeneratorChoice A i
  let j : Fin (i.val + 1) := Fin.last i.val
  have htriggerAug : sourceAug.fundamentalIdeal j <
      sourceAug.fourNormOverWeightIdealWith B (boundaryRightIndex j) := by
    rw [S.boundaryAugmentedAmbient_lastFundamentalIdeal_eq_source i,
      S.boundaryAugmentedAmbient_lastFourNormOverWeightIdealWith_eq_source A i]
    exact htrigger
  let identity : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (S.boundaryAugmentedAmbientLattice i)
      (S.boundaryAugmentedAmbientLattice i) :=
    Isometry.refl _ _
  let residual := R.residualIsometryOfOriginalIsometry identity
  have hAug := R.lastBoundary_conditionIIWith residual B htriggerAug
  let sourcePrefix := S.boundaryAugmentedSourcePrefixIsometry i
  let targetPrefix := S.boundaryMappedTargetAugmentedPrefixIsometry f i
  have hvalue : B.value (boundaryRightIndex j) =
      A.value (boundaryRightIndex i) := by
    change A.value ⟨(boundaryRightIndex j).val, by omega⟩ =
      A.value (boundaryRightIndex i)
    congr 1
  let lineIdentify : QuadraticSpace.Isometry
      (QuadraticSpace.scaledLine (B.value (boundaryRightIndex j)))
      (QuadraticSpace.scaledLine (A.value (boundaryRightIndex i))) := by
    rw [hvalue]
    exact QuadraticSpace.Isometry.refl _
  rcases hAug with ⟨g⟩
  exact ⟨(targetPrefix.symm.toQuadraticSpaceIsometry
      |>.orthogonalSum lineIdentify).toRepresentation.trans
    (g.trans sourcePrefix.toQuadraticSpaceIsometry.toRepresentation)⟩

/-- Condition 93:28(i) at the last residual boundary.  It is the first
boundary of the reverse dual; the full determinant isometry cancels the
complementary suffix. -/
theorem lastBoundary_conditionI
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    let j : Fin (n + 1) := Fin.last n
    BONG.GoodBONG.UnitsCongruentModulo
      (S.targetJordan.prefixDeterminantUnit j)
      (S.sourceJordan.prefixDeterminantUnit j)
      (S.sourceJordan.fundamentalIdeal j) := by
  dsimp only
  let j : Fin (n + 1) := Fin.last n
  have hrevRaw := S.reverseResidual_firstBoundary_conditionI f
  have hrev : BONG.GoodBONG.UnitsCongruentModulo
      (S.targetJordan.reverseDual.prefixDeterminantUnit (Fin.rev j))
      (S.sourceJordan.reverseDual.prefixDeterminantUnit (Fin.rev j))
      (S.sourceJordan.reverseDual.fundamentalIdeal (Fin.rev j)) := by
    simpa only [j, Fin.rev_last] using hrevRaw
  exact boundary_conditionI_of_reverseDual_boundary f j hrev

/-- O'Meara 93:28(i) at an arbitrary residual boundary.  The boundary
augmentation turns it into the last boundary, while its two prefix
isometries preserve determinant square classes. -/
theorem boundary_conditionI
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin (n + 1)) :
    BONG.GoodBONG.UnitsCongruentModulo
      (S.targetJordan.prefixDeterminantUnit i)
      (S.sourceJordan.prefixDeterminantUnit i)
      (S.sourceJordan.fundamentalIdeal i) := by
  let sourceAug := S.boundaryAugmentedAmbientJordan i
  let targetAug := S.boundaryMappedTargetAugmentedJordan f i
  let R := S.boundaryAugmentedReductionSystem f i
  let j : Fin (i.val + 1) := Fin.last i.val
  let identity : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (S.boundaryAugmentedAmbientLattice i)
      (S.boundaryAugmentedAmbientLattice i) :=
    Isometry.refl _ _
  let residual := R.residualIsometryOfOriginalIsometry identity
  have hAugResidual := R.lastBoundary_conditionI residual
  have hAug := R.boundary_conditionI_of_rankFour j hAugResidual
  have hAug' : BONG.GoodBONG.UnitsCongruentModulo
      (targetAug.prefixDeterminantUnit j)
      (sourceAug.prefixDeterminantUnit j)
      (S.sourceJordan.fundamentalIdeal i) := by
    rw [← S.boundaryAugmentedAmbient_lastFundamentalIdeal_eq_source i]
    exact hAug
  let sourcePrefix := S.boundaryAugmentedSourcePrefixIsometry i
  let targetPrefix := S.boundaryMappedTargetAugmentedPrefixIsometry f i
  have htarget : unitSquareClass K (targetAug.prefixDeterminantUnit j) =
      unitSquareClass K (S.targetJordan.prefixDeterminantUnit i) := by
    change determinantClass
        (targetAug.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (j.val + 1)).space
        (targetAug.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (j.val + 1)).lattice =
      determinantClass
        (S.targetJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (i.val + 1)).space
        (S.targetJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (i.val + 1)).lattice
    exact (determinantClass_eq_of_isometry targetPrefix).symm
  have hsource : unitSquareClass K (sourceAug.prefixDeterminantUnit j) =
      unitSquareClass K (S.sourceJordan.prefixDeterminantUnit i) := by
    change determinantClass
        (sourceAug.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (j.val + 1)).space
        (sourceAug.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (j.val + 1)).lattice =
      determinantClass
        (S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (i.val + 1)).space
        (S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (i.val + 1)).lattice
    exact (determinantClass_eq_of_isometry sourcePrefix).symm
  exact BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
    (targetAug.prefixDeterminantUnit j)
    (S.targetJordan.prefixDeterminantUnit i)
    (sourceAug.prefixDeterminantUnit j)
    (S.sourceJordan.prefixDeterminantUnit i)
    (S.sourceJordan.fundamentalIdeal i) htarget hsource hAug'

/-- The reverse-dual reduction system with source and target exchanged.  It
is the system used in Step 3 of O'Meara 93:28. -/
noncomputable def swappedReverseResidualSystem :
    Omeara9328RankFourReductionSystem
      S.targetJordan.reverseDual S.sourceJordan.reverseDual where
  sourceSaturated := S.targetJordan_isSaturated.reverseDual
  targetSaturated := S.sourceJordan_isSaturated.reverseDual
  fundamentalType := S.residualFundamentalType.symm.reverseDual
  componentRank_atLeastTwo := by
    intro k
    rw [reverseDual_componentRank, S.targetJordan_componentRank]
    omega

/-- O'Meara 93:28(iii) at every boundary of the rank-four residual system.
This is Step 3: apply the general-boundary form of (ii) to the exchanged
reverse-dual system, lift it from its rank-four residuals, and cancel the
complementary suffix. -/
theorem boundary_conditionIIIWith
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (A : FundamentalNormGeneratorChoice S.sourceJordan) :
    S.sourceJordan.Omeara9328ConditionIIIWith S.targetJordan A := by
  let F := S.residualFundamentalType
  let B := (A.ofSameFundamentalType F).reverseDual
  let T := S.swappedReverseResidualSystem
  let g := T.residualIsometryOfOriginalIsometry f.dual.symm
  have hIIResidual : T.sourceJordan.Omeara9328ConditionIIWith
      T.targetJordan (T.sourceFundamentalNormGeneratorChoice B) := by
    intro i htrigger
    exact T.boundary_conditionIIWith g
      (T.sourceFundamentalNormGeneratorChoice B) i htrigger
  have hII : S.targetJordan.reverseDual.Omeara9328ConditionIIWith
      S.sourceJordan.reverseDual B :=
    T.omeara9328ConditionIIWith_of_rankFour B hIIResidual
  exact omeara9328ConditionIIIWith_of_reverseDual_conditionIIWith
    ⟨f.toQuadraticSpaceIsometry⟩ F A hII

/-- All three O'Meara 93:28 conditions for the rank-four residual pair follow
from an integral isometry. -/
theorem residualConditionsWith_of_isometry
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (A : FundamentalNormGeneratorChoice S.sourceJordan) :
    S.sourceJordan.Omeara9328ConditionsWith S.targetJordan A := by
  refine ⟨?_, ?_, S.boundary_conditionIIIWith f A⟩
  · intro i
    exact S.boundary_conditionI f i
  · intro i htrigger
    exact S.boundary_conditionIIWith f A i htrigger

/-- Necessity of O'Meara 93:28 for a saturated pair whose source Jordan
components have rank at least two.  The residual theorem is lifted through
the simultaneous rank-four reduction. -/
theorem conditionsWith_of_isometry
    (S : Omeara9328RankFourReductionSystem J H)
    (f : Lattice.Isometry q r L M)
    (A : FundamentalNormGeneratorChoice J) :
    J.Omeara9328ConditionsWith H A := by
  let residual :=
    Omeara9328RankFourReductionSystem.residualIsometryOfOriginalIsometry S f
  let AR := S.sourceFundamentalNormGeneratorChoice A
  have hResidual : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan AR :=
    S.residualConditionsWith_of_isometry residual AR
  exact S.omeara9328ConditionsWith_of_rankFour A hResidual

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
