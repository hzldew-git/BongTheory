/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714TypeIIStopBridge

/-!
# Beli (2019), Lemma 7.14(ii): unconditional endpoint closure

The explicit reverse-dual construction now supplies the stopping-node
isometry and all of its basis equations.  This file repackages those concrete
data into the dependent endpoint interface of Lemma 7.10 and removes the last
external endpoint certificate from the Type-II lattice identity.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

attribute [local instance]
  BONG.OrthogonalPrefixRawSeed.StopSourceData.addCommGroup
  BONG.OrthogonalPrefixRawSeed.StopSourceData.module

section Closure

variable [DyadicDiscriminantClassLaws K]
variable [BONGReverseDualLaws.{u, v} K]
variable [BeliLemma43ConstructionLaws.{u, v} K]
variable (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
variable (D : Lemma714StoppingData b R s)
variable (hfirst : b.order ⟨0, by omega⟩ = R)
variable (hsecond : b.order ⟨1, by omega⟩ =
  R - 2 * (ramificationIndex K : Int))
variable (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
variable (hsCurrent : s < n + 3)
variable (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
variable (S : BONG.TwoBlockSplitWitness b.toBONG 2 (by omega))
variable (hsFour : s = 2 ∨ 4 ≤ s)
variable (U : (b.lemma714Tail S).toBONG.TwoBlockSplitWitness
  (s - 2) (by have := D.le_rank; omega))
variable (block : GoodBONG
  ((q.restrict S.left.carrier S.left.nondegenerate).orthogonalSum
    ((q.restrict S.right.carrier S.right.nondegenerate).restrict
      (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).carrier
      (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).nondegenerate))
  (Lattice.product
    (Lattice.rescale (uniformizerUnit K) S.left.lattice)
    (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).lattice) 3)
variable {N : Lattice K (S.right.carrier × S.left.carrier)}
variable (target : GoodBONG
  ((q.restrict S.right.carrier S.right.nondegenerate).orthogonalSum
    (q.restrict S.left.carrier S.left.nondegenerate)) N (n + 3))
variable (htargetVectors : ∀ i, target.toBONG.ambientVector i =
  lemma714TypeIITargetVector b S s D.two_le hsCurrent block i)

/-- The concrete stopping isometry, exposed in the non-dependent stopping
source package together with its equations on every segment vector. -/
noncomputable def lemma714TypeIIOuterStopSourceProductData :
    let model := b.lemma714TypeIIOuterModel R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors
    model.extraction.seed.StopSourceSegmentProductIsometryData
      model.segment := by
  dsimp only
  refine ⟨b.lemma714TypeIIOuterSegmentToStopProduct R s D hfirst hsecond
    hthird hsCurrent hcurrent S hsFour U block target htargetVectors, ?_⟩
  intro i
  exact b.lemma714TypeIIOuterSegmentToStopProduct_apply_ambientVector R s D
    hfirst hsecond hthird hsCurrent hcurrent S hsFour U block target
    htargetVectors i

/-- The endpoint datum required by the first Lemma-7.10 application is now
constructed internally from the reverse-dual replacement. -/
noncomputable def lemma714TypeIIEndpointDataUnconditional :
    Lemma714TypeIIEndpointData (b := b) (R := R) (s := s) (D := D)
      (hfirst := hfirst) (hsecond := hsecond) (hthird := hthird)
      (hsCurrent := hsCurrent) (S := S) (hsFour := hsFour) (U := U)
      (block := block) (target := target)
      (htargetVectors := htargetVectors) := by
  let model := b.lemma714TypeIIOuterModel R s D hfirst hsecond hthird
    hsCurrent S hsFour U block target htargetVectors
  let exposed := b.lemma714TypeIIOuterStopSourceProductData R s D hfirst
    hsecond hthird hsCurrent hcurrent S hsFour U block target htargetVectors
  let dependent :=
    BONG.OrthogonalPrefixRawSeed.StopSourceSegmentProductIsometryData.toDependent
      model.extraction.seed model.segment exposed
  exact ⟨dependent.1, dependent.2⟩

include hfirst hsecond hthird hcurrent hsFour block target htargetVectors
/-- Unconditional Type-II lattice equality in the reframed coordinates. -/
theorem lemma714TypeIIReframedTarget_lattice_eq_unconditional :
    Lattice.map
        (b.lemma714TypeIIFrameIsometry S s D.two_le D.le_rank U).toLinearEquiv N =
      Lattice.product
        (Lattice.product U.left.lattice
          (Lattice.rescale (uniformizerUnit K) S.left.lattice))
        U.right.lattice := by
  exact b.lemma714TypeIIReframedTarget_lattice_eq R s D hfirst hsecond hthird
    hsCurrent hcurrent S hsFour U block target htargetVectors
    (b.lemma714TypeIIEndpointDataUnconditional R s D hfirst hsecond hthird
      hsCurrent hcurrent S hsFour U block target htargetVectors)

/-- Regard the frame map itself as an integral isometry from the initially
constructed target lattice to the now-identified stopping product. -/
noncomputable def lemma714TypeIIFrameFromTargetIsometry :
    Lattice.Isometry
      ((q.restrict S.right.carrier S.right.nondegenerate).orthogonalSum
        (q.restrict S.left.carrier S.left.nondegenerate))
      ((((q.restrict S.right.carrier S.right.nondegenerate).restrict
          U.left.carrier U.left.nondegenerate).orthogonalSum
        (q.restrict S.left.carrier S.left.nondegenerate)).orthogonalSum
        ((q.restrict S.right.carrier S.right.nondegenerate).restrict
          U.right.carrier U.right.nondegenerate))
      N
      (Lattice.product
        (Lattice.product U.left.lattice
          (Lattice.rescale (uniformizerUnit K) S.left.lattice))
        U.right.lattice) :=
  Lattice.Isometry.ofMapEq
    ((q.restrict S.right.carrier S.right.nondegenerate).orthogonalSum
      (q.restrict S.left.carrier S.left.nondegenerate))
    (b.lemma714TypeIIFrameIsometry S s D.two_le D.le_rank U).toQuadraticSpaceIsometry
    N
    (Lattice.product
      (Lattice.product U.left.lattice
        (Lattice.rescale (uniformizerUnit K) S.left.lattice))
      U.right.lattice)
    (b.lemma714TypeIIReframedTarget_lattice_eq_unconditional R s D hfirst
      hsecond hthird hsCurrent hcurrent S hsFour U block target
      htargetVectors)

/-- Return from the Lemma-7.10 frame, swap the two original factors, and
obtain the exact split model `pi J perp tail`. -/
noncomputable def lemma714TypeIITargetToRescaledProductIsometry :
    Lattice.Isometry
      ((q.restrict S.right.carrier S.right.nondegenerate).orthogonalSum
        (q.restrict S.left.carrier S.left.nondegenerate))
      ((q.restrict S.left.carrier S.left.nondegenerate).orthogonalSum
        (q.restrict S.right.carrier S.right.nondegenerate))
      N
      (Lattice.product
        (Lattice.rescale (uniformizerUnit K) S.left.lattice)
        S.right.lattice) :=
  (b.lemma714TypeIIFrameFromTargetIsometry R s D hfirst hsecond hthird
      hsCurrent hcurrent S hsFour U block target htargetVectors).trans
    ((b.lemma714TypeIIFrameIsometry S s D.two_le D.le_rank U).symm.trans
      (Lattice.orthogonalProductSwap
        (q := q.restrict S.right.carrier S.right.nondegenerate)
        (r := q.restrict S.left.carrier S.left.nondegenerate)
        (L := S.right.lattice)
        (M := Lattice.rescale (uniformizerUnit K) S.left.lattice)))

/-- The type-II candidate, now placed on the literal split lattice
`pi J perp tail` rather than on an existentially generated lattice. -/
noncomputable def lemma714TypeIIRescaledProductGoodBONG :
    GoodBONG
      ((q.restrict S.left.carrier S.left.nondegenerate).orthogonalSum
        (q.restrict S.right.carrier S.right.nondegenerate))
      (Lattice.product
        (Lattice.rescale (uniformizerUnit K) S.left.lattice)
        S.right.lattice)
      (n + 3) :=
  target.mapLatticeIsometry
    (b.lemma714TypeIITargetToRescaledProductIsometry R s D hfirst hsecond
      hthird hsCurrent hcurrent S hsFour U block target htargetVectors)

include hfirst hsecond hthird hsCurrent hcurrent hsFour U block htargetVectors
/-- Transport the identified split-model BONG back to the actual lattice of
non-norm generators, preserving its complete quadratic-value sequence. -/
theorem exists_lemma714_typeII_nonNormGoodBONG_of_target
    (hnorm : Lattice.normIdeal q L = Lattice.powerIdeal (K := K) R)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.powerIdeal (K := K)
        (R - ramificationIndex K + 1))
    (hdiscriminant : b.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (negativeQuarterUnit K *
          (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)) :
    ∃ result : GoodBONG q
        (Lattice.nonNormGeneratorLattice R hnorm hscale) (n + 3),
      ∀ i, result.valueUnit i = target.valueUnit i := by
  let j := S.left.toGoodBONG b.good
  have hj0 : j.order 0 = R := by
    calc
      j.order 0 = b.order (S.left.sourceIndex 0) := S.left.order_eq 0
      _ = b.order 0 := by congr 1
      _ = R := hfirst
  have hnormJ : Lattice.normIdeal
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice =
        Lattice.powerIdeal (K := K) R := by
    calc
      Lattice.normIdeal
          (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice =
          Lattice.powerIdeal (K := K) (j.order 0) :=
        j.toBONG.normIdeal_eq_powerIdeal_order_zero
      _ = Lattice.powerIdeal (K := K) R := by rw [hj0]
  let tail := S.right.toGoodBONG b.good
  have htailLength : n + 3 - 2 = n + 1 := by omega
  let tail' : GoodBONG
      (q.restrict S.right.carrier S.right.nondegenerate)
      S.right.lattice (n + 1) := tail.castLength htailLength
  have htail0 : tail'.order 0 = b.order ⟨2, by omega⟩ := by
    rw [show tail' = tail.castLength htailLength by rfl,
      order_castLength]
    change S.right.bong.order ⟨0, by omega⟩ = _
    rw [S.right.order_eq]
    rfl
  have hnormT : Lattice.normIdeal
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice ≤
        Lattice.powerIdeal (K := K) (R + 1) := by
    rw [tail'.toBONG.normIdeal_eq_powerIdeal_order_zero]
    apply (Lattice.powerIdeal_le_iff (K := K) (tail'.order 0) (R + 1)).2
    rwa [htail0]
  have hjClass : j.toBONG.binaryUnitSquareClass = unitSquareClass K
      (negativeQuarterUnit K *
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit) := by
    change S.left.bong.binaryUnitSquareClass = unitSquareClass K
      (negativeQuarterUnit K *
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)
    calc
      S.left.bong.binaryUnitSquareClass =
          b.toBONG.adjacentUnitSquareClass
            (0 : Fin (n + 3)) (by simp) := by
        unfold binaryUnitSquareClass binaryParameter
          adjacentUnitSquareClass adjacentParameter
        apply congrArg (unitSquareClass K)
        rw [S.left.valueUnit_eq, S.left.valueUnit_eq]
        congr 2 <;> apply Fin.ext <;>
          simp [BONG.SegmentWitness.sourceIndex]
      _ = unitSquareClass K
          (negativeQuarterUnit K *
            (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit) :=
        hdiscriminant
  have hprimitive : Lattice.EveryPrimitiveIsNormGenerator
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice :=
    j.toBONG.everyPrimitiveIsNormGenerator_of_binaryUnitSquareClass_discriminant
      hjClass
  let productBONG := b.lemma714TypeIIRescaledProductGoodBONG R s D hfirst
    hsecond hthird hsCurrent hcurrent S hsFour U block target htargetVectors
  let toNonNorm :=
    Lattice.rescaledLeftProductToNonNormIsometry R hnormJ hnormT
      hprimitive S.toProductLatticeIsometry hscale
  let result := productBONG.mapLatticeIsometry toNonNorm
  refine ⟨result, ?_⟩
  intro i
  apply Units.ext
  change result.toBONG.value i = target.toBONG.value i
  calc
    _ = productBONG.toBONG.value i := by
      simpa only [result, GoodBONG.mapLatticeIsometry] using
        BONG.value_mapLatticeIsometry toNonNorm productBONG.toBONG i
    _ = target.toBONG.value i := by
      simpa only [productBONG, lemma714TypeIIRescaledProductGoodBONG,
        GoodBONG.mapLatticeIsometry] using
        BONG.value_mapLatticeIsometry
          (b.lemma714TypeIITargetToRescaledProductIsometry R s D hfirst
            hsecond hthird hsCurrent hcurrent S hsFour U block target
            htargetVectors) target.toBONG i

end Closure

section InteriorResult

variable [laws : DyadicDiscriminantClassLaws K]
variable [QuadraticDefectLaws K]
variable [DyadicUnramifiedNormLaws K]
variable [HilbertSymbolLaws K]
variable [DyadicDiagonalClassificationLaws K]
variable [BONGStructuralLaws.{u, u} K]
variable [Beli2009WeightIdealData.{u, u} K]
variable [Beli2019UnaryBinaryJordanLaws.{u} K]
variable [Beli2009JordanWeightOrderLaws.{u, u} K]
variable [Beli2006AlphaLaws.{u, u} K]
variable [modelLemma43 : BeliLemma43ConstructionLaws.{u, u} K]
variable [modelSectionTwo : Beli2006SectionTwoLaws.{u, u} K]
variable [GoodBONGClassificationLaws.{u, u, u} K]
variable [ambientLemma43 : BeliLemma43ConstructionLaws.{u, v} K]
variable [ambientSectionTwo : Beli2006SectionTwoLaws.{u, v} K]
variable [BONGReverseDualLaws.{u, v} K]
variable [BeliCorollary44Laws.{u, v} K]

/-- Beli (2019), Lemma 7.14(ii.2), for every admissible even stopping index
`s ≥ 2`: the displayed type-II value sequence is realized by a good BONG of
the actual non-norm-generator lattice.  The boundary `s = 2` is handled by
the canonical zero-prefix split. -/
theorem exists_lemma714_typeII_nonNormGoodBONG
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hfirst : b.order ⟨0, by omega⟩ = R)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hII : Lemma714IsTypeII b R s)
    (S : TwoBlockSplitWitness b.toBONG 2 (by omega))
    (hnorm : Lattice.normIdeal q L = Lattice.powerIdeal (K := K) R)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.powerIdeal (K := K)
        (R - ramificationIndex K + 1))
    (hdiscriminant : b.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hεDefect : defectOrder (K := K) ε = (1 : WithTop ℚ))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ))
    (hhilbert : hilbertSymbol K ε η = -1) :
    ∃ result : GoodBONG q
        (Lattice.nonNormGeneratorLattice R hnorm hscale) (n + 3),
      ∀ i, result.valueUnit i =
        lemma714TypeIITargetValues b s D.two_le (Classical.choose hII) ε η i := by
  have hsFour : s = 2 ∨ 4 ≤ s := by
    have htwo : 2 ≤ s := D.two_le
    rcases D.even with ⟨k, hk⟩
    omega
  let hsCurrent : s < n + 3 := Classical.choose hII
  have hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1 :=
    Classical.choose_spec hII
  rcases b.exists_lemma714_typeII_selectedTailSplit R s D hthird hII S
      hsFour with ⟨U⟩
  rcases exists_lemma714_typeII_targetGoodBONG
      (modelLemma43 := modelLemma43)
      (modelSectionTwo := modelSectionTwo)
      (ambientLemma43 := ambientLemma43)
      (ambientSectionTwo := ambientSectionTwo)
      b R s D hfirst hthird hII S hdiscriminant ε η hεUnit hηUnit
        hεDefect hηDefect hhilbert with
    ⟨N, target, block, hblockValues, htargetValues, htargetVectors⟩
  have hdiscriminant' : b.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (negativeQuarterUnit K * laws.discriminantUnit) := by
    simpa only [lemma712DiscriminantParameter] using hdiscriminant
  rcases b.exists_lemma714_typeII_nonNormGoodBONG_of_target R s D hfirst
      hsecond hthird hsCurrent hcurrent S hsFour U block target htargetVectors
      hnorm hscale hdiscriminant' with ⟨result, hresult⟩
  refine ⟨result, ?_⟩
  intro i
  exact (hresult i).trans (htargetValues i)

end InteriorResult

end BONG.GoodBONG

end Bong
