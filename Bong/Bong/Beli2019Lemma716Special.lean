/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714Special
import Bong.Bong.Beli2019Lemma716

/-!
# Beli (2019), Lemmas 7.15--7.16 on the Section-7 special lattice

The coefficient calculations of Lemmas 7.15 and 7.16 are independent of the
particular realization of the target lattice.  This file applies those
generic results to the scale-free image lattice from Lemma 7.14 and packages
the geometric certificates needed by the well-founded descent.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L N : Lattice K V} {n : Nat}

/-- The geometric content of the special replacement: it is exactly the
non-norm-generator subset, is contained in the parent lattice, and strictly
increases the volume order. -/
structure Beli2019Lemma714SpecialGeometry
    (b : GoodBONG q L (n + 3)) (R : Int)
    (S : TwoBlockSplitWitness b.toBONG 2 (by omega)) : Prop where
  mem_iff : ∀ x : V, x ∈ S.lemma714SpecialLattice ↔
    x ∈ L ∧ ¬ Lattice.IsNormGenerator q L x
  lattice_le : S.lemma714SpecialLattice ≤ L
  volumeOrder_lt : Lattice.volumeOrder q L <
    Lattice.volumeOrder q S.lemma714SpecialLattice

variable [laws : DyadicDiscriminantClassLaws K]

/-- The assumptions of the equal-first-gap branch imply all geometric
properties of the explicit special lattice, with no scale bound. -/
theorem lemma714SpecialGeometry
    (b : GoodBONG q L (n + 3)) (R : Int)
    (hfirst : b.order ⟨0, by omega⟩ = R)
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (S : TwoBlockSplitWitness b.toBONG 2 (by omega))
    (hdiscriminant : b.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K))) :
    Beli2019Lemma714SpecialGeometry b R S := by
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
      (negativeQuarterUnit K * laws.discriminantUnit) := by
    change S.left.bong.binaryUnitSquareClass = unitSquareClass K
      (negativeQuarterUnit K * laws.discriminantUnit)
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
          (negativeQuarterUnit K * laws.discriminantUnit) := by
        simpa only [lemma712DiscriminantParameter] using hdiscriminant
  have hprimitive : Lattice.EveryPrimitiveIsNormGenerator
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice :=
    j.toBONG.everyPrimitiveIsNormGenerator_of_binaryUnitSquareClass_discriminant
      hjClass
  have hfirstGenerator : Lattice.IsNormGenerator q L
      (b.toBONG.ambientVector ⟨0, by omega⟩) :=
    b.toBONG.ambientVector_first_isNormGenerator (by omega)
  exact {
    mem_iff := S.mem_lemma714SpecialLattice_iff R hnormJ hnormT hprimitive
    lattice_le := S.lemma714SpecialLattice_le
    volumeOrder_lt := S.lemma714SpecialLattice_volumeOrder_lt R hnormJ
      hnormT hprimitive _ hfirstGenerator }

/-- The two coefficient alternatives of Lemma 7.16, now realized on the
literal special lattice. -/
inductive Beli2019Lemma716SpecialRealization
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (S : TwoBlockSplitWitness a.toBONG 2 (by omega))
    (ε η : Kˣ) : Prop where
  | typeI
      (hI : Lemma714IsTypeI a R s)
      (result : GoodBONG q S.lemma714SpecialLattice (n + 3))
      (values : ∀ i, result.valueUnit i =
        lemma714TypeITargetValues a s D.two_le D.le_rank i)
      (conditions : RepresentationConditionsPrime result c le_rfl) :
      Beli2019Lemma716SpecialRealization a c R s D S ε η
  | typeII
      (hII : Lemma714IsTypeII a R s)
      (result : GoodBONG q S.lemma714SpecialLattice (n + 3))
      (values : ∀ i, result.valueUnit i =
        lemma714TypeIITargetValues a s D.two_le
          (Classical.choose hII) ε η i)
      (conditions : RepresentationConditionsPrime result c le_rfl) :
      Beli2019Lemma716SpecialRealization a c R s D S ε η

/-- Complete Section-7 conclusion through Lemma 7.16. -/
structure Beli2019Lemma716SpecialConclusion
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (S : TwoBlockSplitWitness a.toBONG 2 (by omega))
    (ε η : Kˣ) : Prop where
  plateau : 4 ≤ s → Lemma714PlateauConsequences a R s D.le_rank
  geometry : Beli2019Lemma714SpecialGeometry a R S
  realization : Beli2019Lemma716SpecialRealization a c R s D S ε η

variable [QuadraticDefectLaws K]
variable [DyadicUnramifiedNormLaws K]
variable [HilbertSymbolLaws K]
variable [DyadicDiagonalClassificationLaws K]
variable [BONGStructuralLaws.{u, u} K]
variable [Beli2009WeightIdealData.{u, u} K]
variable [Beli2019UnaryBinaryJordanLaws.{u} K]
variable [Beli2009JordanWeightOrderLaws.{u, u} K]
variable [modelAlpha : Beli2006AlphaLaws.{u, u} K]
variable [modelLemma43 : BeliLemma43ConstructionLaws.{u, u} K]
variable [modelSectionTwo : Beli2006SectionTwoLaws.{u, u} K]
variable [classificationModel : GoodBONGClassificationLaws.{u, u, u} K]
variable [ambientLemma43 : BeliLemma43ConstructionLaws.{u, v} K]
variable [ambientSectionTwo : Beli2006SectionTwoLaws.{u, v} K]
variable [BONGReverseDualLaws.{u, v} K]
variable [BeliCorollary44Laws.{u, v} K]
variable [Beli2006AlphaLaws.{u, v} K]
variable [Beli2009AlphaParityLaws.{u, v} K]
variable [PerfectResidueFieldLaws K]
variable [DyadicAlternatingEndpointTowerRepresentationLaws K]

/-- Beli (2019), Lemmas 7.14--7.16 in the equal-first-gap branch, with the
actual special lattice and all descent geometry. -/
theorem beli2019Lemma716Special
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hfirst : a.order ⟨0, by omega⟩ = R)
    (hsecond : a.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (S : TwoBlockSplitWitness a.toBONG 2 (by omega))
    (hdiscriminant : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (hnormStrict : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hεDefect : defectOrder (K := K) ε = (1 : WithTop ℚ))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ))
    (hhilbert : hilbertSymbol K ε η = -1) :
    Beli2019Lemma716SpecialConclusion a c R s D S ε η := by
  have C := a.beli2019Lemma714Special
    (modelAlpha := modelAlpha)
    (modelLemma43 := modelLemma43)
    (modelSectionTwo := modelSectionTwo)
    (ambientLemma43 := ambientLemma43)
    (ambientSectionTwo := ambientSectionTwo)
    R s D hfirst hsecond hthird S
    hdiscriminant ε η hεUnit hηUnit hεDefect hηDefect hhilbert
  refine {
    plateau := C.plateau
    geometry := a.lemma714SpecialGeometry R hfirst hthird S hdiscriminant
    realization := ?_ }
  cases C.realization with
  | typeI hI result hvalues =>
      have horders : ∀ i, s ≤ i.val → a.order i = result.order i :=
        fun i hi ↦ a.lemma715_typeI_order_eq s D.two_le D.le_rank
          result hvalues i hi
      have halphas : ∀ i, s ≤ i.val →
          a.alphaValue i = result.alphaValue i :=
        fun i hi ↦ a.lemma715_typeI_alphaValue_eq R s D hsecond hthird
          hI result hvalues i hi
      have hprefix : ∀ (k : Nat), s ≤ k → (hk : k ≤ n + 3) →
          (a.prefixDiagonalSpace k hk).IsIsometric
            (result.prefixDiagonalSpace k hk) :=
        fun k hsk hk ↦ a.lemma715_typeI_prefix_isIsometric s D.two_le
          D.le_rank result hvalues k hsk hk
      exact Beli2019Lemma716SpecialRealization.typeI hI result hvalues
        (a.lemma716_typeI_representationConditionsPrime result c R s D
          hfirst hsecond hthird hdiscriminant hnormStrict hac hI hvalues
            horders halphas hprefix)
  | typeII hII result hvalues =>
      have horders : ∀ i, s ≤ i.val → a.order i = result.order i :=
        fun i hi ↦ a.lemma715_typeII_order_eq R s D hII ε η hεUnit
          hηUnit result hvalues i hi
      have halphas : ∀ i, s ≤ i.val →
          a.alphaValue i = result.alphaValue i :=
        fun i hi ↦ a.lemma715_typeII_alphaValue_eq R s D hsecond hthird
          hII ε η hεUnit hηUnit hηDefect result hvalues i hi
      have hprefix : ∀ (k : Nat), s + 1 ≤ k →
          (hk : k ≤ n + 3) →
          (a.prefixDiagonalSpace k hk).IsIsometric
            (result.prefixDiagonalSpace k hk) :=
        fun k hsk hk ↦ a.lemma715_typeII_prefix_isIsometric R s D hII
          ε η result hvalues k hsk hk
      exact Beli2019Lemma716SpecialRealization.typeII hII result hvalues
        (a.lemma716_typeII_representationConditionsPrime result c R s D
          hfirst hsecond hthird hdiscriminant hnormStrict hac hII ε η
            hεUnit hηUnit hηDefect hvalues horders halphas hprefix)

end BONG.GoodBONG

end Bong
