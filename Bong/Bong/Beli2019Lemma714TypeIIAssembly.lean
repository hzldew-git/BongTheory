/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714TypeIIGeometry
import Bong.Bong.Beli2019Lemma710SegmentDual

/-!
# Beli (2019), Lemma 7.14(ii): assembling the type-II candidate

The local ternary construction and the global orthogonal-basis construction
are combined here.  The resulting good BONG has the exact vectors and values
displayed in Lemma 7.14(ii).  Its lattice is the candidate subsequently
identified with `L_3 perp pi J` by Lemma 7.10.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

private theorem lemma714TypeIIAssembly_two_le_rank (n : Nat) : 2 ≤ n + 3 := by
  omega

/-- The complete type-II candidate, before its lattice is identified by
Lemma 7.10. -/
theorem exists_lemma714_typeII_targetGoodBONG
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [Beli2006AlphaLaws.{u, u} K]
    [modelLemma43 : BeliLemma43ConstructionLaws.{u, u} K]
    [modelSectionTwo : Beli2006SectionTwoLaws.{u, u} K]
    [GoodBONGClassificationLaws.{u, u, u} K]
    (ambientLemma43 : BeliLemma43ConstructionLaws.{u, v} K)
    (ambientSectionTwo : Beli2006SectionTwoLaws.{u, v} K)
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hfirst : b.order ⟨0, by omega⟩ = R)
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hII : Lemma714IsTypeII b R s)
    (S : TwoBlockSplitWitness b.toBONG 2 (lemma714TypeIIAssembly_two_le_rank n))
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
    let hsCurrent := Classical.choose hII
    ∃ (N : Lattice K (S.right.carrier × S.left.carrier))
        (target : GoodBONG
          ((q.restrict S.right.carrier S.right.nondegenerate).orthogonalSum
            (q.restrict S.left.carrier S.left.nondegenerate)) N (n + 3))
        (block : GoodBONG
          ((q.restrict S.left.carrier S.left.nondegenerate).orthogonalSum
            ((q.restrict S.right.carrier S.right.nondegenerate).restrict
              (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).carrier
              (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).nondegenerate))
          (Lattice.product
            (Lattice.rescale (uniformizerUnit K) S.left.lattice)
            (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).lattice) 3),
      (∀ i, block.valueUnit i =
        lemma712TargetValues (b.valueUnit ⟨s, hsCurrent⟩) ε η i) ∧
      (∀ i, target.valueUnit i =
        lemma714TypeIITargetValues b s D.two_le hsCurrent ε η i) ∧
      ∀ i, target.toBONG.ambientVector i =
        lemma714TypeIITargetVector b S s D.two_le hsCurrent block i := by
  let hsCurrent : s < n + 3 := Classical.choose hII
  have hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1 :=
    Classical.choose_spec hII
  letI : BeliLemma43ConstructionLaws.{u, u} K := modelLemma43
  letI : Beli2006SectionTwoLaws.{u, u} K := modelSectionTwo
  have hlocal := b.exists_lemma714_typeII_actualLocalBlock R s D hfirst hII S
    hdiscriminant ε η hεUnit hηUnit hεDefect hηDefect hhilbert
  change ∃ block : GoodBONG
      ((q.restrict S.left.carrier S.left.nondegenerate).orthogonalSum
        ((q.restrict S.right.carrier S.right.nondegenerate).restrict
          (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).carrier
          (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).nondegenerate))
      (Lattice.product
        (Lattice.rescale (uniformizerUnit K) S.left.lattice)
        (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).lattice) 3,
    ∀ i, block.valueUnit i =
      lemma712TargetValues
        ((b.lemma714TypeIILine S s D.two_le hsCurrent).valueUnit 0) ε η i at hlocal
  rcases hlocal with ⟨block, hblockRaw⟩
  have hblockValues : ∀ i, block.valueUnit i =
      lemma712TargetValues (b.valueUnit ⟨s, hsCurrent⟩) ε η i := by
    intro i
    rw [hblockRaw i, b.lemma714TypeIILine_valueUnit_zero]
  letI : BeliLemma43ConstructionLaws.{u, v} K := ambientLemma43
  letI : Beli2006SectionTwoLaws.{u, v} K := ambientSectionTwo
  rcases b.exists_lemma714_typeII_targetGoodBONG_of_localBlock R s D hthird
      hsCurrent hcurrent ε η hεUnit hηUnit hηDefect S block hblockValues with
    ⟨N, target, htargetValues, htargetVectors⟩
  exact ⟨N, target, block, hblockValues, htargetValues, htargetVectors⟩

end BONG.GoodBONG

end Bong
