/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma75StandardModels

/-!
# Beli (2019), Lemma 7.5

This file assembles the arithmetic, splitting, binary-lattice, and ambient
quadratic-space conclusions of Lemma 7.5 over the complete alternating
segment.  Every descending pair is an actual orthogonal component and has one
of the two fixed endpoint models; every cut between consecutive pairs splits.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The full lattice and space classification of one pair occurring in
Lemma 7.5. -/
def Lemma75PairGeometricCase
    [laws : DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 2)) (k : Fin (n + 1)) : Prop :=
  ∃ w : b.toBONG.ThreeBlockSplitWitness k.castSucc
      (Nat.succ_lt_succ k.isLt),
    (Lattice.IsIsometric w.pairBlock.toQuadraticSublattice.space
        (w.pairBlock.bong.standardEndpointModelSpace
          (negativeQuarterUnit K))
        w.pairBlock.lattice (binaryModelLattice (K := K)) ∧
      QuadraticSpace.IsIsometric
        w.pairBlock.toQuadraticSublattice.space
        (QuadraticSpace.binaryDiagonal
          (w.pairBlock.bong.valueUnit 0)
          (-(w.pairBlock.bong.valueUnit 0)))) ∨
    (Lattice.IsIsometric w.pairBlock.toQuadraticSublattice.space
        (w.pairBlock.bong.standardEndpointModelSpace
          (negativeQuarterUnit K * laws.discriminantUnit))
        w.pairBlock.lattice (binaryModelLattice (K := K)) ∧
      QuadraticSpace.IsIsometric
        w.pairBlock.toQuadraticSublattice.space
        (QuadraticSpace.binaryDiagonal
          (w.pairBlock.bong.valueUnit 0)
          (-(w.pairBlock.bong.valueUnit 0 * laws.discriminantUnit))))

/-- The geometric conclusions of Lemma 7.5 over the whole selected segment.
The `pair_case` field covers every even-offset descending pair, while
`boundary_split` certifies every cut between two consecutive pairs. -/
structure Lemma75GeometricConsequences
    [DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) : Prop where
  segment : Nonempty
    (BONG.SegmentWitness b.toBONG i.val (j.val - i.val + 2) (by omega))
  pair_case (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j)
      (hkEven : Even (k.val - i.val)) :
    Lemma75PairGeometricCase b k
  boundary_split (k : Fin (n + 1)) (hik : i ≤ k)
      (hkNext : k.val + 2 ≤ j.val)
      (hkEven : Even (k.val - i.val)) :
    b.toBONG.HasTwoBlockSplit (k.val + 2) (by omega)

/-- The combined arithmetic and geometric statement of Lemma 7.5. -/
structure Lemma75Consequences
    [DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) (R : Int) : Prop where
  arithmetic : Lemma75ArithmeticConsequences b i j R
  geometry : Lemma75GeometricConsequences b i j

/-- Beli (2019), Lemma 7.5, with its complete alternating-segment
classification encoded by concrete orthogonal splitting and isometry
certificates. -/
theorem beli2019Lemma75
    [Beli2006AlphaLaws.{u, v} K]
    [BeliCorollary44Laws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) (R : Int)
    (hij : i ≤ j) (heven : Even (j.val - i.val))
    (hiOrder : b.order i.castSucc = R)
    (hterminal :
      b.order j.succ = R - 2 * (ramificationIndex K : Int)) :
    Lemma75Consequences b i j R := by
  refine {
    arithmetic := b.beli2019Lemma75_arithmetic i j R hij heven
      hiOrder hterminal
    geometry := ?_ }
  refine {
    segment := b.toBONG.exists_segmentWitness_unconditional
      i.val (j.val - i.val + 2) (by omega)
    pair_case := ?_
    boundary_split := ?_ }
  · intro k hik hkj hkEven
    exact b.beli2019Lemma75_pairBlock_geometricCases
      i j k R hij heven hiOrder hterminal hik hkj hkEven
  · intro k hik hkNext hkEven
    exact b.beli2019Lemma75_betweenPair_split
      i j k R hij heven hiOrder hterminal hik hkNext hkEven

end BONG.GoodBONG

end Bong
