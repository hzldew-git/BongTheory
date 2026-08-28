/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma75Splitting
import Bong.Bong.BinaryEndpointStandardModel
import Bong.Bong.BinaryEndpointSpace

/-!
# Beli (2019), Lemma 7.5: fixed binary models

Each descending pair in Lemma 7.5 is split off as an actual orthogonal
component and isometric to one of the two fixed standard-shear models.  These
are the coordinate models underlying `(1/2) a A(0,0)` and
`(1/2) a A(2,2ρ)` in the paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Every selected binary pair in Lemma 7.5 has one of Beli's two fixed
standard endpoint models. -/
theorem beli2019Lemma75_pairBlock_standardModelCases
    [Beli2006AlphaLaws.{u, v} K]
    [BeliCorollary44Laws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 2)) (i j k : Fin (n + 1)) (R : Int)
    (hij : i ≤ j) (heven : Even (j.val - i.val))
    (hiOrder : b.order i.castSucc = R)
    (hterminal :
      b.order j.succ = R - 2 * (ramificationIndex K : Int))
    (hik : i ≤ k) (hkj : k ≤ j)
    (hkEven : Even (k.val - i.val)) :
    ∃ w : b.toBONG.ThreeBlockSplitWitness k.castSucc
        (Nat.succ_lt_succ k.isLt),
      Lattice.IsIsometric w.pairBlock.toQuadraticSublattice.space
          (w.pairBlock.bong.standardEndpointModelSpace
            (negativeQuarterUnit K))
          w.pairBlock.lattice (binaryModelLattice (K := K)) ∨
        Lattice.IsIsometric w.pairBlock.toQuadraticSublattice.space
          (w.pairBlock.bong.standardEndpointModelSpace
            (negativeQuarterUnit K * laws.discriminantUnit))
          w.pairBlock.lattice (binaryModelLattice (K := K)) := by
  let C := b.beli2019Lemma75_arithmetic i j R hij heven
    hiOrder hterminal
  have hkHigh : b.order k.castSucc = R :=
    C.even_order k hik hkj hkEven
  have hkLow : b.order k.succ =
      R - 2 * (ramificationIndex K : Int) := by
    apply C.odd_order k.succ
    · simp only [Fin.val_succ]
      omega
    · simp only [Fin.val_succ]
      omega
    · rcases hkEven with ⟨d, hd⟩
      refine ⟨d, ?_⟩
      simp only [Fin.val_succ]
      omega
  change b.toBONG.order k.castSucc = R at hkHigh
  change b.toBONG.order k.succ =
    R - 2 * (ramificationIndex K : Int) at hkLow
  rcases b.beli2019Lemma75_pairBlock_split i j k R hij heven
      hiOrder hterminal hik hkj hkEven with ⟨w⟩
  refine ⟨w, ?_⟩
  have hzero : w.pairBlock.sourceIndex 0 = k.castSucc := by
    apply Fin.ext
    rfl
  have hone : w.pairBlock.sourceIndex 1 = k.succ := by
    apply Fin.ext
    rfl
  have hgap : w.pairBlock.bong.binaryOrderGap =
      -(2 * (ramificationIndex K : Int)) := by
    change w.pairBlock.bong.order 1 - w.pairBlock.bong.order 0 = _
    rw [w.pairBlock.order_eq, w.pairBlock.order_eq,
      hzero, hone, hkHigh, hkLow]
    ring
  exact w.pairBlock.bong.endpointStandardModel_cases hgap

/-- The same pair classification with the underlying quadratic space made
explicit as `[a,-a]` or `[a,-Δa]`. -/
theorem beli2019Lemma75_pairBlock_geometricCases
    [Beli2006AlphaLaws.{u, v} K]
    [BeliCorollary44Laws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 2)) (i j k : Fin (n + 1)) (R : Int)
    (hij : i ≤ j) (heven : Even (j.val - i.val))
    (hiOrder : b.order i.castSucc = R)
    (hterminal :
      b.order j.succ = R - 2 * (ramificationIndex K : Int))
    (hik : i ≤ k) (hkj : k ≤ j)
    (hkEven : Even (k.val - i.val)) :
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
            (-(w.pairBlock.bong.valueUnit 0 *
              laws.discriminantUnit)))) := by
  rcases b.beli2019Lemma75_pairBlock_standardModelCases
      i j k R hij heven hiOrder hterminal hik hkj hkEven with
    ⟨w, hquarter | hdiscriminant⟩
  · refine ⟨w, Or.inl ⟨hquarter, ?_⟩⟩
    rcases hquarter with ⟨f⟩
    rcases standardEndpointModelSpace_isIsometric_binaryDiagonal
        (w.pairBlock.bong.valueUnit 0) (1 : Kˣ) with ⟨g⟩
    refine ⟨f.toQuadraticSpaceIsometry.trans ?_⟩
    simpa [standardEndpointModelSpace] using g
  · refine ⟨w, Or.inr ⟨hdiscriminant, ?_⟩⟩
    rcases hdiscriminant with ⟨f⟩
    rcases standardEndpointModelSpace_isIsometric_binaryDiagonal
        (w.pairBlock.bong.valueUnit 0) laws.discriminantUnit with ⟨g⟩
    refine ⟨f.toQuadraticSpaceIsometry.trans ?_⟩
    simpa [standardEndpointModelSpace] using g

end BONG.GoodBONG

end Bong
