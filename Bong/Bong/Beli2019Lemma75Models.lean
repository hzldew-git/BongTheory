/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma75Splitting
import Bong.Bong.BinaryEndpointModel

/-!
# Beli (2019), Lemma 7.5: concrete models of the binary blocks

Each binary component split off in Lemma 7.5 has relative order `-2e`.
The general endpoint-model theorem therefore identifies that actual component
lattice with a rescaled model having parameter `-1/4` or `-Δ/4`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Every selected pair in Lemma 7.5 is simultaneously an orthogonal
component and one of the two concrete endpoint model lattices. -/
theorem beli2019Lemma75_pairBlock_modelCases
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
      (∃ s : Kˣ, IsValuationUnit K (s : K) ∧
        Lattice.IsIsometric w.pairBlock.toQuadraticSublattice.space
          (w.pairBlock.bong.squareClassRepresentativeModelSpace
            (negativeQuarterUnit K) s)
          w.pairBlock.lattice (binaryModelLattice (K := K))) ∨
      (∃ s : Kˣ, IsValuationUnit K (s : K) ∧
        Lattice.IsIsometric w.pairBlock.toQuadraticSublattice.space
          (w.pairBlock.bong.squareClassRepresentativeModelSpace
            (negativeQuarterUnit K * laws.discriminantUnit) s)
          w.pairBlock.lattice (binaryModelLattice (K := K))) := by
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
  exact w.pairBlock.bong.endpointModel_cases hgap

end BONG.GoodBONG

end Bong
