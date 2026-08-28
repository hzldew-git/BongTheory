/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma75Splitting
import Bong.Bong.BinaryEndpointClass

/-!
# Beli (2019), Lemma 7.5: binary endpoint classes

Every binary block isolated by Lemma 7.5 has relative order `-2e`, hence its
parameter has the class `-1/4` or `-Δ/4`.  These are the invariant forms of
the paper's scaled `A(0,0)` and `A(2,2ρ)` alternatives.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The pair parameters in Lemma 7.5 have precisely the two endpoint-class
alternatives corresponding to the `A/B` binary lattices. -/
theorem beli2019Lemma75_pairBlock_endpointClass
    [Beli2006AlphaLaws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 2)) (i j k : Fin (n + 1)) (R : Int)
    (hij : i ≤ j) (heven : Even (j.val - i.val))
    (hiOrder : b.order i.castSucc = R)
    (hterminal :
      b.order j.succ = R - 2 * (ramificationIndex K : Int))
    (hik : i ≤ k) (hkj : k ≤ j)
    (hkEven : Even (k.val - i.val)) :
    b.toBONG.adjacentUnitSquareClass k.castSucc
        (Nat.succ_lt_succ k.isLt) =
          unitSquareClass K (negativeQuarterUnit K) ∨
      b.toBONG.adjacentUnitSquareClass k.castSucc
        (Nat.succ_lt_succ k.isLt) = unitSquareClass K
          (negativeQuarterUnit K * laws.discriminantUnit) := by
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
  apply b.toBONG.adjacentUnitSquareClass_endpoint_cases
  change b.order k.succ - b.order k.castSucc =
    -(2 * (ramificationIndex K : Int))
  rw [hkLow, hkHigh]
  ring

end BONG.GoodBONG

end Bong
