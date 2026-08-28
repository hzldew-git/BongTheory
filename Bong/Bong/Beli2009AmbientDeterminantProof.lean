/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009ClassificationPropagation
import Bong.Bong.Map

/-!
# The full determinant square class in Beli (2009), Lemma 3.2

An ambient isometry transports the first BONG without changing any of its
quadratic values.  The transported BONG and the second BONG are bases of the
same quadratic space, so their Gram determinants differ by the square of a
change-of-basis determinant.  This closes `Beli2009AmbientDeterminantLaws`
without using the classification theorem.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {s : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

/-- The full comparison product of two ambiently isometric BONGs is a square. -/
theorem fullComparison_isSquare_proof
    (ambient : q.IsIsometric s)
    (a : GoodBONG q L (N + 1))
    (b : GoodBONG s M (N + 1)) :
    IsSquare (a.comparisonPrefixUnit b (N + 1)) := by
  rcases ambient with ⟨f⟩
  let mapped : BONG W s (Lattice.map f.toLinearEquiv L) (N + 1) :=
    a.toBONG.map f
  rcases BONG.exists_valueProduct_eq_mul_square mapped b.toBONG with ⟨p, hp⟩
  refine ⟨a.toBONG.valueProduct * p, ?_⟩
  have hmapped : mapped.valueProduct = a.toBONG.valueProduct := by
    apply Units.ext
    simp only [BONG.coe_valueProduct]
    apply Finset.prod_congr rfl
    intro i _
    exact BONG.value_map f a.toBONG i
  change b.toBONG.prefixProduct (N + 1) =
    mapped.prefixProduct (N + 1) * p ^ 2 at hp
  change mapped.prefixProduct (N + 1) =
    a.toBONG.prefixProduct (N + 1) at hmapped
  unfold comparisonPrefixUnit GoodBONG.prefixProduct
  rw [hp, hmapped]
  simp only [pow_two]
  ac_rfl

end BONG.GoodBONG

/-- The determinant endpoint in Beli (2009), Lemma 3.2, is unconditional. -/
noncomputable instance beli2009AmbientDeterminantLawsProved
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] :
    Beli2009AmbientDeterminantLaws.{u, v, w} K where
  fullComparison_isSquare :=
    BONG.GoodBONG.fullComparison_isSquare_proof

end Bong
