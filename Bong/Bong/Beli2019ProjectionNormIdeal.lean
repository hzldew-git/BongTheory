/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MaximalIndices
import Bong.Bong.Beli2006SectionThree
import Bong.Lattice.PowerIdeal

/-!
# Beli (2019), Corollary 5.9(i): projected norm ideals

This file translates the second-coordinate criterion into the ideal statement
of Corollary 5.9(i).  `NormGeneratorComparisonData` is the precise interface
for the enlarged-lattice construction in the proof of Lemma 5.7: it records
the induced order relation, the volume identity, and the identification of
the artificial sequence's tail with the chosen BONG.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Distinct integral exponents define distinct fractional power ideals. -/
theorem powerIdeal_injective :
    Function.Injective (powerIdeal (K := K)) := by
  intro r s hrs
  apply le_antisymm
  · exact (powerIdeal_le_iff s r).mp (by rw [hrs])
  · exact (powerIdeal_le_iff r s).mp (by rw [hrs])

theorem powerIdeal_eq_iff (r s : Int) :
    powerIdeal (K := K) r = powerIdeal (K := K) s ↔ r = s := by
  constructor
  · exact fun h => (powerIdeal_injective (K := K)) h
  · intro h
    exact congrArg (powerIdeal (K := K)) h

end Lattice

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The norm ideal of a nonempty BONG is the power ideal determined by its
first order. -/
theorem normIdeal_eq_powerIdeal_order_zero (b : BONG V q L (n + 1)) :
    Lattice.normIdeal q L = Lattice.powerIdeal (K := K) (b.order 0) := by
  calc
    Lattice.normIdeal q L =
        Lattice.principalIdeal (K := K) (q.quadratic b.head) :=
      b.head_isNormGenerator.normIdeal_eq
    _ = Lattice.principalIdeal (K := K) (b.valueUnit 0 : K) := by
      rw [b.coe_valueUnit, b.value_zero_eq_quadratic_head]
    _ = Lattice.powerIdeal (K := K) (Dyadic.ordUnit K (b.valueUnit 0)) :=
      Lattice.principalIdeal_eq_powerIdeal (b.valueUnit 0)
    _ = Lattice.powerIdeal (K := K) (b.order 0) := by
      rw [b.order_eq_ordUnit]

/-- The first orders of any two nonempty BONGs of the same lattice agree. -/
theorem order_zero_eq_of_same_lattice
    {m : Nat} (b : BONG V q L (n + 1)) (c : BONG V q L (m + 1)) :
    b.order 0 = c.order 0 := by
  apply Lattice.powerIdeal_injective (K := K)
  rw [← b.normIdeal_eq_powerIdeal_order_zero,
    ← c.normIdeal_eq_powerIdeal_order_zero]

/-- The concrete output needed from the enlarged-lattice construction in
Lemma 5.7.  The candidate BONG may fail to be good only at its new head. -/
structure NormGeneratorComparisonData
    (b : GoodBONG q L (n + 2)) (c : BONG V q L (n + 2))
    (x : BeliOrderSequence (n + 2) Int) : Prop where
  order_le : BeliOrderLE x b.orderSequence
  tail_sum : x.suffixSum 1 = b.orderSequence.suffixSum 1
  tail_good : c.tail.IsGood
  tail_order (i : Fin (n + 1)) :
    x.entryOrZero (i.val + 1) = c.order i.succ

namespace NormGeneratorComparisonData

variable {b : GoodBONG q L (n + 2)} {c : BONG V q L (n + 2)}
  {x : BeliOrderSequence (n + 2) Int}

/-- The comparison data canonically supplies Corollary 5.9's order
criterion. -/
theorem secondOrderCriterion (D : NormGeneratorComparisonData b c x) :
    BeliOrderSequence.SecondOrderCriterion x b.orderSequence := by
  let k := b.orderSequence.maximalInitialOddPlateauIndex (by omega)
  exact D.order_le.secondOrderCriterion k (by omega)
    (b.orderSequence.maximalInitialOddPlateauIndex_spec (by omega))
    D.tail_sum

theorem source_second_eq (D : NormGeneratorComparisonData b c x) :
    x.entryOrZero 1 = c.order 1 := by
  simpa using D.tail_order (0 : Fin (n + 1))

theorem target_second_eq (_D : NormGeneratorComparisonData b c x) :
    b.orderSequence.entryOrZero 1 = b.order 1 := by
  rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by omega)]
  exact b.orderSequence_at 1 (by omega)

/-- Equality at the second coordinate propagates through the whole candidate
BONG. -/
theorem orders_eq_of_second_order_eq
    (D : NormGeneratorComparisonData b c x)
    (hsecond : c.order 1 = b.order 1) :
    ∀ i : Fin (n + 2), c.order i = b.order i := by
  have hcriterion := D.secondOrderCriterion
  have hsequenceSecond :
      x.entryOrZero 1 = b.orderSequence.entryOrZero 1 := by
    rw [D.source_second_eq, D.target_second_eq]
    exact hsecond
  have htail := hcriterion.second_eq_iff_tail_eq.mp hsequenceSecond
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact c.order_zero_eq_of_same_lattice b.toBONG
  · have hx := D.tail_order j
    have hxy := htail (j.val + 1) (by omega) (by omega)
    have hy : b.orderSequence.entryOrZero (j.val + 1) =
        b.order j.succ := by
      rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by omega)]
      exact b.orderSequence_at (j.val + 1) (by omega)
    exact hx.symm.trans (hxy.trans hy)

/-- If the candidate's second order is the canonical one, its good tail
extends to a good BONG. -/
theorem isGood_of_second_order_eq
    (D : NormGeneratorComparisonData b c x)
    (hsecond : c.order 1 = b.order 1) : c.IsGood := by
  have horders := D.orders_eq_of_second_order_eq hsecond
  intro i hi
  rw [horders i, horders ⟨i.val + 2, hi⟩]
  exact b.good i hi

/-- Corollary 5.9(i), norm-ideal inclusion. -/
theorem projectedNormIdeal_le (D : NormGeneratorComparisonData b c x) :
    Lattice.normIdeal
        (q.orthogonalSpace c.head c.head_isAnisotropic)
        (L.projectedLattice q c.head c.head_isAnisotropic) ≤
      Lattice.powerIdeal (K := K) (b.order 1) := by
  have hcriterion := D.secondOrderCriterion
  have horders : b.order 1 ≤ c.order 1 := by
    rw [← D.source_second_eq, ← D.target_second_eq]
    exact hcriterion.second_le
  rw [c.tail.normIdeal_eq_powerIdeal_order_zero, c.order_tail]
  exact (Lattice.powerIdeal_le_iff (c.order 1) (b.order 1)).mpr horders

/-- Corollary 5.9(i), equality criterion for a prescribed norm-generator
head. -/
theorem projectedNormIdeal_eq_iff_isGood
    [BeliLemma47Laws.{u, v} K]
    (D : NormGeneratorComparisonData b c x) :
    Lattice.normIdeal
        (q.orthogonalSpace c.head c.head_isAnisotropic)
        (L.projectedLattice q c.head c.head_isAnisotropic) =
      Lattice.powerIdeal (K := K) (b.order 1) ↔ c.IsGood := by
  have hcIdeal :
      Lattice.normIdeal
          (q.orthogonalSpace c.head c.head_isAnisotropic)
          (L.projectedLattice q c.head c.head_isAnisotropic) =
        Lattice.powerIdeal (K := K) (c.order 1) := by
    rw [c.tail.normIdeal_eq_powerIdeal_order_zero, c.order_tail]
    congr 2
  constructor
  · intro hideal
    have hsecond : c.order 1 = b.order 1 := by
      apply Lattice.powerIdeal_injective (K := K)
      rw [← hcIdeal, hideal]
    exact D.isGood_of_second_order_eq hsecond
  · intro hc
    let cg : GoodBONG q L (n + 2) := ⟨c, hc⟩
    have horders := cg.toBONG.beliLemma47_orders_eq b.toBONG cg.good b.good
    rw [hcIdeal]
    apply congrArg (Lattice.powerIdeal (K := K))
    exact horders 1

end NormGeneratorComparisonData

end BONG

end Bong
