/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma72

/-!
# Beli (2003), Lemma 7.3

Three consecutive BONG entries satisfying the two unit-bounded binary-group
conditions split off a scaled hyperbolic plane.  The conclusion is represented
by an exact global orthogonal decomposition and a residual BONG obtained by
replacing the three-entry block by one vector.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG

/-- The first index in the three-entry block of Lemma 7.3. -/
def lemma73FirstIndex (i : Fin (n + 1)) : Fin (n + 3) :=
  ⟨i.1, by omega⟩

/-- The middle index in the three-entry block of Lemma 7.3. -/
def lemma73MiddleIndex (i : Fin (n + 1)) : Fin (n + 3) :=
  ⟨i.1 + 1, by omega⟩

/-- The final index in the three-entry block of Lemma 7.3. -/
def lemma73LastIndex (i : Fin (n + 1)) : Fin (n + 3) :=
  ⟨i.1 + 2, by omega⟩

/-- The exponent `(Rᵢ + Rᵢ₊₁)/2` of the split hyperbolic plane. -/
noncomputable def lemma73HyperbolicScaleOrder
    (b : BONG V q L (n + 3)) (i : Fin (n + 1)) : Int :=
  (b.order (lemma73FirstIndex i) +
    b.order (lemma73MiddleIndex i)) / 2

/-- The value `-π^Rᵢ εᵢ εᵢ₊₁ εᵢ₊₂` of the residual vector. -/
noncomputable def lemma73ResidualValue
    (b : BONG V q L (n + 3)) (i : Fin (n + 1)) : Kˣ :=
  -(uniformizerPowerUnit K (b.order (lemma73FirstIndex i)) *
    b.normalizedValue (lemma73FirstIndex i) *
    b.normalizedValue (lemma73MiddleIndex i) *
    b.normalizedValue (lemma73LastIndex i))

/-- The residual value has order `Rᵢ`. -/
theorem ordUnit_lemma73ResidualValue
    (b : BONG V q L (n + 3)) (i : Fin (n + 1)) :
    ordUnit K (b.lemma73ResidualValue i) =
      b.order (lemma73FirstIndex i) := by
  have h0 := (isValuationUnit_iff_ordUnit_eq_zero K _).1
    (b.normalizedValue_isValuationUnit (lemma73FirstIndex i))
  have h1 := (isValuationUnit_iff_ordUnit_eq_zero K _).1
    (b.normalizedValue_isValuationUnit (lemma73MiddleIndex i))
  have h2 := (isValuationUnit_iff_ordUnit_eq_zero K _).1
    (b.normalizedValue_isValuationUnit (lemma73LastIndex i))
  unfold lemma73ResidualValue
  rw [ordUnit_neg, ordUnit_mul, ordUnit_mul, ordUnit_mul,
    ordUnit_uniformizerPowerUnit, h0, h1, h2]
  omega

/-- The hypotheses of Lemma 7.3 at the block beginning at `i`. -/
def Lemma73Hypotheses
    (b : BONG V q L (n + 3)) (i : Fin (n + 1)) : Prop :=
  b.order (lemma73FirstIndex i) = b.order (lemma73LastIndex i) ∧
    beliSpinorGroup K
        (b.adjacentUnitSquareClass (lemma73FirstIndex i) (by
          simp only [lemma73FirstIndex]
          omega)) ≤
      valuationUnitSquareClassSubgroup K ∧
    beliSpinorGroup K
        (b.adjacentUnitSquareClass (lemma73MiddleIndex i) (by
          simp only [lemma73MiddleIndex]
          omega)) ≤
      valuationUnitSquareClassSubgroup K

/-- The exact splitting and replacement conclusion of Lemma 7.3. -/
structure Lemma73SplittingWitness
    (b : BONG V q L (n + 3)) (i : Fin (n + 1)) where
  /-- The global splitting into the hyperbolic plane and its complement. -/
  decomposition : Lattice.OrthogonalDecomposition q L 2
  /-- The first component is the claimed scaled hyperbolic plane. -/
  hyperbolic : Lattice.IsIsometric (decomposition.component 0).space
    (QuadraticSpace.hyperbolicPlane
      (uniformizerPowerUnit K (b.lemma73HyperbolicScaleOrder i)))
    (decomposition.component 0).lattice
    (Lattice.hyperbolicPlaneLattice (K := K))
  /-- The residual component has rank two less. -/
  remainderBONG :
    BONG (decomposition.component 1).carrier
      (decomposition.component 1).space
      (decomposition.component 1).lattice (n + 1)
  /-- Entries before the replaced block retain their values. -/
  value_before : ∀ j : Fin (n + 1), j.1 < i.1 →
    remainderBONG.value j = b.value ⟨j.1, by omega⟩
  /-- The three-entry block is replaced by the vector of the displayed value. -/
  replacement_value :
    remainderBONG.value ⟨i.1, by omega⟩ =
      (b.lemma73ResidualValue i : K)
  /-- Entries after the replacement correspond to original entries shifted by
  two positions. -/
  value_after : ∀ j : Fin (n + 1), i.1 < j.1 →
    remainderBONG.value j = b.value ⟨j.1 + 2, by omega⟩
  /-- Chosen norm generators for the two orthogonal components. -/
  componentNormData :
    Lattice.OrthogonalComponentNormData decomposition
  /-- The first component has the norm order of the scaled hyperbolic plane. -/
  hyperbolicNorm_order :
    (componentNormData 0).order =
      b.lemma73HyperbolicScaleOrder i + ramificationIndex K
  /-- The residual component has the same norm order as the original lattice. -/
  remainderNorm_order :
    (componentNormData 1).order = b.order 0
  /-- The replacement BONG remains good. -/
  good : remainderBONG.IsGood

namespace Lemma73SplittingWitness

/-- The replacement entry has the same order `Rᵢ` as the two endpoints of
the original block. -/
theorem replacement_order
    {b : BONG V q L (n + 3)} {i : Fin (n + 1)}
    (w : Lemma73SplittingWitness b i) :
    w.remainderBONG.order ⟨i.1, by omega⟩ =
      b.order (lemma73FirstIndex i) := by
  apply WithTop.coe_injective
  rw [BONG.coe_order, BONG.coe_order, w.replacement_value]
  rw [← coe_ordUnit, b.ordUnit_lemma73ResidualValue i,
    ← b.coe_order]

/-- The splitting witness in the interface expected by Lemma 7.1(ii). -/
noncomputable def toHyperbolicPlaneSplitting
    {b : BONG V q L (n + 3)} {i : Fin (n + 1)}
    (w : Lemma73SplittingWitness b i) :
    Lattice.HyperbolicPlaneSplitting q L where
  decomposition := w.decomposition
  scaleOrder := b.lemma73HyperbolicScaleOrder i
  hyperbolic := w.hyperbolic
  remainderNorm := w.componentNormData 1

@[simp]
theorem toHyperbolicPlaneSplitting_remainder_order
    {b : BONG V q L (n + 3)} {i : Fin (n + 1)}
    (w : Lemma73SplittingWitness b i) :
    w.toHyperbolicPlaneSplitting.remainderNorm.order = b.order 0 :=
  w.remainderNorm_order

@[simp]
theorem toHyperbolicPlaneSplitting_hyperbolic_order
    {b : BONG V q L (n + 3)} {i : Fin (n + 1)}
    (w : Lemma73SplittingWitness b i) :
    w.toHyperbolicPlaneSplitting.hyperbolicNormOrder =
      b.lemma73HyperbolicScaleOrder i + ramificationIndex K :=
  rfl

end Lemma73SplittingWitness

end BONG

/-- The ternary modular calculation, dualization, and global reconstruction
in Beli (2003), Lemma 7.3.  This interface has no default instance. -/
class BeliLemma73Laws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  exists_splitting
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 3)) (i : Fin (n + 1)) :
    b.IsGood → b.Lemma73Hypotheses i →
      Nonempty (b.Lemma73SplittingWitness i)

namespace BONG

variable [BeliLemma73Laws.{u, v} K]

/-- Beli (2003), Lemma 7.3. -/
theorem beliLemma73
    (b : BONG V q L (n + 3)) (i : Fin (n + 1))
    (hgood : b.IsGood) (h : b.Lemma73Hypotheses i) :
    Nonempty (b.Lemma73SplittingWitness i) :=
  BeliLemma73Laws.exists_splitting b i hgood h

end BONG

end Bong
