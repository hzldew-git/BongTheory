/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Invariants
import Bong.Lattice.Isometry

/-!
# Classification by good BONGs

This file formalizes the statement of Beli's 2009 Theorem 3.1.  It defines
quadratic-space and lattice isometries, diagonal representation, and the four
classification conditions:

1. equality of all orders `R_i`;
2. equality of all invariants `α_i`;
3. the prefix-product defect bounds;
4. the indicated prefix representation conditions when
   `α_{i-1} + α_i > 2e`.

The equivalence with lattice isometry ultimately uses O'Meara's local
classification theorem 93:28, which is not currently available in mathlib.
Accordingly, that single deep implication is isolated in
`GoodBONGClassificationLaws`; all four conditions themselves are concrete.
-/

namespace Bong

open Dyadic

universe u v w

section DiagonalRepresentation

variable {K : Type u} [Field K]

/-- The diagonal quadratic polynomial with coefficients `a_i`. -/
def diagonalQuadratic {m : Nat} (a : Fin m → K) (x : Fin m → K) : K :=
  ∑ i, a i * x i ^ 2

/-- The diagonal form with coefficients `source` is represented by `target`. -/
def DiagonalRepresents {m r : Nat} (source : Fin m → K) (target : Fin r → K) : Prop :=
  ∃ f : (Fin m → K) →ₗ[K] (Fin r → K),
    Function.Injective f ∧
      ∀ x, diagonalQuadratic target (f x) = diagonalQuadratic source x

theorem diagonalRepresents_refl {m : Nat} (a : Fin m → K) :
    DiagonalRepresents a a := by
  refine ⟨LinearMap.id, Function.injective_id, ?_⟩
  intro x
  rfl

namespace DiagonalRepresents

variable {m n : Nat} {source : Fin m → K} {target : Fin n → K}

/-- Representations between diagonal quadratic forms compose. -/
theorem trans {l : Nat} {a : Fin l → K}
    (hab : DiagonalRepresents a source)
    (hbc : DiagonalRepresents source target) :
    DiagonalRepresents a target := by
  rcases hab with ⟨f, hfInjective, hf⟩
  rcases hbc with ⟨g, hgInjective, hg⟩
  refine ⟨g.comp f, hgInjective.comp hfInjective, ?_⟩
  intro x
  rw [LinearMap.comp_apply, hg, hf]

/-- Append a zero coordinate to a vector in a finite-dimensional diagonal
space.  This construction is independent of the later Beli representation
theory and is therefore kept with the basic representation relation. -/
noncomputable def appendZeroLinearMap (n : Nat) :
    (Fin n → K) →ₗ[K] (Fin (n + 1) → K) where
  toFun x := Fin.lastCases 0 x
  map_add' x y := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

@[simp]
theorem appendZeroLinearMap_castSucc (n : Nat) (x : Fin n → K)
    (i : Fin n) : appendZeroLinearMap n x i.castSucc = x i := by
  simp [appendZeroLinearMap]

@[simp]
theorem appendZeroLinearMap_last (n : Nat) (x : Fin n → K) :
    appendZeroLinearMap n x (Fin.last n) = 0 := by
  simp [appendZeroLinearMap]

theorem appendZeroLinearMap_injective (n : Nat) :
    Function.Injective (appendZeroLinearMap (K := K) n) := by
  intro x y hxy
  funext i
  have hi := congrFun hxy i.castSucc
  simpa using hi

/-- A diagonal form represents the form obtained by deleting its last
coefficient. -/
theorem prefixSucc {n : Nat} (a : Fin (n + 1) → K) :
    DiagonalRepresents (fun i : Fin n => a i.castSucc) a := by
  refine ⟨appendZeroLinearMap n, appendZeroLinearMap_injective n, ?_⟩
  intro x
  unfold diagonalQuadratic
  rw [Fin.sum_univ_castSucc]
  simp

/-- Every coefficient prefix of a diagonal form is represented by the full
form. -/
theorem prefixOfLE {k l : Nat} (a : Fin l → K) (hkl : k ≤ l) :
    DiagonalRepresents (fun i : Fin k => a ⟨i.val, i.isLt.trans_le hkl⟩) a := by
  induction l with
  | zero =>
      have hk : k = 0 := Nat.eq_zero_of_le_zero hkl
      subst k
      exact diagonalRepresents_refl a
  | succ l ih =>
      by_cases hk : k = l + 1
      · subst k
        exact diagonalRepresents_refl a
      · have hkle : k ≤ l := by omega
        exact (ih (fun i : Fin l => a i.castSucc) hkle).trans
          (prefixSucc a)

end DiagonalRepresents

end DiagonalRepresentation

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Coerce a finite list of nonzero diagonal coefficients to field
coefficients.  This paper-independent construction lives with diagonal
representation, rather than in the later approximation theory. -/
def diagonalUnitCoefficients {k : Nat} (c : Fin k → Kˣ) : Fin k → K :=
  fun i ↦ c i

/-- Determinant square-class representative of a finite list of nonzero
diagonal coefficients. -/
noncomputable def diagonalUnitDeterminant {k : Nat} (c : Fin k → Kˣ) : Kˣ :=
  ∏ i, c i

/-- The first `m` scalar values of a good BONG. -/
noncomputable def prefixValues (b : GoodBONG q L n) (m : Nat) (hm : m ≤ n) :
    Fin m → K :=
  fun i => b.value ⟨i.1, i.2.trans_le hm⟩

/-- Product used in condition (iii) of Beli's classification theorem. -/
noncomputable def comparisonPrefixProduct (a : GoodBONG q L (n + 1))
    (b : GoodBONG r M (n + 1)) (i : Fin n) : Kˣ :=
  a.prefixProduct (i.1 + 1) * b.prefixProduct (i.1 + 1)

/-- Condition (i): equality of the complete order sequences. -/
def SameOrders (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1)) : Prop :=
  ∀ i, a.order i = b.order i

/-- Condition (ii): equality of the complete `α_i` sequences. -/
noncomputable def SameAlphas (a : GoodBONG q L (n + 1))
    (b : GoodBONG r M (n + 1)) : Prop :=
  ∀ i, a.alphaValue i = b.alphaValue i

/-- Condition (iii): every prefix comparison product has defect at least `α_i`. -/
noncomputable def PrefixDefectBounds (a : GoodBONG q L (n + 1))
    (b : GoodBONG r M (n + 1)) : Prop :=
  ∀ i : Fin n,
    (a.alphaValue i : WithTop ℚ) ≤
      defectOrder (K := K) (a.comparisonPrefixProduct b i)

/--
Condition (iv): the shorter prefix of `b` is represented by the next longer
prefix of `a` whenever `α_{i-1} + α_i > 2e`.
-/
noncomputable def InternalRepresentationConditions (a : GoodBONG q L (n + 1))
    (b : GoodBONG r M (n + 1)) : Prop :=
  ∀ (i : Fin n) (hi : 0 < i.1),
    (2 * ramificationIndex K : ℚ) <
        a.alphaValue ⟨i.1 - 1, by omega⟩ + a.alphaValue i →
      DiagonalRepresents
        (b.prefixValues i.1 (by omega))
        (a.prefixValues (i.1 + 1) (by omega))

end BONG.GoodBONG

/-- The four explicit conditions in Beli's 2009 Theorem 3.1. -/
structure ClassificationConditions
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {n : Nat}
    (a : BONG.GoodBONG q L (n + 1)) (b : BONG.GoodBONG r M (n + 1)) : Prop where
  sameOrders : a.SameOrders b
  sameAlphas : a.SameAlphas b
  prefixDefectBounds : a.PrefixDefectBounds b
  internalRepresentations : a.InternalRepresentationConditions b

/-!
The remaining equivalence is deliberately an explicit local-field interface,
not a global axiom.  An instance should be supplied only after formalizing the
O'Meara classification theorem on which Beli's proof depends.
-/

/-- The deep local classification theorem required to complete Theorem 3.1. -/
class GoodBONGClassificationLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  classify
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {n : Nat}
    (ambient : q.IsIsometric r)
    (a : BONG.GoodBONG q L (n + 1)) (b : BONG.GoodBONG r M (n + 1)) :
    Lattice.IsIsometric q r L M ↔ ClassificationConditions a b

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  [GoodBONGClassificationLaws.{u, v, w} K]

/-- Beli's classification theorem, assuming its isolated local-field laws. -/
theorem isometric_iff_classificationConditions
    (ambient : q.IsIsometric r)
    (a : BONG.GoodBONG q L (n + 1)) (b : BONG.GoodBONG r M (n + 1)) :
    Lattice.IsIsometric q r L M ↔ ClassificationConditions a b :=
  GoodBONGClassificationLaws.classify (K := K) ambient a b

end Bong
