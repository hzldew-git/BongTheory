/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma64
import Bong.Lattice.Reflection

/-!
# Beli (2003), Lemma 6.5

This file packages the least rescaling of the second BONG vector for which
the initial binary lattice has an equal-value norm-generator basis.  The tail
is represented by the recursive BONG in `x₁ᴺ` and its head-rescaling, so the
projection and reflection assertions have their literal lattice meanings.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG

/-- The binary parameter after replacing `x₂` by `πᵏ x₂`. -/
noncomputable def headSecondRescaledParameter
    (b : BONG V q L (n + 3)) (k : Nat) : Kˣ :=
  b.adjacentParameter 0 (by simp) *
    uniformizerPowerUnit K (k : Int) ^ 2

/-- Its order is `R₂ + 2k - R₁`. -/
theorem ordUnit_headSecondRescaledParameter
    (b : BONG V q L (n + 3)) (k : Nat) :
    ordUnit K (b.headSecondRescaledParameter k) =
      b.order 1 + 2 * (k : Int) - b.order 0 := by
  rw [headSecondRescaledParameter, ordUnit_mul, ordUnit_pow,
    ordUnit_uniformizerPowerUnit,
    b.ordUnit_adjacentParameter_zero]
  unfold lemma62Gap
  omega

/-- Admissibility of a second-vector rescaling: its normalized binary model
has a basis of two norm generators with equal quadratic value. -/
def HeadSecondRescaleAdmissible
    (b : BONG V q L (n + 3)) (k : Nat) : Prop :=
  HasSomeEqualNormGeneratorBasis (b.headSecondRescaledParameter k)

/-- The initial binary BONG sublattice is hyperbolic at its natural scale. -/
def FirstBinaryIsHyperbolic (b : BONG V q L (n + 3)) : Prop :=
  Lattice.QuadraticSublattice.ContainsScaledHyperbolicPlane
    (b.prefixWitness 2 (by omega)).quadraticSublattice
    ((b.order 0 + b.order 1) / 2)

/-- The mathematical data defining Beli's least exponent in Lemma 6.5.

This is deliberately separated from the lattice used to realize the shifted
tail.  In the exceptional residue-two case the paper only constructs the
once-rescaled tail although the least exponent is two, so requiring a literal
`HeadRescaleWitness` at the least exponent would be stronger than the paper. -/
structure Lemma65MinimalityData (b : BONG V q L (n + 3)) where
  /-- The least nonnegative rescaling exponent. -/
  k : Nat
  /-- The rescaled initial binary lattice has an equal-value generator basis. -/
  admissible : b.HeadSecondRescaleAdmissible k
  /-- No smaller nonnegative exponent has that property. -/
  least : ∀ j : Nat, b.HeadSecondRescaleAdmissible j → k ≤ j
  /-- The original initial binary lattice is not hyperbolic. -/
  firstBinary_not_hyperbolic : ¬b.FirstBinaryIsHyperbolic

namespace Lemma65MinimalityData

variable {b : BONG V q L (n + 3)}

/-- Minimality in the usual strict form. -/
theorem not_admissible_of_lt (M : b.Lemma65MinimalityData)
    (j : Nat) (hj : j < M.k) :
    ¬b.HeadSecondRescaleAdmissible j := by
  intro hadmissible
  exact (Nat.not_le_of_lt hj) (M.least j hadmissible)

end Lemma65MinimalityData

/-- The low-order range of Lemma 6.5, expressed only in terms of a candidate
rescaling exponent. -/
def Lemma65LowRangeAt (b : BONG V q L (n + 3)) (k : Nat) : Prop :=
  b.order 1 + 2 * (k : Int) - b.order 0 ≤
    2 * (ramificationIndex K : Int)

/-- The complementary high-order range of Lemma 6.5, expressed only in terms
of a candidate rescaling exponent. -/
def Lemma65HighRangeAt (b : BONG V q L (n + 3)) (k : Nat) : Prop :=
  2 * (ramificationIndex K : Int) + 1 ≤
    b.order 1 + 2 * (k : Int) - b.order 0

/-- The orthogonal projection `pr_(x₁ᴺ)(x)` used throughout Lemmas 6.5
and 6.6.  It is intrinsic to the BONG and does not depend on a concrete
rescaled-tail witness. -/
noncomputable def lemma65Projection (b : BONG V q L (n + 3)) (x : V) :
    q.vectorOrthogonal b.head :=
  q.projectionToOrthogonal b.head b.head_isAnisotropic x

/-- The least rescaling and the concrete rescaled tail used in Lemma 6.5. -/
structure Lemma65Setup (b : BONG V q L (n + 3)) where
  /-- The least nonnegative rescaling exponent. -/
  k : Nat
  /-- The lattice `⟨πᵏ x₂, x₃, ..., xₙ⟩` in `x₁ᴺ`. -/
  tailRescale : b.tail.HeadRescaleWitness k
  /-- The rescaled initial binary lattice has an equal-value generator basis. -/
  admissible : b.HeadSecondRescaleAdmissible k
  /-- No smaller nonnegative exponent has that property. -/
  least : ∀ j : Nat, b.HeadSecondRescaleAdmissible j → k ≤ j
  /-- The original initial binary lattice is not hyperbolic. -/
  firstBinary_not_hyperbolic : ¬b.FirstBinaryIsHyperbolic

namespace Lemma65Setup

variable {b : BONG V q L (n + 3)}

/-- Forget the concrete tail realization and retain exactly the least-index
data.  This projection is used to keep the numerical case analysis independent
of the exceptional tail issue. -/
def toMinimalityData (S : b.Lemma65Setup) : b.Lemma65MinimalityData where
  k := S.k
  admissible := S.admissible
  least := S.least
  firstBinary_not_hyperbolic := S.firstBinary_not_hyperbolic

/-- The orthogonal projection `pr_(x₁ᴺ)(x)`. -/
noncomputable def projection (_S : b.Lemma65Setup) (x : V) :
    q.vectorOrthogonal b.head :=
  b.lemma65Projection x

/-- Minimality in the usual strict form. -/
theorem not_admissible_of_lt (S : b.Lemma65Setup)
    (j : Nat) (hj : j < S.k) :
    ¬b.HeadSecondRescaleAdmissible j := by
  intro hadmissible
  exact (Nat.not_le_of_lt hj) (S.least j hadmissible)

/-- The first vector of the rescaled tail is literally `πᵏ x₂` in the
original ambient quadratic space. -/
theorem coe_tailRescale_ambientVector_zero (S : b.Lemma65Setup) :
    (S.tailRescale.bong.ambientVector 0 : V) =
      ((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K) •
        b.ambientVector 1 := by
  have h := congrArg Subtype.val S.tailRescale.ambientVector_zero
  simpa using h

end Lemma65Setup

/-- The exceptional residue-two branch of Lemma 6.5(i). -/
noncomputable def Lemma65Exceptional
    (b : BONG V q L (n + 3)) : Prop :=
  b.lemma62Gap = 2 * (ramificationIndex K : Int) - 2 ∧
    (((1 : ℚ) : WithTop ℚ) < b.normalizedAdjacentDefectOrder 0) ∧
    ¬HasResidueFieldMoreThanTwoElements (K := K)

/-- The range `R₂ + 2k - R₁ ≤ 2e` used in parts (ii) and (iii). -/
def Lemma65LowRange (b : BONG V q L (n + 3))
    (S : b.Lemma65Setup) : Prop :=
  b.order 1 + 2 * (S.k : Int) - b.order 0 ≤
    2 * (ramificationIndex K : Int)

/-- The range `R₂ + 2k - R₁ ≥ 2e+1` used in part (iv). -/
def Lemma65HighRange (b : BONG V q L (n + 3))
    (S : b.Lemma65Setup) : Prop :=
  2 * (ramificationIndex K : Int) + 1 ≤
    b.order 1 + 2 * (S.k : Int) - b.order 0

/-- The exceptional projection lies in the once-rescaled tail but is not a
norm generator there. -/
structure Lemma65ExceptionalProjectionWitness
    (b : BONG V q L (n + 3)) (x : V) where
  /-- A concrete realization of `⟨πx₂,x₃,...,xₙ⟩`. -/
  tailRescaleOne : b.tail.HeadRescaleWitness 1
  /-- The projection belongs to that lattice. -/
  projection_mem :
    q.projectionToOrthogonal b.head b.head_isAnisotropic x ∈
      tailRescaleOne.lattice
  /-- It is not a norm generator of that lattice. -/
  projection_not_generator :
    ¬Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      tailRescaleOne.lattice
      (q.projectionToOrthogonal b.head b.head_isAnisotropic x)

/-- The anisotropic difference and its integral reflection from part (ii). -/
structure Lemma65DifferenceReflectionWitness
    (b : BONG V q L (n + 3)) (x : V) where
  /-- The reflection vector `x₁-x` is anisotropic. -/
  anisotropic : q.IsAnisotropic (b.head - x)
  /-- Reflection in `x₁-x` preserves the original lattice. -/
  integral : Lattice.IsIntegralReflection (L := L) anisotropic

namespace Lemma65DifferenceReflectionWitness

variable {b : BONG V q L (n + 3)} {x : V}

/-- The integral reflection as an element of `O(L)`. -/
noncomputable def integralOrthogonal
    (w : Lemma65DifferenceReflectionWitness b x) :
    Lattice.IntegralOrthogonalGroup q L :=
  Lattice.integralReflection w.anisotropic w.integral

/-- Equal quadratic values make the reflection carry `x₁` to `x`. -/
theorem map_head (w : Lemma65DifferenceReflectionWitness b x)
    (heq : q.quadratic x = q.quadratic b.head) :
    q.reflectionLinearEquiv (b.head - x) w.anisotropic b.head = x :=
  q.reflectionLinearEquiv_sub_apply_left_of_quadratic_eq
    b.head x w.anisotropic heq.symm

end Lemma65DifferenceReflectionWitness

/-- A finite prescribed order makes `x₁-x` anisotropic. -/
theorem lemma65Difference_isAnisotropic_of_order_eq
    (b : BONG V q L (n + 3)) (x : V)
    (horder : ord K (q.quadratic (b.head - x)) =
      ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
        WithTop Int)) :
    q.IsAnisotropic (b.head - x) := by
  intro hzero
  rw [hzero, ord_zero] at horder
  exact WithTop.top_ne_coe horder

/-- The nontrivial valuation and reflection assertions in Beli (2003),
Lemma 6.5.  This interface has no default instance. -/
class BeliLemma65Laws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  projection_alternative
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head) :
    (¬b.Lemma65Exceptional → S.projection x ∈ S.tailRescale.lattice) ∧
      (b.Lemma65Exceptional →
        S.k = 2 ∧ Nonempty (Lemma65ExceptionalProjectionWitness b x))
  low_reflection
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hlow : b.Lemma65LowRange S)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x)) :
    Nonempty (Lemma65DifferenceReflectionWitness b x)
  reflected_projection_generator
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hlow : b.Lemma65LowRange S)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x))
    (w : Lemma65DifferenceReflectionWitness b x)
    (x' : V) (hx' : x' ∈ L)
    (heq' : q.quadratic x' = q.quadratic b.head)
    (hnotGenerator : ¬Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x')) :
    Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice
      (S.projection
        (q.reflectionLinearEquiv (b.head - x) w.anisotropic x'))
  high_reflection_integral
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hhigh : b.Lemma65HighRange S)
    (horder : ord K (q.quadratic (b.head - x)) =
      ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
        WithTop Int)) :
    Lattice.IsIntegralReflection (L := L)
      (lemma65Difference_isAnisotropic_of_order_eq b x horder)

variable [BeliLemma65Laws.{u, v} K]

/-- Beli (2003), Lemma 6.5(i), including its exceptional branch. -/
theorem beliLemma65_i (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head) :
    (¬b.Lemma65Exceptional → S.projection x ∈ S.tailRescale.lattice) ∧
      (b.Lemma65Exceptional →
        S.k = 2 ∧ Nonempty (Lemma65ExceptionalProjectionWitness b x)) :=
  BeliLemma65Laws.projection_alternative b hB S x hx heq

/-- Beli (2003), Lemma 6.5(ii). -/
theorem beliLemma65_ii (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hlow : b.Lemma65LowRange S)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x)) :
    Nonempty (Lemma65DifferenceReflectionWitness b x) :=
  BeliLemma65Laws.low_reflection b hB S x hx heq hlow hgenerator

/-- Beli (2003), Lemma 6.5(iii), using the integral reflection supplied by
part (ii). -/
theorem beliLemma65_iii_with
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hlow : b.Lemma65LowRange S)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x))
    (w : Lemma65DifferenceReflectionWitness b x)
    (x' : V) (hx' : x' ∈ L)
    (heq' : q.quadratic x' = q.quadratic b.head)
    (hnotGenerator : ¬Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x')) :
    Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice
      (S.projection
        (q.reflectionLinearEquiv (b.head - x) w.anisotropic x')) :=
  BeliLemma65Laws.reflected_projection_generator
    b hB S x hx heq hlow hgenerator w x' hx' heq' hnotGenerator

/-- Parts (ii) and (iii) combined without requiring the caller to choose the
anisotropy proof for the reflection. -/
theorem beliLemma65_iii
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hlow : b.Lemma65LowRange S)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x))
    (x' : V) (hx' : x' ∈ L)
    (heq' : q.quadratic x' = q.quadratic b.head)
    (hnotGenerator : ¬Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x')) :
    ∃ w : Lemma65DifferenceReflectionWitness b x,
      Lattice.IsNormGenerator
        (q.orthogonalSpace b.head b.head_isAnisotropic)
        S.tailRescale.lattice
        (S.projection
          (q.reflectionLinearEquiv (b.head - x) w.anisotropic x')) := by
  rcases b.beliLemma65_ii hB S x hx heq hlow hgenerator with ⟨w⟩
  exact ⟨w, b.beliLemma65_iii_with hB S x hx heq hlow hgenerator
    w x' hx' heq' hnotGenerator⟩

/-- Beli (2003), Lemma 6.5(iv). -/
theorem beliLemma65_iv
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hhigh : b.Lemma65HighRange S)
    (horder : ord K (q.quadratic (b.head - x)) =
      ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
        WithTop Int)) :
    Lattice.IsIntegralReflection (L := L)
      (lemma65Difference_isAnisotropic_of_order_eq b x horder) :=
  BeliLemma65Laws.high_reflection_integral
    b hB S x hx heq hhigh horder

end BONG

end Bong
