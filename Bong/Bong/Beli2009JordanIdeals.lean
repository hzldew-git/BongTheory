/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009AlphaArithmetic
import Bong.Lattice.Jordan
import Bong.Lattice.PowerIdeal

/-!
# Beli (2009/2010), Lemmas 2.10--2.12

This file introduces the ideal notation used in the Jordan-theoretic part of
the paper.  In particular, `normGroupSet q L` is Beli's `gL = Q(L) + 2sL`,
and `quadraticDefectIdeal` is the absolute quadratic-defect ideal.

O'Meara's weight-ideal theorem 93A and the weight formula for an orthogonal
sum are not available in mathlib.  Their exact statements are consequently
isolated in two classes without default instances.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- Multiplication by a field scalar, viewed as an integer-ring linear map. -/
noncomputable def coefficientMulLinearMap (a : K) :
    K →ₗ[IntegerRing K] K where
  toFun z := a * z
  map_add' x y := by simp [mul_add]
  map_smul' c x := by
    simp only [RingHom.id_apply, Algebra.smul_def]
    ring

@[simp]
theorem coefficientMulLinearMap_apply (a z : K) :
    coefficientMulLinearMap (K := K) a z = a * z :=
  rfl

/-- The product `a I` of a field scalar and a coefficient ideal. -/
noncomputable def scalarIdeal (a : K) (I : CoefficientIdeal (K := K)) :
    CoefficientIdeal (K := K) :=
  I.map (coefficientMulLinearMap (K := K) a)

/-- The ideal `2 I`. -/
noncomputable def twiceIdeal (I : CoefficientIdeal (K := K)) :
    CoefficientIdeal (K := K) :=
  I.map (twoMulLinearMap (K := K))

/-- Beli's ideal `2sL`. -/
noncomputable def twoScaleIdeal (q : QuadraticSpace K V)
    (L : Lattice K V) : CoefficientIdeal (K := K) :=
  twiceIdeal (scaleIdeal q L)

/-- A nonzero principal fractional ideal together with its integral order. -/
structure OrderedFractionalIdeal (K : Type u) [Field K] [CharZero K]
    [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] where
  carrier : CoefficientIdeal (K := K)
  order : Int
  carrier_eq_powerIdeal : carrier = powerIdeal (K := K) order

/-- The set `a O² + w`. -/
def integralSquareCoset (a : K) (w : CoefficientIdeal (K := K)) : Set K :=
  {z | ∃ c : IntegerRing K, ∃ y ∈ w,
    z = a * (c : K) ^ 2 + y}

/-- Beli's norm group `gL = Q(L) + 2sL`, represented as a scalar set. -/
noncomputable def normGroupSet (q : QuadraticSpace K V)
    (L : Lattice K V) : Set K :=
  {z | ∃ x : V, x ∈ L ∧ ∃ y ∈ twoScaleIdeal q L,
    z = q.quadratic x + y}

/-- O'Meara's scalar notion of a norm generator: `a` belongs to the norm
group `gL` and generates the norm ideal `nL`.  It need not itself lie in
`Q(L)`; this distinction is essential because `gL = Q(L) + 2sL` and because
the negative of a norm generator is again a norm generator (O'Meara 93:5). -/
def IsNormGeneratorValue (q : QuadraticSpace K V) (L : Lattice K V)
    (a : Kˣ) : Prop :=
  (a : K) ∈ normGroupSet q L ∧
    normIdeal q L = principalIdeal (K := K) (a : K)

/-- The absolute quadratic-defect ideal `d(a)`.  A square has zero defect
ideal; otherwise its order is `ord(a) + d(a)`. -/
noncomputable def quadraticDefectIdeal (a : Kˣ) :
    CoefficientIdeal (K := K) :=
  if quadraticDefect K a = ⊤ then
    ⊥
  else
    powerIdeal (K := K)
      (ordUnit K a + Int.ofNat (quadraticDefect K a).toNat)

/-- The two conditions on a candidate `w` in Lemma 2.10. -/
noncomputable def SatisfiesWeightIdealConditions
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ)
    (w : OrderedFractionalIdeal K) : Prop :=
  normGroupSet q L = integralSquareCoset (a : K) w.carrier ∧
    (w.carrier = twoScaleIdeal q L ∨ Odd (ordUnit K a + w.order))

/-- A finite Minkowski sum of scalar sets. -/
def indexedSetSum {t : Nat} (A : Fin t → Set K) : Set K :=
  {z | ∃ x : Fin t → K, (∀ i, x i ∈ A i) ∧ z = ∑ i, x i}

/-- The Minkowski sum of a scalar set and a coefficient ideal. -/
def setPlusIdeal (A : Set K) (I : CoefficientIdeal (K := K)) : Set K :=
  {z | ∃ x ∈ A, ∃ y ∈ I, z = x + y}

end Lattice

/-- Chosen weight ideals and O'Meara's exact characterization, Lemma 2.10.
This class intentionally has no default instance. -/
class Beli2009WeightIdealData
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] where
  weight
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) :
    Lattice.OrderedFractionalIdeal K
  twoScale_le_weight
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) :
    Lattice.twoScaleIdeal q L ≤ (weight q L).carrier
  characterize
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (a : Kˣ) (ha : Lattice.IsNormGeneratorValue q L a)
    (w : Lattice.OrderedFractionalIdeal K)
    (hw : Lattice.twoScaleIdeal q L ≤ w.carrier) :
    w.carrier = (weight q L).carrier ↔
      Lattice.SatisfiesWeightIdealConditions q L a w

namespace Lattice

variable {q : QuadraticSpace K V} {L : Lattice K V}
  [Beli2009WeightIdealData.{u, v} K]

/-- O'Meara's weight ideal `wL`. -/
noncomputable def weightIdeal (q : QuadraticSpace K V)
    (L : Lattice K V) : CoefficientIdeal (K := K) :=
  (Beli2009WeightIdealData.weight q L).carrier

/-- The order of `wL`. -/
noncomputable def weightIdealOrder (q : QuadraticSpace K V)
    (L : Lattice K V) : Int :=
  (Beli2009WeightIdealData.weight q L).order

theorem weightIdeal_eq_powerIdeal (q : QuadraticSpace K V)
    (L : Lattice K V) :
    weightIdeal q L = powerIdeal (K := K) (weightIdealOrder q L) :=
  (Beli2009WeightIdealData.weight q L).carrier_eq_powerIdeal

theorem twoScaleIdeal_le_weightIdeal (q : QuadraticSpace K V)
    (L : Lattice K V) : twoScaleIdeal q L ≤ weightIdeal q L :=
  Beli2009WeightIdealData.twoScale_le_weight q L

/-- Beli (2009/2010), Lemma 2.10. -/
theorem beli2009Lemma210
    (a : Kˣ) (ha : IsNormGeneratorValue q L a)
    (w : OrderedFractionalIdeal K)
    (hw : twoScaleIdeal q L ≤ w.carrier) :
    w.carrier = weightIdeal q L ↔
      SatisfiesWeightIdealConditions q L a w :=
  Beli2009WeightIdealData.characterize a ha w hw

end Lattice

namespace Lattice.OrthogonalDecomposition

variable {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}
  [Beli2009WeightIdealData.{u, v} K]

/-- The right-hand side of the norm-group formula in Lemma 2.11. -/
noncomputable def normGroupExpression
    (D : OrthogonalDecomposition q L t) : Set K :=
  setPlusIdeal
    (indexedSetSum fun i =>
      normGroupSet (D.component i).space (D.component i).lattice)
    (twoScaleIdeal q L)

/-- The sum of the component weight ideals. -/
noncomputable def componentWeightSum
    (D : OrthogonalDecomposition q L t) : CoefficientIdeal (K := K) :=
  ⨆ i, weightIdeal (D.component i).space (D.component i).lattice

/-- The sum of the terms `a⁻¹ d(a a_k)`. -/
noncomputable def componentDefectSum
    (D : OrthogonalDecomposition q L t) (a : Kˣ)
    (ak : Fin t → Kˣ) : CoefficientIdeal (K := K) :=
  ⨆ i, scalarIdeal ((a⁻¹ : Kˣ) : K)
    (quadraticDefectIdeal (a * ak i))

/-- The right-hand side of the weight-ideal formula in Lemma 2.11. -/
noncomputable def weightIdealExpression
    (D : OrthogonalDecomposition q L t) (a : Kˣ)
    (ak : Fin t → Kˣ) : CoefficientIdeal (K := K) :=
  D.componentWeightSum ⊔ D.componentDefectSum a ak ⊔ twoScaleIdeal q L

end Lattice.OrthogonalDecomposition

/-- The local orthogonal-sum calculation used in Lemma 2.11.
This class intentionally has no default instance. -/
class Beli2009OrthogonalIdealLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  lemma211
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}
    [Beli2009WeightIdealData.{u, v} K]
    (D : Lattice.OrthogonalDecomposition q L t)
    (a : Kˣ) (ha : Lattice.IsNormGeneratorValue q L a)
    (ak : Fin t → Kˣ)
    (hak : ∀ i, Lattice.IsNormGeneratorValue
      (D.component i).space (D.component i).lattice (ak i)) :
    Lattice.normGroupSet q L = D.normGroupExpression ∧
      Lattice.weightIdeal q L = D.weightIdealExpression a ak

namespace Lattice.OrthogonalDecomposition

variable {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}
  [Beli2009WeightIdealData.{u, v} K]
  [Beli2009OrthogonalIdealLaws.{u, v} K]

/-- Beli (2009/2010), Lemma 2.11. -/
theorem beli2009Lemma211
    (D : OrthogonalDecomposition q L t)
    (a : Kˣ) (ha : IsNormGeneratorValue q L a)
    (ak : Fin t → Kˣ)
    (hak : ∀ i, IsNormGeneratorValue
      (D.component i).space (D.component i).lattice (ak i)) :
    normGroupSet q L = D.normGroupExpression ∧
      weightIdeal q L = D.weightIdealExpression a ak :=
  Beli2009OrthogonalIdealLaws.lemma211 D a ha ak hak

end Lattice.OrthogonalDecomposition

namespace Lattice

/-- The ideal data at one boundary of a Jordan chain.  The duplicated norm
ideal fields encode the hypotheses `nL_k = nL^{s_k}` and
`nL_{k+1} = nL^{s_{k+1}}` from Lemma 2.12. -/
structure StableJordanBoundaryData
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] where
  scaleGenerator : Kˣ
  leftNormGenerator : Kˣ
  rightNormGenerator : Kˣ
  leftComponentNormIdeal : CoefficientIdeal (K := K)
  leftScaleLayerNormIdeal : CoefficientIdeal (K := K)
  rightComponentNormIdeal : CoefficientIdeal (K := K)
  rightScaleLayerNormIdeal : CoefficientIdeal (K := K)
  leftComponentNorm_eq :
    leftComponentNormIdeal = principalIdeal (leftNormGenerator : K)
  leftScaleLayerNorm_eq :
    leftScaleLayerNormIdeal = principalIdeal (leftNormGenerator : K)
  rightComponentNorm_eq :
    rightComponentNormIdeal = principalIdeal (rightNormGenerator : K)
  rightScaleLayerNorm_eq :
    rightScaleLayerNormIdeal = principalIdeal (rightNormGenerator : K)
  leftDualWeight : OrderedFractionalIdeal K
  rightTailWeight : OrderedFractionalIdeal K
  fundamentalIdeal : OrderedFractionalIdeal K

namespace StableJordanBoundaryData

variable (B : StableJordanBoundaryData K)

/-- The order `r_k` of the scale. -/
noncomputable def scaleOrder : Int :=
  ordUnit K B.scaleGenerator

/-- The order `u_k` of the left norm. -/
noncomputable def leftNormOrder : Int :=
  ordUnit K B.leftNormGenerator

/-- The order `u_{k+1}` of the right norm. -/
noncomputable def rightNormOrder : Int :=
  ordUnit K B.rightNormGenerator

theorem leftNormStable :
    B.leftComponentNormIdeal = B.leftScaleLayerNormIdeal :=
  B.leftComponentNorm_eq.trans B.leftScaleLayerNorm_eq.symm

theorem rightNormStable :
    B.rightComponentNormIdeal = B.rightScaleLayerNormIdeal :=
  B.rightComponentNorm_eq.trans B.rightScaleLayerNorm_eq.symm

/-- The right-hand side of Lemma 2.12. -/
noncomputable def fundamentalIdealExpression :
    CoefficientIdeal (K := K) :=
  let sInvSq : Kˣ := B.scaleGenerator⁻¹ ^ 2
  let boundaryProduct := B.leftNormGenerator * B.rightNormGenerator
  scalarIdeal (sInvSq : K) (quadraticDefectIdeal boundaryProduct) ⊔
    scalarIdeal
      ((B.leftNormGenerator * sInvSq : Kˣ) : K)
      B.rightTailWeight.carrier ⊔
    scalarIdeal (B.rightNormGenerator : K) B.leftDualWeight.carrier ⊔
    twiceIdeal
      (powerIdeal (K := K)
        ((B.leftNormOrder + B.rightNormOrder) / 2 - B.scaleOrder))

end StableJordanBoundaryData

end Lattice

/-- O'Meara's formula 93:26 together with the ideal eliminations in the
proof of Lemma 2.12.  This class intentionally has no default instance. -/
class Beli2009FundamentalIdealLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  lemma212 (B : Lattice.StableJordanBoundaryData K)
    (heven : Even (B.leftNormOrder + B.rightNormOrder)) :
    B.fundamentalIdeal.carrier = B.fundamentalIdealExpression

namespace Lattice.StableJordanBoundaryData

variable [Beli2009FundamentalIdealLaws.{u} K]

/-- Beli (2009/2010), Lemma 2.12. -/
theorem beli2009Lemma212 (B : StableJordanBoundaryData K)
    (heven : Even (B.leftNormOrder + B.rightNormOrder)) :
    B.fundamentalIdeal.carrier = B.fundamentalIdealExpression :=
  Beli2009FundamentalIdealLaws.lemma212 B heven

end Lattice.StableJordanBoundaryData

end Bong
