/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328Conditions
import Bong.Lattice.OmearaSaturatedTailIdeals

/-!
# Coherent fundamental norm generators for O'Meara 93:28

O'Meara chooses one norm generator for each fundamental lattice and uses the
same choices throughout the induction.  A bare `Classical.choose` on every
new tail does not preserve those choices definitionally.  This module makes
the coherent choice explicit while retaining the existing canonical
specialization as the public statement.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {t : Nat}

/-- A coherent choice of scalar norm generator in every fundamental
lattice of a Jordan decomposition. -/
structure FundamentalNormGeneratorChoice
    (J : JordanDecomposition q L t) where
  value : Fin t → Kˣ
  spec (i : Fin t) :
    IsNormGeneratorValue q (J.fundamentalLattice i) (value i)

/-- The pre-existing `Classical.choose` specialization. -/
noncomputable def canonicalFundamentalNormGeneratorChoice
    (J : JordanDecomposition q L t) :
    FundamentalNormGeneratorChoice J where
  value := J.fundamentalNormGenerator
  spec := J.fundamentalNormGenerator_spec

namespace FundamentalNormGeneratorChoice

variable {J : JordanDecomposition q L t}
  {H : JordanDecomposition r M t}

/-- Replace one coherent generator by any other valid generator of the same
fundamental lattice.  This is the formal version of O'Meara's convention
that a boundary norm generator may be chosen to match a displayed unary
line or a BONG endpoint. -/
noncomputable def replaceAt
    (A : FundamentalNormGeneratorChoice J) (i : Fin t) (x : Kˣ)
    (hx : IsNormGeneratorValue q (J.fundamentalLattice i) x) :
    FundamentalNormGeneratorChoice J where
  value := fun j ↦ if h : j = i then x else A.value j
  spec := by
    intro j
    by_cases h : j = i
    · subst j
      simpa using hx
    · simp only [h, ↓reduceDIte]
      exact A.spec j

@[simp]
theorem replaceAt_value_same
    (A : FundamentalNormGeneratorChoice J) (i : Fin t) (x : Kˣ)
    (hx : IsNormGeneratorValue q (J.fundamentalLattice i) x) :
    (A.replaceAt i x hx).value i = x := by
  simp [replaceAt]

@[simp]
theorem replaceAt_value_of_ne
    (A : FundamentalNormGeneratorChoice J) (i j : Fin t) (x : Kˣ)
    (hx : IsNormGeneratorValue q (J.fundamentalLattice i) x)
    (hji : j ≠ i) :
    (A.replaceAt i x hx).value j = A.value j := by
  simp [replaceAt, hji]

/-- Every coherent fundamental norm generator has the same valuation as
the canonical generator of the same fundamental lattice. -/
theorem value_order_eq_fundamentalNormGenerator
    (A : FundamentalNormGeneratorChoice J) (i : Fin t) :
    ordUnit K (A.value i) = ordUnit K (J.fundamentalNormGenerator i) := by
  apply (principalIdeal_eq_iff_ordUnit_eq _ _).mp
  exact (A.spec i).2.symm.trans (J.fundamentalNormGenerator_spec i).2

/-- A choice on the source is valid on a decomposition of the same
fundamental type. -/
theorem spec_right (A : FundamentalNormGeneratorChoice J)
    (F : SameFundamentalType J H) (i : Fin t) :
    IsNormGeneratorValue r
      (H.fundamentalLattice (F.indexEquiv i)) (A.value i) := by
  apply isNormGeneratorValue_of_normGroupSet_eq (A.spec i)
  · exact (F.normGroup_eq i).symm
  · exact H.exists_fundamentalNormGenerator (F.indexEquiv i)

/-- A coherent choice restricts to the exact suffix of a saturated
splitting without making any new arbitrary choices. -/
noncomputable def tail {n : Nat}
    {J : JordanDecomposition q L (n + 1)}
    (A : FundamentalNormGeneratorChoice J) (hJ : J.IsSaturated) :
    FundamentalNormGeneratorChoice J.tail where
  value := fun i => A.value i.succ
  spec := by
    intro i
    exact isNormGeneratorValue_of_normGroupSet_eq
      (A.spec i.succ)
      (IsSaturated.tail_fundamentalNormGroup_eq J hJ i).symm
      (J.tail.exists_fundamentalNormGenerator i)

@[simp]
theorem tail_value {n : Nat}
    {J : JordanDecomposition q L (n + 1)}
    (A : FundamentalNormGeneratorChoice J) (hJ : J.IsSaturated)
    (i : Fin n) :
    (A.tail hJ).value i = A.value i.succ :=
  rfl

end FundamentalNormGeneratorChoice

/-- The threshold `4 a_i w_i⁻¹` formed with an explicit coherent norm
generator. -/
noncomputable def fourNormOverWeightIdealWith
    (J : JordanDecomposition q L t)
    (A : FundamentalNormGeneratorChoice J) (i : Fin t) :
    CoefficientIdeal (K := K) :=
  powerIdeal (K := K)
    (2 * (ramificationIndex K : Int) + ordUnit K (A.value i) -
      J.fundamentalWeightOrder i)

@[simp]
theorem fourNormOverWeightIdealWith_canonical
    {n : Nat} (J : JordanDecomposition q L (n + 1))
    (i : Fin (n + 1)) :
    J.fourNormOverWeightIdealWith
        (canonicalFundamentalNormGeneratorChoice J) i =
      J.fourNormOverWeightIdeal i :=
  rfl

/-- The threshold ideal is independent of the chosen coherent norm
generator.  Only the generator's valuation enters its definition. -/
theorem fourNormOverWeightIdealWith_eq_canonical
    (J : JordanDecomposition q L t)
    (A : FundamentalNormGeneratorChoice J) (i : Fin t) :
    J.fourNormOverWeightIdealWith A i =
      powerIdeal (K := K)
        (2 * (ramificationIndex K : Int) +
          ordUnit K (J.fundamentalNormGenerator i) -
            J.fundamentalWeightOrder i) := by
  unfold fourNormOverWeightIdealWith
  rw [A.value_order_eq_fundamentalNormGenerator]

/-- The explicit threshold shifts exactly along the coherent tail choice. -/
theorem IsSaturated.tail_fourNormOverWeightIdealWith_eq
    {n : Nat} {J : JordanDecomposition q L (n + 1)}
    (hJ : J.IsSaturated) (A : FundamentalNormGeneratorChoice J)
    (i : Fin n) :
    J.tail.fourNormOverWeightIdealWith (A.tail hJ) i =
      J.fourNormOverWeightIdealWith A i.succ := by
  unfold fourNormOverWeightIdealWith
  rw [FundamentalNormGeneratorChoice.tail_value,
    IsSaturated.tail_fundamentalWeightOrder_eq J hJ]

/-- O'Meara 93:28(ii), with its proper-containment trigger and a coherent
generator choice. -/
noncomputable def Omeara9328ConditionIIWith
    {n : Nat} (J : JordanDecomposition q L (n + 1))
    (H : JordanDecomposition r M (n + 1))
    (A : FundamentalNormGeneratorChoice J) : Prop :=
  ∀ i : Fin n,
    J.fundamentalIdeal i <
        J.fourNormOverWeightIdealWith A (boundaryRightIndex i) →
      QuadraticSublattice.EmbedsIntoOrthogonalSum
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1))
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1))
        (QuadraticSpace.scaledLine (A.value (boundaryRightIndex i)))

/-- O'Meara 93:28(iii), with its proper-containment trigger and a coherent
generator choice. -/
noncomputable def Omeara9328ConditionIIIWith
    {n : Nat} (J : JordanDecomposition q L (n + 1))
    (H : JordanDecomposition r M (n + 1))
    (A : FundamentalNormGeneratorChoice J) : Prop :=
  ∀ i : Fin n,
    J.fundamentalIdeal i <
        J.fourNormOverWeightIdealWith A (boundaryLeftIndex i) →
      QuadraticSublattice.EmbedsIntoOrthogonalSum
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1))
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1))
        (QuadraticSpace.scaledLine (A.value (boundaryLeftIndex i)))

/-- The three conditions with a coherent common generator choice. -/
noncomputable def Omeara9328ConditionsWith
    {n : Nat} (J : JordanDecomposition q L (n + 1))
    (H : JordanDecomposition r M (n + 1))
    (A : FundamentalNormGeneratorChoice J) : Prop :=
  J.Omeara9328ConditionI H ∧ J.Omeara9328ConditionIIWith H A ∧
    J.Omeara9328ConditionIIIWith H A

/-- The existing semantic conditions are exactly the canonical-choice
specialization. -/
theorem omeara9328ConditionsWith_canonical_iff
    {n : Nat} (J : JordanDecomposition q L (n + 1))
    (H : JordanDecomposition r M (n + 1)) :
    J.Omeara9328ConditionsWith H
        (canonicalFundamentalNormGeneratorChoice J) ↔
      J.Omeara9328Conditions H :=
  Iff.rfl

end Lattice.JordanDecomposition

end Bong
