/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.AlternatingEndpointTowerRepresentation
import Bong.Bong.BeliCorollary44
import Bong.Bong.Beli2019CanonicalApproximation

/-!
# Integral normalization of alternating endpoint towers

The representation results for diagonal quadratic spaces do not by
themselves replace an integral BONG prefix inside the same lattice.  This
file isolates the stronger, paper-independent integral classification input:
two split endpoint towers with the same coefficient orders and determinant
square class may be exchanged, leaving the complementary suffix fixed.

This is the local integral-lattice content behind the use of O'Meara,
Theorem 93:14, in Beli (2019), Lemma 7.18.  No default instance is supplied.
-/

namespace Bong

open Dyadic

universe u v

/-- The rigid order profile occurring in Beli's alternating endpoint towers. -/
def AlternatingEndpointOrderProfile
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {pairs : Nat} (a : Fin (2 * pairs) → Kˣ) (R : Int) : Prop :=
  ∀ t : Fin pairs,
    ordUnit K (a ⟨2 * t.val, by omega⟩) = R ∧
      ordUnit K (a ⟨2 * t.val + 1, by omega⟩) =
        R - 2 * (ramificationIndex K : Int)

/-- Integral endpoint-tower normalization and gluing.  The conclusion is an
actual good BONG on the original lattice, not merely an isometry of ambient
quadratic spaces. -/
class DyadicAlternatingEndpointTowerNormalizationLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [DyadicDiscriminantClassLaws K] : Prop where
  normalizeSplitPrefix
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    {n pairs : Nat}
    (b : BONG.GoodBONG q L (n + 1))
    (hbound : 2 * pairs ≤ n + 1)
    (target : Fin (2 * pairs) → Kˣ)
    (hsource : AlternatingEndpointPairClasses
      (b.prefixValueUnits (2 * pairs) hbound))
    (htarget : AlternatingEndpointPairClasses target)
    (R : Int)
    (htargetProfile : AlternatingEndpointOrderProfile target R)
    (horders : ∀ i : Fin (2 * pairs),
      ordUnit K (target i) =
        ordUnit K ((b.prefixValueUnits (2 * pairs) hbound) i))
    (hdet : IsSquare
      (BONG.GoodBONG.diagonalUnitDeterminant
          (b.prefixValueUnits (2 * pairs) hbound) *
        BONG.GoodBONG.diagonalUnitDeterminant target)) :
    ∃ c : BONG.GoodBONG q L (n + 1),
      (∀ i : Fin (2 * pairs),
        c.valueUnit ⟨i.val, i.isLt.trans_le hbound⟩ = target i) ∧
      (∀ j : Fin (n + 1), 2 * pairs ≤ j.val →
        c.valueUnit j = b.valueUnit j)

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  [DyadicAlternatingEndpointTowerNormalizationLaws.{u, v} K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}
  {n pairs : Nat}

/-- Public form of integral endpoint-tower normalization. -/
theorem exists_normalizedSplitPrefix
    (b : GoodBONG q L (n + 1))
    (hbound : 2 * pairs ≤ n + 1)
    (target : Fin (2 * pairs) → Kˣ)
    (hsource : AlternatingEndpointPairClasses
      (b.prefixValueUnits (2 * pairs) hbound))
    (htarget : AlternatingEndpointPairClasses target)
    (R : Int)
    (htargetProfile : AlternatingEndpointOrderProfile target R)
    (horders : ∀ i : Fin (2 * pairs),
      ordUnit K (target i) =
        ordUnit K ((b.prefixValueUnits (2 * pairs) hbound) i))
    (hdet : IsSquare
      (diagonalUnitDeterminant
          (b.prefixValueUnits (2 * pairs) hbound) *
        diagonalUnitDeterminant target)) :
    ∃ c : GoodBONG q L (n + 1),
      (∀ i : Fin (2 * pairs),
        c.valueUnit ⟨i.val, i.isLt.trans_le hbound⟩ = target i) ∧
      (∀ j : Fin (n + 1), 2 * pairs ≤ j.val →
        c.valueUnit j = b.valueUnit j) :=
  DyadicAlternatingEndpointTowerNormalizationLaws.normalizeSplitPrefix
    b hbound target hsource htarget R htargetProfile horders hdet

/-- Any prefix normalization with pointwise-preserved orders and an unchanged
suffix preserves the complete BONG order sequence. -/
theorem normalizedSplitPrefix_order_eq
    (b c : GoodBONG q L (n + 1))
    {m : Nat} (hbound : m ≤ n + 1) (target : Fin m → Kˣ)
    (hprefix : ∀ i : Fin m,
      c.valueUnit ⟨i.val, i.isLt.trans_le hbound⟩ = target i)
    (hsuffix : ∀ j : Fin (n + 1), m ≤ j.val →
      c.valueUnit j = b.valueUnit j)
    (horders : ∀ i : Fin m,
      ordUnit K (target i) =
        ordUnit K ((b.prefixValueUnits m hbound) i))
    (j : Fin (n + 1)) :
    c.order j = b.order j := by
  rw [GoodBONG.order, GoodBONG.order,
    c.toBONG.order_eq_ordUnit, b.toBONG.order_eq_ordUnit]
  change ordUnit K (c.valueUnit j) = ordUnit K (b.valueUnit j)
  by_cases hj : j.val < m
  · let i : Fin m := ⟨j.val, hj⟩
    have hindex : (⟨i.val, i.isLt.trans_le hbound⟩ : Fin (n + 1)) = j :=
      Fin.ext rfl
    calc
      ordUnit K (c.valueUnit j) = ordUnit K (target i) := by
        rw [← hprefix i, hindex]
      _ = ordUnit K ((b.prefixValueUnits m hbound) i) := horders i
      _ = ordUnit K (b.valueUnit j) := by
        simp only [prefixValueUnits, i]
  · rw [hsuffix j (Nat.le_of_not_gt hj)]

end BONG.GoodBONG

end Bong
