/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma65

/-!
# Beli (2003), Lemma 6.6 and the following remark

The exponent in Lemma 6.6 is the unrounded half-integer
`(R₃-R₁)/2`.  For a discretely valued field this means the ceiling.  The
following remark replaces it by the floor used in Theorem 1; that weakening
is derived below from antitonicity of principal-unit square-class subgroups.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG

/-- The ceiling of `(R₃-R₁)/2`, the sharp exponent in Lemma 6.6. -/
noncomputable def lemma66SharpDepth (b : BONG V q L (n + 3)) : Nat :=
  Int.toNat ((b.order 2 - b.order 0 + 1) / 2)

/-- The floor of `(R₃-R₁)/2`, used in Theorem 1. -/
noncomputable def lemma66FlooredDepth (b : BONG V q L (n + 3)) : Nat :=
  b.theoremOneTwoStepDepth 0

/-- The sharp principal-unit factor in Lemma 6.6. -/
noncomputable def lemma66SharpCongruenceFactor
    (b : BONG V q L (n + 3)) : Subgroup (SquareClass K) :=
  principalUnitSquareClassSubgroup K b.lemma66SharpDepth

/-- The weakened principal-unit factor in the remark after Lemma 6.6. -/
noncomputable def lemma66FlooredCongruenceFactor
    (b : BONG V q L (n + 3)) : Subgroup (SquareClass K) :=
  principalUnitSquareClassSubgroup K b.lemma66FlooredDepth

/-- The target group `H` in the sharp Lemma 6.6. -/
noncomputable def lemma66SharpHeadFactor
    (b : BONG V q L (n + 3)) : Subgroup (SquareClass K) :=
  beliSpinorGroup K (b.adjacentUnitSquareClass 0 (by simp)) ⊔
    b.lemma66SharpCongruenceFactor

/-- The obstruction group `H'` in the sharp Lemma 6.6. -/
noncomputable def lemma66SharpTailFactor
    (b : BONG V q L (n + 3)) : Subgroup (SquareClass K) :=
  beliSpinorGroup K (b.adjacentUnitSquareClass 1 (by simp)) ⊔
    b.lemma66SharpCongruenceFactor

/-- The target group after replacing the half-integer exponent by its floor. -/
noncomputable def lemma66FlooredHeadFactor
    (b : BONG V q L (n + 3)) : Subgroup (SquareClass K) :=
  beliSpinorGroup K (b.adjacentUnitSquareClass 0 (by simp)) ⊔
    b.lemma66FlooredCongruenceFactor

/-- The obstruction group after replacing the exponent by its floor. -/
noncomputable def lemma66FlooredTailFactor
    (b : BONG V q L (n + 3)) : Subgroup (SquareClass K) :=
  beliSpinorGroup K (b.adjacentUnitSquareClass 1 (by simp)) ⊔
    b.lemma66FlooredCongruenceFactor

/-- Property B makes the floor no larger than the ceiling. -/
theorem lemma66FlooredDepth_le_sharpDepth
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB) :
    b.lemma66FlooredDepth ≤ b.lemma66SharpDepth := by
  have h02 : b.order 0 < b.order 2 := hB.1 0 (by simp)
  unfold lemma66FlooredDepth theoremOneTwoStepDepth lemma66SharpDepth
  change Int.toNat ((b.order 2 - b.order 0) / 2) ≤
    Int.toNat ((b.order 2 - b.order 0 + 1) / 2)
  omega

/-- The sharp congruence group is contained in its floored weakening. -/
theorem lemma66SharpCongruenceFactor_le_floored
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB) :
    b.lemma66SharpCongruenceFactor ≤
      b.lemma66FlooredCongruenceFactor :=
  principalUnitSquareClassSubgroup_anti K
    (b.lemma66FlooredDepth_le_sharpDepth hB)

/-- The sharp head factor is contained in the factor from the remark. -/
theorem lemma66SharpHeadFactor_le_floored
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB) :
    b.lemma66SharpHeadFactor ≤ b.lemma66FlooredHeadFactor :=
  sup_le_sup le_rfl (b.lemma66SharpCongruenceFactor_le_floored hB)

/-- The sharp tail obstruction is contained in its floored version. -/
theorem lemma66SharpTailFactor_le_floored
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB) :
    b.lemma66SharpTailFactor ≤ b.lemma66FlooredTailFactor :=
  sup_le_sup le_rfl (b.lemma66SharpCongruenceFactor_le_floored hB)

/-- A vector of the same quadratic value as the BONG head is again a norm
generator of the lattice. -/
theorem isNormGenerator_of_quadratic_eq_head
    (b : BONG V q L (n + 3)) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head) :
    Lattice.IsNormGenerator q L x := by
  apply (b.isNormGenerator_iff_ord_quadratic_eq_head x hx).2
  rw [heq, ← b.value_zero_eq_quadratic_head]
  exact (b.coe_order 0).symm

/-- The transport assertion in the sharp form of Beli (2003), Lemma 6.6.
This interface has no default instance. -/
class BeliLemma66Laws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  exists_rotation
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hproper : b.lemma66SharpTailFactor ≠ ⊤) :
    ∃ f : Lattice.IntegralRotation q L,
      f.apply b.head = x ∧ f.spinorNorm ∈ b.lemma66SharpHeadFactor

variable [BeliLemma66Laws.{u, v} K]

/-- Beli (2003), Lemma 6.6 in its sharp, ceiling-depth form. -/
theorem beliLemma66 (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hproper : b.lemma66SharpTailFactor ≠ ⊤) :
    ∃ f : Lattice.IntegralRotation q L,
      f.apply b.head = x ∧ f.spinorNorm ∈ b.lemma66SharpHeadFactor :=
  BeliLemma66Laws.exists_rotation b hB x hx heq hproper

/-- The remark following Lemma 6.6: the conclusion remains valid with the
floored depth used in Theorem 1. -/
theorem beliLemma66_floored
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hproper : b.lemma66FlooredTailFactor ≠ ⊤) :
    ∃ f : Lattice.IntegralRotation q L,
      f.apply b.head = x ∧ f.spinorNorm ∈ b.lemma66FlooredHeadFactor := by
  have hsharpProper : b.lemma66SharpTailFactor ≠ ⊤ := by
    intro htop
    apply hproper
    apply top_unique
    rw [← htop]
    exact b.lemma66SharpTailFactor_le_floored hB
  rcases b.beliLemma66 hB x hx heq hsharpProper with ⟨f, hfx, hfspinor⟩
  exact ⟨f, hfx, b.lemma66SharpHeadFactor_le_floored hB hfspinor⟩

end BONG

end Bong
