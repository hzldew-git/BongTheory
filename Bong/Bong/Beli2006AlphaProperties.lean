/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Invariants
import Bong.Bong.Dual

/-!
# Beli (2006), alpha properties

This file contains the definitions of properties P1--P7.  Their proofs are
kept in separate modules so that proved properties do not remain fields of a
local-law interface.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG.GoodBONG

/-- The adjacent order difference `R_{i+1} - R_i`. -/
noncomputable def orderGap (b : GoodBONG q L (n + 1)) (i : Fin n) : Int :=
  b.order i.succ - b.order i.castSucc

/-- The finite version of `(R_{i+1} - R_i) / 2 + e`. -/
noncomputable def halfGapValue (b : GoodBONG q L (n + 1)) (i : Fin n) : ℚ :=
  (b.orderGap i : ℚ) / 2 + (ramificationIndex K : ℚ)

@[simp]
theorem coe_halfGapValue (b : GoodBONG q L (n + 1)) (i : Fin n) :
    (b.halfGapValue i : WithTop ℚ) = b.halfGapCandidate i := by
  rfl

/-- The sequence `R_i + α_i` in property P1. -/
noncomputable def alphaLeftEndpoint
    (b : GoodBONG q L (n + 1)) (i : Fin n) : ℚ :=
  (b.order i.castSucc : ℚ) + b.alphaValue i

/-- The sequence `-R_{i+1} + α_i` in property P1. -/
noncomputable def alphaRightEndpoint
    (b : GoodBONG q L (n + 1)) (i : Fin n) : ℚ :=
  -(b.order i.succ : ℚ) + b.alphaValue i

/-- Property P1: the left endpoints increase and the right endpoints decrease. -/
noncomputable def SatisfiesAlphaP1 (b : GoodBONG q L (n + 1)) : Prop :=
  ∀ (i : Fin n) (hi : i.1 + 1 < n),
    b.alphaLeftEndpoint i ≤
        b.alphaLeftEndpoint ⟨i.1 + 1, hi⟩ ∧
      b.alphaRightEndpoint ⟨i.1 + 1, hi⟩ ≤
        b.alphaRightEndpoint i

/-- Property P2: `α_i` is nonnegative, with the stated equality case. -/
noncomputable def SatisfiesAlphaP2 (b : GoodBONG q L (n + 1)) : Prop :=
  ∀ i,
    0 ≤ b.alphaValue i ∧
      (b.alphaValue i = 0 ↔
        b.orderGap i = -(2 * (ramificationIndex K : Int)))

/-- Property P3, including both the lower bound and its equality cases. -/
noncomputable def SatisfiesAlphaP3 (b : GoodBONG q L (n + 1)) : Prop :=
  ∀ i,
    b.orderGap i ≤ 2 * (ramificationIndex K : Int) →
      (b.orderGap i : ℚ) ≤ b.alphaValue i ∧
        (b.alphaValue i = (b.orderGap i : ℚ) ↔
          b.orderGap i = 2 * (ramificationIndex K : Int) ∨
            Odd (b.orderGap i))

/-- Property P4: above `2e`, the half-gap candidate attains the minimum. -/
noncomputable def SatisfiesAlphaP4 (b : GoodBONG q L (n + 1)) : Prop :=
  ∀ i,
    2 * (ramificationIndex K : Int) ≤ b.orderGap i →
      b.alphaValue i = b.halfGapValue i

/-- Property P5: `α_i` and its order gap lie on the same side of `2e`. -/
noncomputable def SatisfiesAlphaP5 (b : GoodBONG q L (n + 1)) : Prop :=
  ∀ i,
    (b.alphaValue i < 2 * (ramificationIndex K : ℚ) ↔
      b.orderGap i < 2 * (ramificationIndex K : Int)) ∧
    (b.alphaValue i = 2 * (ramificationIndex K : ℚ) ↔
      b.orderGap i = 2 * (ramificationIndex K : Int)) ∧
    (2 * (ramificationIndex K : ℚ) < b.alphaValue i ↔
      2 * (ramificationIndex K : Int) < b.orderGap i)

/-- Property P6: equal orders two places apart bound two adjacent alphas. -/
noncomputable def SatisfiesAlphaP6 (b : GoodBONG q L (n + 1)) : Prop :=
  ∀ (i : Fin n) (hi : i.1 + 1 < n),
    b.order i.castSucc = b.order (⟨i.1 + 1, hi⟩ : Fin n).succ →
      b.alphaValue i + b.alphaValue ⟨i.1 + 1, hi⟩ ≤
        2 * (ramificationIndex K : ℚ)

/-- A good BONG whose vectors are the reversed bilinear-dual vectors of `b`. -/
def IsReverseDualGoodBONG (b : GoodBONG q L (n + 1))
    (c : GoodBONG q (Lattice.dualLattice q L) (n + 1)) : Prop :=
  ∀ i, c.toBONG.ambientVector i = b.toBONG.reverseDualVector i

/-- Property P7: alpha values reverse under lattice duality. -/
noncomputable def SatisfiesAlphaP7 (b : GoodBONG q L (n + 1)) : Prop :=
  ∀ (c : GoodBONG q (Lattice.dualLattice q L) (n + 1)),
    b.IsReverseDualGoodBONG c →
      ∀ i, c.alphaValue i = b.alphaValue (Fin.rev i)

/-- The still-unproved properties from Beli (2006), Section 3.
Only P2 and P3 remain in this bundle. -/
structure Beli2006AlphaProperties (b : GoodBONG q L (n + 1)) : Prop where
  p2 : b.SatisfiesAlphaP2
  p3 : b.SatisfiesAlphaP3

end BONG.GoodBONG

end Bong
