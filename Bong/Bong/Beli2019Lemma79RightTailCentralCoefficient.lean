/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailPropagation

/-!
# Beli (2019), Lemma 7.9(ii), case 8: the central coefficient

The constant-right-endpoint identity rewrites every beta on the tail as
`S_(j+1) - S_(u+1) + beta_u`.  Consequently the expression
`S_u - S_(j+1) + beta_j` is independent of `j`.  This is the common
coefficient occurring throughout the type-I gap-two proof.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M : Lattice K V} {n : Nat}

/-- The paper's coefficient `S_u - S_(j+1) + beta_j` is constant on the
case-8 beta tail. -/
theorem CaseEightBetaTailConsequences.centralCoefficient_eq
    {b : GoodBONG q M (n + 2)} {first last : Fin (n + 1)}
    (H : CaseEightBetaTailConsequences b first last)
    (j : Fin (n + 1)) (hfirst : first <= j) (hlast : j <= last) :
    ((b.order first.castSucc - b.order j.succ : Int) : Rat) +
        b.alphaValue j =
      ((b.order first.castSucc - b.order first.succ : Int) : Rat) +
        b.alphaValue first := by
  have hvalue := H.value_eq j hfirst hlast
  push_cast at hvalue ⊢
  linarith

/-- `WithTop` form of the constant central coefficient, ready for capped
defect comparisons. -/
theorem CaseEightBetaTailConsequences.coe_centralCoefficient_eq
    {b : GoodBONG q M (n + 2)} {first last : Fin (n + 1)}
    (H : CaseEightBetaTailConsequences b first last)
    (j : Fin (n + 1)) (hfirst : first <= j) (hlast : j <= last) :
    ((((b.order first.castSucc - b.order j.succ : Int) : Rat) +
        b.alphaValue j : Rat) : WithTop Rat) =
      ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
        b.alphaValue first : Rat) : WithTop Rat) := by
  exact_mod_cast H.centralCoefficient_eq j hfirst hlast

end BONG.GoodBONG

end Bong
