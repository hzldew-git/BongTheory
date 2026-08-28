/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoOddNonintegral
import Bong.Bong.Beli2019Lemma79EvenTypeIEqualityParity

/-!
# Beli (2019), Lemma 7.9(ii), case 8: odd equality endpoint

Equality in the extended odd-index domination chain identifies the right
alpha endpoint at the selected witness with the endpoint immediately before
`T_i`.  This is the odd analogue of the equality lemma used in lines
5931--5933 and prepares Lemma 7.3(ii) for lines 5971--5975.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {N : Lattice K V} {n : Nat}

/-- Equality of the odd comparison prefix with the transported domination
coefficient forces equality of the corresponding right endpoints. -/
theorem lemma79_odd_rightEndpoint_eq_of_domination_equality
    [Beli2006AlphaLaws.{u, v} K]
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 <= i.val) (j : Fin (n + 1))
    (hjBefore : j.val + 1 < i.val - 1) (current : Int)
    (hjOrder : c.order j.castSucc = current - 1)
    (hjDefect : c.truncatedPrefixDefect c (-1) j.val (j.val + 2) <=
      c.truncatedPrefixDefect c
        ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1))
    (heq : c.truncatedPrefixDefect c
        ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) =
      ((show Rat from
          ((current - c.order (evenTargetPreviousIndex i) : Int) : Rat) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) - 1) :
        WithTop Rat)) :
    c.alphaRightEndpoint j =
      c.alphaRightEndpoint (evenTargetPreviousAlphaIndex i) := by
  let p : Fin (n + 1) := evenTargetPreviousAlphaIndex i
  have hpVal : p.val = i.val - 2 := by
    simp only [p, evenTargetPreviousAlphaIndex]
  have hpSucc : p.succ = evenTargetPreviousIndex i := by
    apply Fin.ext
    simp only [p, evenTargetPreviousAlphaIndex, evenTargetPreviousIndex,
      Fin.succ_mk]
    omega
  have hjp : j <= p := by
    change j.val <= p.val
    rw [hpVal]
    omega
  have hselfWitness :
      c.truncatedPrefixDefect c
          ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) =
        (((((c.order j.castSucc - c.order p.succ : Int) : Rat) +
          c.alphaValue p : Rat)) : WithTop Rat) := by
    calc
      c.truncatedPrefixDefect c
          ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) =
          ((show Rat from
              ((current - c.order (evenTargetPreviousIndex i) : Int) : Rat) +
              c.alphaValue (evenTargetPreviousAlphaIndex i) - 1) :
            WithTop Rat) := heq
      _ = (((((c.order j.castSucc - c.order p.succ : Int) : Rat) +
          c.alphaValue p : Rat)) : WithTop Rat) := by
        rw [<- hpSucc]
        apply congrArg (fun z : Rat => (z : WithTop Rat))
        rw [hjOrder]
        push_cast
        ring
  have hadjacentToSelf :=
    (c.order_sub_add_alpha_le_cappedAdjacent j).trans hjDefect
  have hadjacentToWitness :
      (((((c.order j.castSucc - c.order j.succ : Int) : Rat) +
          c.alphaValue j : Rat)) : WithTop Rat) <=
        (((((c.order j.castSucc - c.order p.succ : Int) : Rat) +
          c.alphaValue p : Rat)) : WithTop Rat) := by
    rw [<- hselfWitness]
    exact hadjacentToSelf
  have hadjacentToWitnessQ :
      ((c.order j.castSucc - c.order j.succ : Int) : Rat) +
          c.alphaValue j <=
        ((c.order j.castSucc - c.order p.succ : Int) : Rat) +
          c.alphaValue p := by
    exact_mod_cast hadjacentToWitness
  have hreverse : c.alphaRightEndpoint j <= c.alphaRightEndpoint p := by
    unfold alphaRightEndpoint
    push_cast at hadjacentToWitnessQ ⊢
    linarith
  have hforward := c.alphaRightEndpoint_antitone hjp
  exact le_antisymm hreverse (by simpa only [p] using hforward)

end BONG.GoodBONG

end Bong
