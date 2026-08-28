/- Beli 2019, Lemma 3.7: the residual (non-triggered) case. -/
import Bong.Bong.Beli2019Lemma37Endpoints

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- Beli (2019), Lemma 3.7, final sentence: when the two neighbouring
two-step orders agree, both representation clauses in Definition 10 are
vacuous, so determinant approximation is sufficient. -/
theorem beli2019Lemma37_other
    {n : Nat} (a : BONG.GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (c : Fin (i.val + 1) → Kˣ)
    (hdet : a.IsPrefixApproximation (i.val + 1)
      (diagonalUnitDeterminant c))
    (hpositive : 0 < i.val)
    (hinternal : i.val + 1 < n + 1)
    (hleftOuter : a.order ⟨i.val - 1, by omega⟩ =
      a.order ⟨i.val + 1, by omega⟩)
    (hrightOuter : a.order i.castSucc =
      a.order (⟨i.val + 1, hinternal⟩ : Fin (n + 1)).succ) :
    a.IsSpaceApproximation i c := by
  have hnotLeft :=
    a.not_leftApproximationTrigger_of_twoStepOrder_eq i hpositive hleftOuter
  have hnotRight :=
    a.not_rightApproximationTrigger_of_twoStepOrder_eq i hinternal hrightOuter
  exact
    ⟨⟨hdet, fun htrigger ↦ (hnotLeft htrigger).elim⟩,
      ⟨hdet, fun htrigger ↦ (hnotRight htrigger).elim⟩⟩

end BONG.GoodBONG

end Bong
