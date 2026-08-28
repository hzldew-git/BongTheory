/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Corollary713GlobalCore

/-!
# Beli (2019), Corollary 7.13

This module proves the induction from Lemma 7.12(i), appends the unchanged
suffix, and identifies the resulting lattice with the literal orthogonal
product.  It exposes every coefficient used later in Lemma 7.18(iii).
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {J : Lattice K V} {T : Lattice K W} {s m : Nat}

/-- The concrete output of Corollary 7.13, followed by the unchanged suffix
as in the application in Lemma 7.18(iii). -/
structure Corollary713Realization
    (j : GoodBONG q J s) (t : GoodBONG r T (m + 1)) (R : Int) where
  bong : GoodBONG (q.orthogonalSum r) (Lattice.product J T) ((m + 1) + s)
  valueUnit_left (i : Fin s) :
    bong.valueUnit (orthogonalProductLeftIndex (m + 1) i) =
      corollary713PrefixValues (K := K) R i
  valueUnit_right (i : Fin (m + 1)) :
    bong.valueUnit (orthogonalProductRightIndex s i) = t.valueUnit i

/-- Beli (2019), Corollary 7.13 in the exact form consumed by Lemma
7.18(iii).  The alternating prefix is transformed by the induction from
Lemma 7.12(i); Lemma 7.10 then appends the unchanged suffix on the same
orthogonal-product lattice. -/
theorem exists_corollary713Realization
    [defect : QuadraticDefectLaws K]
    [hilbert : HilbertSymbolLaws K]
    [diagonal : DyadicDiagonalClassificationLaws K]
    [perfect : PerfectResidueFieldLaws K]
    [structural : BONGStructuralLaws.{u, u} K]
    [weight : Beli2009WeightIdealData.{u, u} K]
    [unaryBinary : Beli2019UnaryBinaryJordanLaws.{u} K]
    [jordanOrder : Beli2009JordanWeightOrderLaws.{u, u} K]
    [alpha : Beli2006AlphaLaws.{u, u} K]
    [constructionBase : BeliLemma43ConstructionLaws.{u, u} K]
    [sectionTwoBase : Beli2006SectionTwoLaws.{u, u} K]
    [classification : GoodBONGClassificationLaws.{u, u, u} K]
    [corollary44V : BeliCorollary44Laws.{u, v} K]
    [corollary44Product : BeliCorollary44Laws.{u, max v w} K]
    [sectionFourV : BONGReverseDualLaws.{u, v} K]
    [sectionFourW : BONGReverseDualLaws.{u, w} K]
    [sectionFourProduct : BONGReverseDualLaws.{u, max v w} K]
    [constructionProduct : BeliLemma43ConstructionLaws.{u, max v w} K]
    [sectionTwoProduct : Beli2006SectionTwoLaws.{u, max v w} K]
    (j : GoodBONG q J s) (t : GoodBONG r T (m + 1)) (R : Int)
    (hsEven : Even s) (hsTwo : 2 ≤ s)
    (hprefix : ∀ i : Fin s,
      j.valueUnit i = if Even i.val then
        lemma718IndexPHigh (K := K) R
      else lemma718IndexPLow (K := K) R)
    (hhead : t.order (0 : Fin (m + 1)) = R)
    (hsecond : ∀ hm : 0 < m,
      R - 2 * (ramificationIndex K : Int) + 2 ≤
        t.order ⟨1, by omega⟩) :
    Nonempty (Corollary713Realization j t R) := by
  have hlocalHead : t.corollary713Head.order 0 = R := by
    rw [corollary713Head_order, hhead]
  rcases (@exists_corollary713LocalRealization.{u, v, w}
      K _ _ _ _ _ V _ _
      (t.corollary713HeadSegment).carrier _ _
      q (r.restrict (t.corollary713HeadSegment).carrier
        (t.corollary713HeadSegment).nondegenerate)
      J (t.corollary713HeadSegment).lattice s
      defect hilbert diagonal perfect structural weight unaryBinary jordanOrder
      alpha constructionBase sectionTwoBase classification
      corollary44V corollary44Product
      j t.corollary713Head R hsEven hsTwo hprefix hlocalHead) with
    ⟨E⟩
  let last : Fin s := ⟨s - 1, by omega⟩
  have hlastOdd : ¬ Even last.val := by
    apply Nat.not_even_iff_odd.mpr
    dsimp only [last]
    exact Nat.Even.sub_odd (le_trans (by norm_num) hsTwo) hsEven
      (⟨0, by norm_num⟩ : Odd (1 : Nat))
  have hlastOrder :
      j.order last = R - 2 * (ramificationIndex K : Int) + 1 := by
    change j.toBONG.order last = _
    rw [j.toBONG.order_eq_ordUnit]
    have hprefixLast := hprefix last
    change j.toBONG.valueUnit last = _ at hprefixLast
    rw [hprefixLast, if_neg hlastOdd]
    unfold lemma718IndexPLow
    rw [ordUnit_neg, ordUnit_uniformizerPowerUnit]
  have hlast : ∀ hm : 0 < m,
      j.order ⟨s - 1, by omega⟩ ≤ t.order ⟨1, by omega⟩ := by
    intro hm
    change j.order last ≤ t.order ⟨1, by omega⟩
    rw [hlastOrder]
    have hboundary := hsecond hm
    omega
  rcases (@exists_corollary713Candidate.{u, v, w}
      K _ _ _ _ _ V _ _ W _ _ q r J T s m j R
      constructionProduct sectionTwoProduct t E hsEven hsecond) with
    ⟨N, target, hvalues, htarget⟩
  have hN := @corollary713Candidate_lattice_eq_product.{u, v, w}
    K _ _ _ _ _ V _ _ W _ _ q r J T s m R
    sectionFourV sectionFourW sectionFourProduct N j t E hsTwo hlast target htarget
  subst N
  refine ⟨⟨target, ?_, ?_⟩⟩
  · intro i
    change target.valueUnit ⟨i.val, by omega⟩ =
      corollary713PrefixValues (K := K) R i
    rw [hvalues,
      corollary713OrthogonalBasisData_valueUnit_local t E]
    exact E.valueUnit_prefix i
  · intro i
    change target.valueUnit ⟨s + i.val, by omega⟩ = t.valueUnit i
    rw [hvalues,
      corollary713OrthogonalBasisData_valueUnit_right t E _ (by simp)]
    congr 1
    apply Fin.ext
    simp

end BONG.GoodBONG

end Bong
