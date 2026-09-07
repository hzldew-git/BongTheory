/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Proposition37
import Bong.Bong.Beli2009ClassificationProof
import Bong.Lattice.OMaximalVolume

/-!
# He (2025), Lemmas 4.11 and 4.12: maximal-lattice order profiles

The criteria apply to an arbitrary integral lattice with the specified ambient
quadratic space. Necessity uses invariance of good-BONG orders under integral
isometry. Sufficiency uses the volume criterion for maximal lattices.

`heADCMaximalOrderProfile k tail` writes the displayed sequence as `k` pairs
`0,-2e` followed by the explicitly specified tail. All indices are zero-based.
-/

namespace Bong

open Dyadic Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The order sequence of `k` half-hyperbolic planes followed by a finite tail. -/
noncomputable def heADCMaximalOrderProfile {t : Nat} (k : Nat) (tail : Fin t → Int)
    (i : Fin (t + 2 * k)) : Int :=
  if h : i.val < 2 * k then
    if Even i.val then 0 else -(2 * (ramificationIndex K : Int))
  else tail ⟨i.val - 2 * k, by omega⟩

namespace BONG.GoodBONG

variable {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The BONG form of the maximal-lattice volume criterion. -/
theorem isIsometric_iff_orders_eq_of_isOMaximal {n : Nat}
    (a : GoodBONG q L n) (b : GoodBONG r M n)
    (hL : Lattice.IsIntegral q L) (hM : Lattice.IsOMaximal r M)
    (ambient : q.IsIsometric r) :
    Lattice.IsIsometric q r L M ↔ ∀ i, a.order i = b.order i := by
  constructor
  · rintro ⟨f⟩
    cases n with
    | zero => exact fun i ↦ Fin.elim0 i
    | succ n => exact a.sameOrders_of_latticeIsometry b f
  · intro horders
    apply (Lattice.isIsometric_iff_volumeOrder_eq_of_isOMaximal hL hM ambient).2
    rw [a.toBONG.volumeOrder_eq_sum_order, b.toBONG.volumeOrder_eq_sum_order]
    exact Finset.sum_congr rfl (fun i _ ↦ horders i)

/-- Remark 4.10, as an equality at every coordinate of the full good BONG. -/
theorem heADC2025Remark410 {t : Nat} (b : GoodBONG r M (t + 1))
    (hM : Lattice.IsIntegral r M) (k : Nat) (tail : Fin (t + 1) → Int)
    (htail : ∀ j, b.order j = tail j) (i : Fin ((t + 1) + 2 * k)) :
    (heHu2022Lemma310BONG b hM k).order i = heADCMaximalOrderProfile (K := K) k tail i := by
  unfold heADCMaximalOrderProfile
  split_ifs with hi heven
  · obtain ⟨s, hs⟩ := heven
    have hslt : s < k := by omega
    have hindex : i = (⟨2 * s, by omega⟩ : Fin ((t + 1) + 2 * k)) := by
      apply Fin.ext
      change i.val = 2 * s
      omega
    rw [hindex]
    exact (heHu2022Lemma310HyperbolicOrders b hM k ⟨s, hslt⟩).1
  · obtain ⟨s, hs⟩ := Nat.not_even_iff_odd.mp heven
    have hslt : s < k := by omega
    have hindex : i = (⟨2 * s + 1, by omega⟩ : Fin ((t + 1) + 2 * k)) := by
      apply Fin.ext
      change i.val = 2 * s + 1
      omega
    rw [hindex]
    exact (heHu2022Lemma310HyperbolicOrders b hM k ⟨s, hslt⟩).2
  · let j : Fin (t + 1) := ⟨i.val - 2 * k, by omega⟩
    have hindex : i = (⟨2 * k + j.val, by omega⟩ : Fin ((t + 1) + 2 * k)) := by
      apply Fin.ext
      dsimp only [j]
      omega
    exact (congrArg (heHu2022Lemma310BONG b hM k).order hindex).trans
      ((heHu2022Lemma310TailOrders b hM k j).trans (htail j))

/-- Common proof for every displayed row of Lemmas 4.11 and 4.12. The maximal
tail and its order calculation are discharged in each paper-numbered endpoint. -/
theorem isIsometric_halfHyperbolicExtension_iff_orderProfile {t : Nat}
    (b : GoodBONG r M (t + 1)) (hM : Lattice.IsOMaximal r M)
    (tail : Fin (t + 1) → Int) (htail : ∀ j, b.order j = tail j)
    (k : Nat) (a : GoodBONG q L ((t + 1) + 2 * k))
    (hL : Lattice.IsIntegral q L)
    (ambient : q.IsIsometric (Lattice.halfHyperbolicExtensionForm r k)) :
    Lattice.IsIsometric q (Lattice.halfHyperbolicExtensionForm r k) L
        (Lattice.halfHyperbolicExtensionLattice M k) ↔
      ∀ i, a.order i = heADCMaximalOrderProfile (K := K) k tail i := by
  let c := heHu2022Lemma310BONG b hM.isIntegral k
  have hcriterion := a.isIsometric_iff_orders_eq_of_isOMaximal c hL
    (hM.halfHyperbolicExtension k) ambient
  simpa only [c, heADC2025Remark410 b hM.isIntegral k tail htail] using hcriterion

/-- A row of the maximal-lattice classification. It quantifies over every
integral lattice on the specified ambient space; the only numerical condition
in the conclusion is equality with the displayed order sequence. -/
def HeADCMaximalProfileCriterion {t : Nat} (q : QuadraticSpace K V) (L : Lattice K V)
    (_b : GoodBONG r M (t + 1)) (tail : Fin (t + 1) → Int) (k : Nat) : Prop :=
  ∀ (a : GoodBONG q L ((t + 1) + 2 * k)), Lattice.IsIntegral q L →
    q.IsIsometric (Lattice.halfHyperbolicExtensionForm r k) →
      (Lattice.IsIsometric q (Lattice.halfHyperbolicExtensionForm r k) L
          (Lattice.halfHyperbolicExtensionLattice M k) ↔
        ∀ i, a.order i = heADCMaximalOrderProfile (K := K) k tail i)

/-! ## Even rank -/

/-- He, Lemma 4.11(i), `c=1`: the entire profile alternates `0,-2e`. -/
theorem heADC2025Lemma411iOne (k : Nat) :
    HeADCMaximalProfileCriterion q L (heHuHyperbolicHeadGoodBONG (K := K))
      ![0, -(2 * (ramificationIndex K : Int))] k := by
  apply isIsometric_halfHyperbolicExtension_iff_orderProfile
    (heHuHyperbolicHeadGoodBONG (K := K))
    (heHu2022Proposition37EvenFirstOne (K := K) 0)
  intro j
  fin_cases j <;> simp

/-- He, Lemma 4.11(i), `c=Delta`: the same alternating profile on the
other allowed first-column ambient space. -/
theorem heADC2025Lemma411iDelta (k : Nat) :
    HeADCMaximalProfileCriterion q L (heHuDiscriminantEndpointGoodBONG (K := K) 0)
      ![0, -(2 * (ramificationIndex K : Int))] k := by
  apply isIsometric_halfHyperbolicExtension_iff_orderProfile
    (heHuDiscriminantEndpointGoodBONG (K := K) 0)
    (heHu2022Proposition37EvenFirstDelta (K := K) 0)
  intro j
  fin_cases j <;> simp

/-- He, Lemma 4.11(ii), `c=Delta`: the final pair has orders `1,1-2e`. -/
theorem heADC2025Lemma411iiDelta (k : Nat) :
    HeADCMaximalProfileCriterion q L (heHuDiscriminantEndpointGoodBONG (K := K) 1)
      ![1, 1 - 2 * (ramificationIndex K : Int)] k := by
  apply isIsometric_halfHyperbolicExtension_iff_orderProfile
    (heHuDiscriminantEndpointGoodBONG (K := K) 1)
    (heHu2022Proposition37EvenSecondDelta (K := K) 0)
  intro j
  fin_cases j <;> simp

/-- He, Lemma 4.11(ii), `c=1`. This row starts in rank four, so the
undefined rank-two second-column square case is absent. -/
theorem heADC2025Lemma411iiOne (k : Nat) :
    HeADCMaximalProfileCriterion q L (heHuLemma311EvenSecondOneTail (K := K))
      ![0, -(2 * (ramificationIndex K : Int)), 1,
        1 - 2 * (ramificationIndex K : Int)] k := by
  exact isIsometric_halfHyperbolicExtension_iff_orderProfile _
    (heHu2022Proposition37EvenSecondOne (K := K) 0) _
    heHuLemma311EvenSecondOneTail_order k

/-- He, Lemma 4.11(iii), the unit rows of defect `d<2e` in either column.
Choosing the leading unit as `1` or `c#` gives the two published models. -/
theorem heADC2025Lemma411iiiUnit
    (a c : Kˣ) (d : Int) (ha : IsValuationUnit K (a : K))
    (hc : IsValuationUnit K (c : K)) (hdOdd : Odd d) (hdNonneg : 0 ≤ d)
    (hdLt : d < 2 * (ramificationIndex K : Int))
    (hcDefect : defectOrder (K := K) c = ((d : ℚ) : WithTop ℚ)) (k : Nat) :
    HeADCMaximalProfileCriterion q L
      (heHuUnitDefectTailGoodBONG a c d ha hc hdOdd hdNonneg hdLt hcDefect)
      ![0, 1 - d] k := by
  exact isIsometric_halfHyperbolicExtension_iff_orderProfile _
    (heHu2022Proposition37EvenGeneric a c d ha hc hdOdd hdNonneg hdLt hcDefect 0)
    _ (heHuUnitDefectTailGoodBONG_order a c d ha hc hdOdd hdNonneg hdLt hcDefect) k

/-- He, Lemma 4.11(iii), the unit-uniformizer rows in either column.
Their defect is zero, and the final order is one. -/
theorem heADC2025Lemma411iiiUnitUniformizer
    (a δ : Kˣ) (ha : IsValuationUnit K (a : K)) (hδ : IsValuationUnit K (δ : K))
    (k : Nat) :
    HeADCMaximalProfileCriterion q L (heHuUnitUniformizerPairGoodBONG a δ ha hδ)
      ![0, 1] k := by
  exact isIsometric_halfHyperbolicExtension_iff_orderProfile _
    (heHu2022Proposition37EvenUnitUniformizer a δ ha hδ 0) _
    (heHuUnitUniformizerPairGoodBONG_orders a δ ha hδ) k

/-! ## Odd rank -/

/-- He, Lemma 4.12(i): alternating hyperbolic orders followed by a unit.
The case `k=0` includes rank one. -/
theorem heADC2025Lemma412i (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) (k : Nat) :
    HeADCMaximalProfileCriterion q L (BONG.unaryModelGoodBONG δ) ![0] k := by
  apply isIsometric_halfHyperbolicExtension_iff_orderProfile (BONG.unaryModelGoodBONG δ)
    (heHu2022Proposition37OddFirstUnit δ hδ 0)
  intro j
  fin_cases j
  simp [BONG.unaryModelGoodBONG_order, (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ]

/-- He, Lemma 4.12(ii): the second-column unit row has terminal orders
`0,2-2e,0`. The Beli classification theorem is supplied by its checked proof. -/
theorem heADC2025Lemma412ii
    (δ κ : Kˣ) (hδ : IsValuationUnit K (δ : K)) (hκ : IsValuationUnit K (κ : K))
    (hκDefect : defectOrder (K := K) κ = ((2 * (ramificationIndex K : ℚ) - 1) : WithTop ℚ))
    (k : Nat) :
    letI : GoodBONGClassificationLaws.{u, u, u} K := goodBONGClassificationLawsProved K
    HeADCMaximalProfileCriterion q L (heHuLemma311OddSecondUnitTail δ κ hδ hκ hκDefect)
      ![0, 2 - 2 * (ramificationIndex K : Int), 0] k := by
  letI : GoodBONGClassificationLaws.{u, u, u} K := goodBONGClassificationLawsProved K
  exact isIsometric_halfHyperbolicExtension_iff_orderProfile _
    (heHu2022Proposition37OddSecondUnit δ κ hδ hκ hκDefect 0) _
    (heHuLemma311OddSecondUnitTail_order δ κ hδ hκ hκDefect) k

/-- He, Lemma 4.12(iii), first column: the terminal order is one. -/
theorem heADC2025Lemma412iiiFirst
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) (k : Nat) :
    HeADCMaximalProfileCriterion q L (BONG.unaryModelGoodBONG (δ * uniformizerPowerUnit K 1))
      ![1] k := by
  apply isIsometric_halfHyperbolicExtension_iff_orderProfile
    (BONG.unaryModelGoodBONG (δ * uniformizerPowerUnit K 1))
    (heHu2022Proposition37OddFirstUnitUniformizer δ hδ 0)
  intro j
  fin_cases j
  simp [BONG.unaryModelGoodBONG_order, ordUnit_mul,
    (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ, ordUnit_uniformizerPowerUnit]

/-- He, Lemma 4.12(iii), second column: the terminal orders are `0,-2e,1`. -/
theorem heADC2025Lemma412iiiSecond
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) (k : Nat) :
    HeADCMaximalProfileCriterion q L (heHuLemma311OddSecondUnitUniformizerTail δ hδ)
      ![0, -(2 * (ramificationIndex K : Int)), 1] k := by
  exact isIsometric_halfHyperbolicExtension_iff_orderProfile _
    (heHu2022Proposition37OddSecondUnitUniformizer δ hδ 0) _
    (heHuLemma311OddSecondUnitUniformizerTail_order δ hδ) k

end BONG.GoodBONG

end Bong
