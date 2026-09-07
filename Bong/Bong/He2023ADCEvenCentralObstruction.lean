/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenCentralPrefix

/-!
# He (2025), Lemma 6.6

Both published clauses concern the exact condition-(iii) failure at i=n+1.
The trigger and the failure of its required prefix representation are proved
for arbitrary good BONGs on integral-isometric copies of the named targets.
-/

namespace Bong

open Dyadic

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- Every good BONG on either defined second-column endpoint has the raised profile. -/
theorem heADCEvenSecondTest_isometric_orders (k : Nat) (μ : Kˣ)
    (hdefined : HeHuEvenSecondDefined k μ)
    (hμ : μ = 1 ∨ μ = (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (b : GoodBONG r M (2 * k + 2)) (hM : Lattice.IsIntegral r M)
    (hmodel : Lattice.IsIsometric r (BONG.coefficientDiagonalSpace
      (heADCW2Even k μ hdefined)) M (heADCN2Even k μ hdefined).lattice)
    (i : Fin (2 * k + 2)) :
    b.order i = heADCMaximalOrderProfile (K := K) k
      ![1, 1 - 2 * (ramificationIndex K : Int)] ⟨i.val, by omega⟩ := by
  rcases hμ with hOne | hDelta
  · subst μ
    cases k with
    | zero =>
        rcases hdefined with hpos | hnotSquare
        · omega
        · exact False.elim (hnotSquare ⟨1, by simp⟩)
    | succ k =>
        let b' := b.castLength (by omega : 2 * (k + 1) + 2 = 4 + 2 * k)
        have H := (heADC2025Lemma411iiOnePublished k b' hM
          ⟨(Classical.choice hmodel).toQuadraticSpaceIsometry⟩).mp hmodel
        have hi := H ⟨i.val, by omega⟩
        rw [heADCMaximalOrderProfile_raisedFour] at hi
        simpa only [b', order_castLength] using hi
  · subst μ
    let b' := b.castLength (by omega : 2 * k + 2 = 2 + 2 * k)
    have H := (heADC2025Lemma411iiDeltaPublished k b' hM
      ⟨(Classical.choice hmodel).toQuadraticSpaceIsometry⟩).mp hmodel
    simpa only [b', order_castLength] using H ⟨i.val, by omega⟩

/-- Lemma 6.6's exact failure, uniformly on its two defined target classes. -/
theorem heADC2025Lemma66_endpoint (k : Nat)
    (a : GoodBONG q L (2 * k + 4)) (b : GoodBONG r M (2 * k + 2))
    (hIntegral : Lattice.IsIntegral q L) (hM : Lattice.IsIntegral r M)
    (hhead : ∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hR : 2 - 2 * (ramificationIndex K : Int) ≤ a.order ⟨2 * k + 3, by omega⟩)
    (hAdjacent : ((1 - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
      a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩)
    (μ : Kˣ) (hdefined : HeHuEvenSecondDefined k μ)
    (hμ : μ = 1 ∨ μ = (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (hcase : Even (a.order ⟨2 * k + 2, by omega⟩) ∨
      quadraticDefect K (a.toBONG.signedEvenPrefixProduct (k + 1)) = quadraticDefect K μ)
    (hmodel : Lattice.IsIsometric r (BONG.coefficientDiagonalSpace
      (heADCW2Even k μ hdefined)) M (heADCN2Even k μ hdefined).lattice) :
    a.centralDefectTrigger b (heHuLemma43CentralIndex k le_rfl) ∧
      ¬ DiagonalRepresents (b.prefixValues (2 * k + 2) le_rfl)
        (a.prefixValues (2 * k + 3) (by omega)) := by
  refine ⟨a.heADCEvenCentral_defectTrigger k b hhead
    (heADCEvenSecondTest_isometric_orders k μ hdefined hμ b hM hmodel) hR hAdjacent, ?_⟩
  have hnot := a.heADCEvenCentral_prefix_not_represents_second k hIntegral hhead
    μ hdefined hμ hcase
  have hw : DiagonalRepresents (diagonalUnitCoefficients (heADCW2Even k μ hdefined))
      (diagonalUnitCoefficients b.valueUnit) := by
    apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      (heADCW2Even k μ hdefined) b.valueUnit).mp
    exact ⟨(((Classical.choice hmodel).toQuadraticSpaceIsometry).symm.trans
      b.toBONG.exactDiagonalizationIsometry).toRepresentation⟩
  intro hrep
  have hb : b.prefixValues (2 * k + 2) le_rfl = diagonalUnitCoefficients b.valueUnit := by
    funext i
    rfl
  rw [hb] at hrep
  exact hnot (hw.trans hrep)

/-- He (2025), Lemma 6.6(i), including the binary discriminant target. -/
theorem heADC2025Lemma66i (k : Nat)
    (a : GoodBONG q L (2 * k + 4)) (b : GoodBONG r M (2 * k + 2))
    (hIntegral : Lattice.IsIntegral q L) (hM : Lattice.IsIntegral r M)
    (hhead : ∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hR : 2 - 2 * (ramificationIndex K : Int) ≤ a.order ⟨2 * k + 3, by omega⟩)
    (hAdjacent : ((1 - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
      a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩)
    (hcase : Even (a.order ⟨2 * k + 2, by omega⟩) ∨
      quadraticDefect K (a.toBONG.signedEvenPrefixProduct (k + 1)) =
        (2 * ramificationIndex K : Nat))
    (hmodel : Lattice.IsIsometric r (BONG.coefficientDiagonalSpace (heADCW2Even k
      (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
      (heHuLemma43_evenSecondDefined (K := K) k))) M (heADCN2Even k
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) k)).lattice) :
    a.centralDefectTrigger b (heHuLemma43CentralIndex k le_rfl) ∧
      ¬ DiagonalRepresents (b.prefixValues (2 * k + 2) le_rfl)
        (a.prefixValues (2 * k + 3) (by omega)) := by
  apply a.heADC2025Lemma66_endpoint k b hIntegral hM hhead hR hAdjacent _
    (heHuLemma43_evenSecondDefined (K := K) k) (Or.inr rfl) _ hmodel
  simpa only [(Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminant_defect]
    using hcase

/-- He (2025), Lemma 6.6(ii); the square second-column target starts at rank four. -/
theorem heADC2025Lemma66ii (k : Nat) (hk : 0 < k)
    (a : GoodBONG q L (2 * k + 4)) (b : GoodBONG r M (2 * k + 2))
    (hIntegral : Lattice.IsIntegral q L) (hM : Lattice.IsIntegral r M)
    (hhead : ∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hR : 2 - 2 * (ramificationIndex K : Int) ≤ a.order ⟨2 * k + 3, by omega⟩)
    (hAdjacent : ((1 - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
      a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩)
    (hcase : Even (a.order ⟨2 * k + 2, by omega⟩) ∨
      quadraticDefect K (a.toBONG.signedEvenPrefixProduct (k + 1)) = ⊤)
    (hmodel : Lattice.IsIsometric r (BONG.coefficientDiagonalSpace
      (heADCW2Even k (1 : Kˣ) (Or.inl hk))) M (heADCN2Even k (1 : Kˣ) (Or.inl hk)).lattice) :
    a.centralDefectTrigger b (heHuLemma43CentralIndex k le_rfl) ∧
      ¬ DiagonalRepresents (b.prefixValues (2 * k + 2) le_rfl)
        (a.prefixValues (2 * k + 3) (by omega)) := by
  apply a.heADC2025Lemma66_endpoint k b hIntegral hM hhead hR hAdjacent 1
    (Or.inl hk) (Or.inl rfl) _ hmodel
  simpa only [quadraticDefect_eq_top_of_isSquare (K := K) (show IsSquare (1 : Kˣ) from
    ⟨1, by simp⟩)] using hcase

end BONG.GoodBONG

end Bong
