/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009OmearaConditionI
import Bong.Bong.Beli2009QuadraticRepresentationProof
import Bong.Lattice.OmearaNormGeneratorDefect
import Bong.QuadraticSpace.OrthogonalSumDiagonal

namespace Bong

/-!
# Concrete Beli (2009/2010) representation bridge

This file closes Lemmas 3.6--3.9 against the actual strict Jordan
decompositions.  It identifies O'Meara's boundary embeddings with the exact
good-BONG prefix representations, proves that every active internal alpha
threshold occurs at an adjacent Jordan boundary, and handles the two unary
endpoint cases without an auxiliary law interface.
-/

open Dyadic Module

universe u v w

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

noncomputable def exactDiagonalSpace (b : BONG V q L n) :
    QuadraticSpace K (Fin n → K) :=
  QuadraticSpace.finiteDiagonal b.value b.value_ne_zero

noncomputable def exactDiagonalizationIsometry (b : BONG V q L n) :
    QuadraticSpace.Isometry q b.exactDiagonalSpace where
  toLinearEquiv := b.basis.equivFun
  map_bilin := by
    intro x y
    rw [b.exactDiagonalSpace.bilin_eq_polarization,
      q.bilin_eq_polarization]
    have hquadratic (z : V) :
        b.exactDiagonalSpace.quadratic (b.basis.equivFun z) =
          q.quadratic z := by
      unfold exactDiagonalSpace
      rw [QuadraticSpace.finiteDiagonal_quadratic_apply]
      rw [b.diagonalQuadratic_value_eq]
      simp
    rw [show b.basis.equivFun x + b.basis.equivFun y =
        b.basis.equivFun (x + y) by simp,
      hquadratic, hquadratic, hquadratic]

/-- Full diagonal presentations of BONGs on isometric ambient spaces
represent one another. -/
theorem diagonalRepresents_values_of_isometric
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : BONG V q L n) (b : BONG W r M n)
    (ambient : q.IsIsometric r) :
    DiagonalRepresents b.value a.value := by
  let f : QuadraticSpace.Isometry b.exactDiagonalSpace a.exactDiagonalSpace :=
    b.exactDiagonalizationIsometry.symm |>.trans
      (Classical.choice ambient).symm |>.trans
        a.exactDiagonalizationIsometry
  refine ⟨f.toLinearEquiv.toLinearMap, f.toLinearEquiv.injective, ?_⟩
  intro x
  change diagonalQuadratic a.value (f.toLinearEquiv x) =
    diagonalQuadratic b.value x
  have hquadratic := f.map_quadratic x
  simpa only [exactDiagonalSpace,
      QuadraticSpace.finiteDiagonal_quadratic_apply, diagonalQuadratic]
    using hquadratic

end BONG

namespace QuadraticSpace

open BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

noncomputable def finiteDiagonalOrthogonalSumScaledLineIsometry
    {n : Nat} (c : Fin n → Kˣ) (a : Kˣ) :
    Isometry
      ((finiteDiagonal (diagonalUnitCoefficients c)
          (diagonalUnitCoefficients_ne_zero c)).orthogonalSum
        (scaledLine a))
      (finiteDiagonal (diagonalUnitCoefficients (Fin.snoc c a))
        (diagonalUnitCoefficients_ne_zero (Fin.snoc c a))) := by
  have f :=
    ((Isometry.refl
      (finiteDiagonal (diagonalUnitCoefficients c)
        (diagonalUnitCoefficients_ne_zero c))).orthogonalSum
      (scaledLineDiagonalizationIsometry a)).trans
      (finiteDiagonalOrthogonalSumIsometry c (fun _ : Fin 1 ↦ a))
  simpa only [Fin.append_right_eq_snoc] using f

theorem finiteDiagonal_orthogonalSum_scaledLine_represents_iff
    {m n : Nat} (source : Fin m → Kˣ) (target : Fin n → Kˣ)
    (a : Kˣ) :
    ((finiteDiagonal (diagonalUnitCoefficients target)
        (diagonalUnitCoefficients_ne_zero target)).orthogonalSum
      (scaledLine a)).Represents
        (finiteDiagonal (diagonalUnitCoefficients source)
          (diagonalUnitCoefficients_ne_zero source)) ↔
      DiagonalRepresents (diagonalUnitCoefficients source)
        (diagonalUnitCoefficients (Fin.snoc target a)) := by
  rw [represents_iff_of_isometries
    (Isometry.refl
      (finiteDiagonal (diagonalUnitCoefficients source)
        (diagonalUnitCoefficients_ne_zero source)))
    (finiteDiagonalOrthogonalSumScaledLineIsometry target a)]
  exact finiteDiagonal_represents_iff_diagonalRepresents source
    (Fin.snoc target a)

end QuadraticSpace

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

noncomputable def prefixExactDiagonalSpace
    (a : GoodBONG q L (n + 1)) (k : Nat) (hk : k ≤ n + 1) :
    QuadraticSpace K (Fin k → K) :=
  QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients (a.prefixValueUnits k hk))
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero
      (a.prefixValueUnits k hk))

noncomputable def prefixWitnessDiagonalizationIsometry
    (a : GoodBONG q L (n + 1)) (k : Nat) (hk : k ≤ n + 1) :
    let T := a.toBONG.prefixWitness k hk
    QuadraticSpace.Isometry
      (q.restrict T.carrier T.nondegenerate)
      (a.prefixExactDiagonalSpace k hk) := by
  let T := a.toBONG.prefixWitness k hk
  have f := T.bong.exactDiagonalizationIsometry
  have hvalues : T.bong.value =
      diagonalUnitCoefficients (a.prefixValueUnits k hk) := by
    funext i
    calc
      T.bong.value i =
          a.toBONG.value (T.sourceIndex i) := T.value_eq i
      _ = diagonalUnitCoefficients (a.prefixValueUnits k hk) i := by
        simp [BONG.SegmentWitness.sourceIndex,
          diagonalUnitCoefficients, prefixValueUnits,
          GoodBONG.valueUnit]
  have hspace : T.bong.exactDiagonalSpace =
      a.prefixExactDiagonalSpace k hk := by
    unfold BONG.exactDiagonalSpace prefixExactDiagonalSpace
    congr
  rw [← hspace]
  exact f

noncomputable def prefixWitnessExactDiagonalizationIsometry
    (a : GoodBONG q L (n + 1)) (k : Nat) (hk : k ≤ n + 1)
    (T : a.toBONG.PrefixWitness k hk) :
    QuadraticSpace.Isometry
      (q.restrict T.carrier T.nondegenerate)
      (a.prefixExactDiagonalSpace k hk) := by
  have f := T.bong.exactDiagonalizationIsometry
  have hvalues : T.bong.value =
      diagonalUnitCoefficients (a.prefixValueUnits k hk) := by
    funext i
    calc
      T.bong.value i =
          a.toBONG.value (T.sourceIndex i) := T.value_eq i
      _ = diagonalUnitCoefficients (a.prefixValueUnits k hk) i := by
        simp [BONG.SegmentWitness.sourceIndex,
          diagonalUnitCoefficients, prefixValueUnits,
          GoodBONG.valueUnit]
  have hspace : T.bong.exactDiagonalSpace =
      a.prefixExactDiagonalSpace k hk := by
    unfold BONG.exactDiagonalSpace prefixExactDiagonalSpace
    congr
  rw [← hspace]
  exact f

/-- Any target BONG prefix is represented by the complete source BONG when
the two ambient quadratic spaces are isometric. -/
theorem prefixRepresentsFull_of_isometric
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (ambient : q.IsIsometric r) (k : Nat) (hk : k ≤ n + 1) :
    DiagonalRepresents (b.prefixValues k hk)
      (a.prefixValues (n + 1) (Nat.le_refl _)) := by
  have hprefix : DiagonalRepresents (b.prefixValues k hk) b.toBONG.value := by
    unfold prefixValues
    exact DiagonalRepresents.prefixOfLE b.toBONG.value hk
  have hfull := a.toBONG.diagonalRepresents_values_of_isometric b.toBONG ambient
  have hresult := hprefix.trans hfull
  unfold prefixValues
  exact hresult

end BONG.GoodBONG

namespace BONG.StrictJordanAdaptedAlignment

open GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  {n : Nat} {a : GoodBONG q L (n + 2)}
  {b : GoodBONG r M (n + 2)}

/-- The integral exponent of the actual O'Meara fundamental ideal at a
strict BONG boundary. -/
structure BoundaryFundamentalIdealOrderData
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t) where
  order : Int
  nonnegative : 0 ≤ order
  ideal_eq : (S.sourceJordanSucc h).fundamentalIdeal i =
    Lattice.powerIdeal (K := K) order
  alphaComparison :
    let j := (S.sourceProfileSucc h).boundaryIndex i
    a.alphaValue j = (order : ℚ) ∨
      (2 * (ramificationIndex K : ℚ) < a.alphaValue j ∧
        2 * (ramificationIndex K : ℚ) < (order : ℚ))

noncomputable def boundaryFundamentalIdealOrderData
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t) :
    BoundaryFundamentalIdealOrderData S h i := by
  let P := S.sourceProfileSucc h
  let J := S.sourceJordanSucc h
  by_cases heven : Even (J.boundaryNormOrderSum i)
  · let E := J.evenOrderedFundamentalIdeal i
      (P.boundaryLeftValue i) (P.boundaryRightValue i)
      (S.sourceBoundaryLeftValue_isNormGeneratorValue h i)
      (S.sourceBoundaryRightValue_isNormGeneratorValue h i) heven
    have hE : ((E.order : Int) : ℚ) =
        a.alphaValue (P.boundaryIndex i) := by
      simpa only [E, J, P] using
        S.sourceEvenBoundaryFundamentalOrder_eq_alpha h i heven
    have hnonnegative : 0 ≤ E.order := by
      have hq : (0 : ℚ) ≤ (E.order : ℚ) := by
        rw [hE]
        exact a.zero_le_alphaValue (P.boundaryIndex i)
      exact_mod_cast hq
    exact
      { order := E.order
        nonnegative := hnonnegative
        ideal_eq := by
          have hcarrier : E.carrier = J.fundamentalIdeal i := rfl
          rw [← hcarrier]
          exact E.carrier_eq_powerIdeal
        alphaComparison := by
          left
          exact hE.symm }
  · have hodd : Odd (J.boundaryNormOrderSum i) :=
      Int.not_even_iff_odd.mp heven
    let D := S.sourceOddBoundaryAlphaData h i hodd
    have hD := S.sourceOddBoundaryAlphaData_lemma216 h i hodd
    have hnonnegative : 0 ≤ D.fundamental.order := by
      by_cases hordinary : Even (a.orderGap D.index) ∨
          a.orderGap D.index ≤ 2 * (ramificationIndex K : Int)
      · have hq : (0 : ℚ) ≤ (D.fundamental.order : ℚ) := by
          rw [← hD.1 hordinary]
          exact a.zero_le_alphaValue D.index
        exact_mod_cast hq
      · have hlarge := (hD.2 hordinary).2.2.2.2
        have htwoNonnegative : (0 : ℚ) ≤
            2 * (ramificationIndex K : ℚ) := by positivity
        have hpositive : (0 : ℚ) < (D.fundamental.order : ℚ) :=
          lt_of_le_of_lt htwoNonnegative hlarge
        exact_mod_cast hpositive.le
    exact
      { order := D.fundamental.order
        nonnegative := hnonnegative
        ideal_eq := by
          have hcarrier : D.fundamental.carrier = J.fundamentalIdeal i := rfl
          rw [← hcarrier]
          exact D.fundamental.carrier_eq_powerIdeal
        alphaComparison := by
          by_cases hordinary : Even (a.orderGap D.index) ∨
              a.orderGap D.index ≤ 2 * (ramificationIndex K : Int)
          · left
            exact hD.1 hordinary
          · right
            exact ⟨(hD.2 hordinary).2.2.2.1,
              (hD.2 hordinary).2.2.2.2⟩ }

/-- Proper containment at a boundary is the strict order inequality used in
Beli's Lemma 3.8. -/
theorem boundaryContainment_iff_normalizedWeight_add_fundamentalOrder
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1)
    (z : Fin t) (c : Fin (t + 1)) :
    let J := S.sourceJordanSucc h
    let D := S.boundaryFundamentalIdealOrderData h z
    J.fundamentalIdeal z < J.fourNormOverWeightIdeal c ↔
      2 * (ramificationIndex K : ℚ) <
        ((J.fundamentalWeightOrder c -
          ordUnit K (J.fundamentalNormGenerator c) : Int) : ℚ) +
          (D.order : ℚ) := by
  let J := S.sourceJordanSucc h
  let D := S.boundaryFundamentalIdealOrderData h z
  change J.fundamentalIdeal z < J.fourNormOverWeightIdeal c ↔
    2 * (ramificationIndex K : ℚ) <
      ((J.fundamentalWeightOrder c -
        ordUnit K (J.fundamentalNormGenerator c) : Int) : ℚ) +
        (D.order : ℚ)
  rw [D.ideal_eq]
  unfold Lattice.JordanDecomposition.fourNormOverWeightIdeal
  rw [Lattice.powerIdeal_lt_iff]
  constructor <;> intro horder
  · push_cast
    exact_mod_cast (show 2 * (ramificationIndex K : Int) <
      (J.fundamentalWeightOrder c -
        ordUnit K (J.fundamentalNormGenerator c)) + D.order by omega)
  · have horderInt : 2 * (ramificationIndex K : Int) <
        (J.fundamentalWeightOrder c -
          ordUnit K (J.fundamentalNormGenerator c)) + D.order := by
      exact_mod_cast horder
    omega

/-- Casting the component count does not change the normalized fundamental
weight, independently of the chosen norm generator. -/
theorem normalizedFundamentalWeight_castComponentCount
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (c : Fin (t + 1)) :
    let k : Fin S.componentCount := Fin.cast h.symm c
    (((S.sourceJordanSucc h).fundamentalWeightOrder c -
        ordUnit K ((S.sourceJordanSucc h).fundamentalNormGenerator c) : Int) : ℚ) =
      (S.sourceNormalizedFundamentalWeightOrder k : ℚ) := by
  let J := S.sourceJordanSucc h
  let k : Fin S.componentCount := Fin.cast h.symm c
  have hsource : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice c) (S.sourceFundamentalGenerator k) := by
    unfold J sourceJordanSucc
    rw [Lattice.JordanDecomposition.castComponentCount_fundamentalLattice]
    exact S.sourceFundamentalGenerator_spec k
  have hcanonical := J.fundamentalNormGenerator_spec c
  have horder : ordUnit K (J.fundamentalNormGenerator c) =
      ordUnit K (S.sourceFundamentalGenerator k) := by
    apply (Lattice.principalIdeal_eq_iff_ordUnit_eq
      (J.fundamentalNormGenerator c) (S.sourceFundamentalGenerator k)).mp
    exact hcanonical.2.symm.trans hsource.2
  have hweight : J.fundamentalWeightOrder c =
      S.sourceJordan.fundamentalWeightOrder k := by
    unfold J sourceJordanSucc
    rw [Lattice.JordanDecomposition.castComponentCount_fundamentalWeightOrder]
  change ((J.fundamentalWeightOrder c -
      ordUnit K (J.fundamentalNormGenerator c) : Int) : ℚ) = _
  unfold sourceNormalizedFundamentalWeightOrder
  rw [hweight, horder]

/-- Beli's Lemma 3.8(ii) at a boundary whose right component is non-unary. -/
theorem rightBoundaryAlphaTrigger_iff_conditionIIContainment_of_rank_two
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (z : Fin t)
    (hrank : 2 ≤ S.sourceJordan.componentRank
      (Fin.cast h.symm
        (Lattice.JordanDecomposition.boundaryRightIndex z))) :
    let j := (S.sourceProfileSucc h).boundaryIndex z
    2 * (ramificationIndex K : ℚ) <
        a.alphaValue j + a.alphaValue ⟨j.val + 1, by
          let k : Fin S.componentCount := Fin.cast h.symm
            (Lattice.JordanDecomposition.boundaryRightIndex z)
          have hrankk : 2 ≤ S.sourceJordan.componentRank k := by
            simpa only [k] using hrank
          have hstart :
              ((S.sourceProfileSucc h).boundaryIndex z).val + 1 =
                S.componentStart k := by
            simpa only [k] using
              S.sourceBoundaryIndex_succ_val_eq_componentStart h z
          have hstop := S.componentStop_le k
          unfold componentStop at hstop
          change S.componentStart k + S.sourceJordan.componentRank k ≤
            n + 2 at hstop
          omega⟩ ↔
      (S.sourceJordanSucc h).fundamentalIdeal z <
        (S.sourceJordanSucc h).fourNormOverWeightIdeal
          (Lattice.JordanDecomposition.boundaryRightIndex z) := by
  let J := S.sourceJordanSucc h
  let c : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex z
  let k : Fin S.componentCount := Fin.cast h.symm c
  have hrankk : 2 ≤ S.sourceJordan.componentRank k := by
    simpa only [k, c] using hrank
  let j := (S.sourceProfileSucc h).boundaryIndex z
  let next : Fin (n + 1) := ⟨j.val + 1, by
    have hstart : j.val + 1 = S.componentStart k := by
      simpa only [j, k, c] using
        S.sourceBoundaryIndex_succ_val_eq_componentStart h z
    have hstop := S.componentStop_le k
    unfold componentStop at hstop
    change S.componentStart k + S.sourceJordan.componentRank k ≤ n + 2 at hstop
    omega⟩
  let D := S.boundaryFundamentalIdealOrderData h z
  have hstart : j.val + 1 = S.componentStart k := by
    simpa only [j, k, c] using
      S.sourceBoundaryIndex_succ_val_eq_componentStart h z
  have hnormalized :
      (((J.fundamentalWeightOrder c -
          ordUnit K (J.fundamentalNormGenerator c) : Int) : ℚ)) =
        a.alphaValue next := by
    calc
      (((J.fundamentalWeightOrder c -
          ordUnit K (J.fundamentalNormGenerator c) : Int) : ℚ)) =
          (S.sourceNormalizedFundamentalWeightOrder k : ℚ) := by
        simpa only [J, k, c] using
          S.normalizedFundamentalWeight_castComponentCount h c
      _ = a.alphaValue ⟨S.componentStart k, by
          have hstop := S.componentStop_le k
          unfold componentStop at hstop
          change S.componentStart k + S.sourceJordan.componentRank k ≤
            n + 2 at hstop
          omega⟩ :=
        S.sourceNormalizedFundamentalWeightOrder_eq_alpha_of_rank_two
          k hrankk
      _ = a.alphaValue next := by
        congr 2
        exact hstart.symm
  let R : Beli2009RegularBoundaryThresholdData :=
    { e := ramificationIndex K
      neighboringAlpha := a.alphaValue next
      boundaryAlpha := a.alphaValue j
      normalizedWeightOrder :=
        ((J.fundamentalWeightOrder c -
          ordUnit K (J.fundamentalNormGenerator c) : Int) : ℚ)
      fundamentalOrder := D.order
      containment := J.fundamentalIdeal z < J.fourNormOverWeightIdeal c
      weight_nonnegative := by
        have hle := Lattice.normGeneratorOrder_le_weightIdealOrder
          (J.fundamentalNormGenerator c)
          (J.fundamentalNormGenerator_spec c)
        change (0 : ℚ) ≤
          ((J.fundamentalWeightOrder c -
            ordUnit K (J.fundamentalNormGenerator c) : Int) : ℚ)
        exact_mod_cast sub_nonneg.mpr hle
      weight_eq_neighboringAlpha := hnormalized
      boundaryComparison := D.alphaComparison
      containment_iff_order := by
        simpa only [J, D] using
          S.boundaryContainment_iff_normalizedWeight_add_fundamentalOrder
            h z c }
  have hresult := R.beli2009Lemma38_ii
  simpa only [R, J, c, j, next] using hresult

/-- On a non-unary left component, the normalized fundamental weight is
the alpha immediately preceding the boundary. -/
theorem leftBoundaryNormalizedWeight_eq_precedingAlpha_of_rank_two
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (z : Fin t)
    (hrank : 2 ≤ S.sourceJordan.componentRank
      (Fin.cast h.symm
        (Lattice.JordanDecomposition.boundaryLeftIndex z))) :
    let J := S.sourceJordanSucc h
    let c := Lattice.JordanDecomposition.boundaryLeftIndex z
    let j := (S.sourceProfileSucc h).boundaryIndex z
    (((J.fundamentalWeightOrder c -
        ordUnit K (J.fundamentalNormGenerator c) : Int) : ℚ)) =
      a.alphaValue ⟨j.val - 1, by omega⟩ := by
  let P := S.sourceProfileSucc h
  let J := S.sourceJordanSucc h
  let c : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryLeftIndex z
  let cr : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex z
  let k : Fin S.componentCount := Fin.cast h.symm c
  let kr : Fin S.componentCount := Fin.cast h.symm cr
  let j : Fin (n + 1) := P.boundaryIndex z
  have hrankk : 2 ≤ S.sourceJordan.componentRank k := by
    simpa only [k, c] using hrank
  have hkr : kr.val = k.val + 1 := by
    dsimp only [kr, k, cr, c,
      Lattice.JordanDecomposition.boundaryRightIndex,
      Lattice.JordanDecomposition.boundaryLeftIndex]
    rfl
  have hstopStart : S.componentStop k = S.componentStart kr :=
    S.componentStop_eq_componentStart_of_val_succ k kr hkr
  have hstartRight : j.val + 1 = S.componentStart kr := by
    simpa only [j, P, kr, cr] using
      S.sourceBoundaryIndex_succ_val_eq_componentStart h z
  have hstop : S.componentStop k = j.val + 1 := by omega
  have hjpos : 0 < j.val := by
    have hstopFormula : S.componentStart k +
        S.sourceJordan.componentRank k = S.componentStop k := by
      unfold componentStop
      rfl
    omega
  let previous : Fin (n + 1) := ⟨j.val - 1, by omega⟩
  have hinsideStart : S.componentStart k ≤ j.val - 1 := by
    have hstopFormula : S.componentStart k +
        S.sourceJordan.componentRank k = S.componentStop k := by
      unfold componentStop
      rfl
    omega
  have hinsideNext : (j.val - 1) + 1 < S.componentStop k := by omega
  have hinternal :=
    S.source_component_internal k (j.val - 1) hinsideStart hinsideNext
  let I := S.sourceInternalAlphaData k (j.val - 1)
    hinsideStart hinsideNext
  have hIleft : I.leftIndex = previous.castSucc := by
    apply Fin.ext
    dsimp only [I, GoodBONG.InternalJordanAlphaData.leftIndex,
      sourceInternalAlphaData, GoodBONG.JordanBlockCoordinates.index,
      sourceComponentCoordinates, previous]
    rfl
  have hIalpha : I.alphaIndex = previous := by
    apply Fin.ext
    rfl
  have hweight : (a.order previous.castSucc : ℚ) +
      a.alphaValue previous = (J.fundamentalWeightOrder c : ℚ) := by
    have hleft := hinternal.1
    rw [hIleft, hIalpha] at hleft
    change (a.order previous.castSucc : ℚ) + a.alphaValue previous =
      ((S.sourceFundamentalWeight k).order : ℚ) at hleft
    rw [S.sourceFundamentalWeight_order] at hleft
    unfold J sourceJordanSucc
    rw [Lattice.JordanDecomposition.castComponentCount_fundamentalWeightOrder]
    simpa only [k, c] using hleft
  have hsumInt := (S.sourceComponentCoordinates k).adjacent_order_sum
    (j.val - 1) hinsideStart hinsideNext
  have hleftIndex :
      (S.sourceComponentCoordinates k).index (j.val - 1)
          (by change j.val - 1 < S.componentStop k; omega) =
        previous.castSucc := by
    apply Fin.ext
    rfl
  have hrightIndex :
      (S.sourceComponentCoordinates k).index ((j.val - 1) + 1)
          hinsideNext = j.castSucc := by
    apply Fin.ext
    dsimp only [GoodBONG.JordanBlockCoordinates.index]
    change (j.val - 1) + 1 = j.val
    omega
  rw [hleftIndex, hrightIndex] at hsumInt
  have hscale : J.fundamentalScaleOrder c =
      S.sourceJordan.fundamentalScaleOrder k := by
    unfold J sourceJordanSucc
    rw [Lattice.JordanDecomposition.castComponentCount_fundamentalScaleOrder]
  have hsum : (a.order previous.castSucc : ℚ) +
      (a.order j.castSucc : ℚ) =
        2 * (J.fundamentalScaleOrder c : ℚ) := by
    rw [hscale]
    exact_mod_cast hsumInt
  have hterminal := S.sourceTerminalValue_isNormGeneratorValue h c
  have hnorm := S.sourceNormGenerator_order_eq_fundamental h c
  have horder := P.order_boundaryIndex z hterminal hnorm
  have horderQ : (a.order j.castSucc : ℚ) =
      2 * (J.fundamentalScaleOrder c : ℚ) -
        (ordUnit K (J.fundamentalNormGenerator c) : ℚ) := by
    exact_mod_cast horder
  change (((J.fundamentalWeightOrder c -
      ordUnit K (J.fundamentalNormGenerator c) : Int) : ℚ)) =
    a.alphaValue previous
  push_cast
  linarith

/-- Beli's Lemma 3.8(i) at a boundary whose left component is non-unary. -/
theorem leftBoundaryAlphaTrigger_iff_conditionIIIContainment_of_rank_two
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (z : Fin t)
    (hrank : 2 ≤ S.sourceJordan.componentRank
      (Fin.cast h.symm
        (Lattice.JordanDecomposition.boundaryLeftIndex z))) :
    let j := (S.sourceProfileSucc h).boundaryIndex z
    2 * (ramificationIndex K : ℚ) <
        a.alphaValue ⟨j.val - 1, by omega⟩ + a.alphaValue j ↔
      (S.sourceJordanSucc h).fundamentalIdeal z <
        (S.sourceJordanSucc h).fourNormOverWeightIdeal
          (Lattice.JordanDecomposition.boundaryLeftIndex z) := by
  let J := S.sourceJordanSucc h
  let c : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryLeftIndex z
  let j := (S.sourceProfileSucc h).boundaryIndex z
  let previous : Fin (n + 1) := ⟨j.val - 1, by omega⟩
  let D := S.boundaryFundamentalIdealOrderData h z
  have hnormalized :
      (((J.fundamentalWeightOrder c -
          ordUnit K (J.fundamentalNormGenerator c) : Int) : ℚ)) =
        a.alphaValue previous := by
    simpa only [J, c, j, previous] using
      S.leftBoundaryNormalizedWeight_eq_precedingAlpha_of_rank_two h z hrank
  let R : Beli2009RegularBoundaryThresholdData :=
    { e := ramificationIndex K
      neighboringAlpha := a.alphaValue previous
      boundaryAlpha := a.alphaValue j
      normalizedWeightOrder :=
        ((J.fundamentalWeightOrder c -
          ordUnit K (J.fundamentalNormGenerator c) : Int) : ℚ)
      fundamentalOrder := D.order
      containment := J.fundamentalIdeal z < J.fourNormOverWeightIdeal c
      weight_nonnegative := by
        have hle := Lattice.normGeneratorOrder_le_weightIdealOrder
          (J.fundamentalNormGenerator c)
          (J.fundamentalNormGenerator_spec c)
        change (0 : ℚ) ≤
          ((J.fundamentalWeightOrder c -
            ordUnit K (J.fundamentalNormGenerator c) : Int) : ℚ)
        exact_mod_cast sub_nonneg.mpr hle
      weight_eq_neighboringAlpha := hnormalized
      boundaryComparison := D.alphaComparison
      containment_iff_order := by
        simpa only [J, D] using
          S.boundaryContainment_iff_normalizedWeight_add_fundamentalOrder
            h z c }
  have hresult := R.beli2009Lemma38_i
  simpa only [R, J, c, j, previous] using hresult

/-- Beli's Lemma 3.8(iii) on an internal unary Jordan component. -/
theorem unaryComponentAlphaTrigger_iff_adjacentContainment
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (hnext : k.val + 1 < S.componentCount)
    (hrank : S.sourceJordan.componentRank k = 1) :
    let c : Fin (t + 1) := Fin.cast h k
    let previousBoundary : Fin t := ⟨k.val - 1, by omega⟩
    let nextBoundary : Fin t := ⟨k.val, by omega⟩
    let start := S.componentStart k
    2 * (ramificationIndex K : ℚ) <
        a.alphaValue ⟨start - 1, by
          have hstart := S.componentStart_lt_componentStop k
          have hstop := S.componentStop_le k
          omega⟩ +
        a.alphaValue ⟨start, by
          let knext : Fin S.componentCount := ⟨k.val + 1, hnext⟩
          have hknext : knext.val = k.val + 1 := by
            dsimp only [knext]
          have hstopStart := S.componentStop_eq_componentStart_of_val_succ
            k knext hknext
          have hcomponentStop : S.componentStop k = S.componentStart k + 1 := by
            calc
              S.componentStop k = S.componentStart k +
                  S.sourceJordan.componentRank k := rfl
              _ = S.componentStart k + 1 := by rw [hrank]
          have hnextBound : S.componentStart knext < n + 2 :=
            (S.componentStart_lt_componentStop knext).trans_le
              (S.componentStop_le knext)
          omega⟩ ↔
      (S.sourceJordanSucc h).fundamentalIdeal previousBoundary <
          (S.sourceJordanSucc h).fourNormOverWeightIdeal c ∨
        (S.sourceJordanSucc h).fundamentalIdeal nextBoundary <
          (S.sourceJordanSucc h).fourNormOverWeightIdeal c := by
  let J := S.sourceJordanSucc h
  let c : Fin (t + 1) := Fin.cast h k
  let previousBoundary : Fin t := ⟨k.val - 1, by omega⟩
  let nextBoundary : Fin t := ⟨k.val, by omega⟩
  let start := S.componentStart k
  let left : Fin (n + 1) := ⟨start - 1, by
    have hstart := S.componentStart_lt_componentStop k
    have hstop := S.componentStop_le k
    omega⟩
  let knext : Fin S.componentCount := ⟨k.val + 1, hnext⟩
  have hknext : knext.val = k.val + 1 := rfl
  have hstopStart : S.componentStop k = S.componentStart knext :=
    S.componentStop_eq_componentStart_of_val_succ k knext hknext
  have hcomponentStop : S.componentStop k = start + 1 := by
    calc
      S.componentStop k = S.componentStart k +
          S.sourceJordan.componentRank k := rfl
      _ = start + 1 := by rw [hrank]
  have hstartRight : start < n + 1 := by
    have hnextBound : S.componentStart knext < n + 2 :=
      (S.componentStart_lt_componentStop knext).trans_le
        (S.componentStop_le knext)
    omega
  let right : Fin (n + 1) := ⟨start, hstartRight⟩
  have hpreviousIndex :
      (S.sourceProfileSucc h).boundaryIndex previousBoundary = left := by
    have hs := S.sourceBoundaryIndex_succ_val_eq_componentStart h
      previousBoundary
    have hc : (Fin.cast h.symm
        (Lattice.JordanDecomposition.boundaryRightIndex previousBoundary)) =
        k := by
      apply Fin.ext
      change (k.val - 1) + 1 = k.val
      omega
    rw [hc] at hs
    apply Fin.ext
    dsimp only [left, start]
    omega
  have hnextIndex :
      (S.sourceProfileSucc h).boundaryIndex nextBoundary = right := by
    have hs := S.sourceBoundaryIndex_succ_val_eq_componentStart h nextBoundary
    have hc : (Fin.cast h.symm
        (Lattice.JordanDecomposition.boundaryRightIndex nextBoundary)) =
        knext := by
      apply Fin.ext
      change k.val + 1 = knext.val
      rfl
    rw [hc] at hs
    apply Fin.ext
    dsimp only [right, start]
    omega
  let Dprevious := S.boundaryFundamentalIdealOrderData h previousBoundary
  let Dnext := S.boundaryFundamentalIdealOrderData h nextBoundary
  have hnormalizedCast :
      (((J.fundamentalWeightOrder c -
          ordUnit K (J.fundamentalNormGenerator c) : Int) : ℚ)) =
        (S.sourceNormalizedFundamentalWeightOrder k : ℚ) := by
    have hraw := S.normalizedFundamentalWeight_castComponentCount h c
    have hcast : Fin.cast h.symm c = k := by
      apply Fin.ext
      rfl
    rw [hcast] at hraw
    simpa only [J, c] using hraw
  let hcut : S.componentStart k ≤ n + 2 := by
    exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
      (S.componentStop_le k)
  let T : a.toBONG.TwoBlockSplitWitness (S.componentStart k) hcut :=
    Classical.choice (S.source_hasTwoBlockSplit_componentStart k hk)
  have hformula :=
    S.sourceFundamentalWeightOrder_eq_order_add_min_neighborAlphas_e_of_unary
      k hk T hrank hstartRight
  have hnormalized : (S.sourceNormalizedFundamentalWeightOrder k : ℚ) =
      min (a.alphaValue left)
        (min (a.alphaValue right) (ramificationIndex K : ℚ)) := by
    have hweight : ((S.sourceJordan.fundamentalWeightOrder k : Int) : ℚ) =
        (a.order right.castSucc : ℚ) +
          min (a.alphaValue left)
            (min (a.alphaValue right) (ramificationIndex K : ℚ)) := by
      change ((S.sourceJordan.fundamentalWeightOrder k : Int) : ℚ) = _
        at hformula
      simpa only [start, left, right] using hformula
    have hgenerator : ordUnit K (S.sourceFundamentalGenerator k) =
        a.order right.castSucc := by
      have hraw := S.sourceFundamentalGenerator_order_eq_componentStart k
      rw [hraw]
      congr 2
    unfold sourceNormalizedFundamentalWeightOrder
    push_cast
    rw [hgenerator]
    linarith
  let U : Beli2009UnaryBoundaryThresholdData :=
    { e := ramificationIndex K
      leftAlpha := a.alphaValue left
      rightAlpha := a.alphaValue right
      normalizedWeightOrder :=
        ((J.fundamentalWeightOrder c -
          ordUnit K (J.fundamentalNormGenerator c) : Int) : ℚ)
      previousFundamentalOrder := Dprevious.order
      nextFundamentalOrder := Dnext.order
      previousContainment :=
        J.fundamentalIdeal previousBoundary < J.fourNormOverWeightIdeal c
      nextContainment :=
        J.fundamentalIdeal nextBoundary < J.fourNormOverWeightIdeal c
      weight_nonnegative := by
        have hle := Lattice.normGeneratorOrder_le_weightIdealOrder
          (J.fundamentalNormGenerator c)
          (J.fundamentalNormGenerator_spec c)
        change (0 : ℚ) ≤
          ((J.fundamentalWeightOrder c -
            ordUnit K (J.fundamentalNormGenerator c) : Int) : ℚ)
        exact_mod_cast sub_nonneg.mpr hle
      weight_eq_cappedMinimum := hnormalizedCast.trans hnormalized
      previousComparison := by
        simpa only [hpreviousIndex] using Dprevious.alphaComparison
      nextComparison := by
        simpa only [hnextIndex] using Dnext.alphaComparison
      previousContainment_iff_order := by
        simpa only [J, Dprevious] using
          S.boundaryContainment_iff_normalizedWeight_add_fundamentalOrder
            h previousBoundary c
      nextContainment_iff_order := by
        simpa only [J, Dnext] using
          S.boundaryContainment_iff_normalizedWeight_add_fundamentalOrder
            h nextBoundary c }
  have hresult := U.beli2009Lemma38_iii
  simpa only [U, J, c, previousBoundary, nextBoundary, start, left, right]
    using hresult

/-- Every non-vacuous internal BONG trigger is supplied by one of the two
adjacent O'Meara boundary containments. -/
theorem internalTrigger_has_adjacentContainment
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1)
    (i : Fin (n + 1)) (hi : 0 < i.val)
    (htrigger : 2 * (ramificationIndex K : ℚ) <
      a.alphaValue ⟨i.val - 1, by omega⟩ + a.alphaValue i) :
    (∃ z : Fin t,
      i.val = ((S.sourceProfileSucc h).boundaryIndex z).val + 1 ∧
      (S.sourceJordanSucc h).fundamentalIdeal z <
        (S.sourceJordanSucc h).fourNormOverWeightIdeal
          (Lattice.JordanDecomposition.boundaryRightIndex z)) ∨
    (∃ z : Fin t,
      i.val = ((S.sourceProfileSucc h).boundaryIndex z).val ∧
      (S.sourceJordanSucc h).fundamentalIdeal z <
        (S.sourceJordanSucc h).fourNormOverWeightIdeal
          (Lattice.JordanDecomposition.boundaryLeftIndex z)) := by
  let P := S.sourceProfile
  let global : Fin (n + 2) := i.castSucc
  let coordinate := P.indexEquiv global
  let k : Fin S.componentCount := coordinate.1
  have hindex : i.val = S.componentStart k + coordinate.2.val := by
    have hraw := P.index_val_eq_componentStart_add_local global
    change i.val = S.componentStart k + coordinate.2.val at hraw
    exact hraw
  have hstart : S.componentStart k ≤ i.val := by omega
  have hstop : i.val < S.componentStop k := by
    have hlocal := coordinate.2.isLt
    change coordinate.2.val <
      S.sourceJordan.componentRank coordinate.1 at hlocal
    have hstopFormula : S.componentStop k = S.componentStart k +
        S.sourceJordan.componentRank k := rfl
    dsimp only [k] at hindex hstopFormula ⊢
    omega
  by_cases hfirst : i.val = S.componentStart k
  · have hk : 0 < k.val := by
      by_contra hkzero
      have hkzero' : k.val = 0 := Nat.eq_zero_of_not_pos hkzero
      have hkFirst : k = S.sourceFirstComponent := by
        apply Fin.ext
        exact hkzero'
      have hstartZero : S.componentStart S.sourceFirstComponent = 0 := by
        unfold componentStart
        rw [S.Iio_sourceFirstComponent_eq_empty]
        simp
      rw [hkFirst, hstartZero] at hfirst
      omega
    let previousBoundary : Fin t := ⟨k.val - 1, by
      have hklt := k.isLt
      have hcount : S.componentCount = t + 1 := h
      omega⟩
    have hcPrevious : Fin.cast h.symm
        (Lattice.JordanDecomposition.boundaryRightIndex previousBoundary) = k := by
      apply Fin.ext
      change (k.val - 1) + 1 = k.val
      omega
    have hcPreviousSucc :
        Lattice.JordanDecomposition.boundaryRightIndex previousBoundary =
          Fin.cast h k := by
      apply Fin.ext
      change (k.val - 1) + 1 = k.val
      omega
    have hpreviousIndex :
        ((S.sourceProfileSucc h).boundaryIndex previousBoundary).val + 1 =
          i.val := by
      have hs := S.sourceBoundaryIndex_succ_val_eq_componentStart h
        previousBoundary
      rw [hcPrevious] at hs
      omega
    by_cases hunary : S.sourceJordan.componentRank k = 1
    · have hcomponentStop : S.componentStop k = i.val + 1 := by
        calc
          S.componentStop k = S.componentStart k +
              S.sourceJordan.componentRank k := rfl
          _ = i.val + 1 := by omega
      have hstopStrict : S.componentStop k < n + 2 := by
        have hiBound := i.isLt
        omega
      have hnext := S.source_component_has_successor_of_stop_lt k hstopStrict
      have hunaryTrigger :=
        S.unaryComponentAlphaTrigger_iff_adjacentContainment
          h k hk hnext hunary
      have hadjacent := hunaryTrigger.1 (by
        have hleftIndex :
            (⟨S.componentStart k - 1, by omega⟩ : Fin (n + 1)) =
              ⟨i.val - 1, by omega⟩ := by
          apply Fin.ext
          exact congrArg (fun x : Nat ↦ x - 1) hfirst.symm
        have hrightIndex :
            (⟨S.componentStart k, by omega⟩ : Fin (n + 1)) = i := by
          apply Fin.ext
          exact hfirst.symm
        rw [hleftIndex, hrightIndex]
        exact htrigger)
      rcases hadjacent with hleft | hright
      · exact Or.inl ⟨previousBoundary, hpreviousIndex.symm, by
          simpa only [hcPreviousSucc] using hleft⟩
      · let nextBoundary : Fin t := ⟨k.val, by
          have hcount : S.componentCount = t + 1 := h
          omega⟩
        have hcNext : Fin.cast h.symm
            (Lattice.JordanDecomposition.boundaryLeftIndex nextBoundary) = k := by
          apply Fin.ext
          rfl
        have hcNextSucc :
            Lattice.JordanDecomposition.boundaryLeftIndex nextBoundary =
              Fin.cast h k := by
          apply Fin.ext
          rfl
        have hnextIndex :
            ((S.sourceProfileSucc h).boundaryIndex nextBoundary).val = i.val := by
          let knext : Fin S.componentCount := ⟨k.val + 1, hnext⟩
          have hknext : knext.val = k.val + 1 := by rfl
          have hstopStart := S.componentStop_eq_componentStart_of_val_succ
            k knext hknext
          have hs := S.sourceBoundaryIndex_succ_val_eq_componentStart h
            nextBoundary
          have hcRight : Fin.cast h.symm
              (Lattice.JordanDecomposition.boundaryRightIndex nextBoundary) =
                knext := by
            apply Fin.ext
            rfl
          rw [hcRight] at hs
          omega
        exact Or.inr ⟨nextBoundary, hnextIndex.symm, by
          simpa only [hcNextSucc] using hright⟩
    · have hrank : 2 ≤ S.sourceJordan.componentRank k := by
        have hpos := S.sourceJordan.component_finrank_pos k
        change 0 < S.sourceJordan.componentRank k at hpos
        omega
      have hrankPrevious : 2 ≤ S.sourceJordan.componentRank
          (Fin.cast h.symm
            (Lattice.JordanDecomposition.boundaryRightIndex
              previousBoundary)) := by
        rw [hcPrevious]
        exact hrank
      have hregular :=
        S.rightBoundaryAlphaTrigger_iff_conditionIIContainment_of_rank_two
          h previousBoundary hrankPrevious
      have hcontainment := hregular.1 (by
        have hleftIndex :
            (S.sourceProfileSucc h).boundaryIndex previousBoundary =
              ⟨i.val - 1, by omega⟩ := by
          apply Fin.ext
          change ((S.sourceProfileSucc h).boundaryIndex
            previousBoundary).val = i.val - 1
          omega
        have hrightIndex :
            (⟨((S.sourceProfileSucc h).boundaryIndex
                previousBoundary).val + 1, by omega⟩ : Fin (n + 1)) = i := by
          apply Fin.ext
          exact hpreviousIndex
        have hleftAlpha := congrArg a.alphaValue hleftIndex
        have hrightAlpha := congrArg a.alphaValue hrightIndex
        rw [hleftAlpha, hrightAlpha]
        exact htrigger)
      exact Or.inl ⟨previousBoundary, hpreviousIndex.symm, hcontainment⟩
  · have hstartStrict : S.componentStart k < i.val := by omega
    by_cases hlast : i.val + 1 = S.componentStop k
    · have hrank : 2 ≤ S.sourceJordan.componentRank k := by
        have hstopFormula : S.componentStop k = S.componentStart k +
            S.sourceJordan.componentRank k := rfl
        omega
      have hstopStrict : S.componentStop k < n + 2 := by
        have hiBound := i.isLt
        omega
      have hnext := S.source_component_has_successor_of_stop_lt k hstopStrict
      let nextBoundary : Fin t := ⟨k.val, by
        have hcount : S.componentCount = t + 1 := h
        omega⟩
      have hcNext : Fin.cast h.symm
          (Lattice.JordanDecomposition.boundaryLeftIndex nextBoundary) = k := by
        apply Fin.ext
        rfl
      have hnextIndex :
          ((S.sourceProfileSucc h).boundaryIndex nextBoundary).val = i.val := by
        let knext : Fin S.componentCount := ⟨k.val + 1, hnext⟩
        have hknext : knext.val = k.val + 1 := by rfl
        have hstopStart := S.componentStop_eq_componentStart_of_val_succ
          k knext hknext
        have hs := S.sourceBoundaryIndex_succ_val_eq_componentStart h nextBoundary
        have hcRight : Fin.cast h.symm
            (Lattice.JordanDecomposition.boundaryRightIndex nextBoundary) =
              knext := by
          apply Fin.ext
          rfl
        rw [hcRight] at hs
        omega
      have hregular :=
        S.leftBoundaryAlphaTrigger_iff_conditionIIIContainment_of_rank_two
          h nextBoundary (by
            rw [hcNext]
            exact hrank)
      have hcontainment := hregular.1 (by
        have hrightIndex :
            (S.sourceProfileSucc h).boundaryIndex nextBoundary = i := by
          apply Fin.ext
          exact hnextIndex
        have hleftIndex :
            (⟨((S.sourceProfileSucc h).boundaryIndex
                nextBoundary).val - 1, by omega⟩ : Fin (n + 1)) =
              ⟨i.val - 1, by omega⟩ := by
          apply Fin.ext
          change ((S.sourceProfileSucc h).boundaryIndex
            nextBoundary).val - 1 = i.val - 1
          omega
        have hleftAlpha := congrArg a.alphaValue hleftIndex
        have hrightAlpha := congrArg a.alphaValue hrightIndex
        rw [hleftAlpha, hrightAlpha]
        exact htrigger)
      exact Or.inr ⟨nextBoundary, hnextIndex.symm, hcontainment⟩
    · have hinside : i.val + 1 < S.componentStop k := by omega
      have houterStart : S.componentStart k ≤ i.val - 1 := by omega
      have houterFit : (i.val - 1) + 2 < S.componentStop k := by omega
      have houter := S.source_order_add_two_eq k (i.val - 1)
        houterStart houterFit
      have hp6 := a.alpha_p6
        (⟨i.val - 1, by omega⟩ : Fin (n + 1)) (by
          change (i.val - 1) + 1 < n + 1
          omega) (by
          have hleftIndex :
              (⟨i.val - 1, by omega⟩ : Fin (n + 1)).castSucc =
                (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
            apply Fin.ext
            rfl
          have hrightIndex :
              (⟨(i.val - 1) + 1, by omega⟩ : Fin (n + 1)).succ =
                (⟨i.val + 1, by omega⟩ : Fin (n + 2)) := by
            apply Fin.ext
            change (i.val - 1 + 1) + 1 = i.val + 1
            omega
          rw [hleftIndex, hrightIndex]
          have hsum : i.val - 1 + 2 = i.val + 1 := by omega
          simpa only [hsum] using houter)
      have hiIndex : (⟨(i.val - 1) + 1, by omega⟩ : Fin (n + 1)) = i := by
        apply Fin.ext
        change i.val - 1 + 1 = i.val
        omega
      rw [hiIndex] at hp6
      linarith

/-- Every nonfirst Jordan component begins at a positive BONG coordinate. -/
theorem componentStart_pos_of_val_pos
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val) :
    0 < S.componentStart k := by
  unfold componentStart
  let previous : Fin S.componentCount := ⟨k.val - 1, by omega⟩
  have hp : previous ∈ Finset.Iio k := by
    simp only [Finset.mem_Iio]
    change k.val - 1 < k.val
    omega
  exact (S.sourceJordan.component_finrank_pos previous).trans_le
    (Finset.single_le_sum
      (s := Finset.Iio k)
      (f := fun z ↦ S.sourceJordan.componentRank z)
      (fun _ _ ↦ Nat.zero_le _) hp)

theorem normalizedFundamentalWeight_nonnegative
    {X : Type v} [AddCommGroup X] [Module K X]
    {p : QuadraticSpace K X} {N : Lattice K X} {d : Nat}
    (J : Lattice.JordanDecomposition p N d) (c : Fin d)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue p (J.fundamentalLattice c) A) :
    0 ≤ J.fundamentalWeightOrder c - ordUnit K A := by
  apply sub_nonneg.mpr
  simpa only [Lattice.JordanDecomposition.fundamentalWeightOrder] using
    Lattice.normGeneratorOrder_le_weightIdealOrder A hA

theorem normalizedFundamentalWeight_le_ramificationIndex
    {X : Type v} [AddCommGroup X] [Module K X]
    {p : QuadraticSpace K X} {N : Lattice K X} {d : Nat}
    (J : Lattice.JordanDecomposition p N d) (c : Fin d)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue p (J.fundamentalLattice c) A) :
    J.fundamentalWeightOrder c - ordUnit K A ≤
      (ramificationIndex K : Int) := by
  let C := J.fundamentalLattice c
  have hweight : Lattice.weightIdealOrder p C ≤
      Lattice.canonicalTwoScaleOrder p C := by
    rw [Lattice.weightIdealOrder_eq_canonicalWeightOrder A hA]
    exact Lattice.canonicalWeightOrder_le_twoScaleOrder hA
  have hscaleIdeal := Lattice.normIdeal_le_scaleIdeal p C
  have hscale : Lattice.canonicalScaleOrder p C ≤ ordUnit K A := by
    rw [hA.2, Lattice.principalIdeal_eq_powerIdeal,
      Lattice.scaleIdeal_eq_powerIdeal_canonicalScaleOrder hA,
      Lattice.powerIdeal_le_iff] at hscaleIdeal
    exact hscaleIdeal
  change Lattice.weightIdealOrder p C - ordUnit K A ≤ _
  unfold Lattice.canonicalTwoScaleOrder at hweight
  omega

theorem prefixProducts_congruent_mod_fundamentalIdeal_of_omeara9328ConditionI
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1)
    (hcondition : (S.sourceJordanSucc h).Omeara9328ConditionI
      (S.targetJordanSucc h)) (i : Fin t) :
    GoodBONG.UnitsCongruentModulo
      (b.prefixProduct (((S.sourceProfileSucc h).boundaryIndex i).val + 1))
      (a.prefixProduct (((S.sourceProfileSucc h).boundaryIndex i).val + 1))
      ((S.sourceJordanSucc h).fundamentalIdeal i) := by
  let P := S.sourceProfileSucc h
  let J := S.sourceJordanSucc h
  let j : Fin (n + 1) := P.boundaryIndex i
  have htargetClass :=
    S.unitSquareClass_targetPrefixProduct_eq_prefixDeterminantUnit h i
  rw [← S.sourceBoundaryIndex_eq_targetBoundaryIndex h i] at htargetClass
  have hsourceClass :=
    S.unitSquareClass_sourcePrefixProduct_eq_prefixDeterminantUnit h i
  apply GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
    ((S.targetJordanSucc h).prefixDeterminantUnit i)
    (b.prefixProduct (j.val + 1))
    ((S.sourceJordanSucc h).prefixDeterminantUnit i)
    (a.prefixProduct (j.val + 1)) (J.fundamentalIdeal i)
  · simpa only [P, J, j] using htargetClass.symm
  · simpa only [P, J, j] using hsourceClass.symm
  · exact hcondition i

/-- The two Hilbert-symbol identities in Beli's Lemma 3.6, specialized to
an actual Jordan boundary and to any second norm generator of the component
whose threshold is active. -/
theorem boundaryHilbertConditions
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1)
    (horders : a.SameOrders b)
    (hcondition : (S.sourceJordanSucc h).Omeara9328ConditionI
      (S.targetJordanSucc h))
    (z : Fin t) (c : Fin (t + 1)) (B : Kˣ)
    (hB : Lattice.IsNormGeneratorValue q
      ((S.sourceJordanSucc h).fundamentalLattice c) B)
    (htrigger : (S.sourceJordanSucc h).fundamentalIdeal z <
      (S.sourceJordanSucc h).fourNormOverWeightIdeal c) :
    let j := (S.sourceProfileSucc h).boundaryIndex z
    let A := (S.sourceJordanSucc h).fundamentalNormGenerator c
    let detTarget := b.prefixProduct (j.val + 1)
    let detSource := a.prefixProduct (j.val + 1)
    hilbertSymbol K (A * B) (detTarget * detSource) = 1 ∧
      hilbertSymbol K ((A * detTarget * detSource) * B)
        (detSource * detTarget) = 1 := by
  let P := S.sourceProfileSucc h
  let J := S.sourceJordanSucc h
  let j : Fin (n + 1) := P.boundaryIndex z
  let A : Kˣ := J.fundamentalNormGenerator c
  let detTarget : Kˣ := b.prefixProduct (j.val + 1)
  let detSource : Kˣ := a.prefixProduct (j.val + 1)
  let D := S.boundaryFundamentalIdealOrderData h z
  let weightOrder : Int := J.fundamentalWeightOrder c - ordUnit K A
  have hA : Lattice.IsNormGeneratorValue q (J.fundamentalLattice c) A :=
    J.fundamentalNormGenerator_spec c
  have hweightNonnegative : 0 ≤ weightOrder := by
    exact normalizedFundamentalWeight_nonnegative J c A hA
  have hweightLeE : weightOrder ≤ (ramificationIndex K : Int) := by
    exact normalizedFundamentalWeight_le_ramificationIndex J c A hA
  have hBOrder : ordUnit K B = ordUnit K A := by
    apply (Lattice.principalIdeal_eq_iff_ordUnit_eq B A).mp
    exact hB.2.symm.trans hA.2
  have hnegBOrder : ordUnit K (-B) = ordUnit K A := by
    simpa only [ordUnit_neg] using hBOrder
  have hweightDefectOrder :
      ((((weightOrder : Int) : ℚ) : WithTop ℚ) ≤
        GoodBONG.defectOrder (K := K) (A * B)) := by
    have hraw :=
      Lattice.weightIdealOrder_sub_ordUnit_le_defectOrder_neg_div_of_normGenerators
        A (-B) hA hB.neg hnegBOrder
    have hproduct : (-(A / (-B))) * B ^ 2 = A * B := by
      apply Units.ext
      simp only [Units.val_neg, Units.val_div_eq_div_val,
        Units.val_mul, Units.val_pow_eq_pow_val]
      field_simp [Units.ne_zero A, Units.ne_zero B]
    have hdefectEq : GoodBONG.defectOrder (K := K) (-(A / (-B))) =
        GoodBONG.defectOrder (K := K) (A * B) := by
      rw [← hproduct]
      exact (GoodBONG.defectOrder_mul_square (-(A / (-B))) B).symm
    simpa only [J, A, weightOrder,
      Lattice.JordanDecomposition.fundamentalWeightOrder,
      hdefectEq] using hraw
  have hweightDefect : ((weightOrder.toNat : Nat) : ℕ∞) ≤
      quadraticDefect K (A * B) := by
    apply (GoodBONG.natCast_le_defectOrder_iff (A * B) weightOrder.toNat).1
    have hcast : ((((weightOrder.toNat : Nat) : ℚ) : WithTop ℚ)) =
        ((((weightOrder : Int) : ℚ) : WithTop ℚ)) := by
      norm_cast
      exact_mod_cast Int.toNat_of_nonneg hweightNonnegative
    rw [hcast]
    exact hweightDefectOrder
  have hdetOrder : ordUnit K detTarget = ordUnit K detSource := by
    exact (a.ordUnit_prefixProduct_eq_of_sameOrders b horders
      (j.val + 1) (by omega)).symm
  have hcongruent : GoodBONG.UnitsCongruentModulo detTarget detSource
      (Lattice.powerIdeal (K := K) D.order) := by
    rw [← D.ideal_eq]
    exact S.prefixProducts_congruent_mod_fundamentalIdeal_of_omeara9328ConditionI
      h hcondition z
  have hfundamentalDefectOrder :
      ((((D.order : Int) : ℚ) : WithTop ℚ) ≤
        GoodBONG.defectOrder (K := K) (detTarget * detSource)) :=
    GoodBONG.intCast_le_defectOrder_mul_of_unitsCongruentModulo_powerIdeal
      detTarget detSource D.order D.nonnegative hdetOrder hcongruent
  have hfundamentalDefect : ((D.order.toNat : Nat) : ℕ∞) ≤
      quadraticDefect K (detTarget * detSource) := by
    apply (GoodBONG.natCast_le_defectOrder_iff
      (detTarget * detSource) D.order.toNat).1
    have hcast : ((((D.order.toNat : Nat) : ℚ) : WithTop ℚ)) =
        ((((D.order : Int) : ℚ) : WithTop ℚ)) := by
      norm_cast
      exact_mod_cast Int.toNat_of_nonneg D.nonnegative
    rw [hcast]
    exact hfundamentalDefectOrder
  have htriggerOrder :
      2 * (ramificationIndex K : Int) - weightOrder < D.order := by
    have ht := htrigger
    unfold Lattice.JordanDecomposition.fourNormOverWeightIdeal at ht
    rw [D.ideal_eq, Lattice.powerIdeal_lt_iff] at ht
    change 2 * (ramificationIndex K : Int) + ordUnit K A -
      J.fundamentalWeightOrder c < D.order at ht
    omega
  have hthresholdInt : 2 * (ramificationIndex K : Int) <
      weightOrder + D.order := by omega
  have hweightLtFundamental : weightOrder < D.order := by omega
  have hthresholdNat : 2 * ramificationIndex K <
      weightOrder.toNat + D.order.toNat := by
    have hw := Int.toNat_of_nonneg hweightNonnegative
    have hf := Int.toNat_of_nonneg D.nonnegative
    omega
  have hthreshold : ((2 * ramificationIndex K : Nat) : ℕ∞) <
      (weightOrder.toNat : ℕ∞) + (D.order.toNat : ℕ∞) := by
    exact_mod_cast hthresholdNat
  have hweightLtFundamentalNat : weightOrder.toNat < D.order.toNat := by
    have hw := Int.toNat_of_nonneg hweightNonnegative
    have hf := Int.toNat_of_nonneg D.nonnegative
    omega
  have hweightLtFundamentalENat : (weightOrder.toNat : ℕ∞) <
      (D.order.toNat : ℕ∞) := by
    exact_mod_cast hweightLtFundamentalNat
  have hfirst : hilbertSymbol K (A * B)
      (detTarget * detSource) = 1 := by
    apply hilbertSymbol_eq_one_of_defect_add_gt_two_mul_e K
    exact hthreshold.trans_le
      (add_le_add hweightDefect hfundamentalDefect)
  have htwistedDefect : (weightOrder.toNat : ℕ∞) ≤
      quadraticDefect K ((A * B) * (detTarget * detSource)) := by
    apply (le_min hweightDefect ?_).trans
      (quadraticDefect_mul_ge_min K (A * B) (detTarget * detSource))
    exact hweightLtFundamentalENat.le.trans hfundamentalDefect
  have hsecond : hilbertSymbol K
      ((A * detTarget * detSource) * B) (detSource * detTarget) = 1 := by
    have hdefect : ((2 * ramificationIndex K : Nat) : ℕ∞) <
        quadraticDefect K ((A * B) * (detTarget * detSource)) +
          quadraticDefect K (detTarget * detSource) :=
      hthreshold.trans_le
        (add_le_add htwistedDefect hfundamentalDefect)
    have hh := hilbertSymbol_eq_one_of_defect_add_gt_two_mul_e K hdefect
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hh
  exact ⟨hfirst, hsecond⟩

/-- Exact-diagonal form of Beli's Lemma 3.6 at an actual Jordan boundary.
The first equivalence replaces the canonical fundamental generator by any
second generator of the active component; the second reverses source and
target prefixes. -/
theorem boundaryDiagonalRepresentationSwitch
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1)
    (horders : a.SameOrders b)
    (hcondition : (S.sourceJordanSucc h).Omeara9328ConditionI
      (S.targetJordanSucc h))
    (z : Fin t) (c : Fin (t + 1)) (B : Kˣ)
    (hB : Lattice.IsNormGeneratorValue q
      ((S.sourceJordanSucc h).fundamentalLattice c) B)
    (htrigger : (S.sourceJordanSucc h).fundamentalIdeal z <
      (S.sourceJordanSucc h).fourNormOverWeightIdeal c) :
    let j := (S.sourceProfileSucc h).boundaryIndex z
    let A := (S.sourceJordanSucc h).fundamentalNormGenerator c
    let targetUnits := b.prefixValueUnits (j.val + 1) (by omega)
    let sourceUnits := a.prefixValueUnits (j.val + 1) (by omega)
    (DiagonalRepresents (diagonalUnitCoefficients sourceUnits)
        (diagonalUnitCoefficients (Fin.snoc targetUnits A)) ↔
      DiagonalRepresents (diagonalUnitCoefficients sourceUnits)
        (diagonalUnitCoefficients (Fin.snoc targetUnits B))) ∧
    (DiagonalRepresents (diagonalUnitCoefficients sourceUnits)
        (diagonalUnitCoefficients (Fin.snoc targetUnits A)) ↔
      DiagonalRepresents (diagonalUnitCoefficients targetUnits)
        (diagonalUnitCoefficients (Fin.snoc sourceUnits B))) := by
  let j := (S.sourceProfileSucc h).boundaryIndex z
  let A := (S.sourceJordanSucc h).fundamentalNormGenerator c
  let targetUnits := b.prefixValueUnits (j.val + 1) (by omega)
  let sourceUnits := a.prefixValueUnits (j.val + 1) (by omega)
  have hhilbert := S.boundaryHilbertConditions h horders hcondition
    z c B hB htrigger
  have hfirstHilbert : hilbertSymbol K (A * B)
      (diagonalUnitDeterminant targetUnits *
        diagonalUnitDeterminant sourceUnits) = 1 := by
    simpa only [j, A, targetUnits, sourceUnits,
      GoodBONG.diagonalUnitDeterminant_prefixValueUnits] using hhilbert.1
  have hsecondHilbert : hilbertSymbol K
      ((A * diagonalUnitDeterminant targetUnits *
          diagonalUnitDeterminant sourceUnits) * B)
        (diagonalUnitDeterminant sourceUnits *
          diagonalUnitDeterminant targetUnits) = 1 := by
    simpa only [j, A, targetUnits, sourceUnits,
      GoodBONG.diagonalUnitDeterminant_prefixValueUnits] using hhilbert.2
  have hforward := beli2009Lemma35iii_diagonal
    targetUnits sourceUnits A B hfirstHilbert
  have hswap := beli2009Lemma35ii_diagonal targetUnits sourceUnits A
  have hreplace := beli2009Lemma35iii_diagonal sourceUnits targetUnits
    (A * diagonalUnitDeterminant targetUnits *
      diagonalUnitDeterminant sourceUnits) B hsecondHilbert
  exact ⟨hforward, hswap.trans hreplace⟩

/-- The signed terminal generator is the negative of the last BONG value,
up to a square. -/
theorem boundaryLeftValue_mul_neg_valueUnit_isSquare
    {d : Nat} {J : Lattice.JordanDecomposition q L (d + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin d) :
    IsSquare (P.boundaryLeftValue z *
      (-a.valueUnit (P.boundaryIndex z).castSucc)) := by
  let li : Fin (d + 1) :=
    Lattice.JordanDecomposition.boundaryLeftIndex z
  let last : Fin (J.toOrthogonalDecomposition.componentRank li) :=
    ⟨J.toOrthogonalDecomposition.componentRank li - 1, by
      exact Nat.sub_lt (J.component_finrank_pos li) Nat.zero_lt_one⟩
  let global : Fin (n + 2) := P.indexEquiv.symm ⟨li, last⟩
  have hglobal : (P.boundaryIndex z).castSucc = global := by
    apply Fin.ext
    rfl
  let exponent : Int := ordUnit K (J.normGenerator li) -
    ordUnit K (J.scaleGenerator li)
  let squareRoot : Kˣ := uniformizerPowerUnit K exponent * a.valueUnit global
  refine ⟨squareRoot, ?_⟩
  have hpower : uniformizerPowerUnit K (2 * exponent) =
      uniformizerPowerUnit K exponent ^ 2 := by
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
    congr 1
    omega
  have hterminalValue : P.terminalValue li =
      uniformizerPowerUnit K
          (2 * ordUnit K (J.normGenerator li) -
            2 * ordUnit K (J.scaleGenerator li)) *
        a.valueUnit global := by
    unfold JordanOrderProfileWitness.terminalValue
    congr 1
  unfold JordanOrderProfileWitness.boundaryLeftValue
  rw [show Lattice.JordanDecomposition.boundaryLeftIndex z = li by rfl,
    hglobal, hterminalValue]
  have hexponent : 2 * ordUnit K (J.normGenerator li) -
      2 * ordUnit K (J.scaleGenerator li) = 2 * exponent := by
    dsimp only [exponent]
    omega
  rw [hexponent, hpower]
  dsimp only [squareRoot, pow_two]
  rw [neg_mul_neg]
  rw [pow_two]
  ac_rfl

/-- After replacing the signed terminal line by its exact square-class
representative, Lemma 3.5(i) removes the resulting hyperbolic pair. -/
theorem boundaryLeftDiagonal_iff_prefixRepresentation
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (z : Fin t) :
    let j := (S.sourceProfileSucc h).boundaryIndex z
    let B := (S.targetProfileSucc h).boundaryLeftValue z
    DiagonalRepresents
        (diagonalUnitCoefficients
          (a.prefixValueUnits (j.val + 1) (by omega)))
        (diagonalUnitCoefficients
          (Fin.snoc (b.prefixValueUnits (j.val + 1) (by omega)) B)) ↔
      DiagonalRepresents
        (b.prefixValues j.val (by omega))
        (a.prefixValues (j.val + 1) (by omega)) := by
  let j := (S.sourceProfileSucc h).boundaryIndex z
  let jt := (S.targetProfileSucc h).boundaryIndex z
  let B := (S.targetProfileSucc h).boundaryLeftValue z
  let sourceUnits := a.prefixValueUnits (j.val + 1) (by omega)
  let targetUnits := b.prefixValueUnits (j.val + 1) (by omega)
  let shorterTargetUnits := b.prefixValueUnits j.val (by omega)
  let terminal : Kˣ := b.valueUnit j.castSucc
  have hindex : j = jt := S.sourceBoundaryIndex_eq_targetBoundaryIndex h z
  have hsquareRaw :=
    boundaryLeftValue_mul_neg_valueUnit_isSquare
      (S.targetProfileSucc h) z
  have hsquare : IsSquare (B * (-terminal)) := by
    simpa only [B, terminal, jt, hindex] using hsquareRaw
  have hreplace := diagonalRepresents_snoc_iff_of_isSquare_mul
    sourceUnits targetUnits B (-terminal) hsquare
  have hprefix : targetUnits = Fin.snoc shorterTargetUnits terminal := by
    have hraw := b.prefixValueUnits_succ_eq_snoc j.val (by omega)
    change targetUnits = Fin.snoc shorterTargetUnits
      (b.valueUnit ⟨j.val, by omega⟩) at hraw
    calc
      targetUnits = Fin.snoc shorterTargetUnits
          (b.valueUnit ⟨j.val, by omega⟩) := hraw
      _ = Fin.snoc shorterTargetUnits terminal := by
        congr 1
  rw [hprefix] at hreplace
  have hhyperbolic := beli2009Lemma35i_diagonal
    sourceUnits shorterTargetUnits terminal
  have hresult := hreplace.trans hhyperbolic.symm
  change DiagonalRepresents (diagonalUnitCoefficients sourceUnits)
      (diagonalUnitCoefficients (Fin.snoc targetUnits B)) ↔
    DiagonalRepresents (diagonalUnitCoefficients shorterTargetUnits)
      (diagonalUnitCoefficients sourceUnits)
  rw [hprefix]
  exact hresult

noncomputable def castTwoBlockSplitCut
    {X : Type v} [AddCommGroup X] [Module K X]
    {f : QuadraticSpace K X} {N : Lattice K X}
    {d cut cut' : Nat} {c : BONG X f N d}
    {hcut : cut ≤ d} {hcut' : cut' ≤ d}
    (T : c.TwoBlockSplitWitness cut hcut) (hEq : cut = cut') :
    c.TwoBlockSplitWitness cut' hcut' := by
  subst cut'
  exact T

noncomputable def sourceSplitLeftLatticeIsometryAtCut
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (cut : Nat) (hcut : cut ≤ n + 2)
    (hEq : cut = S.componentStart k)
    (T : a.toBONG.TwoBlockSplitWitness cut hcut) :
    let D := S.sourceJordan.toOrthogonalDecomposition
    Lattice.Isometry
      (q.restrict T.left.carrier T.left.nondegenerate)
      (D.prefixQuadraticSublattice k.val).space
      T.left.lattice (D.prefixQuadraticSublattice k.val).lattice := by
  subst cut
  exact S.sourceSplitLeftLatticeIsometry k hk T

noncomputable def sourcePrefixExactDiagonalIsometry
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t) :
    let j := (S.sourceProfileSucc h).boundaryIndex i
    QuadraticSpace.Isometry
      (a.prefixExactDiagonalSpace (j.val + 1) (by omega))
      ((S.sourceJordanSucc h).prefixSpace (i.val + 1)) := by
  let j := (S.sourceProfileSucc h).boundaryIndex i
  let k : Fin S.componentCount := Fin.cast h.symm
    (Lattice.JordanDecomposition.boundaryRightIndex i)
  have hk : 0 < k.val := by
    simp [k, Lattice.JordanDecomposition.boundaryRightIndex]
  let hraw : S.componentStart k ≤ n + 2 := by
    exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
      (S.componentStop_le k)
  let Traw : a.toBONG.TwoBlockSplitWitness (S.componentStart k) hraw :=
    Classical.choice (S.source_hasTwoBlockSplit_componentStart k hk)
  have hstart : j.val + 1 = S.componentStart k := by
    simpa only [j, k] using
      S.sourceBoundaryIndex_succ_val_eq_componentStart h i
  let hcut : j.val + 1 ≤ n + 2 := by omega
  let T : a.toBONG.TwoBlockSplitWitness (j.val + 1) hcut :=
    castTwoBlockSplitCut Traw hstart.symm
  let P := T.leftPrefixWitness
  let f : QuadraticSpace.Isometry
      (a.prefixExactDiagonalSpace (j.val + 1) hcut)
      ((S.sourceJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        k.val).space) :=
    (GoodBONG.prefixWitnessExactDiagonalizationIsometry
      a (j.val + 1) hcut P).symm.trans
      (S.sourceSplitLeftLatticeIsometryAtCut
        k hk (j.val + 1) hcut hstart T).toQuadraticSpaceIsometry
  have hkval : k.val = i.val + 1 := by
    simp [k, Lattice.JordanDecomposition.boundaryRightIndex]
  dsimp only
  unfold sourceJordanSucc Lattice.JordanDecomposition.prefixSpace
  rw [Lattice.JordanDecomposition.castComponentCount_prefixQuadraticSublattice]
  rw [← hkval]
  exact f

noncomputable def targetPrefixExactDiagonalIsometry
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t) :
    let j := (S.sourceProfileSucc h).boundaryIndex i
    QuadraticSpace.Isometry
      (b.prefixExactDiagonalSpace (j.val + 1) (by omega))
      ((S.targetJordanSucc h).prefixSpace (i.val + 1)) := by
  let j := (S.sourceProfileSucc h).boundaryIndex i
  let k : Fin S.componentCount := Fin.cast h.symm
    (Lattice.JordanDecomposition.boundaryRightIndex i)
  have hk : 0 < k.val := by
    simp [k, Lattice.JordanDecomposition.boundaryRightIndex]
  let hraw : S.symm.componentStart k ≤ n + 2 := by
    exact le_trans
      (Nat.le_of_lt (S.symm.componentStart_lt_componentStop k))
      (S.symm.componentStop_le k)
  let Traw : b.toBONG.TwoBlockSplitWitness (S.symm.componentStart k) hraw :=
    Classical.choice (S.symm.source_hasTwoBlockSplit_componentStart k hk)
  have hstart : j.val + 1 = S.symm.componentStart k := by
    have ht := S.targetBoundaryIndex_succ_val_eq_componentStart h i
    have hj := S.sourceBoundaryIndex_eq_targetBoundaryIndex h i
    rw [← hj] at ht
    change j.val + 1 = S.targetComponentStart k
    simpa only [j, k] using ht
  let hcut : j.val + 1 ≤ n + 2 := by omega
  let T : b.toBONG.TwoBlockSplitWitness (j.val + 1) hcut :=
    castTwoBlockSplitCut Traw hstart.symm
  let P := T.leftPrefixWitness
  let f : QuadraticSpace.Isometry
      (b.prefixExactDiagonalSpace (j.val + 1) hcut)
      ((S.targetJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        k.val).space) :=
    (GoodBONG.prefixWitnessExactDiagonalizationIsometry
      b (j.val + 1) hcut P).symm.trans
      (S.symm.sourceSplitLeftLatticeIsometryAtCut
        k hk (j.val + 1) hcut hstart T).toQuadraticSpaceIsometry
  have hkval : k.val = i.val + 1 := by
    simp [k, Lattice.JordanDecomposition.boundaryRightIndex]
  dsimp only
  unfold targetJordanSucc Lattice.JordanDecomposition.prefixSpace
  rw [Lattice.JordanDecomposition.castComponentCount_prefixQuadraticSublattice]
  rw [← hkval]
  exact f

/-- A boundary representation in O'Meara's actual Jordan prefixes is the
corresponding exact diagonal-prefix representation. -/
theorem omearaBoundaryEmbedding_iff_diagonal
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1)
    (z : Fin t) (A : Kˣ) :
    let j := (S.sourceProfileSucc h).boundaryIndex z
    Lattice.QuadraticSublattice.EmbedsIntoOrthogonalSum
        ((S.sourceJordanSucc h).toOrthogonalDecomposition.prefixQuadraticSublattice
          (z.val + 1))
        ((S.targetJordanSucc h).toOrthogonalDecomposition.prefixQuadraticSublattice
          (z.val + 1))
        (QuadraticSpace.scaledLine A) ↔
      DiagonalRepresents
        (diagonalUnitCoefficients
          (a.prefixValueUnits (j.val + 1) (by omega)))
        (diagonalUnitCoefficients
          (Fin.snoc (b.prefixValueUnits (j.val + 1) (by omega)) A)) := by
  let j := (S.sourceProfileSucc h).boundaryIndex z
  let sourceIso := (S.sourcePrefixExactDiagonalIsometry h z).symm
  let targetIso :=
    (S.targetPrefixExactDiagonalIsometry h z).symm.orthogonalSum
      (QuadraticSpace.Isometry.refl (QuadraticSpace.scaledLine A))
  unfold Lattice.QuadraticSublattice.EmbedsIntoOrthogonalSum
    QuadraticSpace.EmbedsInto
  rw [QuadraticSpace.represents_iff_of_isometries sourceIso targetIso]
  simpa only [j, GoodBONG.prefixExactDiagonalSpace] using
    (QuadraticSpace.finiteDiagonal_orthogonalSum_scaledLine_represents_iff
      (a.prefixValueUnits (j.val + 1) (by omega))
      (b.prefixValueUnits (j.val + 1) (by omega)) A)

/-- Under the active left threshold, O'Meara 93:28(iii) is exactly the
BONG prefix-representation site ending at that boundary. -/
theorem omearaConditionIIIAt_iff_prefixRepresentation
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1)
    (F : Lattice.JordanDecomposition.SameFundamentalType
      (S.sourceJordanSucc h) (S.targetJordanSucc h))
    (horders : a.SameOrders b)
    (hcondition : (S.sourceJordanSucc h).Omeara9328ConditionI
      (S.targetJordanSucc h))
    (z : Fin t)
    (htrigger : (S.sourceJordanSucc h).fundamentalIdeal z <
      (S.sourceJordanSucc h).fourNormOverWeightIdeal
        (Lattice.JordanDecomposition.boundaryLeftIndex z)) :
    let j := (S.sourceProfileSucc h).boundaryIndex z
    Lattice.QuadraticSublattice.EmbedsIntoOrthogonalSum
        ((S.sourceJordanSucc h).toOrthogonalDecomposition.prefixQuadraticSublattice
          (z.val + 1))
        ((S.targetJordanSucc h).toOrthogonalDecomposition.prefixQuadraticSublattice
          (z.val + 1))
        (QuadraticSpace.scaledLine
          ((S.sourceJordanSucc h).fundamentalNormGenerator
            (Lattice.JordanDecomposition.boundaryLeftIndex z))) ↔
      DiagonalRepresents
        (b.prefixValues j.val (by omega))
        (a.prefixValues (j.val + 1) (by omega)) := by
  let J := S.sourceJordanSucc h
  let H := S.targetJordanSucc h
  let c : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryLeftIndex z
  let A : Kˣ := J.fundamentalNormGenerator c
  let B : Kˣ := (S.targetProfileSucc h).boundaryLeftValue z
  have hBTarget : Lattice.IsNormGeneratorValue r
      (H.fundamentalLattice c) B := by
    exact S.targetBoundaryLeftValue_isNormGeneratorValue h z
  have hBSource : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice c) B := by
    apply Lattice.JordanDecomposition.isNormGeneratorValue_of_normGroupSet_eq
      hBTarget
    · simpa only [J, H,
          Lattice.JordanDecomposition.fundamentalNormGroup,
          Lattice.JordanDecomposition.SameFundamentalType.indexEquiv_apply_eq_self]
        using F.normGroup_eq c
    · exact J.exists_fundamentalNormGenerator c
  have hgeometry := S.omearaBoundaryEmbedding_iff_diagonal h z A
  have hswitch := S.boundaryDiagonalRepresentationSwitch h horders
    hcondition z c B hBSource htrigger
  have hhyperbolic := S.boundaryLeftDiagonal_iff_prefixRepresentation h z
  exact hgeometry.trans (hswitch.1.trans hhyperbolic)

/-- Under the active right threshold, O'Meara 93:28(ii) is exactly the
BONG prefix-representation site immediately after that boundary. -/
theorem omearaConditionIIAt_iff_prefixRepresentation
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1)
    (horders : a.SameOrders b)
    (hcondition : (S.sourceJordanSucc h).Omeara9328ConditionI
      (S.targetJordanSucc h))
    (z : Fin t)
    (htrigger : (S.sourceJordanSucc h).fundamentalIdeal z <
      (S.sourceJordanSucc h).fourNormOverWeightIdeal
        (Lattice.JordanDecomposition.boundaryRightIndex z)) :
    let j := (S.sourceProfileSucc h).boundaryIndex z
    Lattice.QuadraticSublattice.EmbedsIntoOrthogonalSum
        ((S.sourceJordanSucc h).toOrthogonalDecomposition.prefixQuadraticSublattice
          (z.val + 1))
        ((S.targetJordanSucc h).toOrthogonalDecomposition.prefixQuadraticSublattice
          (z.val + 1))
        (QuadraticSpace.scaledLine
          ((S.sourceJordanSucc h).fundamentalNormGenerator
            (Lattice.JordanDecomposition.boundaryRightIndex z))) ↔
      DiagonalRepresents
        (b.prefixValues (j.val + 1) (by omega))
        (a.prefixValues ((j.val + 1) + 1) (by omega)) := by
  let J := S.sourceJordanSucc h
  let c : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex z
  let j := (S.sourceProfileSucc h).boundaryIndex z
  let A : Kˣ := J.fundamentalNormGenerator c
  let B : Kˣ := (S.sourceProfileSucc h).boundaryRightValue z
  let targetUnits := b.prefixValueUnits (j.val + 1) (by omega)
  let sourceUnits := a.prefixValueUnits (j.val + 1) (by omega)
  let extendedSourceUnits := a.prefixValueUnits ((j.val + 1) + 1) (by omega)
  have hBSource : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice c) B := by
    exact S.sourceBoundaryRightValue_isNormGeneratorValue h z
  have hgeometry := S.omearaBoundaryEmbedding_iff_diagonal h z A
  have hswitch := S.boundaryDiagonalRepresentationSwitch h horders
    hcondition z c B hBSource htrigger
  have hBValue : B = a.valueUnit j.succ := by
    exact (S.sourceProfileSucc h).boundaryRightValue_eq_valueUnit_succ z
  have hprefix : Fin.snoc sourceUnits B = extendedSourceUnits := by
    have hraw := a.prefixValueUnits_succ_eq_snoc (j.val + 1) (by omega)
    change extendedSourceUnits = Fin.snoc sourceUnits
      (a.valueUnit ⟨j.val + 1, by omega⟩) at hraw
    calc
      Fin.snoc sourceUnits B =
          Fin.snoc sourceUnits (a.valueUnit j.succ) := by rw [hBValue]
      _ = Fin.snoc sourceUnits
          (a.valueUnit ⟨j.val + 1, by omega⟩) := by
        congr 1
      _ = extendedSourceUnits := hraw.symm
  have hresult := hgeometry.trans hswitch.2
  change _ ↔ DiagonalRepresents
    (diagonalUnitCoefficients targetUnits)
    (diagonalUnitCoefficients extendedSourceUnits)
  rw [← hprefix]
  exact hresult

/-- The two representation clauses of O'Meara 93:28 imply all of Beli's
internal prefix-representation conditions. -/
theorem internalRepresentationConditions_of_omeara9328ConditionII_and_III
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1)
    (F : Lattice.JordanDecomposition.SameFundamentalType
      (S.sourceJordanSucc h) (S.targetJordanSucc h))
    (horders : a.SameOrders b)
    (hconditionI : (S.sourceJordanSucc h).Omeara9328ConditionI
      (S.targetJordanSucc h))
    (hconditionII : (S.sourceJordanSucc h).Omeara9328ConditionII
      (S.targetJordanSucc h))
    (hconditionIII : (S.sourceJordanSucc h).Omeara9328ConditionIII
      (S.targetJordanSucc h)) :
    a.InternalRepresentationConditions b := by
  intro i hi htrigger
  rcases S.internalTrigger_has_adjacentContainment h i hi htrigger with
    ⟨z, hindex, hcontainment⟩ | ⟨z, hindex, hcontainment⟩
  · have hembedding := hconditionII z hcontainment
    have hboundary :=
      (S.omearaConditionIIAt_iff_prefixRepresentation
        h horders hconditionI z hcontainment).1 hembedding
    let j := (S.sourceProfileSucc h).boundaryIndex z
    exact GoodBONG.prefixRepresents_cast b a
      (by omega)
      (by omega)
      hboundary
  · have hembedding := hconditionIII z hcontainment
    have hboundary :=
      (S.omearaConditionIIIAt_iff_prefixRepresentation
        h F horders hconditionI z hcontainment).1 hembedding
    let j := (S.sourceProfileSucc h).boundaryIndex z
    exact GoodBONG.prefixRepresents_cast b a
      (by omega)
      (by omega)
      hboundary

/-- Beli's internal representation conditions imply O'Meara 93:28(ii),
including the terminal-unary case supplied by the ambient-space isometry. -/
theorem omeara9328ConditionII_of_internalRepresentationConditions
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1)
    (ambient : q.IsIsometric r)
    (horders : a.SameOrders b)
    (hconditionI : (S.sourceJordanSucc h).Omeara9328ConditionI
      (S.targetJordanSucc h))
    (hinternal : a.InternalRepresentationConditions b) :
    (S.sourceJordanSucc h).Omeara9328ConditionII
      (S.targetJordanSucc h) := by
  intro z hcontainment
  apply (S.omearaConditionIIAt_iff_prefixRepresentation
    h horders hconditionI z hcontainment).2
  let j := (S.sourceProfileSucc h).boundaryIndex z
  let c : Fin S.componentCount := Fin.cast h.symm
    (Lattice.JordanDecomposition.boundaryRightIndex z)
  have hcPositive : 0 < c.val := by
    simp [c, Lattice.JordanDecomposition.boundaryRightIndex]
  have hboundaryStart : j.val + 1 = S.componentStart c := by
    simpa only [j, c] using
      S.sourceBoundaryIndex_succ_val_eq_componentStart h z
  by_cases hrank : 2 ≤ S.sourceJordan.componentRank c
  · have hthreshold :=
      (S.rightBoundaryAlphaTrigger_iff_conditionIIContainment_of_rank_two
        h z hrank).2 hcontainment
    have hstop := S.componentStop_le c
    have hsiteBound : j.val + 1 < n + 1 := by
      have hstopFormula : S.componentStop c = S.componentStart c +
          S.sourceJordan.componentRank c := rfl
      omega
    let site : Fin (n + 1) := ⟨j.val + 1, hsiteBound⟩
    have hsitePositive : 0 < site.val := by
      dsimp only [site]
      omega
    have hsiteThreshold : 2 * (ramificationIndex K : ℚ) <
        a.alphaValue ⟨site.val - 1, by omega⟩ +
          a.alphaValue site := by
      have hleftIndex :
          (⟨site.val - 1, by omega⟩ : Fin (n + 1)) = j := by
        apply Fin.ext
        dsimp only [site]
        omega
      have hrightIndex : site =
          ⟨j.val + 1, by omega⟩ := by
        apply Fin.ext
        rfl
      have hleftAlpha := congrArg a.alphaValue hleftIndex
      have hrightAlpha := congrArg a.alphaValue hrightIndex
      rw [hleftAlpha, hrightAlpha]
      exact hthreshold
    have hsiteRepresentation := hinternal site hsitePositive hsiteThreshold
    exact GoodBONG.prefixRepresents_cast b a
      rfl
      rfl
      hsiteRepresentation
  · have hrankPositive := S.sourceJordan.component_finrank_pos c
    change 0 < S.sourceJordan.componentRank c at hrankPositive
    have hrankOne : S.sourceJordan.componentRank c = 1 := by omega
    by_cases hnext : c.val + 1 < S.componentCount
    · let previousBoundary : Fin t := ⟨c.val - 1, by
        have hcBound := c.isLt
        have hcount : S.componentCount = t + 1 := h
        omega⟩
      have hpreviousBoundary : previousBoundary = z := by
        apply Fin.ext
        change c.val - 1 = z.val
        have hcVal : c.val = z.val + 1 := by rfl
        omega
      have hcCast : Fin.cast h c =
          Lattice.JordanDecomposition.boundaryRightIndex z := by
        apply Fin.ext
        rfl
      have hleftContainment :
          (S.sourceJordanSucc h).fundamentalIdeal previousBoundary <
            (S.sourceJordanSucc h).fourNormOverWeightIdeal (Fin.cast h c) := by
        rw [hpreviousBoundary, hcCast]
        exact hcontainment
      have hthreshold :=
        (S.unaryComponentAlphaTrigger_iff_adjacentContainment
          h c hcPositive hnext hrankOne).2 (Or.inl hleftContainment)
      have hstopFormula : S.componentStop c = S.componentStart c + 1 := by
        calc
          S.componentStop c = S.componentStart c +
              S.sourceJordan.componentRank c := rfl
          _ = S.componentStart c + 1 := by rw [hrankOne]
      let cnext : Fin S.componentCount := ⟨c.val + 1, hnext⟩
      have hstopStart := S.componentStop_eq_componentStart_of_val_succ
        c cnext rfl
      have hnextBound := (S.componentStart_lt_componentStop cnext).trans_le
        (S.componentStop_le cnext)
      have hsiteBound : S.componentStart c < n + 1 := by omega
      let site : Fin (n + 1) := ⟨S.componentStart c, hsiteBound⟩
      have hsitePositive : 0 < site.val := by
        dsimp only [site]
        rw [← hboundaryStart]
        omega
      have hsiteThreshold : 2 * (ramificationIndex K : ℚ) <
          a.alphaValue ⟨site.val - 1, by omega⟩ +
            a.alphaValue site := by
        simpa only [site] using hthreshold
      have hsiteRepresentation := hinternal site hsitePositive hsiteThreshold
      exact GoodBONG.prefixRepresents_cast b a
        (by dsimp only [site]; omega)
        (by dsimp only [site]; omega)
        hsiteRepresentation
    · have hstopEq : S.componentStop c = n + 2 := by
        have hstopLe := S.componentStop_le c
        by_contra hne
        have hstopLt : S.componentStop c < n + 2 := by omega
        exact hnext (S.source_component_has_successor_of_stop_lt c hstopLt)
      have hfullLength : j.val + 2 = n + 2 := by
        have hstopFormula : S.componentStop c = S.componentStart c +
            S.sourceJordan.componentRank c := rfl
        omega
      have hfull := a.prefixRepresentsFull_of_isometric b ambient
        (j.val + 1) (by omega)
      exact GoodBONG.prefixRepresents_cast b a rfl hfullLength.symm hfull

/-- Beli's internal representation conditions imply O'Meara 93:28(iii),
including the initial-unary case represented by the zero-dimensional prefix. -/
theorem omeara9328ConditionIII_of_internalRepresentationConditions
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1)
    (F : Lattice.JordanDecomposition.SameFundamentalType
      (S.sourceJordanSucc h) (S.targetJordanSucc h))
    (horders : a.SameOrders b)
    (hconditionI : (S.sourceJordanSucc h).Omeara9328ConditionI
      (S.targetJordanSucc h))
    (hinternal : a.InternalRepresentationConditions b) :
    (S.sourceJordanSucc h).Omeara9328ConditionIII
      (S.targetJordanSucc h) := by
  intro z hcontainment
  apply (S.omearaConditionIIIAt_iff_prefixRepresentation
    h F horders hconditionI z hcontainment).2
  let j := (S.sourceProfileSucc h).boundaryIndex z
  let c : Fin S.componentCount := Fin.cast h.symm
    (Lattice.JordanDecomposition.boundaryLeftIndex z)
  have hcVal : c.val = z.val := by rfl
  have hnext : c.val + 1 < S.componentCount := by
    have hzBound := z.isLt
    have hcount : S.componentCount = t + 1 := h
    omega
  let cnext : Fin S.componentCount := ⟨c.val + 1, hnext⟩
  have hcnextEq : cnext = Fin.cast h.symm
      (Lattice.JordanDecomposition.boundaryRightIndex z) := by
    apply Fin.ext
    rfl
  have hboundaryStart :=
    S.sourceBoundaryIndex_succ_val_eq_componentStart h z
  rw [← hcnextEq] at hboundaryStart
  have hstopStart := S.componentStop_eq_componentStart_of_val_succ
    c cnext rfl
  have hboundaryStop : j.val + 1 = S.componentStop c := by
    exact hboundaryStart.trans hstopStart.symm
  by_cases hrank : 2 ≤ S.sourceJordan.componentRank c
  · have hthreshold :=
      (S.leftBoundaryAlphaTrigger_iff_conditionIIIContainment_of_rank_two
        h z hrank).2 hcontainment
    have hstopFormula : S.componentStop c = S.componentStart c +
        S.sourceJordan.componentRank c := rfl
    have hjPositive : 0 < j.val := by omega
    exact hinternal j hjPositive hthreshold
  · have hrankPositive := S.sourceJordan.component_finrank_pos c
    change 0 < S.sourceJordan.componentRank c at hrankPositive
    have hrankOne : S.sourceJordan.componentRank c = 1 := by omega
    by_cases hcPositive : 0 < c.val
    · let nextBoundary : Fin t := ⟨c.val, by omega⟩
      have hnextBoundary : nextBoundary = z := by
        apply Fin.ext
        exact hcVal
      have hcCast : Fin.cast h c =
          Lattice.JordanDecomposition.boundaryLeftIndex z := by
        apply Fin.ext
        rfl
      have hrightContainment :
          (S.sourceJordanSucc h).fundamentalIdeal nextBoundary <
            (S.sourceJordanSucc h).fourNormOverWeightIdeal (Fin.cast h c) := by
        rw [hnextBoundary, hcCast]
        exact hcontainment
      have hthreshold :=
        (S.unaryComponentAlphaTrigger_iff_adjacentContainment
          h c hcPositive hnext hrankOne).2 (Or.inr hrightContainment)
      have hstopFormula : S.componentStop c = S.componentStart c + 1 := by
        calc
          S.componentStop c = S.componentStart c +
              S.sourceJordan.componentRank c := rfl
          _ = S.componentStart c + 1 := by rw [hrankOne]
      have hstartEq : S.componentStart c = j.val := by omega
      have hsiteBound : S.componentStart c < n + 1 := by
        rw [hstartEq]
        exact j.isLt
      let site : Fin (n + 1) := ⟨S.componentStart c, hsiteBound⟩
      have hsitePositive : 0 < site.val := by
        dsimp only [site]
        exact S.componentStart_pos_of_val_pos c hcPositive
      have hsiteThreshold : 2 * (ramificationIndex K : ℚ) <
          a.alphaValue ⟨site.val - 1, by omega⟩ +
            a.alphaValue site := by
        simpa only [site] using hthreshold
      have hsiteRepresentation := hinternal site hsitePositive hsiteThreshold
      exact GoodBONG.prefixRepresents_cast b a
        hstartEq (congrArg (fun x : Nat ↦ x + 1) hstartEq)
        hsiteRepresentation
    · have hcZero : c.val = 0 := Nat.eq_zero_of_not_pos hcPositive
      have hcFirst : c = S.sourceFirstComponent := by
        apply Fin.ext
        exact hcZero
      have hstartZero : S.componentStart c = 0 := by
        rw [hcFirst]
        unfold componentStart
        rw [S.Iio_sourceFirstComponent_eq_empty]
        simp
      have hstopFormula : S.componentStop c = S.componentStart c + 1 := by
        calc
          S.componentStop c = S.componentStart c +
              S.sourceJordan.componentRank c := rfl
          _ = S.componentStart c + 1 := by rw [hrankOne]
      have hjZero : j.val = 0 := by omega
      have hempty : DiagonalRepresents
          (b.prefixValues 0 (by omega))
          (a.prefixValues 1 (by omega)) := by
        have hp := DiagonalRepresents.prefixOfLE
          (a.prefixValues 1 (by omega)) (Nat.zero_le 1)
        convert hp using 1
      exact GoodBONG.prefixRepresents_cast b a
        hjZero.symm (by omega) hempty

/-- Concrete Beli (2009/2010), Lemma 3.9.  No representation-reduction
interface remains: the only endpoint input is the ambient-space isometry
already assumed in Theorem 3.1. -/
theorem beli2009Lemma39_concrete
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1)
    (ambient : q.IsIsometric r)
    (F : Lattice.JordanDecomposition.SameFundamentalType
      (S.sourceJordanSucc h) (S.targetJordanSucc h))
    (horders : a.SameOrders b)
    (hconditionI : (S.sourceJordanSucc h).Omeara9328ConditionI
      (S.targetJordanSucc h)) :
    a.InternalRepresentationConditions b ↔
      (S.sourceJordanSucc h).Omeara9328ConditionII
          (S.targetJordanSucc h) ∧
        (S.sourceJordanSucc h).Omeara9328ConditionIII
          (S.targetJordanSucc h) := by
  constructor
  · intro hinternal
    exact ⟨S.omeara9328ConditionII_of_internalRepresentationConditions
        h ambient horders hconditionI hinternal,
      S.omeara9328ConditionIII_of_internalRepresentationConditions
        h F horders hconditionI hinternal⟩
  · rintro ⟨hII, hIII⟩
    exact S.internalRepresentationConditions_of_omeara9328ConditionII_and_III
      h F horders hconditionI hII hIII

end BONG.StrictJordanAdaptedAlignment

end Bong
