/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9318ParityReduction
import Bong.Lattice.OmearaOddLowRankWeightPlane

/-!
# The odd quinary and senary cases of O'Meara 93:18(v)

Split a norm-preserving binary summand.  Its rank-three or rank-four
complement is governed by 93:18(ii), (iii), and (iv).  In the remaining
odd branch, expose its canonical weight plane and repeat the same low-rank
argument on the norm-preserving residual complement.  If neither complement
already contains a hyperbolic plane, the two canonical weight coefficients
are uniformizer powers of the same parity.  The final 82:15a/93:11
calculation is `ofGeneralTwoPlaneDisplayedIsometryOfSquareRelated`.

This file closes the function argument left explicit in
`Omeara9318ParityReduction`; it introduces no new local classification law.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w x

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [laws : DyadicDiscriminantClassLaws K]

/-- If the right factor in a displayed orthogonal product contains a
hyperbolic plane, rotate that plane to the front. -/
noncomputable def Omeara9318vData.ofRightComplementDisplayedIsometry
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {X : Type x} [AddCommGroup X] [Module K X]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (p : QuadraticSpace K W) (A : Lattice K W)
    (r : QuadraticSpace K X) (M : Lattice K X)
    (hmodular : IsModular q L (1 : Kˣ))
    (displayed : Isometry q (p.orthogonalSum r) L (product A M))
    (E : Omeara9318vData r M (1 : Kˣ)) :
    Omeara9318vData q L (1 : Kˣ) := by
  let exposeRight : Isometry (p.orthogonalSum r)
      (p.orthogonalSum
        ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
          (E.decomposition.component 1).space))
      (product A M)
      (product A
        (product (hyperbolicPlaneLattice (K := K))
          (E.decomposition.component 1).lattice)) :=
    (Isometry.refl p A).orthogonalProductBasic E.displayedIsometry
  let rotate : Isometry
      (p.orthogonalSum
        ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
          (E.decomposition.component 1).space))
      (((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum p)
        |>.orthogonalSum (E.decomposition.component 1).space)
      (product A
        (product (hyperbolicPlaneLattice (K := K))
          (E.decomposition.component 1).lattice))
      (product
        (product (hyperbolicPlaneLattice (K := K)) A)
        (E.decomposition.component 1).lattice) :=
    orthogonalProductRotateLeft
  let reassociate : Isometry
      (((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum p)
        |>.orthogonalSum (E.decomposition.component 1).space)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
        (p.orthogonalSum (E.decomposition.component 1).space))
      (product
        (product (hyperbolicPlaneLattice (K := K)) A)
        (E.decomposition.component 1).lattice)
      (product (hyperbolicPlaneLattice (K := K))
        (product A (E.decomposition.component 1).lattice)) :=
    orthogonalProductAssoc
  let finalDisplayed := displayed.trans
    (exposeRight.trans (rotate.trans reassociate))
  exact Omeara9318vData.ofDisplayedIsometry
    (p.orthogonalSum (E.decomposition.component 1).space)
    (product A (E.decomposition.component 1).lattice)
    hmodular finalDisplayed

/-- Ordered canonical uniformizer powers of the same parity differ by the
square of an integral uniformizer power. -/
theorem exists_integral_square_between_uniformizer_powers
    (R T : Int) (hle : T ≤ R) (hmod : Int.ModEq 2 R T) :
    ∃ c : K, c ∈ IntegerRing K ∧
      (uniformizerPowerUnit K R : K) =
        (uniformizerPowerUnit K T : K) * c ^ 2 := by
  rcases exists_nat_eq_add_two_mul_of_le_modEq_two hle hmod with
    ⟨k, hk⟩
  let cU : Kˣ := uniformizerPowerUnit K (k : Int)
  have hc : (cU : K) ∈ IntegerRing K :=
    uniformizerPowerUnit_nat_mem_integerRing k
  have hUnits : uniformizerPowerUnit K T * cU ^ 2 =
      uniformizerPowerUnit K R := by
    calc
      uniformizerPowerUnit K T * cU ^ 2 =
          uniformizerPowerUnit K T * (1 : Kˣ) * cU ^ 2 := by simp
      _ = uniformizerPowerUnit K (T + 2 * (k : Int)) * (1 : Kˣ) :=
        uniformizerParameter_mul_square (1 : Kˣ) T k
      _ = uniformizerPowerUnit K R := by rw [← hk]
        <;> simp
  refine ⟨(cU : K), hc, ?_⟩
  have hCoe := congrArg (fun z : Kˣ ↦ (z : K)) hUnits
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using hCoe.symm

set_option maxHeartbeats 3000000 in
-- The nested low-rank classification and transported decompositions are
-- elaboration-heavy but are a finite transcription of O'Meara 93:18(v).
/-- O'Meara 93:18(v), normalized odd base case in ranks five and six. -/
noncomputable def omeara9318vOddRankFiveOrSix :
    Omeara9318vOddRankFiveOrSixConstructor.{u, v} (K := K) := by
  intro V _ _ q L hmodular hrank a ha hodd
  letI : Module.Finite K V := L.moduleFinite
  let S :=
    NormPreservingBinaryModularSplittingData.normPreservingBinaryModularSplittingData
      q L (1 : Kˣ) hmodular (by omega)
  let J := S.decomposition.component 0
  let C := S.decomposition.component 1
  letI : Module.Finite K J.carrier := J.lattice.moduleFinite
  letI : Module.Finite K C.carrier := C.lattice.moduleFinite
  have htotal :=
    S.decomposition.pairProductLatticeIsometry.toLinearEquiv.finrank_eq
  have hCrank : finrank K C.carrier = finrank K V - 2 := by
    change finrank K (J.carrier × C.carrier) = finrank K V at htotal
    rw [Module.finrank_prod, S.first_rank] at htotal
    have htotal' : finrank K C.carrier + 2 = finrank K V := by
      simpa only [Nat.add_comm] using htotal
    exact Nat.eq_sub_of_add_eq htotal'
  have hCrankThreeOrFour :
      finrank K C.carrier = 3 ∨ finrank K C.carrier = 4 := by
    rcases hrank with hfive | hsix
    · left
      rw [hCrank, hfive]
    · right
      rw [hCrank, hsix]
  have hCrankAtLeastThree : 3 ≤ finrank K C.carrier :=
    hCrankThreeOrFour.elim (fun h ↦ by omega) (fun h ↦ by omega)
  let hxCExists := exists_isNormGenerator_of_finrank_pos
    C.space C.lattice (by omega)
  let xC : C.carrier := Classical.choose hxCExists
  have hxC : IsNormGenerator C.space C.lattice xC :=
    (Classical.choose_spec hxCExists).1
  have hxCne : C.space.quadratic xC ≠ 0 :=
    (Classical.choose_spec hxCExists).2
  let c : Kˣ := Units.mk0 (C.space.quadratic xC) hxCne
  have hc : IsNormGeneratorValue C.space C.lattice c :=
    hxC.isNormGeneratorValue hxCne
  by_cases hCeven : Even (ordUnit K c + weightIdealOrder C.space C.lattice)
  · let E := omeara9318iiData S.complement_modular hCrankAtLeastThree
        c hc hCeven
    exact Omeara9318vData.ofRightComplementDisplayedIsometry
      J.space J.lattice C.space C.lattice hmodular
      S.decomposition.pairProductLatticeIsometry.symm E
  · have hCodd : Odd
        (ordUnit K c + weightIdealOrder C.space C.lattice) :=
      Int.not_even_iff_odd.mp hCeven
    let D₁ : OmearaOddLowRankWeightPlaneData C.space C.lattice := by
      by_cases hthree : finrank K C.carrier = 3
      · exact omeara9318ivWeightPlaneData
          S.complement_modular hthree c hc hCodd
      · exact omeara9318iiiWeightPlaneData
          S.complement_modular
            (hCrankThreeOrFour.resolve_left hthree) c hc hCodd
    let P₁ := QuadraticSpace.omearaGeneralPlane
      (D₁.b : K) D₁.tail D₁.plane_nondegenerate
    let R₀ := D₁.decomposition.component 1
    let expose : Isometry q (J.space.orthogonalSum C.space) L
        (product J.lattice C.lattice) :=
      S.decomposition.pairProductLatticeIsometry.symm
    let exposeC : Isometry (J.space.orthogonalSum C.space)
        (J.space.orthogonalSum (P₁.orthogonalSum R₀.space))
        (product J.lattice C.lattice)
        (product J.lattice
          (product (hyperbolicPlaneLattice (K := K)) R₀.lattice)) :=
      (Isometry.refl J.space J.lattice).orthogonalProductBasic
        D₁.displayedIsometry
    let rotate₁ : Isometry
        (J.space.orthogonalSum (P₁.orthogonalSum R₀.space))
        ((P₁.orthogonalSum J.space).orthogonalSum R₀.space)
        (product J.lattice
          (product (hyperbolicPlaneLattice (K := K)) R₀.lattice))
        (product
          (product (hyperbolicPlaneLattice (K := K)) J.lattice)
          R₀.lattice) :=
      orthogonalProductRotateLeft
    let reassociate₁ : Isometry
        ((P₁.orthogonalSum J.space).orthogonalSum R₀.space)
        (P₁.orthogonalSum (J.space.orthogonalSum R₀.space))
        (product
          (product (hyperbolicPlaneLattice (K := K)) J.lattice)
          R₀.lattice)
        (product (hyperbolicPlaneLattice (K := K))
          (product J.lattice R₀.lattice)) :=
      orthogonalProductAssoc
    let displayed₁ := expose.trans
      (exposeC.trans (rotate₁.trans reassociate₁))
    let R₁ := J.space.orthogonalSum R₀.space
    let M₁ : Lattice K (J.carrier × R₀.carrier) :=
      product J.lattice R₀.lattice
    have hR₁modular : IsModular R₁ M₁ (1 : Kˣ) :=
      S.first_modular.orthogonalProduct D₁.complement_modular
    have hR₁norm : normIdeal R₁ M₁ = normIdeal q L := by
      calc
        normIdeal R₁ M₁ =
            normIdeal J.space J.lattice ⊔
              normIdeal R₀.space R₀.lattice :=
          normIdeal_orthogonalProduct
        _ = normIdeal J.space J.lattice ⊔ normIdeal q L := by
          rw [D₁.complement_normIdeal_eq,
            S.complement_normIdeal_eq]
        _ = normIdeal q L := sup_eq_right.mpr
          (NormPreservingBinaryModularSplittingData.componentZero_normIdeal_le
            S.decomposition)
    have hR₁rankThreeOrFour :
        finrank K (J.carrier × R₀.carrier) = 3 ∨
          finrank K (J.carrier × R₀.carrier) = 4 := by
      rw [Module.finrank_prod, S.first_rank, D₁.complement_finrank]
      rcases hCrankThreeOrFour with hthree | hfour
      · left
        rw [hthree]
      · right
        rw [hfour]
    have hR₁rankAtLeastThree :
        3 ≤ finrank K (J.carrier × R₀.carrier) :=
      hR₁rankThreeOrFour.elim (fun h ↦ by omega) (fun h ↦ by omega)
    let hx₁Exists := exists_isNormGenerator_of_finrank_pos R₁ M₁
      (by omega)
    let x₁ : J.carrier × R₀.carrier := Classical.choose hx₁Exists
    have hx₁ : IsNormGenerator R₁ M₁ x₁ :=
      (Classical.choose_spec hx₁Exists).1
    have hx₁ne : R₁.quadratic x₁ ≠ 0 :=
      (Classical.choose_spec hx₁Exists).2
    let d : Kˣ := Units.mk0 (R₁.quadratic x₁) hx₁ne
    have hd : IsNormGeneratorValue R₁ M₁ d :=
      hx₁.isNormGeneratorValue hx₁ne
    have hcdOrder : ordUnit K c = ordUnit K d := by
      apply (principalIdeal_eq_iff_ordUnit_eq c d).mp
      calc
        principalIdeal (K := K) (c : K) = normIdeal C.space C.lattice :=
          hc.2.symm
        _ = normIdeal q L := S.complement_normIdeal_eq
        _ = normIdeal R₁ M₁ := hR₁norm.symm
        _ = principalIdeal (K := K) (d : K) := hd.2
    by_cases hR₁even : Even (ordUnit K d + weightIdealOrder R₁ M₁)
    · let E := omeara9318iiData hR₁modular hR₁rankAtLeastThree
          d hd hR₁even
      exact Omeara9318vData.ofRightComplementDisplayedIsometry
        P₁ (hyperbolicPlaneLattice (K := K)) R₁ M₁ hmodular
        displayed₁ E
    · have hR₁odd : Odd
          (ordUnit K d + weightIdealOrder R₁ M₁) :=
        Int.not_even_iff_odd.mp hR₁even
      let D₂ : OmearaOddLowRankWeightPlaneData R₁ M₁ := by
        by_cases hthree :
            finrank K (J.carrier × R₀.carrier) = 3
        · exact omeara9318ivWeightPlaneData
            hR₁modular hthree d hd hR₁odd
        · exact omeara9318iiiWeightPlaneData
            hR₁modular
              (hR₁rankThreeOrFour.resolve_left hthree) d hd hR₁odd
      let P₂ := QuadraticSpace.omearaGeneralPlane
        (D₂.b : K) D₂.tail D₂.plane_nondegenerate
      let R₂ := D₂.decomposition.component 1
      let refineRight : Isometry
          (P₁.orthogonalSum R₁)
          (P₁.orthogonalSum (P₂.orthogonalSum R₂.space))
          (product (hyperbolicPlaneLattice (K := K)) M₁)
          (product (hyperbolicPlaneLattice (K := K))
            (product (hyperbolicPlaneLattice (K := K)) R₂.lattice)) :=
        (Isometry.refl P₁ (hyperbolicPlaneLattice (K := K)))
          |>.orthogonalProductBasic D₂.displayedIsometry
      let displayed₁₂ := displayed₁.trans refineRight
      have hweightMod : Int.ModEq 2
          (weightIdealOrder C.space C.lattice)
          (weightIdealOrder R₁ M₁) := by
        rw [Int.modEq_iff_dvd]
        rcases hCodd with ⟨m, hm⟩
        rcases hR₁odd with ⟨n, hn⟩
        refine ⟨n - m, ?_⟩
        omega
      by_cases h₂₁ : weightIdealOrder R₁ M₁ ≤
          weightIdealOrder C.space C.lattice
      · let hsquareExists :=
          exists_integral_square_between_uniformizer_powers
            (K := K) (weightIdealOrder C.space C.lattice)
              (weightIdealOrder R₁ M₁) h₂₁ hweightMod
        let square : K := Classical.choose hsquareExists
        have hsquareIntegral : square ∈ IntegerRing K :=
          (Classical.choose_spec hsquareExists).1
        have hsquare := (Classical.choose_spec hsquareExists).2
        have hrelated : (D₁.b : K) = (D₂.b : K) * square ^ 2 := by
          rw [D₁.b_eq, D₂.b_eq]
          exact hsquare
        exact Omeara9318vData.ofGeneralTwoPlaneDisplayedIsometryOfSquareRelated
          hmodular (D₁.b : K) D₁.tail (D₂.b : K) D₂.tail
          square D₁.tailHalf D₁.plane_nondegenerate
          D₂.plane_nondegenerate D₁.b_integral D₁.tailHalf_integral
          hsquareIntegral D₁.b_maximal hrelated D₁.tail_eq
          R₂.space R₂.lattice displayed₁₂
      · have h₁₂ : weightIdealOrder C.space C.lattice ≤
            weightIdealOrder R₁ M₁ := le_of_not_ge h₂₁
        let hsquareExists := exists_integral_square_between_uniformizer_powers
            (K := K) (weightIdealOrder R₁ M₁)
              (weightIdealOrder C.space C.lattice) h₁₂ hweightMod.symm
        let square : K := Classical.choose hsquareExists
        have hsquareIntegral : square ∈ IntegerRing K :=
          (Classical.choose_spec hsquareExists).1
        have hsquare := (Classical.choose_spec hsquareExists).2
        have hrelated : (D₂.b : K) = (D₁.b : K) * square ^ 2 := by
          rw [D₂.b_eq, D₁.b_eq]
          exact hsquare
        let rotate₂₁ : Isometry
            (P₁.orthogonalSum (P₂.orthogonalSum R₂.space))
            ((P₂.orthogonalSum P₁).orthogonalSum R₂.space)
            (product (hyperbolicPlaneLattice (K := K))
              (product (hyperbolicPlaneLattice (K := K)) R₂.lattice))
            (product
              (product (hyperbolicPlaneLattice (K := K))
                (hyperbolicPlaneLattice (K := K))) R₂.lattice) :=
          orthogonalProductRotateLeft
        let reassociate₂₁ : Isometry
            ((P₂.orthogonalSum P₁).orthogonalSum R₂.space)
            (P₂.orthogonalSum (P₁.orthogonalSum R₂.space))
            (product
              (product (hyperbolicPlaneLattice (K := K))
                (hyperbolicPlaneLattice (K := K))) R₂.lattice)
            (product (hyperbolicPlaneLattice (K := K))
              (product (hyperbolicPlaneLattice (K := K)) R₂.lattice)) :=
          orthogonalProductAssoc
        let displayed₂₁ := displayed₁₂.trans
          (rotate₂₁.trans reassociate₂₁)
        exact Omeara9318vData.ofGeneralTwoPlaneDisplayedIsometryOfSquareRelated
          hmodular (D₂.b : K) D₂.tail (D₁.b : K) D₁.tail
          square D₂.tailHalf D₂.plane_nondegenerate
          D₁.plane_nondegenerate D₂.b_integral D₂.tailHalf_integral
          hsquareIntegral D₂.b_maximal hrelated D₂.tail_eq
          R₂.space R₂.lattice displayed₂₁

/-- The completed odd base case closes the parity/rank reduction and hence
O'Meara 93:18(v) for every unimodular lattice of rank at least five. -/
noncomputable def omeara9318vDataUnimodular
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V)
    (hmodular : IsModular q L (1 : Kˣ))
    (hrank : 5 ≤ finrank K V) :
    Omeara9318vData q L (1 : Kˣ) :=
  omeara9318vDataOfOddRankFiveOrSix
    (omeara9318vOddRankFiveOrSix (K := K)) q L (1 : Kˣ)
      hmodular hrank

end Lattice

end Bong
