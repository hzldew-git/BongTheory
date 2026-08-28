/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328EqualOrderTwistAbsorption
import Bong.Dyadic.QuadraticDefectHensel

/-!
# O'Meara 93:28, Step 5

Suppose that the first normalized norm ideal is `2 O` and that the second
normalized norm order is strictly larger.  O'Meara observes that the first
fundamental ideal is then contained in `4 p`.  Thus condition 93:28(i) and
the Local Square Theorem force the normalized target-head determinant class
to be one.  The common even-parity branch of 93:18(ii) supplies a hyperbolic
plane in the target head, so the rank-four determinant criterion makes the
whole target head hyperbolic.

The proof below keeps the ramification index explicit: `4 p` is the power
ideal of order `2 * e + 1`, where `e = ord(2)`.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- A common upper bound for two scalar ideals bounds the scalar ideal of
their supremum. -/
private theorem scalarIdeal_sup_le (c : K)
    (I P Q : CoefficientIdeal (K := K))
    (hI : scalarIdeal c I ≤ Q) (hP : scalarIdeal c P ≤ Q) :
    scalarIdeal c (I ⊔ P) ≤ Q := by
  unfold scalarIdeal
  rintro x ⟨y, hy, rfl⟩
  rcases (Submodule.mem_sup).1 hy with ⟨yI, hyI, yP, hyP, rfl⟩
  rw [map_add]
  apply Q.add_mem
  · apply hI
    exact ⟨yI, hyI, rfl⟩
  · apply hP
    exact ⟨yP, hyP, rfl⟩

/-- In Step 5, the product-defect summand of the first fundamental ideal is
contained in `4 p`. -/
theorem firstBoundaryProductDefect_le_fourMaximal_of_firstNormTwo
    (hfirst : ordUnit K S.firstNormGenerator =
      (ramificationIndex K : Int))
    (hsecond : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    scalarIdeal
        (((S.sourceJordan.scaleGenerator (boundaryLeftIndex 0))⁻¹ ^ 2 : Kˣ) : K)
        (S.sourceJordan.boundaryProductDefectSum 0) ≤
      powerIdeal (K := K) (2 * (ramificationIndex K : Int) + 1) := by
  let li : Fin (n + 2) := boundaryLeftIndex 0
  let ri : Fin (n + 2) := boundaryRightIndex 0
  let a := S.sourceJordan.fundamentalNormGenerator li
  let b := S.sourceJordan.fundamentalNormGenerator ri
  let s := S.sourceJordan.fundamentalScaleOrder li
  have hli : li = (0 : Fin (n + 2)) := rfl
  have hri : ri = (1 : Fin (n + 2)) := rfl
  have hproduct : S.sourceJordan.boundaryProductDefectSum 0 ≤
      principalIdeal (K := K) ((a * b : Kˣ) : K) := by
    unfold boundaryProductDefectSum
    exact productDefectSum_le_principalIdeal_of_normGenerators a b
      (S.sourceJordan.fundamentalNormGenerator_spec li)
      (S.sourceJordan.fundamentalNormGenerator_spec ri)
  have hfirstOrder : ordUnit K a = s + (ramificationIndex K : Int) := by
    have h := S.firstNormGenerator_order
    rw [hfirst] at h
    simp only [a, s, hli]
    omega
  have hsecondOrder :
      s + (ramificationIndex K : Int) + 1 ≤ ordUnit K b := by
    have h := S.secondNormalizedNormGenerator_order
    simp only [b, s, hri, hli]
    omega
  calc
    scalarIdeal
        (((S.sourceJordan.scaleGenerator (boundaryLeftIndex 0))⁻¹ ^ 2 : Kˣ) : K)
        (S.sourceJordan.boundaryProductDefectSum 0) ≤
        scalarIdeal
          (((S.sourceJordan.scaleGenerator (boundaryLeftIndex 0))⁻¹ ^ 2 : Kˣ) : K)
          (principalIdeal (K := K) ((a * b : Kˣ) : K)) :=
      Submodule.map_mono hproduct
    _ = powerIdeal (K := K)
        (-2 * s + ordUnit K a + ordUnit K b) := by
      rw [principalIdeal_eq_powerIdeal, scalarIdeal_powerIdeal_units,
        ordUnit_pow, ordUnit_inv, ordUnit_mul]
      congr 1
      have hsOrder : ordUnit K
          (S.sourceJordan.scaleGenerator (boundaryLeftIndex 0)) = s := rfl
      rw [hsOrder]
      ring
    _ ≤ powerIdeal (K := K) (2 * (ramificationIndex K : Int) + 1) := by
      rw [powerIdeal_le_iff]
      omega

/-- In the even-boundary branch of Step 5, the parity summand is also
contained in `4 p`. -/
theorem firstBoundaryParity_le_fourMaximal_of_firstNormTwo
    (hfirst : ordUnit K S.firstNormGenerator =
      (ramificationIndex K : Int))
    (hsecond : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator)
    (heven : Even (S.sourceJordan.boundaryNormOrderSum 0)) :
    scalarIdeal
        (((S.sourceJordan.scaleGenerator (boundaryLeftIndex 0))⁻¹ ^ 2 : Kˣ) : K)
        (S.sourceJordan.boundaryParityIdeal 0) ≤
      powerIdeal (K := K) (2 * (ramificationIndex K : Int) + 1) := by
  let li : Fin (n + 2) := boundaryLeftIndex 0
  let ri : Fin (n + 2) := boundaryRightIndex 0
  let s := S.sourceJordan.fundamentalScaleOrder li
  let u₀ := ordUnit K (S.sourceJordan.fundamentalNormGenerator li)
  let u₁ := ordUnit K (S.sourceJordan.fundamentalNormGenerator ri)
  have hli : li = (0 : Fin (n + 2)) := rfl
  have hri : ri = (1 : Fin (n + 2)) := rfl
  have hu₀ : u₀ = s + (ramificationIndex K : Int) := by
    have h := S.firstNormGenerator_order
    rw [hfirst] at h
    simp only [u₀, s, hli]
    omega
  have hu₁ : s + (ramificationIndex K : Int) + 1 ≤ u₁ := by
    have h := S.secondNormalizedNormGenerator_order
    simp only [u₁, s, hri, hli]
    omega
  have hsum : S.sourceJordan.boundaryNormOrderSum 0 = u₀ + u₁ := by
    rfl
  have hhalf : s + (ramificationIndex K : Int) + 1 ≤
      S.sourceJordan.boundaryNormOrderSum 0 / 2 := by
    rw [hsum] at heven ⊢
    rcases heven with ⟨k, hk⟩
    omega
  unfold boundaryParityIdeal
  rw [twiceIdeal_powerIdeal, scalarIdeal_powerIdeal_units,
    ordUnit_pow, ordUnit_inv, powerIdeal_le_iff]
  have hsOrder : ordUnit K
      (S.sourceJordan.scaleGenerator (boundaryLeftIndex 0)) = s := rfl
  have hsFundamental :
      S.sourceJordan.fundamentalScaleOrder (boundaryLeftIndex 0) = s := rfl
  rw [hsOrder, hsFundamental]
  omega

/-- O'Meara's Step-5 estimate `f₁ ⊆ 4 p`. -/
theorem firstFundamentalIdeal_le_fourMaximal_of_firstNormTwo
    (hfirst : ordUnit K S.firstNormGenerator =
      (ramificationIndex K : Int))
    (hsecond : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    S.sourceJordan.fundamentalIdeal 0 ≤
      powerIdeal (K := K) (2 * (ramificationIndex K : Int) + 1) := by
  let c : K :=
    (((S.sourceJordan.scaleGenerator (boundaryLeftIndex 0))⁻¹ ^ 2 : Kˣ) : K)
  change scalarIdeal c
      (if Even (S.sourceJordan.boundaryNormOrderSum 0) then
        S.sourceJordan.boundaryProductDefectSum 0 ⊔
          S.sourceJordan.boundaryParityIdeal 0
       else S.sourceJordan.boundaryProductDefectSum 0) ≤
    powerIdeal (K := K) (2 * (ramificationIndex K : Int) + 1)
  by_cases heven : Even (S.sourceJordan.boundaryNormOrderSum 0)
  · rw [if_pos heven]
    have hproduct : scalarIdeal c
        (S.sourceJordan.boundaryProductDefectSum 0) ≤
          powerIdeal (K := K)
            (2 * (ramificationIndex K : Int) + 1) := by
      simpa only [c] using
        S.firstBoundaryProductDefect_le_fourMaximal_of_firstNormTwo
          hfirst hsecond
    have hparity : scalarIdeal c
        (S.sourceJordan.boundaryParityIdeal 0) ≤
          powerIdeal (K := K)
            (2 * (ramificationIndex K : Int) + 1) := by
      simpa only [c] using
        S.firstBoundaryParity_le_fourMaximal_of_firstNormTwo
          hfirst hsecond heven
    exact scalarIdeal_sup_le (K := K) c _ _ _ hproduct hparity
  · rw [if_neg heven]
    simpa only [c] using
      S.firstBoundaryProductDefect_le_fourMaximal_of_firstNormTwo
        hfirst hsecond

/-- The determinant-congruence error in Step 5 is deeper than `4`, hence its
unit `1 + error` is a square by the Local Square Theorem. -/
theorem firstNormTwo_congruenceError_isSquare
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hfirst : ordUnit K S.firstNormGenerator =
      (ramificationIndex K : Int))
    (hsecond : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    IsSquare (S.targetFirstCongruenceError A conditions).errorUnit := by
  let C := S.targetFirstCongruenceError A conditions
  have hmem : C.error ∈
      powerIdeal (K := K) (2 * (ramificationIndex K : Int) + 1) :=
    S.firstFundamentalIdeal_le_fourMaximal_of_firstNormTwo hfirst hsecond
      C.error_mem
  have horder :
      (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) <
        ord K C.error := by
    have hmem' := (mem_powerIdeal_iff
      (K := K) (2 * (ramificationIndex K : Int) + 1) C.error).1 hmem
    exact lt_of_lt_of_le (by
      exact_mod_cast (show 2 * ramificationIndex K <
        2 * ramificationIndex K + 1 by omega)) hmem'
  apply isSquare_of_ord_sub_one_gt_two_mul_e K C.errorUnit
  rw [C.errorUnit_coe]
  convert horder using 1 <;> ring

/-- The normalized target head has determinant class one in Step 5. -/
theorem targetFirstNormalized_determinantClass_eq_one_of_firstNormTwo
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hfirst : ordUnit K S.firstNormGenerator =
      (ramificationIndex K : Int))
    (hsecond : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    determinantClass S.targetFirstNormalized
      (S.targetJordan.component 0).lattice = 1 := by
  let C := S.targetFirstCongruenceError A conditions
  have hsquare : IsSquare C.errorUnit :=
    S.firstNormTwo_congruenceError_isSquare A conditions hfirst hsecond
  rcases hsquare with ⟨u, hu⟩
  have huOrder : ordUnit K u = 0 := by
    have hunit := C.errorUnit_isValuationUnit
    have horder := congrArg (ordUnit K) hu
    rw [ordUnit_mul] at horder
    have herrorOrder : ordUnit K C.errorUnit = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K C.errorUnit).1 hunit
    omega
  have huUnit : IsValuationUnit K (u : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K u).2 huOrder
  have hclass : unitSquareClass K C.errorUnit = 1 := by
    calc
      unitSquareClass K C.errorUnit = unitSquareClass K (1 * u ^ 2) := by
        congr 1
        simpa only [one_mul, pow_two] using hu
      _ = unitSquareClass K (1 : Kˣ) :=
        unitSquareClass_mul_unit_square K 1 u huUnit
      _ = 1 := unitSquareClass_one K
  unfold determinantClass
  exact C.unitSquareClass_eq_errorUnit.trans hclass

/-- In Step 5 the first normalized norm and weight orders have even sum, so
the synchronized first-component models use 93:18(ii). -/
theorem firstNormWeightParity_even_of_firstNormTwo
    (hfirst : ordUnit K S.firstNormGenerator =
      (ramificationIndex K : Int)) :
    Even S.firstNormWeightParity := by
  have hnormLe := normGeneratorOrder_le_weightIdealOrder
    S.firstNormGenerator S.firstNormGenerator_source
  have hweightLe : weightIdealOrder S.sourceFirstNormalized
      (S.sourceJordan.component 0).lattice ≤
        (ramificationIndex K : Int) := by
    have h := twoScaleIdeal_le_weightIdeal S.sourceFirstNormalized
      (S.sourceJordan.component 0).lattice
    rw [twoScaleIdeal_eq_principalIdeal_two_of_unimodular
      S.sourceFirstNormalized_unimodular
        (by rw [S.sourceFirstNormalized_finrank]; omega),
      weightIdeal_eq_powerIdeal] at h
    let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
    have htwo : principalIdeal (K := K) (2 : K) =
        powerIdeal (K := K) (ramificationIndex K : Int) := by
      calc
        principalIdeal (K := K) (2 : K) =
            principalIdeal (K := K) (two : K) := rfl
        _ = powerIdeal (K := K) (ordUnit K two) :=
          principalIdeal_eq_powerIdeal two
        _ = powerIdeal (K := K) (ramificationIndex K : Int) := by
          congr 1
          apply WithTop.coe_injective
          rw [coe_ordUnit]
          exact (ramificationIndex_spec K).symm
    rw [htwo, powerIdeal_le_iff] at h
    exact h
  have hweight : weightIdealOrder S.sourceFirstNormalized
      (S.sourceJordan.component 0).lattice =
        (ramificationIndex K : Int) := by
    omega
  unfold firstNormWeightParity
  rw [hfirst, hweight]
  exact ⟨ramificationIndex K, by omega⟩

/-- The even model selected in Step 5 exhibits a hyperbolic plane in the
normalized target head. -/
theorem targetFirstNormalized_represents_hyperbolic_of_firstNormTwo
    (hfirst : ordUnit K S.firstNormGenerator =
      (ramificationIndex K : Int)) :
    S.targetFirstNormalized.Represents
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ)) := by
  have heven := S.firstNormWeightParity_even_of_firstNormTwo hfirst
  have hevenTarget : Even
      (ordUnit K S.firstNormGenerator +
        weightIdealOrder S.targetFirstNormalized
          (S.targetJordan.component 0).lattice) := by
    unfold firstNormWeightParity at heven
    simpa only [S.firstNormalized_weightIdealOrder_eq] using heven
  let target := omeara9318iiData S.targetFirstNormalized_unimodular
    (by rw [S.targetFirstNormalized_finrank]; omega)
    S.firstNormGenerator S.firstNormGenerator_target hevenTarget
  exact ⟨target.displayedIsometry.symm.toQuadraticSpaceIsometry
    |>.toRepresentation |>.trans
      (QuadraticSpace.Representation.orthogonalSumInl
        (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
        (target.decomposition.component 1).space)⟩

/-- The normalized target head is the standard two-plane hyperbolic tower in
Step 5. -/
theorem targetFirstNormalized_isHyperbolic_of_firstNormTwo
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hfirst : ordUnit K S.firstNormGenerator =
      (ramificationIndex K : Int))
    (hsecond : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    S.targetFirstNormalized.IsIsometric
      (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2) := by
  letI : Module.Finite K (S.targetJordan.component 0).carrier :=
    (S.targetJordan.component 0).lattice.moduleFinite
  have hpair :=
    QuadraticSpace.rankFour_isIsometric_hyperbolicPair_of_determinantClass_eq_one
      S.targetFirstNormalized (S.targetJordan.component 0).lattice
      S.targetFirstNormalized_finrank
      (S.targetFirstNormalized_determinantClass_eq_one_of_firstNormTwo
        A conditions hfirst hsecond)
      (S.targetFirstNormalized_represents_hyperbolic_of_firstNormTwo hfirst)
  let hyperbolicToZero :=
    (scaledZeroOmearaPlaneLatticeIsometry (K := K) (1 : Kˣ)).symm
      |>.toQuadraticSpaceIsometry
  let pairToTower :=
    (hyperbolicToZero.orthogonalSum hyperbolicToZero).trans
      (twoZeroPlaneProductToTowerTwoSpaceIsometry (K := K))
  rcases hpair with ⟨f⟩
  exact ⟨f.trans pairToTower⟩

/-- Complete Step-5 head alignment.  No target Jordan replacement is needed:
the original normalized target head is already hyperbolic. -/
noncomputable def firstNormTwoHeadAlignedReplacement
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hfirst : ordUnit K S.firstNormGenerator =
      (ramificationIndex K : Int))
    (hsecond : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    Omeara9328HeadAlignedReplacement S.sourceJordan S.targetJordan A := by
  let targetToTower := Classical.choice
    (S.targetFirstNormalized_isHyperbolic_of_firstNormTwo
      A conditions hfirst hsecond)
  let normalized : QuadraticSpace.Isometry S.sourceFirstNormalized
      S.targetFirstNormalized :=
    S.sourceFirstNormalizedHyperbolicTowerIsometry.trans targetToTower.symm
  let scaled := normalized.rescaleUnitBoth S.firstScale
  let undoSource := undoInverseRescaleLatticeIsometry
    (S.sourceJordan.component 0).space
    (S.sourceJordan.component 0).lattice S.firstScale
  let undoTarget := undoInverseRescaleLatticeIsometry
    (S.targetJordan.component 0).space
    (S.targetJordan.component 0).lattice S.firstScale
  have headSpace : (S.sourceJordan.component 0).space.IsIsometric
      (S.targetJordan.component 0).space :=
    ⟨undoSource.symm.toQuadraticSpaceIsometry.trans
      (scaled.trans undoTarget.toQuadraticSpaceIsometry)⟩
  exact headAlignedReplacementOfHeadSpaceIsometry
    S.sourceJordan S.targetJordan S.sourceJordan_isSaturated
      S.targetJordan_isSaturated S.residualFundamentalType A conditions
        headSpace

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
