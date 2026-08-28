/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328FirstFundamentalIdealCases
import Bong.Lattice.Omeara9319ZeroLeftExchange
import Bong.Lattice.OmearaGeneralPlaneNormAbsorption
import Bong.Lattice.Omeara9318ComplementInvariants
import Bong.Lattice.Omeara9318OddRankFiveSix
import Bong.Lattice.OmearaHyperbolicCancellation
import Bong.Lattice.Omeara9328CoefficientShiftReplacement

/-!
# Determinant correction when `U₂ = U₁` in O'Meara 93:28

This is the first half of Step 4.  Starting from an error
`z = a₂ lambda`, first use 93:13 to change an adjoined hyperbolic plane
to `A(-lambda,0)`.  Then use 93:19 and the represented norm generator
`a₂` to obtain `A(-lambda,a₂)`.  The latter plane together with the
old quaternary head has a displayed hyperbolic summand by 93:18(v); 93:14
cancels the originally adjoined plane.  The remaining two components keep
their Jordan scale and norm ideals.
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

namespace Omeara9328RankFourReductionSystem.EqualNormOrderErrorData

variable {S : Omeara9328RankFourReductionSystem J H}
  {z : K} (D : S.EqualNormOrderErrorData z)

/-- The zero-left 93:19 setup on the normalized second component. -/
noncomputable def exchangeSetup :
    Omeara9319ExchangeSetup S.targetSecondNormalized
      (S.targetJordan.component 1).lattice S.relativeSecondScale :=
  Omeara9319ExchangeSetup.zeroLeft
    S.targetSecondNormalized_modular
    (by rw [S.targetSecondNormalized_finrank]; omega)
    D.coefficient D.coefficient_integral
    S.relativeSecondScale_isInMaximalIdeal
    D.secondGenerator
    D.secondGenerator_targetSecond.1

/-- The new coefficient of the exchanged plane is the chosen second norm
generator. -/
theorem exchangeSetup_newCoefficient :
    D.exchangeSetup.alpha +
        (S.relativeSecondScale : K) * D.exchangeSetup.gamma =
      (D.secondGenerator : K) := by
  exact Omeara9319ExchangeSetup.zeroLeft_newCoefficient
    S.targetSecondNormalized_modular
    (by rw [S.targetSecondNormalized_finrank]; omega)
    D.coefficient D.coefficient_integral
    S.relativeSecondScale_isInMaximalIdeal
    D.secondGenerator
    D.secondGenerator_targetSecond.1

/-- The exchanged plane is unimodular. -/
theorem newPlane_unimodular :
    IsModular D.exchangeSetup.newPlane
      (hyperbolicPlaneLattice (K := K)) (1 : Kˣ) := by
  apply omearaGeneralPlane_isModular_one
  · exact (IntegerRing K).toSubring.add_mem
      D.exchangeSetup.alpha_integral
      ((IntegerRing K).toSubring.mul_mem
        (D.exchangeSetup.scale_integral)
        D.exchangeSetup.gamma_integral)
  · exact D.exchangeSetup.beta_integral
  · exact D.exchangeSetup.new_determinant_unit

/-- Every norm of the exchanged plane is absorbed by the normalized target
first component. -/
theorem newPlane_normGroupSet_subset_targetFirst :
    normGroupSet D.exchangeSetup.newPlane
        (hyperbolicPlaneLattice (K := K)) ⊆
      normGroupSet S.targetFirstNormalized
        (S.targetJordan.component 0).lattice := by
  unfold Omeara9319ExchangeSetup.newPlane
  apply normGroupSet_omearaGeneralPlane_subset_of_coefficients_mem
  · exact (IntegerRing K).toSubring.add_mem
      D.exchangeSetup.alpha_integral
      ((IntegerRing K).toSubring.mul_mem
        D.exchangeSetup.scale_integral D.exchangeSetup.gamma_integral)
  · exact D.exchangeSetup.beta_integral
  · exact D.exchangeSetup.new_determinant_unit
  · exact S.targetFirstNormalized_unimodular
  · rw [S.targetFirstNormalized_finrank]
    omega
  · rw [D.exchangeSetup_newCoefficient]
    exact D.secondGenerator_mem_targetFirst
  · have hneg := neg_mem_normGroupSet S.targetFirstNormalized
        (S.targetJordan.component 0).lattice
        D.coefficient_mem_targetFirst
    simpa only [exchangeSetup, Omeara9319ExchangeSetup.zeroLeft_beta] using hneg

/-- Six-dimensional lattice from the new plane and the old quaternary
head. -/
noncomputable abbrev headAmbient : QuadraticSpace K
    ((Fin 2 → K) × (S.targetJordan.component 0).carrier) :=
  D.exchangeSetup.newPlane.orthogonalSum S.targetFirstNormalized

noncomputable abbrev headAmbientLattice
    (_D : S.EqualNormOrderErrorData z) : Lattice K
    ((Fin 2 → K) × (S.targetJordan.component 0).carrier) :=
  product (hyperbolicPlaneLattice (K := K))
    (S.targetJordan.component 0).lattice

theorem headAmbient_unimodular :
    IsModular D.headAmbient D.headAmbientLattice (1 : Kˣ) :=
  D.newPlane_unimodular.orthogonalProduct
    S.targetFirstNormalized_unimodular

theorem headAmbient_finrank :
    finrank K ((Fin 2 → K) ×
      (S.targetJordan.component 0).carrier) = 6 := by
  letI : Module.Finite K (S.targetJordan.component 0).carrier :=
    (S.targetJordan.component 0).lattice.moduleFinite
  rw [Module.finrank_prod, Module.finrank_fin_fun,
    S.targetFirstNormalized_finrank]

/-- Adding the exchanged plane does not enlarge the head norm group. -/
theorem headAmbient_normGroupSet_eq :
    normGroupSet D.headAmbient D.headAmbientLattice =
      normGroupSet S.targetFirstNormalized
        (S.targetJordan.component 0).lattice := by
  ext a
  rw [mem_normGroupSet_orthogonalProduct_iff]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact add_mem_normGroupSet S.targetFirstNormalized
      (S.targetJordan.component 0).lattice
      (D.newPlane_normGroupSet_subset_targetFirst hx) hy
  · intro ha
    exact ⟨0, zero_mem_normGroupSet D.exchangeSetup.newPlane
      (hyperbolicPlaneLattice (K := K)), a, ha, by simp⟩

/-- 93:18(v) splits one standard hyperbolic plane from the corrected
six-dimensional head. -/
noncomputable def headSplit :
    Omeara9318vData D.headAmbient D.headAmbientLattice (1 : Kˣ) :=
  omeara9318vDataUnimodular D.headAmbient D.headAmbientLattice
    D.headAmbient_unimodular (by rw [headAmbient_finrank (S := S)]; omega)

theorem headSplit_complement_finrank :
    finrank K (D.headSplit.decomposition.component 1).carrier = 4 := by
  rw [D.headSplit.complement_finrank, headAmbient_finrank (S := S)]

/-- The new quaternary complement has exactly the old first norm group. -/
theorem headSplit_complement_normGroupSet_eq :
    normGroupSet (D.headSplit.decomposition.component 1).space
        (D.headSplit.decomposition.component 1).lattice =
      normGroupSet S.targetFirstNormalized
        (S.targetJordan.component 0).lattice := by
  rw [D.headSplit.complement_normGroupSet_eq
    (by rw [D.headSplit_complement_finrank]; omega),
    D.headAmbient_normGroupSet_eq]

/-- The complete 93:19 shift on the normalized second component. -/
noncomputable def tailShift :
    Omeara9319ExchangeSetup.Omeara9319Data D.exchangeSetup :=
  D.exchangeSetup.coefficientShift S.targetSecondNormalized_modular
    (by rw [S.targetSecondNormalized_finrank]; omega)

/-- Corrected normalized first component. -/
noncomputable abbrev newHead : QuadraticSpace K
    (D.headSplit.decomposition.component 1).carrier :=
  (D.headSplit.decomposition.component 1).space

noncomputable abbrev newHeadLattice : Lattice K
    (D.headSplit.decomposition.component 1).carrier :=
  (D.headSplit.decomposition.component 1).lattice

/-- Corrected normalized second component. -/
noncomputable abbrev newTail : QuadraticSpace K
    (D.tailShift.splitting.decomposition.component 1).carrier :=
  (D.tailShift.splitting.decomposition.component 1).space

noncomputable abbrev newTailLattice : Lattice K
    (D.tailShift.splitting.decomposition.component 1).carrier :=
  (D.tailShift.splitting.decomposition.component 1).lattice

/-- The binary exchange complement has the old second norm ideal. -/
theorem exchangeComplement_normIdeal_eq :
    normIdeal D.exchangeSetup.exchangeComplement
        (hyperbolicPlaneLattice (K := K)) =
      principalIdeal (K := K) (D.secondGenerator : K) := by
  exact Omeara9319ExchangeSetup.zeroLeft_exchangeComplement_normIdeal_eq
    S.targetSecondNormalized_modular
    (by rw [S.targetSecondNormalized_finrank]; omega)
    D.coefficient D.coefficient_integral
    S.relativeSecondScale_isInMaximalIdeal
    D.secondGenerator
    D.secondGenerator_targetSecond
    D.coefficient_mul_relativeScale_sq_mem_secondGeneratorIdeal

/-- The six-dimensional tail ambient before 93:18(v). -/
noncomputable abbrev tailAmbient : QuadraticSpace K
    ((Fin 2 → K) × (S.targetJordan.component 1).carrier) :=
  D.exchangeSetup.exchangeComplement.orthogonalSum S.targetSecondNormalized

noncomputable abbrev tailAmbientLattice
    (_D : S.EqualNormOrderErrorData z) : Lattice K
    ((Fin 2 → K) × (S.targetJordan.component 1).carrier) :=
  product (hyperbolicPlaneLattice (K := K))
    (S.targetJordan.component 1).lattice

theorem tailAmbient_normIdeal_eq :
    normIdeal D.tailAmbient D.tailAmbientLattice =
      principalIdeal (K := K) (D.secondGenerator : K) := by
  rw [normIdeal_orthogonalProduct, D.exchangeComplement_normIdeal_eq,
    D.secondGenerator_targetSecond.2, sup_idem]

theorem tailAmbient_finrank :
    finrank K ((Fin 2 → K) ×
      (S.targetJordan.component 1).carrier) = 6 := by
  letI : Module.Finite K (S.targetJordan.component 1).carrier :=
    (S.targetJordan.component 1).lattice.moduleFinite
  rw [Module.finrank_prod, Module.finrank_fin_fun,
    S.targetSecondNormalized_finrank]

theorem tailShift_complement_finrank :
    finrank K
      (D.tailShift.splitting.decomposition.component 1).carrier = 4 := by
  rw [D.tailShift.splitting.complement_finrank,
    tailAmbient_finrank (S := S)]

/-- The final 93:19 complement has the old second norm group. -/
theorem tailShift_complement_normGroupSet_eq :
    normGroupSet
        (D.tailShift.splitting.decomposition.component 1).space
        (D.tailShift.splitting.decomposition.component 1).lattice =
      normGroupSet D.tailAmbient D.tailAmbientLattice := by
  exact D.tailShift.splitting.complement_normGroupSet_eq
    (by rw [D.tailShift_complement_finrank]; omega)

/-- The corrected quaternary head has the original normalized first norm
ideal. -/
theorem headSplit_complement_normIdeal_eq :
    normIdeal (D.headSplit.decomposition.component 1).space
        (D.headSplit.decomposition.component 1).lattice =
      principalIdeal (K := K) (S.firstNormGenerator : K) := by
  have hexists : ∃ a : Kˣ, IsNormGeneratorValue
      (D.headSplit.decomposition.component 1).space
      (D.headSplit.decomposition.component 1).lattice a := by
    rcases exists_isNormGenerator_of_finrank_pos
        (D.headSplit.decomposition.component 1).space
        (D.headSplit.decomposition.component 1).lattice
        (by rw [D.headSplit_complement_finrank]; omega) with
      ⟨x, hx, hne⟩
    exact ⟨Units.mk0
      ((D.headSplit.decomposition.component 1).space.quadratic x) hne,
      hx.isNormGeneratorValue hne⟩
  have hgen := isNormGeneratorValue_of_normGroupSet_eq
    S.firstNormGenerator_target
    D.headSplit_complement_normGroupSet_eq.symm hexists
  exact hgen.2

theorem headSplit_complement_firstNormGenerator :
    IsNormGeneratorValue D.newHead D.newHeadLattice
      S.firstNormGenerator := by
  exact ⟨by
      rw [D.headSplit_complement_normGroupSet_eq]
      exact S.firstNormGenerator_target.1,
    D.headSplit_complement_normIdeal_eq⟩

/-- The final 93:19 complement has the original normalized second norm
ideal. -/
theorem tailShift_complement_normIdeal_eq :
    normIdeal
        (D.tailShift.splitting.decomposition.component 1).space
        (D.tailShift.splitting.decomposition.component 1).lattice =
      principalIdeal (K := K)
        (D.secondGenerator : K) := by
  have hdeltaAmbient : (D.secondGenerator : K) ∈
      normGroupSet D.tailAmbient D.tailAmbientLattice := by
    rw [mem_normGroupSet_orthogonalProduct_iff]
    exact ⟨0, zero_mem_normGroupSet D.exchangeSetup.exchangeComplement
      (hyperbolicPlaneLattice (K := K)),
      (D.secondGenerator : K),
      D.secondGenerator_targetSecond.1, by simp⟩
  have hgenAmbient : IsNormGeneratorValue D.tailAmbient
      D.tailAmbientLattice D.secondGenerator :=
    ⟨hdeltaAmbient, D.tailAmbient_normIdeal_eq⟩
  have hexists : ∃ a : Kˣ, IsNormGeneratorValue
      (D.tailShift.splitting.decomposition.component 1).space
      (D.tailShift.splitting.decomposition.component 1).lattice a := by
    rcases exists_isNormGenerator_of_finrank_pos
        (D.tailShift.splitting.decomposition.component 1).space
        (D.tailShift.splitting.decomposition.component 1).lattice
        (by rw [D.tailShift_complement_finrank]; omega) with
      ⟨x, hx, hne⟩
    exact ⟨Units.mk0
      ((D.tailShift.splitting.decomposition.component 1).space.quadratic x)
        hne, hx.isNormGeneratorValue hne⟩
  have hgen := isNormGeneratorValue_of_normGroupSet_eq hgenAmbient
    D.tailShift_complement_normGroupSet_eq.symm hexists
  exact hgen.2

theorem tailShift_complement_secondNormGenerator :
    IsNormGeneratorValue D.newTail D.newTailLattice
      D.secondGenerator := by
  constructor
  · apply D.tailShift.normGroup_subset
    exact D.secondGenerator_targetSecond.1
  · exact D.tailShift_complement_normIdeal_eq

/-- The coefficient used by 93:13 belongs to the scale-one truncation of
the normalized target first component. -/
theorem coefficient_mem_targetFirst_scaleTruncation :
    D.coefficient ∈ normGroupSet S.targetFirstNormalized
      (omearaScaleTruncation S.targetFirstNormalized
        (S.targetJordan.component 0).lattice (1 : Kˣ)) := by
  rw [omearaScaleTruncation_eq_of_isModular
    S.targetFirstNormalized_unimodular]
  exact D.coefficient_mem_targetFirst

/-- The first 93:13 move changes the adjoined hyperbolic plane into
`A(-lambda,0)` while leaving the old first component fixed. -/
noncomputable def insertCoefficient :
    Isometry
      (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum S.targetFirstNormalized)
      (((QuadraticSpace.omearaPlane (-D.coefficient)).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum S.targetFirstNormalized)
      (product (hyperbolicPlaneLattice (K := K))
        (S.targetJordan.component 0).lattice)
      (product (hyperbolicPlaneLattice (K := K))
        (S.targetJordan.component 0).lattice) := by
  let f := omeara9313 S.targetFirstNormalized
    (S.targetJordan.component 0).lattice (1 : Kˣ)
    (-D.coefficient) D.coefficient
    D.coefficient_mem_targetFirst_scaleTruncation
  simpa only [Units.val_inv_eq_inv_val, Units.val_one, inv_one, one_mul,
    neg_add_cancel] using f

/-- Identify the old plane of the 93:19 package with the plane produced by
the preceding 93:13 move. -/
noncomputable def oldPlaneToNegativeCoefficient :
    Isometry D.exchangeSetup.oldPlane
      ((QuadraticSpace.omearaPlane (-D.coefficient)).rescaleUnit (1 : Kˣ))
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) :=
  Omeara9319ExchangeSetup.zeroLeftOldPlaneToNegativeCoefficient
    S.targetSecondNormalized_modular
    (by rw [S.targetSecondNormalized_finrank]; omega)
    D.coefficient D.coefficient_integral
    S.relativeSecondScale_isInMaximalIdeal
    D.secondGenerator
    D.secondGenerator_targetSecond.1

/-- The complete stabilized calculation before applying 93:14. -/
noncomputable def stabilizedPairIsometry :
    Isometry
      (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum
          (S.targetFirstNormalized.orthogonalSum S.targetSecondNormalized))
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
        (D.newHead.orthogonalSum D.newTail))
      (product (hyperbolicPlaneLattice (K := K))
        (product (S.targetJordan.component 0).lattice
          (S.targetJordan.component 1).lattice))
      (product (hyperbolicPlaneLattice (K := K))
        (product D.newHeadLattice D.newTailLattice)) := by
  let firstIdentity := Isometry.refl S.targetFirstNormalized
    (S.targetJordan.component 0).lattice
  let secondIdentity := Isometry.refl S.targetSecondNormalized
    (S.targetJordan.component 1).lattice
  let newTailIdentity := Isometry.refl D.newTail D.newTailLattice
  let exposeFirst : Isometry
      (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum
          (S.targetFirstNormalized.orthogonalSum S.targetSecondNormalized))
      ((((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum S.targetFirstNormalized).orthogonalSum
          S.targetSecondNormalized)
      (product (hyperbolicPlaneLattice (K := K))
        (product (S.targetJordan.component 0).lattice
          (S.targetJordan.component 1).lattice))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (S.targetJordan.component 0).lattice)
        (S.targetJordan.component 1).lattice) :=
    orthogonalProductAssoc.symm
  let changeCoefficient : Isometry
      ((((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum S.targetFirstNormalized).orthogonalSum
          S.targetSecondNormalized)
      ((((QuadraticSpace.omearaPlane (-D.coefficient)).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum S.targetFirstNormalized).orthogonalSum
          S.targetSecondNormalized)
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (S.targetJordan.component 0).lattice)
        (S.targetJordan.component 1).lattice)
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (S.targetJordan.component 0).lattice)
        (S.targetJordan.component 1).lattice) :=
    D.insertCoefficient.orthogonalProductBasic secondIdentity
  let identifyOldPlane : Isometry
      ((((QuadraticSpace.omearaPlane (-D.coefficient)).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum S.targetFirstNormalized).orthogonalSum
          S.targetSecondNormalized)
      ((D.exchangeSetup.oldPlane.orthogonalSum S.targetFirstNormalized)
        |>.orthogonalSum S.targetSecondNormalized)
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (S.targetJordan.component 0).lattice)
        (S.targetJordan.component 1).lattice)
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (S.targetJordan.component 0).lattice)
        (S.targetJordan.component 1).lattice) :=
    (D.oldPlaneToNegativeCoefficient.symm
      |>.orthogonalProductBasic firstIdentity)
      |>.orthogonalProductBasic secondIdentity
  let associateOld : Isometry
      ((D.exchangeSetup.oldPlane.orthogonalSum S.targetFirstNormalized)
        |>.orthogonalSum S.targetSecondNormalized)
      (D.exchangeSetup.oldPlane.orthogonalSum
        (S.targetFirstNormalized.orthogonalSum S.targetSecondNormalized))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (S.targetJordan.component 0).lattice)
        (S.targetJordan.component 1).lattice)
      (product (hyperbolicPlaneLattice (K := K))
        (product (S.targetJordan.component 0).lattice
          (S.targetJordan.component 1).lattice)) :=
    orthogonalProductAssoc
  let rotateOld : Isometry
      (D.exchangeSetup.oldPlane.orthogonalSum
        (S.targetFirstNormalized.orthogonalSum S.targetSecondNormalized))
      ((S.targetFirstNormalized.orthogonalSum D.exchangeSetup.oldPlane)
        |>.orthogonalSum S.targetSecondNormalized)
      (product (hyperbolicPlaneLattice (K := K))
        (product (S.targetJordan.component 0).lattice
          (S.targetJordan.component 1).lattice))
      (product
        (product (S.targetJordan.component 0).lattice
          (hyperbolicPlaneLattice (K := K)))
        (S.targetJordan.component 1).lattice) :=
    orthogonalProductRotateLeft
  let hideOld : Isometry
      ((S.targetFirstNormalized.orthogonalSum D.exchangeSetup.oldPlane)
        |>.orthogonalSum S.targetSecondNormalized)
      (S.targetFirstNormalized.orthogonalSum
        (D.exchangeSetup.oldPlane.orthogonalSum S.targetSecondNormalized))
      (product
        (product (S.targetJordan.component 0).lattice
          (hyperbolicPlaneLattice (K := K)))
        (S.targetJordan.component 1).lattice)
      (product (S.targetJordan.component 0).lattice
        (product (hyperbolicPlaneLattice (K := K))
          (S.targetJordan.component 1).lattice)) :=
    orthogonalProductAssoc
  let shiftTail : Isometry
      (S.targetFirstNormalized.orthogonalSum
        (D.exchangeSetup.oldPlane.orthogonalSum S.targetSecondNormalized))
      (S.targetFirstNormalized.orthogonalSum
        (D.exchangeSetup.newPlane.orthogonalSum D.newTail))
      (product (S.targetJordan.component 0).lattice
        (product (hyperbolicPlaneLattice (K := K))
          (S.targetJordan.component 1).lattice))
      (product (S.targetJordan.component 0).lattice
        (product (hyperbolicPlaneLattice (K := K)) D.newTailLattice)) :=
    firstIdentity.orthogonalProductBasic D.tailShift.shifted
  let rotateNew : Isometry
      (S.targetFirstNormalized.orthogonalSum
        (D.exchangeSetup.newPlane.orthogonalSum D.newTail))
      ((D.exchangeSetup.newPlane.orthogonalSum S.targetFirstNormalized)
        |>.orthogonalSum D.newTail)
      (product (S.targetJordan.component 0).lattice
        (product (hyperbolicPlaneLattice (K := K)) D.newTailLattice))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (S.targetJordan.component 0).lattice)
        D.newTailLattice) :=
    orthogonalProductRotateLeft
  let splitHead : Isometry
      ((D.exchangeSetup.newPlane.orthogonalSum S.targetFirstNormalized)
        |>.orthogonalSum D.newTail)
      (((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum D.newHead)
        |>.orthogonalSum D.newTail)
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (S.targetJordan.component 0).lattice)
        D.newTailLattice)
      (product
        (product (hyperbolicPlaneLattice (K := K)) D.newHeadLattice)
        D.newTailLattice) :=
    D.headSplit.displayedIsometry.orthogonalProductBasic newTailIdentity
  let hideHead : Isometry
      (((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum D.newHead)
        |>.orthogonalSum D.newTail)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
        (D.newHead.orthogonalSum D.newTail))
      (product
        (product (hyperbolicPlaneLattice (K := K)) D.newHeadLattice)
        D.newTailLattice)
      (product (hyperbolicPlaneLattice (K := K))
        (product D.newHeadLattice D.newTailLattice)) :=
    orthogonalProductAssoc
  exact exposeFirst.trans <| changeCoefficient.trans <|
    identifyOldPlane.trans <| associateOld.trans <| rotateOld.trans <|
      hideOld.trans <| shiftTail.trans <| rotateNew.trans <|
        splitHead.trans hideHead

/-- Cancel the common normalized hyperbolic plane by the concrete theorem
93:14. -/
noncomputable def normalizedPairIsometry :
    Isometry
      (S.targetFirstNormalized.orthogonalSum S.targetSecondNormalized)
      (D.newHead.orthogonalSum D.newTail)
      (product (S.targetJordan.component 0).lattice
        (S.targetJordan.component 1).lattice)
      (product D.newHeadLattice D.newTailLattice) := by
  exact omeara9314_scaled_of_isometric_summand (1 : Kˣ)
    (scaledZeroOmearaPlaneLatticeIsometry (1 : Kˣ))
    (Isometry.refl (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
      (hyperbolicPlaneLattice (K := K)))
    D.stabilizedPairIsometry

/-- Corrected first component at the original Jordan scale. -/
noncomputable abbrev newHeadUnnormalized : QuadraticSpace K
    (D.headSplit.decomposition.component 1).carrier :=
  D.newHead.rescaleUnit S.firstScale

/-- Corrected second component at the original Jordan scale. -/
noncomputable abbrev newTailUnnormalized : QuadraticSpace K
    (D.tailShift.splitting.decomposition.component 1).carrier :=
  D.newTail.rescaleUnit S.firstScale

/-- Undo the first-scale normalization on the complete corrected pair. -/
noncomputable def originalPairIsometry :
    Isometry
      ((S.targetJordan.component 0).space.orthogonalSum
        (S.targetJordan.component 1).space)
      (D.newHeadUnnormalized.orthogonalSum D.newTailUnnormalized)
      (product (S.targetJordan.component 0).lattice
        (S.targetJordan.component 1).lattice)
      (product D.newHeadLattice D.newTailLattice) := by
  let scaled := D.normalizedPairIsometry.rescaleUnitBoth S.firstScale
  let distributeSource := rescaleUnitOrthogonalProductIsometry
    S.targetFirstNormalized S.targetSecondNormalized
    (S.targetJordan.component 0).lattice
    (S.targetJordan.component 1).lattice S.firstScale
  let undoFirstRaw := rescaleUnitMulLatticeIsometry
    (S.targetJordan.component 0).space
    (S.targetJordan.component 0).lattice S.firstScale⁻¹ S.firstScale
  let undoFirst : Isometry
      (S.targetFirstNormalized.rescaleUnit S.firstScale)
      (S.targetJordan.component 0).space
      (S.targetJordan.component 0).lattice
      (S.targetJordan.component 0).lattice := by
    have hscale : S.firstScale * S.firstScale⁻¹ = (1 : Kˣ) := by simp
    let finish : Isometry
        ((S.targetJordan.component 0).space.rescaleUnit
          (S.firstScale * S.firstScale⁻¹))
        (S.targetJordan.component 0).space
        (S.targetJordan.component 0).lattice
        (S.targetJordan.component 0).lattice := by
      simpa only [hscale] using Isometry.rescaleUnitOne
        (S.targetJordan.component 0).space
        (S.targetJordan.component 0).lattice
    simpa only [targetFirstNormalized] using undoFirstRaw.trans finish
  let undoSecondRaw := rescaleUnitMulLatticeIsometry
    (S.targetJordan.component 1).space
    (S.targetJordan.component 1).lattice S.firstScale⁻¹ S.firstScale
  let undoSecond : Isometry
      (S.targetSecondNormalized.rescaleUnit S.firstScale)
      (S.targetJordan.component 1).space
      (S.targetJordan.component 1).lattice
      (S.targetJordan.component 1).lattice := by
    have hscale : S.firstScale * S.firstScale⁻¹ = (1 : Kˣ) := by simp
    let finish : Isometry
        ((S.targetJordan.component 1).space.rescaleUnit
          (S.firstScale * S.firstScale⁻¹))
        (S.targetJordan.component 1).space
        (S.targetJordan.component 1).lattice
        (S.targetJordan.component 1).lattice := by
      simpa only [hscale] using Isometry.rescaleUnitOne
        (S.targetJordan.component 1).space
        (S.targetJordan.component 1).lattice
    simpa only [targetSecondNormalized] using undoSecondRaw.trans finish
  let undoSource := distributeSource.trans
    (undoFirst.orthogonalProductBasic undoSecond)
  let distributeTarget := rescaleUnitOrthogonalProductIsometry
    D.newHead D.newTail D.newHeadLattice D.newTailLattice S.firstScale
  exact undoSource.symm.trans (scaled.trans distributeTarget)

/-- Undoing the normalization restores the original second Jordan scale. -/
theorem firstScale_mul_relativeSecondScale :
    S.firstScale * S.relativeSecondScale =
      S.targetJordan.scaleGenerator 1 := by
  unfold Omeara9328RankFourReductionSystem.firstScale
    Omeara9328RankFourReductionSystem.relativeSecondScale
  rw [S.targetJordan_scaleGenerator]
  group

/-- The chosen normalized first norm generator, restored to the original
scale, is a norm generator for the old target head. -/
theorem targetFirst_unscaledNormGenerator :
    IsNormGeneratorValue (S.targetJordan.component 0).space
      (S.targetJordan.component 0).lattice
      (S.firstScale * S.firstNormGenerator) := by
  have h := S.firstNormGenerator_target.unscaleQuadraticUnit
  simpa only [Omeara9328RankFourReductionSystem.targetFirstNormalized,
    inv_inv] using h

/-- The analogous restored norm generator for the old target tail. -/
theorem targetSecond_unscaledNormGenerator :
    IsNormGeneratorValue (S.targetJordan.component 1).space
      (S.targetJordan.component 1).lattice
      (S.firstScale * D.secondGenerator) := by
  have h := D.secondGenerator_targetSecond.unscaleQuadraticUnit
  simpa only [Omeara9328RankFourReductionSystem.targetSecondNormalized,
    inv_inv] using h

/-- The corrected head remains modular at the first Jordan scale after
undoing normalization. -/
theorem newHeadUnnormalized_modular :
    IsModular D.newHeadUnnormalized D.newHeadLattice
      (S.targetJordan.scaleGenerator 0) := by
  have h := D.headSplit.complement_modular.rescaleQuadraticUnit S.firstScale
  simpa only [newHeadUnnormalized,
    S.targetJordan_scaleGenerator,
    Omeara9328RankFourReductionSystem.firstScale, mul_one] using h

/-- The corrected tail remains modular at the second Jordan scale. -/
theorem newTailUnnormalized_modular :
    IsModular D.newTailUnnormalized D.newTailLattice
      (S.targetJordan.scaleGenerator 1) := by
  have h := D.tailShift.splitting.complement_modular
    |>.rescaleQuadraticUnit S.firstScale
  simpa only [newTailUnnormalized,
    firstScale_mul_relativeSecondScale (S := S)] using h

/-- Restored norm generator for the corrected head. -/
theorem newHeadUnnormalized_normGenerator :
    IsNormGeneratorValue D.newHeadUnnormalized D.newHeadLattice
      (S.firstScale * S.firstNormGenerator) :=
  D.headSplit_complement_firstNormGenerator.rescaleQuadraticUnit S.firstScale

/-- Restored norm generator for the corrected tail. -/
theorem newTailUnnormalized_normGenerator :
    IsNormGeneratorValue D.newTailUnnormalized D.newTailLattice
      (S.firstScale * D.secondGenerator) :=
  D.tailShift_complement_secondNormGenerator.rescaleQuadraticUnit S.firstScale

/-- Scale ideal of the corrected head at the original normalization. -/
theorem newHeadUnnormalized_scaleIdeal :
    scaleIdeal D.newHeadUnnormalized D.newHeadLattice =
      principalIdeal (K := K) (S.targetJordan.scaleGenerator 0 : K) :=
  D.newHeadUnnormalized_modular.scaleIdeal_eq_principal
    (by rw [D.headSplit_complement_finrank]; omega)

/-- Scale ideal of the corrected tail at the original normalization. -/
theorem newTailUnnormalized_scaleIdeal :
    scaleIdeal D.newTailUnnormalized D.newTailLattice =
      principalIdeal (K := K) (S.targetJordan.scaleGenerator 1 : K) :=
  D.newTailUnnormalized_modular.scaleIdeal_eq_principal
    (by rw [D.tailShift_complement_finrank]; omega)

/-- Norm ideal of the corrected head agrees with the old first Jordan norm
ideal. -/
theorem newHeadUnnormalized_normIdeal :
    normIdeal D.newHeadUnnormalized D.newHeadLattice =
      principalIdeal (K := K) (S.targetJordan.normGenerator 0 : K) := by
  calc
    normIdeal D.newHeadUnnormalized D.newHeadLattice =
        principalIdeal (K := K)
          ((S.firstScale * S.firstNormGenerator : Kˣ) : K) :=
      D.newHeadUnnormalized_normGenerator.2
    _ = normIdeal (S.targetJordan.component 0).space
        (S.targetJordan.component 0).lattice :=
      (targetFirst_unscaledNormGenerator (S := S)).2.symm
    _ = principalIdeal (K := K) (S.targetJordan.normGenerator 0 : K) :=
      S.targetJordan.normIdeal_eq 0

/-- Norm ideal of the corrected tail agrees with the old second Jordan norm
ideal. -/
theorem newTailUnnormalized_normIdeal :
    normIdeal D.newTailUnnormalized D.newTailLattice =
      principalIdeal (K := K) (S.targetJordan.normGenerator 1 : K) := by
  calc
    normIdeal D.newTailUnnormalized D.newTailLattice =
        principalIdeal (K := K)
          ((S.firstScale * D.secondGenerator : Kˣ) : K) :=
      D.newTailUnnormalized_normGenerator.2
    _ = normIdeal (S.targetJordan.component 1).space
        (S.targetJordan.component 1).lattice :=
      D.targetSecond_unscaledNormGenerator.2.symm
    _ = principalIdeal (K := K) (S.targetJordan.normGenerator 1 : K) :=
      S.targetJordan.normIdeal_eq 1

/-- The corrected head contains the complete old first-component norm
group, after restoring the common scale. -/
theorem targetFirst_normGroupSet_subset_newHeadUnnormalized :
    normGroupSet (S.targetJordan.component 0).space
        (S.targetJordan.component 0).lattice ⊆
      normGroupSet D.newHeadUnnormalized D.newHeadLattice := by
  intro a ha
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
  rw [D.headSplit_complement_normGroupSet_eq]
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
  simpa only [Units.val_inv_eq_inv_val, inv_inv, ← mul_assoc,
    mul_inv_cancel₀ (Units.ne_zero S.firstScale), one_mul] using ha

/-- The corrected tail contains the complete old second-component norm
group, by the norm containment in 93:19. -/
theorem targetSecond_normGroupSet_subset_newTailUnnormalized :
    normGroupSet (S.targetJordan.component 1).space
        (S.targetJordan.component 1).lattice ⊆
      normGroupSet D.newTailUnnormalized D.newTailLattice := by
  intro a ha
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
  apply D.tailShift.normGroup_subset
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
  simpa only [Units.val_inv_eq_inv_val, inv_inv, ← mul_assoc,
    mul_inv_cancel₀ (Units.ne_zero S.firstScale), one_mul] using ha

/-- View the corrected displayed pair as a decomposition of the original
target Jordan first-pair sublattice. -/
noncomputable def firstPairReplacementIsometry :
    Isometry
      (D.newHeadUnnormalized.orthogonalSum D.newTailUnnormalized)
      S.targetJordan.firstPairSublattice.space
      (product D.newHeadLattice D.newTailLattice)
      S.targetJordan.firstPairSublattice.lattice :=
  D.originalPairIsometry.symm.trans
    (S.targetJordan.toOrthogonalDecomposition.orthogonalSupLatticeIsometry
      firstIndex_ne_secondIndex)

/-- Install the equal-order determinant correction into the target Jordan
splitting.  This is the complete geometric first half of O'Meara 93:28,
Step 4: no local-law parameter remains in the replacement construction. -/
noncomputable def jordanReplacement :
    Omeara9319JordanReplacement S.targetJordan := by
  let f := D.firstPairReplacementIsometry
  let T := S.targetJordan.replaceFirstPairOfIsometry f
    D.newHeadUnnormalized_modular D.newTailUnnormalized_modular
    D.newHeadUnnormalized_scaleIdeal D.newTailUnnormalized_scaleIdeal
    D.newHeadUnnormalized_normIdeal D.newTailUnnormalized_normIdeal
  exact
    { target := T
      fundamentalType :=
        S.targetJordan.replaceFirstPairOfIsometry_sameFundamentalType f
          D.newHeadUnnormalized_modular D.newTailUnnormalized_modular
          D.newHeadUnnormalized_scaleIdeal D.newTailUnnormalized_scaleIdeal
          D.newHeadUnnormalized_normIdeal D.newTailUnnormalized_normIdeal
      saturated :=
        S.targetJordan.replaceFirstPairOfIsometry_isSaturated f
          D.newHeadUnnormalized_modular D.newTailUnnormalized_modular
          D.newHeadUnnormalized_scaleIdeal D.newTailUnnormalized_scaleIdeal
          D.newHeadUnnormalized_normIdeal D.newTailUnnormalized_normIdeal
          S.targetJordan_isSaturated
          D.targetFirst_normGroupSet_subset_newHeadUnnormalized
          D.targetSecond_normGroupSet_subset_newTailUnnormalized
      laterPrefixIsometry := by
        intro k hk
        exact S.targetJordan.toOrthogonalDecomposition
          |>.replacePair_first_prefixLatticeIsometry
            (S.targetJordan.firstPairDecompositionOfIsometry f) k hk }

end Omeara9328RankFourReductionSystem.EqualNormOrderErrorData

end Lattice.JordanDecomposition

end Bong
