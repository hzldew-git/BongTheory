/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328NecessityProjectedBasis
import Bong.Lattice.Omeara9328EqualOrderDeterminantOneModels
import Bong.Lattice.OmearaGeneralPlaneNormAbsorption
import Bong.Lattice.OmearaTwoPlaneCombination
import Bong.Lattice.OmearaSaturationShift

/-!
# O'Meara 93:28 necessity: a source-head basis adapted to two planes

In Step 1 of the necessity proof, O'Meara chooses an integral basis in
which the normalized hyperbolic source head is

`A(a, 0) ⊥ A(a', 0)`,

with both displayed first coefficients generating the norm ideal.  The
construction below follows the parity split in 93:18.  In the even branch
the model `A(a,0) ⊥ A(a,0)` is obtained from O'Meara 93:16.  In the odd
branch the already classified model `A(a,0) ⊥ A(b,0)` is changed by the
explicit two-plane identity of 93:12 to
`A(a,0) ⊥ A(a+b,0)`; odd parity forces `ord(a) < ord(b)`, so `a+b`
generates the same norm ideal as `a`.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The explicit two-plane model used by Step 1 of O'Meara 93:28. -/
noncomputable def omeara9328AdaptedHeadSpace (a c : K) :
    QuadraticSpace K ((Fin 2 → K) × (Fin 2 → K)) :=
  (QuadraticSpace.omearaPlane a).orthogonalSum
    (QuadraticSpace.omearaPlane c)

/-- The standard product lattice of the adapted two-plane model. -/
noncomputable def omeara9328AdaptedHeadLattice :
    Lattice K ((Fin 2 → K) × (Fin 2 → K)) :=
  product (hyperbolicPlaneLattice (K := K))
    (hyperbolicPlaneLattice (K := K))

/-- The standard basis, ordered by the first plane and then the second. -/
noncomputable def omeara9328AdaptedHeadBasis :
    Basis (Fin 4) K ((Fin 2 → K) × (Fin 2 → K)) :=
  ((Pi.basisFun K (Fin 2)).prod (Pi.basisFun K (Fin 2))).reindex
    finSumFinEquiv

theorem basisLattice_omeara9328AdaptedHeadBasis :
    basisLattice (omeara9328AdaptedHeadBasis (K := K)) =
      omeara9328AdaptedHeadLattice (K := K) := by
  rw [omeara9328AdaptedHeadBasis, basisLattice_reindex,
    basisLattice_prod]
  rfl

@[simp]
theorem omeara9328AdaptedHeadBasis_zero :
    omeara9328AdaptedHeadBasis (K := K) 0 = (![1, 0], ![0, 0]) := by
  have hindex : (finSumFinEquiv (m := 2) (n := 2)).symm (0 : Fin 4) =
      Sum.inl (0 : Fin 2) := by
    simpa only [show (0 : Fin 4) = Fin.castAdd 2 (0 : Fin 2) by rfl] using
      (finSumFinEquiv_symm_apply_castAdd (n := 2) (0 : Fin 2))
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [omeara9328AdaptedHeadBasis, hindex, Pi.basisFun_apply]
  · funext i
    fin_cases i <;>
      simp [omeara9328AdaptedHeadBasis, hindex, Pi.basisFun_apply]

@[simp]
theorem omeara9328AdaptedHeadBasis_one :
    omeara9328AdaptedHeadBasis (K := K) 1 = (![0, 1], ![0, 0]) := by
  have hindex : (finSumFinEquiv (m := 2) (n := 2)).symm (1 : Fin 4) =
      Sum.inl (1 : Fin 2) := by
    simpa only [show (1 : Fin 4) = Fin.castAdd 2 (1 : Fin 2) by rfl] using
      (finSumFinEquiv_symm_apply_castAdd (n := 2) (1 : Fin 2))
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [omeara9328AdaptedHeadBasis, hindex, Pi.basisFun_apply]
  · funext i
    fin_cases i <;>
      simp [omeara9328AdaptedHeadBasis, hindex, Pi.basisFun_apply]

@[simp]
theorem omeara9328AdaptedHeadBasis_two :
    omeara9328AdaptedHeadBasis (K := K) 2 = (![0, 0], ![1, 0]) := by
  have hindex : (finSumFinEquiv (m := 2) (n := 2)).symm (2 : Fin 4) =
      Sum.inr (0 : Fin 2) := by
    simpa only [show (2 : Fin 4) = Fin.natAdd 2 (0 : Fin 2) by rfl] using
      (finSumFinEquiv_symm_apply_natAdd (m := 2) (0 : Fin 2))
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [omeara9328AdaptedHeadBasis, hindex, Pi.basisFun_apply]
  · funext i
    fin_cases i <;>
      simp [omeara9328AdaptedHeadBasis, hindex, Pi.basisFun_apply]

@[simp]
theorem omeara9328AdaptedHeadBasis_three :
    omeara9328AdaptedHeadBasis (K := K) 3 = (![0, 0], ![0, 1]) := by
  have hindex : (finSumFinEquiv (m := 2) (n := 2)).symm (3 : Fin 4) =
      Sum.inr (1 : Fin 2) := by
    simpa only [show (3 : Fin 4) = Fin.natAdd 2 (1 : Fin 2) by rfl] using
      (finSumFinEquiv_symm_apply_natAdd (m := 2) (1 : Fin 2))
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [omeara9328AdaptedHeadBasis, hindex, Pi.basisFun_apply]
  · funext i
    fin_cases i <;>
      simp [omeara9328AdaptedHeadBasis, hindex, Pi.basisFun_apply]

/-- The adapted model has the block Gram matrix
`A(a,0) ⊥ A(c,0)` in its standard basis. -/
theorem omeara9328AdaptedHeadBasis_bilin
    (a c : K) (i j : Fin 4) :
    (omeara9328AdaptedHeadSpace a c).bilin
        (omeara9328AdaptedHeadBasis (K := K) i)
        (omeara9328AdaptedHeadBasis (K := K) j) =
      !![a, 1, 0, 0;
         1, 0, 0, 0;
         0, 0, c, 1;
         0, 0, 1, 0] i j := by
  fin_cases i <;> fin_cases j <;>
    simp [omeara9328AdaptedHeadSpace,
      QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.omearaPlane_bilin_apply]

set_option maxHeartbeats 1000000 in
/-- The adapted product is unimodular when both displayed coefficients are
integral. -/
theorem omeara9328AdaptedHead_isModular
    (a c : K) (ha : a ∈ IntegerRing K) (hc : c ∈ IntegerRing K) :
    IsModular (omeara9328AdaptedHeadSpace a c)
      (omeara9328AdaptedHeadLattice (K := K)) (1 : Kˣ) := by
  have hgeneralA : IsModular
      (QuadraticSpace.omearaGeneralPlane a 0 (by simp))
      (hyperbolicPlaneLattice (K := K)) (1 : Kˣ) :=
    omearaGeneralPlane_isModular_one a 0 (by simp) ha
      (IntegerRing K).zero_mem (by simp [IsValuationUnit])
  have hgeneralC : IsModular
      (QuadraticSpace.omearaGeneralPlane c 0 (by simp))
      (hyperbolicPlaneLattice (K := K)) (1 : Kˣ) :=
    omearaGeneralPlane_isModular_one c 0 (by simp) hc
      (IntegerRing K).zero_mem (by simp [IsValuationUnit])
  have hA : IsModular (QuadraticSpace.omearaPlane a)
      (hyperbolicPlaneLattice (K := K)) (1 : Kˣ) :=
    hgeneralA.mapLatticeIsometry
      (omearaGeneralPlaneZeroRightLatticeIsometry (K := K) a)
  have hC : IsModular (QuadraticSpace.omearaPlane c)
      (hyperbolicPlaneLattice (K := K)) (1 : Kˣ) :=
    hgeneralC.mapLatticeIsometry
      (omearaGeneralPlaneZeroRightLatticeIsometry (K := K) c)
  exact hA.orthogonalProduct hC

/-- Every adapted two-plane model is the two-plane hyperbolic tower over
the field. -/
noncomputable def omeara9328AdaptedHeadToHyperbolicTowerSpaceIsometry
    (a c : K) :
    QuadraticSpace.Isometry (omeara9328AdaptedHeadSpace a c)
      (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2) := by
  let leftGeneral :=
    QuadraticSpace.omearaGeneralPlaneZeroRightIsometry (K := K) a
  let rightGeneral :=
    QuadraticSpace.omearaGeneralPlaneZeroRightIsometry (K := K) c
  let left := leftGeneral.symm.trans
    (omearaGeneralPlaneZeroRightToZeroPlaneSpaceIsometry (K := K) a)
  let right := rightGeneral.symm.trans
    (omearaGeneralPlaneZeroRightToZeroPlaneSpaceIsometry (K := K) c)
  exact (left.orthogonalSum right).trans
    (twoZeroPlaneProductToTowerTwoSpaceIsometry (K := K))

/-- The first displayed coefficient is in the norm group of the adapted
model. -/
theorem firstCoefficient_mem_normGroupSet_omeara9328AdaptedHead
    (a c : K) :
    a ∈ normGroupSet (omeara9328AdaptedHeadSpace a c)
      (omeara9328AdaptedHeadLattice (K := K)) := by
  have haPlane : a ∈ normGroupSet (QuadraticSpace.omearaPlane a)
      (hyperbolicPlaneLattice (K := K)) := by
    refine ⟨![1, 0], ?_, 0, Submodule.zero_mem _, ?_⟩
    · rw [mem_omearaPlaneLattice_iff]
      simp
    · rw [QuadraticSpace.quadratic,
        QuadraticSpace.omearaPlane_bilin_apply]
      simp
  change a ∈ normGroupSet
    ((QuadraticSpace.omearaPlane a).orthogonalSum
      (QuadraticSpace.omearaPlane c))
    (product (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)))
  rw [mem_normGroupSet_orthogonalProduct_iff]
  exact ⟨a, haPlane, 0,
    zero_mem_normGroupSet (QuadraticSpace.omearaPlane c)
      (hyperbolicPlaneLattice (K := K)), by simp⟩

/-- If the two coefficients of an adapted model lie in the norm group of a
positive-rank unimodular lattice, the whole model norm group is absorbed by
that lattice. -/
theorem normGroupSet_omeara9328AdaptedHead_subset
    {X : Type*} [AddCommGroup X] [Module K X]
    {p : QuadraticSpace K X} {N : Lattice K X}
    (a c : K) (ha : a ∈ IntegerRing K) (hc : c ∈ IntegerRing K)
    (hN : IsModular p N (1 : Kˣ)) (hpos : 0 < finrank K X)
    (haGroup : a ∈ normGroupSet p N)
    (hcGroup : c ∈ normGroupSet p N) :
    normGroupSet (omeara9328AdaptedHeadSpace a c)
        (omeara9328AdaptedHeadLattice (K := K)) ⊆
      normGroupSet p N := by
  have hplane (d : K) (hd : d ∈ IntegerRing K)
      (hdGroup : d ∈ normGroupSet p N) :
      normGroupSet (QuadraticSpace.omearaPlane d)
          (hyperbolicPlaneLattice (K := K)) ⊆ normGroupSet p N := by
    have hgeneral :=
      normGroupSet_omearaGeneralPlane_subset_of_coefficients_mem
        d 0 (by simp) hd (IntegerRing K).zero_mem
        (by simp [IsValuationUnit]) hN hpos hdGroup
        (zero_mem_normGroupSet p N)
    have heq :
        normGroupSet (QuadraticSpace.omearaPlane d)
            (hyperbolicPlaneLattice (K := K)) =
          normGroupSet
            (QuadraticSpace.omearaGeneralPlane d 0 (by simp))
            (hyperbolicPlaneLattice (K := K)) :=
      normGroupSet_eq_of_latticeIsometry
        (omearaGeneralPlaneZeroRightLatticeIsometry (K := K) d)
    rw [heq]
    exact hgeneral
  intro z hz
  change z ∈ normGroupSet
    ((QuadraticSpace.omearaPlane a).orthogonalSum
      (QuadraticSpace.omearaPlane c))
    (product (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K))) at hz
  rw [mem_normGroupSet_orthogonalProduct_iff] at hz
  rcases hz with ⟨x, hx, y, hy, rfl⟩
  exact add_mem_normGroupSet p N
    (hplane a ha haGroup hx) (hplane c hc hcGroup hy)

/-- The explicit 93:12 two-plane change which replaces the odd model
`A(a,0) ⊥ A(b,0)` by `A(a,0) ⊥ A(a+b,0)`. -/
noncomputable def omeara9328OddAdaptedToUntwistedModelIsometry
    (a b : K) (ha : a ∈ IntegerRing K) (hb : b ∈ IntegerRing K) :
    Isometry (omeara9328AdaptedHeadSpace a (a + b))
      (omeara9328AdaptedHeadSpace a b)
      (omeara9328AdaptedHeadLattice (K := K))
      (omeara9328AdaptedHeadLattice (K := K)) := by
  let swapSource : Isometry
      ((QuadraticSpace.omearaPlane a).orthogonalSum
        (QuadraticSpace.omearaPlane (a + b)))
      ((QuadraticSpace.omearaPlane (a + b)).orthogonalSum
        (QuadraticSpace.omearaPlane a))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K)))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K))) :=
    orthogonalProductSwap
  let squareRaw := omearaTwoPlaneSquareAddLatticeIsometry
    b a 1 ha (by simp)
  let square : Isometry
      ((QuadraticSpace.omearaPlane (a + b)).orthogonalSum
        (QuadraticSpace.omearaPlane a))
      ((QuadraticSpace.omearaPlane b).orthogonalSum
        (QuadraticSpace.omearaPlane a))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K)))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K))) := by
    simpa only [one_pow, mul_one, add_comm] using squareRaw
  let swapTarget : Isometry
      ((QuadraticSpace.omearaPlane b).orthogonalSum
        (QuadraticSpace.omearaPlane a))
      ((QuadraticSpace.omearaPlane a).orthogonalSum
        (QuadraticSpace.omearaPlane b))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K)))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K))) :=
    orthogonalProductSwap
  exact swapSource.trans (square.trans swapTarget)

end Lattice

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

/-- A concrete adapted model of the normalized source head. -/
structure SourceHeadAdaptedModelData where
  secondCoefficient : Kˣ
  secondCoefficient_integral : (secondCoefficient : K) ∈ IntegerRing K
  secondCoefficientIdeal_eq :
    principalIdeal (K := K) (secondCoefficient : K) =
      principalIdeal (K := K) (S.firstNormGenerator : K)
  sourceToModel : Isometry S.sourceFirstNormalized
    (omeara9328AdaptedHeadSpace (S.firstNormGenerator : K)
      (secondCoefficient : K))
    (S.sourceJordan.component 0).lattice
    (omeara9328AdaptedHeadLattice (K := K))

set_option maxHeartbeats 3000000 in
/-- In the even-weight branch, O'Meara 93:16 identifies the source head
with `A(a,0) ⊥ A(a,0)`. -/
noncomputable def sourceHeadEvenAdaptedModelData
    (heven : Even S.firstNormWeightParity) :
    S.SourceHeadAdaptedModelData := by
  let a : Kˣ := S.firstNormGenerator
  have haIntegral : (a : K) ∈ IntegerRing K := by
    simpa only [a] using S.firstNormGenerator_integral
  have hmodelModular : IsModular
      (omeara9328AdaptedHeadSpace (a : K) (a : K))
      (omeara9328AdaptedHeadLattice (K := K)) (1 : Kˣ) :=
    omeara9328AdaptedHead_isModular (a : K) (a : K)
      haIntegral haIntegral
  have hmodelSubset :
      normGroupSet (omeara9328AdaptedHeadSpace (a : K) (a : K))
          (omeara9328AdaptedHeadLattice (K := K)) ⊆
        normGroupSet S.sourceFirstNormalized
          (S.sourceJordan.component 0).lattice := by
    apply normGroupSet_omeara9328AdaptedHead_subset
      (a : K) (a : K) haIntegral haIntegral
      S.sourceFirstNormalized_unimodular
      (by rw [S.sourceFirstNormalized_finrank]; omega)
      S.firstNormGenerator_source.1 S.firstNormGenerator_source.1
  have hsourceSubset :
      normGroupSet S.sourceFirstNormalized
          (S.sourceJordan.component 0).lattice ⊆
        normGroupSet (omeara9328AdaptedHeadSpace (a : K) (a : K))
          (omeara9328AdaptedHeadLattice (K := K)) := by
    have hweight :
        weightIdeal S.sourceFirstNormalized
            (S.sourceJordan.component 0).lattice =
          twoScaleIdeal S.sourceFirstNormalized
            (S.sourceJordan.component 0).lattice :=
      weightIdeal_eq_twoScaleIdeal_of_even a
        S.firstNormGenerator_source (by
          simpa only [firstNormWeightParity, a] using heven)
    rw [normGroupSet_eq_integralSquareCoset_weightIdeal
      a S.firstNormGenerator_source, hweight]
    rintro z ⟨d, y, hy, rfl⟩
    have haModel : (a : K) ∈
        normGroupSet (omeara9328AdaptedHeadSpace (a : K) (a : K))
          (omeara9328AdaptedHeadLattice (K := K)) :=
      firstCoefficient_mem_normGroupSet_omeara9328AdaptedHead
        (a : K) (a : K)
    have hsquare := integralSquare_mul_mem_normGroupSet
      (omeara9328AdaptedHeadSpace (a : K) (a : K))
      (omeara9328AdaptedHeadLattice (K := K)) haModel d
    have hsquare' : (a : K) * (d : K) ^ 2 ∈
        normGroupSet (omeara9328AdaptedHeadSpace (a : K) (a : K))
          (omeara9328AdaptedHeadLattice (K := K)) := by
      simpa only [mul_comm] using hsquare
    have htwoEq :
        twoScaleIdeal S.sourceFirstNormalized
            (S.sourceJordan.component 0).lattice =
          twoScaleIdeal
            (omeara9328AdaptedHeadSpace (a : K) (a : K))
            (omeara9328AdaptedHeadLattice (K := K)) := by
      rw [twoScaleIdeal_eq_principalIdeal_two_of_unimodular
          S.sourceFirstNormalized_unimodular
          (by rw [S.sourceFirstNormalized_finrank]; omega),
        twoScaleIdeal_eq_principalIdeal_two_of_unimodular
          hmodelModular (by simp)]
    have hyModel : y ∈ twoScaleIdeal
        (omeara9328AdaptedHeadSpace (a : K) (a : K))
        (omeara9328AdaptedHeadLattice (K := K)) := by
      rw [← htwoEq]
      exact hy
    exact add_mem_normGroupSet
      (omeara9328AdaptedHeadSpace (a : K) (a : K))
      (omeara9328AdaptedHeadLattice (K := K)) hsquare'
      (twoScaleIdeal_subset_normGroupSet
        (omeara9328AdaptedHeadSpace (a : K) (a : K))
        (omeara9328AdaptedHeadLattice (K := K)) hyModel)
  have hgroup :
      normGroupSet S.sourceFirstNormalized
          (S.sourceJordan.component 0).lattice =
        normGroupSet (omeara9328AdaptedHeadSpace (a : K) (a : K))
          (omeara9328AdaptedHeadLattice (K := K)) :=
    Set.Subset.antisymm hsourceSubset hmodelSubset
  let fieldIsometry :=
    S.sourceFirstNormalizedHyperbolicTowerIsometry.trans
      (omeara9328AdaptedHeadToHyperbolicTowerSpaceIsometry
        (K := K) (a : K) (a : K)).symm
  let integralIsometry := latticeIsometryToUnimodularModel
    S.sourceFirstNormalized_unimodular hmodelModular fieldIsometry hgroup
  exact
    { secondCoefficient := a
      secondCoefficient_integral := haIntegral
      secondCoefficientIdeal_eq := rfl
      sourceToModel := integralIsometry }

/-- In the odd 93:18 branch, the auxiliary coefficient `b` has strictly
larger order than the norm generator `a`. -/
theorem sourceHeadOdd_parameters_order_lt
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.sourceFirstOddDeterminantOneData hodd
    ordUnit K D.parameters.a < ordUnit K D.parameters.b := by
  let D := S.sourceFirstOddDeterminantOneData hodd
  change ordUnit K D.parameters.a < ordUnit K D.parameters.b
  have hle : ordUnit K S.firstNormGenerator ≤
      weightIdealOrder S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice :=
    normGeneratorOrder_le_weightIdealOrder S.firstNormGenerator
      S.firstNormGenerator_source
  have hne : ordUnit K S.firstNormGenerator ≠
      weightIdealOrder S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice := by
    intro heq
    have heven : Even S.firstNormWeightParity := by
      unfold firstNormWeightParity
      rw [heq]
      refine ⟨weightIdealOrder S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice, ?_⟩
      ring
    exact (Int.not_odd_iff_even.mpr heven) hodd
  have hstrict : ordUnit K S.firstNormGenerator <
      weightIdealOrder S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice :=
    lt_of_le_of_ne hle hne
  simpa only [D.parameters_a, D.parameters_b,
    ordUnit_uniformizerPowerUnit] using hstrict

set_option maxHeartbeats 3000000 in
/-- In the odd-weight branch, the determinant-one model of 93:18(vi),
followed by the explicit two-plane change, supplies the adapted source
model `A(a,0) ⊥ A(a+b,0)`. -/
noncomputable def sourceHeadOddAdaptedModelData
    (hodd : Odd S.firstNormWeightParity) :
    S.SourceHeadAdaptedModelData := by
  let D := S.sourceFirstOddDeterminantOneData hodd
  let P := D.parameters
  have hab : ordUnit K P.a < ordUnit K P.b := by
    simpa only [P, D] using S.sourceHeadOdd_parameters_order_lt hodd
  have habTop : ord K (P.a : K) < ord K (P.b : K) := by
    rw [← coe_ordUnit, ← coe_ordUnit]
    exact WithTop.coe_lt_coe.mpr hab
  have hsumOrder : ord K ((P.a : K) + (P.b : K)) =
      ord K (P.a : K) :=
    (ord K).map_add_eq_of_lt_left habTop
  have hsumNe : (P.a : K) + (P.b : K) ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero, ← coe_ordUnit] at hsumOrder
    exact WithTop.top_ne_coe hsumOrder
  let c : Kˣ := Units.mk0 ((P.a : K) + (P.b : K)) hsumNe
  have hcIntegral : (c : K) ∈ IntegerRing K := by
    change (P.a : K) + (P.b : K) ∈ IntegerRing K
    exact (IntegerRing K).toSubring.add_mem P.a_integral P.b_integral
  have hcOrder : ordUnit K c = ordUnit K P.a := by
    apply WithTop.coe_injective
    simpa only [c, Units.val_mk0, coe_ordUnit] using hsumOrder
  have hcIdealP : principalIdeal (K := K) (c : K) =
      principalIdeal (K := K) (P.a : K) :=
    (principalIdeal_eq_iff_ordUnit_eq c P.a).2 hcOrder
  have hcIdeal : principalIdeal (K := K) (c : K) =
      principalIdeal (K := K) (S.firstNormGenerator : K) := by
    simpa only [P, D, D.parameters_a] using hcIdealP
  let sourceToJ := Classical.choice (S.sourceFirstOdd_isometric_j hodd)
  let adaptedToUntwisted :=
    omeara9328OddAdaptedToUntwistedModelIsometry
      (P.a : K) (P.b : K) P.a_integral P.b_integral
  let identifyLeft :=
    (omearaGeneralPlaneZeroRightLatticeIsometry
      (K := K) (P.a : K)).symm
  let identifyRight :=
    (omearaGeneralPlaneZeroRightLatticeIsometry
      (K := K) (P.b : K)).symm
  let identifyRaw := identifyLeft.orthogonalProductBasic identifyRight
  have halpha : P.alpha = 0 := by
    simpa only [P] using D.alpha_zero
  let identify : Isometry
      (omeara9328AdaptedHeadSpace (P.a : K) (P.b : K))
      P.jData.space
      (omeara9328AdaptedHeadLattice (K := K)) P.jData.lattice := by
    simpa only [omeara9328AdaptedHeadSpace,
      omeara9328AdaptedHeadLattice,
      OmearaOddQuaternaryModelData.space,
      OmearaOddQuaternaryModelData.leftSpace,
      OmearaOddQuaternaryModelData.rightSpace,
      OmearaOddQuaternaryModelData.lattice,
      Omeara9318RankFourModelParameters.jData,
      halpha, neg_zero, zero_mul] using identifyRaw
  let modelToJ := adaptedToUntwisted.trans identify
  let sourceToAdaptedP := sourceToJ.trans modelToJ.symm
  let sourceToAdapted : Isometry S.sourceFirstNormalized
      (omeara9328AdaptedHeadSpace (S.firstNormGenerator : K) (c : K))
      (S.sourceJordan.component 0).lattice
      (omeara9328AdaptedHeadLattice (K := K)) := by
    simpa only [c, Units.val_mk0, P, D, D.parameters_a] using
      sourceToAdaptedP
  exact
    { secondCoefficient := c
      secondCoefficient_integral := hcIntegral
      secondCoefficientIdeal_eq := hcIdeal
      sourceToModel := sourceToAdapted }

/-- The parity-independent adapted source model used in Step 1. -/
noncomputable def sourceHeadAdaptedModelData :
    S.SourceHeadAdaptedModelData := by
  by_cases heven : Even S.firstNormWeightParity
  · exact S.sourceHeadEvenAdaptedModelData heven
  · exact S.sourceHeadOddAdaptedModelData
      (Int.not_even_iff_odd.mp heven)

/-- Pull the standard adapted model basis back to the normalized source
head. -/
noncomputable def sourceHeadAdaptedBasis :
    Basis (Fin 4) K (S.sourceJordan.component 0).carrier :=
  let D := S.sourceHeadAdaptedModelData
  (omeara9328AdaptedHeadBasis (K := K)).map
    D.sourceToModel.toLinearEquiv.symm

/-- The pulled-back basis is an integral basis of the source head. -/
theorem sourceHeadAdaptedBasisLattice_eq :
    basisLattice S.sourceHeadAdaptedBasis =
      (S.sourceJordan.component 0).lattice := by
  let D := S.sourceHeadAdaptedModelData
  change basisLattice
      ((omeara9328AdaptedHeadBasis (K := K)).map
        D.sourceToModel.toLinearEquiv.symm) =
    (S.sourceJordan.component 0).lattice
  calc
    basisLattice
        ((omeara9328AdaptedHeadBasis (K := K)).map
          D.sourceToModel.toLinearEquiv.symm) =
        map D.sourceToModel.toLinearEquiv.symm
          (basisLattice (omeara9328AdaptedHeadBasis (K := K))) :=
      (map_basisLattice_eq_basisLattice_map
        (omeara9328AdaptedHeadBasis (K := K))
        D.sourceToModel.toLinearEquiv.symm).symm
    _ = map D.sourceToModel.toLinearEquiv.symm
        (omeara9328AdaptedHeadLattice (K := K)) := by
      rw [basisLattice_omeara9328AdaptedHeadBasis]
    _ = (S.sourceJordan.component 0).lattice :=
      D.sourceToModel.symm.map_eq

/-- Exact block Gram matrix of the adapted source basis. -/
theorem sourceHeadAdaptedBasis_bilin (i j : Fin 4) :
    S.sourceFirstNormalized.bilin
        (S.sourceHeadAdaptedBasis i) (S.sourceHeadAdaptedBasis j) =
      !![(S.firstNormGenerator : K), 1, 0, 0;
         1, 0, 0, 0;
         0, 0, (S.sourceHeadAdaptedModelData.secondCoefficient : K), 1;
         0, 0, 1, 0] i j := by
  let D := S.sourceHeadAdaptedModelData
  change S.sourceFirstNormalized.bilin
      (D.sourceToModel.toLinearEquiv.symm
        (omeara9328AdaptedHeadBasis (K := K) i))
      (D.sourceToModel.toLinearEquiv.symm
        (omeara9328AdaptedHeadBasis (K := K) j)) = _
  calc
    S.sourceFirstNormalized.bilin
        (D.sourceToModel.toLinearEquiv.symm
          (omeara9328AdaptedHeadBasis (K := K) i))
        (D.sourceToModel.toLinearEquiv.symm
          (omeara9328AdaptedHeadBasis (K := K) j)) =
      (omeara9328AdaptedHeadSpace (S.firstNormGenerator : K)
        (D.secondCoefficient : K)).bilin
        (omeara9328AdaptedHeadBasis (K := K) i)
        (omeara9328AdaptedHeadBasis (K := K) j) :=
      D.sourceToModel.symm.map_bilin _ _
    _ = _ := omeara9328AdaptedHeadBasis_bilin
      (S.firstNormGenerator : K) (D.secondCoefficient : K) i j

@[simp]
theorem sourceHeadAdaptedBasis_bilin_zero_zero :
    S.sourceFirstNormalized.bilin
      (S.sourceHeadAdaptedBasis 0) (S.sourceHeadAdaptedBasis 0) =
        (S.firstNormGenerator : K) := by
  simpa using S.sourceHeadAdaptedBasis_bilin 0 0

@[simp]
theorem sourceHeadAdaptedBasis_bilin_two_two :
    S.sourceFirstNormalized.bilin
      (S.sourceHeadAdaptedBasis 2) (S.sourceHeadAdaptedBasis 2) =
        (S.sourceHeadAdaptedModelData.secondCoefficient : K) := by
  simpa using S.sourceHeadAdaptedBasis_bilin 2 2

/-- The first and third displayed norms generate the same norm ideal. -/
theorem sourceHeadAdaptedBasis_first_third_ideals_eq :
    principalIdeal (K := K)
        (S.sourceFirstNormalized.quadratic (S.sourceHeadAdaptedBasis 2)) =
      principalIdeal (K := K)
        (S.sourceFirstNormalized.quadratic (S.sourceHeadAdaptedBasis 0)) := by
  change principalIdeal (K := K)
      (S.sourceFirstNormalized.bilin
        (S.sourceHeadAdaptedBasis 2) (S.sourceHeadAdaptedBasis 2)) =
    principalIdeal (K := K)
      (S.sourceFirstNormalized.bilin
        (S.sourceHeadAdaptedBasis 0) (S.sourceHeadAdaptedBasis 0))
  rw [S.sourceHeadAdaptedBasis_bilin_two_two,
    S.sourceHeadAdaptedBasis_bilin_zero_zero]
  exact S.sourceHeadAdaptedModelData.secondCoefficientIdeal_eq

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
