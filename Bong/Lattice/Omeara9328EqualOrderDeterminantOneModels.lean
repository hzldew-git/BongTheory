/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328EqualOrderDeterminantNormalization
import Bong.Lattice.BinaryDeterminantHyperbolic
import Bong.Lattice.Omeara9328SourceFirstOddModel
import Bong.Lattice.Omeara9318ModelParameterExt

/-!
# Determinant-one models in the equal-order branch of O'Meara 93:28

The determinant correction leaves a normalized quaternary head with the
same norm group, weight ideal, and parity as the hyperbolic source head.  In
even parity, 93:18(ii) and the binary determinant criterion identify this
head with two hyperbolic planes.  In odd parity, 93:18(vi) gives the exact
untwisted/twisted determinant-one dichotomy; field hyperbolicity selects the
untwisted model.  No local-law interface is introduced here.
-/

namespace Bong

open Dyadic Module

universe u v w

namespace Lattice.Omeara9318vData

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- In a determinant-one quaternary splitting, the binary complement of a
displayed hyperbolic plane has determinant class `-1`. -/
theorem complement_determinantClass_eq_neg_one
    (E : Omeara9318vData q L (1 : Kˣ))
    (hdet : determinantClass q L = 1) :
    determinantClass (E.decomposition.component 1).space
        (E.decomposition.component 1).lattice =
      unitSquareClass K (-1 : Kˣ) := by
  have hsplit := E.decomposition.determinantClass_eq_mul_components
  have hhyper := determinantClass_eq_of_isometry E.hyperbolic
  rw [hdet, hhyper, determinantClass_hyperbolicPlaneLattice] at hsplit
  simp only [one_pow, mul_one] at hsplit
  let negClass : UnitSquareClass K := unitSquareClass K (-1 : Kˣ)
  have hnegSq : negClass * negClass = 1 := by
    rw [← unitSquareClass_mul]
    norm_num [negClass]
  calc
    determinantClass (E.decomposition.component 1).space
        (E.decomposition.component 1).lattice =
        1 * determinantClass (E.decomposition.component 1).space
          (E.decomposition.component 1).lattice :=
      (@one_mul (UnitSquareClass K) _ _).symm
    _ = (negClass * negClass) *
        determinantClass (E.decomposition.component 1).space
          (E.decomposition.component 1).lattice := by rw [hnegSq]
    _ = negClass * (negClass *
        determinantClass (E.decomposition.component 1).space
          (E.decomposition.component 1).lattice) := by rw [mul_assoc]
    _ = negClass * 1 := by
      have hcancel := congrArg
        (fun c : UnitSquareClass K ↦ negClass * c) hsplit
      simpa only [negClass] using hcancel.symm
    _ = unitSquareClass K (-1 : Kˣ) := by
      change negClass * 1 = negClass
      exact @mul_one (UnitSquareClass K) _ _

/-- An even determinant-one quaternary lattice with a displayed hyperbolic
summand is a two-plane hyperbolic tower over the field. -/
noncomputable def toHyperbolicTowerSpaceIsometry
    (E : Omeara9318vData q L (1 : Kˣ))
    (hrank : finrank K V = 4)
    (hdet : determinantClass q L = 1) :
    QuadraticSpace.Isometry q
      (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2) := by
  let C := E.decomposition.component 1
  letI : Module.Finite K C.carrier := C.lattice.moduleFinite
  let complementToHyperbolic := Classical.choice <|
    QuadraticSpace.rankTwo_isIsometric_hyperbolicPlane_one_of_determinantClass_eq
      C.space C.lattice (E.complement_finrank_of_rank_four hrank)
      (E.complement_determinantClass_eq_neg_one hdet)
  let splitToHyperbolicProduct :=
    E.displayedIsometry.toQuadraticSpaceIsometry.trans
      ((QuadraticSpace.Isometry.refl (QuadraticSpace.hyperbolicPlane (1 : Kˣ)))
        |>.orthogonalSum complementToHyperbolic)
  let hyperbolicToZero :=
    (scaledZeroOmearaPlaneLatticeIsometry (K := K) (1 : Kˣ)).symm
      |>.toQuadraticSpaceIsometry
  exact splitToHyperbolicProduct.trans <|
    (hyperbolicToZero.orthogonalSum hyperbolicToZero).trans
      (twoZeroPlaneProductToTowerTwoSpaceIsometry (K := K))

end Lattice.Omeara9318vData

namespace Lattice.Omeara9318viOddData

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {a : Kˣ}

/-- The determinant-one odd model is the untwisted model whenever the
ambient quadratic space is the standard two-plane hyperbolic tower. -/
theorem isometric_j_of_isIsometric_hyperbolicTower
    (N : Omeara9318viOddData q L a)
    (htower : q.IsIsometric
      (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2)) :
    IsIsometric q N.parameters.jData.space L N.parameters.jData.lattice := by
  rcases N.isometric_j_or_k with hj | hk
  · exact hj
  · exfalso
    apply N.parameters.j_not_isometric_k
    let jToTower :=
      N.parameters.jSpaceToHyperbolicTowerIsometry N.alpha_zero
    let qToTower := Classical.choice htower
    let jToQ := jToTower.trans qToTower.symm
    let qToK := (Classical.choice hk).toQuadraticSpaceIsometry
    exact ⟨jToQ.trans qToK⟩

end Lattice.Omeara9318viOddData

namespace Lattice.JordanDecomposition

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

theorem newHead_normGroupSet_eq_source :
    normGroupSet S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice =
      normGroupSet D.newHead D.newHeadLattice := by
  exact S.firstNormalized_normGroupSet_eq.trans
    D.headSplit_complement_normGroupSet_eq.symm

theorem newHead_twoScaleIdeal_eq_source :
    twoScaleIdeal S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice =
      twoScaleIdeal D.newHead D.newHeadLattice := by
  rw [twoScaleIdeal_eq_principalIdeal_two_of_unimodular
      S.sourceFirstNormalized_unimodular
      (by rw [S.sourceFirstNormalized_finrank]; omega),
    twoScaleIdeal_eq_principalIdeal_two_of_unimodular
      D.headSplit.complement_modular
      (by rw [D.headSplit_complement_finrank]; omega)]

theorem newHead_weightIdeal_eq_source :
    weightIdeal S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice =
      weightIdeal D.newHead D.newHeadLattice := by
  exact weightIdeal_eq_of_normGroupSet_eq_of_twoScaleIdeal_eq
    S.firstNormGenerator_source
    ⟨S.firstNormGenerator, D.headSplit_complement_firstNormGenerator⟩
    D.newHead_normGroupSet_eq_source D.newHead_twoScaleIdeal_eq_source

theorem newHead_weightIdealOrder_eq_source :
    weightIdealOrder S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice =
      weightIdealOrder D.newHead D.newHeadLattice := by
  apply powerIdeal_order_eq_of_eq (K := K)
  calc
    powerIdeal (K := K)
        (weightIdealOrder S.sourceFirstNormalized
          (S.sourceJordan.component 0).lattice) =
        weightIdeal S.sourceFirstNormalized
          (S.sourceJordan.component 0).lattice :=
      (weightIdeal_eq_powerIdeal _ _).symm
    _ = weightIdeal D.newHead D.newHeadLattice :=
      D.newHead_weightIdeal_eq_source
    _ = powerIdeal (K := K)
        (weightIdealOrder D.newHead D.newHeadLattice) :=
      weightIdeal_eq_powerIdeal _ _

theorem newHead_parity_iff_source :
    Odd S.firstNormWeightParity ↔
      Odd (ordUnit K S.firstNormGenerator +
        weightIdealOrder D.newHead D.newHeadLattice) := by
  unfold Omeara9328RankFourReductionSystem.firstNormWeightParity
  rw [D.newHead_weightIdealOrder_eq_source]

noncomputable def newHeadEvenData
    (heven : Even S.firstNormWeightParity) :
    Omeara9318vData D.newHead D.newHeadLattice (1 : Kˣ) := by
  apply omeara9318iiData D.headSplit.complement_modular
    (by rw [D.headSplit_complement_finrank]; omega)
    S.firstNormGenerator D.headSplit_complement_firstNormGenerator
  unfold Omeara9328RankFourReductionSystem.firstNormWeightParity at heven
  simpa only [D.newHead_weightIdealOrder_eq_source] using heven

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 3000000 in
noncomputable def newHeadEvenToHyperbolicTowerSpaceIsometry
    (heven : Even S.firstNormWeightParity)
    (hdet : determinantClass D.newHead D.newHeadLattice = 1) :
    QuadraticSpace.Isometry D.newHead
      (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2) := by
  let E := D.newHeadEvenData heven
  exact E.toHyperbolicTowerSpaceIsometry
    D.headSplit_complement_finrank hdet

noncomputable def sourceToNewHeadIsometryOfHyperbolic
    (htower : D.newHead.IsIsometric
      (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2)) :
    Isometry S.sourceFirstNormalized D.newHead
      (S.sourceJordan.component 0).lattice D.newHeadLattice := by
  let fieldIsometry := S.sourceFirstNormalizedHyperbolicTowerIsometry.trans
    (Classical.choice htower).symm
  exact latticeIsometryToUnimodularModel
    S.sourceFirstNormalized_unimodular D.headSplit.complement_modular
    fieldIsometry D.newHead_normGroupSet_eq_source

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 3000000 in
noncomputable def sourceToNewHeadEvenIsometry
    (heven : Even S.firstNormWeightParity)
    (hdet : determinantClass D.newHead D.newHeadLattice = 1) :
    Isometry S.sourceFirstNormalized D.newHead
      (S.sourceJordan.component 0).lattice D.newHeadLattice := by
  apply D.sourceToNewHeadIsometryOfHyperbolic
  exact ⟨D.newHeadEvenToHyperbolicTowerSpaceIsometry heven hdet⟩

/-- Determinant-one 93:18(vi) data for the corrected odd head. -/
noncomputable def newHeadOddDeterminantOneData
    (hodd : Odd S.firstNormWeightParity)
    (hdet : determinantClass D.newHead D.newHeadLattice = 1) :
    Omeara9318viOddData D.newHead D.newHeadLattice
      S.firstNormGenerator := by
  apply omeara9318viOddData D.headSplit.complement_modular
    D.headSplit_complement_finrank S.firstNormGenerator
    D.headSplit_complement_firstNormGenerator
  · exact D.newHead_parity_iff_source.mp hodd
  · exact hdet

/-- In the odd branch, field hyperbolicity selects the untwisted integral
model in the 93:18(vi) dichotomy. -/
theorem newHeadOdd_isometric_j_of_hyperbolic
    (hodd : Odd S.firstNormWeightParity)
    (hdet : determinantClass D.newHead D.newHeadLattice = 1)
    (htower : D.newHead.IsIsometric
      (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2)) :
    let N := D.newHeadOddDeterminantOneData hodd hdet
    IsIsometric D.newHead N.parameters.jData.space
      D.newHeadLattice N.parameters.jData.lattice := by
  let N := D.newHeadOddDeterminantOneData hodd hdet
  change IsIsometric D.newHead N.parameters.jData.space
    D.newHeadLattice N.parameters.jData.lattice
  exact N.isometric_j_of_isIsometric_hyperbolicTower htower

end Omeara9328RankFourReductionSystem.EqualNormOrderErrorData

end Lattice.JordanDecomposition

end Bong
