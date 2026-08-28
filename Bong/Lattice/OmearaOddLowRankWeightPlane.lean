/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9318RankThreeOdd
import Bong.Lattice.OmearaGeneralTwoPlaneCombination
import Bong.Lattice.OrthogonalProductDecomposition
import Bong.Lattice.OrthogonalProductIsometry

/-!
# Weight-plane extraction in odd rank three and four

The two alternatives of O'Meara 93:18(iii) and (iv) have a common feature:
after moving the right binary factor to the front they display

`A(pi^W, 2*zeta) orthogonal R`,

where `W` is the weight order, `W > 0`, and the complement `R` has the same
norm ideal as the original lattice.  This file packages that common output
as a decomposition of the original lattice.  It is exactly the low-rank
input used twice in the proof of 93:18(v).
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [laws : DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The weight order is positive in the odd norm-weight parity branch of a
positive-rank unimodular lattice. -/
theorem weightIdealOrder_pos_of_unimodular_odd
    (hmodular : IsModular q L (1 : Kˣ))
    (a : Kˣ) (ha : IsNormGeneratorValue q L a)
    (hodd : Odd (ordUnit K a + weightIdealOrder q L)) :
    0 < weightIdealOrder q L := by
  have hnormLeWeight := normGeneratorOrder_le_weightIdealOrder a ha
  have hnormNonneg : 0 ≤ ordUnit K a := by
    have hnormScale := normIdeal_le_scaleIdeal q L
    rw [ha.2, hmodular.scaleIdeal_eq_principal
      (finrank_pos_of_isNormGeneratorValue ha)] at hnormScale
    have hord : ord K (1 : K) ≤ ord K (a : K) :=
      (principalIdeal_le_iff_ord_ge
        (Units.ne_zero a) (one_ne_zero : (1 : K) ≠ 0)).1 hnormScale
    rw [ord_one, ← coe_ordUnit K a] at hord
    exact WithTop.coe_le_coe.mp hord
  by_contra hnot
  have hweightZero : weightIdealOrder q L = 0 := by omega
  have hnormZero : ordUnit K a = 0 := by omega
  rw [hweightZero, hnormZero] at hodd
  exact Int.not_odd_zero hodd

/-- The canonical coefficient chosen at the weight order lies in the
maximal ideal in the odd branch. -/
theorem uniformizerPower_weightIdealOrder_isInMaximalIdeal_of_odd
    (hmodular : IsModular q L (1 : Kˣ))
    (a : Kˣ) (ha : IsNormGeneratorValue q L a)
    (hodd : Odd (ordUnit K a + weightIdealOrder q L)) :
    IsInMaximalIdeal K
      (uniformizerPowerUnit K (weightIdealOrder q L) : K) := by
  rw [IsInMaximalIdeal, ← coe_ordUnit,
    ordUnit_uniformizerPowerUnit]
  exact_mod_cast weightIdealOrder_pos_of_unimodular_odd
    hmodular a ha hodd

/-- If `2 O` is contained in `b O`, then O'Meara's correction
`4*rho/b` has an integral half. -/
theorem exists_integral_half_four_rho_div
    (b : Kˣ)
    (htwo : principalIdeal (K := K) (2 : K) ≤
      principalIdeal (K := K) (b : K)) :
    ∃ zeta : K, zeta ∈ IntegerRing K ∧
      (4 : K) * laws.rho * (b : K)⁻¹ = (2 : K) * zeta := by
  have htwoMem : (2 : K) ∈ principalIdeal (K := K) (b : K) :=
    htwo (generator_mem_principalIdeal (K := K) (2 : K))
  rw [principalIdeal, Submodule.mem_span_singleton] at htwoMem
  let cO : IntegerRing K := Classical.choose htwoMem
  have hcRaw := Classical.choose_spec htwoMem
  let c : K := algebraMap (IntegerRing K) K cO
  have hc : c * (b : K) = 2 := by
    dsimp only [c]
    dsimp only [cO]
    simpa only [Algebra.smul_def] using hcRaw
  have hcIntegral : c ∈ IntegerRing K := by
    dsimp only [c]
    simpa using cO.property
  let zeta : K := c * laws.rho
  have hrho : laws.rho ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 laws.rho_isValuationUnit.ge
  have hzeta : zeta ∈ IntegerRing K :=
    (IntegerRing K).toSubring.mul_mem hcIntegral hrho
  refine ⟨zeta, hzeta, ?_⟩
  dsimp only [zeta]
  have hquot : (2 : K) * (b : K)⁻¹ = c := by
    calc
      (2 : K) * (b : K)⁻¹ =
          (c * (b : K)) * (b : K)⁻¹ := by rw [hc]
      _ = c := by field_simp [Units.ne_zero b]
  calc
    (4 : K) * laws.rho * (b : K)⁻¹ =
        (2 : K) * ((2 : K) * (b : K)⁻¹) * laws.rho := by ring
    _ = (2 : K) * (c * laws.rho) := by rw [hquot]
      <;> ring

/-- Common integral output of the odd ternary and quaternary classification:
a canonical weight plane and a norm-preserving complement. -/
structure OmearaOddLowRankWeightPlaneData
    (q : QuadraticSpace K V) (L : Lattice K V) where
  b : Kˣ
  tailHalf : K
  tail : K
  b_eq : b = uniformizerPowerUnit K (weightIdealOrder q L)
  b_integral : (b : K) ∈ IntegerRing K
  b_maximal : IsInMaximalIdeal K (b : K)
  tailHalf_integral : tailHalf ∈ IntegerRing K
  tail_eq : tail = (2 : K) * tailHalf
  plane_nondegenerate : (b : K) * tail ≠ 1
  decomposition : OrthogonalDecomposition q L 2
  plane : Isometry
    (decomposition.component 0).space
    (QuadraticSpace.omearaGeneralPlane
      (b : K) tail plane_nondegenerate)
    (decomposition.component 0).lattice
    (hyperbolicPlaneLattice (K := K))
  complement_modular : IsModular
    (decomposition.component 1).space
    (decomposition.component 1).lattice (1 : Kˣ)
  complement_normIdeal_eq :
    normIdeal (decomposition.component 1).space
        (decomposition.component 1).lattice = normIdeal q L

namespace OmearaOddLowRankWeightPlaneData

variable (D : OmearaOddLowRankWeightPlaneData q L)

/-- Display the standard weight plane followed by the constructed
norm-preserving complement. -/
noncomputable def displayedIsometry :
    Isometry q
      ((QuadraticSpace.omearaGeneralPlane
        (D.b : K) D.tail D.plane_nondegenerate).orthogonalSum
          (D.decomposition.component 1).space)
      L
      (product (hyperbolicPlaneLattice (K := K))
        (D.decomposition.component 1).lattice) :=
  D.decomposition.pairProductLatticeIsometry.symm |>.trans
    (D.plane.orthogonalProductBasic
      (Isometry.refl (D.decomposition.component 1).space
        (D.decomposition.component 1).lattice))

/-- The weight plane has rank two, so the complement has rank two less
than the original lattice. -/
theorem complement_finrank :
    finrank K (D.decomposition.component 1).carrier =
      finrank K V - 2 := by
  letI : Module.Finite K V := L.moduleFinite
  let C0 := D.decomposition.component 0
  let C1 := D.decomposition.component 1
  letI : Module.Finite K C0.carrier := C0.lattice.moduleFinite
  letI : Module.Finite K C1.carrier := C1.lattice.moduleFinite
  have hplaneRank : finrank K C0.carrier = 2 := by
    calc
      finrank K C0.carrier = finrank K (Fin 2 → K) :=
        D.plane.toLinearEquiv.finrank_eq
      _ = 2 := by simp
  have htotal :=
    D.decomposition.pairProductLatticeIsometry.toLinearEquiv.finrank_eq
  change finrank K (C0.carrier × C1.carrier) = finrank K V at htotal
  rw [Module.finrank_prod, hplaneRank] at htotal
  have htotal' : finrank K C1.carrier + 2 = finrank K V := by
    simpa only [Nat.add_comm] using htotal
  exact Nat.eq_sub_of_add_eq htotal'

/-- Transport a displayed standard plane and a norm-preserving model
complement back to a decomposition of the original lattice. -/
noncomputable def ofDisplayedIsometry
    {W : Type u} [AddCommGroup W] [Module K W]
    (hmodular : IsModular q L (1 : Kˣ))
    (b : Kˣ) (tailHalf tail : K)
    (hbEq : b = uniformizerPowerUnit K (weightIdealOrder q L))
    (hbIntegral : (b : K) ∈ IntegerRing K)
    (hbMaximal : IsInMaximalIdeal K (b : K))
    (htailHalf : tailHalf ∈ IntegerRing K)
    (htail : tail = (2 : K) * tailHalf)
    (hnondegenerate : (b : K) * tail ≠ 1)
    (r : QuadraticSpace K W) (M : Lattice K W)
    (hresidualNorm : normIdeal r M = normIdeal q L)
    (displayed : Isometry q
      ((QuadraticSpace.omearaGeneralPlane
        (b : K) tail hnondegenerate).orthogonalSum r)
      L (product (hyperbolicPlaneLattice (K := K)) M)) :
    OmearaOddLowRankWeightPlaneData q L := by
  let plane := QuadraticSpace.omearaGeneralPlane
    (b : K) tail hnondegenerate
  let T : OrthogonalDecomposition (plane.orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) M) 2 :=
    orthogonalProductDecomposition plane r
      (hyperbolicPlaneLattice (K := K)) M
  let pulled := T.mapIsometry displayed.symm
  let standardToLeft : Isometry plane (T.component 0).space
      (hyperbolicPlaneLattice (K := K)) (T.component 0).lattice :=
    orthogonalProductLeftComponentIsometry plane r
      (hyperbolicPlaneLattice (K := K))
  let leftToPulled := (T.component 0).mapLatticeIsometry displayed.symm
  let residualToRight : Isometry r (T.component 1).space M
      (T.component 1).lattice :=
    orthogonalProductRightComponentIsometry plane r M
  let rightToPulled := (T.component 1).mapLatticeIsometry displayed.symm
  let residualToPulled := residualToRight.trans rightToPulled
  have hpulledNorm :
      normIdeal (pulled.component 1).space
          (pulled.component 1).lattice = normIdeal q L := by
    change normIdeal ((T.component 1).mapIsometry displayed.symm).space
        ((T.component 1).mapIsometry displayed.symm).lattice =
      normIdeal q L
    calc
      normIdeal ((T.component 1).mapIsometry displayed.symm).space
          ((T.component 1).mapIsometry displayed.symm).lattice =
          normIdeal r M := by
        rw [← residualToPulled.map_eq]
        exact normIdeal_map_isometry
          residualToPulled.toQuadraticSpaceIsometry M
      _ = normIdeal q L := hresidualNorm
  exact
    { b := b
      tailHalf := tailHalf
      tail := tail
      b_eq := hbEq
      b_integral := hbIntegral
      b_maximal := hbMaximal
      tailHalf_integral := htailHalf
      tail_eq := htail
      plane_nondegenerate := hnondegenerate
      decomposition := pulled
      plane := (standardToLeft.trans leftToPulled).symm
      complement_modular := pulled.component_modular_of_ambient hmodular 1
      complement_normIdeal_eq := hpulledNorm }

end OmearaOddLowRankWeightPlaneData

set_option maxHeartbeats 3000000 in

/-- O'Meara 93:18(iii), reoriented as a canonical weight plane followed by
a norm-preserving binary complement. -/
noncomputable def omeara9318iiiWeightPlaneData
    (hmodular : IsModular q L (1 : Kˣ))
    (hrank : finrank K V = 4)
    (a : Kˣ) (ha : IsNormGeneratorValue q L a)
    (hodd : Odd (ordUnit K a + weightIdealOrder q L)) :
    OmearaOddLowRankWeightPlaneData q L := by
  let R := omeara9318iiiData hmodular hrank a ha hodd
  let P := R.congruence.parameters
  have hbEq : P.b = uniformizerPowerUnit K (weightIdealOrder q L) :=
    R.congruence.parameters_b
  have hbMax : IsInMaximalIdeal K (P.b : K) := by
    rw [hbEq]
    exact uniformizerPower_weightIdealOrder_isInMaximalIdeal_of_odd
      hmodular a ha hodd
  have makeJ (f : Isometry q P.jData.space L P.jData.lattice) :
      OmearaOddLowRankWeightPlaneData q L := by
    let model := P.jData
    let swap := orthogonalProductSwap
      (q := model.leftSpace) (r := model.rightSpace)
      (L := hyperbolicPlaneLattice (K := K))
      (M := hyperbolicPlaneLattice (K := K))
    let displayed := f.trans swap
    have hmodelA : model.a = a := by
      change P.a = a
      exact R.congruence.parameters_a
    have hresidualNorm :
        normIdeal model.leftSpace (hyperbolicPlaneLattice (K := K)) =
          normIdeal q L := by
      calc
        _ = principalIdeal (K := K) (model.a : K) :=
          model.left_normIdeal_eq_a
        _ = principalIdeal (K := K) (a : K) := by rw [hmodelA]
        _ = normIdeal q L := ha.2.symm
    exact OmearaOddLowRankWeightPlaneData.ofDisplayedIsometry
      hmodular P.b 0 model.rightTail hbEq P.b_integral hbMax
        (IntegerRing K).zero_mem (by simp [model, Omeara9318RankFourModelParameters.jData])
        model.right_nondegenerate model.leftSpace
        (hyperbolicPlaneLattice (K := K)) hresidualNorm displayed
  have makeK (f : Isometry q P.kData.space L P.kData.lattice) :
      OmearaOddLowRankWeightPlaneData q L := by
    let model := P.kData
    let halfExists := exists_integral_half_four_rho_div P.b
      P.twoIdeal_le_bIdeal
    let zeta : K := Classical.choose halfExists
    have hzeta : zeta ∈ IntegerRing K :=
      (Classical.choose_spec halfExists).1
    have htail : model.rightTail = (2 : K) * zeta := by
      simpa only [model, Omeara9318RankFourModelParameters.kData]
        using (Classical.choose_spec halfExists).2
    let swap := orthogonalProductSwap
      (q := model.leftSpace) (r := model.rightSpace)
      (L := hyperbolicPlaneLattice (K := K))
      (M := hyperbolicPlaneLattice (K := K))
    let displayed := f.trans swap
    have hmodelA : model.a = a := by
      change P.a = a
      exact R.congruence.parameters_a
    have hresidualNorm :
        normIdeal model.leftSpace (hyperbolicPlaneLattice (K := K)) =
          normIdeal q L := by
      calc
        _ = principalIdeal (K := K) (model.a : K) :=
          model.left_normIdeal_eq_a
        _ = principalIdeal (K := K) (a : K) := by rw [hmodelA]
        _ = normIdeal q L := ha.2.symm
    exact OmearaOddLowRankWeightPlaneData.ofDisplayedIsometry
      hmodular P.b zeta model.rightTail hbEq P.b_integral hbMax
        hzeta htail model.right_nondegenerate model.leftSpace
        (hyperbolicPlaneLattice (K := K)) hresidualNorm displayed
  by_cases hJ : IsIsometric q P.jData.space L P.jData.lattice
  · exact makeJ (Classical.choice hJ)
  · have hK : IsIsometric q P.kData.space L P.kData.lattice :=
      R.isometric_j_or_k.resolve_left hJ
    exact makeK (Classical.choice hK)

set_option maxHeartbeats 3000000 in

/-- O'Meara 93:18(iv), reoriented as a canonical weight plane followed by
the norm-preserving unary head factor. -/
noncomputable def omeara9318ivWeightPlaneData
    (hmodular : IsModular q L (1 : Kˣ))
    (hrank : finrank K V = 3)
    (a : Kˣ) (ha : IsNormGeneratorValue q L a)
    (hodd : Odd (ordUnit K a + weightIdealOrder q L)) :
    OmearaOddLowRankWeightPlaneData q L := by
  let R : Omeara9318RankThreeOddData.{u, v} q L :=
    omeara9318ivData hmodular hrank a ha hodd
  let A := R.adjunction
  let P := R.rankFour.congruence.parameters
  have hbEq : P.b = uniformizerPowerUnit K (weightIdealOrder q L) := by
    calc
      P.b = uniformizerPowerUnit K
          (weightIdealOrder A.space A.lattice) :=
        R.rankFour.congruence.parameters_b
      _ = uniformizerPowerUnit K (weightIdealOrder q L) := by
        rw [A.weightIdealOrder_eq]
  have hbMax : IsInMaximalIdeal K (P.b : K) := by
    rw [hbEq]
    exact uniformizerPower_weightIdealOrder_isInMaximalIdeal_of_odd
      hmodular a ha hodd
  by_cases hJ : IsIsometric q
      (P.jTernaryData R.parameters_a_isValuationUnit).space L
      (P.jTernaryData R.parameters_a_isValuationUnit).lattice
  · let T := P.jTernaryData R.parameters_a_isValuationUnit
    let fJ := Classical.choice hJ
    have hbEqT : T.b =
        uniformizerPowerUnit K (weightIdealOrder q L) := by
      simpa [T, Omeara9318RankFourModelParameters.jTernaryData,
        Omeara9318RankFourModelParameters.jData] using hbEq
    have hbMaxT : IsInMaximalIdeal K (T.b : K) := by
      simpa [T, Omeara9318RankFourModelParameters.jTernaryData,
        Omeara9318RankFourModelParameters.jData] using hbMax
    let swap := orthogonalProductSwap
      (q := QuadraticSpace.scaledLine T.head) (r := T.rightSpace)
      (L := BONG.unaryModelLattice (K := K))
      (M := hyperbolicPlaneLattice (K := K))
    let displayed := fJ.trans swap
    have htotalNorm : normIdeal T.space T.lattice = normIdeal q L := by
      rw [← fJ.map_eq]
      exact normIdeal_map_isometry fJ.toQuadraticSpaceIsometry L
    have hresidualNorm :
        normIdeal (QuadraticSpace.scaledLine T.head)
            (BONG.unaryModelLattice (K := K)) = normIdeal q L :=
      T.headLine_normIdeal_eq_head.trans
        (T.normIdeal_eq_head.symm.trans htotalNorm)
    exact OmearaOddLowRankWeightPlaneData.ofDisplayedIsometry
      hmodular T.b 0 T.rightTail hbEqT T.b_integral hbMaxT
        (IntegerRing K).zero_mem
        (by simp [T, Omeara9318RankFourModelParameters.jTernaryData,
          OmearaOddQuaternaryModelData.ternaryComplementData,
          Omeara9318RankFourModelParameters.jData])
        T.right_nondegenerate (QuadraticSpace.scaledLine T.head)
        (BONG.unaryModelLattice (K := K)) hresidualNorm (by
          simpa only [OmearaOddTernaryModelData.rightSpace] using displayed)
  · have hK : IsIsometric q
        (P.kTernaryData R.parameters_a_isValuationUnit).space L
        (P.kTernaryData R.parameters_a_isValuationUnit).lattice :=
      R.isometric_j_or_k.resolve_left hJ
    let T := P.kTernaryData R.parameters_a_isValuationUnit
    let fK := Classical.choice hK
    have hbEqT : T.b =
        uniformizerPowerUnit K (weightIdealOrder q L) := by
      simpa [T, Omeara9318RankFourModelParameters.kTernaryData,
        Omeara9318RankFourModelParameters.kData] using hbEq
    have hbMaxT : IsInMaximalIdeal K (T.b : K) := by
      simpa [T, Omeara9318RankFourModelParameters.kTernaryData,
        Omeara9318RankFourModelParameters.kData] using hbMax
    let halfExists := exists_integral_half_four_rho_div T.b
      T.twoIdeal_le_bIdeal
    let zeta : K := Classical.choose halfExists
    have hzeta : zeta ∈ IntegerRing K :=
      (Classical.choose_spec halfExists).1
    have hhalf : (4 : K) * laws.rho * (T.b : K)⁻¹ =
        (2 : K) * zeta := by
      simpa only [zeta] using (Classical.choose_spec halfExists).2
    have htail : T.rightTail = (2 : K) * zeta := by
      simpa [T, Omeara9318RankFourModelParameters.kTernaryData,
        OmearaOddQuaternaryModelData.ternaryComplementData,
        Omeara9318RankFourModelParameters.kData]
        using hhalf
    let swap := orthogonalProductSwap
      (q := QuadraticSpace.scaledLine T.head) (r := T.rightSpace)
      (L := BONG.unaryModelLattice (K := K))
      (M := hyperbolicPlaneLattice (K := K))
    let displayed := fK.trans swap
    have htotalNorm : normIdeal T.space T.lattice = normIdeal q L := by
      rw [← fK.map_eq]
      exact normIdeal_map_isometry fK.toQuadraticSpaceIsometry L
    have hresidualNorm :
        normIdeal (QuadraticSpace.scaledLine T.head)
            (BONG.unaryModelLattice (K := K)) = normIdeal q L :=
      T.headLine_normIdeal_eq_head.trans
        (T.normIdeal_eq_head.symm.trans htotalNorm)
    exact OmearaOddLowRankWeightPlaneData.ofDisplayedIsometry
      hmodular T.b zeta T.rightTail hbEqT T.b_integral hbMaxT hzeta htail
        T.right_nondegenerate (QuadraticSpace.scaledLine T.head)
        (BONG.unaryModelLattice (K := K)) hresidualNorm (by
          simpa only [OmearaOddTernaryModelData.rightSpace] using displayed)

end Lattice

end Bong
