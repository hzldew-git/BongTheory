/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9318RankFourOdd
import Bong.Lattice.Omeara9318RankThreeModels
import Bong.Lattice.OmearaGeneralModularCancellation
import Bong.Lattice.OmearaUnitLineAdjunction

/-!
# O'Meara 93:18(iv): the odd ternary case

Adjoin a represented unit line to an odd ternary unimodular lattice.  The
resulting quaternary lattice is one of the two models of 93:18(iii).  Both
models split off that same unit line, and Corollary 93:14a cancels it.  This
file carries out the cancellation integrally and proves that the two ternary
alternatives cannot occur simultaneously.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [laws : DyadicDiscriminantClassLaws K]

/-- Equal coefficients give the evident integral isometry between their
standard unary models. -/
noncomputable def scaledLineLatticeIsometryOfEq (a b : Kˣ) (h : a = b) :
    Isometry (QuadraticSpace.scaledLine a)
      (QuadraticSpace.scaledLine b)
      (BONG.unaryModelLattice (K := K))
      (BONG.unaryModelLattice (K := K)) := by
  subst b
  exact Isometry.refl _ _

/-- The common unit line has norm group contained in either ternary
complement.  The only error term on the line is in `2 O`, hence in `b O`. -/
theorem Omeara9318RankFourModelParameters.line_normGroupSet_subset_ternary
    (P : Omeara9318RankFourModelParameters K)
    (ha : IsValuationUnit K (P.a : K))
    (T : OmearaOddTernaryModelData K)
    (hT : normGroupSet T.space T.lattice =
      integralSquareCoset (P.a : K)
        (principalIdeal (K := K) (P.b : K))) :
    normGroupSet (QuadraticSpace.scaledLine P.a)
        (BONG.unaryModelLattice (K := K)) ⊆
      normGroupSet T.space T.lattice := by
  let line := QuadraticSpace.scaledLine P.a
  let lineLattice := BONG.unaryModelLattice (K := K)
  have hline : IsModular line lineLattice (1 : Kˣ) :=
    unaryModelLattice_isModular_scaledLine_of_isValuationUnit P.a ha
  rintro z ⟨c, hc, y, hy, rfl⟩
  rw [twoScaleIdeal_eq_principalIdeal_two_of_unimodular hline (by simp)] at hy
  rw [hT]
  let cO : IntegerRing K :=
    ⟨c, (BONG.mem_unaryModelLattice_iff c).mp hc⟩
  refine ⟨cO, y, P.twoIdeal_le_bIdeal hy, ?_⟩
  rw [QuadraticSpace.scaledLine_quadratic_apply]

/-- Complete integral output of O'Meara 93:18(iv), expressed using the
parameters canonically produced after adjoining the represented unit line. -/
structure Omeara9318RankThreeOddData
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) where
  adjunction : UnitLineAdjunctionData.{u, v} q L
  rankFour : Omeara9318RankFourOddData adjunction.space adjunction.lattice
    adjunction.unitData.valueUnit
  parameters_a_isValuationUnit : IsValuationUnit K
    (rankFour.congruence.parameters.a : K)
  isometric_j_or_k :
    IsIsometric q
        (rankFour.congruence.parameters.jTernaryData
          parameters_a_isValuationUnit).space L
        (rankFour.congruence.parameters.jTernaryData
          parameters_a_isValuationUnit).lattice ∨
      IsIsometric q
        (rankFour.congruence.parameters.kTernaryData
          parameters_a_isValuationUnit).space L
        (rankFour.congruence.parameters.kTernaryData
          parameters_a_isValuationUnit).lattice
  not_both : ¬
    (IsIsometric q
        (rankFour.congruence.parameters.jTernaryData
          parameters_a_isValuationUnit).space L
        (rankFour.congruence.parameters.jTernaryData
          parameters_a_isValuationUnit).lattice ∧
      IsIsometric q
        (rankFour.congruence.parameters.kTernaryData
          parameters_a_isValuationUnit).space L
        (rankFour.congruence.parameters.kTernaryData
          parameters_a_isValuationUnit).lattice)

set_option maxHeartbeats 3000000 in

/-- O'Meara 93:18(iv): an odd ternary unimodular lattice is integrally
isometric to exactly one of the two ternary complements printed in 93:18. -/
noncomputable def omeara9318ivData
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (hmodular : IsModular q L (1 : Kˣ))
    (hrank : finrank K V = 3)
    (a : Kˣ) (ha : IsNormGeneratorValue q L a)
    (hodd : Odd (ordUnit K a + weightIdealOrder q L)) :
    Omeara9318RankThreeOddData.{u, v} q L := by
  letI : Module.Finite K V := L.moduleFinite
  have hrankOdd : Odd (finrank K V) := by
    rw [hrank]
    norm_num
  let A := unitLineAdjunctionData.{u, v} q L hmodular hrankOdd
  have hAspace : A.space =
      (QuadraticSpace.scaledLine A.unitData.valueUnit).orthogonalSum q := by
    exact unitLineAdjunctionData_space q L hmodular hrankOdd
  have hAlattice : A.lattice =
      product (BONG.unaryModelLattice (K := K)) L := by
    exact unitLineAdjunctionData_lattice q L hmodular hrankOdd
  have hchosenOrder : ordUnit K A.unitData.valueUnit = ordUnit K a := by
    apply (principalIdeal_eq_iff_ordUnit_eq A.unitData.valueUnit a).mp
    exact (A.unitData.isNormGeneratorValue hmodular hrankOdd).2.symm.trans ha.2
  have hadjoinedOdd : Odd
      (ordUnit K A.unitData.valueUnit +
        weightIdealOrder A.space A.lattice) := by
    rw [A.weightIdealOrder_eq, hchosenOrder]
    exact hodd
  have hrankFour : finrank K (K × V) = 4 := by
    rw [Module.finrank_prod, hrank]
    simp
  let R := omeara9318iiiData A.modular hrankFour
    A.unitData.valueUnit A.normGenerator hadjoinedOdd
  let P := R.congruence.parameters
  have hPa : P.a = A.unitData.valueUnit := R.congruence.parameters_a
  have hPunit : IsValuationUnit K (P.a : K) := by
    rw [hPa]
    exact A.unitData.value_isValuationUnit
  let lineIdentify := scaledLineLatticeIsometryOfEq
    A.unitData.valueUnit P.a hPa.symm
  have hsourceLine : IsUnimodular
      (QuadraticSpace.scaledLine A.unitData.valueUnit)
      (BONG.unaryModelLattice (K := K)) :=
    unaryModelLattice_isModular_scaledLine_of_isValuationUnit
      A.unitData.valueUnit A.unitData.value_isValuationUnit
  have htargetLine : IsUnimodular
      (QuadraticSpace.scaledLine P.a)
      (BONG.unaryModelLattice (K := K)) :=
    unaryModelLattice_isModular_scaledLine_of_isValuationUnit P.a hPunit
  have hsourceGroup :
      normGroupSet (QuadraticSpace.scaledLine A.unitData.valueUnit)
          (BONG.unaryModelLattice (K := K)) ⊆
        normGroupSet q L :=
    A.unitData.line_normGroupSet_subset hmodular hrankOdd
  let jT := P.jTernaryData hPunit
  let kT := P.kTernaryData hPunit
  have hjTargetGroup :
      normGroupSet (QuadraticSpace.scaledLine P.a)
          (BONG.unaryModelLattice (K := K)) ⊆
        normGroupSet jT.space jT.lattice :=
    P.line_normGroupSet_subset_ternary hPunit jT
      (P.jTernary_normGroupSet_eq_common hPunit)
  have hkTargetGroup :
      normGroupSet (QuadraticSpace.scaledLine P.a)
          (BONG.unaryModelLattice (K := K)) ⊆
        normGroupSet kT.space kT.lattice :=
    P.line_normGroupSet_subset_ternary hPunit kT
      (P.kTernary_normGroupSet_eq_common hPunit)
  have cancelJ (fJ : Isometry A.space P.jData.space
      A.lattice P.jData.lattice) :
      Isometry q jT.space L jT.lattice := by
    let displayed := P.jDisplayedTernaryIsometry hPunit
    let totalRaw := fJ.trans displayed
    have total : Isometry
        ((QuadraticSpace.scaledLine A.unitData.valueUnit).orthogonalSum q)
        ((QuadraticSpace.scaledLine P.a).orthogonalSum jT.space)
        (product (BONG.unaryModelLattice (K := K)) L)
        (product (BONG.unaryModelLattice (K := K)) jT.lattice) := by
      simpa only [hAspace, hAlattice] using totalRaw
    exact omeara9314a_unimodular hsourceLine htargetLine hmodular
      jT.isModular lineIdentify hsourceGroup hjTargetGroup total
  have cancelK (fK : Isometry A.space P.kData.space
      A.lattice P.kData.lattice) :
      Isometry q kT.space L kT.lattice := by
    let displayed := P.kDisplayedTernaryIsometry hPunit
    let totalRaw := fK.trans displayed
    have total : Isometry
        ((QuadraticSpace.scaledLine A.unitData.valueUnit).orthogonalSum q)
        ((QuadraticSpace.scaledLine P.a).orthogonalSum kT.space)
        (product (BONG.unaryModelLattice (K := K)) L)
        (product (BONG.unaryModelLattice (K := K)) kT.lattice) := by
      simpa only [hAspace, hAlattice] using totalRaw
    exact omeara9314a_unimodular hsourceLine htargetLine hmodular
      kT.isModular lineIdentify hsourceGroup hkTargetGroup total
  have hnotBoth : ¬
      (IsIsometric q jT.space L jT.lattice ∧
        IsIsometric q kT.space L kT.lattice) := by
    rintro ⟨⟨fJ⟩, ⟨fK⟩⟩
    let liftJ := lineIdentify.orthogonalProductBasic fJ
    let liftK := lineIdentify.orthogonalProductBasic fK
    let toJRaw := liftJ.trans (P.jDisplayedTernaryIsometry hPunit).symm
    let toKRaw := liftK.trans (P.kDisplayedTernaryIsometry hPunit).symm
    have toJ : Isometry A.space P.jData.space A.lattice P.jData.lattice := by
      simpa only [hAspace, hAlattice] using toJRaw
    have toK : Isometry A.space P.kData.space A.lattice P.kData.lattice := by
      simpa only [hAspace, hAlattice] using toKRaw
    exact R.not_both ⟨⟨toJ⟩, ⟨toK⟩⟩
  have hcases :
      IsIsometric q jT.space L jT.lattice ∨
        IsIsometric q kT.space L kT.lattice := by
    rcases R.isometric_j_or_k with hJ | hK
    · rcases hJ with ⟨fJ⟩
      exact Or.inl ⟨cancelJ fJ⟩
    · rcases hK with ⟨fK⟩
      exact Or.inr ⟨cancelK fK⟩
  exact
    { adjunction := A
      rankFour := R
      parameters_a_isValuationUnit := hPunit
      isometric_j_or_k := hcases
      not_both := hnotBoth }

end Lattice

end Bong
