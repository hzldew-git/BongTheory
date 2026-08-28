/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma34BoundaryRepresentation
import Bong.Lattice.OrthogonalDecompositionPrefix
import Bong.QuadraticSpace.OrthogonalComplementRepresentation
import Bong.QuadraticSpace.OrthogonalSumCancellation

/-!
# Unary boundary collisions in Beli (2019), Lemma 3.4

This module closes the two overlap cases in which a Definition 10 trigger
at a Jordan boundary is supplied by the other boundary of an adjacent unary
component.  The actual unary coefficient is proved to be a norm generator
of O'Meara's intrinsic fundamental layer.  O'Meara 93:28(ii)/(iii), exact
prefix geometry, and Witt cancellation then give the required left and
right diagonal representations.

No representation law or local-law parameter is introduced.
-/

namespace Bong

open Dyadic Module
open BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice.JordanDecomposition

/-- A Jordan component's scale order never exceeds its norm order. -/
theorem scaleOrder_le_normOrder {t : Nat}
    (J : JordanDecomposition q L t) (i : Fin t) :
    ordUnit K (J.scaleGenerator i) ≤ ordUnit K (J.normGenerator i) := by
  have hideal : principalIdeal (K := K) (J.normGenerator i : K) ≤
      principalIdeal (K := K) (J.scaleGenerator i : K) := by
    rw [← J.normIdeal_eq i, ← J.scaleIdeal_eq i]
    exact normIdeal_le_scaleIdeal (J.component i).space
      (J.component i).lattice
  have horder := (principalIdeal_le_iff_ord_ge
    (Units.ne_zero (J.normGenerator i))
    (Units.ne_zero (J.scaleGenerator i))).mp hideal
  apply WithTop.coe_le_coe.mp
  simpa only [coe_ordUnit] using horder

/-- At a unary Jordan component, the intrinsic effective norm is exactly
the component norm. -/
theorem effectiveNormOrder_eq_normGenerator_of_componentRank_eq_one
    {t : Nat} (J : JordanDecomposition q L t) (i : Fin t)
    (hrank : J.componentRank i = 1) :
    BONG.jordanEffectiveNormOrder J i = ordUnit K (J.normGenerator i) := by
  have hnormScale : ordUnit K (J.normGenerator i) =
      ordUnit K (J.scaleGenerator i) := by
    exact ordUnit_normGenerator_eq_scaleGenerator_of_finrank_eq_one
      (J.component i).space (J.component i).lattice
      (J.scaleGenerator i) (J.normGenerator i) hrank
      (J.modular i) (J.normIdeal_eq i)
  unfold BONG.jordanEffectiveNormOrder BONG.jordanEffectiveNormOrderAt
  apply le_antisymm
  · calc
      JordanProfileOrder.effectiveAt
          (fun j ↦ ordUnit K (J.scaleGenerator j))
          (fun j ↦ ordUnit K (J.normGenerator j)) i
          (ordUnit K (J.scaleGenerator i)) ≤
        JordanProfileOrder.adjustedAt
          (fun j ↦ ordUnit K (J.scaleGenerator j))
          (fun j ↦ ordUnit K (J.normGenerator j))
          (ordUnit K (J.scaleGenerator i)) i :=
            JordanProfileOrder.effectiveAt_le _ _ i i _
      _ = ordUnit K (J.normGenerator i) := by
        simp [JordanProfileOrder.adjustedAt]
  · rw [hnormScale]
    apply JordanProfileOrder.target_le_effectiveAt
    intro j
    exact J.scaleOrder_le_normOrder j

/-- The exact one-entry BONG of a unary Jordan component. -/
noncomputable def unaryComponentBONG {t : Nat}
    (J : JordanDecomposition q L t) (i : Fin t)
    (hrank : J.componentRank i = 1) :
    BONG (J.component i).carrier (J.component i).space
      (J.component i).lattice 1 :=
  (BONG.ofLattice (J.component i).space (J.component i).lattice).castLength
    hrank

/-- The actual nonzero coefficient selected from a unary Jordan component. -/
noncomputable def unaryComponentValue {t : Nat}
    (J : JordanDecomposition q L t) (i : Fin t)
    (hrank : J.componentRank i = 1) : Kˣ :=
  (J.unaryComponentBONG i hrank).valueUnit 0

/-- The selected unary coefficient generates the component norm. -/
theorem unaryComponentValue_isNormGeneratorValue_component {t : Nat}
    (J : JordanDecomposition q L t) (i : Fin t)
    (hrank : J.componentRank i = 1) :
    IsNormGeneratorValue (J.component i).space (J.component i).lattice
      (J.unaryComponentValue i hrank) := by
  exact (J.unaryComponentBONG i hrank)
    |>.lemma214_valueUnit_zero_isNormGeneratorValue_nonempty

/-- The same unary coefficient generates the intrinsic fundamental layer. -/
theorem unaryComponentValue_isNormGeneratorValue_fundamental {t : Nat}
    (J : JordanDecomposition q L t) (i : Fin t)
    (hrank : J.componentRank i = 1) :
    IsNormGeneratorValue q (J.fundamentalLattice i)
      (J.unaryComponentValue i hrank) := by
  apply J.isNormGeneratorValue_fundamentalLattice i
    (J.unaryComponentValue_isNormGeneratorValue_component i hrank)
  exact J.effectiveNormOrder_eq_normGenerator_of_componentRank_eq_one i hrank

/-- A unary Jordan component is its selected scaled line. -/
noncomputable def unaryComponentSpaceIsometry {t : Nat}
    (J : JordanDecomposition q L t) (i : Fin t)
    (hrank : J.componentRank i = 1) :
    QuadraticSpace.Isometry (J.component i).space
      (QuadraticSpace.scaledLine (J.unaryComponentValue i hrank)) := by
  let c := J.unaryComponentBONG i hrank
  let e := c.exactDiagonalizationIsometry
  let line := QuadraticSpace.scaledLineDiagonalizationIsometry
    (J.unaryComponentValue i hrank)
  apply e.trans line.symm

/-- Removing a unary Jordan component from a prefix leaves its preceding
prefix and the exact norm-generator line. -/
noncomputable def prefixThroughUnaryIsometry {t : Nat}
    (J : JordanDecomposition q L t) (i : Fin t)
    (hrank : J.componentRank i = 1) :
    QuadraticSpace.Isometry
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice
        (i.val + 1)).space
      ((J.toOrthogonalDecomposition.prefixQuadraticSublattice i.val).space
        |>.orthogonalSum
          (QuadraticSpace.scaledLine (J.unaryComponentValue i hrank))) := by
  let split :=
    (J.toOrthogonalDecomposition.prefixComponentLatticeIsometry i)
      |>.toQuadraticSpaceIsometry.symm
  let component := J.unaryComponentSpaceIsometry i hrank
  exact split.trans
    ((QuadraticSpace.Isometry.refl
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice i.val).space)
      |>.orthogonalSum component)

end Lattice.JordanDecomposition

namespace BONG.JordanOrderProfileWitness.PrescribedJordanComparison

variable {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
  {J : Lattice.JordanDecomposition q L (t + 1)}

/-- Proper Jordan boundary coordinates strictly increase with the component
index.  Positivity of every component rank is the only input. -/
theorem boundaryIndex_strictMono
    (P : BONG.JordanOrderProfileWitness a.toBONG J) :
    StrictMono P.boundaryIndex := by
  intro i j hij
  let ri := Lattice.JordanDecomposition.boundaryRightIndex i
  let rj := Lattice.JordanDecomposition.boundaryRightIndex j
  have hi := P.boundaryIndex_succ_val_eq_componentRankPrefix i
  have hj := P.boundaryIndex_succ_val_eq_componentRankPrefix j
  change (P.boundaryIndex i).val + 1 =
    ∑ k ∈ Finset.Iio ri, J.componentRank k at hi
  change (P.boundaryIndex j).val + 1 =
    ∑ k ∈ Finset.Iio rj, J.componentRank k at hj
  have hsubset : Finset.Iio ri ⊆ Finset.Iio rj := by
    intro k hk
    simp only [Finset.mem_Iio] at hk ⊢
    change k.val < i.val + 1 at hk
    change k.val < j.val + 1
    omega
  have hmem : ri ∈ Finset.Iio rj := by
    simp only [Finset.mem_Iio]
    change i.val + 1 < j.val + 1
    omega
  have hnot : ri ∉ Finset.Iio ri := by simp
  have hpositive : 0 < J.componentRank ri := J.component_finrank_pos ri
  have hsum := Finset.sum_lt_sum_of_subset hsubset hmem hnot hpositive
    (fun _ _ _ ↦ Nat.zero_le _)
  change (P.boundaryIndex i).val < (P.boundaryIndex j).val
  omega

variable [DyadicDiscriminantClassLaws K]

set_option maxHeartbeats 0 in
/-- If the left trigger at a boundary is supplied by 93:28(ii) at the
preceding edge of a unary component, the shorter BONG prefix is represented
by the current prescribed Jordan prefix. -/
theorem leftRepresentation_of_previous_conditionII_of_unary
    (C : PrescribedJordanComparison a J)
    (P : BONG.JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (hz : 0 < z.val)
    (hrank : J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z) = 1)
    (hcontainment :
      let Js := C.adapted.sourceJordanSucc C.componentCount_eq
      let previous : Fin t := ⟨z.val - 1, by omega⟩
      Js.fundamentalIdeal previous < Js.fourNormOverWeightIdeal
        (Lattice.JordanDecomposition.boundaryRightIndex previous)) :
    DiagonalRepresents
      (a.prefixValues (P.boundaryIndex z).val (by omega))
      (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z)) := by
  let S := C.adapted
  let h := C.componentCount_eq
  let Js := S.sourceJordanSucc h
  let Ps := S.sourceProfileSucc h
  let previous : Fin t := ⟨z.val - 1, by omega⟩
  let c : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryLeftIndex z
  have hcval : c.val = z.val := by
    simp [c, Lattice.JordanDecomposition.boundaryLeftIndex]
  let A : Kˣ := J.unaryComponentValue c hrank
  have hAJ : Lattice.IsNormGeneratorValue q (J.fundamentalLattice c) A := by
    simpa only [A] using
      J.unaryComponentValue_isNormGeneratorValue_fundamental c hrank
  have hAJs : Lattice.IsNormGeneratorValue q (Js.fundamentalLattice c) A := by
    apply Lattice.JordanDecomposition.isNormGeneratorValue_of_normGroupSet_eq
      hAJ
    · have hg := C.sameType.normGroup_eq c
      rw [C.sameType.indexEquiv_apply_eq_self] at hg
      simpa only [Lattice.JordanDecomposition.fundamentalNormGroup] using hg
    · exact Js.exists_fundamentalNormGenerator c
  let As0 :=
    Lattice.JordanDecomposition.canonicalFundamentalNormGeneratorChoice Js
  let As := As0.replaceAt c A hAJs
  have hc : Lattice.JordanDecomposition.boundaryRightIndex previous = c := by
    apply Fin.ext
    change (z.val - 1) + 1 = z.val
    omega
  have htrigger : Js.fundamentalIdeal previous <
      Js.fourNormOverWeightIdealWith As
        (Lattice.JordanDecomposition.boundaryRightIndex previous) := by
    rw [Js.fourNormOverWeightIdealWith_eq_canonical]
    exact hcontainment
  have hembedding := (C.conditionsFromAdapted As).2.1 previous htrigger
  have hAvalue : As.value
      (Lattice.JordanDecomposition.boundaryRightIndex previous) = A := by
    rw [hc]
    simp [As]
  rw [hAvalue] at hembedding
  have hpreviousComponent : previous.val + 1 = c.val := by
    calc
      previous.val + 1 =
          (Lattice.JordanDecomposition.boundaryRightIndex previous).val := rfl
      _ = c.val := congrArg Fin.val hc
  rw [hpreviousComponent] at hembedding
  have sourceIso := (S.sourcePrefixExactDiagonalIsometry h previous).symm
  rw [hpreviousComponent] at sourceIso
  let targetIso : QuadraticSpace.Isometry
      ((J.toOrthogonalDecomposition.prefixQuadraticSublattice c.val).space
        |>.orthogonalSum (QuadraticSpace.scaledLine A))
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero
          (P.boundaryPrefixDiagonalUnits z))) := by
    simpa only [A] using
      ((J.prefixThroughUnaryIsometry c hrank).symm |>.trans
        (P.boundaryPrefixDiagonalizationIsometry z))
  unfold Lattice.QuadraticSublattice.EmbedsIntoOrthogonalSum
    QuadraticSpace.EmbedsInto at hembedding
  have hdiag :=
    (QuadraticSpace.represents_iff_of_isometries sourceIso targetIso).1
      hembedding
  have hboundary : Ps.boundaryIndex z = P.boundaryIndex z :=
    C.boundaryIndex_eq P z
  have hpreviousBoundary :
      (Ps.boundaryIndex previous).val + 1 = (P.boundaryIndex z).val := by
    have hprev := Ps.boundaryIndex_succ_val_eq_componentRankPrefix previous
    have hcurr := Ps.boundaryIndex_succ_val_eq_componentRankPrefix z
    have hrankS : Js.componentRank c = 1 := by
      have hrs := C.sameType.componentRank_eq c
      rw [C.sameType.indexEquiv_apply_eq_self] at hrs
      exact hrs.symm.trans hrank
    change (Ps.boundaryIndex previous).val + 1 =
      ∑ k ∈ Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex previous),
          Js.componentRank k at hprev
    change (Ps.boundaryIndex z).val + 1 =
      ∑ k ∈ Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex z),
          Js.componentRank k at hcurr
    have hsum :
        (∑ k ∈ Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex z),
              Js.componentRank k) =
          (∑ k ∈ Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex previous),
               Js.componentRank k) +
            Js.componentRank c := by
      have hIio : Finset.Iio
          (Lattice.JordanDecomposition.boundaryRightIndex z) =
        insert c (Finset.Iio
          (Lattice.JordanDecomposition.boundaryRightIndex previous)) := by
        ext k
        simp only [Finset.mem_Iio, Finset.mem_insert]
        change (k.val < z.val + 1 ↔ k = c ∨ k.val < (z.val - 1) + 1)
        constructor
        · intro hk
          by_cases heq : k.val = z.val
          · exact Or.inl (Fin.ext heq)
          · exact Or.inr (by omega)
        · rintro (rfl | hk)
          · exact hcval.trans_lt (Nat.lt_succ_self z.val)
          · omega
      have hnot : c ∉ Finset.Iio
          (Lattice.JordanDecomposition.boundaryRightIndex previous) := by
        simp only [Finset.mem_Iio, not_lt]
        rw [hc]
      rw [hIio, Finset.sum_insert hnot]
      exact Nat.add_comm _ _
    rw [hsum, hrankS] at hcurr
    omega
  have hpreviousBoundary' :
      ((S.sourceProfileSucc h).boundaryIndex previous).val + 1 =
        (P.boundaryIndex z).val := by
    simpa only [Ps] using hpreviousBoundary
  have hdiag' : DiagonalRepresents
      (diagonalUnitCoefficients
        (a.prefixValueUnits
          (((S.sourceProfileSucc h).boundaryIndex previous).val + 1)
          (by omega)))
      (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z)) := by
    apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      (a.prefixValueUnits
        (((S.sourceProfileSucc h).boundaryIndex previous).val + 1) (by omega))
      (P.boundaryPrefixDiagonalUnits z)).1
    unfold GoodBONG.prefixExactDiagonalSpace at hdiag
    convert hdiag using 1 <;> rfl
  exact BONG.GoodBONG.sourcePrefixRepresents_cast
    (sourceBound := by omega) (sourceBound' := by omega) a
    (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
    hpreviousBoundary' hdiag'

set_option maxHeartbeats 0 in
/-- If the right trigger at a boundary is supplied by 93:28(iii) at the
following edge of a unary component, Witt cancellation gives the required
representation by the BONG prefix through that component. -/
theorem rightRepresentation_of_next_conditionIII_of_unary
    (C : PrescribedJordanComparison a J)
    (P : BONG.JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (hz : z.val + 1 < t)
    (hrank : J.componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex z) = 1)
    (hcontainment :
      let next : Fin t := ⟨z.val + 1, hz⟩
      J.fundamentalIdeal next < J.fourNormOverWeightIdeal
        (Lattice.JordanDecomposition.boundaryLeftIndex next)) :
    DiagonalRepresents
      (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
      (a.prefixValues ((P.boundaryIndex z).val + 2) (by omega)) := by
  letI : Module.Finite K V := L.moduleFinite
  let S := C.adapted
  let h := C.componentCount_eq
  let Js := S.sourceJordanSucc h
  let Ps := S.sourceProfileSucc h
  let next : Fin t := ⟨z.val + 1, hz⟩
  let c : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex z
  have hcval : c.val = z.val + 1 := rfl
  have hc : Lattice.JordanDecomposition.boundaryLeftIndex next = c := by
    apply Fin.ext
    rfl
  let A : Kˣ := J.unaryComponentValue c hrank
  have hAJ : Lattice.IsNormGeneratorValue q (J.fundamentalLattice c) A := by
    simpa only [A] using
      J.unaryComponentValue_isNormGeneratorValue_fundamental c hrank
  let Ap0 :=
    Lattice.JordanDecomposition.canonicalFundamentalNormGeneratorChoice J
  let Ap := Ap0.replaceAt c A hAJ
  have htrigger : J.fundamentalIdeal next <
      J.fourNormOverWeightIdealWith Ap
        (Lattice.JordanDecomposition.boundaryLeftIndex next) := by
    rw [J.fourNormOverWeightIdealWith_eq_canonical]
    exact hcontainment
  have hembedding := (C.conditionsFromPrescribed Ap).2.2 next htrigger
  have hAvalue : Ap.value
      (Lattice.JordanDecomposition.boundaryLeftIndex next) = A := by
    rw [hc]
    simp [Ap]
  rw [hAvalue] at hembedding
  have hnextComponent : next.val + 1 = c.val + 1 := by
    rw [hcval]
  rw [hnextComponent] at hembedding
  unfold Lattice.QuadraticSublattice.EmbedsIntoOrthogonalSum
    QuadraticSpace.EmbedsInto at hembedding
  let currentJ :=
    (J.toOrthogonalDecomposition.prefixQuadraticSublattice c.val).space
  let throughJs :=
    (Js.toOrthogonalDecomposition.prefixQuadraticSublattice
      (c.val + 1)).space
  let line := QuadraticSpace.scaledLine A
  let sourceSwap : QuadraticSpace.Isometry
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice
        (c.val + 1)).space
      (line.orthogonalSum currentJ) := by
    exact (J.prefixThroughUnaryIsometry c hrank).trans
      (QuadraticSpace.orthogonalSumSwap currentJ line)
  let targetSwap : QuadraticSpace.Isometry
      (throughJs.orthogonalSum line) (line.orthogonalSum throughJs) :=
    QuadraticSpace.orthogonalSumSwap throughJs line
  have hswapped :=
    (QuadraticSpace.represents_iff_of_isometries sourceSwap targetSwap).1
      hembedding
  have hcancelled : throughJs.Represents currentJ := by
    exact QuadraticSpace.orthogonalSumCancelRepresents line line
      currentJ throughJs (QuadraticSpace.Isometry.refl line) hswapped
  have hboundary : Ps.boundaryIndex z = P.boundaryIndex z :=
    C.boundaryIndex_eq P z
  have hrankS : Js.componentRank c = 1 := by
    have hrs := C.sameType.componentRank_eq c
    rw [C.sameType.indexEquiv_apply_eq_self] at hrs
    exact hrs.symm.trans hrank
  have hnextBoundary :
      (Ps.boundaryIndex next).val + 1 =
        (P.boundaryIndex z).val + 2 := by
    have hcurr := Ps.boundaryIndex_succ_val_eq_componentRankPrefix z
    have hnext := Ps.boundaryIndex_succ_val_eq_componentRankPrefix next
    change (Ps.boundaryIndex z).val + 1 =
      ∑ k ∈ Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex z),
          Js.componentRank k at hcurr
    change (Ps.boundaryIndex next).val + 1 =
      ∑ k ∈ Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex next),
          Js.componentRank k at hnext
    have hIio : Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex next) =
      insert c (Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex z)) := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_insert]
      change (k.val < z.val + 2 ↔ k = c ∨ k.val < z.val + 1)
      constructor
      · intro hk
        by_cases heq : k.val = z.val + 1
        · exact Or.inl (Fin.ext (heq.trans hcval.symm))
        · exact Or.inr (by omega)
      · rintro (rfl | hk)
        · omega
        · omega
    have hnot : c ∉ Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex z) := by
      simp only [Finset.mem_Iio, not_lt]
      rw [show Lattice.JordanDecomposition.boundaryRightIndex z = c by rfl]
    rw [hIio, Finset.sum_insert hnot, hrankS] at hnext
    rw [hboundary] at hcurr
    omega
  have sourceIso := P.boundaryPrefixDiagonalizationIsometry z
  have targetIso := (S.sourcePrefixExactDiagonalIsometry h next).symm
  rw [hnextComponent] at targetIso
  have hdiagSpace :=
    (QuadraticSpace.represents_iff_of_isometries sourceIso targetIso).1
      hcancelled
  have hdiag : DiagonalRepresents
      (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
      (diagonalUnitCoefficients
        (a.prefixValueUnits
          (((S.sourceProfileSucc h).boundaryIndex next).val + 1)
          (by omega))) := by
    apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      (P.boundaryPrefixDiagonalUnits z)
      (a.prefixValueUnits
        (((S.sourceProfileSucc h).boundaryIndex next).val + 1)
        (by omega))).1
    unfold GoodBONG.prefixExactDiagonalSpace at hdiagSpace
    convert hdiagSpace using 1 <;> rfl
  have hnextBoundary' :
      ((S.sourceProfileSucc h).boundaryIndex next).val + 1 =
        (P.boundaryIndex z).val + 2 := by
    simpa only [Ps] using hnextBoundary
  exact BONG.GoodBONG.targetPrefixRepresents_cast
    (targetBound := by omega) (targetBound' := by omega)
    (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z)) a
    hnextBoundary' hdiag

end BONG.JordanOrderProfileWitness.PrescribedJordanComparison

end Bong
