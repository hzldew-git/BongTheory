import Bong.Bong.Beli2019Lemma34UnaryCollision

namespace Bong

open Dyadic Module
open BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.JordanOrderProfileWitness.PrescribedJordanComparison

variable {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
  {J : Lattice.JordanDecomposition q L (t + 1)}

set_option maxHeartbeats 0 in
theorem boundary_leftRepresentation
    (C : PrescribedJordanComparison a J)
    (P : BONG.JordanOrderProfileWitness a.toBONG J) (z : Fin t) :
    a.leftApproximationTrigger (P.boundaryIndex z) →
      DiagonalRepresents
        (a.prefixValues (P.boundaryIndex z).val (by omega))
        (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z)) := by
  intro htrigger
  rcases htrigger with hzero | ⟨hpositive, hsum⟩
  · exact DiagonalRepresents.of_source_length_eq_zero
      (a.prefixValues (P.boundaryIndex z).val (by omega))
      (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z)) hzero
  · let S := C.adapted
    let h := C.componentCount_eq
    let Js := S.sourceJordanSucc h
    let Ps := S.sourceProfileSucc h
    have hboundary : Ps.boundaryIndex z = P.boundaryIndex z :=
      C.boundaryIndex_eq P z
    let i : Fin (n + 1) := ⟨(P.boundaryIndex z).val, by omega⟩
    have hi : 0 < i.val := by simpa only [i] using hpositive
    have hsum' : 2 * (ramificationIndex K : ℚ) <
        a.alphaValue ⟨i.val - 1, by omega⟩ + a.alphaValue i := by
      simpa only [i] using hsum
    rcases S.internalTrigger_has_adjacentContainment h i hi hsum' with
      ⟨z0, hindex, hcontainment⟩ | ⟨z0, hindex, hcontainment⟩
    · have hvalue : (Ps.boundaryIndex z0).val + 1 =
          (Ps.boundaryIndex z).val := by
        rw [hboundary]
        exact hindex.symm
      have hz0lt : z0 < z := by
        rcases lt_trichotomy z0 z with hlt | heq | hgt
        · exact hlt
        · subst z0
          omega
        · have hb := boundaryIndex_strictMono Ps hgt
          omega
      have hadjacent : z0.val + 1 = z.val := by
        by_contra hne
        have hgap : z0.val + 1 < z.val := by omega
        let middle : Fin t := ⟨z0.val + 1, by omega⟩
        have hleft : z0 < middle := by
          change z0.val < z0.val + 1
          omega
        have hright : middle < z := by
          change z0.val + 1 < z.val
          exact hgap
        have hb₁ := boundaryIndex_strictMono Ps hleft
        have hb₂ := boundaryIndex_strictMono Ps hright
        omega
      let previous : Fin t := ⟨z.val - 1, by omega⟩
      have hz0eq : z0 = previous := by
        apply Fin.ext
        dsimp only [previous]
        omega
      let c : Fin (t + 1) :=
        Lattice.JordanDecomposition.boundaryLeftIndex z
      have hrankS : Js.componentRank c = 1 := by
        have hprev := Ps.boundaryIndex_succ_val_eq_componentRankPrefix z0
        have hcurr := Ps.boundaryIndex_succ_val_eq_componentRankPrefix z
        change (Ps.boundaryIndex z0).val + 1 =
          ∑ k ∈ Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex z0),
              Js.componentRank k at hprev
        change (Ps.boundaryIndex z).val + 1 =
          ∑ k ∈ Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex z),
              Js.componentRank k at hcurr
        have hcprev :
            Lattice.JordanDecomposition.boundaryRightIndex z0 = c := by
          apply Fin.ext
          change z0.val + 1 = z.val
          exact hadjacent
        have hIio : Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex z) =
          insert c (Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex z0)) := by
          ext k
          simp only [Finset.mem_Iio, Finset.mem_insert]
          change (k.val < z.val + 1 ↔ k = c ∨ k.val < z0.val + 1)
          constructor
          · intro hk
            by_cases heq : k.val = z.val
            · exact Or.inl (Fin.ext heq)
            · exact Or.inr (by omega)
          · rintro (rfl | hk)
            · simp [c, Lattice.JordanDecomposition.boundaryLeftIndex]
            · omega
        have hnot : c ∉ Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex z0) := by
          simp only [Finset.mem_Iio, not_lt]
          rw [hcprev]
        rw [hIio, Finset.sum_insert hnot] at hcurr
        omega
      have hrankJ : J.componentRank c = 1 := by
        have hrs := C.sameType.componentRank_eq c
        rw [C.sameType.indexEquiv_apply_eq_self] at hrs
        exact hrs.trans hrankS
      apply C.leftRepresentation_of_previous_conditionII_of_unary P z
        (by omega) hrankJ
      simpa only [previous, Js, hz0eq] using hcontainment
    · have hz0 : z0 = z := by
        apply (boundaryIndex_strictMono Ps).injective
        apply Fin.ext
        rw [hboundary]
        exact hindex.symm
      subst z0
      apply C.leftRepresentation_of_conditionIII P z
      rw [C.sameType.fundamentalIdeal_eq z,
        C.sameType.fourNormOverWeightIdeal_eq
          (Lattice.JordanDecomposition.boundaryLeftIndex z)]
      exact hcontainment

omit [DyadicDiscriminantClassLaws K] in
set_option maxHeartbeats 0 in
theorem boundary_rightRepresentation_of_terminal
    (P : BONG.JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (hterminal : (P.boundaryIndex z).val + 1 = n + 1) :
    DiagonalRepresents
      (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
      (a.prefixValues ((P.boundaryIndex z).val + 2) (by omega)) := by
  let Qprefix := J.toOrthogonalDecomposition.prefixQuadraticSublattice
    (z.val + 1)
  have hinclusion : q.Represents Qprefix.space := by
    refine ⟨{
      toLinearMap := Submodule.subtype Qprefix.carrier
      injective := Subtype.val_injective
      map_bilin := ?_ }⟩
    intro x y
    rfl
  have hspace :=
    (QuadraticSpace.represents_iff_of_isometries
      (P.boundaryPrefixDiagonalizationIsometry z)
      a.toBONG.exactDiagonalizationIsometry).1 hinclusion
  have hdiagFull : DiagonalRepresents
      (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
      (diagonalUnitCoefficients a.valueUnit) := by
    apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      (P.boundaryPrefixDiagonalUnits z) a.valueUnit).1
    unfold BONG.exactDiagonalSpace at hspace
    convert hspace using 1 <;> rfl
  have hfull : DiagonalRepresents
      (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
      (a.prefixValues (n + 2) (by omega)) := by
    have htarget : a.prefixValues (n + 2) (by omega) =
        diagonalUnitCoefficients a.valueUnit := by
      funext i
      rfl
    rw [htarget]
    exact hdiagFull
  exact BONG.GoodBONG.targetPrefixRepresents_cast
    (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z)) a
    (by omega) hfull

set_option maxHeartbeats 0 in
theorem boundary_rightRepresentation
    (C : PrescribedJordanComparison a J)
    (P : BONG.JordanOrderProfileWitness a.toBONG J) (z : Fin t) :
    a.rightApproximationTrigger (P.boundaryIndex z) →
      DiagonalRepresents
        (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
        (a.prefixValues ((P.boundaryIndex z).val + 2) (by omega)) := by
  intro htrigger
  rcases htrigger with hterminal | ⟨hinternal, hsum⟩
  · exact boundary_rightRepresentation_of_terminal P z hterminal
  · let S := C.adapted
    let h := C.componentCount_eq
    let Js := S.sourceJordanSucc h
    let Ps := S.sourceProfileSucc h
    have hboundary : Ps.boundaryIndex z = P.boundaryIndex z :=
      C.boundaryIndex_eq P z
    let i : Fin (n + 1) := ⟨(P.boundaryIndex z).val + 1, by omega⟩
    have hi : 0 < i.val := by simp only [i]; omega
    have hsum' : 2 * (ramificationIndex K : ℚ) <
        a.alphaValue ⟨i.val - 1, by omega⟩ + a.alphaValue i := by
      have hprevious : (⟨i.val - 1, by omega⟩ : Fin (n + 1)) =
          P.boundaryIndex z := by
        apply Fin.ext
        simp only [i]
        omega
      rw [hprevious]
      simpa only [i] using hsum
    rcases S.internalTrigger_has_adjacentContainment h i hi hsum' with
      ⟨z0, hindex, hcontainment⟩ | ⟨z0, hindex, hcontainment⟩
    · have hz0 : z0 = z := by
        apply (boundaryIndex_strictMono Ps).injective
        apply Fin.ext
        have hvalue : (Ps.boundaryIndex z0).val =
            (P.boundaryIndex z).val := by
          change (P.boundaryIndex z).val + 1 =
              (Ps.boundaryIndex z0).val + 1 at hindex
          omega
        rw [hboundary]
        exact hvalue
      subst z0
      apply C.rightRepresentation_of_conditionII P z
      rw [C.sameType.fundamentalIdeal_eq z,
        C.sameType.fourNormOverWeightIdeal_eq
          (Lattice.JordanDecomposition.boundaryRightIndex z)]
      exact hcontainment
    · have hvalue : (Ps.boundaryIndex z).val + 1 =
          (Ps.boundaryIndex z0).val := by
        rw [hboundary]
        exact hindex
      have hzlt : z < z0 := by
        rcases lt_trichotomy z z0 with hlt | heq | hgt
        · exact hlt
        · subst z0
          omega
        · have hb := boundaryIndex_strictMono Ps hgt
          omega
      have hadjacent : z.val + 1 = z0.val := by
        by_contra hne
        have hgap : z.val + 1 < z0.val := by omega
        let middle : Fin t := ⟨z.val + 1, by omega⟩
        have hleft : z < middle := by
          change z.val < z.val + 1
          omega
        have hright : middle < z0 := by
          change z.val + 1 < z0.val
          exact hgap
        have hb₁ := boundaryIndex_strictMono Ps hleft
        have hb₂ := boundaryIndex_strictMono Ps hright
        omega
      have hnext : z.val + 1 < t := by omega
      let next : Fin t := ⟨z.val + 1, hnext⟩
      have hz0eq : z0 = next := by
        apply Fin.ext
        dsimp only [next]
        omega
      let c : Fin (t + 1) :=
        Lattice.JordanDecomposition.boundaryRightIndex z
      have hrankS : Js.componentRank c = 1 := by
        have hcurr := Ps.boundaryIndex_succ_val_eq_componentRankPrefix z
        have hnextBoundary :=
          Ps.boundaryIndex_succ_val_eq_componentRankPrefix z0
        change (Ps.boundaryIndex z).val + 1 =
          ∑ k ∈ Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex z),
              Js.componentRank k at hcurr
        change (Ps.boundaryIndex z0).val + 1 =
          ∑ k ∈ Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex z0),
              Js.componentRank k at hnextBoundary
        have hcnext :
            Lattice.JordanDecomposition.boundaryRightIndex z = c := rfl
        have hIio : Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex z0) =
          insert c (Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex z)) := by
          ext k
          simp only [Finset.mem_Iio, Finset.mem_insert]
          change (k.val < z0.val + 1 ↔ k = c ∨ k.val < z.val + 1)
          constructor
          · intro hk
            by_cases heq : k.val = z.val + 1
            · exact Or.inl (Fin.ext heq)
            · exact Or.inr (by omega)
          · rintro (rfl | hk)
            · simp [c, Lattice.JordanDecomposition.boundaryRightIndex]
              omega
            · omega
        have hnot : c ∉ Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex z) := by
          simp only [Finset.mem_Iio, not_lt]
          rw [hcnext]
        rw [hIio, Finset.sum_insert hnot] at hnextBoundary
        omega
      have hrankJ : J.componentRank c = 1 := by
        have hrs := C.sameType.componentRank_eq c
        rw [C.sameType.indexEquiv_apply_eq_self] at hrs
        exact hrs.trans hrankS
      apply C.rightRepresentation_of_next_conditionIII_of_unary P z
        hnext hrankJ
      change J.fundamentalIdeal next < J.fourNormOverWeightIdeal
        (Lattice.JordanDecomposition.boundaryLeftIndex next)
      rw [C.sameType.fundamentalIdeal_eq next,
        C.sameType.fourNormOverWeightIdeal_eq
          (Lattice.JordanDecomposition.boundaryLeftIndex next)]
      simpa only [next, Js, hz0eq] using hcontainment

set_option maxHeartbeats 0 in
/-- Beli (2019), Lemma 3.4(i), reduced only to the determinant comparison:
the two representation clauses are discharged from the adjacent O'Meara
boundary identities, including the unary collision and terminal cases. -/
theorem boundary_isSpaceApproximation
    (C : PrescribedJordanComparison a J)
    (P : BONG.JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (hdet : a.IsPrefixApproximation ((P.boundaryIndex z).val + 1)
      (diagonalUnitDeterminant (P.boundaryPrefixDiagonalUnits z))) :
    a.IsSpaceApproximation (P.boundaryIndex z)
      (P.boundaryPrefixDiagonalUnits z) := by
  constructor
  · exact ⟨hdet, C.boundary_leftRepresentation P z⟩
  · exact ⟨hdet, C.boundary_rightRepresentation P z⟩

set_option maxHeartbeats 0 in
/-- Beli (2019), Lemma 3.4(i): a complete strict-Jordan prefix is a
two-sided space approximation to the corresponding good-BONG prefix. -/
theorem beli2019Lemma34_i
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : BONG.JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (z : Fin t) :
    a.IsSpaceApproximation (P.boundaryIndex z)
      (P.boundaryPrefixDiagonalUnits z) := by
  let J := W.toJordan hstrict
  let C := PrescribedJordanComparison.ofProfile a J
  apply C.boundary_isSpaceApproximation P z
  exact P.boundaryPrefixDiagonalUnits_isPrefixApproximation a W hW hstrict z

end BONG.JordanOrderProfileWitness.PrescribedJordanComparison

end Bong
