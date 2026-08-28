/- Beli 2019, Lemma 3.7(iv): binary endpoint cases. -/
import Bong.Bong.Beli2019Lemma37Binary

namespace Bong

open Dyadic Module
open BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.JordanOrderProfileWitness.PrescribedJordanComparison

set_option maxHeartbeats 0 in
/-- At the first binary Jordan component, deleting the second norm-generator
line from two presentations of the component identifies the selected first
line with the one-before-boundary complement model. -/
theorem firstBinaryReplacement_diagonalRepresents
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : BONG.JordanOrderProfileWitness a.toBONG J)
    (z : Fin t) (hz : z.val = 0) (A : Kˣ)
    (D : BONG.JordanBinaryNormGeneratorComplementData J 0 A)
    (M : BONG.JordanOrderProfileWitness.BoundaryOneBeforeModel
      P z D.second)
    (hrank : J.componentRank 0 = 2) :
    let hrightRank : 1 < J.componentRank
        (Lattice.JordanDecomposition.boundaryLeftIndex z) := by
      have hcomponent :
          Lattice.JordanDecomposition.boundaryLeftIndex z = (0 : Fin (t + 1)) := by
        apply Fin.ext
        exact hz
      rw [hcomponent, hrank]
      omega
    DiagonalRepresents
      (diagonalUnitCoefficients (fun _ : Fin 1 ↦ A))
      (diagonalUnitCoefficients (M.approximationUnits hrightRank)) := by
  have hcomponent :
      Lattice.JordanDecomposition.boundaryLeftIndex z = (0 : Fin (t + 1)) := by
    apply Fin.ext
    exact hz
  let hrightRank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z) := by
    rw [hcomponent, hrank]
    omega
  let leftUnits : Fin 1 → Kˣ := fun _ ↦ A
  let leftModel := QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients leftUnits)
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero leftUnits)
  let rightModel := QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients M.units)
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero M.units)
  let line := QuadraticSpace.scaledLine D.second
  have hsnoc : Fin.snoc leftUnits D.second = ![A, D.second] := by
    funext i
    fin_cases i <;> rfl
  let leftPair :=
    QuadraticSpace.finiteDiagonalOrthogonalSumScaledLineIsometry
      leftUnits D.second
  rw [hsnoc] at leftPair
  let leftTotal : QuadraticSpace.Isometry
      (leftModel.orthogonalSum line) (J.prefixSpace 1) :=
    leftPair.trans <|
      D.componentDiagonalIsometry.trans <|
        J.toOrthogonalDecomposition.firstComponentPrefixLatticeIsometry
          |>.toQuadraticSpaceIsometry
  have hzPrefix : z.val + 1 = 1 := by omega
  let rightTotal := M.splitIsometry.symm
  rw [hzPrefix] at rightTotal
  let totalIso : QuadraticSpace.Isometry
      (leftModel.orthogonalSum line) (rightModel.orthogonalSum line) :=
    leftTotal.trans rightTotal
  let swappedIso : QuadraticSpace.Isometry
      (line.orthogonalSum leftModel) (line.orthogonalSum rightModel) :=
    (QuadraticSpace.orthogonalSumSwap line leftModel).trans
      (totalIso.trans (QuadraticSpace.orthogonalSumSwap rightModel line))
  have hrepSpace : rightModel.Represents leftModel := by
    exact QuadraticSpace.orthogonalSumCancelRepresents line line
      leftModel rightModel (QuadraticSpace.Isometry.refl line)
      ⟨swappedIso.toRepresentation⟩
  let e := M.rankEquiv hrightRank
  let reindexIso := QuadraticSpace.finiteDiagonalReindexIsometry
    (diagonalUnitCoefficients M.units)
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero M.units) e
  have hrepReindexed :
      (QuadraticSpace.finiteDiagonal
        (fun i ↦ (M.units (e i) : K))
        (fun i ↦ Units.ne_zero (M.units (e i)))).Represents leftModel := by
    exact (QuadraticSpace.represents_iff_of_isometries
      (QuadraticSpace.Isometry.refl leftModel) reindexIso).1 hrepSpace
  apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
    leftUnits (M.approximationUnits hrightRank)).1
  change (QuadraticSpace.finiteDiagonal
      (fun i ↦ (M.units (e i) : K))
      (fun i ↦ Units.ne_zero (M.units (e i)))).Represents leftModel
  exact hrepReindexed

set_option maxHeartbeats 0 in
/-- At the final binary component, the replacement prefix together with its
second norm-generator line is the whole quadratic space, so the replacement
prefix is represented by the complete good-BONG diagonal. -/
theorem binaryReplacement_rightRepresentation_of_terminal
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : BONG.JordanOrderProfileWitness a.toBONG J)
    (z : Fin t) (A : Kˣ)
    (D : BONG.JordanBinaryNormGeneratorComplementData J
      (Lattice.JordanDecomposition.boundaryRightIndex z) A)
    (hrank : J.componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex z) = 2)
    (hprefixFull : z.val + 2 = t + 1)
    (hterminal :
      (P.boundaryOneAfterIndex z (by rw [hrank]; omega)).val + 1 = n + 1) :
    let hleftRank : 1 < J.componentRank
        (Lattice.JordanDecomposition.boundaryRightIndex z) := by
      rw [hrank]
      omega
    DiagonalRepresents
      (diagonalUnitCoefficients (P.boundaryOneAfterDiagonalUnits z A))
      (a.prefixValues
        ((P.boundaryOneAfterIndex z hleftRank).val + 2) (by omega)) := by
  let hleftRank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex z) := by
    rw [hrank]
    omega
  let model := QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients (P.boundaryOneAfterDiagonalUnits z A))
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero
      (P.boundaryOneAfterDiagonalUnits z A))
  let line := QuadraticSpace.scaledLine D.second
  let assembled := P.binaryReplacementPrefixIsometry z A D
  rw [hprefixFull] at assembled
  let fullIso : QuadraticSpace.Isometry (model.orthogonalSum line) q :=
    assembled.trans
      J.toOrthogonalDecomposition.fullPrefixLatticeIsometry.toQuadraticSpaceIsometry
  have hspace : q.Represents model := by
    exact ⟨fullIso.toRepresentation.trans
      (QuadraticSpace.Representation.orthogonalSumInl model line)⟩
  have hdiagonalSpace : a.toBONG.exactDiagonalSpace.Represents model := by
    exact ⟨a.toBONG.exactDiagonalizationIsometry.toRepresentation.trans
      (Classical.choice hspace)⟩
  have hdiagFull : DiagonalRepresents
      (diagonalUnitCoefficients (P.boundaryOneAfterDiagonalUnits z A))
      (diagonalUnitCoefficients a.valueUnit) := by
    apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      (P.boundaryOneAfterDiagonalUnits z A) a.valueUnit).1
    unfold BONG.exactDiagonalSpace at hdiagonalSpace
    convert hdiagonalSpace using 1 <;> rfl
  have hfull : DiagonalRepresents
      (diagonalUnitCoefficients (P.boundaryOneAfterDiagonalUnits z A))
      (a.prefixValues (n + 2) (by omega)) := by
    have htarget : a.prefixValues (n + 2) (by omega) =
        diagonalUnitCoefficients a.valueUnit := by
      funext i
      rfl
    rw [htarget]
    exact hdiagFull
  have hterminal' :
      (P.boundaryOneAfterIndex z hleftRank).val + 1 = n + 1 := by
    simpa only [BONG.JordanOrderProfileWitness.boundaryOneAfterIndex]
      using hterminal
  have hlength :
      (P.boundaryOneAfterIndex z hleftRank).val + 2 = n + 2 := by
    omega
  apply BONG.GoodBONG.targetPrefixRepresents_cast
    (diagonalUnitCoefficients (P.boundaryOneAfterDiagonalUnits z A)) a
    hlength.symm
  exact hfull

set_option maxHeartbeats 0 in
/-- If the binary component is the whole Jordan decomposition, its selected
norm-generator line is represented by the complete good-BONG diagonal. -/
theorem firstBinaryLine_rightRepresentation_of_singleton
    {n : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L 1}
    (A : Kˣ)
    (D : BONG.JordanBinaryNormGeneratorComplementData J 0 A) :
    DiagonalRepresents
      (diagonalUnitCoefficients (fun _ : Fin 1 ↦ A))
      (a.prefixValues (n + 2) (by omega)) := by
  let units : Fin 1 → Kˣ := fun _ ↦ A
  let model := QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients units)
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero units)
  let line := QuadraticSpace.scaledLine D.second
  have hsnoc : Fin.snoc units D.second = ![A, D.second] := by
    funext i
    fin_cases i <;> rfl
  let pair := QuadraticSpace.finiteDiagonalOrthogonalSumScaledLineIsometry
    units D.second
  rw [hsnoc] at pair
  let fullIso : QuadraticSpace.Isometry (model.orthogonalSum line) q :=
    pair.trans <|
      D.componentDiagonalIsometry.trans <|
        J.toOrthogonalDecomposition.singleComponentLatticeIsometry
          |>.toQuadraticSpaceIsometry
  have hspace : q.Represents model := by
    exact ⟨fullIso.toRepresentation.trans
      (QuadraticSpace.Representation.orthogonalSumInl model line)⟩
  have hdiagonalSpace : a.toBONG.exactDiagonalSpace.Represents model := by
    exact ⟨a.toBONG.exactDiagonalizationIsometry.toRepresentation.trans
      (Classical.choice hspace)⟩
  have hdiagFull : DiagonalRepresents
      (diagonalUnitCoefficients units)
      (diagonalUnitCoefficients a.valueUnit) := by
    apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      units a.valueUnit).1
    unfold BONG.exactDiagonalSpace at hdiagonalSpace
    convert hdiagonalSpace using 1 <;> rfl
  have htarget : a.prefixValues (n + 2) (by omega) =
      diagonalUnitCoefficients a.valueUnit := by
    funext i
    rfl
  rw [htarget]
  exact hdiagFull

set_option maxHeartbeats 0 in
/-- The line selected in the first Jordan component supplies the left half
of the endpoint case of Beli (2019), Lemma 3.7(iv). -/
theorem firstLine_isLeftSpaceApproximation
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : BONG.JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice 0) A)
    (hrank : 1 < (W.toJordan hstrict).componentRank 0) :
    a.IsLeftSpaceApproximation (0 : Fin (n + 1))
      (fun _ : Fin 1 ↦ A) := by
  let p : Fin (t + 1) := 0
  let w := BONG.WeakJordanOrderProfileWitness.ofStrict W hstrict P
  let Cb := w.jordanBlockCoordinates hW p
  have hstart : Cb.start = 0 := by
    change w.componentStart p = 0
    unfold BONG.WeakJordanOrderProfileWitness.componentStart
    simp [p]
  have hodd : Cb.start + 1 < Cb.stop := by
    change Cb.start + 1 < Cb.start + finrank K (W.component p).carrier
    change 1 < finrank K (W.component p).carrier at hrank
    omega
  let determinant :=
    BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedDataAny
      W hW hstrict P p
  let seeds :=
    BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWithAny
      W hW hstrict P p determinant A hA
  have hseed := seeds.oddApproximation 0 hodd
  have hleftDet : determinant.leftDet = 1 :=
    BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedDataAny_leftDet_of_component_zero
      W hW hstrict P p rfl
  have hdet : a.IsPrefixApproximation 1 A := by
    simpa only [seeds, Cb, w, Nat.mul_zero, add_zero, pow_zero, one_mul,
      BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWithAny_normGenerator,
      BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWithAny_leftDet,
      determinant, hleftDet, mul_one, hstart] using hseed
  constructor
  · simpa [diagonalUnitDeterminant] using hdet
  · intro _
    exact DiagonalRepresents.of_source_length_eq_zero
      (a.prefixValues 0 (by omega))
      (diagonalUnitCoefficients (fun _ : Fin 1 ↦ A)) rfl

set_option maxHeartbeats 0 in
/-- Beli (2019), Lemma 3.7(iv), at the first binary Jordan component when a
following component is present. -/
theorem beli2019Lemma37_iv_first_nonterminal
    [DyadicDiscriminantClassLaws K]
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : BONG.JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (hnonterminal : 1 < t + 1)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice 0) A)
    (hvalue : (A : K) ∈ Lattice.quadraticValueSet
      ((W.toJordan hstrict).component 0).space
      ((W.toJordan hstrict).component 0).lattice)
    (hrank : (W.toJordan hstrict).componentRank 0 = 2)
    (hrightOuter : ∀ hp : (0 : Fin (t + 1)).val + 1 < t + 1,
      a.order (P.profileComponentFirstIndex 0) <
      a.order (P.profileComponentFirstIndex
        ⟨(0 : Fin (t + 1)).val + 1, by omega⟩)) :
    let zRight : Fin t := ⟨0, by omega⟩
    ∃ (A' : Kˣ) (M : BONG.JordanOrderProfileWitness.BoundaryOneBeforeModel
        P zRight A')
      (hrightRank : 1 < (W.toJordan hstrict).componentRank
        (Lattice.JordanDecomposition.boundaryLeftIndex zRight)),
      (0 : Fin (n + 1)) = P.boundaryOneBeforeIndex zRight hrightRank ∧
        a.IsSpaceApproximation (0 : Fin (n + 1))
          (fun _ : Fin 1 ↦ A) ∧
        a.IsSpaceApproximation
          (P.boundaryOneBeforeIndex zRight hrightRank)
          (M.approximationUnits hrightRank) ∧
        DiagonalRepresents
          (diagonalUnitCoefficients (fun _ : Fin 1 ↦ A))
          (diagonalUnitCoefficients
            (M.approximationUnits hrightRank)) := by
  let J := W.toJordan hstrict
  let p : Fin (t + 1) := 0
  let pNext : Fin (t + 1) := ⟨1, hnonterminal⟩
  let zRight : Fin t := ⟨0, by omega⟩
  have hcomponent :
      Lattice.JordanDecomposition.boundaryLeftIndex zRight = p := by
    apply Fin.ext
    rfl
  let hrightRank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex zRight) := by
    rw [hcomponent, hrank]
    omega
  have heffective : BONG.jordanEffectiveNormOrder J p =
      ordUnit K (J.normGenerator p) := by
    apply P.beli2019Lemma36 W hW hstrict p hrank
    · intro hp
      simp [p] at hp
    · simpa only [p] using hrightOuter
  let D := BONG.JordanBinaryNormGeneratorComplementData.ofQuadraticValue
    J p A hrank heffective hA hvalue
  have hline : (J.prefixSpace (zRight.val + 1)).Represents
      (QuadraticSpace.scaledLine D.second) := by
    have hraw := D.secondLineRepresentation
    have hpval : p.val + 1 = zRight.val + 1 := by
      simp [p, zRight]
    rw [hpval] at hraw
    exact hraw
  let M := BONG.JordanOrderProfileWitness.BoundaryOneBeforeModel.ofLineRepresentation
    (P := P) (z := zRight) (A := D.second) hline
  have hASecond : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex zRight)) D.second := by
    rw [hcomponent]
    exact D.second_isNormGeneratorValue
  have hleftOne := firstLine_isLeftSpaceApproximation
    a W hW hstrict P A hA (by rw [hrank]; omega)
  have hrightOne := beli2019Lemma34_iii
    a W hW hstrict P zRight D.second hASecond M hrightRank
  have hindex : (0 : Fin (n + 1)) =
      P.boundaryOneBeforeIndex zRight hrightRank := by
    have hb := P.boundaryIndex_succ_val_eq_componentRankPrefix zRight
    have hrightIndex :
        Lattice.JordanDecomposition.boundaryRightIndex zRight =
          pNext := by
      apply Fin.ext
      simp [Lattice.JordanDecomposition.boundaryRightIndex, zRight, pNext]
    rw [hrightIndex] at hb
    have hIio : Finset.Iio pNext = {p} := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_singleton]
      change (k.val < 1 ↔ k = p)
      constructor
      · intro hk
        apply Fin.ext
        simp only [p, Fin.val_zero]
        omega
      · rintro rfl
        simp [p]
    change (P.boundaryIndex zRight).val + 1 =
      ∑ k ∈ Finset.Iio pNext, J.componentRank k at hb
    rw [hIio, Finset.sum_singleton, hrank] at hb
    apply Fin.ext
    change 0 = (P.boundaryOneBeforeIndex zRight hrightRank).val
    have hbefore := P.boundaryOneBeforeIndex_succ_val zRight hrightRank
    omega
  have hdiag := firstBinaryReplacement_diagonalRepresents
    P zRight rfl A D M hrank
  have hboth := a.spaceApproximations_of_left_right_of_eq
    (0 : Fin (n + 1))
    (P.boundaryOneBeforeIndex zRight hrightRank) hindex
    (fun _ : Fin 1 ↦ A) (M.approximationUnits hrightRank)
    hleftOne hrightOne hdiag
  refine ⟨D.second, M, hrightRank, hindex, hboth.1, hboth.2, hdiag⟩

set_option maxHeartbeats 0 in
/-- Beli (2019), Lemma 3.7(iv), at a final binary Jordan component with a
nonempty preceding prefix. -/
theorem beli2019Lemma37_iv_last_nonsingleton
    [DyadicDiscriminantClassLaws K]
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : BONG.JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin (t + 1)) (hppos : 0 < p.val)
    (hpLast : p.val + 1 = t + 1)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice p) A)
    (hvalue : (A : K) ∈ Lattice.quadraticValueSet
      ((W.toJordan hstrict).component p).space
      ((W.toJordan hstrict).component p).lattice)
    (hrank : (W.toJordan hstrict).componentRank p = 2)
    (hleftOuter : ∀ _hp : 0 < p.val,
      a.order (P.profileComponentLastIndex
        ⟨p.val - 1, by omega⟩) <
      a.order (P.profileComponentSecondIndex p (by omega))) :
    let zLeft : Fin t := ⟨p.val - 1, by omega⟩
    ∃ (A' : Kˣ)
      (hleftRank : 1 < (W.toJordan hstrict).componentRank
        (Lattice.JordanDecomposition.boundaryRightIndex zLeft)),
      Lattice.IsNormGeneratorValue q
          ((W.toJordan hstrict).fundamentalLattice p) A' ∧
        (P.boundaryOneAfterIndex zLeft hleftRank).val + 1 = n + 1 ∧
        a.IsSpaceApproximation
          (P.boundaryOneAfterIndex zLeft hleftRank)
          (P.boundaryOneAfterDiagonalUnits zLeft A) ∧
        DiagonalRepresents
          (diagonalUnitCoefficients
            (P.boundaryOneAfterDiagonalUnits zLeft A))
          (a.prefixValues
            ((P.boundaryOneAfterIndex zLeft hleftRank).val + 2)
            (by omega)) := by
  let J := W.toJordan hstrict
  let zLeft : Fin t := ⟨p.val - 1, by omega⟩
  have hcomponent :
      Lattice.JordanDecomposition.boundaryRightIndex zLeft = p := by
    apply Fin.ext
    simp [zLeft, Lattice.JordanDecomposition.boundaryRightIndex]
    omega
  let hleftRank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex zLeft) := by
    rw [hcomponent, hrank]
    omega
  have heffective : BONG.jordanEffectiveNormOrder J p =
      ordUnit K (J.normGenerator p) := by
    apply P.beli2019Lemma36 W hW hstrict p hrank hleftOuter
    intro hp
    omega
  have hrankLeft : J.componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex zLeft) = 2 := by
    rw [hcomponent, hrank]
  have hALeft : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryRightIndex zLeft)) A := by
    rw [hcomponent]
    exact hA
  have hvalueLeft : (A : K) ∈ Lattice.quadraticValueSet
      (J.component
        (Lattice.JordanDecomposition.boundaryRightIndex zLeft)).space
      (J.component
        (Lattice.JordanDecomposition.boundaryRightIndex zLeft)).lattice := by
    rw [hcomponent]
    exact hvalue
  let D := BONG.JordanBinaryNormGeneratorComplementData.ofQuadraticValue
    J (Lattice.JordanDecomposition.boundaryRightIndex zLeft) A
      hrankLeft (by simpa only [hcomponent] using heffective)
      hALeft hvalueLeft
  have hleftOne := beli2019Lemma34_ii
    a W hW hstrict P zLeft A hALeft hleftRank
  have hprefixFull : zLeft.val + 2 = t + 1 := by
    dsimp only [zLeft]
    omega
  have hterminal :
      (P.boundaryOneAfterIndex zLeft hleftRank).val + 1 = n + 1 := by
    have hb := P.boundaryIndex_succ_val_eq_componentRankPrefix zLeft
    rw [hcomponent] at hb
    have htotal := P.sum_componentRank_eq_length
    change (∑ k, J.componentRank k) = n + 2 at htotal
    have hUniv : (Finset.univ : Finset (Fin (t + 1))) =
        insert p (Finset.Iio p) := by
      ext k
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_Iio,
        true_iff]
      by_cases heq : k = p
      · exact Or.inl heq
      · exact Or.inr (by
          have hk := k.isLt
          have hneVal : k.val ≠ p.val := by
            intro h
            exact heq (Fin.ext h)
          omega)
    rw [hUniv, Finset.sum_insert (by simp)] at htotal
    change (P.boundaryIndex zLeft).val + 1 =
      ∑ k ∈ Finset.Iio p, J.componentRank k at hb
    simp only [BONG.JordanOrderProfileWitness.boundaryOneAfterIndex]
    rw [hrank] at htotal
    omega
  have hright := binaryReplacement_rightRepresentation_of_terminal
    P zLeft A D hrankLeft hprefixFull hterminal
  have hspace : a.IsSpaceApproximation
      (P.boundaryOneAfterIndex zLeft hleftRank)
      (P.boundaryOneAfterDiagonalUnits zLeft A) := by
    exact ⟨hleftOne, ⟨hleftOne.1, fun _ ↦ hright⟩⟩
  have hsecond : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice p) D.second := by
    simpa only [hcomponent] using D.second_isNormGeneratorValue
  exact ⟨D.second, hleftRank, hsecond, hterminal, hspace, hright⟩

set_option maxHeartbeats 0 in
/-- Beli (2019), Lemma 3.7(iv), when the binary component is the entire
Jordan decomposition. -/
theorem beli2019Lemma37_iv_singleton
    [DyadicDiscriminantClassLaws K]
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L 1)
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : BONG.JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice 0) A)
    (hvalue : (A : K) ∈ Lattice.quadraticValueSet
      ((W.toJordan hstrict).component 0).space
      ((W.toJordan hstrict).component 0).lattice)
    (hrank : (W.toJordan hstrict).componentRank 0 = 2) :
    ∃ (A' : Kˣ),
      Lattice.IsNormGeneratorValue q
          ((W.toJordan hstrict).fundamentalLattice 0) A' ∧
        a.IsSpaceApproximation (0 : Fin (n + 1))
          (fun _ : Fin 1 ↦ A) := by
  let J := W.toJordan hstrict
  have heffective : BONG.jordanEffectiveNormOrder J 0 =
      ordUnit K (J.normGenerator 0) := by
    apply P.beli2019Lemma36 W hW hstrict 0 hrank
    · intro hp
      simp at hp
    · intro hp
      simp at hp
  let D := BONG.JordanBinaryNormGeneratorComplementData.ofQuadraticValue
    J 0 A hrank heffective hA hvalue
  have htotal := P.sum_componentRank_eq_length
  change (∑ k : Fin 1, J.componentRank k) = n + 2 at htotal
  have hn : n = 0 := by
    simp only [Fin.sum_univ_one] at htotal
    have hrankJ : J.componentRank 0 = 2 := by
      exact hrank
    omega
  subst n
  have hleft := firstLine_isLeftSpaceApproximation
    a W hW hstrict P A hA (by rw [hrank]; omega)
  have hrightFull := firstBinaryLine_rightRepresentation_of_singleton
    (a := a) A D
  have hright : DiagonalRepresents
      (diagonalUnitCoefficients (fun _ : Fin 1 ↦ A))
      (a.prefixValues ((0 : Fin (0 + 1)).val + 2) (by omega)) := by
    simpa using hrightFull
  refine ⟨D.second, D.second_isNormGeneratorValue, hleft, ?_⟩
  exact ⟨hleft.1, fun _ ↦ hright⟩

end BONG.JordanOrderProfileWitness.PrescribedJordanComparison

end Bong
