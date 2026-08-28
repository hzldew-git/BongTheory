/- Beli 2019, Lemma 3.7(iv): exceptional binary Jordan component. -/
import Bong.Bong.Beli2019Lemma36
import Bong.Bong.Beli2019Lemma37Jordan

namespace Bong

open Dyadic Module
open BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

theorem spaceApproximations_of_left_right_of_diagonalRepresents
    {n : Nat} (a : GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (c d : Fin (i.val + 1) → Kˣ)
    (hleft : a.IsLeftSpaceApproximation i c)
    (hright : a.IsRightSpaceApproximation i d)
    (hcd : DiagonalRepresents
      (diagonalUnitCoefficients c) (diagonalUnitCoefficients d)) :
    a.IsSpaceApproximation i c ∧ a.IsSpaceApproximation i d := by
  constructor
  · refine ⟨hleft, ⟨hleft.1, ?_⟩⟩
    intro htrigger
    exact hcd.trans (hright.2 htrigger)
  · refine ⟨⟨hright.1, ?_⟩, hright⟩
    intro htrigger
    exact (hleft.2 htrigger).trans hcd

theorem spaceApproximations_of_left_right_of_eq
    {n : Nat} (a : GoodBONG q L (n + 2))
    (i j : Fin (n + 1)) (hij : i = j)
    (c : Fin (i.val + 1) → Kˣ) (d : Fin (j.val + 1) → Kˣ)
    (hleft : a.IsLeftSpaceApproximation i c)
    (hright : a.IsRightSpaceApproximation j d)
    (hcd : DiagonalRepresents
      (diagonalUnitCoefficients c) (diagonalUnitCoefficients d)) :
    a.IsSpaceApproximation i c ∧ a.IsSpaceApproximation j d := by
  subst j
  exact a.spaceApproximations_of_left_right_of_diagonalRepresents
    i c d hleft hright hcd

end BONG.GoodBONG

namespace BONG.JordanBinaryNormGeneratorComplementData

theorem secondLineRepresentation
    {t : Nat} {J : Lattice.JordanDecomposition q L (t + 1)}
    {p : Fin (t + 1)}
    {A : Kˣ} (D : JordanBinaryNormGeneratorComplementData J p A) :
    (J.prefixSpace (p.val + 1)).Represents
      (QuadraticSpace.scaledLine D.second) := by
  let prefixQ := J.prefixSpace p.val
  let lineA := QuadraticSpace.scaledLine A
  let lineB := QuadraticSpace.scaledLine D.second
  let pair := QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients ![A, D.second])
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero ![A, D.second])
  have hsnoc : Fin.snoc (fun _ : Fin 1 ↦ A) D.second = ![A, D.second] := by
    funext i
    fin_cases i <;> rfl
  let pairIso : QuadraticSpace.Isometry (lineA.orthogonalSum lineB) pair := by
    let raw :=
      ((QuadraticSpace.scaledLineDiagonalizationIsometry A).orthogonalSum
        (QuadraticSpace.Isometry.refl lineB)).trans
      (QuadraticSpace.finiteDiagonalOrthogonalSumScaledLineIsometry
        (fun _ : Fin 1 ↦ A) D.second)
    rw [hsnoc] at raw
    exact raw
  let lineToPair : QuadraticSpace.Representation lineB pair :=
    pairIso.toRepresentation.trans
      ((QuadraticSpace.orthogonalSumSwap lineB lineA).toRepresentation.trans
        (QuadraticSpace.Representation.orthogonalSumInl lineB lineA))
  let lineToComponent : QuadraticSpace.Representation lineB
      (J.component p).space :=
    D.componentDiagonalIsometry.toRepresentation.trans lineToPair
  let lineToPrefixComponent : QuadraticSpace.Representation lineB
      (prefixQ.orthogonalSum (J.component p).space) :=
    (QuadraticSpace.orthogonalSumSwap
      (J.component p).space prefixQ).toRepresentation.trans
        ((QuadraticSpace.Representation.orthogonalSumInl
          (J.component p).space prefixQ).trans lineToComponent)
  exact ⟨(J.toOrthogonalDecomposition.prefixComponentLatticeIsometry p
      |>.toQuadraticSpaceIsometry.toRepresentation).trans
    lineToPrefixComponent⟩

end BONG.JordanBinaryNormGeneratorComplementData

namespace BONG.JordanOrderProfileWitness

noncomputable def binaryReplacementPrefixIsometry
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t) (A : Kˣ)
    (D : JordanBinaryNormGeneratorComplementData J
      (Lattice.JordanDecomposition.boundaryRightIndex z) A) :
    QuadraticSpace.Isometry
      ((QuadraticSpace.finiteDiagonal
          (diagonalUnitCoefficients
            (P.boundaryOneAfterDiagonalUnits z A))
          (QuadraticSpace.diagonalUnitCoefficients_ne_zero
            (P.boundaryOneAfterDiagonalUnits z A))).orthogonalSum
        (QuadraticSpace.scaledLine D.second))
      (J.prefixSpace (z.val + 2)) := by
  let c := P.boundaryPrefixDiagonalUnits z
  let left := P.boundaryOneAfterDiagonalUnits z A
  let pair := QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients ![A, D.second])
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero ![A, D.second])
  let first :=
    QuadraticSpace.finiteDiagonalOrthogonalSumScaledLineIsometry
      left D.second
  have hcoeff : Fin.snoc left D.second = Fin.append c ![A, D.second] := by
    unfold left c boundaryOneAfterDiagonalUnits
    rw [QuadraticSpace.append_finTwo_eq_snoc_snoc]
  rw [hcoeff] at first
  let splitDiagonal :=
    (QuadraticSpace.finiteDiagonalOrthogonalSumIsometry c
      ![A, D.second]).symm
  let prefixIso := (P.boundaryPrefixDiagonalizationIsometry z).symm
  let assembled :=
    (prefixIso.orthogonalSum D.componentDiagonalIsometry).trans
      (J.toOrthogonalDecomposition.prefixComponentLatticeIsometry
        (Lattice.JordanDecomposition.boundaryRightIndex z)
        |>.toQuadraticSpaceIsometry)
  exact first.trans (splitDiagonal.trans assembled)

set_option maxHeartbeats 0 in
theorem binaryReplacement_diagonalRepresents
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (zNext : Fin t) (hzNext : zNext.val = z.val + 1) (A : Kˣ)
    (D : JordanBinaryNormGeneratorComplementData J
      (Lattice.JordanDecomposition.boundaryRightIndex z) A)
    (M : BoundaryOneBeforeModel P zNext D.second)
    (hrank : J.componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex z) = 2) :
    let hrightRank : 1 < J.componentRank
        (Lattice.JordanDecomposition.boundaryLeftIndex zNext) := by
      have hcomponent :
          Lattice.JordanDecomposition.boundaryLeftIndex zNext =
            Lattice.JordanDecomposition.boundaryRightIndex z := by
        apply Fin.ext
        change zNext.val = z.val + 1
        exact hzNext
      rw [hcomponent, hrank]
      omega
    DiagonalRepresents
      (diagonalUnitCoefficients (P.boundaryOneAfterDiagonalUnits z A))
      (diagonalUnitCoefficients (M.approximationUnits hrightRank)) := by
  have hcomponent :
      Lattice.JordanDecomposition.boundaryLeftIndex zNext =
        Lattice.JordanDecomposition.boundaryRightIndex z := by
    apply Fin.ext
    change zNext.val = z.val + 1
    exact hzNext
  let hrightRank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex zNext) := by
    rw [hcomponent, hrank]
    omega
  let leftModel := QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients (P.boundaryOneAfterDiagonalUnits z A))
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero
      (P.boundaryOneAfterDiagonalUnits z A))
  let rightModel := QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients M.units)
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero M.units)
  let line := QuadraticSpace.scaledLine D.second
  let leftTotal := P.binaryReplacementPrefixIsometry z A D
  let totalIso : QuadraticSpace.Isometry
      (leftModel.orthogonalSum line) (rightModel.orthogonalSum line) := by
    have hprefix : zNext.val + 1 = z.val + 2 := by omega
    let rightTotal := M.splitIsometry.symm
    rw [hprefix] at rightTotal
    exact leftTotal.trans rightTotal
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
    (P.boundaryOneAfterDiagonalUnits z A)
    (M.approximationUnits hrightRank)).1
  change (QuadraticSpace.finiteDiagonal
      (fun i ↦ (M.units (e i) : K))
      (fun i ↦ Units.ne_zero (M.units (e i)))).Represents leftModel
  exact hrepReindexed

theorem adjacentBoundaryIndex_add_componentRank
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J)
    (p : Fin (t + 1)) (hppos : 0 < p.val)
    (hpnext : p.val + 1 < t + 1) :
    let zLeft : Fin t := ⟨p.val - 1, by omega⟩
    let zRight : Fin t := ⟨p.val, by omega⟩
    (P.boundaryIndex zRight).val + 1 =
      (P.boundaryIndex zLeft).val + 1 + J.componentRank p := by
  let zLeft : Fin t := ⟨p.val - 1, by omega⟩
  let zRight : Fin t := ⟨p.val, by omega⟩
  have hleft := P.boundaryIndex_succ_val_eq_componentRankPrefix zLeft
  have hright := P.boundaryIndex_succ_val_eq_componentRankPrefix zRight
  have hleftComponent :
      Lattice.JordanDecomposition.boundaryRightIndex zLeft = p := by
    apply Fin.ext
    simp [zLeft, Lattice.JordanDecomposition.boundaryRightIndex]
    omega
  have hrightComponent :
      Lattice.JordanDecomposition.boundaryRightIndex zRight =
        ⟨p.val + 1, hpnext⟩ := by
    apply Fin.ext
    rfl
  have hIio : Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex zRight) =
      insert p (Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex zLeft)) := by
    ext k
    simp only [Finset.mem_Iio, Finset.mem_insert]
    rw [hleftComponent, hrightComponent]
    change (k.val < p.val + 1 ↔ k = p ∨ k.val < p.val)
    constructor
    · intro hk
      by_cases heq : k.val = p.val
      · exact Or.inl (Fin.ext heq)
      · exact Or.inr (by omega)
    · rintro (rfl | hk)
      · omega
      · omega
  have hpnot : p ∉ Finset.Iio
      (Lattice.JordanDecomposition.boundaryRightIndex zLeft) := by
    simp only [Finset.mem_Iio, not_lt]
    rw [hleftComponent]
  rw [hIio, Finset.sum_insert hpnot] at hright
  calc
    (P.boundaryIndex zRight).val + 1 =
        J.componentRank p +
          ∑ k ∈ Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex zLeft),
              J.componentRank k := hright
    _ = J.componentRank p + ((P.boundaryIndex zLeft).val + 1) := by
      exact congrArg (fun x ↦ J.componentRank p + x) hleft.symm
    _ = (P.boundaryIndex zLeft).val + 1 + J.componentRank p := by
      omega

theorem boundaryOneAfter_eq_boundaryOneBefore_of_rank_two
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J)
    (p : Fin (t + 1)) (hppos : 0 < p.val)
    (hpnext : p.val + 1 < t + 1)
    (hrank : J.componentRank p = 2) :
    let zLeft : Fin t := ⟨p.val - 1, by omega⟩
    let zRight : Fin t := ⟨p.val, by omega⟩
    let hleftRank : 1 < J.componentRank
        (Lattice.JordanDecomposition.boundaryRightIndex zLeft) := by
      have hcomponent :
          Lattice.JordanDecomposition.boundaryRightIndex zLeft = p := by
        apply Fin.ext
        simp [zLeft, Lattice.JordanDecomposition.boundaryRightIndex]
        omega
      rw [hcomponent, hrank]
      omega
    let hrightRank : 1 < J.componentRank
        (Lattice.JordanDecomposition.boundaryLeftIndex zRight) := by
      have hcomponent :
          Lattice.JordanDecomposition.boundaryLeftIndex zRight = p := by
        apply Fin.ext
        rfl
      rw [hcomponent, hrank]
      omega
    P.boundaryOneAfterIndex zLeft hleftRank =
      P.boundaryOneBeforeIndex zRight hrightRank := by
  let zLeft : Fin t := ⟨p.val - 1, by omega⟩
  let zRight : Fin t := ⟨p.val, by omega⟩
  have hleftComponent :
      Lattice.JordanDecomposition.boundaryRightIndex zLeft = p := by
    apply Fin.ext
    simp [zLeft, Lattice.JordanDecomposition.boundaryRightIndex]
    omega
  have hrightComponent :
      Lattice.JordanDecomposition.boundaryLeftIndex zRight = p := by
    apply Fin.ext
    rfl
  let hleftRank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex zLeft) := by
    rw [hleftComponent, hrank]
    omega
  let hrightRank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex zRight) := by
    rw [hrightComponent, hrank]
    omega
  have hboundary := P.adjacentBoundaryIndex_add_componentRank
    p hppos hpnext
  dsimp only at hboundary
  rw [hrank] at hboundary
  have hbefore := P.boundaryOneBeforeIndex_succ_val zRight hrightRank
  apply Fin.ext
  change (P.boundaryIndex zLeft).val + 1 =
    (P.boundaryOneBeforeIndex zRight hrightRank).val
  change (P.boundaryIndex zRight).val + 1 =
      (P.boundaryIndex zLeft).val + 1 + 2 at hboundary
  omega

namespace PrescribedJordanComparison

set_option maxHeartbeats 0 in
/-- Beli (2019), Lemma 3.7(iv), for a binary Jordan component with both
neighbouring components present.  The second norm generator and the
orthogonal-complement model are constructed rather than assumed. -/
theorem beli2019Lemma37_iv_interior
    [DyadicDiscriminantClassLaws K]
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin (t + 1)) (hppos : 0 < p.val)
    (hpnext : p.val + 1 < t + 1)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice p) A)
    (hvalue : (A : K) ∈ Lattice.quadraticValueSet
      ((W.toJordan hstrict).component p).space
      ((W.toJordan hstrict).component p).lattice)
    (hrank : (W.toJordan hstrict).componentRank p = 2)
    (hleftOuter : ∀ hp : 0 < p.val,
      a.order (P.profileComponentLastIndex
        ⟨p.val - 1, by omega⟩) <
      a.order (P.profileComponentSecondIndex p (by omega)))
    (hrightOuter : ∀ hp : p.val + 1 < t + 1,
      a.order (P.profileComponentFirstIndex p) <
      a.order (P.profileComponentFirstIndex
        ⟨p.val + 1, by omega⟩)) :
    let zLeft : Fin t := ⟨p.val - 1, by omega⟩
    let zRight : Fin t := ⟨p.val, by omega⟩
    ∃ (A' : Kˣ) (M : BoundaryOneBeforeModel P zRight A')
      (hleftRank : 1 < (W.toJordan hstrict).componentRank
        (Lattice.JordanDecomposition.boundaryRightIndex zLeft))
      (hrightRank : 1 < (W.toJordan hstrict).componentRank
        (Lattice.JordanDecomposition.boundaryLeftIndex zRight)),
      P.boundaryOneAfterIndex zLeft hleftRank =
          P.boundaryOneBeforeIndex zRight hrightRank ∧
        a.IsSpaceApproximation
          (P.boundaryOneAfterIndex zLeft hleftRank)
          (P.boundaryOneAfterDiagonalUnits zLeft A) ∧
        a.IsSpaceApproximation
          (P.boundaryOneBeforeIndex zRight hrightRank)
          (M.approximationUnits hrightRank) ∧
        DiagonalRepresents
          (diagonalUnitCoefficients
            (P.boundaryOneAfterDiagonalUnits zLeft A))
          (diagonalUnitCoefficients
            (M.approximationUnits hrightRank)) := by
  let J := W.toJordan hstrict
  let zLeft : Fin t := ⟨p.val - 1, by omega⟩
  let zRight : Fin t := ⟨p.val, by omega⟩
  have hleftComponent :
      Lattice.JordanDecomposition.boundaryRightIndex zLeft = p := by
    apply Fin.ext
    simp [zLeft, Lattice.JordanDecomposition.boundaryRightIndex]
    omega
  have hrightComponent :
      Lattice.JordanDecomposition.boundaryLeftIndex zRight = p := by
    apply Fin.ext
    rfl
  let hleftRank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex zLeft) := by
    rw [hleftComponent, hrank]
    omega
  let hrightRank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex zRight) := by
    rw [hrightComponent, hrank]
    omega
  have heffective : BONG.jordanEffectiveNormOrder J p =
      ordUnit K (J.normGenerator p) :=
    P.beli2019Lemma36 W hW hstrict p hrank hleftOuter hrightOuter
  let pLeft := Lattice.JordanDecomposition.boundaryRightIndex zLeft
  have hpLeft : pLeft = p := hleftComponent
  have hrankLeft : J.componentRank pLeft = 2 := by
    rw [hpLeft, hrank]
  have heffectiveLeft : BONG.jordanEffectiveNormOrder J pLeft =
      ordUnit K (J.normGenerator pLeft) := by
    simpa only [hpLeft] using heffective
  have hALeft : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice pLeft) A := by
    simpa only [hpLeft] using hA
  have hvalueLeft : (A : K) ∈ Lattice.quadraticValueSet
      (J.component pLeft).space (J.component pLeft).lattice := by
    rw [hpLeft]
    simpa only [J] using hvalue
  let D := JordanBinaryNormGeneratorComplementData.ofQuadraticValue
    J pLeft A hrankLeft heffectiveLeft hALeft hvalueLeft
  have hline : (J.prefixSpace (zRight.val + 1)).Represents
      (QuadraticSpace.scaledLine D.second) := by
    have hraw := D.secondLineRepresentation
    have hpval : pLeft.val = zRight.val := by
      rw [hpLeft]
    rw [hpval] at hraw
    exact hraw
  let M := BoundaryOneBeforeModel.ofLineRepresentation
    (P := P) (z := zRight) (A := D.second) hline
  have hASecond : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex zRight)) D.second := by
    rw [hrightComponent]
    simpa only [hpLeft] using D.second_isNormGeneratorValue
  have hleftOne := beli2019Lemma34_ii
    a W hW hstrict P zLeft A hALeft hleftRank
  have hrightOne := beli2019Lemma34_iii
    a W hW hstrict P zRight D.second hASecond M hrightRank
  have hindex : P.boundaryOneAfterIndex zLeft hleftRank =
      P.boundaryOneBeforeIndex zRight hrightRank := by
    simpa only [zLeft, zRight] using
      P.boundaryOneAfter_eq_boundaryOneBefore_of_rank_two
        p hppos hpnext hrank
  have hzNext : zRight.val = zLeft.val + 1 := by
    dsimp only [zLeft, zRight]
    omega
  have hdiag := P.binaryReplacement_diagonalRepresents
    zLeft zRight hzNext A D M hrankLeft
  have hboth := a.spaceApproximations_of_left_right_of_eq
    (P.boundaryOneAfterIndex zLeft hleftRank)
    (P.boundaryOneBeforeIndex zRight hrightRank) hindex
    (P.boundaryOneAfterDiagonalUnits zLeft A)
    (M.approximationUnits hrightRank) hleftOne hrightOne hdiag
  refine ⟨D.second, M, hleftRank, hrightRank, hindex, ?_, ?_, hdiag⟩
  · exact hboth.1
  · exact hboth.2

end PrescribedJordanComparison

end BONG.JordanOrderProfileWitness

end Bong
