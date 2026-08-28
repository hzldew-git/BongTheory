/- Geometric models for Beli 2019, Lemma 3.7(iv). -/
import Bong.Bong.Beli2019Lemma37Models
import Bong.Bong.Beli2019Lemma37Binary
import Bong.Lattice.OrthogonalDecompositionPrefixCarrier

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

set_option maxHeartbeats 0 in
/-- In the exceptional interior binary case, both diagonal presentations in
Lemma 3.7(iv) are realized by explicit ambient subspaces.  The left one is
the prefix plus the represented first line; the right one is the image of
the complementary factor in `BoundaryOneBeforeModel.splitIsometry`. -/
theorem exists_beli2019Lemma37Models_iv_interior
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
    (hleftOuter : ∀ _hp : 0 < p.val,
      a.order (P.profileComponentLastIndex
        ⟨p.val - 1, by omega⟩) <
      a.order (P.profileComponentSecondIndex p (by omega)))
    (hrightOuter : ∀ hp : p.val + 1 < t + 1,
      a.order (P.profileComponentFirstIndex p) <
      a.order (P.profileComponentFirstIndex
        ⟨p.val + 1, by omega⟩)) :
    let zLeft : Fin t := ⟨p.val - 1, by omega⟩
    let zRight : Fin t := ⟨p.val, by omega⟩
    ∃ (hleftRank : 1 < (W.toJordan hstrict).componentRank
          (Lattice.JordanDecomposition.boundaryRightIndex zLeft))
      (hrightRank : 1 < (W.toJordan hstrict).componentRank
          (Lattice.JordanDecomposition.boundaryLeftIndex zRight))
      (_left : BONG.GoodBONG.SpaceApproximationModel a
        (P.boundaryOneAfterIndex zLeft hleftRank))
      (_right : BONG.GoodBONG.SpaceApproximationModel a
        (P.boundaryOneBeforeIndex zRight hrightRank)),
      P.boundaryOneAfterIndex zLeft hleftRank =
        P.boundaryOneBeforeIndex zRight hrightRank ∧
      (W.toJordan hstrict).toOrthogonalDecomposition.prefixCarrier p.val ≤
        _left.carrier ∧
      _left.carrier ≤
        (W.toJordan hstrict).toOrthogonalDecomposition.prefixCarrier
          (p.val + 1) ∧
      _right.carrier ≤
        (W.toJordan hstrict).toOrthogonalDecomposition.prefixCarrier
          (p.val + 1) := by
  let J := W.toJordan hstrict
  let zLeft : Fin t := ⟨p.val - 1, by omega⟩
  let zRight : Fin t := ⟨p.val, by omega⟩
  obtain ⟨A', M, hleftRank, hrightRank, hindex,
      hleftApproximation, hrightApproximation, _hdiag⟩ :=
    beli2019Lemma37_iv_interior a W hW hstrict P p hppos hpnext A hA
      hvalue hrank hleftOuter hrightOuter
  obtain ⟨x, _hxLattice, hxA⟩ :=
    (Lattice.mem_quadraticValueSet_iff
      (J.component p).space (J.component p).lattice (A : K)).1 hvalue
  let xAmbient : V := (x : (J.component p).carrier)
  have hxAmbientA : q.quadratic xAmbient = (A : K) := by
    exact hxA
  have hprefixLength : zLeft.val + 1 = p.val := by
    dsimp only [zLeft]
    omega
  have horth : ∀ y : (J.toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (zLeft.val + 1)).carrier,
      q.bilin (y : V) xAmbient = 0 := by
    intro y
    let y' : (J.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice p.val).carrier :=
      ⟨(y : V), by simpa only [hprefixLength] using y.property⟩
    exact J.toOrthogonalDecomposition.prefix_orthogonal_component p y' x
  let left := spaceApproximationModel_oneAfter_ofOrthogonalVector
    a J P zLeft A hleftRank xAmbient hxAmbientA horth
      hleftApproximation
  let right := spaceApproximationModel_oneBefore
    a J P zRight A' M hrightRank hrightApproximation
  have hleftLower : J.toOrthogonalDecomposition.prefixCarrier p.val ≤
      left.carrier := by
    have h :=
      prefixCarrier_le_spaceApproximationModel_oneAfter_ofOrthogonalVector
        a J P zLeft A hleftRank xAmbient hxAmbientA horth
          hleftApproximation
    simpa only [left, hprefixLength] using h
  have hleftCarrier : left.carrier ≤
      J.toOrthogonalDecomposition.prefixCarrier (p.val + 1) := by
    apply spaceApproximationModel_oneAfter_ofOrthogonalVector_carrier_le
      a J P zLeft A hleftRank xAmbient hxAmbientA horth
        hleftApproximation
    · rw [J.toOrthogonalDecomposition.prefixQuadraticSublattice_carrier]
      apply J.toOrthogonalDecomposition.prefixCarrier_mono
      dsimp only [zLeft]
      omega
    · apply J.toOrthogonalDecomposition.component_carrier_le_prefixCarrier
        p (by omega)
      exact x.property
  have hrightCarrier : right.carrier ≤
      J.toOrthogonalDecomposition.prefixCarrier (p.val + 1) := by
    have h := spaceApproximationModel_oneBefore_carrier_le
      a J P zRight A' M hrightRank hrightApproximation
    rw [J.toOrthogonalDecomposition.prefixQuadraticSublattice_carrier] at h
    simpa only [zRight] using h
  exact ⟨hleftRank, hrightRank, left, right, hindex, hleftLower,
    hleftCarrier, hrightCarrier⟩

end BONG.JordanOrderProfileWitness.PrescribedJordanComparison

end Bong
