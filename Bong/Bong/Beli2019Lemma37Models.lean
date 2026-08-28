/- Geometric space models for the Jordan cases in Beli 2019, Lemma 3.7. -/
import Bong.Bong.Beli2019ApproximationGeometry
import Bong.Bong.Beli2019Lemma37Jordan
import Bong.Lattice.NestedSublattice
import Bong.Lattice.QuadraticSublatticeOrthogonalSup
import Bong.QuadraticSpace.RepresentationRange

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
/-- A represented anisotropic vector realizes a one-dimensional space
approximation at the first BONG coordinate.  This is the concrete endpoint
model needed when a binary Jordan block starts the decomposition. -/
noncomputable def spaceApproximationModel_firstLine
    {n : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (A : Kˣ) (x : V) (hxA : q.quadratic x = (A : K))
    (happroximation : a.IsSpaceApproximation (0 : Fin (n + 1))
      (fun _ : Fin 1 ↦ A)) :
    BONG.GoodBONG.SpaceApproximationModel a (0 : Fin (n + 1)) := by
  have hx : q.IsAnisotropic x := by
    unfold QuadraticSpace.IsAnisotropic
    rw [hxA]
    exact Units.ne_zero A
  refine
    { carrier := K ∙ x
      nondegenerate := Lattice.unarySpan_restrict_nondegenerate hx
      units := fun _ : Fin 1 ↦ A
      approximation := happroximation
      presentation := ?_ }
  exact (QuadraticSpace.scaledLineDiagonalizationIsometry A).symm.trans
    (QuadraticSpace.scaledLineUnarySpanIsometry x A hx hxA)

/-- The first-line model lies in every carrier containing its defining
vector. -/
theorem spaceApproximationModel_firstLine_carrier_le
    {n : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (A : Kˣ) (x : V) (hxA : q.quadratic x = (A : K))
    (happroximation : a.IsSpaceApproximation (0 : Fin (n + 1))
      (fun _ : Fin 1 ↦ A))
    (T : Submodule K V) (hxT : x ∈ T) :
    (spaceApproximationModel_firstLine
      a A x hxA happroximation).carrier ≤ T := by
  change K ∙ x ≤ T
  apply Submodule.span_le.mpr
  intro y hy
  rw [Set.mem_singleton_iff.mp hy]
  exact hxT

/-- The abstract diagonal approximation model in Lemma 3.7(i). -/
noncomputable def beli2019Lemma37DiagonalModel_i
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : BONG.JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (z : Fin t) :
    BONG.GoodBONG.DiagonalApproximationModel a (P.boundaryIndex z) where
  units := P.boundaryPrefixDiagonalUnits z
  approximation := beli2019Lemma37_i a W hW hstrict P z

/-- The abstract model in Lemma 3.7(ii).  In contrast with the ambient
carrier realization below, this construction needs only a fundamental norm
generator, exactly as in the paper. -/
noncomputable def beli2019Lemma37DiagonalModel_ii
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : BONG.JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (z : Fin t) (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice
        (Lattice.JordanDecomposition.boundaryRightIndex z)) A)
    (hrank : 1 < (W.toJordan hstrict).componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex z))
    (hinternal : (P.boundaryOneAfterIndex z hrank).val + 1 < n + 1)
    (houter : a.order (P.boundaryOneAfterIndex z hrank).castSucc =
      a.order (⟨(P.boundaryOneAfterIndex z hrank).val + 1,
        hinternal⟩ : Fin (n + 1)).succ) :
    BONG.GoodBONG.DiagonalApproximationModel a
      (P.boundaryOneAfterIndex z hrank) where
  units := P.boundaryOneAfterDiagonalUnits z A
  approximation := beli2019Lemma37_ii
    a W hW hstrict P z A hA hrank hinternal houter

/-- The abstract complement model in Lemma 3.7(iii).  Its geometric datum is
precisely the splitting `F L_(k) ≅ W ⊥ [A_k]`. -/
noncomputable def beli2019Lemma37DiagonalModel_iii
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : BONG.JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (z : Fin t) (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex z)) A)
    (M : BONG.JordanOrderProfileWitness.BoundaryOneBeforeModel P z A)
    (hrank : 1 < (W.toJordan hstrict).componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z))
    (hpositive : 0 < (P.boundaryOneBeforeIndex z hrank).val)
    (houter : a.order
        ⟨(P.boundaryOneBeforeIndex z hrank).val - 1, by omega⟩ =
      a.order
        ⟨(P.boundaryOneBeforeIndex z hrank).val + 1, by omega⟩) :
    BONG.GoodBONG.DiagonalApproximationModel a
      (P.boundaryOneBeforeIndex z hrank) where
  units := M.approximationUnits hrank
  approximation := beli2019Lemma37_iii
    a W hW hstrict P z A hA M hrank hpositive houter

/-- The unmodified Jordan prefix in Lemma 3.7(i), equipped with its actual
ambient carrier. -/
noncomputable def beli2019Lemma37Model_i
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : BONG.JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (z : Fin t) :
    BONG.GoodBONG.SpaceApproximationModel a (P.boundaryIndex z) where
  carrier := ((W.toJordan hstrict).toOrthogonalDecomposition
    |>.prefixQuadraticSublattice (z.val + 1)).carrier
  nondegenerate := ((W.toJordan hstrict).toOrthogonalDecomposition
    |>.prefixQuadraticSublattice (z.val + 1)).nondegenerate
  units := P.boundaryPrefixDiagonalUnits z
  approximation := beli2019Lemma37_i a W hW hstrict P z
  presentation := (P.boundaryPrefixDiagonalizationIsometry z).symm

set_option maxHeartbeats 0 in
/-- The geometric construction underlying Lemma 3.7(ii) and the left-hand
model in its exceptional binary case.  The approximation proof is supplied
separately from the ambient orthogonal-line realization. -/
noncomputable def spaceApproximationModel_oneAfter_ofOrthogonalVector
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (J : Lattice.JordanDecomposition q L (t + 1))
    (P : BONG.JordanOrderProfileWitness a.toBONG J)
    (z : Fin t) (A : Kˣ)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex z))
    (x : V) (hxA : q.quadratic x = (A : K))
    (horth : ∀ y : (J.toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (z.val + 1)).carrier,
      q.bilin (y : V) x = 0)
    (happroximation : a.IsSpaceApproximation
      (P.boundaryOneAfterIndex z hrank)
      (P.boundaryOneAfterDiagonalUnits z A)) :
    BONG.GoodBONG.SpaceApproximationModel a
      (P.boundaryOneAfterIndex z hrank) := by
  let C := J.toOrthogonalDecomposition.prefixQuadraticSublattice
    (z.val + 1)
  have hx : q.IsAnisotropic x := by
    unfold QuadraticSpace.IsAnisotropic
    rw [hxA]
    exact Units.ne_zero A
  let lineComponent := Lattice.unaryScaleComponent (q := q) x hx
  have hCD : C.AreOrthogonal lineComponent := by
    intro y w
    rcases Submodule.mem_span_singleton.mp w.property with ⟨c, hc⟩
    change q.bilin (y : V) (w : V) = 0
    rw [← hc, LinearMap.BilinForm.smul_right, horth y, mul_zero]
  let S := C.pairSup lineComponent hCD
  let prefixPresentation := (P.boundaryPrefixDiagonalizationIsometry z).symm
  let linePresentation :=
    QuadraticSpace.scaledLineUnarySpanIsometry x A hx hxA
  let splitPresentation := prefixPresentation.orthogonalSum linePresentation
  let combinedPresentation := splitPresentation.trans
    (Lattice.QuadraticSublattice.pairSupSpaceIsometry hCD)
  let diagonalSplit :=
    (QuadraticSpace.finiteDiagonalOrthogonalSumScaledLineIsometry
      (P.boundaryPrefixDiagonalUnits z) A).symm
  refine
    { carrier := S.carrier
      nondegenerate := S.nondegenerate
      units := P.boundaryOneAfterDiagonalUnits z A
      approximation := happroximation
      presentation := ?_ }
  exact diagonalSplit.trans combinedPresentation

set_option maxHeartbeats 0 in
/-- The preceding Jordan prefix is contained in the concrete one-after model.
This is the lower carrier bound complementary to
`spaceApproximationModel_oneAfter_ofOrthogonalVector_carrier_le`. -/
theorem prefixCarrier_le_spaceApproximationModel_oneAfter_ofOrthogonalVector
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (J : Lattice.JordanDecomposition q L (t + 1))
    (P : BONG.JordanOrderProfileWitness a.toBONG J)
    (z : Fin t) (A : Kˣ)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex z))
    (x : V) (hxA : q.quadratic x = (A : K))
    (horth : ∀ y : (J.toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (z.val + 1)).carrier,
      q.bilin (y : V) x = 0)
    (happroximation : a.IsSpaceApproximation
      (P.boundaryOneAfterIndex z hrank)
      (P.boundaryOneAfterDiagonalUnits z A)) :
    J.toOrthogonalDecomposition.prefixCarrier (z.val + 1) ≤
      (spaceApproximationModel_oneAfter_ofOrthogonalVector
        a J P z A hrank x hxA horth happroximation).carrier := by
  let C := J.toOrthogonalDecomposition.prefixQuadraticSublattice
    (z.val + 1)
  have hx : q.IsAnisotropic x := by
    unfold QuadraticSpace.IsAnisotropic
    rw [hxA]
    exact Units.ne_zero A
  let lineComponent := Lattice.unaryScaleComponent (q := q) x hx
  change C.carrier ≤ C.pairSupCarrier lineComponent
  exact Lattice.QuadraticSublattice.leftCarrier_le_pairSupCarrier
    C lineComponent

set_option maxHeartbeats 0 in
/-- The one-after model is carried by any ambient subspace containing both
the preceding Jordan prefix and the adjoined vector. -/
theorem spaceApproximationModel_oneAfter_ofOrthogonalVector_carrier_le
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (J : Lattice.JordanDecomposition q L (t + 1))
    (P : BONG.JordanOrderProfileWitness a.toBONG J)
    (z : Fin t) (A : Kˣ)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex z))
    (x : V) (hxA : q.quadratic x = (A : K))
    (horth : ∀ y : (J.toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (z.val + 1)).carrier,
      q.bilin (y : V) x = 0)
    (happroximation : a.IsSpaceApproximation
      (P.boundaryOneAfterIndex z hrank)
      (P.boundaryOneAfterDiagonalUnits z A))
    (T : Submodule K V)
    (hprefix : (J.toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (z.val + 1)).carrier ≤ T)
    (hxT : x ∈ T) :
    (spaceApproximationModel_oneAfter_ofOrthogonalVector
      a J P z A hrank x hxA horth happroximation).carrier ≤ T := by
  let C := J.toOrthogonalDecomposition.prefixQuadraticSublattice
    (z.val + 1)
  have hx : q.IsAnisotropic x := by
    unfold QuadraticSpace.IsAnisotropic
    rw [hxA]
    exact Units.ne_zero A
  let lineComponent := Lattice.unaryScaleComponent (q := q) x hx
  have hline : lineComponent.carrier ≤ T := by
    apply Submodule.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact hxT
  change C.pairSupCarrier lineComponent ≤ T
  exact Lattice.QuadraticSublattice.pairSupCarrier_le
    C lineComponent T hprefix hline

set_option maxHeartbeats 0 in
/-- Lemma 3.7(ii) realized as the concrete orthogonal sum of a Jordan prefix
and an ambient represented line. -/
noncomputable def beli2019Lemma37Model_ii_ofOrthogonalVector
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : BONG.JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (z : Fin t) (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice
        (Lattice.JordanDecomposition.boundaryRightIndex z)) A)
    (hrank : 1 < (W.toJordan hstrict).componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex z))
    (hinternal : (P.boundaryOneAfterIndex z hrank).val + 1 < n + 1)
    (houter : a.order (P.boundaryOneAfterIndex z hrank).castSucc =
      a.order (⟨(P.boundaryOneAfterIndex z hrank).val + 1,
        hinternal⟩ : Fin (n + 1)).succ)
    (x : V) (hxA : q.quadratic x = (A : K))
    (horth : ∀ y : ((W.toJordan hstrict).toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (z.val + 1)).carrier,
      q.bilin (y : V) x = 0) :
    BONG.GoodBONG.SpaceApproximationModel a
      (P.boundaryOneAfterIndex z hrank) := by
  let J := W.toJordan hstrict
  let C := J.toOrthogonalDecomposition.prefixQuadraticSublattice
    (z.val + 1)
  have hx : q.IsAnisotropic x := by
    unfold QuadraticSpace.IsAnisotropic
    rw [hxA]
    exact Units.ne_zero A
  let D := Lattice.unaryScaleComponent (q := q) x hx
  have hCD : C.AreOrthogonal D := by
    intro y w
    rcases Submodule.mem_span_singleton.mp w.property with ⟨c, hc⟩
    change q.bilin (y : V) (w : V) = 0
    rw [← hc, LinearMap.BilinForm.smul_right, horth y, mul_zero]
  let S := C.pairSup D hCD
  let prefixPresentation := (P.boundaryPrefixDiagonalizationIsometry z).symm
  let linePresentation :=
    QuadraticSpace.scaledLineUnarySpanIsometry x A hx hxA
  let splitPresentation := prefixPresentation.orthogonalSum linePresentation
  let combinedPresentation := splitPresentation.trans
    (Lattice.QuadraticSublattice.pairSupSpaceIsometry hCD)
  let diagonalSplit :=
    (QuadraticSpace.finiteDiagonalOrthogonalSumScaledLineIsometry
      (P.boundaryPrefixDiagonalUnits z) A).symm
  refine
    { carrier := S.carrier
      nondegenerate := S.nondegenerate
      units := P.boundaryOneAfterDiagonalUnits z A
      approximation := beli2019Lemma37_ii a W hW hstrict P z A hA hrank
        hinternal houter
      presentation := ?_ }
  exact diagonalSplit.trans combinedPresentation

set_option maxHeartbeats 0 in
/-- The geometric construction underlying Lemma 3.7(iii) and the right-hand
model in its exceptional binary case. -/
noncomputable def spaceApproximationModel_oneBefore
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (J : Lattice.JordanDecomposition q L (t + 1))
    (P : BONG.JordanOrderProfileWitness a.toBONG J)
    (z : Fin t) (A : Kˣ)
    (M : BONG.JordanOrderProfileWitness.BoundaryOneBeforeModel P z A)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z))
    (happroximation : a.IsSpaceApproximation
      (P.boundaryOneBeforeIndex z hrank) (M.approximationUnits hrank)) :
    BONG.GoodBONG.SpaceApproximationModel a
      (P.boundaryOneBeforeIndex z hrank) := by
  letI : Module.Finite K V := L.moduleFinite
  let C := J.toOrthogonalDecomposition.prefixQuadraticSublattice
    (z.val + 1)
  let model := QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients M.units)
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero M.units)
  let line := QuadraticSpace.scaledLine A
  let embedded : QuadraticSpace.Representation model C.space :=
    M.splitIsometry.toRepresentation.trans
      (QuadraticSpace.Representation.orthogonalSumInl model line)
  let image : Lattice.QuadraticSublattice C.space :=
    { carrier := LinearMap.range embedded.toLinearMap
      nondegenerate := embedded.range_nondegenerate
      lattice := Lattice.basisLattice
        (Module.finBasis K (LinearMap.range embedded.toLinearMap)) }
  let lifted := C.liftNested image
  let e := M.rankEquiv hrank
  let reindex := QuadraticSpace.finiteDiagonalReindexIsometry
    (diagonalUnitCoefficients M.units)
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero M.units) e
  refine
    { carrier := lifted.carrier
      nondegenerate := lifted.nondegenerate
      units := M.approximationUnits hrank
      approximation := happroximation
      presentation := ?_ }
  exact reindex.symm |>.trans embedded.rangeIsometry |>.trans
    (C.liftNestedIsometry image).toQuadraticSpaceIsometry

set_option maxHeartbeats 0 in
/-- The one-before complement model is contained in the Jordan prefix from
which its represented line was removed. -/
theorem spaceApproximationModel_oneBefore_carrier_le
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (J : Lattice.JordanDecomposition q L (t + 1))
    (P : BONG.JordanOrderProfileWitness a.toBONG J)
    (z : Fin t) (A : Kˣ)
    (M : BONG.JordanOrderProfileWitness.BoundaryOneBeforeModel P z A)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z))
    (happroximation : a.IsSpaceApproximation
      (P.boundaryOneBeforeIndex z hrank) (M.approximationUnits hrank)) :
    (spaceApproximationModel_oneBefore
      a J P z A M hrank happroximation).carrier ≤
      (J.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (z.val + 1)).carrier := by
  let C := J.toOrthogonalDecomposition.prefixQuadraticSublattice
    (z.val + 1)
  let model := QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients M.units)
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero M.units)
  let line := QuadraticSpace.scaledLine A
  let embedded : QuadraticSpace.Representation model C.space :=
    M.splitIsometry.toRepresentation.trans
      (QuadraticSpace.Representation.orthogonalSumInl model line)
  let image : Lattice.QuadraticSublattice C.space :=
    { carrier := LinearMap.range embedded.toLinearMap
      nondegenerate := embedded.range_nondegenerate
      lattice := Lattice.basisLattice
        (Module.finBasis K (LinearMap.range embedded.toLinearMap)) }
  change C.nestedCarrier image ≤ C.carrier
  exact C.nestedCarrier_le image

set_option maxHeartbeats 0 in
/-- The same one-before construction specialized to the canonical
orthogonal complement of a represented vector. -/
noncomputable def spaceApproximationModel_oneBefore_ofRepresentedVector
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (J : Lattice.JordanDecomposition q L (t + 1))
    (P : BONG.JordanOrderProfileWitness a.toBONG J)
    (z : Fin t) (A : Kˣ)
    (x : (J.toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (z.val + 1)).carrier)
    (hxA : (J.prefixSpace (z.val + 1)).quadratic x = (A : K))
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z))
    (happroximation : a.IsSpaceApproximation
      (P.boundaryOneBeforeIndex z hrank)
      ((BONG.JordanOrderProfileWitness.BoundaryOneBeforeModel.ofRepresentedVector
        (P := P) (z := z) (A := A) x hxA).approximationUnits hrank)) :
    BONG.GoodBONG.SpaceApproximationModel a
      (P.boundaryOneBeforeIndex z hrank) := by
  letI : Module.Finite K V := L.moduleFinite
  let C := J.toOrthogonalDecomposition.prefixQuadraticSublattice
    (z.val + 1)
  let Qp := C.space
  have hx : Qp.IsAnisotropic x := by
    unfold QuadraticSpace.IsAnisotropic
    rw [hxA]
    exact Units.ne_zero A
  let Qc := Qp.orthogonalSpace x hx
  let D : Lattice.QuadraticSublattice Qp :=
    { carrier := Qp.vectorOrthogonal x
      nondegenerate := Qc.nondegenerate
      lattice := Lattice.basisLattice (Module.finBasis K (Qp.vectorOrthogonal x)) }
  let lifted := C.liftNested D
  let M := BONG.JordanOrderProfileWitness.BoundaryOneBeforeModel.ofRepresentedVector
    (P := P) (z := z) (A := A) x hxA
  have hprefix : (P.boundaryIndex z).val + 1 =
      finrank K C.carrier := by
    simpa only [Fintype.card_fin] using
      Fintype.card_congr (P.boundaryPrefixRankEquiv z)
  have horth := Qp.finrank_vectorOrthogonal hx
  have hcomplement : finrank K (Qp.vectorOrthogonal x) =
      (P.boundaryIndex z).val := by
    omega
  let e : Fin (P.boundaryIndex z).val ≃
      Fin (finrank K (Qp.vectorOrthogonal x)) :=
    finCongr hcomplement.symm
  let units : Fin (P.boundaryIndex z).val → Kˣ :=
    Qc.diagonalUnits ∘ e
  let reindex := QuadraticSpace.finiteDiagonalReindexIsometry
    (diagonalUnitCoefficients Qc.diagonalUnits)
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero Qc.diagonalUnits) e
  let complementIso : QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients units)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero units)) Qc := by
    have hraw := reindex.symm.trans Qc.diagonalizationIsometry.symm
    change QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal
        (fun i ↦ (Qc.diagonalUnits (e i) : K))
        (fun i ↦ Units.ne_zero (Qc.diagonalUnits (e i)))) Qc
    simpa only [reindex, Qc, QuadraticSpace.diagonalModel,
      diagonalUnitCoefficients] using hraw
  have hMunits : M.units = units := by rfl
  let e' := M.rankEquiv hrank
  let approximationReindex := QuadraticSpace.finiteDiagonalReindexIsometry
    (diagonalUnitCoefficients M.units)
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero M.units) e'
  let complementPresentation : QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients (M.approximationUnits hrank))
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero
          (M.approximationUnits hrank))) Qc := by
    rw [hMunits] at approximationReindex
    exact approximationReindex.symm.trans complementIso
  refine
    { carrier := lifted.carrier
      nondegenerate := lifted.nondegenerate
      units := M.approximationUnits hrank
      approximation := happroximation
      presentation := ?_ }
  exact complementPresentation.trans
    (C.liftNestedIsometry D).toQuadraticSpaceIsometry

set_option maxHeartbeats 0 in
/-- A vector in the complete Jordan prefix belongs to the canonical
one-before model exactly when it is orthogonal to the removed represented
vector.  This introduction form avoids exposing the nested-subtype
bookkeeping to Section 5. -/
theorem mem_spaceApproximationModel_oneBefore_ofRepresentedVector_carrier
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (J : Lattice.JordanDecomposition q L (t + 1))
    (P : BONG.JordanOrderProfileWitness a.toBONG J)
    (z : Fin t) (A : Kˣ)
    (x : (J.toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (z.val + 1)).carrier)
    (hxA : (J.prefixSpace (z.val + 1)).quadratic x = (A : K))
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z))
    (happroximation : a.IsSpaceApproximation
      (P.boundaryOneBeforeIndex z hrank)
      ((BONG.JordanOrderProfileWitness.BoundaryOneBeforeModel.ofRepresentedVector
        (P := P) (z := z) (A := A) x hxA).approximationUnits hrank))
    (y : V)
    (hyPrefix : y ∈ J.toOrthogonalDecomposition.prefixCarrier (z.val + 1))
    (hyOrthogonal : q.bilin y (x : V) = 0) :
    y ∈ (spaceApproximationModel_oneBefore_ofRepresentedVector
      a J P z A x hxA hrank happroximation).carrier := by
  letI : Module.Finite K V := L.moduleFinite
  let C := J.toOrthogonalDecomposition.prefixQuadraticSublattice
    (z.val + 1)
  let Qp := C.space
  have hx : Qp.IsAnisotropic x := by
    unfold QuadraticSpace.IsAnisotropic
    rw [hxA]
    exact Units.ne_zero A
  let Qc := Qp.orthogonalSpace x hx
  let D : Lattice.QuadraticSublattice Qp :=
    { carrier := Qp.vectorOrthogonal x
      nondegenerate := Qc.nondegenerate
      lattice := Lattice.basisLattice (Module.finBasis K (Qp.vectorOrthogonal x)) }
  change y ∈ C.nestedCarrier D
  let yC : C.carrier := ⟨y, hyPrefix⟩
  have hyD : yC ∈ D.carrier := by
    change yC ∈ Qp.vectorOrthogonal x
    rw [Qp.mem_vectorOrthogonal_iff]
    change q.bilin (x : V) y = 0
    rw [q.isSymm.eq]
    exact hyOrthogonal
  exact ⟨yC, hyD, rfl⟩

set_option maxHeartbeats 0 in
/-- A represented abstract line supplies the vector needed by the preceding
geometric construction. -/
noncomputable def spaceApproximationModel_oneBefore_ofLineRepresentation
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (J : Lattice.JordanDecomposition q L (t + 1))
    (P : BONG.JordanOrderProfileWitness a.toBONG J)
    (z : Fin t) (A : Kˣ)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z))
    (hrep : (J.prefixSpace (z.val + 1)).Represents
      (QuadraticSpace.scaledLine A))
    (happroximation : a.IsSpaceApproximation
      (P.boundaryOneBeforeIndex z hrank)
      ((BONG.JordanOrderProfileWitness.BoundaryOneBeforeModel.ofLineRepresentation
        (P := P) (z := z) (A := A) hrep).approximationUnits hrank)) :
    BONG.GoodBONG.SpaceApproximationModel a
      (P.boundaryOneBeforeIndex z hrank) := by
  let f := Classical.choice hrep
  let x := f.toLinearMap 1
  have hxA : (J.prefixSpace (z.val + 1)).quadratic x = (A : K) := by
    have hq := f.map_quadratic 1
    simpa only [x, QuadraticSpace.scaledLine_quadratic_apply, one_pow,
      mul_one] using hq
  apply spaceApproximationModel_oneBefore_ofRepresentedVector
    a J P z A x hxA hrank
  exact happroximation

set_option maxHeartbeats 0 in
/-- Lemma 3.7(iii) realized as the orthogonal complement of a represented
norm-generator vector in the preceding Jordan prefix. -/
noncomputable def beli2019Lemma37Model_iii_ofRepresentedVector
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : BONG.JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (z : Fin t) (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex z)) A)
    (x : ((W.toJordan hstrict).toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (z.val + 1)).carrier)
    (hxA : ((W.toJordan hstrict).prefixSpace
      (z.val + 1)).quadratic x = (A : K))
    (hrank : 1 < (W.toJordan hstrict).componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z))
    (hpositive : 0 < (P.boundaryOneBeforeIndex z hrank).val)
    (houter : a.order
        ⟨(P.boundaryOneBeforeIndex z hrank).val - 1, by omega⟩ =
      a.order
        ⟨(P.boundaryOneBeforeIndex z hrank).val + 1, by omega⟩) :
    BONG.GoodBONG.SpaceApproximationModel a
      (P.boundaryOneBeforeIndex z hrank) := by
  let M := BONG.JordanOrderProfileWitness.BoundaryOneBeforeModel.ofRepresentedVector
    (P := P) (z := z) (A := A) x hxA
  apply spaceApproximationModel_oneBefore_ofRepresentedVector
    a (W.toJordan hstrict) P z A x hxA hrank
  exact beli2019Lemma37_iii a W hW hstrict P z A hA M hrank
    hpositive houter

end BONG.JordanOrderProfileWitness.PrescribedJordanComparison

end Bong
