/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Representation
import Bong.Bong.SectionTwo
import Bong.Lattice.OrthogonalMap
import Bong.QuadraticSpace.OrthogonalExtension

/-!
# Beli (2019), Section 9: the solved-head geometric step

Lemmas 9.3 and 9.6 construct norm generators of the source and target
lattices with equal quadratic value.  After applying the induction hypothesis
to their orthogonal projections, the resulting ambient isometry sends the
source generator to the target generator and sends the projected source
lattice into the projected target lattice.

This file isolates the common geometric conclusion.  Beli's reconstruction
lemma (2003, Lemma 2.2) then proves integrality of the whole ambient map, so
the original source lattice is represented by the target lattice.
-/

namespace Bong

open Dyadic

universe u v w

/--
The concrete certificate produced by either solved head branch in Beli
(2019), Section 9.  The terminology follows `Lattice.Represents`: `L` is the
target (representing) lattice and `M` is the source lattice.
-/
structure Beli2019SolvedHeadData
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (L : Lattice K V) (M : Lattice K W) where
  /-- The target norm generator. -/
  targetHead : V
  /-- The source norm generator. -/
  sourceHead : W
  targetHeadGenerator :
    Lattice.IsNormGenerator q L targetHead
  sourceHeadGenerator :
    Lattice.IsNormGenerator r M sourceHead
  targetHeadAnisotropic : q.IsAnisotropic targetHead
  sourceHeadAnisotropic : r.IsAnisotropic sourceHead
  /-- The ambient isometry obtained by adjoining the equal head line to the
  representation of the two projected lattices. -/
  ambient : QuadraticSpace.Isometry r q
  /-- The two selected heads agree under the ambient isometry. -/
  ambient_sourceHead : ambient.toLinearEquiv sourceHead = targetHead
  /-- The induction hypothesis on the orthogonal complements, transported to
  a literal inclusion in the target orthogonal complement. -/
  projected_le :
    Lattice.projectedLattice q
        (Lattice.map ambient.toLinearEquiv M) targetHead
        targetHeadAnisotropic ≤
      Lattice.projectedLattice q L targetHead targetHeadAnisotropic

namespace Beli2019SolvedHeadData

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The image of the source head is a norm generator of the image lattice. -/
theorem imageHeadGenerator (D : Beli2019SolvedHeadData q r L M) :
    Lattice.IsNormGenerator q (Lattice.map D.ambient.toLinearEquiv M)
      D.targetHead := by
  refine ⟨?_, ?_⟩
  · rw [← D.ambient_sourceHead]
    exact (Lattice.map_mem_map_iff D.ambient.toLinearEquiv M
      D.sourceHead).2 D.sourceHeadGenerator.mem
  · calc
      Lattice.normIdeal q (Lattice.map D.ambient.toLinearEquiv M) =
          Lattice.normIdeal r M :=
        Lattice.normIdeal_map_isometry D.ambient M
      _ = Lattice.principalIdeal (K := K)
          (r.quadratic D.sourceHead) :=
        D.sourceHeadGenerator.normIdeal_eq
      _ = Lattice.principalIdeal (K := K)
          (q.quadratic (D.ambient.toLinearEquiv D.sourceHead)) := by
        rw [D.ambient.map_quadratic]
      _ = Lattice.principalIdeal (K := K)
          (q.quadratic D.targetHead) := by
        rw [D.ambient_sourceHead]

/-- The mapped source lattice and target lattice have the same norm ideal. -/
theorem image_normIdeal_eq (D : Beli2019SolvedHeadData q r L M) :
    Lattice.normIdeal q (Lattice.map D.ambient.toLinearEquiv M) =
      Lattice.normIdeal q L :=
  D.imageHeadGenerator.normIdeal_eq.trans
    D.targetHeadGenerator.normIdeal_eq.symm

/-- Beli's reconstruction lemma turns the head certificate into a literal
inclusion of the isometric image of the source lattice. -/
theorem image_le (D : Beli2019SolvedHeadData q r L M) :
    Lattice.map D.ambient.toLinearEquiv M ≤ L := by
  apply Lattice.le_of_normIdeal_le_of_projectedLattice_le
    q L (Lattice.map D.ambient.toLinearEquiv M) D.targetHead
      D.targetHeadGenerator D.targetHeadAnisotropic
  · exact D.image_normIdeal_eq.le
  · exact D.projected_le

/-- The solved-head certificate proves the required lattice representation. -/
theorem represents (D : Beli2019SolvedHeadData q r L M) :
    Lattice.Represents q r L M := by
  refine ⟨
    { toLinearMap := D.ambient.toLinearEquiv.toLinearMap
      injective := D.ambient.toLinearEquiv.injective
      map_bilin := D.ambient.map_bilin
      map_mem := ?_ }⟩
  intro x hx
  exact D.image_le
    ((Lattice.map_mem_map_iff D.ambient.toLinearEquiv M x).2 hx)

/-- A same-rank representation of the two projected lattices, together with
equal-valued norm-generating heads, produces the complete solved-head
certificate.  This is the common geometric final step in Beli (2019),
Lemmas 9.3 and 9.6. -/
noncomputable def ofProjectedRepresentation
    (targetHead : V) (sourceHead : W)
    (targetHeadGenerator : Lattice.IsNormGenerator q L targetHead)
    (sourceHeadGenerator : Lattice.IsNormGenerator r M sourceHead)
    (targetHeadAnisotropic : q.IsAnisotropic targetHead)
    (sourceHeadAnisotropic : r.IsAnisotropic sourceHead)
    (hvalue : q.quadratic targetHead = r.quadratic sourceHead)
    (hfinrank : Module.finrank K W = Module.finrank K V)
    (tail : Lattice.Representation
      (r.orthogonalSpace sourceHead sourceHeadAnisotropic)
      (q.orthogonalSpace targetHead targetHeadAnisotropic)
      (Lattice.projectedLattice r M sourceHead sourceHeadAnisotropic)
      (Lattice.projectedLattice q L targetHead targetHeadAnisotropic)) :
    Beli2019SolvedHeadData q r L M := by
  letI : FiniteDimensional K W :=
    M.ambientBasis.finiteDimensional_of_finite
  letI : FiniteDimensional K V :=
    L.ambientBasis.finiteDimensional_of_finite
  have htailFinrank :
      Module.finrank K (r.vectorOrthogonal sourceHead) =
        Module.finrank K (q.vectorOrthogonal targetHead) := by
    have hsource := r.finrank_vectorOrthogonal sourceHeadAnisotropic
    have htarget := q.finrank_vectorOrthogonal targetHeadAnisotropic
    omega
  let tailIsometry : QuadraticSpace.Isometry
      (r.orthogonalSpace sourceHead sourceHeadAnisotropic)
      (q.orthogonalSpace targetHead targetHeadAnisotropic) :=
    tail.toQuadraticSpaceIsometryOfFinrankEq htailFinrank
  let ambient : QuadraticSpace.Isometry r q :=
    QuadraticSpace.headExtensionIsometry hvalue tailIsometry
  refine
    { targetHead := targetHead
      sourceHead := sourceHead
      targetHeadGenerator := targetHeadGenerator
      sourceHeadGenerator := sourceHeadGenerator
      targetHeadAnisotropic := targetHeadAnisotropic
      sourceHeadAnisotropic := sourceHeadAnisotropic
      ambient := ambient
      ambient_sourceHead := ?_
      projected_le := ?_ }
  · exact QuadraticSpace.headExtensionIsometry_apply_sourceHead
      hvalue tailIsometry
  · intro z hz
    rcases (Lattice.mem_projectedLattice_iff q
      (Lattice.map ambient.toLinearEquiv M) targetHead
      targetHeadAnisotropic z).1 hz with ⟨v, hv, hvProjection⟩
    let w : W := ambient.toLinearEquiv.symm v
    have hw : w ∈ M :=
      (Lattice.mem_map_iff ambient.toLinearEquiv M v).1 hv
    let p := r.projectionToOrthogonal sourceHead sourceHeadAnisotropic w
    have hp : p ∈ Lattice.projectedLattice r M sourceHead
        sourceHeadAnisotropic :=
      Lattice.projection_mem_projectedLattice r M sourceHead
        sourceHeadAnisotropic hw
    have htailMem := tail.map_mem hp
    have htailMem' : tailIsometry.toLinearEquiv p ∈
        Lattice.projectedLattice q L targetHead targetHeadAnisotropic := by
      simpa [tailIsometry] using htailMem
    have hambient : ambient.toLinearEquiv w = v :=
      ambient.toLinearEquiv.apply_symm_apply v
    have hprojection :
        q.projectionToOrthogonal targetHead targetHeadAnisotropic
            (ambient.toLinearEquiv w) =
          tailIsometry.toLinearEquiv p := by
      change q.projectionToOrthogonal targetHead targetHeadAnisotropic
          (QuadraticSpace.headExtensionLinearEquiv hvalue tailIsometry w) =
        tailIsometry.toLinearEquiv
          (r.projectionToOrthogonal sourceHead sourceHeadAnisotropic w)
      exact QuadraticSpace.projectionToOrthogonal_headExtensionLinearEquiv
        hvalue tailIsometry w
    have hz : z = tailIsometry.toLinearEquiv p := by
      calc
        z = q.projectionToOrthogonal targetHead targetHeadAnisotropic v :=
          hvProjection.symm
        _ = q.projectionToOrthogonal targetHead targetHeadAnisotropic
              (ambient.toLinearEquiv w) := by rw [hambient]
        _ = tailIsometry.toLinearEquiv p := hprojection
    rw [hz]
    exact htailMem'

/-- The proposition-level form used by the induction in Section 9: a
representation of the projected source lattice by the projected target
lattice lifts to a representation of the original lattices. -/
theorem represents_of_projected
    (targetHead : V) (sourceHead : W)
    (targetHeadGenerator : Lattice.IsNormGenerator q L targetHead)
    (sourceHeadGenerator : Lattice.IsNormGenerator r M sourceHead)
    (targetHeadAnisotropic : q.IsAnisotropic targetHead)
    (sourceHeadAnisotropic : r.IsAnisotropic sourceHead)
    (hvalue : q.quadratic targetHead = r.quadratic sourceHead)
    (hfinrank : Module.finrank K W = Module.finrank K V)
    (tail : Lattice.Represents
      (q.orthogonalSpace targetHead targetHeadAnisotropic)
      (r.orthogonalSpace sourceHead sourceHeadAnisotropic)
      (Lattice.projectedLattice q L targetHead targetHeadAnisotropic)
      (Lattice.projectedLattice r M sourceHead sourceHeadAnisotropic)) :
    Lattice.Represents q r L M := by
  rcases tail with ⟨tailRepresentation⟩
  exact (ofProjectedRepresentation targetHead sourceHead
    targetHeadGenerator sourceHeadGenerator targetHeadAnisotropic
    sourceHeadAnisotropic hvalue hfinrank tailRepresentation).represents

end Beli2019SolvedHeadData

end Bong
