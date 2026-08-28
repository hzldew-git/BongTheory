/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019RepresentationConditionsScalarTransport
import Bong.Bong.GoodMap

/-!
# Moving equal-rank scalar data into one quadratic space

At equal rank, an ambient quadratic-space representation is an isometry.
This light-weight module transports the source lattice, its good BONG, and
the four scalar conditions along that isometry.  The recursive Section 9
problem package is deliberately kept out of this dependency layer.
-/

namespace Bong

open Dyadic

universe u v w

/-- A choice of the ambient isometry that identifies an equal-rank source
space with the target space. -/
structure Beli2019SameRankCommonSpace
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {n : Nat}
    (a : BONG.GoodBONG q L (n + 1))
    (b : BONG.GoodBONG r M (n + 1)) where
  ambientIsometry : QuadraticSpace.Isometry r q

namespace Beli2019SameRankCommonSpace

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {a : BONG.GoodBONG q L (n + 1)}
  {b : BONG.GoodBONG r M (n + 1)}

/-- An ambient representation becomes an ambient isometry because the two
good BONGs certify equal finite dimensions. -/
noncomputable def ofAmbient (ambient : q.Represents r) :
    Beli2019SameRankCommonSpace a b := by
  letI : FiniteDimensional K W :=
    M.ambientBasis.finiteDimensional_of_finite
  letI : FiniteDimensional K V :=
    L.ambientBasis.finiteDimensional_of_finite
  have hsource : n + 1 = Module.finrank K W :=
    b.toBONG.length_eq_finrank
  have htarget : n + 1 = Module.finrank K V :=
    a.toBONG.length_eq_finrank
  have hfinrank : Module.finrank K W = Module.finrank K V := by
    omega
  let f := Classical.choice ambient
  exact ⟨f.toIsometryOfFinrankEq hfinrank⟩

variable (D : Beli2019SameRankCommonSpace a b)

/-- The literal image of the source lattice in the target space. -/
noncomputable def sourceImage : Lattice K V :=
  Lattice.map D.ambientIsometry.toLinearEquiv M

/-- The source good BONG transported to its literal image lattice. -/
noncomputable def sourceImageBONG :
    BONG.GoodBONG q D.sourceImage (n + 1) :=
  b.map D.ambientIsometry

/-- The ambient isometry is a lattice isometry from the source lattice to
its literal image. -/
noncomputable def sourceImageIsometry :
    Lattice.Isometry r q M D.sourceImage where
  toLinearEquiv := D.ambientIsometry.toLinearEquiv
  map_bilin := D.ambientIsometry.map_bilin
  map_mem x :=
    (Lattice.map_mem_map_iff D.ambientIsometry.toLinearEquiv M x).symm

/-- Mapping an ambient good BONG preserves its complete scalar sequence. -/
theorem source_scalarAgreement :
    BONG.GoodBONG.ScalarAgreement b D.sourceImageBONG where
  valueUnit_eq i := by
    apply Units.ext
    change b.value i = D.sourceImageBONG.value i
    exact (BONG.value_map D.ambientIsometry b.toBONG i).symm

/-- The target BONG agrees with itself while the source is mapped. -/
theorem conditions
    (h : RepresentationConditions a b (Nat.le_refl n)) :
    RepresentationConditions a D.sourceImageBONG (Nat.le_refl n) :=
  (BONG.GoodBONG.ScalarAgreement.refl a).representationConditions_transport
    D.source_scalarAgreement h

/-- The same construction for the revised v2 condition package. -/
theorem conditionsPrime
    (h : RepresentationConditionsPrime a b (Nat.le_refl n)) :
    RepresentationConditionsPrime a D.sourceImageBONG (Nat.le_refl n) :=
  (BONG.GoodBONG.ScalarAgreement.refl a)
    |>.representationConditionsPrime_transport D.source_scalarAgreement h

/-- Mapping the source along the chosen ambient isometry neither creates nor
destroys an integral lattice representation. -/
theorem represents_image_iff :
    Lattice.Represents q q L D.sourceImage ↔
      Lattice.Represents q r L M := by
  constructor
  · intro himage
    exact himage.trans ⟨D.sourceImageIsometry.toRepresentation⟩
  · intro horiginal
    exact horiginal.trans ⟨D.sourceImageIsometry.symm.toRepresentation⟩

end Beli2019SameRankCommonSpace

end Bong
