import Bong.Lattice.MinimalScaleComponent
import Bong.Lattice.OrthogonalProductIsometry

/-!
# Orthogonal sums of two quadratic sublattices

This module packages the carrier sum of two arbitrary orthogonal
nondegenerate subspaces.  Unlike `OrthogonalDecomposition.orthogonalSup`, it
does not require the two subspaces to have first been installed as components
of a decomposition of the whole ambient lattice.
-/

namespace Bong

open Dyadic

namespace Lattice.QuadraticSublattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}

/-- The carriers of two quadratic sublattices are mutually orthogonal. -/
def AreOrthogonal (C D : Lattice.QuadraticSublattice q) : Prop :=
  ∀ (x : C.carrier) (y : D.carrier), q.bilin (x : V) (y : V) = 0

/-- Addition from the product of two carriers to the ambient space. -/
def pairSumMap (C D : Lattice.QuadraticSublattice q) :
    C.carrier × D.carrier →ₗ[K] V :=
  C.carrier.subtype.coprod D.carrier.subtype

/-- The ambient carrier spanned by a pair of sublattices. -/
abbrev pairSupCarrier (C D : Lattice.QuadraticSublattice q) :
    Submodule K V := (pairSumMap C D).range

/-- The first summand is contained in the carrier of the orthogonal pair
sum. -/
theorem leftCarrier_le_pairSupCarrier
    (C D : Lattice.QuadraticSublattice q) :
    C.carrier ≤ C.pairSupCarrier D := by
  intro x hx
  refine ⟨(⟨x, hx⟩, 0), ?_⟩
  simp [pairSumMap]

/-- The second summand is contained in the carrier of the orthogonal pair
sum. -/
theorem rightCarrier_le_pairSupCarrier
    (C D : Lattice.QuadraticSublattice q) :
    D.carrier ≤ C.pairSupCarrier D := by
  intro x hx
  refine ⟨(0, ⟨x, hx⟩), ?_⟩
  simp [pairSumMap]

/-- If both summands lie in a fixed ambient subspace, then so does their
sum carrier.  This elementary carrier lemma is useful when an orthogonal
line is adjoined inside a Jordan prefix. -/
theorem pairSupCarrier_le
    (C D : Lattice.QuadraticSublattice q) (S : Submodule K V)
    (hC : C.carrier ≤ S) (hD : D.carrier ≤ S) :
    C.pairSupCarrier D ≤ S := by
  rintro _ ⟨x, rfl⟩
  exact S.add_mem (hC x.1.property) (hD x.2.property)

variable {C D : Lattice.QuadraticSublattice q}

/-- Orthogonal nondegenerate carriers have zero intersection. -/
theorem carrier_disjoint_of_areOrthogonal
    (horth : C.AreOrthogonal D) : Disjoint C.carrier D.carrier := by
  rw [Submodule.disjoint_def]
  intro x hxC hxD
  let xC : C.carrier := ⟨x, hxC⟩
  have hxorth : ∀ y : C.carrier, q.bilin x (y : V) = 0 := by
    intro y
    exact q.isSymm.eq x (y : V) |>.trans (horth y ⟨x, hxD⟩)
  have hzero : xC = 0 := C.nondegenerate.1 xC hxorth
  exact congrArg Subtype.val hzero

/-- Addition is an equivalence onto the carrier sum. -/
noncomputable def pairSupEquiv (horth : C.AreOrthogonal D) :=
  LinearEquiv.ofInjective (pairSumMap C D) (by
    intro x y hxy
    change (x.1 : V) + (x.2 : V) = (y.1 : V) + (y.2 : V) at hxy
    have hsum : (x.1 : V) - (y.1 : V) = (y.2 : V) - (x.2 : V) :=
      sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm] using hxy)
    have hfirst : (x.1 : V) = (y.1 : V) := by
      apply sub_eq_zero.mp
      exact (Submodule.disjoint_def.mp
        (carrier_disjoint_of_areOrthogonal horth))
          ((x.1 : V) - (y.1 : V))
          (Submodule.sub_mem _ x.1.property y.1.property)
          (hsum ▸ Submodule.sub_mem _ y.2.property x.2.property)
    have hsecond : (x.2 : V) = (y.2 : V) := by
      rw [hfirst] at hxy
      exact add_left_cancel hxy
    exact Prod.ext (Subtype.ext hfirst) (Subtype.ext hsecond))

/-- The restricted ambient form is the transported orthogonal-product form. -/
theorem pairSup_bilin_eq (horth : C.AreOrthogonal D) :
    q.bilin.restrict (C.pairSupCarrier D) =
      LinearMap.BilinForm.congr (pairSupEquiv horth)
        (C.space.orthogonalSum D.space).bilin := by
  let e := pairSupEquiv horth
  apply LinearMap.BilinForm.ext
  intro x y
  obtain ⟨x, rfl⟩ := e.surjective x
  obtain ⟨y, rfl⟩ := e.surjective y
  rw [LinearMap.BilinForm.congr_apply, e.symm_apply_apply,
    e.symm_apply_apply, QuadraticSpace.orthogonalSum_bilin_apply]
  change q.bilin ((x.1 : V) + (x.2 : V))
    ((y.1 : V) + (y.2 : V)) = _
  rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.add_right, horth x.1 y.2]
  have hyx : q.bilin (x.2 : V) (y.1 : V) = 0 :=
    q.isSymm.eq (x.2 : V) (y.1 : V) |>.trans (horth y.1 x.2)
  rw [hyx]
  simp only [add_zero, zero_add]
  rfl

/-- The carrier sum of orthogonal nondegenerate subspaces is nondegenerate. -/
theorem pairSup_nondegenerate (horth : C.AreOrthogonal D) :
    (q.bilin.restrict (C.pairSupCarrier D)).Nondegenerate := by
  rw [pairSup_bilin_eq horth]
  exact (C.space.orthogonalSum D.space).nondegenerate.congr
    (pairSupEquiv horth)

/-- Addition identifies the abstract orthogonal product with its concrete
ambient carrier. -/
noncomputable def pairSupSpaceIsometry (horth : C.AreOrthogonal D) :
    QuadraticSpace.Isometry (C.space.orthogonalSum D.space)
      (q.restrict (C.pairSupCarrier D) (pairSup_nondegenerate horth)) where
  toLinearEquiv := pairSupEquiv horth
  map_bilin x y := by
    rw [QuadraticSpace.orthogonalSum_bilin_apply]
    change q.bilin ((x.1 : V) + (x.2 : V))
      ((y.1 : V) + (y.2 : V)) = _
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.add_right, horth x.1 y.2]
    have hyx : q.bilin (x.2 : V) (y.1 : V) = 0 :=
      q.isSymm.eq (x.2 : V) (y.1 : V) |>.trans (horth y.1 x.2)
    rw [hyx]
    simp only [add_zero, zero_add]
    rfl

/-- The quadratic sublattice obtained by orthogonally adjoining two
sublattices. -/
noncomputable def pairSup (C D : Lattice.QuadraticSublattice q)
    (horth : C.AreOrthogonal D) : Lattice.QuadraticSublattice q where
  carrier := C.pairSupCarrier D
  nondegenerate := pairSup_nondegenerate horth
  lattice := Lattice.map (pairSupEquiv horth)
    (Lattice.product C.lattice D.lattice)

end Lattice.QuadraticSublattice

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}

/-- A represented anisotropic vector identifies its ambient span with the
one-dimensional quadratic space having the represented coefficient. -/
noncomputable def scaledLineUnarySpanIsometry
    (x : V) (A : Kˣ) (hx : q.IsAnisotropic x)
    (hA : q.quadratic x = (A : K)) :
    QuadraticSpace.Isometry (QuadraticSpace.scaledLine A)
      (q.restrict (K ∙ x) (Lattice.unarySpan_restrict_nondegenerate hx)) where
  toLinearEquiv := LinearEquiv.toSpanNonzeroSingleton K V x hx.ne_zero
  map_bilin s t := by
    change q.bilin (s • x) (t • x) = (A : K) * s * t
    rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
    rw [show q.bilin x x = q.quadratic x from rfl, hA]
    ring

end QuadraticSpace

end Bong
