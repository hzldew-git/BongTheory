import Bong.Bong.Representation

/-!
# The nondegenerate image of a quadratic-space representation

An injective representation identifies its source with a nondegenerate
restricted subspace of the target.  This packages the range equivalence and
the resulting quadratic isometry.
-/

namespace Bong

namespace QuadraticSpace.Representation

universe u v w

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}

/-- The source of a representation is linearly equivalent to its range. -/
noncomputable def rangeEquiv (f : QuadraticSpace.Representation q r) :
    V ≃ₗ[K] LinearMap.range f.toLinearMap :=
  LinearEquiv.ofBijective f.toLinearMap.rangeRestrict ⟨by
    intro x y hxy
    apply f.injective
    exact congrArg Subtype.val hxy, LinearMap.surjective_rangeRestrict _⟩

@[simp]
theorem coe_rangeEquiv_apply (f : QuadraticSpace.Representation q r)
    (x : V) :
    ((f.rangeEquiv x : LinearMap.range f.toLinearMap) : W) =
      f.toLinearMap x :=
  rfl

/-- The range of a quadratic-space representation is nondegenerate. -/
theorem range_nondegenerate (f : QuadraticSpace.Representation q r) :
    (r.bilin.restrict (LinearMap.range f.toLinearMap)).Nondegenerate := by
  let e := f.rangeEquiv
  have hform :
      r.bilin.restrict (LinearMap.range f.toLinearMap) =
        LinearMap.BilinForm.congr e q.bilin := by
    ext x y
    change r.bilin (x : W) (y : W) =
      q.bilin (e.symm x) (e.symm y)
    rw [← f.map_bilin]
    congr 2
    · exact (congrArg Subtype.val (e.apply_symm_apply x)).symm
    · exact (congrArg Subtype.val (e.apply_symm_apply y)).symm
  rw [hform]
  exact q.nondegenerate.congr e

/-- A representation is an isometry from its source onto the restricted
quadratic space carried by its range. -/
noncomputable def rangeIsometry (f : QuadraticSpace.Representation q r) :
    QuadraticSpace.Isometry q
      (r.restrict (LinearMap.range f.toLinearMap) f.range_nondegenerate) where
  toLinearEquiv := f.rangeEquiv
  map_bilin := f.map_bilin

end QuadraticSpace.Representation

end Bong
