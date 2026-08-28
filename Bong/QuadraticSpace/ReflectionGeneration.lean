/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.WallReflectionReduction

/-!
# Reflection generation of a finite-dimensional orthogonal group

This is a source-compatible Cartan--Dieudonne existence theorem.  The proof
uses at most two reflections to make an anisotropic vector fixed, restricts
to its orthogonal complement, and proceeds by induction on dimension.  The
sharp bound on the number of reflections is not needed for the spinor norm.
-/

namespace Bong

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}

/-- A typed word in anisotropic reflections. -/
inductive ReflectionWord (q : QuadraticSpace K V) where
  | nil : ReflectionWord q
  | snoc (w : ReflectionWord q) (x : V)
      (hx : q.IsAnisotropic x) : ReflectionWord q

/-- Evaluate a reflection word from left to right. -/
noncomputable def ReflectionWord.eval : ReflectionWord q → Isometry q q
  | .nil => Isometry.refl q
  | .snoc w x hx => reflectAfter w.eval x hx

@[simp]
theorem ReflectionWord.eval_nil :
    (ReflectionWord.nil : ReflectionWord q).eval = Isometry.refl q :=
  rfl

@[simp]
theorem ReflectionWord.eval_snoc (w : ReflectionWord q) (x : V)
    (hx : q.IsAnisotropic x) :
    (ReflectionWord.snoc w x hx).eval = reflectAfter w.eval x hx :=
  rfl

variable {x : V} {hx : q.IsAnisotropic x}

/-- Orthogonal extension preserves the identity. -/
theorem orthogonalExtensionIsometry_refl :
    orthogonalExtensionIsometry
        (Isometry.refl (q.orthogonalSpace x hx)) =
      Isometry.refl q := by
  apply Isometry.ext
  intro y
  rw [orthogonalExtensionIsometry,
    orthogonalExtensionLinearEquiv_apply,
    orthogonalExtensionLinearMap_apply]
  change (q.bilin x y / q.quadratic x) • x +
      (q.orthogonalProjection x y) = y
  simpa only [q.lineProjection_apply] using
    q.lineProjection_add_orthogonalProjection x y

/-- Orthogonal extension preserves composition. -/
theorem orthogonalExtensionIsometry_trans
    (f g : Isometry (q.orthogonalSpace x hx)
      (q.orthogonalSpace x hx)) :
    orthogonalExtensionIsometry (f.trans g) =
      (orthogonalExtensionIsometry f).trans
        (orthogonalExtensionIsometry g) := by
  apply Isometry.ext
  intro y
  change orthogonalExtensionLinearMap (f.trans g) y =
    orthogonalExtensionLinearMap g (orthogonalExtensionLinearMap f y)
  calc
    orthogonalExtensionLinearMap (f.trans g) y =
        (q.bilin x y / q.quadratic x) • x +
          (g.toLinearEquiv
            (f.toLinearEquiv (q.projectionToOrthogonal x hx y)) : V) := by
      rw [orthogonalExtensionLinearMap_apply]
      rfl
    _ = orthogonalExtensionLinearMap g
        (orthogonalExtensionLinearMap f y) := by
      rw [orthogonalExtensionLinearMap_apply,
        bilin_orthogonalExtensionLinearMap]
      congr 1
      rw [show q.projectionToOrthogonal x hx
          (orthogonalExtensionLinearMap f y) =
            f.toLinearEquiv (q.projectionToOrthogonal x hx y) by
        apply Subtype.ext
        exact orthogonalProjection_orthogonalExtensionLinearMap f y]

/-- Restrict an isometry fixing `x` to `x^perp`. -/
noncomputable def restrictFixingVector (f : Isometry q q)
    (hfix : f.toLinearEquiv x = x) :
    Isometry (q.orthogonalSpace x hx) (q.orthogonalSpace x hx) := by
  have hfixInv : f.toLinearEquiv.symm x = x := by
    apply f.toLinearEquiv.injective
    rw [f.toLinearEquiv.apply_symm_apply, hfix]
  let forward : q.vectorOrthogonal x →ₗ[K] q.vectorOrthogonal x :=
    { toFun := fun y => ⟨f.toLinearEquiv y, by
        rw [q.mem_vectorOrthogonal_iff]
        have hmap := f.map_bilin x y
        rw [hfix] at hmap
        exact hmap.trans
          ((q.mem_vectorOrthogonal_iff x y).1 y.property)⟩
      map_add' := fun y z => by
        apply Subtype.ext
        exact f.toLinearEquiv.map_add y z
      map_smul' := fun a y => by
        apply Subtype.ext
        exact f.toLinearEquiv.map_smul a y }
  let backward : q.vectorOrthogonal x →ₗ[K] q.vectorOrthogonal x :=
    { toFun := fun y => ⟨f.toLinearEquiv.symm y, by
        rw [q.mem_vectorOrthogonal_iff]
        have hmap := f.symm.map_bilin x y
        change q.bilin (f.toLinearEquiv.symm x)
          (f.toLinearEquiv.symm y) = q.bilin x y at hmap
        rw [hfixInv] at hmap
        exact hmap.trans
          ((q.mem_vectorOrthogonal_iff x y).1 y.property)⟩
      map_add' := fun y z => by
        apply Subtype.ext
        exact f.toLinearEquiv.symm.map_add y z
      map_smul' := fun a y => by
        apply Subtype.ext
        exact f.toLinearEquiv.symm.map_smul a y }
  let e : q.vectorOrthogonal x ≃ₗ[K] q.vectorOrthogonal x :=
    LinearEquiv.ofLinear forward backward
      (by
        ext y
        change f.toLinearEquiv (f.toLinearEquiv.symm y) = y
        exact f.toLinearEquiv.apply_symm_apply y)
      (by
        ext y
        change f.toLinearEquiv.symm (f.toLinearEquiv y) = y
        exact f.toLinearEquiv.symm_apply_apply y)
  exact
    { toLinearEquiv := e
      map_bilin := fun y z => f.map_bilin y z }

@[simp]
theorem restrictFixingVector_apply (f : Isometry q q)
    (hfix : f.toLinearEquiv x = x) (y : q.vectorOrthogonal x) :
    ((restrictFixingVector (hx := hx) f hfix).toLinearEquiv y : V) =
      f.toLinearEquiv y :=
  rfl

/-- Extending the restriction of a fixing isometry recovers the original
isometry. -/
theorem orthogonalExtensionIsometry_restrictFixingVector
    (f : Isometry q q) (hfix : f.toLinearEquiv x = x) :
    orthogonalExtensionIsometry (anisotropic := hx)
      (restrictFixingVector (hx := hx) f hfix) = f := by
  apply Isometry.ext
  intro y
  rw [orthogonalExtensionIsometry,
    orthogonalExtensionLinearEquiv_apply,
    orthogonalExtensionLinearMap_apply]
  change (q.bilin x y / q.quadratic x) • x +
      f.toLinearEquiv (q.projectionToOrthogonal x hx y) =
    f.toLinearEquiv y
  calc
    _ = f.toLinearEquiv
        ((q.bilin x y / q.quadratic x) • x +
          q.orthogonalProjection x y) := by
      rw [map_add, map_smul, hfix]
      rfl
    _ = f.toLinearEquiv y := by
      rw [← q.lineProjection_apply,
        q.lineProjection_add_orthogonalProjection]

/-- Lift a reflection word on `x^perp` to the ambient space. -/
noncomputable def ReflectionWord.liftOrthogonal :
    ReflectionWord (q.orthogonalSpace x hx) → ReflectionWord q
  | .nil => .nil
  | .snoc w y hy =>
      .snoc w.liftOrthogonal (y : V) (by exact hy)

/-- Evaluation commutes with lifting from an orthogonal complement. -/
theorem ReflectionWord.eval_liftOrthogonal
    (w : ReflectionWord (q.orthogonalSpace x hx)) :
    w.liftOrthogonal.eval = orthogonalExtensionIsometry w.eval := by
  induction w with
  | nil =>
      exact orthogonalExtensionIsometry_refl.symm
  | snoc w y hy ih =>
      rw [liftOrthogonal, eval_snoc, eval_snoc, ih]
      change (orthogonalExtensionIsometry w.eval).trans
          (q.reflectionIsometry (y : V) hy) =
        orthogonalExtensionIsometry
          (w.eval.trans
            ((q.orthogonalSpace x hx).reflectionIsometry y hy))
      rw [orthogonalExtensionIsometry_trans,
        orthogonalExtensionIsometry_reflection]

private theorem reflectionWord_exists_of_finrank_eq (n : ℕ) :
    ∀ {V : Type v} [AddCommGroup V] [Module K V]
      [FiniteDimensional K V] (q : QuadraticSpace K V)
      (f : Isometry q q),
      Module.finrank K V = n → ∃ w : ReflectionWord q, w.eval = f := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro V _ _ _ q f hdim
      by_cases hn : n = 0
      · have hzero : Module.finrank K V = 0 := hdim.trans hn
        refine ⟨.nil, ?_⟩
        rw [ReflectionWord.eval_nil]
        apply Isometry.ext
        intro z
        have hz := finrank_zero_iff_forall_zero.mp hzero z
        rw [hz]
        simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hVpos : 0 < Module.finrank K V := by simpa [hdim]
        obtain ⟨x, hx⟩ := q.exists_isAnisotropic_of_finrank_pos hVpos
        let y : V := f.toLinearEquiv x
        have hy : q.IsAnisotropic y := by
          change q.quadratic (f.toLinearEquiv x) ≠ 0
          rw [f.map_quadratic]
          exact hx
        have hyx : q.quadratic y = q.quadratic x := by
          exact f.map_quadratic x
        have htailRank :
            Module.finrank K (q.vectorOrthogonal x) < n := by
          have hrank := q.finrank_vectorOrthogonal hx
          rw [hdim] at hrank
          omega
        have factorFixing (g : Isometry q q)
            (hfix : g.toLinearEquiv x = x) :
            ∃ w : ReflectionWord q, w.eval = g := by
          let r := restrictFixingVector (hx := hx) g hfix
          obtain ⟨w, hw⟩ :=
            ih (Module.finrank K (q.vectorOrthogonal x)) htailRank
              (q.orthogonalSpace x hx) r rfl
          refine ⟨w.liftOrthogonal, ?_⟩
          rw [ReflectionWord.eval_liftOrthogonal, hw,
            orthogonalExtensionIsometry_restrictFixingVector]
        by_cases hsub : q.IsAnisotropic (y - x)
        · let t := q.reflectionIsometry (y - x) hsub
          let g := f.trans t
          have hfix : g.toLinearEquiv x = x := by
            change q.reflectionLinearEquiv (y - x) hsub y = x
            exact q.reflectionLinearEquiv_sub_apply_left_of_equalValue
              y x hsub hyx
          obtain ⟨w, hw⟩ := factorFixing g hfix
          refine ⟨.snoc w (y - x) hsub, ?_⟩
          rw [ReflectionWord.eval_snoc, hw]
          apply Isometry.ext
          intro z
          change q.reflectionLinearEquiv (y - x) hsub
              (q.reflectionLinearEquiv (y - x) hsub
                (f.toLinearEquiv z)) = f.toLinearEquiv z
          exact q.reflectionLinearEquiv_involutive (y - x) hsub _
        · have hsum : q.IsAnisotropic (y + x) :=
            q.isAnisotropic_add_of_not_isAnisotropic_sub
              y x hy hyx hsub
          let s := q.reflectionIsometry (y + x) hsum
          let t := q.reflectionIsometry x hx
          let g := (f.trans s).trans t
          have hfix : g.toLinearEquiv x = x := by
            change q.reflectionLinearEquiv x hx
              (q.reflectionLinearEquiv (y + x) hsum y) = x
            rw [q.reflectionLinearEquiv_add_apply_left_of_quadratic_eq
              y x hsum hyx]
            calc
              q.reflectionLinearEquiv x hx (-x) =
                  -q.reflectionLinearEquiv x hx x :=
                (q.reflectionLinearEquiv x hx).map_neg x
              _ = -(-x) := by
                rw [q.reflectionLinearEquiv_apply_self]
              _ = x := neg_neg x
          obtain ⟨w, hw⟩ := factorFixing g hfix
          refine ⟨.snoc (.snoc w x hx) (y + x) hsum, ?_⟩
          rw [ReflectionWord.eval_snoc, ReflectionWord.eval_snoc, hw]
          apply Isometry.ext
          intro z
          change q.reflectionLinearEquiv (y + x) hsum
              (q.reflectionLinearEquiv x hx
                (q.reflectionLinearEquiv x hx
                  (q.reflectionLinearEquiv (y + x) hsum
                    (f.toLinearEquiv z)))) = f.toLinearEquiv z
          rw [q.reflectionLinearEquiv_involutive x hx,
            q.reflectionLinearEquiv_involutive (y + x) hsum]

/-- Every isometry of a finite-dimensional nondegenerate quadratic space
over a characteristic-zero field is a product of anisotropic reflections. -/
theorem exists_reflectionWord [FiniteDimensional K V]
    (f : Isometry q q) :
    ∃ w : ReflectionWord q, w.eval = f :=
  reflectionWord_exists_of_finrank_eq
    (Module.finrank K V) q f rfl

end QuadraticSpace

end Bong
