/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Representation
import Bong.QuadraticSpace.Reflection
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Cancellation of a common diagonal head

If an embedding of nondegenerate diagonal spaces contains the same
anisotropic coefficient on both sides, a one-vector Witt transporter moves
the image of the source head onto the target head.  Restriction to the two
orthogonal complements then cancels that common coefficient.

This is the geometric cancellation used after choosing `a₁ = b₁` in Beli
(2019), Lemmas 9.3 and 9.6.
-/

namespace Bong

universe u

namespace QuadraticSpace

variable {K : Type u} [Field K]

/-- The finite nondegenerate diagonal space with coefficients `a`. -/
noncomputable def finiteDiagonal {n : Nat} (a : Fin n → K)
    (ha : ∀ i, a i ≠ 0) : QuadraticSpace K (Fin n → K) where
  bilin := Matrix.toBilin' (Matrix.diagonal a)
  isSymm := (Matrix.isSymm_toBilin'_iff_isSymm).2
    (Matrix.isSymm_diagonal a)
  nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
      (Matrix.diagonal a) (by
        rw [Matrix.det_diagonal]
        exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ ha i))

@[simp]
theorem finiteDiagonal_bilin_apply {n : Nat} (a : Fin n → K)
    (ha : ∀ i, a i ≠ 0) (x y : Fin n → K) :
    (finiteDiagonal a ha).bilin x y = ∑ i, a i * x i * y i := by
  rw [finiteDiagonal, Matrix.toBilin'_apply]
  simp [Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp]
theorem finiteDiagonal_quadratic_apply {n : Nat} (a : Fin n → K)
    (ha : ∀ i, a i ≠ 0) (x : Fin n → K) :
    (finiteDiagonal a ha).quadratic x = diagonalQuadratic a x := by
  rw [quadratic, finiteDiagonal_bilin_apply]
  unfold diagonalQuadratic
  apply Finset.sum_congr rfl
  intro i _
  ring

end QuadraticSpace

namespace DiagonalRepresents

variable {K : Type u} [Field K] [CharZero K]

@[simp]
theorem diagonalQuadratic_cons {n : Nat} (head : K) (tail : Fin n → K)
    (x₀ : K) (x : Fin n → K) :
    diagonalQuadratic (Fin.cons head tail) (Fin.cons x₀ x) =
      head * x₀ ^ 2 + diagonalQuadratic tail x := by
  unfold diagonalQuadratic
  rw [Fin.sum_univ_succ]
  simp

/-- A diagonal representation with nonzero coefficients is a representation
of the associated nondegenerate quadratic spaces. -/
theorem toQuadraticSpaceRepresents
    {m n : Nat} {source : Fin m → K} {target : Fin n → K}
    (hsource : ∀ i, source i ≠ 0) (htarget : ∀ i, target i ≠ 0)
    (h : DiagonalRepresents source target) :
    (QuadraticSpace.finiteDiagonal target htarget).Represents
      (QuadraticSpace.finiteDiagonal source hsource) := by
  rcases h with ⟨f, hf, hquadratic⟩
  refine ⟨
    { toLinearMap := f
      injective := hf
      map_bilin := ?_ }⟩
  intro x y
  let qs := QuadraticSpace.finiteDiagonal source hsource
  let qt := QuadraticSpace.finiteDiagonal target htarget
  have hx : qt.quadratic (f x) = qs.quadratic x := by
    simpa only [qs, qt, QuadraticSpace.finiteDiagonal_quadratic_apply]
      using hquadratic x
  have hy : qt.quadratic (f y) = qs.quadratic y := by
    simpa only [qs, qt, QuadraticSpace.finiteDiagonal_quadratic_apply]
      using hquadratic y
  have hxy : qt.quadratic (f (x + y)) = qs.quadratic (x + y) := by
    simpa only [qs, qt, QuadraticSpace.finiteDiagonal_quadratic_apply]
      using hquadratic (x + y)
  have htwo : (2 : K) ≠ 0 := by norm_num
  apply (mul_left_cancel₀ htwo)
  calc
    2 * qt.bilin (f x) (f y) =
        qt.quadratic (f x + f y) - qt.quadratic (f x) -
          qt.quadratic (f y) := by
      rw [qt.quadratic_add]
      ring
    _ = qs.quadratic (x + y) - qs.quadratic x - qs.quadratic y := by
      rw [← f.map_add, hxy, hx, hy]
    _ = 2 * qs.bilin x y := by
      rw [qs.quadratic_add]
      ring

/-- Cancel a common nonzero first coefficient from a representation of
nondegenerate diagonal forms. -/
theorem cancel_common_head
    {m n : Nat} (head : K) (source : Fin m → K) (target : Fin n → K)
    (hhead : head ≠ 0) (hsource : ∀ i, source i ≠ 0)
    (htarget : ∀ i, target i ≠ 0)
    (hrep : DiagonalRepresents
      (Fin.cons head source) (Fin.cons head target)) :
    DiagonalRepresents source target := by
  let sourceFull : Fin (m + 1) → K := Fin.cons head source
  let targetFull : Fin (n + 1) → K := Fin.cons head target
  have hsourceFull : ∀ i, sourceFull i ≠ 0 := by
    intro i
    refine Fin.cases hhead (fun j ↦ ?_) i
    simpa only [sourceFull, Fin.cons_succ] using hsource j
  have htargetFull : ∀ i, targetFull i ≠ 0 := by
    intro i
    refine Fin.cases hhead (fun j ↦ ?_) i
    simpa only [targetFull, Fin.cons_succ] using htarget j
  let qs := QuadraticSpace.finiteDiagonal sourceFull hsourceFull
  let qt := QuadraticSpace.finiteDiagonal targetFull htargetFull
  have hspace : qt.Represents qs := by
    apply toQuadraticSpaceRepresents hsourceFull htargetFull
    simpa only [sourceFull, targetFull] using hrep
  rcases hspace with ⟨F⟩
  let sourceHead : Fin (m + 1) → K := Fin.cons 1 0
  let targetHead : Fin (n + 1) → K := Fin.cons 1 0
  have hsourceHeadValue : qs.quadratic sourceHead = head := by
    rw [QuadraticSpace.finiteDiagonal_quadratic_apply]
    change diagonalQuadratic (Fin.cons head source) (Fin.cons 1 0) = head
    rw [diagonalQuadratic_cons]
    simp [diagonalQuadratic]
  have htargetHeadValue : qt.quadratic targetHead = head := by
    rw [QuadraticSpace.finiteDiagonal_quadratic_apply]
    change diagonalQuadratic (Fin.cons head target) (Fin.cons 1 0) = head
    rw [diagonalQuadratic_cons]
    simp [diagonalQuadratic]
  have hsourceHeadAnisotropic : qs.IsAnisotropic sourceHead := by
    unfold QuadraticSpace.IsAnisotropic
    rw [hsourceHeadValue]
    exact hhead
  have htargetHeadAnisotropic : qt.IsAnisotropic targetHead := by
    unfold QuadraticSpace.IsAnisotropic
    rw [htargetHeadValue]
    exact hhead
  have himageHeadAnisotropic :
      qt.IsAnisotropic (F.toLinearMap sourceHead) := by
    unfold QuadraticSpace.IsAnisotropic
    rw [F.map_quadratic]
    exact hsourceHeadAnisotropic
  have himageHeadValue :
      qt.quadratic (F.toLinearMap sourceHead) =
        qt.quadratic targetHead := by
    rw [F.map_quadratic, hsourceHeadValue, htargetHeadValue]
  let g := qt.equalValueTransportIsometry
    (F.toLinearMap sourceHead) targetHead
      himageHeadAnisotropic htargetHeadAnisotropic himageHeadValue
  let F' : (Fin (m + 1) → K) →ₗ[K] (Fin (n + 1) → K) :=
    g.toLinearEquiv.toLinearMap.comp F.toLinearMap
  have hF'head : F' sourceHead = targetHead := by
    change g.toLinearEquiv (F.toLinearMap sourceHead) = targetHead
    exact qt.equalValueTransportIsometry_apply_left
      (F.toLinearMap sourceHead) targetHead
        himageHeadAnisotropic htargetHeadAnisotropic himageHeadValue
  have hF'Bilin (x y : Fin (m + 1) → K) :
      qt.bilin (F' x) (F' y) = qs.bilin x y := by
    change qt.bilin (g.toLinearEquiv (F.toLinearMap x))
      (g.toLinearEquiv (F.toLinearMap y)) = qs.bilin x y
    calc
      _ = qt.bilin (F.toLinearMap x) (F.toLinearMap y) :=
        g.map_bilin (F.toLinearMap x) (F.toLinearMap y)
      _ = qs.bilin x y := F.map_bilin x y
  have hF'Injective : Function.Injective F' :=
    g.toLinearEquiv.injective.comp F.injective
  have hfirstZero (x : Fin m → K) :
      (F' (Fin.cons 0 x)) 0 = 0 := by
    have horthogonal :
        qt.bilin targetHead (F' (Fin.cons 0 x)) = 0 := by
      calc
        qt.bilin targetHead (F' (Fin.cons 0 x)) =
            qt.bilin (F' sourceHead) (F' (Fin.cons 0 x)) := by
          rw [hF'head]
        _ = qs.bilin sourceHead (Fin.cons 0 x) :=
          hF'Bilin sourceHead (Fin.cons 0 x)
        _ = 0 := by
          simp [qs, sourceHead, sourceFull,
            QuadraticSpace.finiteDiagonal_bilin_apply,
            Fin.sum_univ_succ]
    have hmul : head * (F' (Fin.cons 0 x)) 0 = 0 := by
      simpa [qt, targetHead, targetFull,
        QuadraticSpace.finiteDiagonal_bilin_apply,
        Fin.sum_univ_succ] using horthogonal
    exact (mul_eq_zero.mp hmul).resolve_left hhead
  let tailMap : (Fin m → K) →ₗ[K] (Fin n → K) :=
    { toFun := fun x i ↦ F' (Fin.cons 0 x) i.succ
      map_add' := by
        intro x y
        funext i
        have hcons : Fin.cons (0 : K) (x + y) =
            (Fin.cons 0 x : Fin (m + 1) → K) +
              (Fin.cons 0 y : Fin (m + 1) → K) := by
          funext j
          refine Fin.cases ?_ (fun k ↦ ?_) j <;> simp
        rw [hcons, map_add]
        rfl
      map_smul' := by
        intro c x
        funext i
        have hcons : Fin.cons (0 : K) (c • x) =
            c • (Fin.cons 0 x : Fin (m + 1) → K) := by
          funext j
          refine Fin.cases ?_ (fun k ↦ ?_) j <;> simp
        rw [hcons, map_smul]
        rfl }
  have htailMapInjective : Function.Injective tailMap := by
    intro x y hxy
    have hfull : F' (Fin.cons 0 x) = F' (Fin.cons 0 y) := by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · rw [hfirstZero x, hfirstZero y]
      · exact congrFun hxy j
    have hcons := hF'Injective hfull
    funext i
    exact congrFun hcons i.succ
  refine ⟨tailMap, htailMapInjective, ?_⟩
  intro x
  calc
    diagonalQuadratic target (tailMap x) =
        qt.quadratic (F' (Fin.cons 0 x)) := by
      rw [QuadraticSpace.finiteDiagonal_quadratic_apply]
      change diagonalQuadratic target (tailMap x) =
        diagonalQuadratic (Fin.cons head target) (F' (Fin.cons 0 x))
      conv_rhs => rw [← Fin.cons_self_tail (F' (Fin.cons 0 x))]
      rw [diagonalQuadratic_cons, hfirstZero]
      simp only [pow_two, zero_mul, mul_zero, zero_add]
      rfl
    _ = qs.quadratic (Fin.cons 0 x) :=
      hF'Bilin (Fin.cons 0 x) (Fin.cons 0 x)
    _ = diagonalQuadratic source x := by
      rw [QuadraticSpace.finiteDiagonal_quadratic_apply]
      change diagonalQuadratic (Fin.cons head source) (Fin.cons 0 x) =
        diagonalQuadratic source x
      rw [diagonalQuadratic_cons]
      simp

end DiagonalRepresents

open Dyadic

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type*} [AddCommGroup V] [Module K V]
  {W : Type*} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- A nonempty value prefix is its head followed by the corresponding value
prefix of the recursive tail. -/
theorem prefixValues_succ_eq_cons_head_tail
    (b : GoodBONG q L (n + 2)) (k : Nat) (hk : k ≤ n + 1) :
    b.prefixValues (k + 1) (by omega) =
      Fin.cons (b.value 0) (b.tail.prefixValues k hk) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · change b.toBONG.value ⟨j.val + 1, by omega⟩ =
      b.toBONG.tail.value ⟨j.val, by omega⟩
    symm
    exact b.toBONG.value_tail ⟨j.val, by omega⟩

/-- A representation between two nonempty prefixes with a common first
value descends to the corresponding projected-tail prefixes. -/
theorem tailPrefix_represents_of_common_head
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (sourceLength targetLength : Nat)
    (hsourceLength : sourceLength ≤ n + 1)
    (htargetLength : targetLength ≤ n + 1)
    (hrep : DiagonalRepresents
      (b.prefixValues (sourceLength + 1) (by omega))
      (a.prefixValues (targetLength + 1) (by omega))) :
    DiagonalRepresents
      (b.tail.prefixValues sourceLength hsourceLength)
      (a.tail.prefixValues targetLength htargetLength) := by
  rw [b.prefixValues_succ_eq_cons_head_tail sourceLength hsourceLength,
    a.prefixValues_succ_eq_cons_head_tail targetLength htargetLength,
    hhead] at hrep
  apply DiagonalRepresents.cancel_common_head
    (b.value 0)
    (b.tail.prefixValues sourceLength hsourceLength)
    (a.tail.prefixValues targetLength htargetLength)
  · exact b.toBONG.value_ne_zero 0
  · intro i
    change b.tail.toBONG.value
      ⟨i.val, i.isLt.trans_le hsourceLength⟩ ≠ 0
    exact b.tail.toBONG.value_ne_zero _
  · intro i
    change a.tail.toBONG.value
      ⟨i.val, i.isLt.trans_le htargetLength⟩ ≠ 0
    exact a.tail.toBONG.value_ne_zero _
  · exact hrep

end BONG.GoodBONG

end Bong
