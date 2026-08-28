/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma715Prefix
import Bong.Bong.DiagonalSquareIsometry
import Bong.QuadraticSpace.HyperbolicPlane

/-!
# Finite diagonal towers of hyperbolic binary blocks

This file supplies the explicit linear algebra used in Beli (2019),
Lemma 7.19.  A binary diagonal form whose signed coefficient ratio is a
square is carried to the standard hyperbolic plane by an explicit coordinate
map.  Such maps can be joined blockwise, giving an isometry of arbitrary
even diagonal prefixes once every adjacent binary block is hyperbolic.
-/

namespace Bong

universe u v

namespace QuadraticSpace

variable {K : Type u} [Field K] [CharZero K]

/-- Explicit hyperbolic coordinates for the diagonal plane whose first
coefficient is `first` and whose signed ratio has square root `t`. -/
noncomputable def diagonalFinTwoToHyperbolicEquiv
    (first t : Kˣ) : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) where
  toFun x := ![(x 0 + x 1 / (t : K)) / 2,
    (first : K) * (x 0 - x 1 / (t : K))]
  invFun y := ![y 0 + y 1 / (2 * (first : K)),
    (t : K) * (y 0 - y 1 / (2 * (first : K)))]
  left_inv x := by
    funext i
    fin_cases i <;> simp [div_eq_mul_inv]
      <;> field_simp [Units.ne_zero first, Units.ne_zero t]
      <;> ring
  right_inv y := by
    funext i
    fin_cases i <;> simp [div_eq_mul_inv]
      <;> field_simp [Units.ne_zero first, Units.ne_zero t]
      <;> ring
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp <;> ring

/-- A binary finite diagonal space is hyperbolic when its signed coefficient
ratio is a square. -/
theorem finiteDiagonal_fin_two_isIsometric_hyperbolicPlane_one
    (first second : Kˣ)
    (hsquare : IsSquare (-(first / second))) :
    (finiteDiagonal ![(first : K), (second : K)] (by simp)).IsIsometric
      (hyperbolicPlane (1 : Kˣ)) := by
  rcases hsquare with ⟨t, ht⟩
  let e := diagonalFinTwoToHyperbolicEquiv first t
  refine ⟨{
    toLinearEquiv := e
    map_bilin := ?_ }⟩
  intro x y
  rw [hyperbolicPlane_bilin_apply, finiteDiagonal_bilin_apply]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Units.val_one, one_mul]
  change
    ((x 0 + x 1 / (t : K)) / 2) *
          ((first : K) * (y 0 - y 1 / (t : K))) +
        ((first : K) * (x 0 - x 1 / (t : K))) *
          ((y 0 + y 1 / (t : K)) / 2) =
      (first : K) * x 0 * y 0 + (second : K) * x 1 * y 1
  have htK : -((first : K) / (second : K)) = (t : K) ^ 2 := by
    simpa [pow_two] using congrArg Units.val ht
  have hsecond : (second : K) ≠ 0 := Units.ne_zero second
  have htMul : (t : K) ^ 2 * (second : K) = -(first : K) := by
    rw [← htK]
    field_simp [hsecond]
  field_simp [hsecond, Units.ne_zero first, Units.ne_zero t]
  linear_combination (-2 * x 1 * y 1) * htMul

end QuadraticSpace

namespace DiagonalRepresents

variable {K : Type u} [Field K]

/-- Orthogonally append two diagonal representations. -/
theorem appendBoth {m₁ n₁ m₂ n₂ : Nat}
    {source₁ : Fin m₁ → K} {target₁ : Fin n₁ → K}
    {source₂ : Fin m₂ → K} {target₂ : Fin n₂ → K}
    (h₁ : DiagonalRepresents source₁ target₁)
    (h₂ : DiagonalRepresents source₂ target₂) :
    DiagonalRepresents (Fin.append source₁ source₂)
      (Fin.append target₁ target₂) := by
  rcases h₁ with ⟨f, hf, hqf⟩
  rcases h₂ with ⟨g, hg, hqg⟩
  let F : (Fin (m₁ + m₂) → K) →ₗ[K] (Fin (n₁ + n₂) → K) :=
    { toFun := fun x => Fin.append
        (f (fun i => x (Fin.castAdd m₂ i)))
        (g (fun j => x (Fin.natAdd m₁ j)))
      map_add' := by
        intro x y
        funext i
        refine Fin.addCases (m := n₁) (n := n₂)
          (fun j => ?_) (fun j => ?_) i
        · simp only [Fin.append_left, Pi.add_apply]
          change f (fun i => (x + y) (Fin.castAdd m₂ i)) j = _
          rw [show (fun i => (x + y) (Fin.castAdd m₂ i)) =
              (fun i => x (Fin.castAdd m₂ i)) +
                (fun i => y (Fin.castAdd m₂ i)) by rfl, map_add]
          rfl
        · simp only [Fin.append_right, Pi.add_apply]
          change g (fun i => (x + y) (Fin.natAdd m₁ i)) j = _
          rw [show (fun i => (x + y) (Fin.natAdd m₁ i)) =
              (fun i => x (Fin.natAdd m₁ i)) +
                (fun i => y (Fin.natAdd m₁ i)) by rfl, map_add]
          rfl
      map_smul' := by
        intro c x
        funext i
        refine Fin.addCases (m := n₁) (n := n₂)
          (fun j => ?_) (fun j => ?_) i
        · simp only [Fin.append_left, Pi.smul_apply]
          change f (fun i => (c • x) (Fin.castAdd m₂ i)) j = _
          rw [show (fun i => (c • x) (Fin.castAdd m₂ i)) =
              c • (fun i => x (Fin.castAdd m₂ i)) by rfl, map_smul]
          rfl
        · simp only [Fin.append_right, Pi.smul_apply]
          change g (fun i => (c • x) (Fin.natAdd m₁ i)) j = _
          rw [show (fun i => (c • x) (Fin.natAdd m₁ i)) =
              c • (fun i => x (Fin.natAdd m₁ i)) by rfl, map_smul]
          rfl }
  refine ⟨F, ?_, ?_⟩
  · intro x y hxy
    have hleft : (fun i => x (Fin.castAdd m₂ i)) =
        (fun i => y (Fin.castAdd m₂ i)) := by
      apply hf
      funext i
      have hi := congrFun hxy (Fin.castAdd n₂ i)
      simpa [F] using hi
    have hright : (fun i => x (Fin.natAdd m₁ i)) =
        (fun i => y (Fin.natAdd m₁ i)) := by
      apply hg
      funext i
      have hi := congrFun hxy (Fin.natAdd n₁ i)
      simpa [F] using hi
    funext i
    refine Fin.addCases (m := m₁) (n := m₂)
      (fun j => ?_) (fun j => ?_) i
    · exact congrFun hleft j
    · exact congrFun hright j
  · intro x
    unfold diagonalQuadratic
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, F,
      LinearMap.coe_mk, AddHom.coe_mk]
    have hf' := hqf (fun i => x (Fin.castAdd m₂ i))
    have hg' := hqg (fun i => x (Fin.natAdd m₁ i))
    unfold diagonalQuadratic at hf' hg'
    rw [hf', hg']

end DiagonalRepresents

namespace QuadraticSpace

variable {K : Type u} [Field K] [CharZero K]

/-- Two hyperbolic binary diagonal forms represent one another. -/
theorem finiteDiagonal_fin_two_diagonalRepresents_of_signedRatioSquares
    (sourceFirst sourceSecond targetFirst targetSecond : Kˣ)
    (hsource : IsSquare (-(sourceFirst / sourceSecond)))
    (htarget : IsSquare (-(targetFirst / targetSecond))) :
    DiagonalRepresents
      ![(sourceFirst : K), (sourceSecond : K)]
      ![(targetFirst : K), (targetSecond : K)] := by
  rcases finiteDiagonal_fin_two_isIsometric_hyperbolicPlane_one
      sourceFirst sourceSecond hsource with ⟨fs⟩
  rcases finiteDiagonal_fin_two_isIsometric_hyperbolicPlane_one
      targetFirst targetSecond htarget with ⟨ft⟩
  let f := fs.trans ft.symm
  refine ⟨f.toLinearEquiv.toLinearMap, f.toLinearEquiv.injective, ?_⟩
  intro x
  change diagonalQuadratic
      ![(targetFirst : K), (targetSecond : K)] (f.toLinearEquiv x) =
    diagonalQuadratic ![(sourceFirst : K), (sourceSecond : K)] x
  simpa only [finiteDiagonal_quadratic_apply] using f.map_quadratic x

/-- A finite tower of binary diagonal blocks is represented by joining one
given representation for each adjacent pair. -/
theorem diagonalRepresents_even_of_pairRepresentations
    (m : Nat) (source target : Fin (2 * m) → Kˣ)
    (hpair : ∀ j : Fin m, DiagonalRepresents
      ![(source ⟨2 * j.val, by omega⟩ : K),
        (source ⟨2 * j.val + 1, by omega⟩ : K)]
      ![(target ⟨2 * j.val, by omega⟩ : K),
        (target ⟨2 * j.val + 1, by omega⟩ : K)]) :
    DiagonalRepresents (fun i => (source i : K))
      (fun i => (target i : K)) := by
  induction m with
  | zero => exact diagonalRepresents_refl _
  | succ m ih =>
      let sourceInit : Fin (2 * m) → Kˣ := fun i =>
        source ⟨i.val, by omega⟩
      let targetInit : Fin (2 * m) → Kˣ := fun i =>
        target ⟨i.val, by omega⟩
      let sourceLast : Fin 2 → Kˣ := fun i =>
        source ⟨2 * m + i.val, by omega⟩
      let targetLast : Fin 2 → Kˣ := fun i =>
        target ⟨2 * m + i.val, by omega⟩
      have hinit := ih sourceInit targetInit
        (fun j => by
          simpa [sourceInit, targetInit] using hpair ⟨j.val, by omega⟩)
      have hlast : DiagonalRepresents
          (fun i => (sourceLast i : K))
          (fun i => (targetLast i : K)) := by
        have hp := hpair ⟨m, by omega⟩
        convert hp using 1 <;> funext i <;> fin_cases i <;> rfl
      have happ := DiagonalRepresents.appendBoth hinit hlast
      have hsEq : Fin.append
          (fun i => (sourceInit i : K))
          (fun i => (sourceLast i : K)) =
          (fun i => (source i : K)) := by
        funext i
        refine Fin.addCases (m := 2 * m) (n := 2)
          (fun j => ?_) (fun j => ?_) i
        · simp only [Fin.append_left, sourceInit]
          congr 2
        · simp only [Fin.append_right, sourceLast]
          congr 2
      have htEq : Fin.append
          (fun i => (targetInit i : K))
          (fun i => (targetLast i : K)) =
          (fun i => (target i : K)) := by
        funext i
        refine Fin.addCases (m := 2 * m) (n := 2)
          (fun j => ?_) (fun j => ?_) i
        · simp only [Fin.append_left, targetInit]
          congr 2
        · simp only [Fin.append_right, targetLast]
          congr 2
      rw [hsEq, htEq] at happ
      exact happ

/-- A finite tower of binary diagonal blocks is represented blockwise when
the signed ratio of every source and target block is a square. -/
theorem diagonalRepresents_even_of_pair_signedRatioSquares
    (m : Nat) (source target : Fin (2 * m) → Kˣ)
    (hsource : ∀ j : Fin m,
      IsSquare (-(source ⟨2 * j.val, by omega⟩ /
        source ⟨2 * j.val + 1, by omega⟩)))
    (htarget : ∀ j : Fin m,
      IsSquare (-(target ⟨2 * j.val, by omega⟩ /
        target ⟨2 * j.val + 1, by omega⟩))) :
    DiagonalRepresents (fun i => (source i : K))
      (fun i => (target i : K)) := by
  apply diagonalRepresents_even_of_pairRepresentations m source target
  intro j
  exact finiteDiagonal_fin_two_diagonalRepresents_of_signedRatioSquares
    (source ⟨2 * j.val, by omega⟩)
    (source ⟨2 * j.val + 1, by omega⟩)
    (target ⟨2 * j.val, by omega⟩)
    (target ⟨2 * j.val + 1, by omega⟩)
    (hsource j) (htarget j)

end QuadraticSpace

namespace BONG.GoodBONG

open Dyadic

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The blockwise representation theorem specialized to good-BONG prefix
coefficients, with an arbitrary representation supplied for each pair. -/
theorem prefixDiagonalSpace_isIsometric_of_two_mul_pairRepresentations
    (a : GoodBONG q L n) (b : GoodBONG q M n)
    (m : Nat) (hk : 2 * m ≤ n)
    (hpair : ∀ j : Fin m, DiagonalRepresents
      ![(a.valueUnit ⟨2 * j.val, by omega⟩ : K),
        (a.valueUnit ⟨2 * j.val + 1, by omega⟩ : K)]
      ![(b.valueUnit ⟨2 * j.val, by omega⟩ : K),
        (b.valueUnit ⟨2 * j.val + 1, by omega⟩ : K)]) :
    (a.prefixDiagonalSpace (2 * m) hk).IsIsometric
      (b.prefixDiagonalSpace (2 * m) hk) := by
  let source : Fin (2 * m) → Kˣ := fun i =>
    a.valueUnit ⟨i.val, i.isLt.trans_le hk⟩
  let target : Fin (2 * m) → Kˣ := fun i =>
    b.valueUnit ⟨i.val, i.isLt.trans_le hk⟩
  have hrep := QuadraticSpace.diagonalRepresents_even_of_pairRepresentations
    m source target (fun j => by
      simpa only [source, target] using hpair j)
  have hrepPrefix : DiagonalRepresents
      (a.prefixValues (2 * m) hk) (b.prefixValues (2 * m) hk) := by
    convert hrep using 1 <;> funext i
    · exact (a.toBONG.coe_valueUnit ⟨i.val, i.isLt.trans_le hk⟩).symm
    · exact (b.toBONG.coe_valueUnit ⟨i.val, i.isLt.trans_le hk⟩).symm
  have hsne : ∀ i, a.prefixValues (2 * m) hk i ≠ 0 := by
    intro i
    exact a.toBONG.value_ne_zero ⟨i.val, i.isLt.trans_le hk⟩
  have htne : ∀ i, b.prefixValues (2 * m) hk i ≠ 0 := by
    intro i
    exact b.toBONG.value_ne_zero ⟨i.val, i.isLt.trans_le hk⟩
  rcases DiagonalRepresents.toQuadraticSpaceRepresents
      hsne htne hrepPrefix with ⟨f⟩
  have hisometry :
      (QuadraticSpace.finiteDiagonal
        (a.prefixValues (2 * m) hk) hsne).IsIsometric
        (QuadraticSpace.finiteDiagonal
          (b.prefixValues (2 * m) hk) htne) :=
    ⟨f.toIsometryOfFinrankEq rfl⟩
  simpa only [prefixDiagonalSpace] using hisometry

/-- The blockwise theorem specialized to the diagonal prefixes attached to
two good BONGs. -/
theorem prefixDiagonalSpace_isIsometric_of_two_mul_pair_signedRatioSquares
    (a : GoodBONG q L n) (b : GoodBONG q M n)
    (m : Nat) (hk : 2 * m ≤ n)
    (hsource : ∀ j : Fin m,
      IsSquare (-(a.valueUnit ⟨2 * j.val, by omega⟩ /
        a.valueUnit ⟨2 * j.val + 1, by omega⟩)))
    (htarget : ∀ j : Fin m,
      IsSquare (-(b.valueUnit ⟨2 * j.val, by omega⟩ /
        b.valueUnit ⟨2 * j.val + 1, by omega⟩))) :
    (a.prefixDiagonalSpace (2 * m) hk).IsIsometric
      (b.prefixDiagonalSpace (2 * m) hk) := by
  let source : Fin (2 * m) → Kˣ := fun i =>
    a.valueUnit ⟨i.val, i.isLt.trans_le hk⟩
  let target : Fin (2 * m) → Kˣ := fun i =>
    b.valueUnit ⟨i.val, i.isLt.trans_le hk⟩
  have hrep := QuadraticSpace.diagonalRepresents_even_of_pair_signedRatioSquares
    m source target
      (fun j => by simpa only [source] using hsource j)
      (fun j => by simpa only [target] using htarget j)
  have hrepPrefix : DiagonalRepresents
      (a.prefixValues (2 * m) hk) (b.prefixValues (2 * m) hk) := by
    convert hrep using 1 <;> funext i
    · exact (a.toBONG.coe_valueUnit ⟨i.val, i.isLt.trans_le hk⟩).symm
    · exact (b.toBONG.coe_valueUnit ⟨i.val, i.isLt.trans_le hk⟩).symm
  have hsne : ∀ i, a.prefixValues (2 * m) hk i ≠ 0 := by
    intro i
    exact a.toBONG.value_ne_zero ⟨i.val, i.isLt.trans_le hk⟩
  have htne : ∀ i, b.prefixValues (2 * m) hk i ≠ 0 := by
    intro i
    exact b.toBONG.value_ne_zero ⟨i.val, i.isLt.trans_le hk⟩
  rcases DiagonalRepresents.toQuadraticSpaceRepresents
      hsne htne hrepPrefix with ⟨f⟩
  have hisometry :
      (QuadraticSpace.finiteDiagonal
        (a.prefixValues (2 * m) hk) hsne).IsIsometric
        (QuadraticSpace.finiteDiagonal
          (b.prefixValues (2 * m) hk) htne) :=
    ⟨f.toIsometryOfFinrankEq rfl⟩
  simpa only [prefixDiagonalSpace] using hisometry

end BONG.GoodBONG

end Bong
