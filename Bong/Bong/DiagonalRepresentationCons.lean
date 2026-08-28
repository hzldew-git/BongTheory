/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Classification

/-!
# Prepending a common diagonal coefficient

This is the left-handed companion to `diagonalRepresents_snoc`.  It is used
to extend the ternary diagonal isometries in Beli (2019), Lemma 9.2 by one or
two unchanged initial coefficients.
-/

namespace Bong

universe u

variable {K : Type u} [Field K]

/-- Orthogonally prepend the same one-dimensional coefficient to a diagonal
representation. -/
theorem diagonalRepresents_cons {m n : Nat}
    {source : Fin m → K} {target : Fin n → K}
    (h : DiagonalRepresents source target) (d : K) :
    DiagonalRepresents (Fin.cons d source) (Fin.cons d target) := by
  rcases h with ⟨f, hf, hquadratic⟩
  let F : (Fin (m + 1) → K) →ₗ[K] (Fin (n + 1) → K) :=
    { toFun := fun x => Fin.cons (x 0) (f (Fin.tail x))
      map_add' := by
        intro x y
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · simp only [Fin.cons_succ, Pi.add_apply]
          change f (Fin.tail (x + y)) j =
            f (Fin.tail x) j + f (Fin.tail y) j
          rw [show Fin.tail (x + y) = Fin.tail x + Fin.tail y by rfl,
            map_add]
          rfl
      map_smul' := by
        intro c x
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · simp only [Fin.cons_succ, Pi.smul_apply]
          change f (Fin.tail (c • x)) j = c * f (Fin.tail x) j
          rw [show Fin.tail (c • x) = c • Fin.tail x by rfl,
            map_smul]
          rfl }
  refine ⟨F, ?_, ?_⟩
  · intro x y hxy
    have hzero : x 0 = y 0 := by
      have h := congrFun hxy 0
      simpa [F] using h
    have htail : Fin.tail x = Fin.tail y := by
      apply hf
      funext i
      have h := congrFun hxy i.succ
      simpa [F] using h
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hzero
    · exact congrFun htail j
  · intro x
    unfold diagonalQuadratic
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [F, LinearMap.coe_mk, AddHom.coe_mk, Fin.cons_zero,
      Fin.cons_succ]
    change d * x 0 ^ 2 +
        ∑ i, target i * (f (Fin.tail x) i) ^ 2 =
      d * x 0 ^ 2 + ∑ i, source i * (Fin.tail x i) ^ 2
    have hq := hquadratic (Fin.tail x)
    unfold diagonalQuadratic at hq
    rw [hq]

/-- Orthogonally append a common diagonal block to a diagonal
representation.  This is the finite-block version of repeated use of
`diagonalRepresents_snoc`. -/
theorem diagonalRepresents_append {m n k : Nat}
    {source : Fin m → K} {target : Fin n → K}
    (h : DiagonalRepresents source target) (common : Fin k → K) :
    DiagonalRepresents (Fin.append source common)
      (Fin.append target common) := by
  rcases h with ⟨f, hf, hquadratic⟩
  let F : (Fin (m + k) → K) →ₗ[K] (Fin (n + k) → K) :=
    { toFun := fun x =>
        Fin.append
          (f (fun i => x (Fin.castAdd k i)))
          (fun j => x (Fin.natAdd m j))
      map_add' := by
        intro x y
        funext i
        refine Fin.addCases (m := n) (n := k)
          (fun j => ?_) (fun j => ?_) i
        · simp only [Fin.append_left, Pi.add_apply]
          change f (fun i => (x + y) (Fin.castAdd k i)) j = _
          rw [show (fun i => (x + y) (Fin.castAdd k i)) =
              (fun i => x (Fin.castAdd k i)) +
                (fun i => y (Fin.castAdd k i)) by rfl,
            map_add]
          rfl
        · simp only [Fin.append_right, Pi.add_apply]
      map_smul' := by
        intro c x
        funext i
        refine Fin.addCases (m := n) (n := k)
          (fun j => ?_) (fun j => ?_) i
        · simp only [Fin.append_left, Pi.smul_apply]
          change f (fun i => (c • x) (Fin.castAdd k i)) j = _
          rw [show (fun i => (c • x) (Fin.castAdd k i)) =
              c • (fun i => x (Fin.castAdd k i)) by rfl,
            map_smul]
          rfl
        · simp only [Fin.append_right, Pi.smul_apply]
          rfl }
  refine ⟨F, ?_, ?_⟩
  · intro x y hxy
    have hleft :
        (fun i => x (Fin.castAdd k i)) =
          (fun i => y (Fin.castAdd k i)) := by
      apply hf
      funext i
      have hi := congrFun hxy (Fin.castAdd k i)
      simpa [F] using hi
    have hright :
        (fun j => x (Fin.natAdd m j)) =
          (fun j => y (Fin.natAdd m j)) := by
      funext j
      have hj := congrFun hxy (Fin.natAdd n j)
      simpa [F] using hj
    funext i
    refine Fin.addCases (m := m) (n := k)
      (fun j => ?_) (fun j => ?_) i
    · exact congrFun hleft j
    · exact congrFun hright j
  · intro x
    unfold diagonalQuadratic
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, F,
      LinearMap.coe_mk, AddHom.coe_mk]
    have hq := hquadratic (fun i => x (Fin.castAdd k i))
    unfold diagonalQuadratic at hq
    rw [hq]

end Bong
