/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalRepresentationDeterminant
import Bong.Bong.DiagonalBinaryRepresentation
import Bong.Bong.DiagonalRepresentationCons
import Bong.Bong.DiagonalHeadCancellation
import Bong.Dyadic.HilbertSymbolProof

/-!
# Isometry invariance of diagonal determinant and Hasse symbols

This file proves the standard equal-rank invariance laws used by Beli's
classification and representation arguments.  The proof follows the content
of O'Meara 58:1--58:2 in a recursion convenient for Lean:

* a represented nonzero line is split from a diagonal form by successive
  binary changes of variables;
* binary Hasse invariance is proved from the Hilbert-symbol norm criterion;
* the complementary diagonal form is handled by induction on the rank.

Consequently `DiagonalIsometryInvariantLaws K` is no longer an external local
law for dyadic local fields.
-/

namespace Bong

open Dyadic BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

private theorem diagonalHasseSymbol_one (a : Fin 1 → Kˣ) :
    diagonalHasseSymbol K a = hilbertSymbol K (a 0) (a 0) := by
  rw [show a = Fin.snoc (fun _ : Fin 0 => (1 : Kˣ)) (a 0) by
    funext i
    exact Fin.eq_zero i ▸ rfl]
  simp [diagonalUnitDeterminant]
  rfl

private theorem diagonalHasseSymbol_two (a : Fin 2 → Kˣ) :
    diagonalHasseSymbol K a =
      hilbertSymbol K (a 0) (a 0) *
        hilbertSymbol K (a 0) (a 1) *
          hilbertSymbol K (a 1) (a 1) := by
  rw [show a = Fin.snoc (Fin.snoc (fun _ : Fin 0 => (1 : Kˣ)) (a 0)) (a 1) by
    funext i
    fin_cases i <;> rfl]
  simp [diagonalUnitDeterminant]
  rfl

private theorem diagonalUnitDeterminant_square_of_represents
    {n : Nat} (a b : Fin n → Kˣ)
    (hrep : DiagonalRepresents (diagonalUnitCoefficients a)
      (diagonalUnitCoefficients b)) :
    IsSquare (diagonalUnitDeterminant a * diagonalUnitDeterminant b) := by
  rcases DiagonalRepresents.exists_prod_eq_mul_square_of_sameRank hrep with ⟨p, hp⟩
  have hpUnits : diagonalUnitDeterminant a =
      diagonalUnitDeterminant b * p ^ 2 := by
    apply Units.ext
    simp only [diagonalUnitDeterminant, Units.val_mul, Units.val_pow_eq_pow_val]
    change (Units.coeHom K (∏ i, a i)) =
      Units.coeHom K (∏ i, b i) * (p : K) ^ 2
    rw [map_prod (Units.coeHom K) a Finset.univ,
      map_prod (Units.coeHom K) b Finset.univ]
    change (∏ i, (a i : K)) = (∏ i, (b i : K)) * (p : K) ^ 2 at hp
    exact hp
  refine ⟨diagonalUnitDeterminant b * p, ?_⟩
  rw [hpUnits]
  simp only [pow_two]
  ac_rfl

private noncomputable def unaryScalingLinearMap (x : K) :
    (Fin 1 → K) →ₗ[K] (Fin 1 → K) where
  toFun z := fun _ => x * z 0
  map_add' z w := by
    funext i
    simp only [Pi.add_apply]
    rw [mul_add]
  map_smul' c z := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ac_rfl

private theorem unaryScalingLinearMap_injective
    {x : K} (hx : x ≠ 0) :
    Function.Injective (unaryScalingLinearMap (K := K) x) := by
  intro z w hzw
  funext i
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  have hzero := congrFun hzw (0 : Fin 1)
  exact mul_left_cancel₀ hx hzero

private theorem unary_diagonalRepresents_of_eq_mul_sq
    (A B : Kˣ) (x : K)
    (hvalue : (B : K) * x ^ 2 = (A : K)) :
    DiagonalRepresents (fun _ : Fin 1 => (A : K))
      (fun _ : Fin 1 => (B : K)) := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx] at hvalue
    simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] at hvalue
    exact Units.ne_zero A hvalue.symm
  refine ⟨unaryScalingLinearMap (K := K) x,
    unaryScalingLinearMap_injective hx, ?_⟩
  intro z
  simp only [diagonalQuadratic, Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero]
  change (B : K) * (x * z 0) ^ 2 = (A : K) * z 0 ^ 2
  rw [← hvalue]
  ring

private theorem diagonalHasseSymbol_unary_eq_of_square
    (A B : Kˣ) (hdet : IsSquare (A * B)) :
    diagonalHasseSymbol K (fun _ : Fin 1 => A) =
      diagonalHasseSymbol K (fun _ : Fin 1 => B) := by
  rw [diagonalHasseSymbol_one, diagonalHasseSymbol_one,
    hilbertSymbol_self_eq_neg_one, hilbertSymbol_self_eq_neg_one]
  exact hilbertSymbol_eq_of_isSquare_mul_left hdet

private noncomputable def binaryHasseCore (a b : Kˣ) : ℤˣ :=
  hilbertSymbol K a a * hilbertSymbol K a b * hilbertSymbol K b b

private theorem binaryHasseCore_eq (a b : Kˣ) :
    binaryHasseCore (K := K) a b =
      hilbertSymbol K (a * b) (-1) * hilbertSymbol K a b := by
  unfold binaryHasseCore
  rw [hilbertSymbol_self_eq_neg_one, hilbertSymbol_self_eq_neg_one,
    hilbertSymbol_mul_left]
  ac_rfl

private theorem binary_cross_hilbert_eq
    (A D B C : Kˣ)
    (hnorm : hilbertSymbol K (A * B⁻¹) (-(B * C)) = 1)
    (hdet : IsSquare ((A * D) * (B * C))) :
    hilbertSymbol K A D = hilbertSymbol K B C := by
  have hclass : IsSquare (D * (A * B * C)) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hdet
  have hreplace : hilbertSymbol K A D =
      hilbertSymbol K A (A * B * C) :=
    hilbertSymbol_eq_of_isSquare_mul_right hclass
  have hnormEq : hilbertSymbol K A (-(B * C)) =
      hilbertSymbol K B⁻¹ (-(B * C)) :=
    hilbertSymbol_eq_of_mul_left_eq_one A B⁻¹ (-(B * C)) hnorm
  have hinvSquare : IsSquare (B⁻¹ * B) := ⟨1, by simp⟩
  have hinvEq : hilbertSymbol K B⁻¹ (-(B * C)) =
      hilbertSymbol K B (-(B * C)) :=
    hilbertSymbol_eq_of_isSquare_mul_left hinvSquare
  calc
    hilbertSymbol K A D = hilbertSymbol K A (A * B * C) := hreplace
    _ = hilbertSymbol K A A * hilbertSymbol K A B *
        hilbertSymbol K A C := by
      rw [hilbertSymbol_mul_right, hilbertSymbol_mul_right]
    _ = hilbertSymbol K A (-(B * C)) := by
      rw [hilbertSymbol_self_eq_neg_one]
      rw [show (-(B * C)) = (-1 : Kˣ) * B * C by simp]
      rw [hilbertSymbol_mul_right, hilbertSymbol_mul_right]
    _ = hilbertSymbol K B⁻¹ (-(B * C)) := hnormEq
    _ = hilbertSymbol K B (-(B * C)) := hinvEq
    _ = hilbertSymbol K B C := by
      rw [show (-(B * C)) = (-B) * C by simp,
        hilbertSymbol_mul_right, hilbertSymbol_self_neg_eq_one]
      simp

private theorem binaryHasseCore_eq_of_norm_and_det
    (A D B C : Kˣ)
    (hnorm : hilbertSymbol K (A * B⁻¹) (-(B * C)) = 1)
    (hdet : IsSquare ((A * D) * (B * C))) :
    binaryHasseCore (K := K) A D = binaryHasseCore (K := K) B C := by
  rw [binaryHasseCore_eq, binaryHasseCore_eq]
  have hdetHilbert : hilbertSymbol K (A * D) (-1) =
      hilbertSymbol K (B * C) (-1) :=
    hilbertSymbol_eq_of_isSquare_mul_left hdet
  rw [hdetHilbert, binary_cross_hilbert_eq A D B C hnorm hdet]

private theorem diagonalUnitDeterminant_append
    {m n : Nat} (a : Fin m → Kˣ) (b : Fin n → Kˣ) :
    diagonalUnitDeterminant (Fin.append a b) =
      diagonalUnitDeterminant a * diagonalUnitDeterminant b := by
  unfold diagonalUnitDeterminant
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

private theorem diagonalHasseSymbol_append
    {m n : Nat} (a : Fin m → Kˣ) (b : Fin n → Kˣ) :
    diagonalHasseSymbol K (Fin.append a b) =
      diagonalHasseSymbol K a *
        hilbertSymbol K (diagonalUnitDeterminant a)
          (diagonalUnitDeterminant b) *
        diagonalHasseSymbol K b := by
  induction n with
  | zero =>
      have happ : Fin.append a b = a := by
        funext i
        simpa using Fin.append_left a b i
      rw [happ]
      simp [diagonalUnitDeterminant]
  | succ n ih =>
      let b₀ : Fin n → Kˣ := Fin.init b
      let d : Kˣ := b (Fin.last n)
      have hb : b = Fin.snoc b₀ d := by
        exact (Fin.snoc_init_self b).symm
      rw [hb]
      rw [Fin.append_snoc, diagonalHasseSymbol_snoc,
        diagonalHasseSymbol_snoc, ih]
      rw [diagonalUnitDeterminant_append,
        diagonalUnitDeterminant_snoc,
        hilbertSymbol_mul_left, hilbertSymbol_mul_right]
      ac_rfl

private theorem diagonalHasseSymbol_append_right_eq
    {m n : Nat} (a₁ a₂ : Fin m → Kˣ) (b : Fin n → Kˣ)
    (hhasse : diagonalHasseSymbol K a₁ = diagonalHasseSymbol K a₂)
    (hdet : IsSquare
      (diagonalUnitDeterminant a₁ * diagonalUnitDeterminant a₂)) :
    diagonalHasseSymbol K (Fin.append a₁ b) =
      diagonalHasseSymbol K (Fin.append a₂ b) := by
  rw [diagonalHasseSymbol_append, diagonalHasseSymbol_append, hhasse]
  rw [hilbertSymbol_eq_of_isSquare_mul_left hdet]

private theorem diagonalHasseSymbol_append_left_eq
    {m n : Nat} (a : Fin m → Kˣ) (b₁ b₂ : Fin n → Kˣ)
    (hhasse : diagonalHasseSymbol K b₁ = diagonalHasseSymbol K b₂)
    (hdet : IsSquare
      (diagonalUnitDeterminant b₁ * diagonalUnitDeterminant b₂)) :
    diagonalHasseSymbol K (Fin.append a b₁) =
      diagonalHasseSymbol K (Fin.append a b₂) := by
  rw [diagonalHasseSymbol_append, diagonalHasseSymbol_append, hhasse]
  rw [hilbertSymbol_eq_of_isSquare_mul_right hdet]

private noncomputable def hasseFoldStep
    (state : Kˣ × ℤˣ) (d : Kˣ) : Kˣ × ℤˣ :=
  (state.1 * d,
    state.2 * hilbertSymbol K state.1 d * hilbertSymbol K d d)

private theorem hasseFoldStep_rightCommutative :
    RightCommutative (hasseFoldStep (K := K)) := by
  constructor
  rintro ⟨D, S⟩ x y
  apply Prod.ext
  · simp only [hasseFoldStep]
    ac_rfl
  · simp only [hasseFoldStep]
    rw [hilbertSymbol_mul_left, hilbertSymbol_mul_left,
      hilbertSymbol_comm K x y]
    ac_rfl

private theorem hasseFold_ofFn {n : Nat} (a : Fin n → Kˣ) :
    List.foldl (hasseFoldStep (K := K)) (1, 1) (List.ofFn a) =
      (diagonalUnitDeterminant a, diagonalHasseSymbol K a) := by
  induction n with
  | zero =>
      have ha : a = fun _ : Fin 0 => (1 : Kˣ) := Subsingleton.elim _ _
      subst a
      simp [hasseFoldStep, diagonalUnitDeterminant]
  | succ n ih =>
      let a₀ : Fin n → Kˣ := Fin.init a
      let d : Kˣ := a (Fin.last n)
      have ha : a = Fin.snoc a₀ d := (Fin.snoc_init_self a).symm
      rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, hasseFoldStep]
      rw [ha, diagonalUnitDeterminant_snoc, diagonalHasseSymbol_snoc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]

private theorem hasseFold_eq_of_perm {l₁ l₂ : List Kˣ}
    (hperm : l₁.Perm l₂) :
    List.foldl (hasseFoldStep (K := K)) (1, 1) l₁ =
      List.foldl (hasseFoldStep (K := K)) (1, 1) l₂ := by
  letI : RightCommutative (hasseFoldStep (K := K)) :=
    hasseFoldStep_rightCommutative (K := K)
  exact hperm.foldl_eq (1, 1)

private theorem diagonalHasseSymbol_reindex
    {n : Nat} (a : Fin n → Kˣ) (e : Fin n ≃ Fin n) :
    diagonalHasseSymbol K (a ∘ e) = diagonalHasseSymbol K a := by
  have hperm : (List.ofFn (a ∘ e)).Perm (List.ofFn a) :=
    Equiv.Perm.ofFn_comp_perm e a
  have hfold := hasseFold_eq_of_perm (K := K) hperm
  rw [hasseFold_ofFn, hasseFold_ofFn] at hfold
  exact congrArg Prod.snd hfold

/-- Orthogonal-sum formula when a diagonal line is prepended. -/
theorem diagonalHasseSymbol_cons {n : Nat}
    (d : Kˣ) (a : Fin n → Kˣ) :
    diagonalHasseSymbol K (Fin.cons d a) =
      diagonalHasseSymbol K a *
        hilbertSymbol K (diagonalUnitDeterminant a) d *
        hilbertSymbol K d d := by
  have hreindex := diagonalHasseSymbol_reindex (K := K)
    (Fin.cons d a) (finRotate (n + 1))
  have hcoefficients :
      (Fin.cons d a) ∘ finRotate (n + 1) = Fin.snoc a d := by
    exact (Fin.snoc_eq_cons_rotate a d).symm
  rw [hcoefficients] at hreindex
  rw [← hreindex, diagonalHasseSymbol_snoc]

private theorem diagonalHasseSymbol_cons_head_eq
    {n : Nat} (A B : Kˣ) (c : Fin n → Kˣ)
    (hdet : IsSquare (A * B)) :
    diagonalHasseSymbol K (Fin.cons A c) =
      diagonalHasseSymbol K (Fin.cons B c) := by
  rw [diagonalHasseSymbol_cons, diagonalHasseSymbol_cons]
  rw [hilbertSymbol_eq_of_isSquare_mul_right hdet]
  rw [hilbertSymbol_self_eq_neg_one, hilbertSymbol_self_eq_neg_one,
    hilbertSymbol_eq_of_isSquare_mul_left hdet]

/-- Equal Hasse symbols and determinant square classes of two tails remain
equal after adjoining a common first line. -/
theorem diagonalHasseSymbol_cons_tail_eq
    {n : Nat} (A : Kˣ) (c₁ c₂ : Fin n → Kˣ)
    (hhasse : diagonalHasseSymbol K c₁ = diagonalHasseSymbol K c₂)
    (hdet : IsSquare
      (diagonalUnitDeterminant c₁ * diagonalUnitDeterminant c₂)) :
    diagonalHasseSymbol K (Fin.cons A c₁) =
      diagonalHasseSymbol K (Fin.cons A c₂) := by
  rw [diagonalHasseSymbol_cons, diagonalHasseSymbol_cons, hhasse]
  rw [hilbertSymbol_eq_of_isSquare_mul_left hdet]

private noncomputable def consScalingLinearMap (n : Nat) (x : K) :
    (Fin (n + 1) → K) →ₗ[K] (Fin (n + 1) → K) where
  toFun z := Fin.cons (x * z 0) (Fin.tail z)
  map_add' z w := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [mul_add]
    · rfl
  map_smul' c z := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      ac_rfl
    · rfl

private theorem consScalingLinearMap_injective (n : Nat)
    {x : K} (hx : x ≠ 0) :
    Function.Injective (consScalingLinearMap (K := K) n x) := by
  intro z w hzw
  have hhead : z 0 = w 0 := by
    have h := congrFun hzw 0
    exact mul_left_cancel₀ hx h
  have htail : Fin.tail z = Fin.tail w := by
    funext i
    have h := congrFun hzw i.succ
    exact h
  rw [← Fin.cons_self_tail z, ← Fin.cons_self_tail w, hhead, htail]

private theorem diagonalRepresents_cons_scaling
    {n : Nat} (A B : Kˣ) (c : Fin n → Kˣ) (x : K)
    (hvalue : (B : K) * x ^ 2 = (A : K)) :
    DiagonalRepresents
      (diagonalUnitCoefficients (Fin.cons A c))
      (diagonalUnitCoefficients (Fin.cons B c)) := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx] at hvalue
    simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] at hvalue
    exact Units.ne_zero A hvalue.symm
  refine ⟨consScalingLinearMap (K := K) n x,
    consScalingLinearMap_injective n hx, ?_⟩
  intro z
  simp only [diagonalUnitCoefficients_cons]
  change diagonalQuadratic
      (Fin.cons (B : K) (diagonalUnitCoefficients c))
        (Fin.cons (x * z 0) (Fin.tail z)) = _
  conv_rhs => rw [← Fin.cons_self_tail z]
  rw [DiagonalRepresents.diagonalQuadratic_cons,
    DiagonalRepresents.diagonalQuadratic_cons]
  change (B : K) * (x * z 0) ^ 2 +
      diagonalQuadratic (diagonalUnitCoefficients c) (Fin.tail z) =
    (A : K) * z 0 ^ 2 +
      diagonalQuadratic (diagonalUnitCoefficients c) (Fin.tail z)
  rw [← hvalue]
  ring

private noncomputable def firstTwoLinearMap (n : Nat) :
    (Fin (n + 2) → K) →ₗ[K] (Fin 2 → K) where
  toFun z i := z ⟨i.val, by omega⟩
  map_add' z w := by rfl
  map_smul' c z := by rfl

private noncomputable def tailTwoLinearMap (n : Nat) :
    (Fin (n + 2) → K) →ₗ[K] (Fin n → K) where
  toFun z i := z ⟨i.val + 2, by omega⟩
  map_add' z w := by rfl
  map_smul' c z := by rfl

private noncomputable def binaryTailLinearMap {n : Nat}
    (f : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) :
    (Fin (n + 2) → K) →ₗ[K] (Fin (n + 2) → K) where
  toFun z :=
    Fin.cons (f (firstTwoLinearMap (K := K) n z) 0)
      (Fin.cons (f (firstTwoLinearMap (K := K) n z) 1)
        (tailTwoLinearMap (K := K) n z))
  map_add' z w := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      rw [show firstTwoLinearMap (K := K) n (z + w) =
          firstTwoLinearMap (K := K) n z +
            firstTwoLinearMap (K := K) n w by rfl,
        map_add]
      rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp only [Fin.cons_succ, Fin.cons_zero]
        rw [show firstTwoLinearMap (K := K) n (z + w) =
            firstTwoLinearMap (K := K) n z +
              firstTwoLinearMap (K := K) n w by rfl,
          map_add]
        rfl
      · rfl
  map_smul' c z := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Pi.smul_apply]
      rw [show firstTwoLinearMap (K := K) n (c • z) =
          c • firstTwoLinearMap (K := K) n z by rfl,
        map_smul]
      rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp only [Fin.cons_succ, Fin.cons_zero, Pi.smul_apply]
        rw [show firstTwoLinearMap (K := K) n (c • z) =
            c • firstTwoLinearMap (K := K) n z by rfl,
          map_smul]
        rfl
      · rfl

private theorem binaryTailLinearMap_injective {n : Nat}
    {f : (Fin 2 → K) →ₗ[K] (Fin 2 → K)}
    (hf : Function.Injective f) :
    Function.Injective (binaryTailLinearMap (n := n) f) := by
  intro z w hzw
  have hfirst : firstTwoLinearMap (K := K) n z =
      firstTwoLinearMap (K := K) n w := by
    apply hf
    funext i
    fin_cases i
    · exact congrFun hzw 0
    · exact congrFun hzw 1
  have htail : tailTwoLinearMap (K := K) n z =
      tailTwoLinearMap (K := K) n w := by
    funext i
    have h := congrFun hzw i.succ.succ
    exact h
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact congrFun hfirst 0
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact congrFun hfirst 1
    · exact congrFun htail k

private theorem diagonalRepresents_binary_with_tail
    {n : Nat} (A D B P : Kˣ) (c : Fin n → Kˣ)
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.cons A (fun _ : Fin 1 => D)))
      (diagonalUnitCoefficients (Fin.cons B (fun _ : Fin 1 => P)))) :
    DiagonalRepresents
      (diagonalUnitCoefficients (Fin.cons A (Fin.cons D c)))
      (diagonalUnitCoefficients (Fin.cons B (Fin.cons P c))) := by
  rcases hrep with ⟨f, hf, hquadratic⟩
  refine ⟨binaryTailLinearMap (n := n) f,
    binaryTailLinearMap_injective hf, ?_⟩
  intro z
  have hq := hquadratic (firstTwoLinearMap (K := K) n z)
  simp only [diagonalUnitCoefficients_cons] at hq ⊢
  conv_lhs at hq =>
    rw [← Fin.cons_self_tail
      (f (firstTwoLinearMap (K := K) n z))]
  conv_rhs at hq =>
    rw [← Fin.cons_self_tail
      (firstTwoLinearMap (K := K) n z)]
  rw [DiagonalRepresents.diagonalQuadratic_cons,
    DiagonalRepresents.diagonalQuadratic_cons] at hq
  simp only [diagonalQuadratic, Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero] at hq
  change diagonalQuadratic
      (Fin.cons (B : K) (Fin.cons (P : K)
        (diagonalUnitCoefficients c)))
      (Fin.cons (f (firstTwoLinearMap (K := K) n z) 0)
        (Fin.cons (f (firstTwoLinearMap (K := K) n z) 1)
          (tailTwoLinearMap (K := K) n z))) = _
  unfold diagonalQuadratic
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  change (B : K) * (f (firstTwoLinearMap (K := K) n z) 0) ^ 2 +
      ((P : K) * (f (firstTwoLinearMap (K := K) n z) 1) ^ 2 +
        ∑ i, (c i : K) * (tailTwoLinearMap (K := K) n z i) ^ 2) =
    (A : K) * z 0 ^ 2 +
      ((D : K) * z 1 ^ 2 +
        ∑ i, (c i : K) * (tailTwoLinearMap (K := K) n z i) ^ 2)
  change (B : K) * (f (firstTwoLinearMap (K := K) n z) 0) ^ 2 +
      (P : K) * (f (firstTwoLinearMap (K := K) n z) 1) ^ 2 =
    (A : K) * z 0 ^ 2 + (D : K) * z 1 ^ 2 at hq
  linear_combination hq

private theorem diagonalHasseSymbol_binary_eq_of_represents
    (a b : Fin 2 → Kˣ)
    (hrep : DiagonalRepresents (diagonalUnitCoefficients a)
      (diagonalUnitCoefficients b)) :
    diagonalHasseSymbol K a = diagonalHasseSymbol K b := by
  let A := a (0 : Fin 2)
  let D := a (1 : Fin 2)
  let B := b (0 : Fin 2)
  let C := b (1 : Fin 2)
  have hprefix : DiagonalRepresents (fun _ : Fin 1 => (A : K))
      (diagonalUnitCoefficients a) := by
    convert DiagonalRepresents.prefixSucc (diagonalUnitCoefficients a) using 1
    funext i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    rfl
  have hfirst : DiagonalRepresents (fun _ : Fin 1 => (A : K))
      (Fin.cons (B : K) (fun _ : Fin 1 => (C : K))) := by
    have h := hprefix.trans hrep
    convert h using 1
    funext i
    fin_cases i <;> rfl
  have hnorm : hilbertSymbol K (A * B⁻¹) (-(B * C)) = 1 :=
    (DiagonalRepresents.unary_binary_iff_hilbertSymbol_one B C A).mp hfirst
  have hdet : IsSquare ((A * D) * (B * C)) := by
    have h := (show IsSquare
        (diagonalUnitDeterminant a * diagonalUnitDeterminant b) by
      rcases DiagonalRepresents.exists_prod_eq_mul_square_of_sameRank hrep with ⟨p, hp⟩
      have hpUnits : diagonalUnitDeterminant a =
          diagonalUnitDeterminant b * p ^ 2 := by
        apply Units.ext
        simp only [diagonalUnitDeterminant, Units.val_mul, Units.val_pow_eq_pow_val]
        change (Units.coeHom K (∏ i, a i)) =
          Units.coeHom K (∏ i, b i) * (p : K) ^ 2
        rw [map_prod (Units.coeHom K) a Finset.univ,
          map_prod (Units.coeHom K) b Finset.univ]
        change (∏ i, (a i : K)) = (∏ i, (b i : K)) * (p : K) ^ 2 at hp
        exact hp
      refine ⟨diagonalUnitDeterminant b * p, ?_⟩
      rw [hpUnits]
      simp only [pow_two]
      ac_rfl)
    simpa [A, D, B, C, diagonalUnitDeterminant, Fin.prod_univ_two] using h
  rw [show diagonalHasseSymbol K a = binaryHasseCore (K := K) A D by
    simpa [binaryHasseCore, A, D] using (show diagonalHasseSymbol K a =
      hilbertSymbol K (a 0) (a 0) * hilbertSymbol K (a 0) (a 1) *
        hilbertSymbol K (a 1) (a 1) by
      rw [show a = Fin.snoc (Fin.snoc (fun _ : Fin 0 => (1 : Kˣ)) (a 0)) (a 1) by
        funext i
        fin_cases i <;> rfl]
      simp [diagonalUnitDeterminant]
      rfl)]
  rw [show diagonalHasseSymbol K b = binaryHasseCore (K := K) B C by
    simpa [binaryHasseCore, B, C] using (show diagonalHasseSymbol K b =
      hilbertSymbol K (b 0) (b 0) * hilbertSymbol K (b 0) (b 1) *
        hilbertSymbol K (b 1) (b 1) by
      rw [show b = Fin.snoc (Fin.snoc (fun _ : Fin 0 => (1 : Kˣ)) (b 0)) (b 1) by
        funext i
        fin_cases i <;> rfl]
      simp [diagonalUnitDeterminant]
      rfl)]
  exact binaryHasseCore_eq_of_norm_and_det A D B C hnorm hdet

private theorem diagonalHasseSymbol_cons_cons
    {n : Nat} (A D : Kˣ) (c : Fin n → Kˣ) :
    diagonalHasseSymbol K (Fin.cons A (Fin.cons D c)) =
      binaryHasseCore (K := K) A D *
        hilbertSymbol K (A * D) (diagonalUnitDeterminant c) *
        diagonalHasseSymbol K c := by
  rw [diagonalHasseSymbol_cons, diagonalHasseSymbol_cons,
    diagonalUnitDeterminant_cons]
  simp only [hilbertSymbol_mul_left]
  rw [hilbertSymbol_comm K (diagonalUnitDeterminant c) D,
    hilbertSymbol_comm K (diagonalUnitDeterminant c) A,
    hilbertSymbol_comm K D A]
  unfold binaryHasseCore
  ac_rfl

private theorem diagonalHasseSymbol_binary_with_tail_eq
    {n : Nat} (A D B P : Kˣ) (c : Fin n → Kˣ)
    (hhasse : binaryHasseCore (K := K) A D =
      binaryHasseCore (K := K) B P)
    (hdet : IsSquare ((A * D) * (B * P))) :
    diagonalHasseSymbol K (Fin.cons A (Fin.cons D c)) =
      diagonalHasseSymbol K (Fin.cons B (Fin.cons P c)) := by
  rw [diagonalHasseSymbol_cons_cons, diagonalHasseSymbol_cons_cons,
    hhasse]
  rw [hilbertSymbol_eq_of_isSquare_mul_left hdet]

/-- Split a represented nonzero line from a nondegenerate diagonal form.
The returned tail is diagonal, the resulting full coefficient list is
isometric to the original one, and its Hasse symbol is unchanged.  This is
the explicit diagonal form of O'Meara 58:1--58:2. -/
theorem exists_diagonal_split_first
    (n : Nat) (b : Fin (n + 1) → Kˣ) (A : Kˣ)
    (x : Fin (n + 1) → K)
    (hvalue : diagonalQuadratic (diagonalUnitCoefficients b) x = (A : K)) :
    ∃ c : Fin n → Kˣ,
      DiagonalRepresents
          (diagonalUnitCoefficients (Fin.cons A c))
          (diagonalUnitCoefficients b) ∧
        diagonalHasseSymbol K (Fin.cons A c) =
          diagonalHasseSymbol K b := by
  induction n generalizing A with
  | zero =>
      let B : Kˣ := b 0
      let c : Fin 0 → Kˣ := fun i => i.elim0
      have hb : b = Fin.cons B c := by
        funext i
        have hi : i = (0 : Fin 1) := Fin.eq_zero i
        subst i
        rfl
      have hscale : (B : K) * (x 0) ^ 2 = (A : K) := by
        simpa [diagonalQuadratic, diagonalUnitCoefficients, B] using hvalue
      have hrep₀ := diagonalRepresents_cons_scaling
        (K := K) A B c (x 0) hscale
      have hrep : DiagonalRepresents
          (diagonalUnitCoefficients (Fin.cons A c))
          (diagonalUnitCoefficients b) := by
        rw [hb]
        exact hrep₀
      have hunary := unary_diagonalRepresents_of_eq_mul_sq
        (K := K) A B (x 0) hscale
      have hAB := diagonalUnitDeterminant_square_of_represents
        (K := K) (fun _ : Fin 1 => A) (fun _ : Fin 1 => B) hunary
      have hhasse₀ := diagonalHasseSymbol_cons_head_eq
        (K := K) A B c (by
          simpa [diagonalUnitDeterminant] using hAB)
      refine ⟨c, hrep, ?_⟩
      simpa only [hb] using hhasse₀
  | succ n ih =>
      let B : Kˣ := b 0
      let bt : Fin (n + 1) → Kˣ := Fin.tail b
      let xt : Fin (n + 1) → K := Fin.tail x
      let P : K := diagonalQuadratic (diagonalUnitCoefficients bt) xt
      have hb : b = Fin.cons B bt := by
        exact (Fin.cons_self_tail b).symm
      have hdecomp : (B : K) * (x 0) ^ 2 + P = (A : K) := by
        rw [hb] at hvalue
        conv_lhs at hvalue => rw [← Fin.cons_self_tail x]
        rw [diagonalUnitCoefficients_cons,
          DiagonalRepresents.diagonalQuadratic_cons] at hvalue
        exact hvalue
      by_cases hP : P = 0
      · have hscale : (B : K) * (x 0) ^ 2 = (A : K) := by
          simpa only [hP, add_zero] using hdecomp
        have hrep₀ := diagonalRepresents_cons_scaling
          (K := K) A B bt (x 0) hscale
        have hrep : DiagonalRepresents
            (diagonalUnitCoefficients (Fin.cons A bt))
            (diagonalUnitCoefficients b) := by
          rw [hb]
          exact hrep₀
        have hunary := unary_diagonalRepresents_of_eq_mul_sq
          (K := K) A B (x 0) hscale
        have hAB := diagonalUnitDeterminant_square_of_represents
          (K := K) (fun _ : Fin 1 => A) (fun _ : Fin 1 => B) hunary
        have hhasse₀ := diagonalHasseSymbol_cons_head_eq
          (K := K) A B bt (by
            simpa [diagonalUnitDeterminant] using hAB)
        refine ⟨bt, hrep, ?_⟩
        simpa only [hb] using hhasse₀
      · let Pu : Kˣ := Units.mk0 P hP
        have htailValue :
            diagonalQuadratic (diagonalUnitCoefficients bt) xt =
              (Pu : K) := by
          rfl
        rcases ih bt Pu xt htailValue with ⟨c, hrepRec, hhasseRec⟩
        let D : Kˣ := B * Pu / A
        have hbinaryValue :
            (B : K) * (x 0) ^ 2 + (Pu : K) * (1 : K) ^ 2 =
              (A : K) := by
          simpa only [Pu, Units.val_mk0, one_pow, mul_one] using hdecomp
        have hbin : DiagonalRepresents
            (diagonalUnitCoefficients
              (Fin.cons A (fun _ : Fin 1 => D)))
            (diagonalUnitCoefficients
              (Fin.cons B (fun _ : Fin 1 => Pu))) := by
          have h := Dyadic.binaryChange_diagonalRepresents
            B Pu A (x 0) 1 hbinaryValue
          convert h using 1 <;>
            funext i <;> fin_cases i <;> rfl
        have hstep := diagonalRepresents_binary_with_tail
          (K := K) A D B Pu c hbin
        have hprepend : DiagonalRepresents
            (diagonalUnitCoefficients (Fin.cons B (Fin.cons Pu c)))
            (diagonalUnitCoefficients (Fin.cons B bt)) := by
          simpa only [diagonalUnitCoefficients_cons] using
            diagonalRepresents_cons hrepRec (B : K)
        have hrep₀ := hstep.trans hprepend
        have hrep : DiagonalRepresents
            (diagonalUnitCoefficients (Fin.cons A (Fin.cons D c)))
            (diagonalUnitCoefficients b) := by
          rw [hb]
          exact hrep₀
        have hbinHasse := diagonalHasseSymbol_binary_eq_of_represents
          (K := K) (Fin.cons A (fun _ : Fin 1 => D))
            (Fin.cons B (fun _ : Fin 1 => Pu)) hbin
        have hbinCore : binaryHasseCore (K := K) A D =
            binaryHasseCore (K := K) B Pu := by
          rw [diagonalHasseSymbol_two, diagonalHasseSymbol_two] at hbinHasse
          simpa [binaryHasseCore] using hbinHasse
        have hbinDet₀ := diagonalUnitDeterminant_square_of_represents
          (K := K) (Fin.cons A (fun _ : Fin 1 => D))
            (Fin.cons B (fun _ : Fin 1 => Pu)) hbin
        have hbinDet : IsSquare ((A * D) * (B * Pu)) := by
          simpa [diagonalUnitDeterminant, Fin.prod_univ_two] using hbinDet₀
        have hstepHasse := diagonalHasseSymbol_binary_with_tail_eq
          (K := K) A D B Pu c hbinCore hbinDet
        have hrecDet := diagonalUnitDeterminant_square_of_represents
          (K := K) (Fin.cons Pu c) bt hrepRec
        have hprependHasse := diagonalHasseSymbol_cons_tail_eq
          (K := K) B (Fin.cons Pu c) bt hhasseRec hrecDet
        refine ⟨Fin.cons D c, hrep, ?_⟩
        calc
          diagonalHasseSymbol K (Fin.cons A (Fin.cons D c)) =
              diagonalHasseSymbol K (Fin.cons B (Fin.cons Pu c)) :=
            hstepHasse
          _ = diagonalHasseSymbol K (Fin.cons B bt) := hprependHasse
          _ = diagonalHasseSymbol K b := by rw [hb]

private theorem diagonalHasseSymbol_eq_of_represents
    (n : Nat) (a b : Fin n → Kˣ)
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients a) (diagonalUnitCoefficients b)) :
    diagonalHasseSymbol K a = diagonalHasseSymbol K b := by
  induction n with
  | zero =>
      simp only [diagonalHasseSymbol_zero]
  | succ n ih =>
      let A : Kˣ := a 0
      let aTail : Fin n → Kˣ := Fin.tail a
      have ha : a = Fin.cons A aTail := (Fin.cons_self_tail a).symm
      rcases hrep with ⟨f, hf, hquadratic⟩
      let e₀ : Fin (n + 1) → K := Pi.basisFun K (Fin (n + 1)) 0
      let y : Fin (n + 1) → K := f e₀
      have hy : diagonalQuadratic (diagonalUnitCoefficients b) y =
          (A : K) := by
        calc
          diagonalQuadratic (diagonalUnitCoefficients b) y =
              diagonalQuadratic (diagonalUnitCoefficients a) e₀ :=
            hquadratic e₀
          _ = diagonalUnitCoefficients a 0 := by
            exact DiagonalRepresents.diagonalQuadratic_basisFun
              (diagonalUnitCoefficients a) 0
          _ = (A : K) := rfl
      rcases exists_diagonal_split_first (K := K) n b A y hy with
        ⟨c, hsplit, hsplitHasse⟩
      have hrepFull : DiagonalRepresents
          (diagonalUnitCoefficients a)
          (diagonalUnitCoefficients (Fin.cons A c)) := by
        have horiginal : DiagonalRepresents
            (diagonalUnitCoefficients a)
            (diagonalUnitCoefficients b) := ⟨f, hf, hquadratic⟩
        exact horiginal.trans
          (DiagonalRepresents.symm_of_sameRank hsplit)
      have hrepCons : DiagonalRepresents
          (diagonalUnitCoefficients (Fin.cons A aTail))
          (diagonalUnitCoefficients (Fin.cons A c)) := by
        rw [← ha]
        exact hrepFull
      have htail : DiagonalRepresents
          (diagonalUnitCoefficients aTail)
          (diagonalUnitCoefficients c) := by
        apply DiagonalRepresents.cancel_common_head
          (A : K) (diagonalUnitCoefficients aTail)
            (diagonalUnitCoefficients c)
        · exact Units.ne_zero A
        · intro i
          exact Units.ne_zero (aTail i)
        · intro i
          exact Units.ne_zero (c i)
        · simpa only [diagonalUnitCoefficients_cons] using hrepCons
      have htailHasse := ih aTail c htail
      have htailDet := diagonalUnitDeterminant_square_of_represents
        (K := K) aTail c htail
      have hconsHasse := diagonalHasseSymbol_cons_tail_eq
        (K := K) A aTail c htailHasse htailDet
      calc
        diagonalHasseSymbol K a =
            diagonalHasseSymbol K (Fin.cons A aTail) := by rw [ha]
        _ = diagonalHasseSymbol K (Fin.cons A c) := hconsHasse
        _ = diagonalHasseSymbol K b := hsplitHasse

instance diagonalIsometryInvariantLaws :
    DiagonalIsometryInvariantLaws K where
  determinant_square a b hrep :=
    diagonalUnitDeterminant_square_of_represents (K := K) a b hrep
  hasse_eq a b hrep :=
    diagonalHasseSymbol_eq_of_represents (K := K) _ a b hrep

example : DiagonalIsometryInvariantLaws K := inferInstance

end Bong
