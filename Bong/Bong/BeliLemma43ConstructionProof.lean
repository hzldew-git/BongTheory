/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma43
import Bong.Bong.BeliLemma41AdaptedBinary
import Bong.Bong.Beli2019Lemma710BONGProduct
import Bong.Bong.BinaryScaledExactRealization
import Bong.Bong.DiagonalHeadCancellation
import Bong.Bong.GoodMap
import Bong.Bong.UnaryModelBONG

/-!
# Constructive proof of Beli (2003), Lemma 4.3

The proof first realizes a prescribed admissible order sequence in a standard
diagonal space.  Unary and improper binary blocks are concatenated in the
order used by Beli.  The resulting BONG basis is then carried to the supplied
orthogonal basis by the unique basis equivalence; equality of the diagonal
values makes that equivalence an isometry.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG

/-- The nondegenerate diagonal quadratic space with coefficient units `a`. -/
noncomputable def coefficientDiagonalSpace {n : Nat} (a : Fin n → Kˣ) :
    QuadraticSpace K (Fin n → K) :=
  QuadraticSpace.finiteDiagonal (fun i ↦ (a i : K))
    (fun i ↦ Units.ne_zero (a i))

/-- A BONG in the standard diagonal space with a prescribed exact value
sequence.  The lattice is part of the output, as in Lemma 4.3. -/
structure DiagonalBONGRealization {n : Nat} (a : Fin n → Kˣ) where
  lattice : Lattice K (Fin n → K)
  bong : BONG (Fin n → K) (coefficientDiagonalSpace a) lattice n
  valueUnit_eq : ∀ i, bong.valueUnit i = a i

namespace DiagonalBONGRealization

variable {n : Nat} {a : Fin n → Kˣ}

/-- The order sequence of an exact diagonal realization is the prescribed
coefficient order sequence. -/
theorem order_eq (R : DiagonalBONGRealization a) (i : Fin n) :
    R.bong.order i = ordUnit K (a i) := by
  rw [R.bong.order_eq_ordUnit, R.valueUnit_eq]

/-- Weak two-step monotonicity of the prescribed coefficients makes the
realized BONG good. -/
theorem isGood (R : DiagonalBONGRealization a)
    (hgood : ∀ (i : Fin n) (hi : i.val + 2 < n),
      ordUnit K (a i) ≤ ordUnit K (a ⟨i.val + 2, hi⟩)) :
    R.bong.IsGood := by
  intro i hi
  rw [R.order_eq, R.order_eq]
  exact hgood i hi

/-- Strict two-step monotonicity of the prescribed coefficients gives BONG
property A. -/
theorem hasPropertyA (R : DiagonalBONGRealization a)
    (hA : ∀ (i : Fin n) (hi : i.val + 2 < n),
      ordUnit K (a i) < ordUnit K (a ⟨i.val + 2, hi⟩)) :
    R.bong.HasPropertyA := by
  intro i hi
  rw [R.order_eq, R.order_eq]
  exact hA i hi

end DiagonalBONGRealization

/-- Any BONG with a prescribed exact value sequence can be transported to
the corresponding standard diagonal space. -/
noncomputable def diagonalBONGRealizationOfExactValues
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W} {n : Nat}
    (b : BONG W r M n) (a : Fin n → Kˣ)
    (hvalues : ∀ i, b.valueUnit i = a i) :
    DiagonalBONGRealization a := by
  classical
  let target := coefficientDiagonalSpace a
  let standardBasis : Basis (Fin n) K (Fin n → K) := Pi.basisFun K (Fin n)
  let e : W ≃ₗ[K] (Fin n → K) :=
    b.basis.equiv standardBasis (Equiv.refl (Fin n))
  have hforms : target.bilin.comp e.toLinearMap e.toLinearMap = r.bilin := by
    apply LinearMap.BilinForm.ext_basis b.basis
    intro i j
    rw [LinearMap.BilinForm.comp_apply]
    change target.bilin (e (b.basis i)) (e (b.basis j)) =
      r.bilin (b.basis i) (b.basis j)
    simp only [e, standardBasis, Module.Basis.equiv_apply, Equiv.refl_apply]
    change target.bilin ((Pi.basisFun K (Fin n)) i)
        ((Pi.basisFun K (Fin n)) j) =
      r.bilin (b.ambientVector i) (b.ambientVector j)
    by_cases hij : i = j
    · subst j
      change target.quadratic ((Pi.basisFun K (Fin n)) i) =
        r.quadratic (b.ambientVector i)
      rw [b.quadratic_ambientVector]
      have hv := congrArg Units.val (hvalues i)
      change b.value i = (a i : K) at hv
      rw [show target.quadratic ((Pi.basisFun K (Fin n)) i) =
          (a i : K) by
        rw [show target.quadratic ((Pi.basisFun K (Fin n)) i) =
            diagonalQuadratic (fun j ↦ (a j : K))
              ((Pi.basisFun K (Fin n)) i) by
          simpa only [target, coefficientDiagonalSpace,
            QuadraticSpace.finiteDiagonal_quadratic_apply]]
        simp [diagonalQuadratic, Pi.basisFun_apply, Pi.single_apply]]
      exact hv.symm
    · rw [(LinearMap.BilinForm.iIsOrtho_def.mp
          b.ambientVector_iIsOrtho) i j hij]
      rw [show target.bilin ((Pi.basisFun K (Fin n)) i)
          ((Pi.basisFun K (Fin n)) j) =
          ∑ k, (a k : K) * (Pi.basisFun K (Fin n) i) k *
            (Pi.basisFun K (Fin n) j) k by
        simpa only [target, coefficientDiagonalSpace,
          QuadraticSpace.finiteDiagonal_bilin_apply]]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hki : k = i
      · subst k
        simp [Pi.basisFun_apply, hij]
      · simp [Pi.basisFun_apply, hki]
  let f : QuadraticSpace.Isometry r target :=
    { toLinearEquiv := e
      map_bilin := by
        intro x y
        exact DFunLike.congr_fun (DFunLike.congr_fun hforms x) y }
  let mapped := b.map f
  refine {
    lattice := Lattice.map f.toLinearEquiv M
    bong := mapped
    valueUnit_eq := ?_ }
  intro i
  apply Units.ext
  change mapped.value i = (a i : K)
  rw [show mapped.value i = b.value i by
    exact BONG.value_map f b i]
  exact congrArg Units.val (hvalues i)

/-- The empty prescribed sequence has its tautological zero-dimensional
realization. -/
noncomputable def emptyDiagonalBONGRealization (a : Fin 0 → Kˣ) :
    DiagonalBONGRealization a := by
  let standardBasis : Basis (Fin 0) K (Fin 0 → K) :=
    Pi.basisFun K (Fin 0)
  let M : Lattice K (Fin 0 → K) := Lattice.basisLattice standardBasis
  let exhausted : Subsingleton (Fin 0 → K) := inferInstance
  exact {
    lattice := M
    bong := BONG.nil (coefficientDiagonalSpace a) M exhausted
    valueUnit_eq := fun i ↦ Fin.elim0 i }

/-- Exact realization of an arbitrary one-term coefficient vector. -/
noncomputable def unaryDiagonalBONGRealization (a : Fin 1 → Kˣ) :
    DiagonalBONGRealization a :=
  diagonalBONGRealizationOfExactValues (unaryModelBONG (a 0)) a (by
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    exact unaryModelBONG_valueUnit (a 0) 0)

/-- Exact realization of an admissible two-term coefficient vector. -/
noncomputable def binaryDiagonalBONGRealization (a : Fin 2 → Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (a 1 / a 0)) :
    DiagonalBONGRealization a :=
  diagonalBONGRealizationOfExactValues
    (scaledBinaryExactBONG (a 0) (a 1) hadmissible) a (by
      intro i
      apply Units.ext
      fin_cases i
      · exact scaledBinaryExactBONG_value_zero (a 0) (a 1) hadmissible
      · exact scaledBinaryExactBONG_value_one (a 0) (a 1) hadmissible)

/-- Prepend a unary block to a nonempty exact diagonal realization.  The
single cross-order inequality is exactly the norm-generator hypothesis for
the orthogonal-product constructor. -/
noncomputable def prependUnaryDiagonalBONGRealization
    {m : Nat} {a : Fin (m + 1) → Kˣ}
    (head : Kˣ) (tail : DiagonalBONGRealization a)
    (hhead : ordUnit K head ≤ ordUnit K (a 0)) :
    DiagonalBONGRealization (Fin.cons head a) := by
  let singleton : Fin 1 → Kˣ := fun _ ↦ head
  let left := unaryDiagonalBONGRealization singleton
  have horder : ∀ i : Fin 1, left.bong.order i ≤ tail.bong.order 0 := by
    intro i
    rw [left.order_eq, tail.order_eq]
    simpa [singleton] using hhead
  let joined := left.bong.orthogonalProductRight tail.bong horder
  apply diagonalBONGRealizationOfExactValues joined (Fin.cons head a)
  intro i
  apply Units.ext
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · have hp := BONG.value_orthogonalProductRight_left
      left.bong tail.bong horder (0 : Fin 1)
    have hv := congrArg Units.val (left.valueUnit_eq (0 : Fin 1))
    change left.bong.value 0 = (head : K) at hv
    change joined.value 0 = (head : K)
    calc
      joined.value 0 = left.bong.value 0 := by
        simpa [joined, orthogonalProductLeftIndex] using hp
      _ = (head : K) := hv
  · have hp := BONG.value_orthogonalProductRight_right
      left.bong tail.bong horder j
    have hv := congrArg Units.val (tail.valueUnit_eq j)
    change tail.bong.value j = (a j : K) at hv
    change joined.value j.succ = (a j : K)
    calc
      joined.value j.succ = tail.bong.value j := by
        have hindex : orthogonalProductRightIndex 1 j = j.succ := by
          apply Fin.ext
          simp [orthogonalProductRightIndex]
          omega
        change (left.bong.orthogonalProductRight tail.bong horder).value
          j.succ = tail.bong.value j
        rw [← hindex]
        exact hp
      _ = (a j : K) := hv

/-- Prepend an admissible improper binary block to a nonempty exact diagonal
realization.  The two displayed bounds supply all norm-generator bounds for
the left block. -/
noncomputable def prependBinaryDiagonalBONGRealization
    {m : Nat} {a : Fin (m + 1) → Kˣ}
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first))
    (tail : DiagonalBONGRealization a)
    (hfirst : ordUnit K first ≤ ordUnit K (a 0))
    (hsecond : ordUnit K second ≤ ordUnit K (a 0)) :
    DiagonalBONGRealization (Fin.cons first (Fin.cons second a)) := by
  let pair : Fin 2 → Kˣ := ![first, second]
  have hpairAdmissible : IsBinaryParameterAdmissible (pair 1 / pair 0) := by
    simpa [pair] using hadmissible
  let left := binaryDiagonalBONGRealization pair hpairAdmissible
  have horder : ∀ i : Fin 2, left.bong.order i ≤ tail.bong.order 0 := by
    intro i
    fin_cases i
    · rw [left.order_eq, tail.order_eq]
      simpa [pair] using hfirst
    · rw [left.order_eq, tail.order_eq]
      simpa [pair] using hsecond
  let joined := left.bong.orthogonalProductRight tail.bong horder
  apply diagonalBONGRealizationOfExactValues joined
    (Fin.cons first (Fin.cons second a))
  intro i
  apply Units.ext
  refine Fin.cases ?_ (fun i' ↦ Fin.cases ?_ (fun j ↦ ?_) i') i
  · have hp := BONG.value_orthogonalProductRight_left
      left.bong tail.bong horder (0 : Fin 2)
    have hv := congrArg Units.val (left.valueUnit_eq (0 : Fin 2))
    change left.bong.value 0 = (first : K) at hv
    change joined.value 0 = (first : K)
    calc
      joined.value 0 = left.bong.value 0 := by
        simpa [joined, orthogonalProductLeftIndex] using hp
      _ = (first : K) := hv
  · have hp := BONG.value_orthogonalProductRight_left
      left.bong tail.bong horder (1 : Fin 2)
    have hv := congrArg Units.val (left.valueUnit_eq (1 : Fin 2))
    change left.bong.value 1 = (second : K) at hv
    change joined.value 1 = (second : K)
    calc
      joined.value 1 = left.bong.value 1 := by
        simpa [joined, orthogonalProductLeftIndex] using hp
      _ = (second : K) := hv
  · have hp := BONG.value_orthogonalProductRight_right
      left.bong tail.bong horder j
    have hv := congrArg Units.val (tail.valueUnit_eq j)
    change tail.bong.value j = (a j : K) at hv
    change joined.value j.succ.succ = (a j : K)
    calc
      joined.value j.succ.succ = tail.bong.value j := by
        have hindex : orthogonalProductRightIndex 2 j = j.succ.succ := by
          apply Fin.ext
          simp [orthogonalProductRightIndex]
          omega
        change (left.bong.orthogonalProductRight tail.bong horder).value
          j.succ.succ = tail.bong.value j
        rw [← hindex]
        exact hp
      _ = (a j : K) := hv

/-- Admissibility of every consecutive coefficient ratio. -/
def CoefficientAdjacentAdmissible {n : Nat} (a : Fin n → Kˣ) : Prop :=
  ∀ (i : Fin n) (hi : i.val + 1 < n),
    IsBinaryParameterAdmissible (a ⟨i.val + 1, hi⟩ / a i)

/-- Weak monotonicity along each parity chain of coefficient orders. -/
def CoefficientWeakTwoStep {n : Nat} (a : Fin n → Kˣ) : Prop :=
  ∀ (i : Fin n) (hi : i.val + 2 < n),
    ordUnit K (a i) ≤ ordUnit K (a ⟨i.val + 2, hi⟩)

/-- Consecutive admissibility passes to the coefficient tail. -/
theorem coefficientAdjacentAdmissible_tail {n : Nat}
    {a : Fin (n + 1) → Kˣ} (h : CoefficientAdjacentAdmissible a) :
    CoefficientAdjacentAdmissible (Fin.tail a) := by
  intro i hi
  let next : Fin n := ⟨i.val + 1, hi⟩
  let sourceNext : Fin (n + 1) :=
    ⟨i.succ.val + 1, by simp; omega⟩
  have hsourceNext : sourceNext = next.succ := by
    apply Fin.ext
    simp [sourceNext, next]
  have hh := h i.succ (by
    simp only [Fin.val_succ]
    omega)
  change IsBinaryParameterAdmissible (a next.succ / a i.succ)
  rw [← hsourceNext]
  exact hh

/-- Weak two-step monotonicity passes to the coefficient tail. -/
theorem coefficientWeakTwoStep_tail {n : Nat}
    {a : Fin (n + 1) → Kˣ} (h : CoefficientWeakTwoStep (K := K) a) :
    CoefficientWeakTwoStep (K := K) (Fin.tail a) := by
  intro i hi
  let next : Fin n := ⟨i.val + 2, hi⟩
  let sourceNext : Fin (n + 1) :=
    ⟨i.succ.val + 2, by simp; omega⟩
  have hsourceNext : sourceNext = next.succ := by
    apply Fin.ext
    simp [sourceNext, next]
  have hh := h i.succ (by
    simp only [Fin.val_succ]
    omega)
  change ordUnit K (a i.succ) ≤ ordUnit K (a next.succ)
  rw [← hsourceNext]
  exact hh

/-- Construct the exact diagonal BONG required by Lemma 4.3(ii).  At each
step Beli's dichotomy is used: a weakly increasing first pair contributes a
unary block, while a decreasing first pair contributes an admissible
improper binary block. -/
noncomputable def diagonalBONGRealizationOfCriteria
    {n : Nat} (a : Fin n → Kˣ)
    (hadj : CoefficientAdjacentAdmissible a)
    (hweak : CoefficientWeakTwoStep (K := K) a) :
    DiagonalBONGRealization a := by
  cases n with
  | zero =>
      exact emptyDiagonalBONGRealization a
  | succ n =>
      cases n with
      | zero =>
          exact unaryDiagonalBONGRealization a
      | succ m =>
          by_cases h01 : ordUnit K (a 0) ≤ ordUnit K (a 1)
          · let tailA : Fin (m + 1) → Kˣ := Fin.tail a
            have hadjTail : CoefficientAdjacentAdmissible tailA := by
              exact coefficientAdjacentAdmissible_tail hadj
            have hweakTail : CoefficientWeakTwoStep (K := K) tailA := by
              exact coefficientWeakTwoStep_tail hweak
            let tailR := diagonalBONGRealizationOfCriteria tailA
              hadjTail hweakTail
            rw [← Fin.cons_self_tail a]
            exact prependUnaryDiagonalBONGRealization (a 0) tailR (by
              simpa [tailA, Fin.tail] using h01)
          · cases m with
            | zero =>
                have hadmissible :
                    IsBinaryParameterAdmissible (a 1 / a 0) := by
                  exact hadj 0 (by decide)
                exact binaryDiagonalBONGRealization a hadmissible
            | succ k =>
                let firstTail : Fin (k + 2) → Kˣ := Fin.tail a
                let tailA : Fin (k + 1) → Kˣ := Fin.tail firstTail
                have hadjTail : CoefficientAdjacentAdmissible tailA := by
                  exact coefficientAdjacentAdmissible_tail
                    (coefficientAdjacentAdmissible_tail hadj)
                have hweakTail : CoefficientWeakTwoStep (K := K) tailA := by
                  exact coefficientWeakTwoStep_tail
                    (coefficientWeakTwoStep_tail hweak)
                let tailR := diagonalBONGRealizationOfCriteria tailA
                  hadjTail hweakTail
                have hadmissible : IsBinaryParameterAdmissible
                    (firstTail 0 / a 0) := by
                  simpa [firstTail, Fin.tail] using hadj 0 (by
                    simp only [Fin.val_zero]
                    omega)
                have hfirst : ordUnit K (a 0) ≤
                    ordUnit K (tailA 0) := by
                  have hh := hweak 0 (by
                    simp only [Fin.val_zero]
                    omega)
                  calc
                    ordUnit K (a 0) ≤
                        ordUnit K (a ⟨2, by omega⟩) := by
                      convert hh using 1
                      apply congrArg (ordUnit K)
                      apply congrArg a
                      apply Fin.ext
                      rfl
                    _ = ordUnit K (tailA 0) := by
                      apply congrArg (ordUnit K)
                      apply congrArg a
                      apply Fin.ext
                      rfl
                have hsecondFirst : ordUnit K (firstTail 0) ≤
                    ordUnit K (a 0) := by
                  exact (lt_of_not_ge h01).le
                have hsecond : ordUnit K (firstTail 0) ≤
                    ordUnit K (tailA 0) := hsecondFirst.trans hfirst
                rw [← Fin.cons_self_tail a]
                change DiagonalBONGRealization
                  (Fin.cons (a 0) firstTail)
                rw [← Fin.cons_self_tail firstTail]
                exact prependBinaryDiagonalBONGRealization
                  (a 0) (firstTail 0) hadmissible tailR hfirst hsecond
termination_by n
decreasing_by all_goals omega

/-- A concrete BONG realization of a supplied orthogonal basis. -/
structure OrthogonalBasisBONGRealization
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {n : Nat}
    (X : OrthogonalBasisData q n) where
  lattice : Lattice K V
  bong : BONG V q lattice n
  isRealizedBy : X.IsRealizedBy bong

/-- Carry an exact standard diagonal realization to the given orthogonal
basis by the unique basis equivalence. -/
noncomputable def orthogonalBasisBONGRealizationOfDiagonal
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {n : Nat}
    (X : OrthogonalBasisData q n)
    (R : DiagonalBONGRealization X.valueUnit) :
    OrthogonalBasisBONGRealization X := by
  let source := coefficientDiagonalSpace X.valueUnit
  let e : (Fin n → K) ≃ₗ[K] V :=
    R.bong.basis.equiv X.basis (Equiv.refl (Fin n))
  have hforms : q.bilin.comp e.toLinearMap e.toLinearMap = source.bilin := by
    apply LinearMap.BilinForm.ext_basis R.bong.basis
    intro i j
    rw [LinearMap.BilinForm.comp_apply]
    change q.bilin (e (R.bong.basis i)) (e (R.bong.basis j)) =
      source.bilin (R.bong.basis i) (R.bong.basis j)
    simp only [e, Module.Basis.equiv_apply, Equiv.refl_apply]
    change q.bilin (X.basis i) (X.basis j) =
      source.bilin (R.bong.ambientVector i) (R.bong.ambientVector j)
    by_cases hij : i = j
    · subst j
      change q.quadratic (X.basis i) =
        source.quadratic (R.bong.ambientVector i)
      rw [R.bong.quadratic_ambientVector]
      change X.value i = R.bong.value i
      have hv := congrArg Units.val (R.valueUnit_eq i)
      exact hv.symm
    · rw [(LinearMap.BilinForm.iIsOrtho_def.mp X.orthogonal) i j hij,
        (LinearMap.BilinForm.iIsOrtho_def.mp
          R.bong.ambientVector_iIsOrtho) i j hij]
  let f : QuadraticSpace.Isometry source q :=
    { toLinearEquiv := e
      map_bilin := by
        intro x y
        exact DFunLike.congr_fun (DFunLike.congr_fun hforms x) y }
  let mapped := R.bong.map f
  exact {
    lattice := Lattice.map f.toLinearEquiv R.lattice
    bong := mapped
    isRealizedBy := by
      intro i
      rw [BONG.ambientVector_map]
      change e (R.bong.basis i) = X.basis i
      simp [e, Module.Basis.equiv_apply] }

namespace OrthogonalBasisBONGRealization

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {n : Nat}
  {X : OrthogonalBasisData q n}

/-- Weak two-step inequalities of the supplied basis make its transported
realization good. -/
theorem isGood (T : OrthogonalBasisBONGRealization X)
    (hweak : X.HasWeakTwoStepOrder) : T.bong.IsGood := by
  intro i hi
  simpa only [X.order_eq_of_isRealizedBy T.isRealizedBy] using hweak i hi

/-- Strict two-step inequalities of the supplied basis give coordinate
property A for its transported realization. -/
theorem hasPropertyA (T : OrthogonalBasisBONGRealization X)
    (hstrict : X.HasStrictTwoStepOrder) : T.bong.HasPropertyA := by
  intro i hi
  simpa only [X.order_eq_of_isRealizedBy T.isRealizedBy] using hstrict i hi

end OrthogonalBasisBONGRealization

/-- Adjacent binary realizability gives exactly the consecutive
admissibility input used by the diagonal recursion. -/
theorem coefficientAdjacentAdmissible_valueUnit
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {n : Nat}
    {X : OrthogonalBasisData q n} (h : X.HasAdjacentBONGs) :
    CoefficientAdjacentAdmissible X.valueUnit := by
  intro i hi
  rcases h i hi with ⟨w⟩
  have hparameter : w.bong.binaryParameter =
      X.valueUnit ⟨i.val + 1, hi⟩ / X.valueUnit i := by
    apply Units.ext
    rw [coe_binaryParameter]
    simp only [Units.val_div_eq_div_val,
      OrthogonalBasisData.coe_valueUnit]
    rw [← w.bong.quadratic_ambientVector 1,
      ← w.bong.quadratic_ambientVector 0]
    unfold OrthogonalBasisData.value
    change q.quadratic (w.bong.ambientVector 1 : V) /
        q.quadratic (w.bong.ambientVector 0 : V) = _
    rw [w.ambientVector_zero, w.ambientVector_one]
  rw [← hparameter]
  exact w.bong.binaryParameter_isBinaryParameterAdmissible

/-- The good realization in Beli (2003), Lemma 4.3(ii), constructed with no
law parameter. -/
theorem hasGoodRealization_of_conditions_proof
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {n : Nat}
    (X : OrthogonalBasisData q n)
    (hpairs : X.HasAdjacentBONGs) (hweak : X.HasWeakTwoStepOrder) :
    X.HasGoodRealization := by
  have hadj : CoefficientAdjacentAdmissible X.valueUnit :=
    coefficientAdjacentAdmissible_valueUnit hpairs
  have hcoeffWeak : CoefficientWeakTwoStep (K := K) X.valueUnit := by
    intro i hi
    exact hweak i hi
  let R := diagonalBONGRealizationOfCriteria X.valueUnit hadj hcoeffWeak
  let T := orthogonalBasisBONGRealizationOfDiagonal X R
  exact ⟨T.lattice, T.bong, T.isRealizedBy, T.isGood hweak⟩

/-- The property-A realization in Beli (2003), Lemma 4.3(i), constructed
with no law parameter. -/
theorem hasPropertyARealization_of_conditions_proof
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {n : Nat}
    (X : OrthogonalBasisData q n)
    (hpairs : X.HasAdjacentBONGs) (hstrict : X.HasStrictTwoStepOrder) :
    X.HasPropertyARealization := by
  have hadj : CoefficientAdjacentAdmissible X.valueUnit :=
    coefficientAdjacentAdmissible_valueUnit hpairs
  have hcoeffWeak : CoefficientWeakTwoStep (K := K) X.valueUnit := by
    intro i hi
    exact (hstrict i hi).le
  let R := diagonalBONGRealizationOfCriteria X.valueUnit hadj hcoeffWeak
  let T := orthogonalBasisBONGRealizationOfDiagonal X R
  have hA : T.bong.HasPropertyA := T.hasPropertyA hstrict
  letI : Module.Finite K V := T.lattice.moduleFinite
  exact ⟨T.lattice, T.bong, T.isRealizedBy,
    T.bong.hasJordanPropertyA_of_hasPropertyA hA⟩

end BONG

end Bong
