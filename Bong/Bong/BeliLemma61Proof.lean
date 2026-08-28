/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma62Proof
import Bong.Bong.BinaryScaledExactRealization
import Bong.Lattice.DVRFactorization
import Bong.Dyadic.QuadraticDefectHensel
import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Proof of Beli (2003), Lemma 6.1

The key point is that a forward head rescaling can be enlarged back by the
inverse-head construction of Lemma 6.2(i).  Equality of all ambient BONG
vectors then identifies the enlarged lattice with the original one.  This
turns the carrier calculation into a one-dimensional DVR calculation.
-/

namespace Bong

open Dyadic
open Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG

/-- Coordinate factors for multiplying only the first ambient BONG vector by
`π^k`. -/
noncomputable def headRescaleFactors (k : Nat) : Fin (n + 2) → Kˣ :=
  fun i ↦ if i = 0 then uniformizerPowerUnit K (k : Int) else 1

/-- The ambient orthogonal basis with only its first vector multiplied by
`π^k`. -/
noncomputable def headRescaledBasis (b : BONG V q L (n + 2)) (k : Nat) :
    Basis (Fin (n + 2)) K V :=
  b.basis.unitsSMul (headRescaleFactors (K := K) (n := n) k)

@[simp]
theorem headRescaledBasis_zero (b : BONG V q L (n + 2)) (k : Nat) :
    b.headRescaledBasis k 0 =
      ((uniformizerPowerUnit K (k : Int) : Kˣ) : K) • b.ambientVector 0 := by
  change b.headRescaledBasis k 0 =
    ((uniformizerPowerUnit K (k : Int) : Kˣ) : K) • b.basis 0
  simp [headRescaledBasis, headRescaleFactors, Basis.unitsSMul_apply,
    Units.smul_def]

@[simp]
theorem headRescaledBasis_succ (b : BONG V q L (n + 2)) (k : Nat)
    (i : Fin (n + 1)) :
    b.headRescaledBasis k i.succ = b.ambientVector i.succ := by
  change b.headRescaledBasis k i.succ = b.basis i.succ
  simp [headRescaledBasis, headRescaleFactors, Basis.unitsSMul_apply]

/-- Rescaling one vector of an orthogonal basis preserves orthogonality. -/
private theorem headRescaledBasis_iIsOrtho
    (b : BONG V q L (n + 2)) (k : Nat) :
    q.bilin.iIsOrtho (b.headRescaledBasis k) := by
  rw [LinearMap.BilinForm.iIsOrtho_def]
  intro i j hij
  simp only [headRescaledBasis, Basis.unitsSMul_apply, Units.smul_def,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  have hzero : q.bilin (b.basis i) (b.basis j) = 0 :=
    (LinearMap.BilinForm.iIsOrtho_def.mp b.ambientVector_iIsOrtho) i j hij
  rw [hzero]
  simp

/-- Orthogonal-basis data underlying the desired globally rescaled BONG. -/
noncomputable def headRescaledOrthogonalBasisData
    (b : BONG V q L (n + 2)) (k : Nat) :
    OrthogonalBasisData q (n + 2) where
  basis := b.headRescaledBasis k
  orthogonal := b.headRescaledBasis_iIsOrtho k

@[simp]
theorem headRescaledOrthogonalBasisData_basis_zero
    (b : BONG V q L (n + 2)) (k : Nat) :
    (b.headRescaledOrthogonalBasisData k).basis 0 =
      ((uniformizerPowerUnit K (k : Int) : Kˣ) : K) •
        b.ambientVector 0 :=
  b.headRescaledBasis_zero k

@[simp]
theorem headRescaledOrthogonalBasisData_basis_succ
    (b : BONG V q L (n + 2)) (k : Nat) (i : Fin (n + 1)) :
    (b.headRescaledOrthogonalBasisData k).basis i.succ =
      b.ambientVector i.succ :=
  b.headRescaledBasis_succ k i

@[simp]
theorem headRescaledOrthogonalBasisData_valueUnit_zero
    (b : BONG V q L (n + 2)) (k : Nat) :
    (b.headRescaledOrthogonalBasisData k).valueUnit 0 =
      uniformizerPowerUnit K (k : Int) ^ 2 * b.valueUnit 0 := by
  apply Units.ext
  change q.quadratic
      ((b.headRescaledOrthogonalBasisData k).basis 0) =
    (uniformizerPowerUnit K (k : Int) : K) ^ 2 * b.value 0
  rw [b.headRescaledOrthogonalBasisData_basis_zero, q.quadratic_smul,
    b.quadratic_ambientVector]

@[simp]
theorem headRescaledOrthogonalBasisData_valueUnit_succ
    (b : BONG V q L (n + 2)) (k : Nat) (i : Fin (n + 1)) :
    (b.headRescaledOrthogonalBasisData k).valueUnit i.succ =
      b.valueUnit i.succ := by
  apply Units.ext
  change q.quadratic
      ((b.headRescaledOrthogonalBasisData k).basis i.succ) = b.value i.succ
  rw [b.headRescaledOrthogonalBasisData_basis_succ,
    b.quadratic_ambientVector]

/-- The zeroth order of the rescaled orthogonal basis is shifted by `2k`. -/
theorem headRescaledOrthogonalBasisData_order_zero
    (b : BONG V q L (n + 2)) (k : Nat) :
    (b.headRescaledOrthogonalBasisData k).order 0 =
      b.order 0 + 2 * (k : Int) := by
  unfold OrthogonalBasisData.order
  rw [b.headRescaledOrthogonalBasisData_valueUnit_zero,
    ordUnit_mul, ordUnit_pow, ordUnit_uniformizerPowerUnit,
    ← b.order_eq_ordUnit]
  omega

/-- Every positive order of the rescaled orthogonal basis is unchanged. -/
theorem headRescaledOrthogonalBasisData_order_succ
    (b : BONG V q L (n + 2)) (k : Nat) (i : Fin (n + 1)) :
    (b.headRescaledOrthogonalBasisData k).order i.succ =
      b.order i.succ := by
  unfold OrthogonalBasisData.order
  rw [b.headRescaledOrthogonalBasisData_valueUnit_succ,
    ← b.order_eq_ordUnit]

/-- The first adjacent parameter after rescaling the head by `π^k`. -/
noncomputable def headRescaledFirstParameter
    (b : BONG V q L (n + 2)) (k : Nat) : Kˣ :=
  (b.headRescaledOrthogonalBasisData k).valueUnit 1 /
    (b.headRescaledOrthogonalBasisData k).valueUnit 0

/-- Rescaling the head divides the first adjacent parameter by a square. -/
theorem headRescaledFirstParameter_eq_mul_inv_square
    (b : BONG V q L (n + 2)) (k : Nat) :
    b.headRescaledFirstParameter k =
      b.adjacentParameter 0 (by simp) *
        (uniformizerPowerUnit K (k : Int))⁻¹ ^ 2 := by
  unfold headRescaledFirstParameter
  have hindex : (1 : Fin (n + 2)) = (0 : Fin (n + 1)).succ := by
    apply Fin.ext
    rfl
  have hone : (b.headRescaledOrthogonalBasisData k).valueUnit 1 =
      b.valueUnit 1 := by
    rw [hindex]
    exact b.headRescaledOrthogonalBasisData_valueUnit_succ k
      (0 : Fin (n + 1))
  have hadj : b.adjacentParameter 0 (by simp) =
      b.valueUnit 1 / b.valueUnit 0 := by
    unfold adjacentParameter
    congr 2
  rw [hone, b.headRescaledOrthogonalBasisData_valueUnit_zero, hadj]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  exact (mul_assoc (b.valueUnit 1) ((b.valueUnit 0)⁻¹ : Kˣ)
    ((uniformizerPowerUnit K (k : Int) ^ 2)⁻¹ : Kˣ)).symm

/-- The first adjacent order gap decreases by `2k`. -/
theorem ordUnit_headRescaledFirstParameter
    (b : BONG V q L (n + 2)) (k : Nat) :
    ordUnit K (b.headRescaledFirstParameter k) =
      b.lemma62Gap - 2 * (k : Int) := by
  rw [b.headRescaledFirstParameter_eq_mul_inv_square,
    ordUnit_mul, ordUnit_pow, ordUnit_inv,
    ordUnit_uniformizerPowerUnit, b.ordUnit_adjacentParameter_zero]
  omega

/-- The relative quadratic defect of the rescaled parameter is unchanged. -/
theorem quadraticDefect_neg_headRescaledFirstParameter
    (b : BONG V q L (n + 2)) (k : Nat) :
    quadraticDefect K (-b.headRescaledFirstParameter k) =
      beliParameterDefect K (b.adjacentParameter 0 (by simp)) := by
  rw [b.headRescaledFirstParameter_eq_mul_inv_square]
  change quadraticDefect K
      (-(b.adjacentParameter 0 (by simp) *
        (uniformizerPowerUnit K (k : Int))⁻¹ ^ 2)) = _
  rw [← neg_mul, quadraticDefect_mul_square]
  rfl

/-- An admissible first adjacent parameter realizes the literal binary
segment `⟨π^k x₁,x₂⟩`. -/
noncomputable def headBinaryRescaleWitnessOfAdmissible
    (b : BONG V q L (n + 2)) (k : Nat)
    (hadmissible : IsBinaryParameterAdmissible
      ((b.headRescaledOrthogonalBasisData k).valueUnit 1 /
        (b.headRescaledOrthogonalBasisData k).valueUnit 0)) :
    b.HeadBinaryRescaleWitness k := by
  let X := b.headRescaledOrthogonalBasisData k
  let index : Fin 2 → Fin (n + 2) := ![0, 1]
  have hindex : Function.Injective index := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · norm_num [index] at hij
    · norm_num [index] at hij
    · rfl
  have hli : LinearIndependent K
      (binaryPairFamily (X.basis 0) (X.basis 1)) := by
    convert X.basis.linearIndependent.comp index hindex using 1
    funext j
    fin_cases j <;> rfl
  let carrier := binaryPairSpan (K := K) (X.basis 0) (X.basis 1)
  let pairBasis : Basis (Fin 2) K carrier :=
    binaryPairBasis (K := K) (X.basis 0) (X.basis 1) hli
  have hpairOrtho :
      (q.bilin.restrict carrier).iIsOrtho pairBasis := by
    rw [LinearMap.BilinForm.iIsOrtho_def]
    intro i j hij
    change q.bilin (pairBasis i : V) (pairBasis j : V) = 0
    rw [coe_binaryPairBasis, coe_binaryPairBasis]
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact (LinearMap.BilinForm.iIsOrtho_def.mp X.orthogonal)
        (0 : Fin (n + 2)) (1 : Fin (n + 2)) (by norm_num)
    · exact (LinearMap.BilinForm.iIsOrtho_def.mp X.orthogonal)
        (1 : Fin (n + 2)) (0 : Fin (n + 2)) (by norm_num)
    · exact (hij rfl).elim
  have hpairSelf : ∀ i,
      (q.bilin.restrict carrier) (pairBasis i) (pairBasis i) ≠ 0 := by
    intro i
    change q.quadratic (pairBasis i : V) ≠ 0
    rw [coe_binaryPairBasis]
    fin_cases i
    · exact X.value_ne_zero 0
    · exact X.value_ne_zero 1
  have hnondeg : (q.bilin.restrict carrier).Nondegenerate :=
    (hpairOrtho.nondegenerate_iff_not_isOrtho_basis_self
      (q.bilin.restrict carrier) pairBasis).2 hpairSelf
  let targetQ := q.restrict carrier hnondeg
  let first := X.valueUnit 0
  let second := X.valueUnit 1
  let source := scaledBinaryExactBONG first second hadmissible
  let e : (Fin 2 → K) ≃ₗ[K] carrier :=
    source.basis.equiv pairBasis (Equiv.refl (Fin 2))
  have hforms : targetQ.bilin.comp e.toLinearMap e.toLinearMap =
      (scaledBinaryModelSpace first second hadmissible).bilin := by
    apply LinearMap.BilinForm.ext_basis source.basis
    intro i j
    rw [LinearMap.BilinForm.comp_apply]
    change q.bilin (e (source.basis i) : V) (e (source.basis j) : V) = _
    simp only [e, Module.Basis.equiv_apply, Equiv.refl_apply]
    by_cases hij : i = j
    · subst j
      rw [show (scaledBinaryModelSpace first second hadmissible).bilin
          (source.basis i) (source.basis i) = source.value i by
        exact source.quadratic_ambientVector i]
      change q.quadratic (pairBasis i : V) = source.value i
      have hpairValue : ∀ j : Fin 2,
          q.quadratic (pairBasis j : V) = ![X.value 0, X.value 1] j := by
        intro j
        rw [coe_binaryPairBasis]
        fin_cases j <;> rfl
      have hsourceValue : ∀ j : Fin 2,
          source.value j = ![(first : K), (second : K)] j := by
        intro j
        fin_cases j
        · simp [source]
        · simp [source]
      rw [hpairValue i, hsourceValue i]
      fin_cases i <;> rfl
    · have hleft :=
        (LinearMap.BilinForm.iIsOrtho_def.mp hpairOrtho) i j hij
      have hright :=
        (LinearMap.BilinForm.iIsOrtho_def.mp source.ambientVector_iIsOrtho)
          i j hij
      change q.bilin (pairBasis i : V) (pairBasis j : V) =
        (scaledBinaryModelSpace first second hadmissible).bilin
          (source.ambientVector i) (source.ambientVector j)
      exact hleft.trans hright.symm
  let f : QuadraticSpace.Isometry
      (scaledBinaryModelSpace first second hadmissible) targetQ := {
    toLinearEquiv := e
    map_bilin := by
      intro x y
      exact DFunLike.congr_fun (DFunLike.congr_fun hforms x) y }
  let mapped := source.map f
  refine {
    carrier := carrier
    nondegenerate := hnondeg
    lattice := Lattice.map e (scaledBinaryModelLattice (K := K))
    bong := mapped
    ambientVector_zero := ?_
    ambientVector_one := ?_ }
  · change ((mapped.ambientVector 0 : carrier) : V) = _
    rw [BONG.ambientVector_map]
    change ((e (source.basis 0) : carrier) : V) = _
    rw [show e (source.basis 0) = pairBasis 0 by simp [e],
      coe_binaryPairBasis]
    exact b.headRescaledOrthogonalBasisData_basis_zero k
  · change ((mapped.ambientVector 1 : carrier) : V) = _
    rw [BONG.ambientVector_map]
    change ((e (source.basis 1) : carrier) : V) = _
    rw [show e (source.basis 1) = pairBasis 1 by simp [e],
      coe_binaryPairBasis]
    exact b.headRescaledOrthogonalBasisData_basis_succ k 0

/-- Transport any BONG with the right diagonal values to a prescribed
orthogonal basis.  This is the linear-algebraic transport used in the
constructive direction of Beli's Lemma 4.3. -/
structure ValueMatchedOrthogonalBasisRealization
    (X : OrthogonalBasisData q (n + 2)) where
  lattice : Lattice K V
  bong : BONG V q lattice (n + 2)
  realized : X.IsRealizedBy bong

noncomputable def valueMatchedOrthogonalBasisRealization
    {U : Type w} [AddCommGroup U] [Module K U]
    {r : QuadraticSpace K U} {N : Lattice K U}
    (X : OrthogonalBasisData q (n + 2))
    (c : BONG U r N (n + 2))
    (hvalue : ∀ i, c.valueUnit i = X.valueUnit i) :
    ValueMatchedOrthogonalBasisRealization X := by
  let e : U ≃ₗ[K] V := c.basis.equiv X.basis (Equiv.refl (Fin (n + 2)))
  have hforms : q.bilin.comp e.toLinearMap e.toLinearMap = r.bilin := by
    apply LinearMap.BilinForm.ext_basis c.basis
    intro i j
    rw [LinearMap.BilinForm.comp_apply]
    change q.bilin (e (c.basis i)) (e (c.basis j)) =
      r.bilin (c.basis i) (c.basis j)
    simp only [e, Module.Basis.equiv_apply, Equiv.refl_apply]
    change q.bilin (X.basis i) (X.basis j) =
      r.bilin (c.ambientVector i) (c.ambientVector j)
    by_cases hij : i = j
    · subst j
      change q.quadratic (X.basis i) =
        r.quadratic (c.ambientVector i)
      rw [c.quadratic_ambientVector]
      have hv := congrArg Units.val (hvalue i)
      exact hv.symm
    · rw [(LinearMap.BilinForm.iIsOrtho_def.mp X.orthogonal) i j hij,
        (LinearMap.BilinForm.iIsOrtho_def.mp c.ambientVector_iIsOrtho) i j hij]
  let f : QuadraticSpace.Isometry r q := {
    toLinearEquiv := e
    map_bilin := by
      intro x y
      exact DFunLike.congr_fun (DFunLike.congr_fun hforms x) y }
  let mapped := c.map f
  exact {
    lattice := Lattice.map f.toLinearEquiv N
    bong := mapped
    realized := by
      intro i
      rw [BONG.ambientVector_map]
      change e (c.basis i) = X.basis i
      simp [e, Module.Basis.equiv_apply] }

namespace HeadBinaryRescaleWitness

variable {b : BONG V q L (n + 2)} {k : Nat}

@[simp]
theorem valueUnit_zero (w : b.HeadBinaryRescaleWitness k) :
    w.bong.valueUnit 0 =
      (b.headRescaledOrthogonalBasisData k).valueUnit 0 := by
  apply Units.ext
  change w.bong.value 0 =
    (b.headRescaledOrthogonalBasisData k).value 0
  rw [← w.bong.quadratic_ambientVector 0]
  change (q.restrict w.carrier w.nondegenerate).quadratic
      (w.bong.ambientVector 0) = _
  change q.quadratic (w.bong.ambientVector 0 : V) =
    q.quadratic ((b.headRescaledOrthogonalBasisData k).basis 0)
  rw [w.ambientVector_zero,
    b.headRescaledOrthogonalBasisData_basis_zero]

@[simp]
theorem valueUnit_one (w : b.HeadBinaryRescaleWitness k) :
    w.bong.valueUnit 1 =
      (b.headRescaledOrthogonalBasisData k).valueUnit 1 := by
  apply Units.ext
  change w.bong.value 1 =
    (b.headRescaledOrthogonalBasisData k).value 1
  rw [← w.bong.quadratic_ambientVector 1]
  change q.quadratic (w.bong.ambientVector 1 : V) =
    q.quadratic ((b.headRescaledOrthogonalBasisData k).basis 1)
  rw [w.ambientVector_one]
  congr 1
  simpa using (b.headRescaledOrthogonalBasisData_basis_succ k 0).symm

@[simp]
theorem order_zero (w : b.HeadBinaryRescaleWitness k) :
    w.bong.order 0 = b.order 0 + 2 * (k : Int) := by
  rw [w.bong.order_eq_ordUnit, w.valueUnit_zero]
  exact b.headRescaledOrthogonalBasisData_order_zero k

@[simp]
theorem order_one (w : b.HeadBinaryRescaleWitness k) :
    w.bong.order 1 = b.order 1 := by
  rw [w.bong.order_eq_ordUnit, w.valueUnit_one]
  exact b.headRescaledOrthogonalBasisData_order_succ k 0

end HeadBinaryRescaleWitness

/-- The one-dimensional BONG generated by the rescaled head. -/
noncomputable def headUnaryRescaleBasis
    (b : BONG V q L (n + 2)) (k : Nat) :
    Basis (Fin 1) K (b.prefixWitness 1 (by omega)).carrier :=
  (b.prefixWitness 1 (by omega)).bong.basis.unitsSMul
    (fun _ ↦ uniformizerPowerUnit K (k : Int))

private theorem headUnaryRescaleBasis_iIsOrtho
    (b : BONG V q L (n + 2)) (k : Nat) :
    ((q.restrict (b.prefixWitness 1 (by omega)).carrier
      (b.prefixWitness 1 (by omega)).nondegenerate).bilin).iIsOrtho
        (b.headUnaryRescaleBasis k) := by
  rw [LinearMap.BilinForm.iIsOrtho_def]
  intro i j hij
  exact (hij (Subsingleton.elim i j)).elim

private theorem headUnaryRescaleBasis_quadratic_ne
    (b : BONG V q L (n + 2)) (k : Nat) :
    (q.restrict (b.prefixWitness 1 (by omega)).carrier
      (b.prefixWitness 1 (by omega)).nondegenerate).quadratic
        (b.headUnaryRescaleBasis k 0) ≠ 0 := by
  rw [headUnaryRescaleBasis, Basis.unitsSMul_apply, Units.smul_def,
    QuadraticSpace.quadratic_smul]
  have hvalue :
      (q.restrict (b.prefixWitness 1 (by omega)).carrier
        (b.prefixWitness 1 (by omega)).nondegenerate).quadratic
          ((b.prefixWitness 1 (by omega)).bong.basis 0) ≠ 0 := by
    have hq :=
      (b.prefixWitness 1 (by omega)).bong.quadratic_ambientVector (0 : Fin 1)
    simp only [BONG.ambientVector] at hq
    rw [hq]
    exact (b.prefixWitness 1 (by omega)).bong.value_ne_zero 0
  exact mul_ne_zero (pow_ne_zero 2 (uniformizerPowerUnit K (k : Int)).ne_zero)
    hvalue

noncomputable def headUnaryRescaleBONG
    (b : BONG V q L (n + 2)) (k : Nat) :
    BONG (b.prefixWitness 1
        (Nat.succ_le_succ (Nat.zero_le (n + 1)))).carrier
      (q.restrict
        (b.prefixWitness 1
          (Nat.succ_le_succ (Nat.zero_le (n + 1)))).carrier
        (b.prefixWitness 1
          (Nat.succ_le_succ (Nat.zero_le (n + 1)))).nondegenerate)
      (Lattice.basisLattice (b.headUnaryRescaleBasis k)) 1 :=
  BONG.ofOrthogonalBasisFinOne _ (b.headUnaryRescaleBasis k)
    (b.headUnaryRescaleBasis_iIsOrtho k)
    (b.headUnaryRescaleBasis_quadratic_ne k)

@[simp]
theorem headUnaryRescaleBONG_ambientVector
    (b : BONG V q L (n + 2)) (k : Nat) :
    ((b.headUnaryRescaleBONG k).ambientVector 0 : V) =
      ((uniformizerPowerUnit K (k : Int) : Kˣ) : K) •
        b.ambientVector 0 := by
  rw [headUnaryRescaleBONG, ambientVector_ofOrthogonalBasisFinOne,
    headUnaryRescaleBasis, Basis.unitsSMul_apply]
  change ((uniformizerPowerUnit K (k : Int) : Kˣ) : K) •
      ((b.prefixWitness 1 (by omega)).bong.ambientVector 0 : V) = _
  rw [(b.prefixWitness 1 (by omega)).ambientVector_eq]
  congr 2

@[simp]
theorem headUnaryRescaleBONG_valueUnit
    (b : BONG V q L (n + 2)) (k : Nat) :
    (b.headUnaryRescaleBONG k).valueUnit 0 =
      (b.headRescaledOrthogonalBasisData k).valueUnit 0 := by
  apply Units.ext
  change (b.headUnaryRescaleBONG k).value 0 =
    (b.headRescaledOrthogonalBasisData k).value 0
  rw [← (b.headUnaryRescaleBONG k).quadratic_ambientVector 0]
  change q.quadratic ((b.headUnaryRescaleBONG k).ambientVector 0 : V) =
    q.quadratic ((b.headRescaledOrthogonalBasisData k).basis 0)
  rw [b.headUnaryRescaleBONG_ambientVector,
    b.headRescaledOrthogonalBasisData_basis_zero]

@[simp]
theorem headUnaryRescaleBONG_order
    (b : BONG V q L (n + 2)) (k : Nat) :
    (b.headUnaryRescaleBONG k).order 0 =
      b.order 0 + 2 * (k : Int) := by
  rw [(b.headUnaryRescaleBONG k).order_eq_ordUnit,
    b.headUnaryRescaleBONG_valueUnit]
  exact b.headRescaledOrthogonalBasisData_order_zero k

/-- Casting the length index preserves the bundled nonzero value. -/
@[simp]
theorem beliLemma61_valueUnit_castLength
    {U : Type w} [AddCommGroup U] [Module K U]
    {r : QuadraticSpace K U} {N : Lattice K U} {a c : Nat}
    (d : BONG U r N a) (h : a = c) (i : Fin c) :
    (d.castLength h).valueUnit i =
      d.valueUnit ⟨i.val, by simpa [h] using i.isLt⟩ := by
  subst c
  rfl

/-- Rescaling the head by the zeroth uniformizer power is the original
BONG itself. -/
noncomputable def headRescaleWitness_zero
    (b : BONG V q L (n + 2)) : b.HeadRescaleWitness 0 where
  lattice := L
  bong := b
  ambientVector_zero := by simp
  ambientVector_succ := by
    intro i
    rfl

/-- If the rescaled head order is no larger than the second order, the
rescaled line can be concatenated directly with the unchanged suffix. -/
noncomputable def headRescaleWitness_of_headOrder_le_second
    (b : BONG V q L (n + 2)) (k : Nat)
    (hle : b.order 0 + 2 * (k : Int) ≤ b.order 1) :
    b.HeadRescaleWitness k := by
  let left := b.headUnaryRescaleBONG k
  let right := b.segmentWitness 1 (n + 1) (by omega)
  have horder : ∀ i : Fin 1, left.order i ≤ right.bong.order 0 := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [show left = b.headUnaryRescaleBONG k by rfl,
      b.headUnaryRescaleBONG_order, right.order_eq]
    simpa [SegmentWitness.sourceIndex] using hle
  let raw := left.orthogonalProductRight right.bong horder
  let X := b.headRescaledOrthogonalBasisData k
  have hvalue : ∀ i : Fin (n + 2), raw.valueUnit i = X.valueUnit i := by
    intro i
    cases i using Fin.cases with
    | zero =>
        apply Units.ext
        have hindex : (0 : Fin (n + 2)) =
            orthogonalProductLeftIndex (n + 1) (0 : Fin 1) := by
          apply Fin.ext
          rfl
        rw [hindex]
        change raw.value (orthogonalProductLeftIndex (n + 1) (0 : Fin 1)) =
          X.value 0
        rw [show raw = left.orthogonalProductRight right.bong horder by rfl,
          value_orthogonalProductRight_left]
        exact congrArg Units.val (b.headUnaryRescaleBONG_valueUnit k)
    | succ i =>
        apply Units.ext
        have hindex : i.succ = orthogonalProductRightIndex 1 i := by
          apply Fin.ext
          simp [orthogonalProductRightIndex]
          omega
        rw [hindex]
        change raw.value (orthogonalProductRightIndex 1 i) =
          X.value (orthogonalProductRightIndex 1 i)
        rw [show raw = left.orthogonalProductRight right.bong horder by rfl,
          value_orthogonalProductRight_right, right.value_eq]
        have hsource : right.sourceIndex i = i.succ := by
          apply Fin.ext
          simp [SegmentWitness.sourceIndex]
          omega
        have htarget : orthogonalProductRightIndex 1 i = i.succ := by
          apply Fin.ext
          simp [orthogonalProductRightIndex]
          omega
        rw [hsource, htarget]
        have hv := congrArg Units.val
          (b.headRescaledOrthogonalBasisData_valueUnit_succ k i)
        simpa only [OrthogonalBasisData.coe_valueUnit, BONG.coe_valueUnit]
          using hv.symm
  let realized := valueMatchedOrthogonalBasisRealization X raw hvalue
  exact {
    lattice := realized.lattice
    bong := realized.bong
    ambientVector_zero := by
      rw [realized.realized]
      exact b.headRescaledOrthogonalBasisData_basis_zero k
    ambientVector_succ := by
      intro i
      rw [realized.realized]
      exact b.headRescaledOrthogonalBasisData_basis_succ k i }

/-- Extend the binary hypothesis occurring in Beli's Lemma 6.1 to the full
rescaled BONG.  If the new first order is below the second, split after the
first vector; otherwise split after the supplied binary block.  The bound on
the third order is exactly what makes the latter concatenation a BONG. -/
noncomputable def headRescaleWitness_of_binary
    (b : BONG V q L (n + 2)) (k : Nat)
    (w : b.HeadBinaryRescaleWitness k)
    (hthird : ∀ _h : 1 ≤ n,
      b.order 0 + 2 * (k : Int) ≤ b.order ⟨2, by omega⟩) :
    b.HeadRescaleWitness k := by
  by_cases hle : b.order 0 + 2 * (k : Int) ≤ b.order 1
  · exact b.headRescaleWitness_of_headOrder_le_second k hle
  · have hlt : b.order 1 < b.order 0 + 2 * (k : Int) :=
      lt_of_not_ge hle
    cases n with
    | zero =>
        let X := b.headRescaledOrthogonalBasisData k
        have hvalue : ∀ i : Fin 2, w.bong.valueUnit i = X.valueUnit i := by
          intro i
          fin_cases i
          · exact w.valueUnit_zero
          · exact w.valueUnit_one
        let realized := valueMatchedOrthogonalBasisRealization X w.bong hvalue
        exact {
          lattice := realized.lattice
          bong := realized.bong
          ambientVector_zero := by
            rw [realized.realized]
            exact b.headRescaledOrthogonalBasisData_basis_zero k
          ambientVector_succ := by
            intro i
            rw [realized.realized]
            exact b.headRescaledOrthogonalBasisData_basis_succ k i }

    | succ m =>
        let right := b.segmentWitness 2 (m + 1) (by omega)
        have horder : ∀ i : Fin 2,
            w.bong.order i ≤ right.bong.order 0 := by
          intro i
          fin_cases i
          · change w.bong.order (0 : Fin 2) ≤ right.bong.order 0
            rw [w.order_zero, right.order_eq]
            simpa [SegmentWitness.sourceIndex] using hthird (by omega)
          · change w.bong.order (1 : Fin 2) ≤ right.bong.order 0
            rw [w.order_one, right.order_eq]
            have hleThird : b.order 1 ≤ b.order ⟨2, by omega⟩ :=
              (le_of_lt hlt).trans (hthird (by omega))
            simpa [SegmentWitness.sourceIndex] using hleThird
        let raw := w.bong.orthogonalProductRight right.bong horder
        let X := b.headRescaledOrthogonalBasisData k
        have hvalue : ∀ i : Fin ((m + 1) + 2),
            raw.valueUnit i = X.valueUnit i := by
          intro i
          cases i using Fin.cases with
          | zero =>
              apply Units.ext
              have hindex : (0 : Fin ((m + 1) + 2)) =
                  orthogonalProductLeftIndex (m + 1) (0 : Fin 2) := by
                apply Fin.ext
                rfl
              rw [hindex]
              change raw.value
                  (orthogonalProductLeftIndex (m + 1) (0 : Fin 2)) =
                X.value 0
              rw [show raw = w.bong.orthogonalProductRight right.bong horder
                  by rfl,
                value_orthogonalProductRight_left]
              exact congrArg Units.val w.valueUnit_zero
          | succ i =>
              cases i using Fin.cases with
              | zero =>
                  change raw.valueUnit (1 : Fin ((m + 1) + 2)) =
                    X.valueUnit 1
                  apply Units.ext
                  have hindex : (1 : Fin ((m + 1) + 2)) =
                      orthogonalProductLeftIndex (m + 1) (1 : Fin 2) := by
                    apply Fin.ext
                    rfl
                  rw [hindex]
                  change raw.value
                      (orthogonalProductLeftIndex (m + 1) (1 : Fin 2)) =
                    X.value 1
                  rw [show raw =
                        w.bong.orthogonalProductRight right.bong horder by rfl,
                    value_orthogonalProductRight_left]
                  exact congrArg Units.val w.valueUnit_one
              | succ j =>
                  apply Units.ext
                  have hindex : j.succ.succ =
                      orthogonalProductRightIndex 2 j := by
                    apply Fin.ext
                    simp [orthogonalProductRightIndex]
                    omega
                  rw [hindex]
                  change raw.value (orthogonalProductRightIndex 2 j) =
                    X.value (orthogonalProductRightIndex 2 j)
                  rw [show raw =
                        w.bong.orthogonalProductRight right.bong horder by rfl,
                    value_orthogonalProductRight_right, right.value_eq]
                  have hsource : right.sourceIndex j = j.succ.succ := by
                    apply Fin.ext
                    simp [SegmentWitness.sourceIndex]
                    omega
                  have htarget : orthogonalProductRightIndex 2 j =
                      j.succ.succ := by
                    apply Fin.ext
                    simp [orthogonalProductRightIndex]
                    omega
                  rw [hsource, htarget]
                  have hv := congrArg Units.val
                    (b.headRescaledOrthogonalBasisData_valueUnit_succ k j.succ)
                  simpa only [OrthogonalBasisData.coe_valueUnit,
                    BONG.coe_valueUnit] using hv.symm
        let realized := valueMatchedOrthogonalBasisRealization X raw hvalue
        exact {
          lattice := realized.lattice
          bong := realized.bong
          ambientVector_zero := by
            rw [realized.realized]
            exact b.headRescaledOrthogonalBasisData_basis_zero k
          ambientVector_succ := by
            intro i
            rw [realized.realized]
            exact b.headRescaledOrthogonalBasisData_basis_succ k i }

/-- The numerical alternative in Lemma 6.1(iii) makes the rescaled first
binary parameter admissible.  In the high-defect branch the strict rational
inequality is converted back to the integral absolute-defect threshold. -/
theorem headRescaledFirstParameter_admissible_of_criterion
    (b : BONG V q L (n + 2)) (hcriterion : b.HeadRescaleCriterion) :
    IsBinaryParameterAdmissible (b.headRescaledFirstParameter 1) := by
  change
    2 * (ramificationIndex K : Int) + 1 ≤ b.lemma62Gap ∨
      (-(2 * (ramificationIndex K : Int)) < b.lemma62Gap ∧
        Even b.lemma62Gap ∧
          ((((ramificationIndex K : ℚ) -
            (b.lemma62Gap : ℚ) / 2) : ℚ) : WithTop ℚ) <
            b.normalizedAdjacentDefectOrder (0 : Fin (n + 1))) at hcriterion
  rcases hcriterion with hlarge | ⟨hlower, heven, hhigh⟩
  · apply isBinaryParameterAdmissible_of_ordUnit_nonneg
    rw [b.ordUnit_headRescaledFirstParameter]
    have hePos : 0 < (ramificationIndex K : Int) := by
      exact_mod_cast ramificationIndex_pos (K := K)
    omega
  · by_cases hnonneg : 0 ≤ b.lemma62Gap - 2
    · apply isBinaryParameterAdmissible_of_ordUnit_nonneg
      rw [b.ordUnit_headRescaledFirstParameter]
      simpa using hnonneg
    · apply
        (isBinaryParameterAdmissible_iff_order_add_two_e_and_defect
          (b.headRescaledFirstParameter 1)).2
      constructor
      · rw [b.ordUnit_headRescaledFirstParameter]
        rcases heven with ⟨r, hr⟩
        omega
      · rw [hasNonnegativeAbsoluteQuadraticDefect_iff_threshold_le,
          b.quadraticDefect_neg_headRescaledFirstParameter]
        let a : Kˣ := b.adjacentParameter 0 (by simp)
        have hnegOrder :
            ordUnit K (-b.headRescaledFirstParameter 1) =
              b.lemma62Gap - 2 := by
          calc
            ordUnit K (-b.headRescaledFirstParameter 1) =
                ordUnit K (b.headRescaledFirstParameter 1) := by
              apply WithTop.coe_injective
              simpa using ord_neg K
                ((b.headRescaledFirstParameter 1 : Kˣ) : K)
            _ = b.lemma62Gap - 2 := by
              simpa using b.ordUnit_headRescaledFirstParameter 1
        have hthreshold :
            absoluteDefectThreshold (-b.headRescaledFirstParameter 1) =
              Int.toNat (2 - b.lemma62Gap) := by
          unfold absoluteDefectThreshold
          rw [hnegOrder]
          congr 1
          omega
        rw [hthreshold]
        by_cases htop : beliParameterDefect K a = ⊤
        · change (Int.toNat (2 - b.lemma62Gap) : ℕ∞) ≤
              beliParameterDefect K a
          rw [htop]
          exact le_top
        · have hgapAtZero :
              b.order (0 : Fin (n + 1)).succ -
                  b.order (0 : Fin (n + 1)).castSucc = b.lemma62Gap := by
            unfold lemma62Gap
            rfl
          have hevenAtZero : Even
              (b.order (0 : Fin (n + 1)).succ -
                b.order (0 : Fin (n + 1)).castSucc) := by
            rw [hgapAtZero]
            exact heven
          have hparameterAtZero :
              b.adjacentParameter (0 : Fin (n + 1)).castSucc
                  (by simpa using (0 : Fin (n + 1)).isLt) =
                b.adjacentParameter 0 (by simp) := by
            congr 1
          have hdefectEq :
              beliParameterDefect K a =
                quadraticDefect K
                  (b.normalizedAdjacentProduct (0 : Fin (n + 1))) := by
            have hraw :=
              b.quadraticDefect_negative_adjacentParameter_eq_normalizedProduct_of_even
                (0 : Fin (n + 1)) hevenAtZero
            unfold a beliParameterDefect
            rw [← hparameterAtZero]
            exact hraw
          have hfiniteNormalized :
              quadraticDefect K
                  (b.normalizedAdjacentProduct (0 : Fin (n + 1))) ≠ ⊤ := by
            rw [← hdefectEq]
            exact htop
          have hnormalizedOrder :
              b.normalizedAdjacentDefectOrder (0 : Fin (n + 1)) =
                (((quadraticDefect K
                  (b.normalizedAdjacentProduct
                    (0 : Fin (n + 1)))).toNat : ℚ) : WithTop ℚ) := by
            unfold normalizedAdjacentDefectOrder
            rw [← ENat.coe_toNat hfiniteNormalized]
            rfl
          have htoNatEq :
              (beliParameterDefect K a).toNat =
                (quadraticDefect K
                  (b.normalizedAdjacentProduct
                    (0 : Fin (n + 1)))).toNat :=
            congrArg ENat.toNat hdefectEq
          rw [hnormalizedOrder, ← htoNatEq] at hhigh
          have hhighRat :
              (ramificationIndex K : ℚ) -
                  (b.lemma62Gap : ℚ) / 2 <
                ((beliParameterDefect K a).toNat : ℚ) := by
            exact_mod_cast hhigh
          rcases heven with ⟨r, hr⟩
          have hhighInt :
              (ramificationIndex K : Int) - r <
                ((beliParameterDefect K a).toNat : Int) := by
            rw [hr] at hhighRat
            norm_num at hhighRat
            exact_mod_cast hhighRat
          have hthresholdInt :
              2 - b.lemma62Gap ≤
                ((beliParameterDefect K a).toNat : Int) := by
            rw [hr] at hlower ⊢
            omega
          have hthresholdNonneg : 0 ≤ 2 - b.lemma62Gap := by
            omega
          have hcast :
              ((Int.toNat (2 - b.lemma62Gap) : Nat) : Int) =
                2 - b.lemma62Gap :=
            Int.toNat_of_nonneg hthresholdNonneg
          rw [← ENat.coe_toNat htop]
          norm_cast
          exact_mod_cast (hcast.symm ▸ hthresholdInt)

/-- Construct the literal binary initial segment required by Lemma 6.1(iii). -/
theorem headBinaryRescaleExists_of_criterion_proved
    (b : BONG V q L (n + 2)) (hcriterion : b.HeadRescaleCriterion) :
    b.HeadBinaryRescaleExists 1 := by
  refine ⟨b.headBinaryRescaleWitnessOfAdmissible 1 ?_⟩
  exact b.headRescaledFirstParameter_admissible_of_criterion hcriterion

/-- Cancellation of a common nonzero field factor in two generators of a
principal integral ideal. -/
private theorem mem_principalIdeal_cancel_left
    {a x y : K} (ha : a ≠ 0)
    (h : a * x ∈ Lattice.principalIdeal (K := K) (a * y)) :
    x ∈ Lattice.principalIdeal (K := K) y := by
  rw [Lattice.principalIdeal, Submodule.mem_span_singleton] at h ⊢
  rcases h with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  change (c : K) * y = x
  apply mul_left_cancel₀ ha
  change a * ((c : K) * y) = a * x
  calc
    a * ((c : K) * y) = (c : K) * (a * y) := by ring
    _ = a * x := by simpa [Algebra.smul_def] using hc

namespace HeadRescaleWitness

variable {b : BONG V q L (n + 2)} {k : Nat}

/-- The zeroth order after a head rescaling is shifted by exactly `2k`. -/
theorem order_zero_eq (w : b.HeadRescaleWitness k) :
    w.bong.order 0 = b.order 0 + 2 * (k : Int) := by
  have hvalueUnit : w.bong.valueUnit 0 =
      uniformizerPowerUnit K (k : Int) ^ 2 * b.valueUnit 0 := by
    apply Units.ext
    change w.bong.value 0 =
      (uniformizerPowerUnit K (k : Int) : K) ^ 2 * b.value 0
    rw [← w.bong.quadratic_ambientVector 0,
      w.ambientVector_zero, q.quadratic_smul,
      b.quadratic_ambientVector]
  rw [w.bong.order_eq_ordUnit, b.order_eq_ordUnit, hvalueUnit,
    ordUnit_mul, ordUnit_pow, ordUnit_uniformizerPowerUnit]
  omega

/-- Every order after the head is unchanged. -/
theorem order_succ_eq (w : b.HeadRescaleWitness k) (i : Fin (n + 1)) :
    w.bong.order i.succ = b.order i.succ := by
  apply WithTop.coe_injective
  rw [w.bong.coe_order, b.coe_order,
    ← w.bong.quadratic_ambientVector i.succ,
    ← b.quadratic_ambientVector i.succ,
    w.ambientVector_succ]

/-- Removing one uniformizer from a positive head rescaling. -/
noncomputable def predecessor
    (w : b.HeadRescaleWitness (k + 1)) : b.HeadRescaleWitness k := by
  let inverse := w.bong.headInverseRescaleWitness
  refine {
    lattice := inverse.lattice
    bong := inverse.bong
    ambientVector_zero := ?_
    ambientVector_succ := ?_
  }
  · rw [inverse.ambientVector_zero, w.ambientVector_zero]
    change
      ((uniformizerUnit K ^ (-1 : Int) : Kˣ) : K) •
          (((uniformizerUnit K ^ ((k + 1 : Nat) : Int) : Kˣ) : K) •
            b.ambientVector 0) =
        ((uniformizerUnit K ^ (k : Int) : Kˣ) : K) •
          b.ambientVector 0
    rw [smul_smul]
    congr 1
    have hunit :
        uniformizerUnit K ^ (-1 : Int) *
            uniformizerUnit K ^ ((k + 1 : Nat) : Int) =
          uniformizerUnit K ^ (k : Int) := by
      rw [← zpow_add (uniformizerUnit K) (-1)
        ((k + 1 : Nat) : Int)]
      congr 1
      omega
    simpa using congrArg (fun z : Kˣ ↦ (z : K)) hunit
  · intro i
    rw [inverse.ambientVector_succ, w.ambientVector_succ]

/-- A `(k+1)`-rescaling is a one-step rescaling of its predecessor. -/
noncomputable def asOneStepFromPredecessor
    (w : b.HeadRescaleWitness (k + 1)) :
    (w.predecessor).bong.HeadRescaleWitness 1 := by
  refine {
    lattice := w.lattice
    bong := w.bong
    ambientVector_zero := ?_
    ambientVector_succ := ?_
  }
  · rw [w.ambientVector_zero, (w.predecessor).ambientVector_zero]
    change
      ((uniformizerUnit K ^ ((k + 1 : Nat) : Int) : Kˣ) : K) •
          b.ambientVector 0 =
        ((uniformizerUnit K ^ (1 : Int) : Kˣ) : K) •
          (((uniformizerUnit K ^ (k : Int) : Kˣ) : K) •
            b.ambientVector 0)
    rw [smul_smul]
    congr 1
    have hunit :
        uniformizerUnit K ^ ((k + 1 : Nat) : Int) =
          uniformizerUnit K ^ (1 : Int) *
            uniformizerUnit K ^ (k : Int) := by
      rw [← zpow_add (uniformizerUnit K) (1 : Int) (k : Int)]
      congr 1
      omega
    simpa using congrArg (fun z : Kˣ ↦ (z : K)) hunit
  · intro i
    rw [w.ambientVector_succ, (w.predecessor).ambientVector_succ]

/-- Enlarging a one-step forward rescaling by the old head recovers the
original lattice. -/
theorem enlarged_eq_original (w : b.HeadRescaleWitness 1) :
    lemma57EnlargedLattice w.lattice w.bong.head 1 = L := by
  let inverse := w.bong.headInverseRescaleWitness
  change inverse.lattice = L
  apply inverse.bong.lattice_eq_of_ambientVector_eq b
  intro i
  cases i using Fin.cases with
  | zero =>
      rw [inverse.ambientVector_zero, w.ambientVector_zero]
      change
        ((uniformizerUnit K ^ (-1 : Int) : Kˣ) : K) •
            (((uniformizerUnit K ^ (1 : Int) : Kˣ) : K) •
              b.ambientVector 0) = b.ambientVector 0
      rw [smul_smul]
      simp [uniformizer_ne_zero K]
  | succ i =>
      rw [inverse.ambientVector_succ, w.ambientVector_succ]

/-- The vector adjoined by the inverse construction is literally the old
head. -/
theorem enlargedHead_eq_originalHead (w : b.HeadRescaleWitness 1) :
    lemma57EnlargedHead (K := K) w.bong.head 1 = b.head := by
  rw [lemma57EnlargedHead, ← w.bong.ambientVector_zero_eq_head,
    w.ambientVector_zero, b.ambientVector_zero_eq_head]
  change
    ((uniformizerUnit K ^ (-1 : Int) : Kˣ) : K) •
        (((uniformizerUnit K ^ (1 : Int) : Kˣ) : K) • b.head) = b.head
  rw [smul_smul]
  simp [uniformizer_ne_zero K]

/-- A one-step head-rescaled lattice is contained in its parent. -/
theorem lattice_le_original (w : b.HeadRescaleWitness 1) :
    w.lattice ≤ L := by
  intro x hx
  have hx' :=
    le_lemma57EnlargedLattice w.lattice w.bong.head 1 hx
  simpa only [w.enlarged_eq_original] using hx'

/-- Every vector of the parent is an integral multiple of the old head
modulo the one-step rescaled lattice. -/
theorem exists_sub_head_mem (w : b.HeadRescaleWitness 1)
    {y : V} (hy : y ∈ L) :
    ∃ z ∈ w.lattice, ∃ c : IntegerRing K, z + c • b.head = y := by
  rw [← w.enlarged_eq_original] at hy
  rw [lemma57EnlargedLattice, Lattice.mem_adjoinVector_iff] at hy
  rcases hy with ⟨z, hz, c, hzc⟩
  refine ⟨z, hz, c, ?_⟩
  rwa [w.enlargedHead_eq_originalHead] at hzc

/-- Twice the mixed pairing with the old head gains one uniformizer on the
forward-rescaled lattice. -/
theorem two_bilin_mem_shifted_head_ideal
    (w : b.HeadRescaleWitness 1) {z : V} (hz : z ∈ w.lattice) :
    (2 : K) * q.bilin b.head z ∈
      Lattice.principalIdeal (K := K)
        (uniformizer K * q.quadratic b.head) := by
  let I := Lattice.principalIdeal (K := K)
    (q.quadratic w.bong.head)
  have hhead : w.bong.head ∈ w.lattice :=
    w.bong.head_isNormGenerator.mem
  have hsum : q.quadratic (w.bong.head + z) ∈ I := by
    have h := Lattice.quadratic_mem_normIdeal_of_mem q w.lattice
      (w.lattice.add_mem hhead hz)
    rw [w.bong.head_isNormGenerator.normIdeal_eq] at h
    exact h
  have hheadValue : q.quadratic w.bong.head ∈ I := by
    exact Lattice.generator_mem_principalIdeal _
  have hzValue : q.quadratic z ∈ I := by
    have h := Lattice.quadratic_mem_normIdeal_of_mem q w.lattice hz
    rw [w.bong.head_isNormGenerator.normIdeal_eq] at h
    exact h
  have hcrossW : (2 : K) * q.bilin w.bong.head z ∈ I := by
    have h := I.sub_mem (I.sub_mem hsum hheadValue) hzValue
    convert h using 1
    rw [q.quadratic_add]
    ring
  have hscaledHead : w.bong.head = uniformizer K • b.head := by
    rw [← w.bong.ambientVector_zero_eq_head,
      w.ambientVector_zero, b.ambientVector_zero_eq_head]
    simp [uniformizerPowerUnit, coe_uniformizerUnit]
  have hrewritten :
      uniformizer K * ((2 : K) * q.bilin b.head z) ∈
        Lattice.principalIdeal (K := K)
          (uniformizer K * (uniformizer K * q.quadratic b.head)) := by
    dsimp only [I] at hcrossW
    rw [hscaledHead, q.quadratic_smul,
      LinearMap.BilinForm.smul_left] at hcrossW
    convert hcrossW using 1 <;> ring
  exact mem_principalIdeal_cancel_left (uniformizer_ne_zero K) hrewritten

/-- Values on the forward-rescaled lattice gain at least one uniformizer
relative to the old head value. -/
theorem quadratic_mem_shifted_head_ideal
    (w : b.HeadRescaleWitness 1) {z : V} (hz : z ∈ w.lattice) :
    q.quadratic z ∈ Lattice.principalIdeal (K := K)
      (uniformizer K * q.quadratic b.head) := by
  have hzHead : q.quadratic z ∈
      Lattice.principalIdeal (K := K) (q.quadratic w.bong.head) := by
    have h := Lattice.quadratic_mem_normIdeal_of_mem q w.lattice hz
    rw [w.bong.head_isNormGenerator.normIdeal_eq] at h
    exact h
  have hscaledHead : w.bong.head = uniformizer K • b.head := by
    rw [← w.bong.ambientVector_zero_eq_head,
      w.ambientVector_zero, b.ambientVector_zero_eq_head]
    simp [uniformizerPowerUnit, coe_uniformizerUnit]
  have hgenerator : q.quadratic w.bong.head ∈
      Lattice.principalIdeal (K := K)
        (uniformizer K * q.quadratic b.head) := by
    rw [hscaledHead, q.quadratic_smul]
    have hpi : uniformizer K ∈ IntegerRing K := by
      rw [mem_integerRing_iff, Dyadic.IsIntegral, ord_uniformizer]
      norm_num
    convert Lattice.mul_mem_principalIdeal_of_mem_integerRing
      (uniformizer K * q.quadratic b.head) (uniformizer K) hpi using 1 <;>
        ring
  have hle : Lattice.principalIdeal (K := K)
      (q.quadratic w.bong.head) ≤
      Lattice.principalIdeal (K := K)
        (uniformizer K * q.quadratic b.head) := by
    rw [Lattice.principalIdeal, Submodule.span_le]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hgenerator
  exact hle hzHead

/-- The literal one-step carrier calculation in Lemma 6.1(i).  Once the
full forward-rescaled BONG exists, no goodness hypothesis is needed for this
identity. -/
theorem mem_lattice_iff_ord_ge_head_add_one
    (w : b.HeadRescaleWitness 1) (y : V) :
    y ∈ w.lattice ↔
      y ∈ L ∧
        ((b.order 0 + 1 : Int) : WithTop Int) ≤ ord K (q.quadratic y) := by
  let t : K := uniformizer K * q.quadratic b.head
  have htNe : t ≠ 0 :=
    mul_ne_zero (uniformizer_ne_zero K) b.head_isAnisotropic
  have htOrder : ord K t =
      ((b.order 0 + 1 : Int) : WithTop Int) := by
    dsimp only [t]
    rw [ord_mul, ord_uniformizer,
      ← b.value_zero_eq_quadratic_head, ← b.coe_order]
    norm_cast
    omega
  constructor
  · intro hy
    refine ⟨w.lattice_le_original hy, ?_⟩
    rw [← htOrder]
    exact Lattice.ord_le_of_mem_principalIdeal htNe
      (w.quadratic_mem_shifted_head_ideal hy)
  · rintro ⟨hyL, hyOrder⟩
    have hyTarget : q.quadratic y ∈
        Lattice.principalIdeal (K := K) t := by
      apply Lattice.mem_principalIdeal_of_ord_le htNe
      rwa [htOrder]
    rcases w.exists_sub_head_mem hyL with ⟨z, hz, c, hzc⟩
    by_cases hcZero : c = 0
    · subst c
      have hzy : z = y := by simpa using hzc
      rwa [← hzy]
    rcases exists_eq_uniformizerInteger_pow_mul_unit K c hcZero with
      ⟨m, u, hfactor⟩
    by_cases hmZero : m = 0
    · subst m
      have hcUnit : IsValuationUnit K (c : K) := by
        have hu := Lattice.isValuationUnit_coe_integerRingUnit (K := K) u
        simpa [hfactor] using hu
      have hzTarget : q.quadratic z ∈
          Lattice.principalIdeal (K := K) t := by
        simpa only [t] using w.quadratic_mem_shifted_head_ideal hz
      have hcrossTarget :
          (c : K) * ((2 : K) * q.bilin b.head z) ∈
            Lattice.principalIdeal (K := K) t := by
        have hcross : (2 : K) * q.bilin b.head z ∈
            Lattice.principalIdeal (K := K) t := by
          simpa only [t] using w.two_bilin_mem_shifted_head_ideal hz
        exact (Lattice.principalIdeal (K := K) t).smul_mem c hcross
      have herror : q.quadratic z +
          (c : K) * ((2 : K) * q.bilin b.head z) ∈
            Lattice.principalIdeal (K := K) t :=
        (Lattice.principalIdeal (K := K) t).add_mem hzTarget hcrossTarget
      have hlead : (c : K) ^ 2 * q.quadratic b.head ∈
          Lattice.principalIdeal (K := K) t := by
        have hdiff :=
          (Lattice.principalIdeal (K := K) t).sub_mem hyTarget herror
        have hzcK : z + (c : K) • b.head = y := by
          change z + algebraMap (IntegerRing K) K c • b.head = y
          rw [IsScalarTower.algebraMap_smul K]
          exact hzc
        convert hdiff using 1
        rw [← hzcK, q.quadratic_add, q.quadratic_smul,
          LinearMap.BilinForm.smul_right]
        rw [q.isSymm.eq z b.head]
        ring
      have hleadOrder := Lattice.ord_le_of_mem_principalIdeal htNe hlead
      have hcOrder : ord K (c : K) = 0 := hcUnit
      have hquadraticOrder : ord K (q.quadratic b.head) =
          (b.order 0 : WithTop Int) := by
        rw [← b.value_zero_eq_quadratic_head, ← b.coe_order]
      have hleadOrderEq :
          ord K ((c : K) ^ 2 * q.quadratic b.head) =
            (b.order 0 : WithTop Int) := by
        rw [ord_mul, ord_pow, hcOrder, hquadraticOrder]
        simp
      have hbad : ((b.order 0 + 1 : Int) : WithTop Int) ≤
          (b.order 0 : WithTop Int) := by
        rwa [htOrder, hleadOrderEq] at hleadOrder
      have hbadInt : b.order 0 + 1 ≤ b.order 0 :=
        WithTop.coe_le_coe.mp hbad
      omega
    · have hmPos : 0 < m := Nat.pos_of_ne_zero hmZero
      let d : IntegerRing K :=
        uniformizerInteger K ^ (m - 1) * (u : IntegerRing K)
      have hcoeff : c = d * uniformizerInteger K := by
        have hpow : uniformizerInteger K ^ m =
            uniformizerInteger K ^ (m - 1) * uniformizerInteger K := by
          calc
            uniformizerInteger K ^ m =
                uniformizerInteger K ^ ((m - 1) + 1) := by congr 1 <;> omega
            _ = uniformizerInteger K ^ (m - 1) * uniformizerInteger K :=
              pow_succ _ _
        calc
          c = uniformizerInteger K ^ m * (u : IntegerRing K) := hfactor
          _ = (uniformizerInteger K ^ (m - 1) *
              (u : IntegerRing K)) * uniformizerInteger K := by
            rw [hpow]
            ring
          _ = d * uniformizerInteger K := rfl
      have hscaledHead : (uniformizerInteger K) • b.head =
          w.bong.head := by
        change uniformizer K • b.head = w.bong.head
        rw [← w.bong.ambientVector_zero_eq_head,
          w.ambientVector_zero, b.ambientVector_zero_eq_head]
        simp [uniformizerPowerUnit, coe_uniformizerUnit]
      have hcHead : c • b.head ∈ w.lattice := by
        rw [hcoeff, mul_smul, hscaledHead]
        exact w.lattice.smul_mem d w.bong.head_isNormGenerator.mem
      rw [← hzc]
      exact w.lattice.add_mem hz hcHead

/-- Away from the head, every rescaled order is the original order. -/
theorem order_eq_of_pos (w : b.HeadRescaleWitness k)
    (i : Fin (n + 2)) (hi : 0 < i.1) :
    w.bong.order i = b.order i := by
  let j : Fin (n + 1) := ⟨i.1 - 1, by omega⟩
  have hij : j.succ = i := by
    apply Fin.ext
    simp [j]
    omega
  rw [← hij]
  exact w.order_succ_eq j

/-- Iterating the one-step carrier calculation gives the full threshold in
Lemma 6.1(ii). -/
theorem mem_lattice_iff_ord_ge_head_depth
    (w : b.HeadRescaleWitness k) (y : V) :
    y ∈ w.lattice ↔
      y ∈ L ∧
        ((b.order 0 + 2 * (k : Int) - 1 : Int) : WithTop Int) ≤
          ord K (q.quadratic y) := by
  induction k with
  | zero =>
      have hlattice : w.lattice = L := by
        apply w.bong.lattice_eq_of_ambientVector_eq b
        intro i
        cases i using Fin.cases with
        | zero =>
            rw [w.ambientVector_zero]
            simp [uniformizerPowerUnit]
        | succ i => exact w.ambientVector_succ i
      rw [hlattice]
      constructor
      · intro hy
        refine ⟨hy, ?_⟩
        have hvalue := Lattice.quadratic_mem_normIdeal_of_mem q L hy
        rw [b.head_isNormGenerator.normIdeal_eq,
          ← b.value_zero_eq_quadratic_head] at hvalue
        have hminimum := Lattice.ord_le_of_mem_principalIdeal
          (b.value_ne_zero 0) hvalue
        rw [← b.coe_order] at hminimum
        have hlower :
            ((b.order 0 + 2 * ((0 : Nat) : Int) - 1 : Int) :
                WithTop Int) ≤ (b.order 0 : WithTop Int) := by
          norm_cast
          omega
        exact hlower.trans hminimum
      · exact And.left
  | succ k ih =>
      let predecessor := w.predecessor
      let step := w.asOneStepFromPredecessor
      have hstep := step.mem_lattice_iff_ord_ge_head_add_one y
      have hpredecessor := ih predecessor
      change y ∈ w.lattice ↔ _
      change y ∈ w.lattice ↔ _ at hstep
      rw [hstep, hpredecessor]
      have hpredecessorOrder :
          predecessor.bong.order 0 = b.order 0 + 2 * (k : Int) :=
        predecessor.order_zero_eq
      constructor
      · rintro ⟨⟨hy, _hold⟩, hnew⟩
        refine ⟨hy, ?_⟩
        rw [hpredecessorOrder] at hnew
        convert hnew using 1 <;> norm_cast <;> omega
      · rintro ⟨hy, hnew⟩
        refine ⟨⟨hy, ?_⟩, ?_⟩
        · have hthreshold :
              ((b.order 0 + 2 * (k : Int) - 1 : Int) : WithTop Int) ≤
                ((b.order 0 + 2 * ((k + 1 : Nat) : Int) - 1 : Int) :
                  WithTop Int) := by
              norm_cast
              omega
          exact hthreshold.trans hnew
        · rw [hpredecessorOrder]
          convert hnew using 1 <;> norm_cast <;> omega

/-- The only new two-step goodness inequality is the one starting at the
rescaled head. -/
theorem isGood_of_original
    (w : b.HeadRescaleWitness k) (hgood : b.IsGood)
    (hthird : ∀ _h : 1 ≤ n,
      b.order 0 + 2 * (k : Int) ≤ b.order ⟨2, by omega⟩) :
    w.bong.IsGood := by
  intro i hi
  by_cases hiZero : i.1 = 0
  · have hiEq : i = 0 := by
      apply Fin.ext
      exact hiZero
    subst i
    have hn : 1 ≤ n := by omega
    calc
      w.bong.order 0 = b.order 0 + 2 * (k : Int) := w.order_zero_eq
      _ ≤ b.order ⟨2, by omega⟩ := hthird hn
      _ = w.bong.order ⟨0 + 2, hi⟩ := by
        symm
        apply w.order_eq_of_pos
        norm_num
  · have hiPos : 0 < i.1 := Nat.pos_of_ne_zero hiZero
    calc
      w.bong.order i = b.order i := w.order_eq_of_pos i hiPos
      _ ≤ b.order ⟨i.1 + 2, hi⟩ := hgood i hi
      _ = w.bong.order ⟨i.1 + 2, hi⟩ := by
        exact (w.order_eq_of_pos ⟨i.1 + 2, hi⟩ (Nat.zero_lt_succ _)).symm

end HeadRescaleWitness

/-- The carrier calculation, stated for an already assembled full rescaling.
This is the internal strong form used after extending the binary hypothesis. -/
theorem beliLemma61_headDepth_of_fullRescale_proved
    (b : BONG V q L (n + 2)) (hgood : b.IsGood)
    (k : Nat) (hexists : b.HeadRescaleExists k)
    (hthird : ∀ _h : 1 ≤ n,
      b.order 0 + 2 * (k : Int) ≤ b.order ⟨2, by omega⟩) :
    Nonempty (HeadDepthWitness b k) := by
  rcases hexists with ⟨w⟩
  exact ⟨{
    lattice := w.lattice
    bong := w.bong
    ambientVector_zero := w.ambientVector_zero
    ambientVector_succ := w.ambientVector_succ
    mem_lattice_iff := w.mem_lattice_iff_ord_ge_head_depth
    good := w.isGood_of_original hgood hthird
  }⟩

/-- Beli (2003), Lemma 6.1(ii), with exactly the paper's binary initial-
segment existence hypothesis. -/
theorem beliLemma61_headDepth_proved
    (b : BONG V q L (n + 2)) (hgood : b.IsGood)
    (k : Nat) (hexists : b.HeadBinaryRescaleExists k)
    (hthird : ∀ _h : 1 ≤ n,
      b.order 0 + 2 * (k : Int) ≤ b.order ⟨2, by omega⟩) :
    Nonempty (HeadDepthWitness b k) := by
  rcases hexists with ⟨binary⟩
  let full := b.headRescaleWitness_of_binary k binary hthird
  exact b.beliLemma61_headDepth_of_fullRescale_proved hgood k ⟨full⟩ hthird

/-- The unconditional law instance for all dyadic local fields represented by
`DyadicContext`. -/
noncomputable instance beliLemma61LawsProved :
    BeliLemma61Laws.{u, v} K where
  headDepth := fun b hgood hexists hthird ↦
    beliLemma61_headDepth_proved b hgood _ hexists hthird
  headRescale_of_criterion := headBinaryRescaleExists_of_criterion_proved

end BONG

end Bong
