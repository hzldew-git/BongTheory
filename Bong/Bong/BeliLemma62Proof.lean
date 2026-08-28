/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma62
import Bong.Bong.Beli2019EnlargedProjection
import Bong.Bong.BeliCorollary44Proof
import Bong.Bong.TwoBlockProductIsometry
import Bong.Bong.BasisLattice
import Bong.Bong.Existence
import Bong.Lattice.MinimalScaleComponent
import Bong.Lattice.MixedPairing

/-!
# Proof of Beli (2003), Lemma 6.2

The inverse head rescaling is realized by the enlarged lattice from Beli
(2019), Lemma 5.7.  The value-set estimates are then proved by splitting off
the first one or two BONG vectors and applying the defect-adapted binary
calculation.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG

/-- The norm ideal of a nonempty BONG is the power ideal determined by its
explicit zeroth index.  This form avoids requiring an `OfNat (Fin m) 0`
instance when positivity of `m` is available only locally. -/
private theorem normIdeal_eq_powerIdeal_order_mk_zero {m : Nat}
    (b : BONG V q L m) (hm : 0 < m) :
    Lattice.normIdeal q L =
      Lattice.powerIdeal (K := K) (b.order ⟨0, hm⟩) := by
  cases m with
  | zero => omega
  | succ m =>
      have hindex : (⟨0, hm⟩ : Fin (m + 1)) = 0 := by
        apply Fin.ext
        rfl
      rw [hindex]
      calc
        Lattice.normIdeal q L =
            Lattice.principalIdeal (K := K) (q.quadratic b.head) :=
          b.head_isNormGenerator.normIdeal_eq
        _ = Lattice.principalIdeal (K := K) (b.valueUnit 0 : K) := by
          rw [b.coe_valueUnit, b.value_zero_eq_quadratic_head]
        _ = Lattice.powerIdeal (K := K)
            (ordUnit K (b.valueUnit 0)) :=
          Lattice.principalIdeal_eq_powerIdeal (b.valueUnit 0)
        _ = Lattice.powerIdeal (K := K) (b.order 0) := by
          rw [b.order_eq_ordUnit]

/-- A value-set estimate on the left block and an ideal bound on the right
block glue across an integral orthogonal two-block decomposition. -/
theorem TwoBlockSplitWitness.quadraticValueSet_subset_scaled_of_blocks
    {m cut : Nat} {b : BONG V q L m} {hcut : cut ≤ m}
    (S : b.TwoBlockSplitWitness cut hcut) (a : K)
    (I : Lattice.CoefficientIdeal (K := K))
    (hleft : Lattice.quadraticValueSet
        (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice ⊆
      Lattice.scaledIntegralSquareResidueSet a I)
    (hright : Lattice.quadraticValueSet
        (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice ⊆ I) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.scaledIntegralSquareResidueSet a I := by
  let F := S.toProductLatticeIsometry
  intro z hz
  rw [Lattice.mem_quadraticValueSet_iff] at hz
  rcases hz with ⟨y, hy, rfl⟩
  let xy := F.toLinearEquiv.symm y
  have hxy : xy ∈ Lattice.product S.left.lattice S.right.lattice := by
    apply (F.map_mem xy).mpr
    simpa [xy]
  have hxyParts := Lattice.mem_product_iff.mp hxy
  have hleftValue :
      (q.restrict S.left.carrier S.left.nondegenerate).quadratic xy.1 ∈
        Lattice.scaledIntegralSquareResidueSet a I := by
    apply hleft
    rw [Lattice.mem_quadraticValueSet_iff]
    exact ⟨xy.1, hxyParts.1, rfl⟩
  rcases hleftValue with ⟨x, hx⟩
  have hrightValue :
      (q.restrict S.right.carrier S.right.nondegenerate).quadratic xy.2 ∈ I := by
    apply hright
    rw [Lattice.mem_quadraticValueSet_iff]
    exact ⟨xy.2, hxyParts.2, rfl⟩
  refine ⟨x, ?_⟩
  have hmap := F.map_quadratic xy
  have hFxy : F.toLinearEquiv xy = y := by simp [xy]
  rw [← hFxy, hmap, QuadraticSpace.orthogonalSum_quadratic_apply]
  convert I.add_mem hx hrightValue using 1 <;> ring

/-- Scaled form of Corollary 3.10(a) for an arbitrary binary BONG. -/
theorem binary_quadraticValueSet_scaled_subset_powerIdeal_of_order_le
    (b : BONG V q L 2) (horder : b.order 0 ≤ b.order 1) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.scaledIntegralSquareResidueSet (b.value 0)
        (Lattice.powerIdeal (K := K) (b.order 1)) := by
  intro z hz
  rw [Lattice.mem_quadraticValueSet_iff] at hz
  rcases hz with ⟨y, hy, rfl⟩
  have hyBasis : y ∈ Lattice.basisLattice b.basis := by
    rw [← b.lattice_eq_basisLattice_of_order_le horder]
    exact hy
  have hyIntegral :=
    (Lattice.mem_basisLattice_iff_repr_mem_integerRing b.basis y).1 hyBasis
  let a : IntegerRing K := ⟨b.basis.repr y 0, hyIntegral 0⟩
  let c : IntegerRing K := ⟨b.basis.repr y 1, hyIntegral 1⟩
  refine ⟨a, ?_⟩
  have hprincipal :
      Lattice.principalIdeal (K := K) (b.value 1) =
        Lattice.powerIdeal (K := K) (b.order 1) := by
    calc
      Lattice.principalIdeal (K := K) (b.value 1) =
          Lattice.powerIdeal (K := K)
            (ordUnit K (b.valueUnit 1)) :=
        Lattice.principalIdeal_eq_powerIdeal (b.valueUnit 1)
      _ = Lattice.powerIdeal (K := K) (b.order 1) := by
        rw [b.order_eq_ordUnit]
  rw [b.quadratic_eq_binaryBasis_repr]
  have hmem :=
    (Lattice.principalIdeal (K := K) (b.value 1)).smul_mem
      (c ^ 2) (Lattice.generator_mem_principalIdeal (b.value 1))
  rw [hprincipal] at hmem
  convert hmem using 1 <;> simp [a, c, Algebra.smul_def, mul_comm]

/-- A lattice vector whose projection away from the first BONG vector has
nonzero norm lies in an integral binary slice with the same first value.  The
second value of the slice is represented by the original projected tail.
This is the precise geometric content of `J = O x₁ + O v` in Beli's proof. -/
theorem exists_binarySlice_for_value
    (b : BONG V q L (n + 1)) (v : V) (hv : v ∈ L)
    (hprojection :
      q.quadratic (q.orthogonalProjection b.head v) ≠ 0) :
    ∃ (C : Lattice.QuadraticSublattice q)
        (p : BONG C.carrier C.space C.lattice 2),
      p.value 0 = b.value 0 ∧
      p.value 1 ∈ Lattice.quadraticValueSet
        (q.orthogonalSpace b.head b.head_isAnisotropic)
        (L.projectedLattice q b.head b.head_isAnisotropic) ∧
      q.quadratic v ∈
        Lattice.quadraticValueSet C.space C.lattice := by
  classical
  let x : V := b.head
  let u : V := q.orthogonalProjection x v
  have hxAn : q.IsAnisotropic x := b.head_isAnisotropic
  have huNe : u ≠ 0 := by
    intro hu
    apply hprojection
    change q.quadratic u = 0
    rw [hu]
    exact q.quadratic_zero
  have hli : LinearIndependent K (binaryPairFamily x v) := by
    rw [linearIndependent_fin2]
    constructor
    · intro hvzero
      change v = 0 at hvzero
      apply huNe
      dsimp only [u]
      rw [hvzero]
      simp
    · intro a havx
      change a • v = x at havx
      have hp := congrArg (q.orthogonalProjection x) havx
      have hprojx : q.orthogonalProjection x x = 0 :=
        q.orthogonalProjection_self hxAn
      have hau : a • u = 0 := by
        simpa only [u, map_smul, hprojx] using hp
      rcases smul_eq_zero.mp hau with ha | hu
      · rw [ha, zero_smul] at havx
        exact hxAn.ne_zero havx.symm
      · exact huNe hu
  let P := binaryPairSpan (K := K) x v
  let pairBasis : Basis (Fin 2) K P :=
    binaryPairBasis (K := K) x v hli
  have hnondeg : (q.bilin.restrict P).Nondegenerate := by
    apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero pairBasis).2
    rw [Matrix.det_fin_two]
    simp only [LinearMap.BilinForm.toMatrix_apply,
      LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
    rw [show ((pairBasis 0 : P) : V) = x by
        calc
          ((pairBasis 0 : P) : V) = binaryPairFamily x v 0 :=
            coe_binaryPairBasis x v hli 0
          _ = x := binaryPairFamily_zero x v,
      show ((pairBasis 1 : P) : V) = v by
        calc
          ((pairBasis 1 : P) : V) = binaryPairFamily x v 1 :=
            coe_binaryPairBasis x v hli 1
          _ = v := binaryPairFamily_one x v,
      q.isSymm.eq v x]
    have hdecomp := Lattice.quadratic_projection_decomposition q x hxAn v
    have hxNe : q.quadratic x ≠ 0 := hxAn
    intro hdet
    apply hprojection
    have hdet' :
        q.quadratic x * q.quadratic v - q.bilin x v ^ 2 = 0 := by
      simpa only [QuadraticSpace.quadratic, pow_two] using hdet
    have hid :
        q.quadratic x * q.quadratic v - q.bilin x v ^ 2 =
          q.quadratic x * q.quadratic (q.orthogonalProjection x v) := by
      rw [hdecomp]
      field_simp [hxNe]
      ring
    rw [hid] at hdet'
    simpa only [x] using (mul_eq_zero.mp hdet').resolve_left hxNe
  let C : Lattice.QuadraticSublattice q :=
    Lattice.basisQuadraticSublattice P hnondeg pairBasis
  have hcontained : C.ambientSubmodule ≤ L.toSubmodule := by
    apply Lattice.basisQuadraticSublattice_ambientSubmodule_le
    intro i
    rw [show ((pairBasis i : P) : V) = binaryPairFamily x v i by
      exact coe_binaryPairBasis x v hli i]
    fin_cases i
    · exact b.head_isNormGenerator.mem
    · exact hv
  have hxP : x ∈ P := by
    apply Submodule.subset_span
    exact ⟨0, binaryPairFamily_zero x v⟩
  let X : C.carrier := ⟨x, hxP⟩
  have hXmem : X ∈ C.lattice := by
    change X ∈ Lattice.basisLattice pairBasis
    change X ∈ Submodule.span (IntegerRing K) (Set.range pairBasis)
    apply Submodule.subset_span
    refine ⟨0, ?_⟩
    apply Subtype.ext
    exact coe_binaryPairBasis x v hli 0
  have hXAn : C.space.IsAnisotropic X := by
    change q.quadratic x ≠ 0
    exact hxAn
  have hXgen : Lattice.IsNormGenerator C.space C.lattice X := by
    refine ⟨hXmem, ?_⟩
    apply le_antisymm
    · calc
        Lattice.normIdeal C.space C.lattice ≤
            Lattice.normIdeal q L :=
          C.normIdeal_le_of_ambientSubmodule_le hcontained
        _ = Lattice.principalIdeal (K := K) (q.quadratic x) :=
          b.head_isNormGenerator.normIdeal_eq
        _ = Lattice.principalIdeal (K := K)
            (C.space.quadratic X) := by rfl
    · rw [Lattice.principalIdeal, Submodule.span_le]
      rintro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact Lattice.quadratic_mem_normIdeal_of_mem C.space C.lattice hXmem
  have hfin : Module.finrank K C.carrier = 2 := by
    change Module.finrank K P = 2
    simpa using Module.finrank_eq_card_basis pairBasis
  let p : BONG C.carrier C.space C.lattice 2 :=
    BONG.ofNormGeneratorBinary C.space C.lattice X hXgen hXAn hfin
  have hpHead : p.head = X := by
    exact BONG.head_ofNormGeneratorBinary C.space C.lattice X hXgen hXAn hfin
  have hpValueZero : p.value 0 = b.value 0 := by
    rw [p.value_zero_eq_quadratic_head, hpHead,
      b.value_zero_eq_quadratic_head]
    rfl
  have hvP : v ∈ P := by
    apply Submodule.subset_span
    exact ⟨1, binaryPairFamily_one x v⟩
  let vP : C.carrier := ⟨v, hvP⟩
  have hvPmem : vP ∈ C.lattice := by
    change vP ∈ Lattice.basisLattice pairBasis
    change vP ∈ Submodule.span (IntegerRing K) (Set.range pairBasis)
    apply Submodule.subset_span
    refine ⟨1, ?_⟩
    apply Subtype.ext
    exact coe_binaryPairBasis x v hli 1
  have hvValue : q.quadratic v ∈
      Lattice.quadraticValueSet C.space C.lattice := by
    rw [Lattice.mem_quadraticValueSet_iff]
    exact ⟨vP, hvPmem, rfl⟩
  have htailHeadMem := p.tail.head_isNormGenerator.mem
  rcases (Lattice.mem_projectedLattice_iff C.space C.lattice p.head
      p.head_isAnisotropic p.tail.head).1 htailHeadMem with
    ⟨zP, hzP, hprojectionP⟩
  have hzAmbient : ((zP : C.carrier) : V) ∈ L := by
    apply hcontained
    exact ⟨zP, hzP, rfl⟩
  let tailHeadP : C.carrier := (p.tail.head : C.carrier)
  let tailHeadV : V := (tailHeadP : V)
  have htailOrthogonal : q.bilin x tailHeadV = 0 := by
    have h := (C.space.mem_vectorOrthogonal_iff p.head tailHeadP).1
      p.tail.head.property
    change q.bilin ((p.head : C.carrier) : V) tailHeadV = 0 at h
    rw [hpHead] at h
    exact h
  let tailHead : q.vectorOrthogonal b.head :=
    ⟨tailHeadV, by
      apply (q.mem_vectorOrthogonal_iff b.head tailHeadV).2
      simpa only [x] using htailOrthogonal⟩
  have hprojectionAmbient :
      q.projectionToOrthogonal b.head b.head_isAnisotropic
          ((zP : C.carrier) : V) = tailHead := by
    apply Subtype.ext
    have hp := congrArg Subtype.val hprojectionP
    change C.space.orthogonalProjection p.head zP = tailHeadP at hp
    rw [hpHead] at hp
    rw [C.space.orthogonalProjection_apply] at hp
    have hpV := congrArg Subtype.val hp
    change q.orthogonalProjection b.head ((zP : C.carrier) : V) =
      tailHeadV
    rw [q.orthogonalProjection_apply]
    have hquadX : C.space.quadratic X = q.quadratic b.head := by rfl
    change ((zP : C.carrier) : V) -
        (q.bilin b.head ((zP : C.carrier) : V) /
          C.space.quadratic X) • b.head = tailHeadV at hpV
    rw [hquadX] at hpV
    exact hpV
  have htailHeadMemAmbient : tailHead ∈
      L.projectedLattice q b.head b.head_isAnisotropic := by
    rw [Lattice.mem_projectedLattice_iff]
    exact ⟨((zP : C.carrier) : V), hzAmbient, hprojectionAmbient⟩
  have htailValue :
      p.value 1 =
        (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic tailHead := by
    calc
      p.value 1 = p.tail.value 0 := (p.value_tail 0).symm
      _ = C.space.quadratic tailHeadP :=
        p.tail.value_zero_eq_quadratic_head
      _ = (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          tailHead := by rfl
  refine ⟨C, p, hpValueZero, ?_, hvValue⟩
  rw [Lattice.mem_quadraticValueSet_iff]
  exact ⟨tailHead, htailHeadMemAmbient, htailValue.symm⟩

/-- If the orthogonal remainder of a lattice vector has zero quadratic value,
then its value is already an integral square multiple of the first BONG value.
This includes nonzero isotropic remainders; no anisotropy of the orthogonal
complement is assumed. -/
theorem quadraticValue_mem_scaled_of_projection_quadratic_zero
    (b : BONG V q L (n + 1)) (v : V) (hv : v ∈ L)
    (hprojection :
      q.quadratic (q.orthogonalProjection b.head v) = 0)
    (I : Lattice.CoefficientIdeal (K := K)) :
    q.quadratic v ∈
      Lattice.scaledIntegralSquareResidueSet (b.value 0) I := by
  let a : K := q.bilin b.head v / q.quadratic b.head
  have hdecomp := Lattice.quadratic_projection_decomposition
    q b.head b.head_isAnisotropic v
  have hvalue : q.quadratic v = b.value 0 * a ^ 2 := by
    rw [hdecomp, hprojection, add_zero,
      b.value_zero_eq_quadratic_head]
    dsimp only [a]
    ring
  have hvNorm := Lattice.quadratic_mem_normIdeal_of_mem q L hv
  rw [b.head_isNormGenerator.normIdeal_eq] at hvNorm
  have haSq : a ^ 2 ∈ IntegerRing K := by
    apply Lattice.mem_integerRing_of_mul_mem_principalIdeal
      b.head_isAnisotropic
    convert hvNorm using 1
    rw [hvalue, b.value_zero_eq_quadratic_head]
  let aIntegral : IntegerRing K :=
    ⟨a, Lattice.mem_integerRing_of_sq_mem_integerRing haSq⟩
  refine ⟨aIntegral, ?_⟩
  rw [hvalue]
  change b.value 0 * a ^ 2 - b.value 0 * a ^ 2 ∈ I
  simpa only [sub_self] using I.zero_mem

/-- The actual enlarged lattice and BONG used in Beli (2003), Lemma 6.2(i). -/
noncomputable def headInverseRescaleWitness
    (b : BONG V q L (n + 2)) : b.HeadInverseRescaleWitness := by
  let y : V := b.head
  let enlargedHead : V := lemma57EnlargedHead (K := K) y 1
  have enlargedGenerator : Lattice.IsNormGenerator q
      (lemma57EnlargedLattice L y 1) enlargedHead := by
    exact lemma57EnlargedHead_isNormGenerator q b.head_isNormGenerator (by omega)
  have enlargedAnisotropic : q.IsAnisotropic enlargedHead := by
    exact lemma57EnlargedHead_isAnisotropic q b.head_isAnisotropic 1
  let projectedIsometry :=
    lemma57ProjectedIsometry q L b.head_isAnisotropic 1
  let enlargedTail : BONG (q.vectorOrthogonal enlargedHead)
      (q.orthogonalSpace enlargedHead enlargedAnisotropic)
      (Lattice.projectedLattice q (lemma57EnlargedLattice L y 1)
        enlargedHead enlargedAnisotropic) (n + 1) :=
    b.tail.mapLatticeIsometry projectedIsometry.symm
  let enlargedBONG : BONG V q (lemma57EnlargedLattice L y 1) (n + 2) :=
    BONG.cons enlargedHead enlargedGenerator enlargedAnisotropic enlargedTail
  refine {
    lattice := lemma57EnlargedLattice L y 1
    bong := enlargedBONG
    ambientVector_zero := ?_
    ambientVector_succ := ?_
  }
  · simp only [enlargedBONG, BONG.ambientVector_cons_zero]
    change (uniformizerPowerUnit K (-1) : K) • b.head =
      (uniformizerPowerUnit K (-1) : K) • b.ambientVector 0
    rw [b.ambientVector_zero_eq_head]
  · intro i
    simp only [enlargedBONG, BONG.ambientVector_cons_succ]
    change ((enlargedTail.ambientVector i :
      q.vectorOrthogonal enlargedHead) : V) = b.ambientVector i.succ
    rw [show enlargedTail =
        b.tail.mapLatticeIsometry projectedIsometry.symm by rfl,
      BONG.ambientVector_mapLatticeIsometry]
    have hprojected :
        ((projectedIsometry.symm.toLinearEquiv
          (b.tail.ambientVector i) : q.vectorOrthogonal enlargedHead) : V) =
          (b.tail.ambientVector i : V) := by
      rfl
    rw [hprojected, BONG.coe_ambientVector_tail]

theorem headInverseRescaleExists_proved (b : BONG V q L (n + 2)) :
    Nonempty b.HeadInverseRescaleWitness :=
  ⟨b.headInverseRescaleWitness⟩

namespace HeadInverseRescaleWitness

variable {b : BONG V q L (n + 2)} (w : b.HeadInverseRescaleWitness)

/-- Unit-valued form of the first-value rescaling. -/
theorem valueUnit_zero_proved :
    w.bong.valueUnit 0 =
      uniformizerPowerUnit K (-1) ^ 2 * b.valueUnit 0 := by
  apply Units.ext
  simpa only [coe_valueUnit, Units.val_mul, Units.val_pow_eq_pow_val] using
    w.value_zero

/-- Unit-valued form of the unchanged tail values. -/
theorem valueUnit_succ_proved (i : Fin (n + 1)) :
    w.bong.valueUnit i.succ = b.valueUnit i.succ := by
  apply Units.ext
  simpa only [coe_valueUnit] using w.value_succ i

/-- Inverse rescaling of the head multiplies the first adjacent parameter by
the square of a uniformizer. -/
theorem adjacentParameter_zero_proved :
    w.bong.adjacentParameter 0 (by simp) =
      uniformizerPowerUnit K 1 ^ 2 *
        b.adjacentParameter 0 (by simp) := by
  have hzero := w.valueUnit_zero_proved
  have hone := w.valueUnit_succ_proved (0 : Fin (n + 1))
  unfold adjacentParameter
  change w.bong.valueUnit (Fin.succ (0 : Fin (n + 1))) /
      w.bong.valueUnit 0 =
    uniformizerPowerUnit K 1 ^ 2 *
      (b.valueUnit (Fin.succ (0 : Fin (n + 1))) / b.valueUnit 0)
  rw [hone, hzero]
  unfold uniformizerPowerUnit
  simp [div_eq_mul_inv, zpow_neg]
  ac_rfl

/-- Hence the relative quadratic defect of the first adjacent parameter is
unchanged by inverse head rescaling. -/
theorem beliParameterDefect_adjacentParameter_zero_proved :
    beliParameterDefect K (w.bong.adjacentParameter 0 (by simp)) =
      beliParameterDefect K (b.adjacentParameter 0 (by simp)) := by
  rw [w.adjacentParameter_zero_proved]
  unfold beliParameterDefect
  calc
    quadraticDefect K
        (-(uniformizerPowerUnit K 1 ^ 2 *
          b.adjacentParameter 0 (by simp))) =
        quadraticDefect K
          (-(b.adjacentParameter 0 (by simp)) *
            uniformizerPowerUnit K 1 ^ 2) := by
      congr 1
      apply Units.ext
      simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    _ = quadraticDefect K (-(b.adjacentParameter 0 (by simp))) :=
      quadraticDefect_mul_square K
        (-(b.adjacentParameter 0 (by simp))) (uniformizerPowerUnit K 1)

/-- The first adjacent order gap increases by two under inverse head
rescaling. -/
theorem lemma62Gap_eq_add_two :
    w.bong.lemma62Gap = b.lemma62Gap + 2 := by
  unfold lemma62Gap
  change w.bong.order (Fin.succ (0 : Fin (n + 1))) - w.bong.order 0 =
    b.order (Fin.succ (0 : Fin (n + 1))) - b.order 0 + 2
  rw [w.order_succ (0 : Fin (n + 1)), w.order_zero]
  omega

/-- After deleting the rescaled head, all remaining unit-valued entries
agree with the original tail. -/
theorem tail_valueUnit_eq (i : Fin (n + 1)) :
    w.bong.tail.valueUnit i = b.tail.valueUnit i := by
  apply Units.ext
  simp only [coe_valueUnit, value_tail]
  exact congrArg Units.val (w.valueUnit_succ_proved i)

/-- Consequently all tail orders agree. -/
theorem tail_order_eq (i : Fin (n + 1)) :
    w.bong.tail.order i = b.tail.order i := by
  rw [order_tail, order_tail, w.order_succ i]

/-- Consequently all normalized tail values agree. -/
theorem tail_normalizedValue_eq (i : Fin (n + 1)) :
    w.bong.tail.normalizedValue i = b.tail.normalizedValue i := by
  unfold normalizedValue
  rw [w.tail_valueUnit_eq i, w.tail_order_eq i]

/-- The normalized adjacent defects of the two tails agree. -/
theorem tail_normalizedAdjacentDefectOrder_eq (i : Fin n) :
    w.bong.tail.normalizedAdjacentDefectOrder i =
      b.tail.normalizedAdjacentDefectOrder i := by
  unfold normalizedAdjacentDefectOrder normalizedAdjacentProduct
  congr 2
  rw [w.tail_normalizedValue_eq i.castSucc,
    w.tail_normalizedValue_eq i.succ]

end HeadInverseRescaleWitness

/-- Local proof that Property B passes to the tail, kept here below the
Section 4 dependency boundary needed by Lemma 6.2. -/
theorem HasPropertyB.tail_for_lemma62
    {b : BONG V q L (n + 2)} (hB : b.HasPropertyB) :
    b.tail.HasPropertyB :=
  hB.tail

namespace HeadInverseRescaleWitness

variable {b : BONG V q L (n + 2)} (w : b.HeadInverseRescaleWitness)

/-- Property B on the rescaled BONG induces Property B on the original
tail, since rescaling changes only the deleted head. -/
theorem originalTail_hasPropertyB_of_rescaled
    (hB : w.bong.HasPropertyB) : b.tail.HasPropertyB := by
  have htail := hB.tail_for_lemma62
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [← w.tail_order_eq i,
      ← w.tail_order_eq ⟨i.1 + 2, hi⟩]
    exact htail.hasPropertyA i hi
  · intro i hi
    have hi' : w.bong.tail.propertyBTrigger i := by
      unfold propertyBTrigger at hi ⊢
      rw [w.tail_order_eq i.succ, w.tail_order_eq i.castSucc,
        w.tail_normalizedAdjacentDefectOrder_eq i]
      exact hi
    rcases htail.2 i hi' with ⟨hleft, hright⟩
    constructor
    · intro j hj
      rw [← w.tail_order_eq i.castSucc, ← w.tail_order_eq j]
      exact hleft j hj
    · intro k hk
      rw [← w.tail_order_eq k, ← w.tail_order_eq i.succ]
      exact hright k hk

end HeadInverseRescaleWitness

/-- Either branch of the Lemma 6.2 hypothesis therefore gives Property B
on the original recursive tail. -/
theorem HasPropertyBOrInverse.tail_hasPropertyB
    {b : BONG V q L (n + 2)} {w : b.HeadInverseRescaleWitness}
    (hB : b.HasPropertyBOrInverse w) : b.tail.HasPropertyB := by
  rcases hB with hB | hB
  · exact hB.tail_for_lemma62
  · exact w.originalTail_hasPropertyB_of_rescaled hB

/-- Beli (2003), Lemma 6.2(ii)(a), with the Corollary 4.4 split constructed
from goodness. -/
theorem lemma62_quadraticValues_a_proved
    (b : BONG V q L (n + 2)) (w : b.HeadInverseRescaleWitness)
    (hB : b.HasPropertyBOrInverse w) (hgap : b.order 0 ≤ b.order 1) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.scaledIntegralSquareResidueSet (b.value 0)
        (Lattice.powerIdeal (K := K) (b.order 1)) := by
  rcases b.beliCorollary44_i_unconditional hB.isGood 0 (by simp) hgap with ⟨S⟩
  let F := S.toProductLatticeIsometry
  intro z hz
  rw [Lattice.mem_quadraticValueSet_iff] at hz
  rcases hz with ⟨y, hy, rfl⟩
  let xy := F.toLinearEquiv.symm y
  have hxy : xy ∈ Lattice.product S.left.lattice S.right.lattice := by
    apply (F.map_mem xy).mpr
    simpa [xy]
  have hxyParts := (Lattice.mem_product_iff.mp hxy)
  let yLeft : S.left.lattice.toSubmodule := ⟨xy.1, hxyParts.1⟩
  let a : IntegerRing K := S.left.bong.integralBasisFinOne.repr yLeft 0
  have hleftVector : (xy.1 : S.left.carrier) =
      (a : K) • S.left.bong.head := by
    have hrepr := S.left.bong.integralBasisFinOne.sum_repr yLeft
    rw [Fin.sum_univ_one] at hrepr
    change a • S.left.bong.integralBasisFinOne 0 = yLeft at hrepr
    have hcoe := congrArg
      (fun z : S.left.lattice.toSubmodule ↦
        (((z : S.left.carrier) : V))) hrepr
    apply Subtype.ext
    calc
      (((xy.1 : S.left.carrier) : V)) =
          (((a • S.left.bong.integralBasisFinOne 0 :
            S.left.lattice.toSubmodule) : S.left.carrier) : V) := hcoe.symm
      _ = (a : K) •
          (((S.left.bong.integralBasisFinOne 0 :
            S.left.lattice.toSubmodule) : S.left.carrier) : V) := by
        rfl
      _ = (a : K) • ((S.left.bong.head : S.left.carrier) : V) := by
        rw [S.left.bong.coe_integralBasisFinOne_zero]
        rfl
  have hleftValue : S.left.bong.value 0 = b.value 0 := by
    simpa [SegmentWitness.sourceIndex] using S.left.value_eq (0 : Fin 1)
  have hleftQuadratic :
      (q.restrict S.left.carrier S.left.nondegenerate).quadratic xy.1 =
        b.value 0 * (a : K) ^ 2 := by
    rw [hleftVector,
      (q.restrict S.left.carrier S.left.nondegenerate).quadratic_smul,
      ← S.left.bong.value_zero_eq_quadratic_head, hleftValue]
    ring
  let j0 : Fin (n + 2 - (0 + 1)) := ⟨0, by omega⟩
  have hrightOrder : S.right.bong.order j0 = b.order 1 := by
    simpa [j0, SegmentWitness.sourceIndex] using S.right.order_eq j0
  have hrightIdeal :
      (q.restrict S.right.carrier S.right.nondegenerate).quadratic xy.2 ∈
        Lattice.powerIdeal (K := K) (b.order 1) := by
    have hmem := Lattice.quadratic_mem_normIdeal_of_mem
      (q.restrict S.right.carrier S.right.nondegenerate)
      S.right.lattice hxyParts.2
    have hnorm : Lattice.normIdeal
        (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice =
          Lattice.powerIdeal (K := K) (S.right.bong.order j0) := by
      have hrightPos : 0 < n + 2 - ((0 : Fin (n + 2)).1 + 1) := by
        simp
      simpa [j0] using
        normIdeal_eq_powerIdeal_order_mk_zero S.right.bong hrightPos
    rw [hnorm, hrightOrder] at hmem
    exact hmem
  refine ⟨a, ?_⟩
  have hmap := F.map_quadratic xy
  have hFxy : F.toLinearEquiv xy = y := by simp [xy]
  rw [← hFxy, hmap, QuadraticSpace.orthogonalSum_quadratic_apply,
    hleftQuadratic]
  convert hrightIdeal using 1
  ring

/-- Corollary 3.10 on any realized initial binary segment, translated to the
ambient orders and first value. -/
theorem lemma62_segmentBinaryValues_b
    (b : BONG V q L (n + 2))
    (p : SegmentWitness b 0 2 (by omega))
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hdefect : beliParameterDefect K
        (b.adjacentParameter 0 (by simp)) ≤
      (b.lemma62DefectCutoff : ℕ∞)) :
    ∀ z ∈ Lattice.quadraticValueSet
        (q.restrict p.carrier p.nondegenerate) p.lattice,
      ∃ x : IntegerRing K,
        z - b.value 0 * (x : K) ^ 2 ∈
          Lattice.powerIdeal (K := K) b.lemma62LowExponent := by
  have hgap : p.bong.binaryOrderGap = b.lemma62Gap := by
    unfold binaryOrderGap lemma62Gap
    rw [p.order_eq, p.order_eq]
    simp [SegmentWitness.sourceIndex]
  have hparameter : p.bong.binaryParameter =
      b.adjacentParameter 0 (by simp) := by
    unfold binaryParameter adjacentParameter
    rw [p.valueUnit_eq, p.valueUnit_eq]
    congr 2
  have horderZero : p.bong.order 0 = b.order 0 := by
    simpa [SegmentWitness.sourceIndex] using p.order_eq (0 : Fin 2)
  have hvalueZero : p.bong.value 0 = b.value 0 := by
    simpa [SegmentWitness.sourceIndex] using p.value_eq (0 : Fin 2)
  have hcutoff : binaryCorollaryDefectCutoff p.bong =
      b.lemma62DefectCutoff := by
    unfold binaryCorollaryDefectCutoff lemma62DefectCutoff
    rw [hgap]
  have hp := p.bong.quadraticValueSet_scaled_subset_powerIdeal_of_low_defect
    (by simpa [hgap] using heven)
    (by simpa [hgap] using hupper)
    (by simpa [hparameter, hcutoff] using hdefect)
  have hexponent :
      p.bong.order 0 +
          (p.bong.binaryOrderGap +
            (beliParameterDefectNat K p.bong.binaryParameter : Int)) =
        b.lemma62LowExponent := by
    rw [horderZero, hgap, hparameter]
    unfold lemma62LowExponent lemma62Gap lemma62DefectNat
    omega
  intro z hz
  rcases hp z hz with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  rwa [hvalueZero, hexponent] at hx

/-- The initial binary segment has the low-defect estimate of Lemma 6.2(b),
with all relative Corollary 3.10 exponents translated back to the ambient
BONG orders. -/
theorem lemma62_prefixBinaryValues_b
    (b : BONG V q L (n + 2))
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hdefect : beliParameterDefect K
        (b.adjacentParameter 0 (by simp)) ≤
      (b.lemma62DefectCutoff : ℕ∞)) :
    let p := b.prefixWitness 2 (by omega)
    ∀ z ∈ Lattice.quadraticValueSet
        (q.restrict p.carrier p.nondegenerate) p.lattice,
      ∃ x : IntegerRing K,
        z - b.value 0 * (x : K) ^ 2 ∈
          Lattice.powerIdeal (K := K) b.lemma62LowExponent := by
  let p := b.prefixWitness 2 (by omega)
  change ∀ z ∈ Lattice.quadraticValueSet
      (q.restrict p.carrier p.nondegenerate) p.lattice,
    ∃ x : IntegerRing K,
      z - b.value 0 * (x : K) ^ 2 ∈
        Lattice.powerIdeal (K := K) b.lemma62LowExponent
  have hgap : p.bong.binaryOrderGap = b.lemma62Gap := by
    unfold binaryOrderGap lemma62Gap
    rw [p.order_eq, p.order_eq]
    simp [SegmentWitness.sourceIndex]
  have hparameter : p.bong.binaryParameter =
      b.adjacentParameter 0 (by simp) := by
    unfold binaryParameter adjacentParameter
    rw [p.valueUnit_eq, p.valueUnit_eq]
    congr 2 <;> apply Fin.ext <;> simp [SegmentWitness.sourceIndex]
  have horderZero : p.bong.order 0 = b.order 0 := by
    simpa [SegmentWitness.sourceIndex] using p.order_eq (0 : Fin 2)
  have hvalueZero : p.bong.value 0 = b.value 0 := by
    simpa [SegmentWitness.sourceIndex] using p.value_eq (0 : Fin 2)
  have hcutoff : binaryCorollaryDefectCutoff p.bong =
      b.lemma62DefectCutoff := by
    unfold binaryCorollaryDefectCutoff lemma62DefectCutoff
    rw [hgap]
  have hp := p.bong.quadraticValueSet_scaled_subset_powerIdeal_of_low_defect
    (by simpa [hgap] using heven)
    (by simpa [hgap] using hupper)
    (by simpa [hparameter, hcutoff] using hdefect)
  have hexponent :
      p.bong.order 0 +
          (p.bong.binaryOrderGap +
            (beliParameterDefectNat K p.bong.binaryParameter : Int)) =
        b.lemma62LowExponent := by
    rw [horderZero, hgap, hparameter]
    unfold lemma62LowExponent lemma62Gap lemma62DefectNat
    omega
  intro z hz
  rcases hp z hz with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  rwa [hvalueZero, hexponent] at hx

/-- The initial binary segment has the high-defect estimate of Lemma 6.2(c),
again expressed with the ambient absolute exponent. -/
theorem lemma62_prefixBinaryValues_c
    (b : BONG V q L (n + 2))
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hdefect : (b.lemma62DefectCutoff : ℕ∞) ≤
      beliParameterDefect K (b.adjacentParameter 0 (by simp))) :
    let p := b.prefixWitness 2 (by omega)
    ∀ z ∈ Lattice.quadraticValueSet
        (q.restrict p.carrier p.nondegenerate) p.lattice,
      ∃ x : IntegerRing K,
        z - b.value 0 * (x : K) ^ 2 ∈
          Lattice.powerIdeal (K := K) b.lemma62HighExponent := by
  let p := b.prefixWitness 2 (by omega)
  change ∀ z ∈ Lattice.quadraticValueSet
      (q.restrict p.carrier p.nondegenerate) p.lattice,
    ∃ x : IntegerRing K,
      z - b.value 0 * (x : K) ^ 2 ∈
        Lattice.powerIdeal (K := K) b.lemma62HighExponent
  have hgap : p.bong.binaryOrderGap = b.lemma62Gap := by
    unfold binaryOrderGap lemma62Gap
    rw [p.order_eq, p.order_eq]
    simp [SegmentWitness.sourceIndex]
  have hparameter : p.bong.binaryParameter =
      b.adjacentParameter 0 (by simp) := by
    unfold binaryParameter adjacentParameter
    rw [p.valueUnit_eq, p.valueUnit_eq]
    congr 2 <;> apply Fin.ext <;> simp [SegmentWitness.sourceIndex]
  have horderZero : p.bong.order 0 = b.order 0 := by
    simpa [SegmentWitness.sourceIndex] using p.order_eq (0 : Fin 2)
  have hvalueZero : p.bong.value 0 = b.value 0 := by
    simpa [SegmentWitness.sourceIndex] using p.value_eq (0 : Fin 2)
  have hcutoff : binaryCorollaryDefectCutoff p.bong =
      b.lemma62DefectCutoff := by
    unfold binaryCorollaryDefectCutoff lemma62DefectCutoff
    rw [hgap]
  have hp := p.bong.quadraticValueSet_scaled_subset_powerIdeal_of_high_defect
    (by simpa [hgap] using heven)
    (by simpa [hgap] using hupper)
    (by simpa [hparameter, hcutoff] using hdefect)
  have hexponent :
      p.bong.order 0 +
          ((ramificationIndex K : Int) +
            p.bong.binaryOrderGap / 2) =
        b.lemma62HighExponent := by
    rw [horderZero, hgap]
    unfold lemma62HighExponent lemma62Gap
    rcases heven with ⟨r, hr⟩
    omega
  intro z hz
  rcases hp z hz with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  rwa [hvalueZero, hexponent] at hx

/-- Corollary 3.10 on any realized initial binary segment in the high-defect
branch, again translated to ambient data. -/
theorem lemma62_segmentBinaryValues_c
    (b : BONG V q L (n + 2))
    (p : SegmentWitness b 0 2 (by omega))
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hdefect : (b.lemma62DefectCutoff : ℕ∞) ≤
      beliParameterDefect K (b.adjacentParameter 0 (by simp))) :
    ∀ z ∈ Lattice.quadraticValueSet
        (q.restrict p.carrier p.nondegenerate) p.lattice,
      ∃ x : IntegerRing K,
        z - b.value 0 * (x : K) ^ 2 ∈
          Lattice.powerIdeal (K := K) b.lemma62HighExponent := by
  have hgap : p.bong.binaryOrderGap = b.lemma62Gap := by
    unfold binaryOrderGap lemma62Gap
    rw [p.order_eq, p.order_eq]
    simp [SegmentWitness.sourceIndex]
  have hparameter : p.bong.binaryParameter =
      b.adjacentParameter 0 (by simp) := by
    unfold binaryParameter adjacentParameter
    rw [p.valueUnit_eq, p.valueUnit_eq]
    congr 2
  have horderZero : p.bong.order 0 = b.order 0 := by
    simpa [SegmentWitness.sourceIndex] using p.order_eq (0 : Fin 2)
  have hvalueZero : p.bong.value 0 = b.value 0 := by
    simpa [SegmentWitness.sourceIndex] using p.value_eq (0 : Fin 2)
  have hcutoff : binaryCorollaryDefectCutoff p.bong =
      b.lemma62DefectCutoff := by
    unfold binaryCorollaryDefectCutoff lemma62DefectCutoff
    rw [hgap]
  have hp := p.bong.quadraticValueSet_scaled_subset_powerIdeal_of_high_defect
    (by simpa [hgap] using heven)
    (by simpa [hgap] using hupper)
    (by simpa [hparameter, hcutoff] using hdefect)
  have hexponent :
      p.bong.order 0 +
          ((ramificationIndex K : Int) +
            p.bong.binaryOrderGap / 2) =
        b.lemma62HighExponent := by
    rw [horderZero, hgap]
    unfold lemma62HighExponent lemma62Gap
    rcases heven with ⟨r, hr⟩
    omega
  intro z hz
  rcases hp z hz with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  rwa [hvalueZero, hexponent] at hx

/-- The low-defect inequality in Lemma 6.2 is exactly the even branch of
the Property B trigger for the first adjacent pair. -/
theorem normalizedAdjacentDefectOrder_zero_le_of_lemma62_low
    (b : BONG V q L (n + 2))
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hdefect : beliParameterDefect K
        (b.adjacentParameter 0 (by simp)) ≤
      (b.lemma62DefectCutoff : ℕ∞)) :
    b.normalizedAdjacentDefectOrder (0 : Fin (n + 1)) ≤
      ((((ramificationIndex K : ℚ) -
        (b.lemma62Gap : ℚ) / 2) : ℚ) : WithTop ℚ) := by
  let a : Kˣ := b.adjacentParameter 0 (by simp)
  have hfinite : beliParameterDefect K a ≠ ⊤ := by
    intro htop
    rw [htop] at hdefect
    simp at hdefect
  have hgapAtZero :
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
  have hdNat := hdefect
  rw [← ENat.coe_toNat hfinite] at hdNat
  norm_cast at hdNat
  have hdInt :
      ((beliParameterDefect K a).toNat : Int) ≤
        (ramificationIndex K : Int) - b.lemma62Gap / 2 := by
    rw [← b.lemma62DefectCutoff_cast heven hupper]
    exact_mod_cast hdNat
  have hfiniteNormalized :
      quadraticDefect K
          (b.normalizedAdjacentProduct (0 : Fin (n + 1))) ≠ ⊤ := by
    rw [← hdefectEq]
    exact hfinite
  have hnormalizedOrder :
      b.normalizedAdjacentDefectOrder (0 : Fin (n + 1)) =
        (((quadraticDefect K
          (b.normalizedAdjacentProduct (0 : Fin (n + 1)))).toNat : ℚ) :
            WithTop ℚ) := by
    unfold normalizedAdjacentDefectOrder
    rw [← ENat.coe_toNat hfiniteNormalized]
    rfl
  have htoNatEq :
      (beliParameterDefect K a).toNat =
        (quadraticDefect K
          (b.normalizedAdjacentProduct (0 : Fin (n + 1)))).toNat :=
    congrArg ENat.toNat hdefectEq
  rw [hnormalizedOrder, ← htoNatEq]
  rcases heven with ⟨r, hr⟩
  rw [hr] at hdInt ⊢
  have hdInt' :
      ((beliParameterDefect K a).toNat : Int) ≤
        (ramificationIndex K : Int) - r := by
    omega
  norm_num
  exact_mod_cast hdInt'

/-- Conversely, a strict normalized-defect inequality implies the
high-defect inequality of Lemma 6.2(c). -/
theorem lemma62_high_of_normalizedAdjacentDefectOrder_zero_gt
    (b : BONG V q L (n + 2))
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hhigh :
      ((((ramificationIndex K : ℚ) -
        (b.lemma62Gap : ℚ) / 2) : ℚ) : WithTop ℚ) <
          b.normalizedAdjacentDefectOrder (0 : Fin (n + 1))) :
    (b.lemma62DefectCutoff : ℕ∞) ≤
      beliParameterDefect K (b.adjacentParameter 0 (by simp)) := by
  apply le_of_not_gt
  intro hlow
  have hnormalized :=
    b.normalizedAdjacentDefectOrder_zero_le_of_lemma62_low
      heven hupper hlow.le
  exact (not_le_of_gt hhigh) hnormalized

/-- The negation of a Property B trigger has exactly the two alternatives
used in Beli's induction: a very large gap, or an even high-defect gap. -/
theorem not_propertyBTrigger_iff_large_or_even_high
    (b : BONG V q L (n + 1)) (i : Fin n)
    (hnot : ¬b.propertyBTrigger i) :
    2 * (ramificationIndex K : Int) + 1 <
        b.order i.succ - b.order i.castSucc ∨
      (Even (b.order i.succ - b.order i.castSucc) ∧
        b.order i.succ - b.order i.castSucc ≤
          2 * (ramificationIndex K : Int) ∧
        ((((ramificationIndex K : ℚ) -
          ((b.order i.succ - b.order i.castSucc : Int) : ℚ) / 2) : ℚ) :
            WithTop ℚ) < b.normalizedAdjacentDefectOrder i) := by
  let gap := b.order i.succ - b.order i.castSucc
  by_cases hlarge : 2 * (ramificationIndex K : Int) + 1 < gap
  · exact Or.inl hlarge
  · have hsmall : gap ≤ 2 * (ramificationIndex K : Int) + 1 :=
      le_of_not_gt hlarge
    rcases Int.even_or_odd gap with heven | hodd
    · right
      refine ⟨heven, ?_, ?_⟩
      · rcases heven with ⟨s, hs⟩
        omega
      apply lt_of_not_ge
      intro hlow
      apply hnot
      unfold propertyBTrigger
      exact Or.inr ⟨heven, hlow⟩
    · exact (hnot (by
        unfold propertyBTrigger
        exact Or.inl ⟨hsmall, hodd⟩)).elim

/-- Inverse rescaling of the head does not change any Property B trigger
strictly inside the recursive tail. -/
theorem HeadInverseRescaleWitness.propertyBTrigger_succ_iff
    (b : BONG V q L (n + 3)) (w : b.HeadInverseRescaleWitness)
    (i : Fin (n + 1)) :
    w.bong.propertyBTrigger i.succ ↔ b.propertyBTrigger i.succ := by
  have horderRight :
      w.bong.order i.succ.succ = b.order i.succ.succ :=
    w.order_succ i.succ
  have hcast : i.succ.castSucc = i.castSucc.succ := by
    apply Fin.ext
    simp
  have horderLeft :
      w.bong.order i.succ.castSucc = b.order i.succ.castSucc := by
    rw [hcast, w.order_succ i.castSucc]
  have hdefect :
      w.bong.normalizedAdjacentDefectOrder i.succ =
        b.normalizedAdjacentDefectOrder i.succ := by
    calc
      w.bong.normalizedAdjacentDefectOrder i.succ =
          w.bong.tail.normalizedAdjacentDefectOrder i :=
        (w.bong.normalizedAdjacentDefectOrder_tail i).symm
      _ = b.tail.normalizedAdjacentDefectOrder i :=
        w.tail_normalizedAdjacentDefectOrder_eq i
      _ = b.normalizedAdjacentDefectOrder i.succ :=
        b.normalizedAdjacentDefectOrder_tail i
  unfold propertyBTrigger
  rw [horderRight, horderLeft, hdefect]

/-- Away from the endpoint gap `2e`, the second adjacent pair cannot trigger
Property B in either the original or the inverse-head-rescaled BONG. -/
theorem not_second_propertyBTrigger_of_lemma62_nonendpoint
    (b : BONG V q L (n + 3)) (w : b.HeadInverseRescaleWitness)
    (hB : b.HasPropertyBOrInverse w)
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hne : b.lemma62Gap ≠ 2 * (ramificationIndex K : Int)) :
    ¬ b.propertyBTrigger (Fin.succ (0 : Fin (n + 1))) := by
  intro htrigger
  rcases heven with ⟨r, hr⟩
  have hstrict : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int) - 2 := by
    rw [hr] at hupper hne ⊢
    omega
  rcases hB with hB | hB
  · have hleft := (hB.2 (Fin.succ (0 : Fin (n + 1))) htrigger).1
        (0 : Fin (n + 3)) (by simp)
    have hleft' :
        2 * (ramificationIndex K : Int) + 1 ≤ b.lemma62Gap := by
      simpa [lemma62Gap] using hleft
    omega
  · have htriggerW :
        w.bong.propertyBTrigger (Fin.succ (0 : Fin (n + 1))) :=
      (w.propertyBTrigger_succ_iff b (0 : Fin (n + 1))).2 htrigger
    have hleft := (hB.2 (Fin.succ (0 : Fin (n + 1))) htriggerW).1
        (0 : Fin (n + 3)) (by simp)
    have hleft' :
        2 * (ramificationIndex K : Int) + 1 ≤ w.bong.lemma62Gap := by
      simpa [lemma62Gap] using hleft
    rw [w.lemma62Gap_eq_add_two] at hleft'
    omega

/-- The Property B alternative for the recursive tail used in the
non-endpoint case of Lemma 6.2(c). -/
theorem lemma62_tail_large_or_even_high
    (b : BONG V q L (n + 3)) (w : b.HeadInverseRescaleWitness)
    (hB : b.HasPropertyBOrInverse w)
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hne : b.lemma62Gap ≠ 2 * (ramificationIndex K : Int)) :
    2 * (ramificationIndex K : Int) + 1 < b.tail.lemma62Gap ∨
      (Even b.tail.lemma62Gap ∧
        b.tail.lemma62Gap ≤ 2 * (ramificationIndex K : Int) ∧
        (b.tail.lemma62DefectCutoff : ℕ∞) ≤
          beliParameterDefect K
            (b.tail.adjacentParameter 0 (by simp))) := by
  let i : Fin (n + 2) := Fin.succ (0 : Fin (n + 1))
  have htailGap :
      b.tail.lemma62Gap = b.order i.succ - b.order i.castSucc := by
    unfold lemma62Gap
    rw [b.order_tail (1 : Fin (n + 2)),
      b.order_tail (0 : Fin (n + 2))]
    congr 2 <;> apply congrArg b.order <;> apply Fin.ext <;> simp [i]
  have htailDefect :
      b.tail.normalizedAdjacentDefectOrder (0 : Fin (n + 1)) =
        b.normalizedAdjacentDefectOrder i := by
    simpa [i] using
      (b.normalizedAdjacentDefectOrder_tail (0 : Fin (n + 1)))
  have hnot := b.not_second_propertyBTrigger_of_lemma62_nonendpoint
    w hB heven hupper hne
  have hdichotomy := b.not_propertyBTrigger_iff_large_or_even_high
    i (by simpa [i] using hnot)
  rcases hdichotomy with hlarge | ⟨hevenTail, hupperTail, hhighTail⟩
  · left
    rw [htailGap]
    exact hlarge
  · right
    have hevenTail' : Even b.tail.lemma62Gap := by
      rw [htailGap]
      exact hevenTail
    have hupperTail' :
        b.tail.lemma62Gap ≤ 2 * (ramificationIndex K : Int) := by
      rw [htailGap]
      exact hupperTail
    refine ⟨hevenTail', hupperTail',
      b.tail.lemma62_high_of_normalizedAdjacentDefectOrder_zero_gt
        hevenTail' hupperTail' ?_⟩
    rw [htailGap, htailDefect]
    exact hhighTail

/-- For a Property B BONG, the low-defect first pair forces the next order
gap to be at least `2e + 1`.  This is the neighboring-gap implication used
in the induction step of Lemma 6.2(b). -/
theorem thirdGap_ge_of_propertyB_lemma62_low
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hdefect : beliParameterDefect K
        (b.adjacentParameter 0 (by simp)) ≤
      (b.lemma62DefectCutoff : ℕ∞)) :
    2 * (ramificationIndex K : Int) + 1 ≤ b.order 2 - b.order 1 := by
  have hnormalized :=
    b.normalizedAdjacentDefectOrder_zero_le_of_lemma62_low
      heven hupper hdefect
  have htrigger : b.propertyBTrigger (0 : Fin (n + 2)) := by
    unfold propertyBTrigger
    right
    constructor
    · simpa [lemma62Gap] using heven
    · simpa [lemma62Gap] using hnormalized
  have hright := (hB.2 (0 : Fin (n + 2)) htrigger).2
  exact hright ⟨2, by omega⟩ rfl

/-- If only the inverse-head-rescaled BONG has Property B, a *strict*
low-defect inequality still triggers Property B there: its first gap and
cutoff are respectively the original gap plus two and the original cutoff
minus one. -/
theorem thirdGap_ge_of_inverse_propertyB_lemma62_strict_low
    (b : BONG V q L (n + 3)) (w : b.HeadInverseRescaleWitness)
    (hB : w.bong.HasPropertyB)
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hdefect : beliParameterDefect K
        (b.adjacentParameter 0 (by simp)) <
      (b.lemma62DefectCutoff : ℕ∞)) :
    2 * (ramificationIndex K : Int) + 1 ≤ b.order 2 - b.order 1 := by
  have hfinite : beliParameterDefect K
      (b.adjacentParameter 0 (by simp)) ≠ ⊤ := by
    intro htop
    rw [htop] at hdefect
    simp at hdefect
  have hdNat := hdefect
  rw [← ENat.coe_toNat hfinite] at hdNat
  norm_cast at hdNat
  have hcutPos : 0 < b.lemma62DefectCutoff := by omega
  have hgapW := w.lemma62Gap_eq_add_two
  rcases heven with ⟨r, hr⟩
  have hevenW : Even w.bong.lemma62Gap := by
    refine ⟨r + 1, ?_⟩
    rw [hgapW, hr]
    omega
  have hcutB := b.lemma62DefectCutoff_cast (by exact ⟨r, hr⟩) hupper
  have hupperW :
      w.bong.lemma62Gap ≤ 2 * (ramificationIndex K : Int) := by
    rw [hgapW, hr]
    rw [hr] at hcutB
    omega
  have hcutW := w.bong.lemma62DefectCutoff_cast hevenW hupperW
  have hcutRelation :
      w.bong.lemma62DefectCutoff + 1 = b.lemma62DefectCutoff := by
    have hcutRelationInt :
        (w.bong.lemma62DefectCutoff : Int) + 1 =
          (b.lemma62DefectCutoff : Int) := by
      rw [hcutW, hcutB, hgapW, hr]
      omega
    exact_mod_cast hcutRelationInt
  have hparameterDefect :=
    w.beliParameterDefect_adjacentParameter_zero_proved
  have hfiniteW : beliParameterDefect K
      (w.bong.adjacentParameter 0 (by simp)) ≠ ⊤ := by
    rw [hparameterDefect]
    exact hfinite
  have hdWNat :
      (beliParameterDefect K
          (w.bong.adjacentParameter 0 (by simp))).toNat ≤
        w.bong.lemma62DefectCutoff := by
    rw [hparameterDefect]
    omega
  have hdW : beliParameterDefect K
        (w.bong.adjacentParameter 0 (by simp)) ≤
      (w.bong.lemma62DefectCutoff : ℕ∞) := by
    rw [← ENat.coe_toNat hfiniteW]
    exact_mod_cast hdWNat
  have hbound := w.bong.thirdGap_ge_of_propertyB_lemma62_low
    hB hevenW hupperW hdW
  change 2 * (ramificationIndex K : Int) + 1 ≤
      w.bong.order (Fin.succ (1 : Fin (n + 2))) -
        w.bong.order (Fin.succ (0 : Fin (n + 2))) at hbound
  rw [w.order_succ (1 : Fin (n + 2)),
    w.order_succ (0 : Fin (n + 2))] at hbound
  exact hbound

/-- A finite Beli parameter defect is bounded by `2e`. -/
theorem lemma62DefectNat_le_twoE_of_finite
    (b : BONG V q L (n + 2))
    (hfinite : beliParameterDefect K
      (b.adjacentParameter 0 (by simp)) ≠ ⊤) :
    b.lemma62DefectNat ≤ 2 * ramificationIndex K := by
  have hnotSquare : ¬IsSquare (-(b.adjacentParameter 0 (by simp))) := by
    intro hsquare
    apply hfinite
    unfold beliParameterDefect
    exact quadraticDefect_eq_top_of_isSquare K hsquare
  have hbound := quadraticDefect_le_two_mul_e_of_not_isSquare
    (K := K) hnotSquare
  have hbound' : beliParameterDefect K
      (b.adjacentParameter 0 (by simp)) ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
    simpa only [beliParameterDefect] using hbound
  rw [← ENat.coe_toNat hfinite] at hbound'
  norm_cast at hbound'

/-- Lemma 6.2(b) in rank two, obtained directly from Corollary 3.10 through
the whole-segment lattice isometry. -/
theorem lemma62_quadraticValues_b_rankTwo_proved
    (b : BONG V q L 2)
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hdefect : beliParameterDefect K
        (b.adjacentParameter 0 (by simp)) ≤
      (b.lemma62DefectCutoff : ℕ∞)) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.scaledIntegralSquareResidueSet (b.value 0)
        (Lattice.powerIdeal (K := K) b.lemma62LowExponent) := by
  let p := SegmentWitness.whole b
  have hp := b.lemma62_segmentBinaryValues_b p heven hupper hdefect
  have hvalues := Lattice.quadraticValueSet_eq_of_latticeIsometry
    (SegmentWitness.wholeLatticeIsometry b)
  intro z hz
  apply hp z
  rwa [hvalues]

/-- Lemma 6.2(c) in rank two, directly from Corollary 3.10. -/
theorem lemma62_quadraticValues_c_rankTwo_proved
    (b : BONG V q L 2)
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hdefect : (b.lemma62DefectCutoff : ℕ∞) ≤
      beliParameterDefect K (b.adjacentParameter 0 (by simp))) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.scaledIntegralSquareResidueSet (b.value 0)
        (Lattice.powerIdeal (K := K) b.lemma62HighExponent) := by
  let p := SegmentWitness.whole b
  have hp := b.lemma62_segmentBinaryValues_c p heven hupper hdefect
  have hvalues := Lattice.quadraticValueSet_eq_of_latticeIsometry
    (SegmentWitness.wholeLatticeIsometry b)
  intro z hz
  apply hp z
  rwa [hvalues]

/-- The endpoint `R₂ - R₁ = 2e` of Lemma 6.2(c) is already part (a),
because the two error exponents coincide exactly. -/
theorem lemma62_quadraticValues_c_of_gap_eq_twoE_proved
    (b : BONG V q L (n + 2)) (w : b.HeadInverseRescaleWitness)
    (hB : b.HasPropertyBOrInverse w)
    (hgap : b.lemma62Gap = 2 * (ramificationIndex K : Int)) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.scaledIntegralSquareResidueSet (b.value 0)
        (Lattice.powerIdeal (K := K) b.lemma62HighExponent) := by
  have horder : b.order 0 ≤ b.order 1 := by
    unfold lemma62Gap at hgap
    omega
  have ha := b.lemma62_quadraticValues_a_proved w hB horder
  have hexponent : b.lemma62HighExponent = b.order 1 := by
    unfold lemma62Gap at hgap
    unfold lemma62HighExponent
    omega
  rw [hexponent]
  exact ha

/-- The strict low-defect induction step in Lemma 6.2(b), for every rank at
least three. -/
theorem lemma62_quadraticValues_b_strict_higherRank_proved
    (b : BONG V q L (n + 3)) (w : b.HeadInverseRescaleWitness)
    (hB : b.HasPropertyBOrInverse w)
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hdefect : beliParameterDefect K
        (b.adjacentParameter 0 (by simp)) <
      (b.lemma62DefectCutoff : ℕ∞)) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.scaledIntegralSquareResidueSet (b.value 0)
        (Lattice.powerIdeal (K := K) b.lemma62LowExponent) := by
  have hthird :
      2 * (ramificationIndex K : Int) + 1 ≤ b.order 2 - b.order 1 := by
    rcases hB with hB | hB
    · exact b.thirdGap_ge_of_propertyB_lemma62_low hB heven hupper hdefect.le
    · exact b.thirdGap_ge_of_inverse_propertyB_lemma62_strict_low
        w hB heven hupper hdefect
  let one : Fin (n + 3) := ⟨1, by omega⟩
  let two : Fin (n + 3) := ⟨2, by omega⟩
  have honeNumeral : (1 : Fin (n + 3)) = one := by
    apply Fin.ext
    change 1 % (n + 3) = 1
    exact Nat.mod_eq_of_lt (by omega)
  have htwoNumeral : (2 : Fin (n + 3)) = two := by
    apply Fin.ext
    change 2 % (n + 3) = 2
    exact Nat.mod_eq_of_lt (by omega)
  rw [honeNumeral, htwoNumeral] at hthird
  let i : Fin (n + 3) := one
  have hi : i.1 + 1 < n + 3 := by
    dsimp only [i, one]
    omega
  have hnext : (⟨i.1 + 1, hi⟩ : Fin (n + 3)) = two := by
    apply Fin.ext
    rfl
  have horder : b.order i ≤ b.order ⟨i.1 + 1, hi⟩ := by
    rw [hnext]
    change b.order one ≤ b.order two
    omega
  rcases b.beliCorollary44_i_unconditional hB.isGood i hi horder with ⟨S⟩
  dsimp only [i, one] at S
  have hleft := b.lemma62_segmentBinaryValues_b S.left heven hupper hdefect.le
  have hfinite : beliParameterDefect K
      (b.adjacentParameter 0 (by simp)) ≠ ⊤ := by
    intro htop
    rw [htop] at hdefect
    simp at hdefect
  have hdBound := b.lemma62DefectNat_le_twoE_of_finite hfinite
  have htargetOrder : b.lemma62LowExponent ≤ b.order two := by
    unfold lemma62LowExponent
    rw [honeNumeral]
    omega
  let j0 : Fin (n + 3 - 2) := ⟨0, by omega⟩
  have hrightOrder : S.right.bong.order j0 = b.order two := by
    calc
      S.right.bong.order j0 = b.order (S.right.sourceIndex j0) :=
        S.right.order_eq j0
      _ = b.order two := by
        apply congrArg b.order
        apply Fin.ext
        simp [SegmentWitness.sourceIndex, j0, two]
  have hrightNorm : Lattice.normIdeal
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice =
        Lattice.powerIdeal (K := K) (b.order two) := by
    calc
      Lattice.normIdeal
          (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice =
          Lattice.powerIdeal (K := K)
            (S.right.bong.order j0) := by
        exact normIdeal_eq_powerIdeal_order_mk_zero S.right.bong (by omega)
      _ = Lattice.powerIdeal (K := K) (b.order two) := by rw [hrightOrder]
  have hright : Lattice.quadraticValueSet
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice ⊆
        Lattice.powerIdeal (K := K) b.lemma62LowExponent := by
    intro z hz
    rw [Lattice.mem_quadraticValueSet_iff] at hz
    rcases hz with ⟨y, hy, rfl⟩
    have hyNorm := Lattice.quadratic_mem_normIdeal_of_mem
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice hy
    rw [hrightNorm] at hyNorm
    exact (Lattice.powerIdeal_le_iff (K := K)
      (b.order two) b.lemma62LowExponent).2 htargetOrder hyNorm
  exact S.quadraticValueSet_subset_scaled_of_blocks
    (b.value 0) (Lattice.powerIdeal (K := K) b.lemma62LowExponent)
      hleft hright

/-- The recursive-tail estimate in the non-endpoint branch of Lemma 6.2(c).
The induction hypothesis is needed only in the even high-defect alternative;
the large-gap alternative follows already from part (a). -/
theorem lemma62_tail_quadraticValues_c_proved
    (b : BONG V q L (n + 3)) (w : b.HeadInverseRescaleWitness)
    (hB : b.HasPropertyBOrInverse w)
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hne : b.lemma62Gap ≠ 2 * (ramificationIndex K : Int))
    (hind : ∀ (wt : b.tail.HeadInverseRescaleWitness),
      b.tail.HasPropertyBOrInverse wt →
      Even b.tail.lemma62Gap →
      b.tail.lemma62Gap ≤ 2 * (ramificationIndex K : Int) →
      (b.tail.lemma62DefectCutoff : ℕ∞) ≤
        beliParameterDefect K
          (b.tail.adjacentParameter 0 (by simp)) →
      Lattice.quadraticValueSet
          (q.orthogonalSpace b.head b.head_isAnisotropic)
          (L.projectedLattice q b.head b.head_isAnisotropic) ⊆
        Lattice.scaledIntegralSquareResidueSet (b.tail.value 0)
          (Lattice.powerIdeal (K := K) b.tail.lemma62HighExponent)) :
    Lattice.quadraticValueSet
        (q.orthogonalSpace b.head b.head_isAnisotropic)
        (L.projectedLattice q b.head b.head_isAnisotropic) ⊆
      Lattice.scaledIntegralSquareResidueSet (b.value 1)
        (Lattice.powerIdeal (K := K) b.lemma62HighExponent) := by
  let wt := b.tail.headInverseRescaleWitness
  have htailB : b.tail.HasPropertyB := hB.tail_hasPropertyB
  have htailBOrInverse : b.tail.HasPropertyBOrInverse wt := Or.inl htailB
  let zero : Fin (n + 3) := ⟨0, by omega⟩
  let one : Fin (n + 3) := ⟨1, by omega⟩
  let two : Fin (n + 3) := ⟨2, by omega⟩
  have hzeroNumeral : (0 : Fin (n + 3)) = zero := by
    apply Fin.ext
    rfl
  have honeNumeral : (1 : Fin (n + 3)) = one := by
    apply Fin.ext
    change 1 % (n + 3) = 1
    exact Nat.mod_eq_of_lt (by omega)
  have htwoNumeral : (2 : Fin (n + 3)) = two := by
    apply Fin.ext
    change 2 % (n + 3) = 2
    exact Nat.mod_eq_of_lt (by omega)
  have hR0R2 : b.order zero ≤ b.order two := by
    exact hB.isGood zero (by simp [zero])
  have htailGap :
      b.tail.lemma62Gap = b.order two - b.order one := by
    unfold lemma62Gap
    rw [b.order_tail (1 : Fin (n + 2)),
      b.order_tail (0 : Fin (n + 2))]
    congr 2 <;> apply congrArg b.order <;> apply Fin.ext <;>
      simp [one, two]
  by_cases hlarge :
      2 * (ramificationIndex K : Int) + 1 < b.tail.lemma62Gap
  · have htailOrder : b.tail.order 0 ≤ b.tail.order 1 := by
      rw [b.order_tail (0 : Fin (n + 2)),
        b.order_tail (1 : Fin (n + 2))]
      rw [htailGap] at hlarge
      change b.order one ≤ b.order two
      omega
    have ha := b.tail.lemma62_quadraticValues_a_proved
      wt htailBOrInverse htailOrder
    have htargetOrder : b.lemma62HighExponent ≤ b.order two := by
      rw [htailGap] at hlarge
      unfold lemma62HighExponent
      rw [hzeroNumeral, honeNumeral]
      omega
    have hideal :
        Lattice.powerIdeal (K := K) (b.tail.order 1) ≤
          Lattice.powerIdeal (K := K) b.lemma62HighExponent := by
      apply (Lattice.powerIdeal_le_iff (K := K)
        (b.tail.order 1) b.lemma62HighExponent).2
      calc
        b.lemma62HighExponent ≤ b.order two := htargetOrder
        _ = b.tail.order 1 := by
          rw [b.order_tail (1 : Fin (n + 2))]
          apply congrArg b.order
          apply Fin.ext
          change 2 = 2 % (n + 3)
          exact (Nat.mod_eq_of_lt (by omega)).symm
    have hmono := Lattice.scaledIntegralSquareResidueSet_mono
      (b.tail.value 0) hideal
    rw [b.value_tail (0 : Fin (n + 2))] at ha hmono
    exact fun z hz ↦ hmono (ha hz)
  · have hhigh := (b.lemma62_tail_large_or_even_high
      w hB heven hupper hne).resolve_left hlarge
    have hevenTail := hhigh.1
    have hupperTail := hhigh.2.1
    have hdefectTail := hhigh.2.2
    have hi := hind wt htailBOrInverse hevenTail hupperTail hdefectTail
    have hexponent :
        b.lemma62HighExponent ≤ b.tail.lemma62HighExponent := by
      unfold lemma62HighExponent
      rw [b.order_tail (0 : Fin (n + 2)),
        b.order_tail (1 : Fin (n + 2))]
      rw [hzeroNumeral, honeNumeral]
      change (b.order zero + b.order one) / 2 +
          (ramificationIndex K : Int) ≤
        (b.order one + b.order two) / 2 +
          (ramificationIndex K : Int)
      omega
    have hideal :
        Lattice.powerIdeal (K := K) b.tail.lemma62HighExponent ≤
          Lattice.powerIdeal (K := K) b.lemma62HighExponent :=
      (Lattice.powerIdeal_le_iff (K := K)
        b.tail.lemma62HighExponent b.lemma62HighExponent).2 hexponent
    have hmono := Lattice.scaledIntegralSquareResidueSet_mono
      (b.tail.value 0) hideal
    rw [b.value_tail (0 : Fin (n + 2))] at hi hmono
    exact fun z hz ↦ hmono (hi hz)

/-- The binary absorption calculation at the end of Beli's proof of Lemma
6.2(c).  A binary slice whose second BONG value is represented by the
recursive tail inherits the required first-value square-residue estimate. -/
theorem lemma62_binary_absorption_c
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (b : BONG V q L (n + 2)) (p : BONG W r M 2)
    (hvalueZero : p.value 0 = b.value 0)
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hdefect : (b.lemma62DefectCutoff : ℕ∞) ≤
      beliParameterDefect K (b.adjacentParameter 0 (by simp)))
    (htail : p.value 1 ∈
      Lattice.scaledIntegralSquareResidueSet (b.value 1)
        (Lattice.powerIdeal (K := K) b.lemma62HighExponent)) :
    Lattice.quadraticValueSet r M ⊆
      Lattice.scaledIntegralSquareResidueSet (b.value 0)
        (Lattice.powerIdeal (K := K) b.lemma62HighExponent) := by
  rcases htail with ⟨s, hs⟩
  let main : K := b.value 1 * (s : K) ^ 2
  have hpOrderZero : p.order 0 = b.order 0 := by
    apply WithTop.coe_injective
    rw [p.coe_order, b.coe_order, hvalueZero]
  have hgapLower :
      -(2 * (ramificationIndex K : Int)) ≤ b.lemma62Gap := by
    have h := (b.adjacentParameter_isBinaryParameterAdmissible
      (0 : Fin (n + 2)) (by simp)).ordUnit_ge_neg_two_mul_e
    simpa only [b.ordUnit_adjacentParameter_zero] using h
  have hhigh_ge_first : b.order 0 ≤ b.lemma62HighExponent := by
    rcases heven with ⟨g, hg⟩
    unfold lemma62HighExponent lemma62Gap at *
    omega
  by_cases hmain : main ∈
      Lattice.powerIdeal (K := K) b.lemma62HighExponent
  · have hpValueIdeal : p.value 1 ∈
        Lattice.powerIdeal (K := K) b.lemma62HighExponent := by
      have hadd := (Lattice.powerIdeal (K := K)
        b.lemma62HighExponent).add_mem hs hmain
      convert hadd using 1
      dsimp only [main]
      ring
    have htarget_le_one : b.lemma62HighExponent ≤ p.order 1 := by
      rw [Lattice.mem_powerIdeal_iff] at hpValueIdeal
      rw [← p.coe_order] at hpValueIdeal
      exact WithTop.coe_le_coe.mp hpValueIdeal
    have hpOrder : p.order 0 ≤ p.order 1 := by
      rw [hpOrderZero]
      exact hhigh_ge_first.trans htarget_le_one
    have hpValues :=
      p.binary_quadraticValueSet_scaled_subset_powerIdeal_of_order_le hpOrder
    have hideal : Lattice.powerIdeal (K := K) (p.order 1) ≤
        Lattice.powerIdeal (K := K) b.lemma62HighExponent :=
      (Lattice.powerIdeal_le_iff (K := K)
        (p.order 1) b.lemma62HighExponent).2 htarget_le_one
    have hmono := Lattice.scaledIntegralSquareResidueSet_mono
      (p.value 0) hideal
    rw [hvalueZero] at hpValues hmono
    exact fun z hz ↦ hmono (hpValues hz)
  · have hsNe : (s : K) ≠ 0 := by
      intro hsZero
      apply hmain
      dsimp only [main]
      rw [hsZero, zero_pow (by omega), mul_zero]
      exact Submodule.zero_mem _
    let su : Kˣ := Units.mk0 (s : K) hsNe
    let k : Int := ordUnit K su
    have hk : 0 ≤ k := by
      have hsIntegral : (0 : WithTop Int) ≤ ord K (s : K) :=
        (mem_integerRing_iff K).1 s.property
      have hsIntegral' : (0 : WithTop Int) ≤ ord K (su : K) := by
        change (0 : WithTop Int) ≤ ord K (s : K)
        exact hsIntegral
      rw [← coe_ordUnit K su] at hsIntegral'
      exact WithTop.coe_nonneg.mp hsIntegral'
    have hsuOrder : ord K (s : K) = (k : WithTop Int) := by
      change ord K (su : K) = (k : WithTop Int)
      exact (coe_ordUnit K su).symm
    have hmainOrder : ord K main =
        ((b.order 1 + 2 * k : Int) : WithTop Int) := by
      dsimp only [main]
      rw [ord_mul, ord_pow, ← b.coe_order, hsuOrder]
      norm_cast
    have hmainLt : ord K main <
        (b.lemma62HighExponent : WithTop Int) := by
      apply lt_of_not_ge
      intro hge
      apply hmain
      exact (Lattice.mem_powerIdeal_iff
        b.lemma62HighExponent main).2 hge
    have herrorOrder :
        (b.lemma62HighExponent : WithTop Int) ≤
          ord K (p.value 1 - main) := by
      exact (Lattice.mem_powerIdeal_iff
        b.lemma62HighExponent (p.value 1 - main)).1 hs
    have hpValueEq : p.value 1 = main + (p.value 1 - main) := by ring
    have hpValueOrder : ord K (p.value 1) = ord K main := by
      rw [hpValueEq]
      exact (ord K).map_add_eq_of_lt_left (hmainLt.trans_le herrorOrder)
    have hpOrderOne : p.order 1 = b.order 1 + 2 * k := by
      apply WithTop.coe_injective
      rw [p.coe_order, hpValueOrder, hmainOrder]
    have hpGap : p.binaryOrderGap = b.lemma62Gap + 2 * k := by
      unfold binaryOrderGap lemma62Gap
      rw [hpOrderZero, hpOrderOne]
      omega
    have hpEven : Even p.binaryOrderGap := by
      rcases heven with ⟨g, hg⟩
      refine ⟨g + k, ?_⟩
      rw [hpGap, hg]
      omega
    have hmainExponentLt :
        b.order 1 + 2 * k < b.lemma62HighExponent := by
      rw [hmainOrder] at hmainLt
      exact WithTop.coe_lt_coe.mp hmainLt
    have hpUpper :
        p.binaryOrderGap ≤ 2 * (ramificationIndex K : Int) := by
      rcases heven with ⟨g, hg⟩
      rw [hpGap, hg]
      have hgapEq : b.order 1 - b.order 0 = g + g := by
        simpa only [lemma62Gap] using hg
      have horderOne : b.order 1 = b.order 0 + (g + g) := by omega
      unfold lemma62HighExponent at hmainExponentLt
      rw [horderOne] at hmainExponentLt
      omega
    let dInt : Int := (ramificationIndex K : Int) -
      b.lemma62Gap / 2 - 2 * k
    have hdInt : 0 ≤ dInt := by
      rcases heven with ⟨g, hg⟩
      dsimp only [dInt]
      have hgapEq : b.order 1 - b.order 0 = g + g := by
        simpa only [lemma62Gap] using hg
      have horderOne : b.order 1 = b.order 0 + (g + g) := by omega
      unfold lemma62HighExponent at hmainExponentLt
      rw [horderOne] at hmainExponentLt
      rw [hg]
      omega
    let d : Nat := Int.toNat dInt
    have hdCast : (d : Int) = dInt := by
      dsimp only [d]
      rw [Int.toNat_of_nonneg hdInt]
    let mainUnit : Kˣ := b.valueUnit 1 * su ^ 2
    let zUnit : Kˣ := p.valueUnit 1 / mainUnit
    have hnormalizedError :
        1 - (1 : K) ^ 2 / (zUnit : K) =
          (p.value 1 - main) / p.value 1 := by
      dsimp only [zUnit, mainUnit, main]
      simp only [Units.val_div_eq_div_val, Units.val_mul,
        Units.val_pow_eq_pow_val, p.coe_valueUnit, b.coe_valueUnit,
        su]
      rw [one_pow]
      change 1 - 1 / (p.value 1 /
          (b.value 1 * (s : K) ^ 2)) =
        (p.value 1 - b.value 1 * (s : K) ^ 2) / p.value 1
      field_simp [p.value_ne_zero 1, b.value_ne_zero 1, hsNe]
    have hdepth : (d : WithTop Int) ≤
        ord K ((p.value 1 - main) / p.value 1) := by
      rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv,
        ← p.coe_order, hpOrderOne]
      rcases heven with ⟨g, hg⟩
      have hgapEq : b.order 1 - b.order 0 = g + g := by
        simpa only [lemma62Gap] using hg
      have horderOne : b.order 1 = b.order 0 + (g + g) := by omega
      have hleftEq : (d : WithTop Int) =
          (b.lemma62HighExponent : WithTop Int) +
            (-((b.order 1 + 2 * k : Int) : WithTop Int)) := by
        norm_cast
        rw [hdCast]
        dsimp only [dInt]
        unfold lemma62HighExponent
        rw [hg, horderOne]
        norm_cast
        omega
      rw [hleftEq]
      have hadd := add_le_add_right herrorOrder
        (-((b.order 1 + 2 * k : Int) : WithTop Int))
      simpa only [add_comm] using hadd
    have hzApprox : IsQuadraticApproximation K zUnit d := by
      refine ⟨1, ?_⟩
      rw [hnormalizedError]
      exact hdepth
    have hzDefect : (d : ℕ∞) ≤ quadraticDefect K zUnit :=
      natCast_le_quadraticDefect K hzApprox
    have hpUnitZero : p.valueUnit 0 = b.valueUnit 0 := by
      apply Units.ext
      simpa only [p.coe_valueUnit, b.coe_valueUnit] using hvalueZero
    have hfactor : -(p.binaryParameter) =
        (-(b.adjacentParameter 0 (by simp))) * su ^ 2 * zUnit := by
      change -(p.valueUnit 1 / p.valueUnit 0) =
        (-(b.valueUnit 1 / b.valueUnit 0)) * su ^ 2 *
          (p.valueUnit 1 / (b.valueUnit 1 * su ^ 2))
      rw [hpUnitZero]
      apply Units.ext
      simp only [Units.val_neg, Units.val_mul, Units.val_div_eq_div_val,
        Units.val_pow_eq_pow_val, neg_mul]
      apply neg_inj.mpr
      field_simp [Units.ne_zero (p.valueUnit 1),
        Units.ne_zero (b.valueUnit 0), Units.ne_zero (b.valueUnit 1),
        Units.ne_zero su] <;> ring
      simp only [p.coe_valueUnit, b.coe_valueUnit]
      rw [mul_assoc, mul_inv_cancel₀ (b.value_ne_zero 1), mul_one]
    have hdCutoffNat : d ≤ b.lemma62DefectCutoff := by
      have hcut := b.lemma62DefectCutoff_cast heven hupper
      have hdCutoffInt : (d : Int) ≤
          (b.lemma62DefectCutoff : Int) := by
        rw [hdCast, hcut]
        dsimp only [dInt]
        omega
      exact_mod_cast hdCutoffInt
    have hdOriginal : (d : ℕ∞) ≤
        quadraticDefect K (-(b.adjacentParameter 0 (by simp))) := by
      exact (show (d : ℕ∞) ≤
          (b.lemma62DefectCutoff : ℕ∞) by exact_mod_cast hdCutoffNat).trans
        hdefect
    have hdParameter : (d : ℕ∞) ≤
        beliParameterDefect K p.binaryParameter := by
      unfold beliParameterDefect
      rw [hfactor]
      have hdom := quadraticDefect_mul_ge_min K
        ((-(b.adjacentParameter 0 (by simp))) * su ^ 2) zUnit
      rw [quadraticDefect_mul_square] at hdom
      exact (le_min hdOriginal hzDefect).trans hdom
    by_cases hpHigh : (p.binaryCorollaryDefectCutoff : ℕ∞) ≤
        beliParameterDefect K p.binaryParameter
    · have hpValues :=
        p.quadraticValueSet_scaled_subset_powerIdeal_of_high_defect
          hpEven hpUpper hpHigh
      have hexponent : b.lemma62HighExponent ≤
          p.order 0 + ((ramificationIndex K : Int) +
            p.binaryOrderGap / 2) := by
        rw [hpOrderZero, hpGap]
        rcases heven with ⟨g, hg⟩
        have hgapEq : b.order 1 - b.order 0 = g + g := by
          simpa only [lemma62Gap] using hg
        have horderOne : b.order 1 = b.order 0 + (g + g) := by omega
        unfold lemma62HighExponent
        rw [horderOne, hg]
        omega
      have hideal : Lattice.powerIdeal (K := K)
            (p.order 0 + ((ramificationIndex K : Int) +
              p.binaryOrderGap / 2)) ≤
          Lattice.powerIdeal (K := K) b.lemma62HighExponent :=
        (Lattice.powerIdeal_le_iff (K := K) _ _).2 hexponent
      intro z hz
      rcases hpValues z hz with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [hvalueZero] at ha
      exact hideal ha
    · have hpLow : beliParameterDefect K p.binaryParameter ≤
          (p.binaryCorollaryDefectCutoff : ℕ∞) :=
        le_of_not_ge hpHigh
      have hpValues :=
        p.quadraticValueSet_scaled_subset_powerIdeal_of_low_defect
          hpEven hpUpper hpLow
      have hpFinite : beliParameterDefect K p.binaryParameter ≠ ⊤ := by
        intro htop
        rw [htop] at hpLow
        simp at hpLow
      have hdDefectNat : d ≤
          beliParameterDefectNat K p.binaryParameter := by
        have hdToNat := ENat.toNat_le_toNat hdParameter hpFinite
        simpa [beliParameterDefectNat] using hdToNat
      have hexponent : b.lemma62HighExponent ≤
          p.order 0 + (p.binaryOrderGap +
            (beliParameterDefectNat K p.binaryParameter : Int)) := by
        rw [hpOrderZero, hpGap]
        have hdDefectInt : (d : Int) ≤
            (beliParameterDefectNat K p.binaryParameter : Int) := by
          exact_mod_cast hdDefectNat
        rw [hdCast] at hdDefectInt
        rcases heven with ⟨g, hg⟩
        have hgapEq : b.order 1 - b.order 0 = g + g := by
          simpa only [lemma62Gap] using hg
        have horderOne : b.order 1 = b.order 0 + (g + g) := by omega
        unfold lemma62HighExponent
        rw [horderOne, hg]
        dsimp only [dInt] at hdDefectInt
        rw [hg] at hdDefectInt
        omega
      have hideal : Lattice.powerIdeal (K := K)
            (p.order 0 + (p.binaryOrderGap +
              (beliParameterDefectNat K p.binaryParameter : Int))) ≤
          Lattice.powerIdeal (K := K) b.lemma62HighExponent :=
        (Lattice.powerIdeal_le_iff (K := K) _ _).2 hexponent
      intro z hz
      rcases hpValues z hz with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [hvalueZero] at ha
      exact hideal ha

/-- The higher-rank induction step in Lemma 6.2(c).  The zero-norm projection
branch is an exact integral square.  Otherwise the vector and the first BONG
vector generate the binary slice used in Beli's proof. -/
theorem lemma62_quadraticValues_c_higherRank_step_proved
    (b : BONG V q L (n + 3)) (w : b.HeadInverseRescaleWitness)
    (hB : b.HasPropertyBOrInverse w)
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hne : b.lemma62Gap ≠ 2 * (ramificationIndex K : Int))
    (hdefect : (b.lemma62DefectCutoff : ℕ∞) ≤
      beliParameterDefect K (b.adjacentParameter 0 (by simp)))
    (hind : ∀ (wt : b.tail.HeadInverseRescaleWitness),
      b.tail.HasPropertyBOrInverse wt →
      Even b.tail.lemma62Gap →
      b.tail.lemma62Gap ≤ 2 * (ramificationIndex K : Int) →
      (b.tail.lemma62DefectCutoff : ℕ∞) ≤
        beliParameterDefect K
          (b.tail.adjacentParameter 0 (by simp)) →
      Lattice.quadraticValueSet
          (q.orthogonalSpace b.head b.head_isAnisotropic)
          (L.projectedLattice q b.head b.head_isAnisotropic) ⊆
        Lattice.scaledIntegralSquareResidueSet (b.tail.value 0)
          (Lattice.powerIdeal (K := K) b.tail.lemma62HighExponent)) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.scaledIntegralSquareResidueSet (b.value 0)
        (Lattice.powerIdeal (K := K) b.lemma62HighExponent) := by
  have htail := b.lemma62_tail_quadraticValues_c_proved
    w hB heven hupper hne hind
  intro z hz
  rw [Lattice.mem_quadraticValueSet_iff] at hz
  rcases hz with ⟨v, hv, rfl⟩
  by_cases hprojection :
      q.quadratic (q.orthogonalProjection b.head v) = 0
  · exact b.quadraticValue_mem_scaled_of_projection_quadratic_zero
      v hv hprojection
        (Lattice.powerIdeal (K := K) b.lemma62HighExponent)
  · rcases b.exists_binarySlice_for_value v hv hprojection with
      ⟨C, p, hpZero, hpTail, hpValue⟩
    have hpTailEstimate := htail hpTail
    have hpValues := b.lemma62_binary_absorption_c p hpZero
      heven hupper hdefect hpTailEstimate
    exact hpValues hpValue

/-- Lemma 6.2(c) in every rank, proved by induction on the rank beyond two. -/
theorem lemma62_quadraticValues_c_proved
    (b : BONG V q L (n + 2)) (w : b.HeadInverseRescaleWitness)
    (hB : b.HasPropertyBOrInverse w)
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hdefect : (b.lemma62DefectCutoff : ℕ∞) ≤
      beliParameterDefect K (b.adjacentParameter 0 (by simp))) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.scaledIntegralSquareResidueSet (b.value 0)
        (Lattice.powerIdeal (K := K) b.lemma62HighExponent) := by
  induction n generalizing V with
  | zero =>
      exact b.lemma62_quadraticValues_c_rankTwo_proved
        heven hupper hdefect
  | succ n ih =>
      by_cases hendpoint :
          b.lemma62Gap = 2 * (ramificationIndex K : Int)
      · exact b.lemma62_quadraticValues_c_of_gap_eq_twoE_proved
          w hB hendpoint
      · apply b.lemma62_quadraticValues_c_higherRank_step_proved
          w hB heven hupper hendpoint hdefect
        intro wt htailB htailEven htailUpper htailDefect
        exact ih b.tail wt htailB htailEven htailUpper htailDefect

/-- Lemma 6.2(b) in every rank.  In rank at least three the strict
low-defect branch is the two-block argument above; equality with the cutoff is
part (c), whose two displayed exponents then coincide. -/
theorem lemma62_quadraticValues_b_proved
    (b : BONG V q L (n + 2)) (w : b.HeadInverseRescaleWitness)
    (hB : b.HasPropertyBOrInverse w)
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hdefect : beliParameterDefect K
        (b.adjacentParameter 0 (by simp)) ≤
      (b.lemma62DefectCutoff : ℕ∞)) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.scaledIntegralSquareResidueSet (b.value 0)
        (Lattice.powerIdeal (K := K) b.lemma62LowExponent) := by
  cases n with
  | zero =>
      exact b.lemma62_quadraticValues_b_rankTwo_proved
        heven hupper hdefect
  | succ n =>
      by_cases hstrict : beliParameterDefect K
          (b.adjacentParameter 0 (by simp)) <
        (b.lemma62DefectCutoff : ℕ∞)
      · exact b.lemma62_quadraticValues_b_strict_higherRank_proved
          w hB heven hupper hstrict
      · have hreverse : (b.lemma62DefectCutoff : ℕ∞) ≤
            beliParameterDefect K
              (b.adjacentParameter 0 (by simp)) :=
          le_of_not_gt hstrict
        have hdefectEq : beliParameterDefect K
              (b.adjacentParameter 0 (by simp)) =
            (b.lemma62DefectCutoff : ℕ∞) :=
          le_antisymm hdefect hreverse
        have hdefectNat : b.lemma62DefectNat =
            b.lemma62DefectCutoff := by
          unfold lemma62DefectNat beliParameterDefectNat
          rw [hdefectEq]
          simp
        have hcutoffCast := b.lemma62DefectCutoff_cast heven hupper
        have hexponent : b.lemma62LowExponent =
            b.lemma62HighExponent := by
          unfold lemma62LowExponent lemma62HighExponent
          rw [hdefectNat, hcutoffCast]
          rcases heven with ⟨g, hg⟩
          have hgapEq : b.order 1 - b.order 0 = g + g := by
            simpa only [lemma62Gap] using hg
          have horderOne : b.order 1 = b.order 0 + (g + g) := by omega
          rw [hg, horderOne]
          omega
        have hc := b.lemma62_quadraticValues_c_proved
          w hB heven hupper hreverse
        rw [hexponent]
        exact hc

end BONG

/-- Unconditional realization of every construction in Beli (2003), Lemma
6.2.  Importing this proof file discharges the former local-law boundary. -/
noncomputable instance beliLemma62LawsProved :
    BeliLemma62Laws.{u, v} K where
  inverseHeadRescale b := ⟨b.headInverseRescaleWitness⟩
  quadraticValues_a b w hB hgap :=
    b.lemma62_quadraticValues_a_proved w hB hgap
  quadraticValues_b b w hB heven hupper hdefect :=
    b.lemma62_quadraticValues_b_proved
      w hB heven hupper hdefect
  quadraticValues_c b w hB heven hupper hdefect :=
    b.lemma62_quadraticValues_c_proved
      w hB heven hupper hdefect

end Bong
