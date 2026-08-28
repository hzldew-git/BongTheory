/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryAdaptedBasis
import Bong.Bong.BinaryModularInvariant
import Bong.Lattice.MixedPairing
import Bong.Lattice.ModularCriterion
import Bong.Lattice.ScaleBasis

/-!
# Modularity in the strict-negative binary branch

For the BONG-adapted integral basis `(x, y)`, write `c = B(x, y)`.  If the
second BONG order is strictly below the first, the norm-generator condition
and the ultrametric equality force

`2 ord(c) = R₁ + R₂`.

The same calculation shows that `c` divides every entry of the integral Gram
matrix.  The scale-and-volume criterion then proves modularity.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- The mixed Gram entry in the BONG-adapted binary integral basis. -/
noncomputable def binaryMixedPairing (b : BONG V q L 2) : K :=
  q.bilin b.head b.binarySecondVector

/-- The second adapted vector still has norm in the principal ideal generated
by the BONG head value. -/
theorem quadratic_binarySecondVector_mem_principal_value_zero
    (b : BONG V q L 2) :
    q.quadratic b.binarySecondVector ∈
      Lattice.principalIdeal (K := K) (b.value 0) := by
  rw [b.value_zero_eq_quadratic_head,
    ← b.head_isNormGenerator.normIdeal_eq]
  exact Lattice.quadratic_mem_normIdeal_of_mem
    q L b.binarySecondVector_mem

/-- Orthogonal projection gives the exact two-by-two Gram decomposition. -/
theorem quadratic_binarySecondVector_eq (b : BONG V q L 2) :
    q.quadratic b.binarySecondVector =
      (b.binaryMixedPairing / b.value 0) ^ 2 * b.value 0 +
        b.value 1 := by
  have h := Lattice.quadratic_projection_decomposition
    q b.head b.head_isAnisotropic b.binarySecondVector
  rw [b.quadratic_projection_binarySecondVector] at h
  simpa [binaryMixedPairing, b.value_zero_eq_quadratic_head] using h

/-- In the strict-negative branch the mixed Gram entry is nonzero. -/
theorem binaryMixedPairing_ne_zero_of_order_one_lt_order_zero
    (b : BONG V q L 2) (hstrict : b.order 1 < b.order 0) :
    b.binaryMixedPairing ≠ 0 := by
  have hmem :=
    b.quadratic_binarySecondVector_mem_principal_value_zero
  have hAD := Lattice.ord_le_of_mem_principalIdeal
    (b.value_ne_zero 0) hmem
  have hEA : ord K (b.value 1) < ord K (b.value 0) := by
    rw [← b.coe_order, ← b.coe_order]
    exact WithTop.coe_lt_coe.mpr hstrict
  have hED : ord K (b.value 1) <
      ord K (q.quadratic b.binarySecondVector) :=
    hEA.trans_le hAD
  have hdiff :
      q.quadratic b.binarySecondVector - b.value 1 =
        (b.binaryMixedPairing / b.value 0) ^ 2 * b.value 0 := by
    rw [b.quadratic_binarySecondVector_eq]
    ring
  have hord := (ord K).map_sub_eq_of_lt_right hED
  intro hc
  rw [hdiff, hc] at hord
  norm_num at hord
  rw [← b.coe_order] at hord
  exact WithTop.top_ne_coe hord

/-- The nonzero mixed Gram entry as a field unit. -/
noncomputable def binaryMixedPairingUnit (b : BONG V q L 2)
    (hstrict : b.order 1 < b.order 0) : Kˣ :=
  Units.mk0 b.binaryMixedPairing
    (b.binaryMixedPairing_ne_zero_of_order_one_lt_order_zero hstrict)

@[simp]
theorem coe_binaryMixedPairingUnit (b : BONG V q L 2)
    (hstrict : b.order 1 < b.order 0) :
    (b.binaryMixedPairingUnit hstrict : K) = b.binaryMixedPairing :=
  rfl

/-- In the strict-negative branch, the mixed pairing order is the average of
the two BONG orders. -/
theorem two_mul_ordUnit_binaryMixedPairing_eq_order_add
    (b : BONG V q L 2) (hstrict : b.order 1 < b.order 0) :
    2 * ordUnit K (b.binaryMixedPairingUnit hstrict) =
      b.order 0 + b.order 1 := by
  have hmem :=
    b.quadratic_binarySecondVector_mem_principal_value_zero
  have hAD := Lattice.ord_le_of_mem_principalIdeal
    (b.value_ne_zero 0) hmem
  have hEA : ord K (b.value 1) < ord K (b.value 0) := by
    rw [← b.coe_order, ← b.coe_order]
    exact WithTop.coe_lt_coe.mpr hstrict
  have hED : ord K (b.value 1) <
      ord K (q.quadratic b.binarySecondVector) :=
    hEA.trans_le hAD
  have hdiff :
      q.quadratic b.binarySecondVector - b.value 1 =
        (b.binaryMixedPairing / b.value 0) ^ 2 * b.value 0 := by
    rw [b.quadratic_binarySecondVector_eq]
    ring
  have hterm :
      ord K ((b.binaryMixedPairing / b.value 0) ^ 2 * b.value 0) =
        ord K (b.value 1) := by
    rw [← hdiff]
    exact (ord K).map_sub_eq_of_lt_right hED
  let cUnit := b.binaryMixedPairingUnit hstrict
  let termUnit : Kˣ :=
    (cUnit / b.valueUnit 0) ^ 2 * b.valueUnit 0
  have hcoeTerm :
      (termUnit : K) =
        (b.binaryMixedPairing / b.value 0) ^ 2 * b.value 0 := by
    simp [termUnit, cUnit, div_eq_mul_inv]
  have htermOrder : ordUnit K termUnit = b.order 1 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, hcoeTerm, hterm, ← b.coe_order]
  dsimp [termUnit] at htermOrder
  simp only [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
    ordUnit_pow] at htermOrder
  simp only [cUnit] at htermOrder
  norm_num at htermOrder
  rw [← b.order_eq_ordUnit 0, ← b.order_eq_ordUnit 1] at htermOrder
  omega

/-- The strict-negative mixed scale has lower order than the head norm. -/
theorem ordUnit_binaryMixedPairing_lt_order_zero
    (b : BONG V q L 2) (hstrict : b.order 1 < b.order 0) :
    ordUnit K (b.binaryMixedPairingUnit hstrict) < b.order 0 := by
  have hsum :=
    b.two_mul_ordUnit_binaryMixedPairing_eq_order_add hstrict
  omega

/-- In the strict-negative branch, every adapted Gram entry is divisible by
the mixed pairing. -/
theorem scaleIdeal_le_principal_binaryMixedPairing
    (b : BONG V q L 2) (hstrict : b.order 1 < b.order 0) :
    Lattice.scaleIdeal q L ≤
      Lattice.principalIdeal (K := K) b.binaryMixedPairing := by
  have hcne :=
    b.binaryMixedPairing_ne_zero_of_order_one_lt_order_zero hstrict
  have hcOrder : ord K b.binaryMixedPairing ≤ ord K (b.value 0) := by
    rw [← b.coe_binaryMixedPairingUnit hstrict, ← coe_ordUnit,
      ← b.coe_order]
    exact WithTop.coe_le_coe.mpr
      (b.ordUnit_binaryMixedPairing_lt_order_zero hstrict).le
  have hvalueIdeal :
      Lattice.principalIdeal (K := K) (b.value 0) ≤
        Lattice.principalIdeal (K := K) b.binaryMixedPairing :=
    (Lattice.principalIdeal_le_iff_ord_ge
      (b.value_ne_zero 0) hcne).2 hcOrder
  refine Lattice.scaleIdeal_le_of_integralBasis
    b.binaryIntegralBasis
      (Lattice.principalIdeal (K := K) b.binaryMixedPairing) ?_
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · rw [b.coe_binaryIntegralBasis_inl]
    change q.quadratic b.head ∈
      Lattice.principalIdeal (K := K) b.binaryMixedPairing
    rw [← b.value_zero_eq_quadratic_head]
    exact hvalueIdeal
      (Lattice.generator_mem_principalIdeal (b.value 0))
  · rw [b.coe_binaryIntegralBasis_inl,
      b.coe_binaryIntegralBasis_inr]
    exact Lattice.generator_mem_principalIdeal b.binaryMixedPairing
  · rw [b.coe_binaryIntegralBasis_inr,
      b.coe_binaryIntegralBasis_inl, q.isSymm.eq]
    exact Lattice.generator_mem_principalIdeal b.binaryMixedPairing
  · rw [b.coe_binaryIntegralBasis_inr,
      b.coe_binaryIntegralBasis_inr]
    change q.quadratic b.binarySecondVector ∈
      Lattice.principalIdeal (K := K) b.binaryMixedPairing
    exact hvalueIdeal
      b.quadratic_binarySecondVector_mem_principal_value_zero

/-- In the strict-negative branch, the mixed adapted Gram entry generates
the scale ideal exactly. -/
theorem scaleIdeal_eq_principal_binaryMixedPairing
    (b : BONG V q L 2) (hstrict : b.order 1 < b.order 0) :
    Lattice.scaleIdeal q L =
      Lattice.principalIdeal (K := K) b.binaryMixedPairing := by
  apply le_antisymm
  · exact b.scaleIdeal_le_principal_binaryMixedPairing hstrict
  · rw [Lattice.principalIdeal, Submodule.span_le,
      Set.singleton_subset_iff]
    exact Lattice.bilin_mem_scaleIdeal_of_mem q L
      b.head_isNormGenerator.mem b.binarySecondVector_mem

/-- The determinant order in the strict-negative branch is twice the mixed
pairing order. -/
theorem volumeOrder_eq_two_mul_ordUnit_binaryMixedPairing
    (b : BONG V q L 2) (hstrict : b.order 1 < b.order 0) :
    Lattice.volumeOrder q L =
      2 * ordUnit K (b.binaryMixedPairingUnit hstrict) := by
  calc
    Lattice.volumeOrder q L = ordUnit K b.valueProduct :=
      b.volumeOrder_eq_ordUnit_valueProduct
    _ = ordUnit K (b.valueUnit 0) +
        ordUnit K (b.valueUnit 1) := by
      rw [b.valueProduct_fin_two, ordUnit_mul]
    _ = b.order 0 + b.order 1 := by
      rw [← b.order_eq_ordUnit 0, ← b.order_eq_ordUnit 1]
    _ = 2 * ordUnit K (b.binaryMixedPairingUnit hstrict) :=
      (b.two_mul_ordUnit_binaryMixedPairing_eq_order_add hstrict).symm

/-- The strict-negative scale has the determinant order required for
binary modularity. -/
theorem volumeOrder_eq_finrank_mul_ordUnit_binaryMixedPairing
    (b : BONG V q L 2) (hstrict : b.order 1 < b.order 0) :
    Lattice.volumeOrder q L =
      (finrank K V : Int) *
        ordUnit K (b.binaryMixedPairingUnit hstrict) := by
  rw [← b.length_eq_finrank]
  exact b.volumeOrder_eq_two_mul_ordUnit_binaryMixedPairing hstrict

/-- A binary BONG with strictly decreasing orders is modular at its mixed
Gram entry. -/
theorem isModular_binaryMixedPairing_of_order_one_lt_order_zero
    (b : BONG V q L 2) (hstrict : b.order 1 < b.order 0) :
    Lattice.IsModular q L (b.binaryMixedPairingUnit hstrict) :=
  Lattice.isModular_of_scaleIdeal_le_of_volumeOrder_eq q L
    (b.binaryMixedPairingUnit hstrict)
    (b.scaleIdeal_le_principal_binaryMixedPairing hstrict)
    (b.volumeOrder_eq_finrank_mul_ordUnit_binaryMixedPairing hstrict)

/-- Nonpositive binary relative order produces a modular parameter. -/
theorem exists_isModular_of_binaryOrderGap_nonpos
    (b : BONG V q L 2) (hgap : b.binaryOrderGap ≤ 0) :
    ∃ a : Kˣ, Lattice.IsModular q L a := by
  have horder : b.order 1 ≤ b.order 0 := by
    rw [binaryOrderGap] at hgap
    omega
  rcases horder.lt_or_eq with hstrict | heq
  · exact ⟨b.binaryMixedPairingUnit hstrict,
      b.isModular_binaryMixedPairing_of_order_one_lt_order_zero hstrict⟩
  · have hgapZero : b.binaryOrderGap = 0 := by
      rw [binaryOrderGap]
      omega
    have hnonneg : 0 ≤ b.binaryOrderGap := by omega
    exact ⟨b.valueUnit 0,
      (b.isModular_value_zero_iff_binaryOrderGap_eq_zero_of_nonneg
        hnonneg).2 hgapZero⟩

/-- Beli (2003), Lemma 3.3(i): a binary lattice is modular exactly when its
relative BONG order is nonpositive. -/
theorem exists_isModular_iff_binaryOrderGap_nonpos
    (b : BONG V q L 2) :
    (∃ a : Kˣ, Lattice.IsModular q L a) ↔
      b.binaryOrderGap ≤ 0 := by
  constructor
  · rintro ⟨a, ha⟩
    exact b.binaryOrderGap_nonpos_of_isModular a ha
  · exact b.exists_isModular_of_binaryOrderGap_nonpos

/-- The order formulation of the binary modularity criterion. -/
theorem exists_isModular_iff_order_one_le_order_zero
    (b : BONG V q L 2) :
    (∃ a : Kˣ, Lattice.IsModular q L a) ↔
      b.order 1 ≤ b.order 0 := by
  rw [b.exists_isModular_iff_binaryOrderGap_nonpos, binaryOrderGap]
  omega

end BONG

end Bong
