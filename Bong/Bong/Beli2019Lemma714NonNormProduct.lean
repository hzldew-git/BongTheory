/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma71
import Bong.Bong.Beli2019Lemma710OrthogonalSum
import Bong.Bong.Beli2019Lemma714RescaledBinary

/-!
# Beli (2019), Lemma 7.14(ii): non-norm generators in the split model

When `M = J ⊥ K`, the norm of `J` has order `R`, the norm of `K` has
order at least `R + 1`, and every primitive vector of `J` is a norm
generator, a vector `(x,y)` fails to generate the norm of `M` exactly when
`x ∈ \mathfrak p J`.  Consequently the non-norm-generator lattice is the
literal orthogonal product `\mathfrak p J ⊥ K`.
-/

namespace Bong

open Dyadic

universe u v w

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {J : Lattice K V} {T : Lattice K W}

/-- A basis-free formulation of the statement that every primitive vector
of a lattice is a norm generator: primitive means not divisible by the
selected uniformizer inside the lattice. -/
def EveryPrimitiveIsNormGenerator (q : QuadraticSpace K V)
    (J : Lattice K V) : Prop :=
  ∀ x : V, x ∈ J →
    x ∉ rescale (uniformizerUnit K) J → IsNormGenerator q J x

/-- If the right factor has norm order at least `R+1`, the norm ideal of the
orthogonal product is the norm ideal `p^R` of the left factor. -/
theorem normIdeal_orthogonalProduct_eq_powerIdeal
    (R : Int) (hnormJ : normIdeal q J = powerIdeal (K := K) R)
    (hnormT : normIdeal r T ≤ powerIdeal (K := K) (R + 1)) :
    normIdeal (q.orthogonalSum r) (product J T) =
      powerIdeal (K := K) R := by
  rw [normIdeal_orthogonalProduct, hnormJ, sup_eq_left]
  exact hnormT.trans ((powerIdeal_le_iff (K := K) (R + 1) R).2 (by omega))

/-- Pointwise form of the split-model calculation: for a vector already in
`J ⊥ T`, failure to generate the norm is equivalent to divisibility of its
left coordinate by the uniformizer. -/
theorem not_isNormGenerator_orthogonalProduct_iff_left_mem_rescale
    (R : Int) (hnormJ : normIdeal q J = powerIdeal (K := K) R)
    (hnormT : normIdeal r T ≤ powerIdeal (K := K) (R + 1))
    (hprimitive : EveryPrimitiveIsNormGenerator q J)
    (z : V × W) (hz : z ∈ product J T) :
    (¬IsNormGenerator (q.orthogonalSum r) (product J T) z) ↔
      z.1 ∈ rescale (uniformizerUnit K) J := by
  let hnormProduct :=
    normIdeal_orthogonalProduct_eq_powerIdeal R hnormJ hnormT
  have hRsucc : (R : WithTop Int) < ((R + 1 : Int) : WithTop Int) := by
    exact_mod_cast (show R < R + 1 by omega)
  constructor
  · intro hnotGenerator
    by_contra hxNot
    apply hnotGenerator
    have hxGenerator := hprimitive z.1
      (mem_product_iff.mp hz).1 hxNot
    apply (isNormGenerator_iff_ord_quadratic_eq R hnormProduct hz).2
    rw [QuadraticSpace.orthogonalSum_quadratic_apply]
    have hxOrder :=
      (isNormGenerator_iff_ord_quadratic_eq R hnormJ
        (mem_product_iff.mp hz).1).1 hxGenerator
    have hyOrder := hnormT
      (quadratic_mem_normIdeal_of_mem r T (mem_product_iff.mp hz).2)
    rw [mem_powerIdeal_iff] at hyOrder
    have hlt : ord K (q.quadratic z.1) < ord K (r.quadratic z.2) := by
      rw [hxOrder]
      exact hRsucc.trans_le hyOrder
    rw [AddValuation.map_add_eq_of_lt_left (ord K) hlt, hxOrder]
  · intro hxScaled
    apply (not_isNormGenerator_iff_ord_quadratic_gt
      R hnormProduct hz).2
    rw [QuadraticSpace.orthogonalSum_quadratic_apply]
    rw [mem_rescale_iff] at hxScaled
    rcases hxScaled with ⟨x, hx, hscaled⟩
    have hxOrder : (R : WithTop Int) < ord K (q.quadratic z.1) := by
      rw [← hscaled, coe_uniformizerUnit]
      exact normOrder_lt_ord_quadratic_uniformizer_smul R hnormJ hx
    have hyOrder := hnormT
      (quadratic_mem_normIdeal_of_mem r T (mem_product_iff.mp hz).2)
    rw [mem_powerIdeal_iff] at hyOrder
    have hyStrict : (R : WithTop Int) < ord K (r.quadratic z.2) :=
      hRsucc.trans_le hyOrder
    exact (lt_min hxOrder hyStrict).trans_le
      (min_ord_le_ord_add K (q.quadratic z.1) (r.quadratic z.2))

/-- In the split model of Lemma 7.14, the non-norm-generator lattice is
exactly `pJ ⊥ T`.  The scale bound is the same explicit hypothesis used to
construct the left-hand lattice in Lemma 7.1. -/
theorem nonNormGeneratorLattice_orthogonalProduct_eq
    (R : Int) (hnormJ : normIdeal q J = powerIdeal (K := K) R)
    (hnormT : normIdeal r T ≤ powerIdeal (K := K) (R + 1))
    (hscale : scaleIdeal (q.orthogonalSum r) (product J T) ≤
      powerIdeal (K := K) (R - ramificationIndex K + 1))
    (hprimitive : EveryPrimitiveIsNormGenerator q J) :
    nonNormGeneratorLattice R
        (normIdeal_orthogonalProduct_eq_powerIdeal R hnormJ hnormT)
        hscale =
      product (rescale (uniformizerUnit K) J) T := by
  let hnormProduct :=
    normIdeal_orthogonalProduct_eq_powerIdeal R hnormJ hnormT
  have hpiLe : rescale (uniformizerUnit K) J ≤ J := by
    apply rescale_le_self_of_mem_integerRing
    rw [coe_uniformizerUnit, mem_integerRing_iff, Dyadic.IsIntegral,
      ord_uniformizer]
    norm_num
  apply Lattice.ext
  ext z
  change z ∈ nonNormGeneratorLattice R hnormProduct hscale ↔
    z ∈ product (rescale (uniformizerUnit K) J) T
  rw [mem_nonNormGeneratorLattice_iff, mem_product_iff, mem_product_iff]
  constructor
  · rintro ⟨hz, hnotGenerator⟩
    exact ⟨(not_isNormGenerator_orthogonalProduct_iff_left_mem_rescale
      R hnormJ hnormT hprimitive z (mem_product_iff.mpr hz)).1
        hnotGenerator, hz.2⟩
  · rintro ⟨hxScaled, hyT⟩
    have hxJ : z.1 ∈ J := hpiLe hxScaled
    have hzProduct : z ∈ product J T :=
      mem_product_iff.mpr ⟨hxJ, hyT⟩
    exact ⟨mem_product_iff.mp hzProduct,
      (not_isNormGenerator_orthogonalProduct_iff_left_mem_rescale
        R hnormJ hnormT hprimitive z hzProduct).2 hxScaled⟩

end Lattice

end Bong
