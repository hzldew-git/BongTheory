/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalCorollary45
import Bong.Bong.BeliCorollary44ScaleProof
import Bong.Bong.Beli2019VolumeOrders
import Bong.Bong.BeliLemma47Proof
import Bong.Bong.Beli2009ModularSignedDeterminantWeight
import Bong.Bong.Beli2019Lemma710BONGProduct
import Bong.Bong.AlternatingEndpointProduct

/-!
# Beli's alternating half-modular block

This file begins the BONG splitting calculation in Section 4 of
"Universal integral quadratic forms over dyadic local fields".  Indices are
zero based: the paper's sequence

`R₁, R₂, ..., R₂ₖ = 0, -2e, ..., 0, -2e`

is therefore recorded pair by pair below.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

noncomputable local instance universalSplittingDiscriminant :
    DyadicDiscriminantClassLaws K :=
  dyadicDiscriminantClassLawsProved

namespace BONG.GoodBONG

/-- Consecutive-pair indexing for a sequence of length `2 * k`. -/
def halfModularPairIndexEquiv (k : Nat) :
    Fin k × Fin 2 ≃ Fin (2 * k) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm k 2))

@[simp]
theorem halfModularPairIndexEquiv_zero_val (k : Nat) (j : Fin k) :
    (halfModularPairIndexEquiv k (j, (0 : Fin 2))).val = 2 * j.val := by
  simp [halfModularPairIndexEquiv, finProdFinEquiv]

@[simp]
theorem halfModularPairIndexEquiv_one_val (k : Nat) (j : Fin k) :
    (halfModularPairIndexEquiv k (j, (1 : Fin 2))).val =
      2 * j.val + 1 := by
  simp [halfModularPairIndexEquiv, finProdFinEquiv]
  omega

/-- The alternating order sequence in Beli, Lemma 4.6. -/
def HasHalfModularOrderPattern {k : Nat}
    (b : GoodBONG q L (2 * k)) : Prop :=
  ∀ j : Fin k,
    b.order (halfModularPairIndexEquiv k (j, (0 : Fin 2))) = 0 ∧
      b.order (halfModularPairIndexEquiv k (j, (1 : Fin 2))) =
        -2 * (ramificationIndex K : Int)

/-- The valuation of the paper's scalar `1/2`. -/
theorem ordUnit_dyadicHalfUnit :
    ordUnit K (Lattice.dyadicHalfUnit (K := K)) =
      -(ramificationIndex K : Int) := by
  rw [Lattice.dyadicHalfUnit, ordUnit_inv]
  congr 1
  apply WithTop.coe_injective
  rw [coe_ordUnit]
  exact (ramificationIndex_spec K).symm

/-- The sum of an alternating `0,-2e` order sequence. -/
theorem sum_order_eq_of_hasHalfModularOrderPattern {k : Nat}
    (b : GoodBONG q L (2 * k))
    (h : b.HasHalfModularOrderPattern) :
    (∑ i, b.order i) =
      (2 * k : Int) * ordUnit K (Lattice.dyadicHalfUnit (K := K)) := by
  rw [← Equiv.sum_comp (halfModularPairIndexEquiv k)
    (fun i => b.order i)]
  rw [Fintype.sum_prod_type]
  rw [ordUnit_dyadicHalfUnit]
  simp only [Fin.sum_univ_two]
  simp_rw [(h _).1, (h _).2]
  simp
  ring

end BONG.GoodBONG

namespace Lattice

/-- The intrinsic lattice property called "`1/2 O`-modular with norm
`O`" in Lemma 4.6. -/
def IsHalfModularWithUnitNorm (q : QuadraticSpace K V)
    (L : Lattice K V) : Prop :=
  IsModular q L (dyadicHalfUnit (K := K)) ∧
    normIdeal q L = unitIdeal (K := K)

end Lattice

namespace BONG.GoodBONG

set_option maxHeartbeats 1000000 in
-- The scale-normalization proof expands the full good-BONG volume sum.
/-- Beli, Lemma 4.6, converse direction: the alternating order sequence
forces half-modularity and norm `O`. -/
theorem isHalfModularWithUnitNorm_of_orderPattern {k : Nat}
    (hk : 1 ≤ k) (b : GoodBONG q L (2 * k))
    (h : b.HasHalfModularOrderPattern) :
    Lattice.IsHalfModularWithUnitNorm q L := by
  have hlen : 2 * k = (2 * k - 2) + 2 := by omega
  let c : GoodBONG q L ((2 * k - 2) + 2) := b.castLength hlen
  have hc0 : c.order 0 = 0 := by
    rw [GoodBONG.order_castLength]
    have hj := (h (⟨0, by omega⟩ : Fin k)).1
    calc
      b.order ⟨(0 : Fin ((2 * k - 2) + 2)).val, by omega⟩ =
          b.order (halfModularPairIndexEquiv k
            ((⟨0, by omega⟩ : Fin k), (0 : Fin 2))) := by
        apply congrArg b.order
        apply Fin.ext
        simp
      _ = 0 := hj
  have hc1 : c.order 1 = -2 * (ramificationIndex K : Int) := by
    rw [GoodBONG.order_castLength]
    have hj := (h (⟨0, by omega⟩ : Fin k)).2
    calc
      b.order ⟨(1 : Fin ((2 * k - 2) + 2)).val, by omega⟩ =
          b.order (halfModularPairIndexEquiv k
            ((⟨0, by omega⟩ : Fin k), (1 : Fin 2))) := by
        apply congrArg b.order
        apply Fin.ext
        simp
      _ = -2 * (ramificationIndex K : Int) := hj
  rcases c.toBONG.beliCorollary44_iv_unconditional c.good with
    ⟨s, hscale, hsorder⟩
  have hs : ordUnit K s =
      ordUnit K (Lattice.dyadicHalfUnit (K := K)) := by
    change 2 * ordUnit K s =
      min (2 * c.order 0) (c.order 0 + c.order 1) at hsorder
    rw [hc0, hc1] at hsorder
    have he : 0 ≤ (ramificationIndex K : Int) := by positivity
    norm_num only [mul_zero, zero_add] at hsorder
    rw [min_eq_right (by omega)] at hsorder
    rw [ordUnit_dyadicHalfUnit]
    omega
  have hscale' : Lattice.scaleIdeal q L ≤
      Lattice.principalIdeal (K := K)
        (Lattice.dyadicHalfUnit (K := K) : K) := by
    rw [hscale]
    exact le_of_eq
      ((Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).2 hs)
  have hvolume : Lattice.volumeOrder q L =
      (finrank K V : Int) *
        ordUnit K (Lattice.dyadicHalfUnit (K := K)) := by
    rw [b.toBONG.volumeOrder_eq_sum_order]
    change (∑ i, b.order i) = _
    rw [b.sum_order_eq_of_hasHalfModularOrderPattern h]
    rw [← b.toBONG.length_eq_finrank]
    norm_num [Nat.cast_mul]
  have hmodular : Lattice.IsModular q L
      (Lattice.dyadicHalfUnit (K := K)) :=
    Lattice.isModular_of_scaleIdeal_le_of_volumeOrder_eq
      q L (Lattice.dyadicHalfUnit (K := K)) hscale' hvolume
  have hnorm : Lattice.normIdeal q L = Lattice.unitIdeal (K := K) := by
    calc
      Lattice.normIdeal q L =
          Lattice.principalIdeal (K := K)
            (q.quadratic c.toBONG.head) :=
        c.toBONG.head_isNormGenerator.normIdeal_eq
      _ =
          Lattice.principalIdeal (K := K)
            (c.valueUnit 0 : K) := by
        rw [← c.toBONG.value_zero_eq_quadratic_head]
        rfl
      _ = Lattice.principalIdeal (K := K) ((1 : Kˣ) : K) := by
        apply (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).2
        change ordUnit K (c.toBONG.valueUnit 0) = ordUnit K (1 : Kˣ)
        rw [← c.toBONG.order_eq_ordUnit]
        have hc0' : c.toBONG.order 0 = 0 := hc0
        rw [hc0']
        apply WithTop.coe_injective
        simp
      _ = Lattice.unitIdeal (K := K) := by
        rfl
  exact ⟨hmodular, hnorm⟩

/-- The one-component Jordan profile of a half-modular lattice with norm
`O` has the alternating `0,-2e` order sequence. -/
theorem orderPattern_of_isHalfModularWithUnitNorm {k : Nat}
    (hk : 1 ≤ k) (b : GoodBONG q L (2 * k))
    (h : Lattice.IsHalfModularWithUnitNorm q L) :
    b.HasHalfModularOrderPattern := by
  let W := Lattice.WeakJordanDecomposition.singleOfModular
    (Lattice.dyadicHalfUnit (K := K)) h.1 (by
      rw [← b.toBONG.length_eq_finrank]
      omega)
  let hstrict :=
    Lattice.WeakJordanDecomposition.singleOfModular_scaleOrder_strict
      (Lattice.dyadicHalfUnit (K := K)) h.1 (by
        rw [← b.toBONG.length_eq_finrank]
        omega)
  let J := W.toJordan hstrict
  let P : BONG.JordanOrderProfileWitness b.toBONG J :=
    Classical.choice (b.toBONG.beliLemma47_profile b.good J)
  have hnormOrder : ordUnit K (J.normGenerator 0) = 0 := by
    have hwhole : Lattice.normIdeal (J.component 0).space
        (J.component 0).lattice = Lattice.normIdeal q L := by
      let f := J.toOrthogonalDecomposition.singleComponentLatticeIsometry
      have hmap := Lattice.normIdeal_map_isometry
        f.toQuadraticSpaceIsometry (J.component 0).lattice
      change Lattice.normIdeal q
        (Lattice.map f.toLinearEquiv (J.component 0).lattice) = _ at hmap
      rw [f.map_eq] at hmap
      exact hmap.symm
    have hgen := J.normIdeal_eq (0 : Fin 1)
    rw [hwhole, h.2] at hgen
    have hone : Lattice.unitIdeal (K := K) =
        Lattice.principalIdeal (K := K) ((1 : Kˣ) : K) := rfl
    rw [hone] at hgen
    have hord := (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp hgen
    have honeOrder : ordUnit K (1 : Kˣ) = 0 := by
      apply WithTop.coe_injective
      simp
    exact hord.symm.trans honeOrder
  have heffective : BONG.jordanEffectiveNormOrder J (0 : Fin 1) = 0 := by
    simp only [BONG.jordanEffectiveNormOrder,
      BONG.jordanEffectiveNormOrderAt, JordanProfileOrder.effectiveAt,
      JordanProfileOrder.adjustedAt]
    simp [hnormOrder]
  have hscale : ordUnit K (J.scaleGenerator 0) =
      -(ramificationIndex K : Int) := by
    change ordUnit K (Lattice.dyadicHalfUnit (K := K)) = _
    exact ordUnit_dyadicHalfUnit
  intro j
  have component_zero (i : Fin (2 * k)) : (P.indexEquiv i).1 = (0 : Fin 1) :=
    Subsingleton.elim _ _
  have local_val (i : Fin (2 * k)) : (P.indexEquiv i).2.val = i.val := by
    have hi := P.index_val_eq_componentStart_add_local i
    rw [component_zero i] at hi
    have hsum :
        (∑ x ∈ Finset.Iio (0 : Fin 1),
          J.toOrthogonalDecomposition.componentRank x) = 0 := by simp
    rw [hsum, zero_add] at hi
    exact hi.symm
  constructor
  · let i := halfModularPairIndexEquiv k (j, (0 : Fin 2))
    have hival : i.val = 2 * j.val := by simp [i]
    have hparity : Even (P.indexEquiv i).2.val := by
      rw [local_val i, hival]
      exact even_two_mul _
    change b.toBONG.order i = 0
    rw [P.order_eq i]
    simp only [BONG.jordanExpectedOrder, component_zero i, hscale,
      heffective]
    simp [hparity]
  · let i := halfModularPairIndexEquiv k (j, (1 : Fin 2))
    have hival : i.val = 2 * j.val + 1 := by simp [i]
    have hparity : ¬Even (P.indexEquiv i).2.val := by
      rw [local_val i, hival]
      exact Nat.not_even_iff_odd.mpr ⟨j.val, by omega⟩
    change b.toBONG.order i = -2 * (ramificationIndex K : Int)
    rw [P.order_eq i]
    simp only [BONG.jordanExpectedOrder, component_zero i, hscale,
      heffective]
    have hepos : 0 < (ramificationIndex K : Int) := by
      exact_mod_cast ramificationIndex_pos K
    simp [hparity]
    omega

/-- Beli, Lemma 4.6: exact good-BONG characterization of a
`1/2 O`-modular rank-`2k` lattice with norm `O`. -/
theorem beliUniversalLemma46 {k : Nat} (hk : 1 ≤ k)
    (b : GoodBONG q L (2 * k)) :
    Lattice.IsHalfModularWithUnitNorm q L ↔
      b.HasHalfModularOrderPattern := by
  constructor
  · exact b.orderPattern_of_isHalfModularWithUnitNorm hk
  · exact b.isHalfModularWithUnitNorm_of_orderPattern hk

/-- The two determinant square classes in the second assertion of Beli's
Lemma 4.6.  Since `signedEvenPrefixProduct k` is
`(-1)^k a₁⋯ a₂ₖ`, the two disjuncts say respectively
`det(FJ)=(-1)^k` and `det(FJ)=(-1)^k Delta` in `K×/(K×)^2`. -/
theorem beliUniversalLemma46_determinantCases {k : Nat}
    (b : GoodBONG q L (2 * k))
    (h : b.HasHalfModularOrderPattern) :
    IsSquare (b.toBONG.signedEvenPrefixProduct k) ∨
      IsSquare (b.toBONG.signedEvenPrefixProduct k *
        (universalSplittingDiscriminant (K := K)).discriminantUnit) := by
  apply b.toBONG.signedEvenPrefixProduct_endpoint_cases k le_rfl
  intro t ht
  let j : Fin k := ⟨t, ht⟩
  let i : Fin (2 * k) :=
    halfModularPairIndexEquiv k (j, (0 : Fin 2))
  have hi : i.val + 1 < 2 * k := by
    simp [i, j]
    omega
  have hnext : (⟨i.val + 1, hi⟩ : Fin (2 * k)) =
      halfModularPairIndexEquiv k (j, (1 : Fin 2)) := by
    apply Fin.ext
    simp [i, j]
  have hgap : b.order ⟨i.val + 1, hi⟩ - b.order i =
      -(2 * (ramificationIndex K : Int)) := by
    rw [hnext, (h j).1, (h j).2]
    ring
  have hcur : i = (⟨2 * t, by omega⟩ : Fin (2 * k)) := by
    apply Fin.ext
    simp [i, j]
  have hresult := b.toBONG.adjacentSignedProduct_endpoint_cases i hi
    (b.toBONG.adjacentUnitSquareClass_endpoint_cases i hi hgap)
  have hv0 : b.toBONG.valueUnit i =
      b.toBONG.valueUnit ⟨2 * t, by omega⟩ :=
    congrArg b.toBONG.valueUnit hcur
  have hv1 : b.toBONG.valueUnit ⟨i.val + 1, hi⟩ =
      b.toBONG.valueUnit ⟨2 * t + 1, by omega⟩ := by
    apply congrArg b.toBONG.valueUnit
    apply Fin.ext
    simp [i, j]
  rw [hv0, hv1] at hresult
  exact hresult

universe w

variable {W : Type w} [AddCommGroup W] [Module K W]
  {r : QuadraticSpace K W} {M : Lattice K W}

/-- Beli, Lemma 4.7.  The two selected good BONGs concatenate, in their
paper order, to a good BONG of the orthogonal sum.  The statement includes
the rank-zero residual case; then the second value assertion is vacuous. -/
theorem beliUniversalLemma47 {k m : Nat} (hk : 1 ≤ k)
    (a : GoodBONG q L (2 * k)) (c : GoodBONG r M m)
    (ha : Lattice.IsHalfModularWithUnitNorm q L)
    (hc : Lattice.IsIntegral r M) :
    ∃ d : GoodBONG (q.orthogonalSum r) (Lattice.product L M)
        (m + 2 * k),
      (∀ i : Fin (2 * k),
        d.valueUnit (BONG.orthogonalProductLeftIndex m i) =
          a.valueUnit i) ∧
      (∀ j : Fin m,
        d.valueUnit (BONG.orthogonalProductRightIndex (2 * k) j) =
          c.valueUnit j) := by
  have hpattern : a.HasHalfModularOrderPattern :=
    (a.beliUniversalLemma46 hk).1 ha
  cases m with
  | zero =>
      letI : Module.Finite K W := M.moduleFinite
      have hfin : finrank K W = 0 := by
        simpa using c.toBONG.length_eq_finrank.symm
      have hW : Subsingleton W :=
        (Module.finrank_zero_iff.mp hfin)
      let removeRight : Lattice.Isometry
          (q.orthogonalSum r) q (Lattice.product L M) L :=
        Lattice.orthogonalProductSwap.trans
          (Lattice.orthogonalProductSndIsometryOfSubsingleton
            r q M L hW)
      let ac : GoodBONG q L (0 + 2 * k) := a.castLength (by omega)
      let d : GoodBONG (q.orthogonalSum r) (Lattice.product L M)
          (0 + 2 * k) := ac.mapLatticeIsometry removeRight.symm
      refine ⟨d, ?_, ?_⟩
      · intro i
        change (ac.mapLatticeIsometry removeRight.symm).valueUnit
          (BONG.orthogonalProductLeftIndex 0 i) = _
        rw [GoodBONG.valueUnit_mapLatticeIsometry,
          GoodBONG.valueUnit_castLength]
        congr 1
      · intro j
        exact Fin.elim0 j
  | succ m =>
      have hcHead : 0 ≤ c.order 0 :=
        (BONG.beliUniversalLemma22 c.toBONG).mp hc
      let lastPair : Fin k := ⟨k - 1, by omega⟩
      have hpenultimate :
          a.order ⟨2 * k - 2, by omega⟩ ≤ c.order 0 := by
        have hzero := (hpattern lastPair).1
        have hindex :
            (⟨2 * k - 2, by omega⟩ : Fin (2 * k)) =
              halfModularPairIndexEquiv k (lastPair, (0 : Fin 2)) := by
          apply Fin.ext
          simp [lastPair]
          omega
        rw [hindex, hzero]
        exact hcHead
      have hlast :
          a.order ⟨2 * k - 1, by omega⟩ =
            -2 * (ramificationIndex K : Int) := by
        have hodd := (hpattern lastPair).2
        have hindex :
            (⟨2 * k - 1, by omega⟩ : Fin (2 * k)) =
              halfModularPairIndexEquiv k (lastPair, (1 : Fin 2)) := by
          apply Fin.ext
          simp [lastPair]
          omega
        rw [hindex]
        exact hodd
      have hlastHead :
          a.order ⟨2 * k - 1, by omega⟩ ≤ c.order 0 := by
        rw [hlast]
        have he : 0 ≤ (ramificationIndex K : Int) := by positivity
        omega
      have hlastSecond : ∀ hm : 1 < m + 1,
          a.order ⟨2 * k - 1, by omega⟩ ≤ c.order ⟨1, hm⟩ := by
        intro hm
        rw [hlast]
        have hgap := c.orderGap_ge_neg_two_mul_e
          (⟨0, by omega⟩ : Fin m)
        unfold orderGap at hgap
        have hsucc : (⟨0, by omega⟩ : Fin m).succ =
            (⟨1, hm⟩ : Fin (m + 1)) := by
          apply Fin.ext
          rfl
        have hcast : (⟨0, by omega⟩ : Fin m).castSucc =
            (⟨0, by omega⟩ : Fin (m + 1)) := by
          apply Fin.ext
          rfl
        rw [hsucc, hcast] at hgap
        have hhead : 0 ≤ c.order (⟨0, by omega⟩ : Fin (m + 1)) := by
          simpa using hcHead
        omega
      let d := a.orthogonalProductRight_of_endpointBounds c
        (by omega) hpenultimate hlastHead hlastSecond
      refine ⟨d, ?_, ?_⟩
      · intro i
        exact GoodBONG.valueUnit_orthogonalProductRight_of_endpointBounds_left
          a c (by omega) hpenultimate hlastHead hlastSecond i
      · intro j
        exact GoodBONG.valueUnit_orthogonalProductRight_of_endpointBounds_right
          a c (by omega) hpenultimate hlastHead hlastSecond j

end BONG.GoodBONG

end Bong
