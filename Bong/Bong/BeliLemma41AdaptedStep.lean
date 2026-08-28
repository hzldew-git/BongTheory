/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma41
import Bong.Bong.Beli2019Lemma51Block
import Bong.Bong.BeliCorollary44Proof
import Bong.Lattice.OrthogonalDecompositionIdeals
import Bong.Lattice.OrthogonalDecompositionDual

/-!
# The primitive first-projection step in Beli (2003), Lemma 4.1(ii)

Let a property-A Jordan decomposition be fixed and let `x` be the first
vector of an arbitrary BONG of the same lattice.  Beli's proof first shows
that the projection of `x` to the first Jordan component is primitive.  If it
were divisible by the uniformizer, both its quadratic value and the value of
the complementary projection would lie one level deeper than the norm ideal,
contradicting that `x` is a norm generator.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}

namespace BONG

/-- A Jordan decomposition of the lattice of a nonempty BONG has at least
one component. -/
theorem Lattice.JordanDecomposition.blockCount_pos_of_bong
    (b : BONG V q L (n + 1)) (J : Lattice.JordanDecomposition q L t) :
    0 < t := by
  by_contra ht
  have ht0 : t = 0 := Nat.eq_zero_of_not_pos ht
  subst t
  letI : Module.Finite K V := L.moduleFinite
  let D := J.toOrthogonalDecomposition
  have hfin : finrank K V = 0 := by
    rw [Module.finrank_eq_card_basis D.componentAmbientBasis]
    simp
  have hlength := b.length_eq_finrank
  omega

/-- The first BONG value and the first property-A Jordan norm generator have
the same valuation. -/
theorem headOrder_eq_firstJordanNormOrder
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    b.order 0 = ordUnit K (J.normGenerator ⟨0, ht⟩) := by
  have hideal :
      Lattice.principalIdeal (K := K) (b.valueUnit 0 : K) =
        Lattice.principalIdeal (K := K)
          (J.normGenerator ⟨0, ht⟩ : K) := by
    calc
      Lattice.principalIdeal (K := K) (b.valueUnit 0 : K) =
          Lattice.normIdeal q L := by
        change Lattice.principalIdeal (K := K) (b.value 0) =
          Lattice.normIdeal q L
        rw [b.value_zero_eq_quadratic_head]
        exact b.head_isNormGenerator.normIdeal_eq.symm
      _ = Lattice.principalIdeal (K := K)
          (J.normGenerator ⟨0, ht⟩ : K) :=
        J.normIdeal_eq_first hA ht
  rw [b.order_eq_ordUnit]
  exact (Lattice.principalIdeal_eq_iff_ordUnit_eq
    (b.valueUnit 0) (J.normGenerator ⟨0, ht⟩)).mp hideal

/-- The projection of the first vector of an arbitrary BONG to the first
component of a property-A Jordan decomposition is primitive. -/
theorem firstJordanProjection_not_mem_rescale
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    (J.component ⟨0, ht⟩).carrierProjection b.head ∉
      Lattice.rescale (uniformizerUnit K)
        (J.component ⟨0, ht⟩).lattice := by
  let i0 : Fin t := ⟨0, ht⟩
  let C := J.component i0
  let p : C.carrier := C.carrierProjection b.head
  let z : C.orthogonalCarrier := C.orthogonalProjection b.head
  intro hscaled
  have hpQ : q.quadratic (p : V) ∈
      Lattice.principalIdeal (K := K)
        (((J.normGenerator i0) * uniformizerUnit K : Kˣ) : K) := by
    simpa [i0, C, p] using
      J.firstCarrierProjection_quadratic_mem_nextNorm_of_mem_rescale
        ht b.head hscaled
  have hzQ : q.quadratic (z : V) ∈
      Lattice.principalIdeal (K := K)
        (((J.normGenerator i0) * uniformizerUnit K : Kˣ) : K) := by
    simpa [i0, C, z] using
      J.firstOrthogonalProjection_quadratic_mem_nextNorm
        hA ht b.head b.head_isNormGenerator.mem
  have horth : q.bilin (p : V) (z : V) = 0 :=
    z.property (p : V) p.property
  have hheadQ : q.quadratic b.head ∈
      Lattice.principalIdeal (K := K)
        (((J.normGenerator i0) * uniformizerUnit K : Kˣ) : K) := by
    have hsum :=
      (Lattice.principalIdeal (K := K)
        (((J.normGenerator i0) * uniformizerUnit K : Kˣ) : K)).add_mem hpQ hzQ
    rw [← C.carrierProjection_add_orthogonalProjection b.head,
      q.quadratic_add, horth]
    simpa using hsum
  have hprincipal :
      Lattice.principalIdeal (K := K) (q.quadratic b.head) ≤
        Lattice.principalIdeal (K := K)
          (((J.normGenerator i0) * uniformizerUnit K : Kˣ) : K) := by
    rw [Lattice.principalIdeal, Submodule.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact hheadQ
  have hnormEq :
      Lattice.principalIdeal (K := K) (J.normGenerator i0 : K) =
        Lattice.principalIdeal (K := K) (q.quadratic b.head) := by
    calc
      Lattice.principalIdeal (K := K) (J.normGenerator i0 : K) =
          Lattice.normIdeal q L :=
        (J.normIdeal_eq_first hA ht).symm
      _ = Lattice.principalIdeal (K := K) (q.quadratic b.head) :=
        b.head_isNormGenerator.normIdeal_eq
  have hle :
      Lattice.principalIdeal (K := K) (J.normGenerator i0 : K) ≤
        Lattice.principalIdeal (K := K)
          (((J.normGenerator i0) * uniformizerUnit K : Kˣ) : K) := by
    rw [hnormEq]
    exact hprincipal
  have horderWithTop :=
    (Lattice.principalIdeal_le_iff_ord_ge
      (Units.ne_zero (J.normGenerator i0))
      (Units.ne_zero (J.normGenerator i0 * uniformizerUnit K))).mp hle
  have horder :
      ordUnit K (J.normGenerator i0 * uniformizerUnit K) ≤
        ordUnit K (J.normGenerator i0) := by
    apply WithTop.coe_le_coe.mp
    simpa only [coe_ordUnit] using horderWithTop
  have hpi : ordUnit K (uniformizerUnit K) = 1 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, coe_uniformizerUnit, ord_uniformizer]
    rfl
  rw [ordUnit_mul, hpi] at horder
  omega

/-- The first vector of an arbitrary BONG of a property-A lattice lies in an
exact unary or binary modular block.  In contrast with the general recursive
construction of Beli (2019), Lemma 5.1, the representative here is literally
the prescribed BONG head, because its projection to the first Jordan
component is already known to be primitive. -/
noncomputable def firstJordanAdaptedBlockData
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    Lattice.Beli2019Lemma51BlockData q L b.head := by
  let i0 : Fin t := ⟨0, ht⟩
  let C := J.component i0
  let p : C.carrier := C.carrierProjection b.head
  let z : C.orthogonalCarrier := C.orthogonalProjection b.head
  have hp : p ∈ C.lattice := by
    simpa [i0, C, p] using
      J.firstCarrierProjection_mem_lattice ht b.head
        b.head_isNormGenerator.mem
  have hpPrimitive : p ∉
      Lattice.rescale (uniformizerUnit K) C.lattice := by
    simpa [i0, C, p] using
      b.firstJordanProjection_not_mem_rescale J hA ht
  let hexistsPair :=
    (J.modular i0).exists_pairing_eq_of_not_mem_rescale hp hpPrimitive
  let y : C.carrier := Classical.choose hexistsPair
  have hy : y ∈ C.lattice := (Classical.choose_spec hexistsPair).1
  have hpy : C.space.bilin p y = (J.scaleGenerator i0 : K) :=
    (Classical.choose_spec hexistsPair).2
  have hyL : (y : V) ∈ L :=
    J.toOrthogonalDecomposition.component_ambientSubmodule_le i0
      ⟨y, hy, rfl⟩
  have hxy : q.bilin b.head (y : V) = (J.scaleGenerator i0 : K) := by
    have horth : q.bilin (z : V) (y : V) = 0 := by
      rw [q.isSymm.eq (z : V) (y : V)]
      exact z.property (y : V) y.property
    calc
      q.bilin b.head (y : V) =
          q.bilin ((p : V) + (z : V)) (y : V) := by
        rw [C.carrierProjection_add_orthogonalProjection]
      _ = q.bilin (p : V) (y : V) + q.bilin (z : V) (y : V) := by
        rw [LinearMap.BilinForm.add_left]
      _ = (J.scaleGenerator i0 : K) := by
        change C.space.bilin p y + _ = _
        rw [hpy, horth, add_zero]
  have hscale : Lattice.scaleIdeal q L =
      Lattice.principalIdeal (K := K) (J.scaleGenerator i0 : K) := by
    simpa [i0] using J.scaleIdeal_eq_first ht
  have hpairHead : ∀ w : V, w ∈ L →
      q.bilin b.head w ∈
        Lattice.principalIdeal (K := K) (J.scaleGenerator i0 : K) := by
    intro w hw
    rw [← hscale]
    exact Lattice.bilin_mem_scaleIdeal_of_mem q L
      b.head_isNormGenerator.mem hw
  have hpairY : ∀ w : V, w ∈ L →
      q.bilin (y : V) w ∈
        Lattice.principalIdeal (K := K) (J.scaleGenerator i0 : K) := by
    intro w hw
    rw [← hscale]
    exact Lattice.bilin_mem_scaleIdeal_of_mem q L hyL hw
  have hscaleHead := hpairHead b.head b.head_isNormGenerator.mem
  have hscaleY := hpairY (y : V) hyL
  have hscaleHeadOrder :
      ord K (J.scaleGenerator i0 : K) ≤ ord K (q.quadratic b.head) :=
    Lattice.ord_le_of_mem_principalIdeal
      (Units.ne_zero (J.scaleGenerator i0)) hscaleHead
  have hscaleYOrder :
      ord K (J.scaleGenerator i0 : K) ≤ ord K (q.quadratic (y : V)) :=
    Lattice.ord_le_of_mem_principalIdeal
      (Units.ne_zero (J.scaleGenerator i0)) hscaleY
  by_cases heq :
      ord K (J.scaleGenerator i0 : K) = ord K (q.quadratic b.head)
  · apply Lattice.Beli2019Lemma51BlockData.unary b.head
      b.head_isNormGenerator.mem
    · simp
    · exact b.head_isAnisotropic
    · intro w hw
      have hideal :
          Lattice.principalIdeal (K := K) (J.scaleGenerator i0 : K) =
            Lattice.principalIdeal (K := K) (q.quadratic b.head) := by
        apply le_antisymm
        · exact (Lattice.principalIdeal_le_iff_ord_ge
            (Units.ne_zero (J.scaleGenerator i0))
            b.head_isAnisotropic).2 heq.ge
        · exact (Lattice.principalIdeal_le_iff_ord_ge
            b.head_isAnisotropic
            (Units.ne_zero (J.scaleGenerator i0))).2 heq.le
      rw [← hideal]
      exact hpairHead w hw
  · have hstrict :
        ord K (J.scaleGenerator i0 : K) < ord K (q.quadratic b.head) :=
      lt_of_le_of_ne hscaleHeadOrder heq
    have hxyne : q.bilin b.head (y : V) ≠ 0 := by
      rw [hxy]
      exact Units.ne_zero (J.scaleGenerator i0)
    apply Lattice.Beli2019Lemma51BlockData.binary b.head (y : V)
      b.head_isNormGenerator.mem hyL
    · simp
    · exact hxyne
    · rwa [hxy]
    · rwa [hxy]
    · intro w hw
      rw [hxy]
      exact hpairHead w hw
    · intro w hw
      rw [hxy]
      exact hpairY w hw

/-- The block selected from the first Jordan component uses the prescribed
BONG head itself, not merely a congruent representative. -/
theorem firstJordanAdaptedBlockData_representative
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    (b.firstJordanAdaptedBlockData J hA ht).representative = b.head := by
  classical
  simp only [firstJordanAdaptedBlockData]
  split <;> rfl

/-- If the line generated by a lattice vector splits at its own quadratic
value, orthogonal projection along that vector remains integral.  This is the
integral content of the unary branch in Beli's proof of Lemma 4.1(ii). -/
theorem Lattice.coe_mem_of_mem_projectedLattice_of_pairing_divisible
    {x : V} (hxL : x ∈ L) (hx : q.IsAnisotropic x)
    (hpair : ∀ w : V, w ∈ L →
      q.bilin x w ∈
        Lattice.principalIdeal (K := K) (q.quadratic x))
    {y : q.vectorOrthogonal x}
    (hy : y ∈ L.projectedLattice q x hx) : (y : V) ∈ L := by
  rcases (Lattice.mem_projectedLattice_iff q L x hx y).1 hy with
    ⟨w, hw, rfl⟩
  change q.orthogonalProjection x w ∈ L
  have hdiv := hpair w hw
  rw [Lattice.principalIdeal, Submodule.mem_span_singleton] at hdiv
  rcases hdiv with ⟨c, hc⟩
  have hc' : (c : K) * q.quadratic x = q.bilin x w := by
    change algebraMap (IntegerRing K) K c * q.quadratic x =
      q.bilin x w at hc
    rw [ValuationSubring.algebraMap_apply (IntegerRing K) c] at hc
    exact hc
  have hratio : q.bilin x w / q.quadratic x = (c : K) := by
    rw [← hc', mul_div_cancel_right₀]
    exact hx
  rw [q.orthogonalProjection_apply, hratio]
  have hcx : (c : K) • x ∈ L := by
    change (algebraMap (IntegerRing K) K c) • x ∈ L
    simpa only [IsScalarTower.algebraMap_smul] using L.smul_mem c hxL
  exact L.sub_mem hw hcx

/-- In the unary branch, the next BONG norm cannot have smaller valuation
than the head norm.  Indeed the whole projected lattice embeds back into
`L`, while the head norm generates `nL`. -/
theorem order_zero_le_order_one_of_firstJordanAdaptedBlockData_isUnary
    [FiniteDimensional K V]
    (b : BONG V q L (n + 2))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hUnary : (b.firstJordanAdaptedBlockData J hA ht).IsUnary) :
    b.order 0 ≤ b.order 1 := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  have hrep : D.representative = b.head := by
    simpa only [D] using
      b.firstJordanAdaptedBlockData_representative J hA ht
  cases hD : D with
  | unary z hz hcongruent hanisotropic hpair =>
      have hzhead : z = b.head := by
        simpa [Lattice.Beli2019Lemma51BlockData.representative, hD] using hrep
      subst z
      have htailMem : (b.tail.head : V) ∈ L :=
        Lattice.coe_mem_of_mem_projectedLattice_of_pairing_divisible
          b.head_isNormGenerator.mem b.head_isAnisotropic hpair
          b.tail.head_isNormGenerator.mem
      have hvalueMem : q.quadratic (b.tail.head : V) ∈
          Lattice.principalIdeal (K := K) (q.quadratic b.head) := by
        rw [← b.head_isNormGenerator.normIdeal_eq]
        exact Lattice.quadratic_mem_normIdeal_of_mem q L htailMem
      have hord : ord K (q.quadratic b.head) ≤
          ord K (q.quadratic (b.tail.head : V)) :=
        Lattice.ord_le_of_mem_principalIdeal
          b.head_isAnisotropic hvalueMem
      have hvalueOne : b.value (1 : Fin (n + 2)) =
          q.quadratic (b.tail.head : V) := by
        calc
          b.value (1 : Fin (n + 2)) = b.tail.value 0 :=
            (b.value_tail 0).symm
          _ = (q.orthogonalSpace b.head
                b.head_isAnisotropic).quadratic b.tail.head :=
            b.tail.value_zero_eq_quadratic_head
          _ = q.quadratic (b.tail.head : V) := rfl
      apply WithTop.coe_le_coe.mp
      simpa only [b.coe_order, b.value_zero_eq_quadratic_head,
        hvalueOne] using hord
  | binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY =>
      exact False.elim (by
        have : ¬D.IsUnary := by
          rw [hD]
          exact Lattice.Beli2019Lemma51BlockData.not_isUnary_binary
            z y hz hy hcongruent hzy hleft hright hpairZ hpairY
        exact this hUnary)

/-- The unary branch gives the literal cut after the first prescribed BONG
vector. -/
theorem hasTwoBlockSplit_one_of_firstJordanAdaptedBlockData_isUnary
    [FiniteDimensional K V]
    (b : BONG V q L (n + 2))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hUnary : (b.firstJordanAdaptedBlockData J hA ht).IsUnary) :
    b.HasTwoBlockSplit 1 (by omega) := by
  apply b.exists_twoBlockSplit_of_leftOrders_le_rightHead 1 (by omega) (by omega)
  intro i
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  rw [SegmentWitness.order_eq, SegmentWitness.order_eq]
  simpa [SegmentWitness.sourceIndex] using
    b.order_zero_le_order_one_of_firstJordanAdaptedBlockData_isUnary
      J hA ht hUnary

end BONG

end Bong
