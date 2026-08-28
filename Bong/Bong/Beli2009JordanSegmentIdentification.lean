/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanConcreteCoordinates
import Bong.Bong.BeliCorollary44Proof
import Bong.Bong.TwoBlockProductIsometry
import Bong.Lattice.JordanFundamentalLayerSplit
import Bong.Lattice.OrthogonalProductIsometry

/-!
# Consecutive BONG segments at strict Jordan boundaries

An exact put-together witness enumerates the component BONGs in Jordan
order.  Consequently, cutting the ambient BONG at the rank preceding a
component gives exactly the vector-space prefix of the Jordan decomposition.
When Corollary 4.4 supplies an integral split at that cut, uniqueness of the
integral orthogonal summands identifies its segment lattices with the Jordan
prefix and suffix lattices.
-/

namespace Bong

open Dyadic Module
open scoped DirectSum

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

namespace Lattice.OrthogonalDecomposition

variable {t : Nat} (D : OrthogonalDecomposition q L t)

/-- The dimension of a prefix carrier is the sum of the component ranks
strictly before the numerical cut. -/
theorem finrank_prefixCarrier (k : Nat) :
    Module.finrank K (D.prefixCarrier k) =
      ∑ i : D.PrefixIndex k, D.componentRank i.1 := by
  letI : ∀ i : D.PrefixIndex k,
      Module.Finite K (D.component i.1).carrier :=
    fun i ↦ (D.component i.1).lattice.moduleFinite
  rw [← (D.prefixCarrierDirectSumEquiv k).finrank_eq]
  rw [(DirectSum.linearEquivFunOnFintype K (D.PrefixIndex k)
    (fun i ↦ (D.component i.1).carrier)).finrank_eq]
  rw [Module.finrank_pi_fintype]
  rfl

/-- At a genuine component index, the subtype sum in
`finrank_prefixCarrier` is the usual `Iio` rank sum. -/
theorem finrank_prefixCarrier_index (k : Fin t) :
    Module.finrank K (D.prefixCarrier k.val) =
      ∑ i ∈ Finset.Iio k, D.componentRank i := by
  rw [D.finrank_prefixCarrier]
  symm
  exact Finset.sum_subtype (Finset.Iio k) (by
    intro x
    simp only [Finset.mem_Iio]
    rfl) (fun i ↦ D.componentRank i)

/-- The integral suffix is exactly the intersection of the parent lattice
with the suffix vector space. -/
theorem mem_suffixAmbientSubmodule_iff (k : Nat) (x : V) :
    x ∈ D.suffixAmbientSubmodule k ↔
      x ∈ L ∧ x ∈ D.suffixCarrier k := by
  constructor
  · intro hx
    refine ⟨?_, D.mem_suffixCarrier_of_mem_suffixAmbientSubmodule k hx⟩
    have hle : D.suffixAmbientSubmodule k ≤ L.toSubmodule :=
      (_root_.le_sup_right : D.suffixAmbientSubmodule k ≤
        D.prefixAmbientSubmodule k ⊔ D.suffixAmbientSubmodule k).trans_eq
          (D.prefixAmbientSubmodule_sup_suffixAmbientSubmodule k)
    exact hle hx
  · rintro ⟨hxL, hxS⟩
    have hxSum : x ∈ D.prefixAmbientSubmodule k ⊔
        D.suffixAmbientSubmodule k := by
      rw [D.prefixAmbientSubmodule_sup_suffixAmbientSubmodule k]
      exact hxL
    rw [Submodule.mem_sup] at hxSum
    rcases hxSum with ⟨p, hp, s, hs, hps⟩
    have hpP : p ∈ D.prefixCarrier k :=
      D.mem_prefixCarrier_of_mem_prefixAmbientSubmodule k hp
    have hsS : s ∈ D.suffixCarrier k :=
      D.mem_suffixCarrier_of_mem_suffixAmbientSubmodule k hs
    have hpS : p ∈ D.suffixCarrier k := by
      have hpeq : p = x - s := by
        rw [← hps]
        abel
      rw [hpeq]
      exact (D.suffixCarrier k).sub_mem hxS hsS
    have hpZero : p = 0 :=
      Submodule.disjoint_def.mp (D.prefixCarrier_disjoint_suffixCarrier k)
        p hpP hpS
    rw [hpZero, zero_add] at hps
    rwa [← hps]

end Lattice.OrthogonalDecomposition

namespace BONG.PutTogetherWitness

variable {n t : Nat} {b : BONG V q L n}
  {D : Lattice.OrthogonalDecomposition q L t}
  {c : D.ComponentBONGFamily}

/-- The first `sum_{i<k} rank(L_i)` ambient BONG vectors span precisely the
Jordan-prefix carrier.  This is a vector-space statement and uses only the
exact ordered concatenation witness. -/
theorem segmentCarrier_zero_prefixRank_eq_prefixCarrier
    (h : PutTogetherWitness b D c) (k : Fin t)
    (hpos : 0 < D.componentRank k) :
    b.segmentCarrier 0 (∑ i ∈ Finset.Iio k, D.componentRank i) (by
        let z : Fin (D.componentRank k) := ⟨0, hpos⟩
        have hv := h.inverse_index_val k z
        have hg := (h.indexEquiv.symm ⟨k, z⟩).isLt
        omega) =
      D.prefixCarrier k.val := by
  let cut := ∑ i ∈ Finset.Iio k, D.componentRank i
  let z : Fin (D.componentRank k) := ⟨0, hpos⟩
  let boundary : Fin n := h.indexEquiv.symm ⟨k, z⟩
  have hboundaryVal : boundary.val = cut := by
    dsimp only [boundary, cut]
    simpa only [z, Nat.add_zero] using h.inverse_index_val k z
  have hcutLt : cut < n := by
    rw [← hboundaryVal]
    exact boundary.isLt
  letI : FiniteDimensional K (D.prefixCarrier k.val) :=
    (D.prefixAmbientBasis k.val).finiteDimensional_of_finite
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [segmentCarrier, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    let global : Fin n := segmentIndex 0 cut (by omega) j
    have hglobalVal : global.val = j.val := by
      dsimp only [global]
      simp only [segmentIndex_val, Nat.zero_add]
    have hglobalLt : global < boundary := by
      change global.val < boundary.val
      rw [hglobalVal, hboundaryVal]
      exact j.isLt
    have hbefore := (h.order_iff global boundary).1 hglobalLt
    have hboundaryIndex : h.indexEquiv boundary = ⟨k, z⟩ :=
      h.indexEquiv.apply_symm_apply ⟨k, z⟩
    rw [hboundaryIndex] at hbefore
    have hcomponent : (h.indexEquiv global).1.val < k.val := by
      rcases hbefore with hlt | ⟨heq, hlocal⟩
      · exact hlt
      · have himpossible : (h.indexEquiv global).2.val < 0 := by
          simpa only [z] using hlocal
        exact (Nat.not_lt_zero _ himpossible).elim
    let prefixIndex : D.PrefixIndex k.val :=
      ⟨(h.indexEquiv global).1, hcomponent⟩
    have hmember :
        ((c (h.indexEquiv global).1).ambientVector
            (h.indexEquiv global).2 : V) ∈ D.prefixCarrier k.val := by
      apply le_iSup
        (fun i : D.PrefixIndex k.val ↦ (D.component i.1).carrier)
        prefixIndex
      exact (c (h.indexEquiv global).1).ambientVector
        (h.indexEquiv global).2 |>.property
    have hambient := h.ambientVector_eq global
    change b.ambientVector global ∈ D.prefixCarrier k.val
    rw [hambient]
    exact hmember
  · rw [b.finrank_segmentCarrier,
      D.finrank_prefixCarrier_index]

/-- Every vector of the complementary consecutive BONG segment lies in the
Jordan-suffix carrier.  Equality will follow once an integral two-block
split supplies complementarity. -/
theorem segmentCarrier_prefixRank_le_suffixCarrier
    (h : PutTogetherWitness b D c) (k : Fin t)
    (hpos : 0 < D.componentRank k) :
    b.segmentCarrier (∑ i ∈ Finset.Iio k, D.componentRank i)
        (n - ∑ i ∈ Finset.Iio k, D.componentRank i) (by
          let z : Fin (D.componentRank k) := ⟨0, hpos⟩
          have hv := h.inverse_index_val k z
          have hg := (h.indexEquiv.symm ⟨k, z⟩).isLt
          omega) ≤
      D.suffixCarrier k.val := by
  let cut := ∑ i ∈ Finset.Iio k, D.componentRank i
  let z : Fin (D.componentRank k) := ⟨0, hpos⟩
  let boundary : Fin n := h.indexEquiv.symm ⟨k, z⟩
  have hboundaryVal : boundary.val = cut := by
    dsimp only [boundary, cut]
    simpa only [z, Nat.add_zero] using h.inverse_index_val k z
  have hcutLt : cut < n := by
    rw [← hboundaryVal]
    exact boundary.isLt
  rw [segmentCarrier, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  let global : Fin n := segmentIndex cut (n - cut) (by omega) j
  have hglobalVal : global.val = cut + j.val := by
    exact segmentIndex_val cut (n - cut) (by omega) j
  have hcomponent : k.val ≤ (h.indexEquiv global).1.val := by
    apply Nat.le_of_not_gt
    intro hlt
    have hbefore : ComponentIndexBefore D (h.indexEquiv global) ⟨k, z⟩ :=
      Or.inl hlt
    have hglobalLt : global < boundary := by
      apply (h.order_iff global boundary).2
      have hboundaryIndex : h.indexEquiv boundary = ⟨k, z⟩ :=
        h.indexEquiv.apply_symm_apply ⟨k, z⟩
      rw [hboundaryIndex]
      exact hbefore
    change global.val < boundary.val at hglobalLt
    rw [hglobalVal, hboundaryVal] at hglobalLt
    omega
  let suffixIndex : D.SuffixIndex k.val :=
    ⟨(h.indexEquiv global).1, hcomponent⟩
  have hmember :
      ((c (h.indexEquiv global).1).ambientVector
          (h.indexEquiv global).2 : V) ∈ D.suffixCarrier k.val := by
    apply le_iSup
      (fun i : D.SuffixIndex k.val ↦ (D.component i.1).carrier)
      suffixIndex
    exact (c (h.indexEquiv global).1).ambientVector
      (h.indexEquiv global).2 |>.property
  have hambient := h.ambientVector_eq global
  change b.ambientVector global ∈ D.suffixCarrier k.val
  rw [hambient]
  exact hmember

end BONG.PutTogetherWitness

namespace BONG.StrictJordanAdaptedAlignment

variable {m : Nat} {a : GoodBONG q L (m + 1)}
  {b : GoodBONG r M (m + 1)}

/-- At every strict source Jordan component, the scale order is no larger
than the effective norm order of the corresponding fundamental layer. -/
theorem source_scaleOrder_le_effectiveNormOrder
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) :
    ordUnit K (S.sourceJordan.scaleGenerator k) ≤
      jordanEffectiveNormOrder S.sourceJordan k := by
  change ordUnit K
      (S.weakAlignment.endpoint.sourceWeak.scaleGenerator k) ≤
    S.weakAlignment.endpoint.sourceWeak.effectiveNormOrderAt k
      (ordUnit K
        (S.weakAlignment.endpoint.sourceWeak.scaleGenerator k))
  exact S.weakAlignment.endpoint.sourceWeak.targetScale_le_effectiveNormOrderAt
    k _

/-- The last profile order of a strict Jordan component is
`2 r_k - u_k`.  In the improper case this uses the even-rank conclusion;
in the proper case the formula reduces to `r_k`. -/
theorem source_expectedOrder_last
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) :
    jordanExpectedOrder S.sourceJordan k
        ⟨S.sourceJordan.toOrthogonalDecomposition.componentRank k - 1,
          by
            simp only [Lattice.OrthogonalDecomposition.componentRank]
            exact Nat.sub_lt (S.sourceJordan.component_finrank_pos k)
              Nat.zero_lt_one⟩ =
      2 * ordUnit K (S.sourceJordan.scaleGenerator k) -
        jordanEffectiveNormOrder S.sourceJordan k := by
  let last : Fin
      (S.sourceJordan.toOrthogonalDecomposition.componentRank k) :=
    ⟨S.sourceJordan.toOrthogonalDecomposition.componentRank k - 1,
      by
        simp only [Lattice.OrthogonalDecomposition.componentRank]
        exact Nat.sub_lt (S.sourceJordan.component_finrank_pos k)
          Nat.zero_lt_one⟩
  let C := S.sourceComponentCoordinates k
  change jordanExpectedOrder S.sourceJordan k last = _
  by_cases hproper : ordUnit K (S.sourceJordan.scaleGenerator k) =
      jordanEffectiveNormOrder S.sourceJordan k
  · unfold jordanExpectedOrder
    rw [if_pos hproper]
    omega
  · have hevenRank : Even
        (S.sourceJordan.toOrthogonalDecomposition.componentRank k) := by
      rcases C.proper_or_even with hCproper | hCeven
      · exfalso
        apply hproper
        exact hCproper.symm
      · have hdiff : C.stop - C.start =
            S.sourceJordan.toOrthogonalDecomposition.componentRank k := by
          simp only [C, sourceComponentCoordinates, componentStop,
            Nat.add_sub_cancel_left]
        rwa [hdiff] at hCeven
    have hlastOdd : ¬ Even last.val := by
      rw [Nat.not_even_iff_odd]
      rcases hevenRank with ⟨d, hd⟩
      refine ⟨d - 1, ?_⟩
      dsimp only [last]
      have hpos : 0 <
          S.sourceJordan.toOrthogonalDecomposition.componentRank k := by
        simpa only [Lattice.OrthogonalDecomposition.componentRank] using
          S.sourceJordan.component_finrank_pos k
      omega
    unfold jordanExpectedOrder
    rw [if_neg hproper, if_neg hlastOdd]

/-- The first profile order of a Jordan component is its effective norm
order. -/
theorem source_expectedOrder_first
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) :
    jordanExpectedOrder S.sourceJordan k
        ⟨0, S.sourceJordan.component_finrank_pos k⟩ =
      jordanEffectiveNormOrder S.sourceJordan k := by
  unfold jordanExpectedOrder
  by_cases hproper : ordUnit K (S.sourceJordan.scaleGenerator k) =
      jordanEffectiveNormOrder S.sourceJordan k
  · rw [if_pos hproper, hproper]
  · simp only [hproper, if_false, even_iff_two_dvd, dvd_zero, if_true]

/-- Across every noninitial strict Jordan boundary, the terminal BONG order
on the left is no larger than the first BONG order on the right. -/
theorem source_boundary_order_le
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val) :
    let previous : Fin S.componentCount := ⟨k.val - 1, by omega⟩
    let last : Fin
        (S.sourceJordan.toOrthogonalDecomposition.componentRank previous) :=
      ⟨S.sourceJordan.toOrthogonalDecomposition.componentRank previous - 1,
        by
          simp only [Lattice.OrthogonalDecomposition.componentRank]
          exact Nat.sub_lt (S.sourceJordan.component_finrank_pos previous)
            Nat.zero_lt_one⟩
    let first : Fin
        (S.sourceJordan.toOrthogonalDecomposition.componentRank k) :=
      ⟨0, S.sourceJordan.component_finrank_pos k⟩
    a.order (S.sourceProfile.indexEquiv.symm ⟨previous, last⟩) ≤
      a.order (S.sourceProfile.indexEquiv.symm ⟨k, first⟩) := by
  let previous : Fin S.componentCount := ⟨k.val - 1, by omega⟩
  let last : Fin
      (S.sourceJordan.toOrthogonalDecomposition.componentRank previous) :=
    ⟨S.sourceJordan.toOrthogonalDecomposition.componentRank previous - 1,
      by
        simp only [Lattice.OrthogonalDecomposition.componentRank]
        exact Nat.sub_lt (S.sourceJordan.component_finrank_pos previous)
          Nat.zero_lt_one⟩
  let first : Fin
      (S.sourceJordan.toOrthogonalDecomposition.componentRank k) :=
    ⟨0, S.sourceJordan.component_finrank_pos k⟩
  change a.toBONG.order
      (S.sourceProfile.indexEquiv.symm ⟨previous, last⟩) ≤
    a.toBONG.order (S.sourceProfile.indexEquiv.symm ⟨k, first⟩)
  have hpreviousLt : previous < k := by
    change previous.val < k.val
    dsimp only [previous]
    omega
  have hstrict := S.sourceStrict hpreviousLt
  change ordUnit K (S.sourceJordan.scaleGenerator previous) <
    ordUnit K (S.sourceJordan.scaleGenerator k) at hstrict
  have hleftScaleNorm := S.source_scaleOrder_le_effectiveNormOrder previous
  have hrightScaleNorm := S.source_scaleOrder_le_effectiveNormOrder k
  have hleft := S.sourceProfile.order_inverse_indexEquiv previous last
  have hright := S.sourceProfile.order_inverse_indexEquiv k first
  have hlast := S.source_expectedOrder_last previous
  have hfirst := S.source_expectedOrder_first k
  rw [hlast] at hleft
  rw [hfirst] at hright
  rw [hleft, hright]
  omega

/-- Corollary 4.4(i) splits the source BONG at every noninitial strict
Jordan boundary. -/
theorem source_hasTwoBlockSplit_componentStart
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val) :
    a.toBONG.HasTwoBlockSplit (S.componentStart k) (by
      exact (S.componentStart_lt_componentStop k).le.trans
        (S.componentStop_le k)) := by
  let previous : Fin S.componentCount := ⟨k.val - 1, by omega⟩
  let last : Fin
      (S.sourceJordan.toOrthogonalDecomposition.componentRank previous) :=
    ⟨S.sourceJordan.toOrthogonalDecomposition.componentRank previous - 1,
      by
        simp only [Lattice.OrthogonalDecomposition.componentRank]
        exact Nat.sub_lt (S.sourceJordan.component_finrank_pos previous)
          Nat.zero_lt_one⟩
  let first : Fin
      (S.sourceJordan.toOrthogonalDecomposition.componentRank k) :=
    ⟨0, S.sourceJordan.component_finrank_pos k⟩
  let leftGlobal : Fin (m + 1) :=
    S.sourceProfile.indexEquiv.symm ⟨previous, last⟩
  let rightGlobal : Fin (m + 1) :=
    S.sourceProfile.indexEquiv.symm ⟨k, first⟩
  have hpreviousSucc : k.val = previous.val + 1 := by
    dsimp only [previous]
    omega
  have hlast : last.val + 1 =
      S.sourceJordan.toOrthogonalDecomposition.componentRank previous := by
    dsimp only [last]
    have hpos : 0 <
        S.sourceJordan.toOrthogonalDecomposition.componentRank previous := by
      simpa only [Lattice.OrthogonalDecomposition.componentRank] using
        S.sourceJordan.component_finrank_pos previous
    omega
  have hnext : rightGlobal.val = leftGlobal.val + 1 := by
    exact S.sourceProfile.inverse_index_val_next_component
      previous k hpreviousSucc last hlast
        (S.sourceJordan.component_finrank_pos k)
  have hrightVal : rightGlobal.val = S.componentStart k := by
    have hv := S.sourceProfile.inverse_index_val k first
    change rightGlobal.val =
      (∑ i ∈ Finset.Iio k,
        S.sourceJordan.toOrthogonalDecomposition.componentRank i) +
          first.val at hv
    change rightGlobal.val = S.componentStart k
    dsimp only [first, componentStart] at hv ⊢
    omega
  have hcut : leftGlobal.val + 1 = S.componentStart k := by
    omega
  have horder : a.order leftGlobal ≤ a.order rightGlobal := by
    simpa only [leftGlobal, rightGlobal, previous, last, first] using
      S.source_boundary_order_le k hk
  change a.toBONG.order leftGlobal ≤ a.toBONG.order rightGlobal at horder
  have hsplit := a.toBONG.beliCorollary44_i_unconditional a.good
    leftGlobal (by
      have := rightGlobal.isLt
      omega) (by
        have hrightIndex :
            (⟨leftGlobal.val + 1, by omega⟩ : Fin (m + 1)) =
              rightGlobal := Fin.ext hnext.symm
        rw [hrightIndex]
        exact horder)
  simpa only [hcut] using hsplit

/-- The left carrier in any such Corollary 4.4 split is the exact Jordan
prefix carrier. -/
theorem sourceSplit_left_carrier
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k))) :
    T.left.carrier =
      S.sourceJordan.toOrthogonalDecomposition.prefixCarrier k.val := by
  let D := S.sourceJordan.toOrthogonalDecomposition
  let h := S.weakAlignment.sourceAdapted.putTogether
  have hpos : 0 < D.componentRank k := by
    simpa only [D, Lattice.OrthogonalDecomposition.componentRank] using
      S.sourceJordan.component_finrank_pos k
  calc
    T.left.carrier = a.toBONG.segmentCarrier 0 (S.componentStart k) _ :=
      T.left.carrier_eq_segmentCarrier
    _ = D.prefixCarrier k.val := by
      convert h.segmentCarrier_zero_prefixRank_eq_prefixCarrier k hpos using 1 <;>
        simp only [D, h, componentStart, sourceJordan,
          toStrictJordanEndpointAlignment,
          StrictJordanEndpointAlignment.sourceJordan,
          StrictJordanEndpointWitness.jordan,
          Lattice.OrthogonalDecomposition.prefixCarrier,
          Lattice.OrthogonalDecomposition.componentRank,
          Lattice.WeakJordanDecomposition.toJordan_component] <;> congr

/-- The right carrier in any such split is the exact complementary Jordan
suffix carrier. -/
theorem sourceSplit_right_carrier
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k))) :
    T.right.carrier =
      S.sourceJordan.toOrthogonalDecomposition.suffixCarrier k.val := by
  let D := S.sourceJordan.toOrthogonalDecomposition
  let h := S.weakAlignment.sourceAdapted.putTogether
  have hpos : 0 < D.componentRank k := by
    simpa only [D, Lattice.OrthogonalDecomposition.componentRank] using
      S.sourceJordan.component_finrank_pos k
  have hle : T.right.carrier ≤ D.suffixCarrier k.val := by
    rw [T.right.carrier_eq_segmentCarrier]
    convert h.segmentCarrier_prefixRank_le_suffixCarrier k hpos using 1 <;>
      simp only [D, h, componentStart, sourceJordan,
        toStrictJordanEndpointAlignment,
        StrictJordanEndpointAlignment.sourceJordan,
        StrictJordanEndpointWitness.jordan,
        Lattice.OrthogonalDecomposition.suffixCarrier,
        Lattice.OrthogonalDecomposition.componentRank,
        Lattice.WeakJordanDecomposition.toJordan_component] <;> congr
  letI : Module.Finite K V := L.moduleFinite
  letI : FiniteDimensional K (D.suffixCarrier k.val) :=
    (D.suffixAmbientBasis k.val).finiteDimensional_of_finite
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hsplitDim := Submodule.finrank_add_eq_of_isCompl T.carriers_isCompl
  have hcanonical : IsCompl (D.prefixCarrier k.val)
      (D.suffixCarrier k.val) :=
    ⟨D.prefixCarrier_disjoint_suffixCarrier k.val,
      codisjoint_iff.mpr (D.prefixCarrier_sup_suffixCarrier k.val)⟩
  have hcanonicalDim := Submodule.finrank_add_eq_of_isCompl hcanonical
  rw [S.sourceSplit_left_carrier k hk T] at hsplitDim
  exact Nat.add_left_cancel (hsplitDim.trans hcanonicalDim.symm)

/-- The left Corollary 4.4 segment is integrally isometric to the canonical
Jordan prefix, by the identity on ambient vectors. -/
noncomputable def sourceSplitLeftLatticeIsometry
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k))) :
    let D := S.sourceJordan.toOrthogonalDecomposition
    Lattice.Isometry
      (q.restrict T.left.carrier T.left.nondegenerate)
      (D.prefixQuadraticSublattice k.val).space
      T.left.lattice (D.prefixQuadraticSublattice k.val).lattice := by
  let D := S.sourceJordan.toOrthogonalDecomposition
  let hcarrier := S.sourceSplit_left_carrier k hk T
  let e : T.left.carrier ≃ₗ[K] D.prefixCarrier k.val :=
    LinearEquiv.ofEq _ _ hcarrier
  refine {
    toLinearEquiv := e
    map_bilin := ?_
    map_mem := ?_ }
  · intro x y
    change q.bilin (((e x : D.prefixCarrier k.val) : V))
        (((e y : D.prefixCarrier k.val) : V)) =
      q.bilin (x : V) (y : V)
    simp [e]
  · intro x
    change x ∈ T.left.lattice ↔ e x ∈ D.prefixLattice k.val
    constructor
    · intro hx
      rw [D.mem_prefixLattice_iff,
        D.mem_prefixAmbientSubmodule_iff]
      refine ⟨?_, (e x).property⟩
      simpa [e] using T.left_contained x hx
    · intro hx
      apply T.left_contains_parent
      have hambient :=
        (D.mem_prefixAmbientSubmodule_iff k.val (e x : V)).1
          ((D.mem_prefixLattice_iff k.val (e x)).1 hx)
      simpa [e] using hambient.1

/-- The right Corollary 4.4 segment is integrally isometric to the canonical
Jordan suffix, again by the identity on ambient vectors. -/
noncomputable def sourceSplitRightLatticeIsometry
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k))) :
    let D := S.sourceJordan.toOrthogonalDecomposition
    Lattice.Isometry
      (q.restrict T.right.carrier T.right.nondegenerate)
      (D.suffixQuadraticSublattice k.val).space
      T.right.lattice (D.suffixQuadraticSublattice k.val).lattice := by
  let D := S.sourceJordan.toOrthogonalDecomposition
  let hcarrier := S.sourceSplit_right_carrier k hk T
  let e : T.right.carrier ≃ₗ[K] D.suffixCarrier k.val :=
    LinearEquiv.ofEq _ _ hcarrier
  refine {
    toLinearEquiv := e
    map_bilin := ?_
    map_mem := ?_ }
  · intro x y
    change q.bilin (((e x : D.suffixCarrier k.val) : V))
        (((e y : D.suffixCarrier k.val) : V)) =
      q.bilin (x : V) (y : V)
    simp [e]
  · intro x
    change x ∈ T.right.lattice ↔ e x ∈ D.suffixLattice k.val
    constructor
    · intro hx
      rw [D.mem_suffixLattice_iff,
        D.mem_suffixAmbientSubmodule_iff]
      refine ⟨?_, (e x).property⟩
      simpa [e] using T.right_contained x hx
    · intro hx
      have hparent : (x : V) ∈ L := by
        have hambient :=
          (D.mem_suffixAmbientSubmodule_iff k.val (e x : V)).1
            ((D.mem_suffixLattice_iff k.val (e x)).1 hx)
        simpa [e] using hambient.1
      have hmapped : T.toAmbientLinearEquiv (0, x) ∈ L := by
        change (0 : V) + (x : V) ∈ L
        simpa using hparent
      have hproduct :=
        (T.toProductLatticeIsometry.map_mem (0, x)).mpr hmapped
      exact (Lattice.mem_product_iff.mp hproduct).2

/-- After exchanging the two factors, the actual suffix and the rescaled
dual of the actual prefix give the concrete fundamental lattice at a
noninitial Jordan scale.  This is the factor order used in the proof of
Beli's Lemma 2.16(i): the suffix, whose head is a norm generator of the
fundamental layer, is component zero. -/
noncomputable def sourceFundamentalLayerSwappedIsometry
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val) :
    let D := S.sourceJordan.toOrthogonalDecomposition
    let P := D.prefixQuadraticSublattice k.val
    let U := D.suffixQuadraticSublattice k.val
    let c := Lattice.scaleTruncationUnit (K := K)
      (ordUnit K (S.sourceJordan.scaleGenerator k))
    Lattice.Isometry (U.space.orthogonalSum P.space) q
      (Lattice.product U.lattice
        (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)))
      (S.sourceJordan.fundamentalLattice k) := by
  let D := S.sourceJordan.toOrthogonalDecomposition
  let P := D.prefixQuadraticSublattice k.val
  let U := D.suffixQuadraticSublattice k.val
  let c := Lattice.scaleTruncationUnit (K := K)
    (ordUnit K (S.sourceJordan.scaleGenerator k))
  let tailCount := S.componentCount - k.val - 1
  have hcount : k.val + (tailCount + 1) = S.componentCount := by
    dsimp only [tailCount]
    omega
  let swap : Lattice.Isometry (U.space.orthogonalSum P.space)
      (P.space.orthogonalSum U.space)
      (Lattice.product U.lattice
        (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)))
      (Lattice.product
        (Lattice.rescale c (Lattice.dualLattice P.space P.lattice))
        U.lattice) :=
    Lattice.orthogonalProductSwap
  let split := S.sourceJordan.fundamentalLayerSplitIsometry hcount hk
  have hkEq : (⟨k.val, by omega⟩ : Fin S.componentCount) = k := Fin.ext rfl
  simpa only [D, P, U, c, hkEq] using swap.trans split

end BONG.StrictJordanAdaptedAlignment

end Bong
