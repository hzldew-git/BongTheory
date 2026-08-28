/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma32Seeds
import Bong.Bong.Beli2019JordanApproximationProfile
import Bong.Bong.Beli2009JordanProfileBoundary
import Bong.Bong.Beli2009OmearaConditionI
import Bong.Bong.Beli2009ComponentCongruence
import Bong.Bong.Beli2009JordanProfileInternal
import Bong.Lattice.Omeara9328Necessity
import Bong.Lattice.OrthogonalDecompositionPrefixVolume
import Bong.Lattice.ModularVolume

/-!
# Concrete Jordan-profile seeds for Beli (2019), Lemma 3.2

The seed interface in `Beli2019Lemma32Seeds` records the two scalar inputs
used by Beli's two-step approximation recurrence.  This file constructs
those inputs for an arbitrary good BONG profiled by a strict Jordan
decomposition.

At a noninitial component, O'Meara 93:28(i), applied to the identity
isometry between the adapted and the prescribed Jordan decompositions,
identifies the good-BONG prefix product with the prescribed Jordan-prefix
determinant modulo the actual fundamental ideal.  The odd seed uses the
first BONG value in the component and the canonical norm generator of the
same fundamental lattice; Beli (2009), Lemma 2.16(i), identifies the
normalized weight depth with the relevant alpha.
-/

namespace Bong

open Dyadic Module
open scoped BigOperators

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice.JordanDecomposition.SameFundamentalType

/-- Equal complete fundamental type forces equality of the valuation of
every proper Jordan-prefix determinant.  Indeed, the prefix volume is the
sum of the component volumes, while a modular component has volume order
equal to its rank times its scale order.  Both ranks and scale orders are
part of the complete fundamental type. -/
theorem prefixDeterminantUnit_order_eq
    {d : Nat}
    {J H : Lattice.JordanDecomposition q L (d + 2)}
    (F : Lattice.JordanDecomposition.SameFundamentalType J H)
    (z : Fin (d + 1)) :
    ordUnit K (H.prefixDeterminantUnit z) =
      ordUnit K (J.prefixDeterminantUnit z) := by
  have hdetVolume (X : Lattice.JordanDecomposition q L (d + 2)) :
      ordUnit K (X.prefixDeterminantUnit z) =
        Lattice.volumeOrder
          (X.toOrthogonalDecomposition.prefixQuadraticSublattice
            (z.val + 1)).space
          (X.toOrthogonalDecomposition.prefixQuadraticSublattice
            (z.val + 1)).lattice := by
    unfold Lattice.JordanDecomposition.prefixDeterminantUnit
      Lattice.QuadraticSublattice.refinedDeterminantUnit
    apply WithTop.coe_injective
    rw [Lattice.coe_volumeOrder, Dyadic.coe_ordUnit,
      Lattice.coe_determinantUnit]
  rw [hdetVolume H, hdetVolume J]
  rw [H.toOrthogonalDecomposition.volumeOrder_prefixQuadraticSublattice_eq_sum
      (n := z.val) (by omega),
    J.toOrthogonalDecomposition.volumeOrder_prefixQuadraticSublattice_eq_sum
      (n := z.val) (by omega)]
  apply Finset.sum_congr rfl
  intro i _
  let iH :=
    (H.toOrthogonalDecomposition.prefixIndexEquiv
      (z.val + 1) (by omega) i).1
  let iJ :=
    (J.toOrthogonalDecomposition.prefixIndexEquiv
      (z.val + 1) (by omega) i).1
  have hiEq : iH = iJ := by
    apply Fin.ext
    rfl
  have hH := (H.modular iH).volumeOrder_eq
  have hJ := (J.modular iJ).volumeOrder_eq
  change Lattice.volumeOrder
      (H.component iH).space (H.component iH).lattice = _ at hH
  change Lattice.volumeOrder
      (J.component iJ).space (J.component iJ).lattice = _ at hJ
  change Lattice.volumeOrder
      (H.component iH).space (H.component iH).lattice =
    Lattice.volumeOrder
      (J.component iJ).space (J.component iJ).lattice
  rw [hH, hJ]
  have hrank := F.componentRank_eq iJ
  have hscale := F.scaleOrder_eq iJ
  rw [F.indexEquiv_apply_eq_self] at hrank hscale
  unfold Lattice.JordanDecomposition.componentRank at hrank
  unfold Lattice.JordanDecomposition.fundamentalScaleOrder at hscale
  rw [hiEq]
  exact congrArg₂ (· * ·) (by exact_mod_cast hrank) hscale

end Lattice.JordanDecomposition.SameFundamentalType

namespace BONG.JordanOrderProfileWitness

/-- At a proper Jordan boundary the prefix product and the determinant of
the prescribed Jordan prefix have the same valuation. -/
theorem prefixProduct_order_eq_prefixDeterminantUnit
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t) :
    ordUnit K (a.prefixProduct ((P.boundaryIndex z).val + 1)) =
      ordUnit K (J.prefixDeterminantUnit z) := by
  obtain ⟨S⟩ := a.nonempty_strictJordanAdaptedAlignment a (fun _ ↦ rfl)
  let F := Lattice.JordanDecomposition.sameFundamentalTypeOfIsometry
    S.sourceJordan J (Lattice.Isometry.refl q L)
  have hcount : S.componentCount = t + 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_congr F.indexEquiv
  let Js := S.sourceJordanSucc hcount
  let Ps := S.sourceProfileSucc hcount
  let Fs : Lattice.JordanDecomposition.SameFundamentalType Js J :=
    F.castSourceComponentCount hcount
  have hRank :
      Js.toOrthogonalDecomposition.componentRank =
        J.toOrthogonalDecomposition.componentRank := by
    funext k
    have hk := Fs.componentRank_eq k
    rw [Fs.indexEquiv_apply_eq_self] at hk
    exact hk.symm
  have hboundary : Ps.boundaryIndex z = P.boundaryIndex z := by
    apply Fin.ext
    have hs := Ps.boundaryIndex_succ_val_eq_componentRankPrefix z
    have ht := P.boundaryIndex_succ_val_eq_componentRankPrefix z
    rw [hRank] at hs
    omega
  have hsourceClass :=
    S.unitSquareClass_sourcePrefixProduct_eq_prefixDeterminantUnit hcount z
  rw [hboundary] at hsourceClass
  cases t with
  | zero => exact Fin.elim0 z
  | succ d =>
      exact (ordUnit_eq_of_unitSquareClass_eq (K := K) hsourceClass).trans
        (Fs.prefixDeterminantUnit_order_eq z).symm

set_option maxHeartbeats 3000000 in
/-- At every proper Jordan boundary, the prefix product of an arbitrary
good BONG is congruent to the determinant of the prescribed Jordan prefix.
This is O'Meara 93:28(i) for the identity isometry, with the adapted-prefix
determinant replaced by the good-BONG prefix product. -/
theorem prefixProduct_congruent_prefixDeterminantUnit
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t) :
    BONG.GoodBONG.UnitsCongruentModulo
      (a.prefixProduct ((P.boundaryIndex z).val + 1))
      (J.prefixDeterminantUnit z) (J.fundamentalIdeal z) := by
  obtain ⟨S⟩ := a.nonempty_strictJordanAdaptedAlignment a (fun _ ↦ rfl)
  let F := Lattice.JordanDecomposition.sameFundamentalTypeOfIsometry
    S.sourceJordan J (Lattice.Isometry.refl q L)
  have hcount : S.componentCount = t + 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_congr F.indexEquiv
  let Js := S.sourceJordanSucc hcount
  let Ps := S.sourceProfileSucc hcount
  let Fs : Lattice.JordanDecomposition.SameFundamentalType Js J :=
    F.castSourceComponentCount hcount
  have hRank :
      Js.toOrthogonalDecomposition.componentRank =
        J.toOrthogonalDecomposition.componentRank := by
    funext k
    have hk := Fs.componentRank_eq k
    rw [Fs.indexEquiv_apply_eq_self] at hk
    exact hk.symm
  have hboundary : Ps.boundaryIndex z = P.boundaryIndex z := by
    apply Fin.ext
    have hs := Ps.boundaryIndex_succ_val_eq_componentRankPrefix z
    have ht := P.boundaryIndex_succ_val_eq_componentRankPrefix z
    rw [hRank] at hs
    omega
  have hsourceClass :=
    S.unitSquareClass_sourcePrefixProduct_eq_prefixDeterminantUnit hcount z
  rw [hboundary] at hsourceClass
  cases t with
  | zero => exact Fin.elim0 z
  | succ d =>
      have hcondition : J.Omeara9328ConditionI Js :=
        (Lattice.JordanDecomposition.omeara9328Conditions_of_isometry J Js
          (Lattice.Isometry.refl q L)).1
      have hraw := hcondition z
      exact BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
        (Js.prefixDeterminantUnit z)
        (a.prefixProduct ((P.boundaryIndex z).val + 1))
        (J.prefixDeterminantUnit z) (J.prefixDeterminantUnit z)
        (J.fundamentalIdeal z) hsourceClass.symm rfl hraw

/-- The first good-BONG value in every component of an arbitrary strict
Jordan profile is a norm generator of the corresponding fundamental
lattice.  The proof compares the profile with the Jordan splitting adapted
to the same BONG and then transports the generator across equality of the
complete fundamental type. -/
theorem componentFirstValue_isNormGeneratorValue
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (p : Fin (t + 1)) :
    Lattice.IsNormGeneratorValue q (J.fundamentalLattice p)
      (P.componentFirstValue p) := by
  obtain ⟨S⟩ := a.nonempty_strictJordanAdaptedAlignment a (fun _ ↦ rfl)
  let F := Lattice.JordanDecomposition.sameFundamentalTypeOfIsometry
    S.sourceJordan J (Lattice.Isometry.refl q L)
  have hcount : S.componentCount = t + 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_congr F.indexEquiv
  let Js := S.sourceJordanSucc hcount
  let Ps := S.sourceProfileSucc hcount
  let Fs : Lattice.JordanDecomposition.SameFundamentalType Js J :=
    F.castSourceComponentCount hcount
  have hRank :
      Js.toOrthogonalDecomposition.componentRank =
        J.toOrthogonalDecomposition.componentRank := by
    funext k
    have hk := Fs.componentRank_eq k
    rw [Fs.indexEquiv_apply_eq_self] at hk
    exact hk.symm
  let k : Fin S.componentCount := Fin.cast hcount.symm p
  have hsource : Lattice.IsNormGeneratorValue q
      (Js.fundamentalLattice p) (Ps.componentFirstValue p) := by
    have hfirst :=
      S.toStrictJordanEndpointAlignment.sourceFirstGenerator_fundamentalLattice k
    unfold Js Ps StrictJordanAdaptedAlignment.sourceJordanSucc
      StrictJordanAdaptedAlignment.sourceProfileSucc
    rw [Lattice.JordanDecomposition.castComponentCount_fundamentalLattice]
    rw [JordanOrderProfileWitness.castComponentCount_componentFirstValue]
    rw [show Fin.cast hcount.symm p = k by rfl,
      S.sourceProfile_componentFirstValue_eq_endpointFirstValue k]
    simpa [StrictJordanAdaptedAlignment.sourceJordan,
      StrictJordanAdaptedAlignment.toStrictJordanEndpointAlignment] using hfirst
  have hvalue : Ps.componentFirstValue p = P.componentFirstValue p := by
    unfold JordanOrderProfileWitness.componentFirstValue
    apply congrArg a.valueUnit
    apply Fin.ext
    rw [Ps.inverse_index_val, P.inverse_index_val]
    simp only [Fin.val_mk]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact congrFun hRank i
  have hgroup := Fs.normGroup_eq p
  rw [Fs.indexEquiv_apply_eq_self] at hgroup
  rw [← hvalue]
  exact Lattice.JordanDecomposition.isNormGeneratorValue_of_normGroupSet_eq hsource
    (by
      simpa only [Lattice.JordanDecomposition.fundamentalNormGroup] using
        hgroup.symm)
    (J.exists_fundamentalNormGenerator p)

/-- The right-end value attached to the *fundamental* norm order of a
profiled Jordan component.  Unlike `terminalValue`, this definition remains
the correct norm generator when the component norm itself does not attain
the effective norm of the scale truncation. -/
noncomputable def fundamentalTerminalValue
    {n c : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L c}
    (P : JordanOrderProfileWitness a.toBONG J) (p : Fin c) : Kˣ :=
  let last : Fin (J.toOrthogonalDecomposition.componentRank p) :=
    ⟨J.toOrthogonalDecomposition.componentRank p - 1, by
      exact Nat.sub_lt (J.component_finrank_pos p) Nat.zero_lt_one⟩
  uniformizerPowerUnit K
      (2 * ordUnit K (J.fundamentalNormGenerator p) -
        2 * ordUnit K (J.scaleGenerator p)) *
    a.valueUnit (P.indexEquiv.symm ⟨p, last⟩)

/-- The fundamental right-end value is a norm generator of the intrinsic
scale truncation.  This is the profile-invariant norm-generator assertion
needed for the arbitrary-generator form of Beli (2019), Corollary 3.3. -/
theorem fundamentalTerminalValue_isNormGeneratorValue_succ
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (p : Fin (t + 1)) :
    Lattice.IsNormGeneratorValue q (J.fundamentalLattice p)
      (P.fundamentalTerminalValue p) := by
  obtain ⟨S⟩ := a.nonempty_strictJordanAdaptedAlignment a (fun _ ↦ rfl)
  let F := Lattice.JordanDecomposition.sameFundamentalTypeOfIsometry
    S.sourceJordan J (Lattice.Isometry.refl q L)
  have hcount : S.componentCount = t + 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_congr F.indexEquiv
  let Js := S.sourceJordanSucc hcount
  let Ps := S.sourceProfileSucc hcount
  let Fs : Lattice.JordanDecomposition.SameFundamentalType Js J :=
    F.castSourceComponentCount hcount
  have hRank :
      Js.toOrthogonalDecomposition.componentRank =
        J.toOrthogonalDecomposition.componentRank := by
    funext k
    have hk := Fs.componentRank_eq k
    rw [Fs.indexEquiv_apply_eq_self] at hk
    exact hk.symm
  have hscale : ordUnit K (Js.scaleGenerator p) =
      ordUnit K (J.scaleGenerator p) := by
    have h := Fs.scaleOrder_eq p
    rw [Fs.indexEquiv_apply_eq_self] at h
    exact h.symm
  have hfund : ordUnit K (Js.fundamentalNormGenerator p) =
      ordUnit K (J.fundamentalNormGenerator p) := by
    have h := Fs.fundamentalNormGenerator_order_eq p
    rw [Fs.indexEquiv_apply_eq_self] at h
    exact h.symm
  have hsourceNorm : ordUnit K (Js.normGenerator p) =
      ordUnit K (Js.fundamentalNormGenerator p) :=
    S.sourceNormGenerator_order_eq_fundamental hcount p
  let lastJs : Fin (Js.toOrthogonalDecomposition.componentRank p) :=
    ⟨Js.toOrthogonalDecomposition.componentRank p - 1, by
      exact Nat.sub_lt (Js.component_finrank_pos p) Nat.zero_lt_one⟩
  let lastJ : Fin (J.toOrthogonalDecomposition.componentRank p) :=
    ⟨J.toOrthogonalDecomposition.componentRank p - 1, by
      exact Nat.sub_lt (J.component_finrank_pos p) Nat.zero_lt_one⟩
  have hlastIndex : Ps.indexEquiv.symm ⟨p, lastJs⟩ =
      P.indexEquiv.symm ⟨p, lastJ⟩ := by
    apply Fin.ext
    rw [Ps.inverse_index_val, P.inverse_index_val]
    simp only [lastJs, lastJ]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      exact congrFun hRank i
    · rw [congrFun hRank p]
  have hvalue : Ps.terminalValue p = P.fundamentalTerminalValue p := by
    unfold JordanOrderProfileWitness.terminalValue fundamentalTerminalValue
    change uniformizerPowerUnit K
          (2 * ordUnit K (Js.normGenerator p) -
            2 * ordUnit K (Js.scaleGenerator p)) *
        a.valueUnit (Ps.indexEquiv.symm ⟨p, lastJs⟩) =
      uniformizerPowerUnit K
          (2 * ordUnit K (J.fundamentalNormGenerator p) -
            2 * ordUnit K (J.scaleGenerator p)) *
        a.valueUnit (P.indexEquiv.symm ⟨p, lastJ⟩)
    rw [hsourceNorm, hfund, hscale, hlastIndex]
  have hsource : Lattice.IsNormGeneratorValue q
      (Js.fundamentalLattice p) (Ps.terminalValue p) :=
    S.sourceTerminalValue_isNormGeneratorValue hcount p
  have hgroup := Fs.normGroup_eq p
  rw [Fs.indexEquiv_apply_eq_self] at hgroup
  rw [← hvalue]
  exact Lattice.JordanDecomposition.isNormGeneratorValue_of_normGroupSet_eq hsource
    (by
      simpa only [Lattice.JordanDecomposition.fundamentalNormGroup] using
        hgroup.symm)
    (J.exists_fundamentalNormGenerator p)

/-- Component-count-generic wrapper for the fundamental terminal generator.
The zero-component case is empty. -/
theorem fundamentalTerminalValue_isNormGeneratorValue
    {n c : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L c}
    (P : JordanOrderProfileWitness a.toBONG J) (p : Fin c) :
    Lattice.IsNormGeneratorValue q (J.fundamentalLattice p)
      (P.fundamentalTerminalValue p) := by
  cases c with
  | zero => exact Fin.elim0 p
  | succ t => exact P.fundamentalTerminalValue_isNormGeneratorValue_succ p

/-- The rescaled last good-BONG value of a profiled Jordan component is a
generator of the corresponding fundamental norm group as soon as the
displayed component norm order is already the effective (fundamental) norm
order.  The proof compares with the strict splitting adapted to the same
good BONG.  Complete fundamental type identifies the ranks, scales and
fundamental norm groups, while the order hypothesis identifies the square
rescaling used in `terminalValue`. -/
theorem componentTerminalValue_isNormGeneratorValue
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (p : Fin (t + 1))
    (hnorm : ordUnit K (J.normGenerator p) =
      ordUnit K (J.fundamentalNormGenerator p)) :
    Lattice.IsNormGeneratorValue q (J.fundamentalLattice p)
      (P.terminalValue p) := by
  obtain ⟨S⟩ := a.nonempty_strictJordanAdaptedAlignment a (fun _ ↦ rfl)
  let F := Lattice.JordanDecomposition.sameFundamentalTypeOfIsometry
    S.sourceJordan J (Lattice.Isometry.refl q L)
  have hcount : S.componentCount = t + 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_congr F.indexEquiv
  let Js := S.sourceJordanSucc hcount
  let Ps := S.sourceProfileSucc hcount
  let Fs : Lattice.JordanDecomposition.SameFundamentalType Js J :=
    F.castSourceComponentCount hcount
  have hRank :
      Js.toOrthogonalDecomposition.componentRank =
        J.toOrthogonalDecomposition.componentRank := by
    funext k
    have hk := Fs.componentRank_eq k
    rw [Fs.indexEquiv_apply_eq_self] at hk
    exact hk.symm
  have hscale : ordUnit K (Js.scaleGenerator p) =
      ordUnit K (J.scaleGenerator p) := by
    have h := Fs.scaleOrder_eq p
    rw [Fs.indexEquiv_apply_eq_self] at h
    exact h.symm
  have hfund : ordUnit K (Js.fundamentalNormGenerator p) =
      ordUnit K (J.fundamentalNormGenerator p) := by
    have h := Fs.fundamentalNormGenerator_order_eq p
    rw [Fs.indexEquiv_apply_eq_self] at h
    exact h.symm
  have hsourceNorm : ordUnit K (Js.normGenerator p) =
      ordUnit K (Js.fundamentalNormGenerator p) :=
    S.sourceNormGenerator_order_eq_fundamental hcount p
  have hnormOrders : ordUnit K (Js.normGenerator p) =
      ordUnit K (J.normGenerator p) := by
    rw [hsourceNorm, hfund, hnorm]
  let lastJs : Fin (Js.toOrthogonalDecomposition.componentRank p) :=
    ⟨Js.toOrthogonalDecomposition.componentRank p - 1, by
      exact Nat.sub_lt (Js.component_finrank_pos p) Nat.zero_lt_one⟩
  let lastJ : Fin (J.toOrthogonalDecomposition.componentRank p) :=
    ⟨J.toOrthogonalDecomposition.componentRank p - 1, by
      exact Nat.sub_lt (J.component_finrank_pos p) Nat.zero_lt_one⟩
  have hlastIndex : Ps.indexEquiv.symm ⟨p, lastJs⟩ =
      P.indexEquiv.symm ⟨p, lastJ⟩ := by
    apply Fin.ext
    rw [Ps.inverse_index_val, P.inverse_index_val]
    simp only [Fin.val_mk, lastJs, lastJ]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      exact congrFun hRank i
    · rw [congrFun hRank p]
  have hvalue : Ps.terminalValue p = P.terminalValue p := by
    unfold JordanOrderProfileWitness.terminalValue
    rw [hnormOrders, hscale]
    change uniformizerPowerUnit K
          (2 * ordUnit K (J.normGenerator p) -
            2 * ordUnit K (J.scaleGenerator p)) *
        a.valueUnit (Ps.indexEquiv.symm ⟨p, lastJs⟩) =
      uniformizerPowerUnit K
          (2 * ordUnit K (J.normGenerator p) -
            2 * ordUnit K (J.scaleGenerator p)) *
        a.valueUnit (P.indexEquiv.symm ⟨p, lastJ⟩)
    rw [hlastIndex]
  have hsource : Lattice.IsNormGeneratorValue q
      (Js.fundamentalLattice p) (Ps.terminalValue p) :=
    S.sourceTerminalValue_isNormGeneratorValue hcount p
  have hgroup := Fs.normGroup_eq p
  rw [Fs.indexEquiv_apply_eq_self] at hgroup
  rw [← hvalue]
  exact Lattice.JordanDecomposition.isNormGeneratorValue_of_normGroupSet_eq hsource
    (by
      simpa only [Lattice.JordanDecomposition.fundamentalNormGroup] using
        hgroup.symm)
    (J.exists_fundamentalNormGenerator p)

/-- The determinant seed at the empty prefix. -/
def determinantSeedDataOfStartZero
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J)
    (C : a.JordanBlockCoordinates) (hzero : C.start = 0) :
    BONG.GoodBONG.Omeara9328DeterminantSeedData a C where
  leftDet := 1
  boundary := Or.inl ⟨hzero, rfl⟩

/-- The explicit O'Meara 93:28 determinant seed at an internal Jordan
boundary.  Its `leftDet` field is definitionally the prescribed prefix
determinant, which is important when two decompositions are compared. -/
noncomputable def determinantSeedDataOfBoundary
    [Beli2006AlphaLaws.{u, v} K]
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J)
    (C : a.JordanBlockCoordinates)
    (z : Fin t) (hz : C.start = (P.boundaryIndex z).val + 1) :
    BONG.GoodBONG.Omeara9328DeterminantSeedData a C := by
  let hexists := P.exists_orderedFundamentalIdeal_alpha_eq_min z
  let I := Classical.choose hexists
  have hspec := Classical.choose_spec hexists
  have hcarrier : I.carrier = J.fundamentalIdeal z := hspec.1
  have hformula : a.alphaValue (P.boundaryIndex z) =
      min (I.order : ℚ) (a.halfGapValue (P.boundaryIndex z)) := hspec.2
  refine {
    leftDet := J.prefixDeterminantUnit z
    boundary := Or.inr ⟨I, ?_, ?_, ?_, ?_⟩ }
  · have halpha : 0 ≤ a.alphaValue (P.boundaryIndex z) :=
      (a.alpha_p2 (P.boundaryIndex z)).1
    have horderQ : (0 : ℚ) ≤ (I.order : ℚ) :=
      halpha.trans (hformula.trans_le (min_le_left _ _))
    exact_mod_cast horderQ
  · rw [hz]
    exact P.prefixProduct_order_eq_prefixDeterminantUnit z
  · rw [hz, hcarrier]
    exact P.prefixProduct_congruent_prefixDeterminantUnit z
  · have hstartPos : 0 < C.start := by omega
    have hstartLt : C.start < n + 2 :=
      C.start_lt_stop.trans_le C.stop_le
    rw [a.prefixAlphaCap_of_internal hstartPos hstartLt]
    have hidx :
        (⟨C.start - 1, by omega⟩ : Fin (n + 1)) =
          P.boundaryIndex z := by
      apply Fin.ext
      change C.start - 1 = (P.boundaryIndex z).val
      omega
    rw [hidx]
    have hleQ : a.alphaValue (P.boundaryIndex z) ≤ (I.order : ℚ) :=
      hformula.trans_le (min_le_left _ _)
    exact_mod_cast hleQ

/-- O'Meara 93:28(i) and Beli (2009), Lemma 2.16(ii), construct the
determinant seed for any Jordan block whose left endpoint is either zero or
an actual boundary of the prescribed strict Jordan profile. -/
theorem exists_determinantSeedData
    [Beli2006AlphaLaws.{u, v} K]
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J)
    (C : a.JordanBlockCoordinates)
    (hboundary : C.start = 0 ∨
      ∃ z : Fin t, C.start = (P.boundaryIndex z).val + 1) :
    Nonempty (BONG.GoodBONG.Omeara9328DeterminantSeedData a C) := by
  rcases hboundary with hzero | ⟨z, hz⟩
  · exact ⟨P.determinantSeedDataOfStartZero C hzero⟩
  · exact ⟨P.determinantSeedDataOfBoundary C z hz⟩

end BONG.JordanOrderProfileWitness

namespace BONG.WeakJordanOrderProfileWitness

/-- The left endpoint of a component in a strict weak-Jordan profile is
either the empty prefix or the successor of a genuine Jordan boundary. -/
theorem componentStart_eq_zero_or_boundaryIndex_succ
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin (t + 1)) :
    let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
    let C := w.jordanBlockCoordinates hW p
    C.start = 0 ∨
      ∃ z : Fin t, C.start = (P.boundaryIndex z).val + 1 := by
  dsimp only
  let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
  let C := w.jordanBlockCoordinates hW p
  by_cases hp : p.val = 0
  · left
    change w.componentStart p = 0
    unfold componentStart
    have hpzero : p = (0 : Fin (t + 1)) := Fin.ext hp
    subst p
    simp
  · right
    let z : Fin t := ⟨p.val - 1, by omega⟩
    refine ⟨z, ?_⟩
    have hb := P.boundaryIndex_succ_val_eq_componentRankPrefix z
    have hzRight :
        Lattice.JordanDecomposition.boundaryRightIndex z = p := by
      apply Fin.ext
      change z.val + 1 = p.val
      dsimp only [z]
      omega
    rw [hzRight] at hb
    change w.componentStart p = (P.boundaryIndex z).val + 1
    rw [hb]
    unfold componentStart
    rfl

/-- The canonical determinant seed of a strict-profile block, with an
explicit branch at the empty prefix and an explicit preceding-boundary
index otherwise. -/
noncomputable def strictDeterminantSeedData
    [Beli2006AlphaLaws.{u, v} K]
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin (t + 1)) :
    let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
    let C := w.jordanBlockCoordinates hW p
    BONG.GoodBONG.Omeara9328DeterminantSeedData a C := by
  dsimp only
  let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
  let C := w.jordanBlockCoordinates hW p
  by_cases hp : p.val = 0
  · apply P.determinantSeedDataOfStartZero C
    change w.componentStart p = 0
    unfold componentStart
    have hpzero : p = (0 : Fin (t + 1)) := Fin.ext hp
    subst p
    simp
  · let z : Fin t := ⟨p.val - 1, by omega⟩
    apply P.determinantSeedDataOfBoundary C z
    have hb := P.boundaryIndex_succ_val_eq_componentRankPrefix z
    have hzRight :
        Lattice.JordanDecomposition.boundaryRightIndex z = p := by
      apply Fin.ext
      change z.val + 1 = p.val
      dsimp only [z]
      omega
    rw [hzRight] at hb
    change w.componentStart p = (P.boundaryIndex z).val + 1
    rw [hb]
    unfold componentStart
    rfl

/-- Count-polymorphic wrapper for `strictDeterminantSeedData`.  A selected
component itself rules out the empty decomposition, while the successor
branch exposes the boundary indexing required by O'Meara 93:28. -/
noncomputable def strictDeterminantSeedDataAny
    [Beli2006AlphaLaws.{u, v} K]
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    (W : Lattice.WeakJordanDecomposition q L t)
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin t) :
    let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
    let C := w.jordanBlockCoordinates hW p
    BONG.GoodBONG.Omeara9328DeterminantSeedData a C := by
  cases t with
  | zero => exact Fin.elim0 p
  | succ t => exact strictDeterminantSeedData W hW hstrict P p

@[simp]
theorem strictDeterminantSeedData_leftDet_of_component_zero
    [Beli2006AlphaLaws.{u, v} K]
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin (t + 1)) (hp : p.val = 0) :
    (strictDeterminantSeedData W hW hstrict P p).leftDet = 1 := by
  unfold strictDeterminantSeedData
  simp only [hp, ↓reduceDIte]
  rfl

@[simp]
theorem strictDeterminantSeedData_leftDet_of_component_ne_zero
    [Beli2006AlphaLaws.{u, v} K]
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin (t + 1)) (hp : p.val ≠ 0) :
    (strictDeterminantSeedData W hW hstrict P p).leftDet =
      (W.toJordan hstrict).prefixDeterminantUnit
        ⟨p.val - 1, by omega⟩ := by
  unfold strictDeterminantSeedData
  simp only [hp, ↓reduceDIte]
  rfl

@[simp]
theorem strictDeterminantSeedDataAny_leftDet_of_component_zero
    [Beli2006AlphaLaws.{u, v} K]
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    (W : Lattice.WeakJordanDecomposition q L t)
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin t) (hp : p.val = 0) :
    (strictDeterminantSeedDataAny W hW hstrict P p).leftDet = 1 := by
  cases t with
  | zero => exact Fin.elim0 p
  | succ t =>
      exact strictDeterminantSeedData_leftDet_of_component_zero
        W hW hstrict P p hp

@[simp]
theorem strictDeterminantSeedDataAny_leftDet_of_component_ne_zero
    [Beli2006AlphaLaws.{u, v} K]
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    (W : Lattice.WeakJordanDecomposition q L t)
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin t) (hp : p.val ≠ 0) :
    (strictDeterminantSeedDataAny W hW hstrict P p).leftDet =
      ((W.toJordan hstrict).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice p.val).refinedDeterminantUnit := by
  cases t with
  | zero => exact Fin.elim0 p
  | succ t =>
      change (strictDeterminantSeedData W hW hstrict P p).leftDet = _
      rw [strictDeterminantSeedData_leftDet_of_component_ne_zero
        W hW hstrict P p hp]
      unfold Lattice.JordanDecomposition.prefixDeterminantUnit
      congr 2
      simp only [Fin.val_mk]
      omega

/-- The checked first BONG index of a strict weak-Jordan block is the
inverse profile coordinate `(p,0)`. -/
theorem jordanBlockCoordinates_firstIndex_eq_inverse_zero
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin (t + 1)) :
    let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
    let C := w.jordanBlockCoordinates hW p
    C.firstIndex = P.indexEquiv.symm
      ⟨p, ⟨0, W.component_finrank_pos p⟩⟩ := by
  dsimp only
  let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
  let C := w.jordanBlockCoordinates hW p
  apply Fin.ext
  have h := w.inverse_index_val p ⟨0, W.component_finrank_pos p⟩
  change
    (w.indexEquiv.symm ⟨p, ⟨0, W.component_finrank_pos p⟩⟩).val =
      w.componentStart p at h
  change C.start =
    (w.indexEquiv.symm ⟨p, ⟨0, W.component_finrank_pos p⟩⟩).val
  exact h.symm

/-- Beli (2009), Lemma 2.16(i), together with equality of the norm group of
the same fundamental lattice, constructs the norm-generator seed at every
nonunary strict weak-Jordan block. -/
noncomputable def normGeneratorSeedDataOf
    [Beli2006AlphaLaws.{u, v} K]
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin (t + 1))
    (A : Kˣ)
    (hASpec : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice p) A)
    (hnext :
      let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
      let C := w.jordanBlockCoordinates hW p
      C.start + 1 < C.stop) :
    let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
    let C := w.jordanBlockCoordinates hW p
    BONG.GoodBONG.Beli2009NormGeneratorSeedData a C
      A hnext := by
  dsimp only
  dsimp only at hnext
  let J := W.toJordan hstrict
  let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
  let C := w.jordanBlockCoordinates hW p
  have hfirst :=
    jordanBlockCoordinates_firstIndex_eq_inverse_zero W hW hstrict P p
  have hfirstSpec : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice p) (a.valueUnit C.firstIndex) := by
    rw [hfirst]
    exact P.componentFirstValue_isNormGeneratorValue p
  have hsameOrder : ordUnit K (a.valueUnit C.firstIndex) = ordUnit K A := by
    apply (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp
    exact hfirstSpec.2.symm.trans hASpec.2
  have hcoordinate : P.indexEquiv C.firstIndex =
      ⟨p, ⟨0, W.component_finrank_pos p⟩⟩ := by
    rw [hfirst]
    simp
  let alphaIndex : Fin (n + 1) := ⟨C.start, by
    have hstop := C.stop_le
    change C.start + 1 < C.stop at hnext
    omega⟩
  have halphaCast : alphaIndex.castSucc = C.firstIndex := by
    apply Fin.ext
    rfl
  have hlocal :
      (P.indexEquiv alphaIndex.castSucc).2.val + 1 <
        J.componentRank (P.indexEquiv alphaIndex.castSucc).1 := by
    rw [halphaCast, hcoordinate]
    change 0 + 1 < finrank K (W.component p).carrier
    change C.start + 1 < C.stop at hnext
    have hCstop : C.stop =
        C.start + finrank K (W.component p).carrier := rfl
    rw [hCstop] at hnext
    omega

  have hweight := P.internal_weightOrder_eq_order_add_alpha alphaIndex hlocal
  rw [halphaCast, hcoordinate] at hweight
  have hdepth :
      (((J.fundamentalWeightOrder p -
          ordUnit K (a.valueUnit C.firstIndex) : Int) : ℚ)) =
        a.alphaValue alphaIndex := by
    push_cast
    change (J.fundamentalWeightOrder p : ℚ) -
        (a.order C.firstIndex : ℚ) = a.alphaValue alphaIndex
    linarith
  refine {
    depth := J.fundamentalWeightOrder p -
      ordUnit K (a.valueUnit C.firstIndex)
    depth_nonnegative := ?_
    depth_eq_alpha := ?_
    same_order := hsameOrder
    congruent := ?_
    firstStep_descending := ?_ }
  · have halphaNonnegative : 0 ≤ a.alphaValue alphaIndex :=
      (a.alpha_p2 alphaIndex).1
    have hdepthNonnegativeQ : (0 : ℚ) ≤
        ((J.fundamentalWeightOrder p -
          ordUnit K (a.valueUnit C.firstIndex) : Int) : ℚ) := by
      rw [hdepth]
      exact halphaNonnegative
    exact_mod_cast hdepthNonnegativeQ
  · simpa only [alphaIndex] using hdepth
  · exact Lattice.unitsCongruentModulo_normalizedWeight_of_normGroupSet_eq
      (a.valueUnit C.firstIndex) A hfirstSpec hASpec hsameOrder rfl
  · have hfirstOrder :=
      (C.beli2009Lemma213_i C.start (by omega) C.start_lt_stop).1 (by omega)
    have hnextOrder :=
      (C.beli2009Lemma213_i (C.start + 1) (by omega) hnext).2 (by omega)
    change a.order (C.index (C.start + 1) hnext) ≤
      a.order C.firstIndex
    change a.order (C.index (C.start + 1) hnext) ≤
      a.order (C.index C.start C.start_lt_stop)
    rw [hnextOrder, hfirstOrder]
    have hscale := W.targetScale_le_effectiveNormOrderAt p
      (ordUnit K (W.scaleGenerator p))
    change 2 * ordUnit K (W.scaleGenerator p) -
        W.effectiveNormOrderAt p (ordUnit K (W.scaleGenerator p)) ≤
      W.effectiveNormOrderAt p (ordUnit K (W.scaleGenerator p))
    omega

/-- The canonical fundamental norm generator gives the default odd seed. -/
noncomputable def normGeneratorSeedData
    [Beli2006AlphaLaws.{u, v} K]
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin (t + 1))
    (hnext :
      let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
      let C := w.jordanBlockCoordinates hW p
      C.start + 1 < C.stop) :
    let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
    let C := w.jordanBlockCoordinates hW p
    BONG.GoodBONG.Beli2009NormGeneratorSeedData a C
      ((W.toJordan hstrict).fundamentalNormGenerator p) hnext := by
  exact normGeneratorSeedDataOf W hW hstrict P p
    ((W.toJordan hstrict).fundamentalNormGenerator p)
    ((W.toJordan hstrict).fundamentalNormGenerator_spec p) hnext

/-- All seeds in Beli (2019), Lemma 3.2, for a block of an arbitrary good
BONG carrying a strict weak-Jordan profile.  No approximation hypothesis is
left in the statement. -/
noncomputable def strictJordanApproximationSeedsWith
    [Beli2006AlphaLaws.{u, v} K]
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin (t + 1))
    (determinant :
      let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
      let C := w.jordanBlockCoordinates hW p
      BONG.GoodBONG.Omeara9328DeterminantSeedData a C)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice p) A) :
    let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
    let C := w.jordanBlockCoordinates hW p
    BONG.GoodBONG.JordanApproximationSeeds a C := by
  dsimp only
  let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
  let C := w.jordanBlockCoordinates hW p
  exact BONG.GoodBONG.JordanApproximationSeeds.ofOmeara9328AndNormGenerator
    determinant A
    (fun hnext => normGeneratorSeedDataOf W hW hstrict P p A hA hnext)

/-- Count-polymorphic wrapper for `strictJordanApproximationSeedsWith`.
The empty component family is impossible because `p : Fin t`; in the
successor branch this is exactly the strict-profile seed theorem above. -/
noncomputable def strictJordanApproximationSeedsWithAny
    [Beli2006AlphaLaws.{u, v} K]
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    (W : Lattice.WeakJordanDecomposition q L t)
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin t)
    (determinant :
      let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
      let C := w.jordanBlockCoordinates hW p
      BONG.GoodBONG.Omeara9328DeterminantSeedData a C)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice p) A) :
    let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
    let C := w.jordanBlockCoordinates hW p
    BONG.GoodBONG.JordanApproximationSeeds a C := by
  cases t with
  | zero => exact Fin.elim0 p
  | succ t =>
      exact strictJordanApproximationSeedsWith W hW hstrict P p determinant A hA

@[simp]
theorem strictJordanApproximationSeedsWithAny_leftDet
    [Beli2006AlphaLaws.{u, v} K]
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    (W : Lattice.WeakJordanDecomposition q L t)
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin t)
    (determinant :
      let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
      let C := w.jordanBlockCoordinates hW p
      BONG.GoodBONG.Omeara9328DeterminantSeedData a C)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice p) A) :
    (strictJordanApproximationSeedsWithAny W hW hstrict P p
      determinant A hA).leftDet = determinant.leftDet := by
  cases t with
  | zero => exact Fin.elim0 p
  | succ t => rfl

@[simp]
theorem strictJordanApproximationSeedsWithAny_normGenerator
    [Beli2006AlphaLaws.{u, v} K]
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    (W : Lattice.WeakJordanDecomposition q L t)
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin t)
    (determinant :
      let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
      let C := w.jordanBlockCoordinates hW p
      BONG.GoodBONG.Omeara9328DeterminantSeedData a C)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice p) A) :
    (strictJordanApproximationSeedsWithAny W hW hstrict P p
      determinant A hA).normGenerator = A := by
  cases t with
  | zero => exact Fin.elim0 p
  | succ t => rfl

/-- The custom-generator specialization, with the canonical determinant
seed at the left Jordan boundary. -/
noncomputable def strictJordanApproximationSeedsOf
    [Beli2006AlphaLaws.{u, v} K]
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin (t + 1))
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice p) A) :
    let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
    let C := w.jordanBlockCoordinates hW p
    BONG.GoodBONG.JordanApproximationSeeds a C := by
  dsimp only
  let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
  let C := w.jordanBlockCoordinates hW p
  let determinant := strictDeterminantSeedData W hW hstrict P p
  exact strictJordanApproximationSeedsWith W hW hstrict P p determinant A hA

/-- The canonical-generator specialization of
`strictJordanApproximationSeedsOf`. -/
noncomputable def strictJordanApproximationSeeds
    [Beli2006AlphaLaws.{u, v} K]
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin (t + 1)) :
    let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
    let C := w.jordanBlockCoordinates hW p
    BONG.GoodBONG.JordanApproximationSeeds a C := by
  exact strictJordanApproximationSeedsOf W hW hstrict P p
    ((W.toJordan hstrict).fundamentalNormGenerator p)
    ((W.toJordan hstrict).fundamentalNormGenerator_spec p)

end BONG.WeakJordanOrderProfileWitness

end Bong
