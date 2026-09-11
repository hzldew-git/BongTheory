/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Dyadic.PrincipalUnitResidueQuotient
import Bong.Dyadic.UnitDefectClassification

/-!
# Odd layers of the dyadic unit square-class filtration

At every positive odd depth below `2e`, passage from principal units to unit
square classes does not change the successive quotient.  Consequently that
layer has cardinality equal to the residue-field norm.
-/

namespace Bong.Dyadic

universe u

variable (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A principal unit mapped to its class modulo valuation-unit squares. -/
noncomputable def principalUnitClassHom (n : Nat) :
    principalUnitSubgroup K n →* ValuationUnitClass K where
  toFun u := valuationUnitClassHom K
    ⟨(u : Kˣ), u.property.1⟩
  map_one' := by
    change valuationUnitClassHom K 1 = 1
    exact map_one _
  map_mul' u v := by
    change valuationUnitClassHom K
        (⟨(u : Kˣ), u.property.1⟩ *
          ⟨(v : Kˣ), v.property.1⟩) =
      valuationUnitClassHom K ⟨(u : Kˣ), u.property.1⟩ *
        valuationUnitClassHom K ⟨(v : Kˣ), v.property.1⟩
    exact map_mul _ _ _

private theorem principalUnitClassHom_mem_filtration
    (n : Nat) (u : principalUnitSubgroup K n) :
    principalUnitClassHom K n u ∈
      principalUnitValuationClassSubgroup K n := by
  let v : valuationUnitSubgroup K := ⟨(u : Kˣ), u.property.1⟩
  refine ⟨v, ?_, rfl⟩
  exact u.property

/-- The principal-unit class homomorphism with its codomain restricted to
the corresponding filtration subgroup. -/
noncomputable def principalUnitClassInFiltrationHom (n : Nat) :
    principalUnitSubgroup K n →*
      principalUnitValuationClassSubgroup K n where
  toFun u :=
    ⟨principalUnitClassHom K n u,
      principalUnitClassHom_mem_filtration K n u⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (principalUnitClassHom K n)
  map_mul' u v := by
    apply Subtype.ext
    exact map_mul (principalUnitClassHom K n) u v

/-- The next square-class filtration subgroup, viewed inside the current
one. -/
noncomputable def principalUnitValuationClassSuccSubgroup (n : Nat) :
    Subgroup (principalUnitValuationClassSubgroup K n) :=
  (principalUnitValuationClassSubgroup K (n + 1)).comap
    (principalUnitValuationClassSubgroup K n).subtype

/-- The quotient map from depth-`n` principal units to the corresponding
successive unit-square-class layer. -/
noncomputable def principalUnitSquareClassLayerHom (n : Nat) :
    principalUnitSubgroup K n →*
      (principalUnitValuationClassSubgroup K n ⧸
        principalUnitValuationClassSuccSubgroup K n) :=
  (QuotientGroup.mk' (principalUnitValuationClassSuccSubgroup K n)).comp
    (principalUnitClassInFiltrationHom K n)

theorem principalUnitSquareClassLayerHom_surjective (n : Nat) :
    Function.Surjective (principalUnitSquareClassLayerHom K n) := by
  intro z
  obtain ⟨c, rfl⟩ := Quotient.exists_rep z
  rcases c.property with ⟨v, hv, hvc⟩
  let u : principalUnitSubgroup K n :=
    ⟨((v : valuationUnitSubgroup K) : Kˣ), hv⟩
  refine ⟨u, ?_⟩
  apply congrArg
    (QuotientGroup.mk' (principalUnitValuationClassSuccSubgroup K n))
  apply Subtype.ext
  exact hvc

private theorem isSquare_mul_of_valuationUnitClassHom_eq
    (a b : valuationUnitSubgroup K)
    (h : valuationUnitClassHom K a = valuationUnitClassHom K b) :
    IsSquare ((a : Kˣ) * (b : Kˣ)) := by
  change QuotientGroup.mk' (Subgroup.square (valuationUnitSubgroup K)) a =
    QuotientGroup.mk' (Subgroup.square (valuationUnitSubgroup K)) b at h
  rw [QuotientGroup.mk'_eq_mk'] at h
  obtain ⟨s, hs, hasb⟩ := h
  have hsField : IsSquare (s : Kˣ) := by
    change (s : Kˣ) ∈ Subgroup.square Kˣ
    apply valuationUnitSubgroup_square_map_le_square K
    exact ⟨s, hs, rfl⟩
  have haSquare : IsSquare ((a : Kˣ) ^ 2) :=
    ⟨(a : Kˣ), pow_two (a : Kˣ)⟩
  have hproduct := haSquare.mul hsField
  have hasbField : (a : Kˣ) * (s : Kˣ) = (b : Kˣ) := by
    exact congrArg Subtype.val hasb
  rw [← hasbField]
  simpa only [pow_two, mul_assoc] using hproduct

/-- At a positive odd depth below `2e`, a square principal unit already
lies one step deeper. -/
theorem isSquare_principalUnit_mem_succ_of_odd
    {n : Nat} (hn : 0 < n) (hlt : n < 2 * ramificationIndex K)
    (hodd : Odd n) (a : Kˣ) (ha : a ∈ principalUnitSubgroup K n)
    (haSquare : IsSquare a) :
    a ∈ principalUnitSubgroup K (n + 1) := by
  refine ⟨ha.1, ?_⟩
  by_contra hnot
  have hlower : (n : WithTop Int) ≤ ord K ((a : K) - 1) :=
    (Lattice.mem_powerIdeal_iff (K := K) (n : Int) ((a : K) - 1)).1 ha.2
  have hnotUpper : ¬ (((n + 1 : Nat) : Int) : WithTop Int) ≤
      ord K ((a : K) - 1) := by
    intro hupper
    apply hnot
    exact (Lattice.mem_powerIdeal_iff (K := K)
      ((n + 1 : Nat) : Int) ((a : K) - 1)).2 hupper
  have hfinite : ord K ((a : K) - 1) ≠ ⊤ := by
    intro htop
    apply hnotUpper
    rw [htop]
    simp
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have horder : ord K ((a : K) - 1) = (n : WithTop Int) := by
    rw [← hm] at hlower hnotUpper ⊢
    norm_cast at hlower hnotUpper ⊢
    omega
  obtain ⟨t, hat⟩ := haSquare
  have horderOne : ord K (1 - (t : K) ^ 2) = (n : WithTop Int) := by
    have heq : 1 - (t : K) ^ 2 = -((a : K) - 1) := by
      rw [hat]
      simp only [Units.val_mul]
      ring
    rw [heq, ord_neg, horder]
  have hevenInt := even_order_one_sub_sq_of_lt_two_mul_e_proved
    (K := K) (t : K) (n : Int) horderOne (by exact_mod_cast hn)
      (by exact_mod_cast hlt)
  have hoddInt : Odd (n : Int) := by exact_mod_cast hodd
  exact (Int.not_odd_iff_even.mpr hevenInt hoddInt).elim

theorem mem_principalUnitSquareClassLayerHom_ker_iff_of_odd
    {n : Nat} (hn : 0 < n) (hlt : n < 2 * ramificationIndex K)
    (hodd : Odd n) (u : principalUnitSubgroup K n) :
    u ∈ (principalUnitSquareClassLayerHom K n).ker ↔
      (u : Kˣ) ∈ principalUnitSubgroup K (n + 1) := by
  change principalUnitSquareClassLayerHom K n u = 1 ↔ _
  constructor
  · intro h
    have hmem := (QuotientGroup.eq_one_iff _).1 h
    change principalUnitClassHom K n u ∈
      principalUnitValuationClassSubgroup K (n + 1) at hmem
    rcases hmem with ⟨v, hv, hclass⟩
    let vu : valuationUnitSubgroup K := ⟨(u : Kˣ), u.property.1⟩
    have hvInN : (v : Kˣ) ∈ principalUnitSubgroup K n :=
      principalUnitSubgroup_anti K (Nat.le_succ n) hv
    have hproductMem : (u : Kˣ) * (v : Kˣ) ∈
        principalUnitSubgroup K n :=
      (principalUnitSubgroup K n).mul_mem u.property hvInN
    have hclass' : valuationUnitClassHom K vu =
        valuationUnitClassHom K v := by
      exact hclass.symm
    have hproductSquare : IsSquare ((u : Kˣ) * (v : Kˣ)) :=
      isSquare_mul_of_valuationUnitClassHom_eq K vu v hclass'
    have hproductNext := isSquare_principalUnit_mem_succ_of_odd
      K hn hlt hodd ((u : Kˣ) * (v : Kˣ)) hproductMem hproductSquare
    have hrecover := (principalUnitSubgroup K (n + 1)).mul_mem
      hproductNext ((principalUnitSubgroup K (n + 1)).inv_mem hv)
    change (((u : Kˣ) * (v : Kˣ)) * (v : Kˣ)⁻¹) ∈
      principalUnitSubgroup K (n + 1) at hrecover
    simpa using hrecover
  · intro hnext
    apply (QuotientGroup.eq_one_iff _).2
    change principalUnitClassHom K n u ∈
      principalUnitValuationClassSubgroup K (n + 1)
    let v : principalUnitSubgroupInUnits K (n + 1) :=
      ⟨⟨(u : Kˣ), u.property.1⟩, hnext⟩
    exact ⟨v, v.property, rfl⟩

theorem principalUnitSquareClassLayerHom_ker_eq_of_odd
    {n : Nat} (hn : 0 < n) (hlt : n < 2 * ramificationIndex K)
    (hodd : Odd n) :
    (principalUnitSquareClassLayerHom K n).ker =
      principalUnitResidueKernel K n hn := by
  ext u
  rw [mem_principalUnitSquareClassLayerHom_ker_iff_of_odd
    K hn hlt hodd u, mem_principalUnitResidueKernel_iff]

/-- At positive odd depth below `2e`, the unit-square-class layer is
multiplicatively equivalent to the additive residue group. -/
noncomputable def oddUnitSquareClassLayerEquivResidueField
    {n : Nat} (hn : 0 < n) (hlt : n < 2 * ramificationIndex K)
    (hodd : Odd n) :
    (principalUnitValuationClassSubgroup K n ⧸
        principalUnitValuationClassSuccSubgroup K n) ≃*
      Multiplicative (normalizedResidueField K) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective
    (principalUnitSquareClassLayerHom K n)
    (principalUnitSquareClassLayerHom_surjective K n)
  have hker := principalUnitSquareClassLayerHom_ker_eq_of_odd
    K hn hlt hodd
  let e' :
      (principalUnitSubgroup K n ⧸ principalUnitResidueKernel K n hn) ≃*
        (principalUnitValuationClassSubgroup K n ⧸
          principalUnitValuationClassSuccSubgroup K n) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans e
  exact e'.symm.trans (principalUnitQuotientEquivResidueField K n hn)

/-- Every positive odd layer below `2e` has cardinality equal to the residue
field. -/
theorem card_oddUnitSquareClassLayer
    {n : Nat} (hn : 0 < n) (hlt : n < 2 * ramificationIndex K)
    (hodd : Odd n) :
    Nat.card
        (principalUnitValuationClassSubgroup K n ⧸
          principalUnitValuationClassSuccSubgroup K n) =
      Nat.card (normalizedResidueField K) :=
  Nat.card_congr
    (oddUnitSquareClassLayerEquivResidueField K hn hlt hodd).toEquiv

end Bong.Dyadic
