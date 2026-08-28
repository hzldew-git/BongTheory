/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.Valuation
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Index

/-!
# The Artin--Schreier quotient of the dyadic residue field

O'Meara 63:4 ultimately uses one elementary fact about the finite residue
field of a dyadic local field: in characteristic two, the image of
`z ↦ z² + z` has additive index two.  Consequently the sum of any two
elements outside that image lies in the image.

This file proves that finite-field calculation and transports it to the
normalized valuation used by the BONG development.  It is the common residue
calculation behind uniqueness of the defect-`2e` square class and the equal
defect product rule.
-/

namespace Bong.Dyadic

section FiniteField

variable (k : Type*) [Field k] [Finite k] [CharP k 2]

/-- The Artin--Schreier additive endomorphism in characteristic two. -/
noncomputable def artinSchreierHom : k →+ k where
  toFun x := x ^ 2 + x
  map_zero' := by simp
  map_add' x y := by
    have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
    rw [add_sq]
    simp [htwo]
    ring

omit [Finite k] in
/-- The kernel of `z ↦ z² + z` is exactly `{0,1}`. -/
theorem mem_artinSchreierHom_ker_iff (x : k) :
    x ∈ (artinSchreierHom k).ker ↔ x = 0 ∨ x = 1 := by
  rw [AddMonoidHom.mem_ker]
  change x ^ 2 + x = 0 ↔ _
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  constructor
  · intro h
    have hfactor : x * (x + 1) = 0 := by
      calc
        x * (x + 1) = x ^ 2 + x := by ring
        _ = 0 := h
    rcases mul_eq_zero.mp hfactor with hx | hx
    · exact Or.inl hx
    · right
      have hneg : (-1 : k) = 1 := by
        apply neg_eq_iff_add_eq_zero.mpr
        have hone : (1 : k) + 1 = 0 := by
          norm_num at htwo ⊢
          exact htwo
        exact hone
      exact (eq_neg_of_add_eq_zero_left hx).trans hneg
  · rintro (rfl | rfl)
    · simp
    · have hone : (1 : k) + 1 = 0 := by
        norm_num at htwo ⊢
        exact htwo
      simpa using hone

/-- The Artin--Schreier kernel has two elements. -/
theorem artinSchreierHom_ker_card :
    Nat.card (artinSchreierHom k).ker = 2 := by
  let zeroKer : (artinSchreierHom k).ker :=
    ⟨0, by simp [artinSchreierHom]⟩
  rw [Nat.card_eq_two_iff' zeroKer]
  let oneKer : (artinSchreierHom k).ker := ⟨1, by
    rw [AddMonoidHom.mem_ker]
    change (1 : k) ^ 2 + 1 = 0
    have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
    have hone : (1 : k) + 1 = 0 := by
      norm_num at htwo ⊢
      exact htwo
    simpa using hone⟩
  refine ⟨oneKer, ?_, ?_⟩
  · intro h
    have hval := congrArg Subtype.val h
    simp [oneKer, zeroKer] at hval
  · intro x hx
    rcases (mem_artinSchreierHom_ker_iff k x).mp x.property with h | h
    · exfalso
      apply hx
      exact Subtype.ext h
    · exact Subtype.ext h

/-- The Artin--Schreier image has additive index two. -/
theorem artinSchreierHom_range_index :
    (artinSchreierHom k).range.index = 2 := by
  let H := (artinSchreierHom k).range
  have hkerIndex :
      (artinSchreierHom k).ker.index = Nat.card H :=
    AddSubgroup.index_ker (artinSchreierHom k)
  have hker := (artinSchreierHom k).ker.index_mul_card
  have hrange := H.index_mul_card
  rw [hkerIndex, artinSchreierHom_ker_card] at hker
  change H.index = 2
  apply Nat.mul_right_cancel (Nat.card_pos (α := H))
  calc
    H.index * Nat.card H = Nat.card k := hrange
    _ = Nat.card H * 2 := hker.symm
    _ = 2 * Nat.card H := Nat.mul_comm _ _

/-- The two non-Artin--Schreier elements lie in the same nontrivial coset. -/
theorem add_mem_artinSchreierHom_range_of_not_mem {a b : k}
    (ha : a ∉ (artinSchreierHom k).range)
    (hb : b ∉ (artinSchreierHom k).range) :
    a + b ∈ (artinSchreierHom k).range := by
  let H := (artinSchreierHom k).range
  obtain ⟨c, hc⟩ :=
    AddSubgroup.index_eq_two_iff.mp (artinSchreierHom_range_index k)
  have hac : a + c ∈ H := by
    rcases hc a with h | h
    · exact h.1
    · exact (ha h.1).elim
  have hbc : b + c ∈ H := by
    rcases hc b with h | h
    · exact h.1
    · exact (hb h.1).elim
  have hsum := H.add_mem hac hbc
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have heq : (a + c) + (b + c) = a + b := by
    have hcc : c + c = 0 := by
      calc
        c + c = (2 : k) * c := by ring
        _ = 0 := by rw [htwo, zero_mul]
    rw [show (a + c) + (b + c) = (a + b) + (c + c) by abel,
      hcc, add_zero]
  rw [heq] at hsum
  exact hsum

end FiniteField

section LocalField

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The valuation ring belonging to the project's normalized additive
valuation. -/
noncomputable abbrev normalizedValuationRing :=
  (AddValuation.toValuation (ord K)).valuationSubring

/-- The residue field of the normalized valuation ring. -/
noncomputable abbrev normalizedResidueField :=
  IsLocalRing.ResidueField (normalizedValuationRing K)

/-- Membership in the normalized valuation ring in additive-order form. -/
theorem mem_normalizedValuationRing_iff {x : K} :
    x ∈ normalizedValuationRing K ↔ IsIntegral K x := by
  change
    Multiplicative.ofAdd (OrderDual.toDual (ord K x)) ≤
        Multiplicative.ofAdd (OrderDual.toDual 0) ↔
      0 ≤ ord K x
  simp only [Multiplicative.ofAdd_le, OrderDual.toDual_le_toDual]

/-- Maximal-ideal membership in the normalized valuation ring in
additive-order form. -/
theorem mem_normalizedMaximalIdeal_iff
    (x : normalizedValuationRing K) :
    x ∈ IsLocalRing.maximalIdeal (normalizedValuationRing K) ↔
      IsInMaximalIdeal K (x : K) := by
  let v := AddValuation.toValuation (ord K)
  change x ∈ IsLocalRing.maximalIdeal v.valuationSubring ↔
    0 < ord K (x : K)
  rw [Valuation.mem_maximalIdeal_iff K v]
  change
    Multiplicative.ofAdd (OrderDual.toDual (ord K (x : K))) <
        Multiplicative.ofAdd (OrderDual.toDual 0) ↔
      0 < ord K (x : K)
  simp only [Multiplicative.ofAdd_lt, OrderDual.toDual_lt_toDual]

/-- The normalized residue field is finite. -/
noncomputable instance normalizedResidueFieldFinite :
    Finite (normalizedResidueField K) := by
  letI : IsNonarchimedeanLocalField K :=
    DyadicContext.toIsNonarchimedeanLocalField
  let v := AddValuation.toValuation (ord K)
  let A := v.valuationSubring
  have hA : A = (ValuativeRel.valuation K).valuationSubring := by
    apply (Valuation.isEquiv_iff_valuationSubring _ _).mp
    exact ValuativeRel.isEquiv _ _
  change Finite (IsLocalRing.ResidueField A)
  rw [hA]
  change Finite (IsLocalRing.ResidueField
    (ValuativeRel.valuation K).integer)
  infer_instance

/-- The normalized residue field has characteristic two. -/
noncomputable instance normalizedResidueFieldCharTwo :
    CharP (normalizedResidueField K) 2 := by
  let v := AddValuation.toValuation (ord K)
  let A := v.valuationSubring
  let k := IsLocalRing.ResidueField A
  have htwoA : (2 : A) ∈ IsLocalRing.maximalIdeal A := by
    exact (mem_normalizedMaximalIdeal_iff K (2 : A)).2 (ord_two_pos K)
  have htwoZero : (2 : k) = 0 := by
    change IsLocalRing.residue A (2 : A) = 0
    exact (IsLocalRing.residue_eq_zero_iff (2 : A)).mpr htwoA
  exact (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr htwoZero

/-- An integral field element has Artin--Schreier residue if its residue is
of the form `z²+z`. -/
def IsArtinSchreierResidue (a : K) : Prop :=
  ∃ z : K, IsIntegral K z ∧
    IsInMaximalIdeal K (z ^ 2 + z - a)

/-- Residue-field characterization of `IsArtinSchreierResidue`. -/
theorem isArtinSchreierResidue_iff_mem_range
    {a : K} (ha : IsIntegral K a) :
    IsArtinSchreierResidue K a ↔
      IsLocalRing.residue (normalizedValuationRing K)
          (⟨a, (mem_normalizedValuationRing_iff K).2 ha⟩ :
            normalizedValuationRing K) ∈
        (artinSchreierHom (normalizedResidueField K)).range := by
  let A := normalizedValuationRing K
  let k := normalizedResidueField K
  let aA : A := ⟨a, (mem_normalizedValuationRing_iff K).2 ha⟩
  constructor
  · rintro ⟨z, hzIntegral, hzMax⟩
    let zA : A :=
      ⟨z, (mem_normalizedValuationRing_iff K).2 hzIntegral⟩
    refine ⟨IsLocalRing.residue A zA, ?_⟩
    change
      IsLocalRing.residue A zA ^ 2 + IsLocalRing.residue A zA =
        IsLocalRing.residue A aA
    rw [← map_pow, ← map_add]
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (IsLocalRing.residue_eq_zero_iff _).2
    apply (mem_normalizedMaximalIdeal_iff K _).2
    simpa [zA, aA] using hzMax
  · rintro ⟨zBar, hzBar⟩
    obtain ⟨zA, hzA⟩ := IsLocalRing.residue_surjective zBar
    refine ⟨(zA : K), ?_, ?_⟩
    · exact (mem_normalizedValuationRing_iff K).1 zA.property
    · have hdMem : zA ^ 2 + zA - aA ∈
          IsLocalRing.maximalIdeal A := by
        apply (IsLocalRing.residue_eq_zero_iff _).1
        change IsLocalRing.residue A (zA ^ 2 + zA - aA) = 0
        rw [map_sub, map_add, map_pow, hzA]
        exact sub_eq_zero.mpr hzBar
      have hdMax :=
        (mem_normalizedMaximalIdeal_iff K (zA ^ 2 + zA - aA)).1 hdMem
      simpa [aA] using hdMax

/-- Two integral elements with non-Artin--Schreier residues have an
Artin--Schreier sum. -/
theorem isArtinSchreierResidue_add_of_not
    {a b : K} (ha : IsIntegral K a) (hb : IsIntegral K b)
    (hna : ¬IsArtinSchreierResidue K a)
    (hnb : ¬IsArtinSchreierResidue K b) :
    IsArtinSchreierResidue K (a + b) := by
  have hab : IsIntegral K (a + b) := by
    exact (min_ord_le_ord_add K a b).trans' (le_min ha hb)
  rw [isArtinSchreierResidue_iff_mem_range K hab]
  let A := normalizedValuationRing K
  let aA : A := ⟨a, (mem_normalizedValuationRing_iff K).2 ha⟩
  let bA : A := ⟨b, (mem_normalizedValuationRing_iff K).2 hb⟩
  have hna' : IsLocalRing.residue A aA ∉
      (artinSchreierHom (normalizedResidueField K)).range := by
    intro h
    exact hna ((isArtinSchreierResidue_iff_mem_range K ha).2 h)
  have hnb' : IsLocalRing.residue A bA ∉
      (artinSchreierHom (normalizedResidueField K)).range := by
    intro h
    exact hnb ((isArtinSchreierResidue_iff_mem_range K hb).2 h)
  have hsum := add_mem_artinSchreierHom_range_of_not_mem
    (normalizedResidueField K) hna' hnb'
  change IsLocalRing.residue A
      (⟨a + b, (mem_normalizedValuationRing_iff K).2 hab⟩ : A) ∈
    (artinSchreierHom (normalizedResidueField K)).range
  have habA :
      (⟨a + b, (mem_normalizedValuationRing_iff K).2 hab⟩ : A) =
        aA + bA := by
    rfl
  rw [habA, map_add]
  exact hsum

end LocalField

end Bong.Dyadic
