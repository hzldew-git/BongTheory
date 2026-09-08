/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.DiscriminantClassProof
import Bong.Dyadic.UnitSquareClassOddLayer

/-!
# Cardinality of the dyadic unit square-class group

This file proves the unit square-class count customarily cited as O'Meara
63:9.  The principal-unit filtration has residue-field cardinality at each
positive odd layer below `2e`, collapses at the intervening even layers, and
has exactly the trivial and discriminant classes at depth `2e`.
-/

namespace Bong.Dyadic

universe u

variable (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

noncomputable local instance discriminantLaws :
    DyadicDiscriminantClassLaws K :=
  dyadicDiscriminantClassLawsProved

noncomputable local instance maximalDefectLaws :
    DyadicMaximalDefectClassLaws K :=
  dyadicMaximalDefectClassLawsProved

/-- The depth-zero principal-unit filtration is the full unit square-class
group. -/
theorem principalUnitValuationClassSubgroup_zero_eq_top :
    principalUnitValuationClassSubgroup K 0 = ⊤ := by
  apply top_unique
  intro c _hc
  obtain ⟨u, rfl⟩ := Quotient.exists_rep c
  refine ⟨u, ?_, rfl⟩
  change (u : Kˣ) ∈ principalUnitSubgroup K 0
  rw [principalUnitSubgroup_zero]
  exact u.property

/-- The depth-one filtration is also the full unit square-class group. -/
theorem principalUnitValuationClassSubgroup_one_eq_top :
    principalUnitValuationClassSubgroup K 1 = ⊤ := by
  apply top_unique
  intro c _hc
  obtain ⟨u, rfl⟩ := Quotient.exists_rep c
  apply valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
  exact one_le_quadraticDefect_of_unit (u : Kˣ) u.property

/-- At every even depth strictly below `2e`, including depth zero, the unit
square-class filtration does not change at the following step. -/
theorem principalUnitValuationClassSubgroup_even_eq_succ
    (r : Nat) (hr : r < ramificationIndex K) :
    principalUnitValuationClassSubgroup K (2 * r) =
      principalUnitValuationClassSubgroup K (2 * r + 1) := by
  by_cases hrZero : r = 0
  · subst r
    rw [principalUnitValuationClassSubgroup_zero_eq_top,
      principalUnitValuationClassSubgroup_one_eq_top]
  · apply principalUnitValuationClassSubgroup_eq_succ_of_even
    · omega
    · omega
    · exact even_two_mul r

/-- The subgroup at the next depth, viewed inside the present filtration
subgroup, is canonically equivalent to that next subgroup itself. -/
noncomputable def principalUnitValuationClassSuccEquiv (n : Nat) :
    principalUnitValuationClassSuccSubgroup K n ≃*
      principalUnitValuationClassSubgroup K (n + 1) :=
  Subgroup.subgroupOfEquivOfLe
    (principalUnitValuationClassSubgroup_anti K (Nat.le_succ n))

/-- Cardinalities in two consecutive filtration depths are related by the
cardinality of their quotient layer. -/
theorem card_principalUnitValuationClassSubgroup_eq_layer_mul_succ
    (n : Nat) :
    Nat.card (principalUnitValuationClassSubgroup K n) =
      Nat.card
          (principalUnitValuationClassSubgroup K n ⧸
            principalUnitValuationClassSuccSubgroup K n) *
        Nat.card (principalUnitValuationClassSubgroup K (n + 1)) := by
  calc
    Nat.card (principalUnitValuationClassSubgroup K n) =
        Nat.card
            (principalUnitValuationClassSubgroup K n ⧸
              principalUnitValuationClassSuccSubgroup K n) *
          Nat.card (principalUnitValuationClassSuccSubgroup K n) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    _ = Nat.card
            (principalUnitValuationClassSubgroup K n ⧸
              principalUnitValuationClassSuccSubgroup K n) *
          Nat.card (principalUnitValuationClassSubgroup K (n + 1)) := by
      rw [Nat.card_congr (principalUnitValuationClassSuccEquiv K n).toEquiv]

private theorem discriminantUnit_not_isSquare :
    ¬IsSquare
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit := by
  let laws : DyadicDiscriminantClassLaws K := inferInstance
  intro hsquare
  have htop := quadraticDefect_eq_top_of_isSquare K hsquare
  rw [laws.discriminant_defect] at htop
  exact ENat.coe_ne_top _ htop

private theorem isSquare_of_valuationUnitClass_eq_one
    (u : valuationUnitSubgroup K)
    (h : valuationUnitClassHom K u = 1) :
    IsSquare (u : Kˣ) := by
  have huSquare : u ∈ Subgroup.square (valuationUnitSubgroup K) :=
    (QuotientGroup.eq_one_iff u).1 h
  change IsSquare u at huSquare
  obtain ⟨s, hs⟩ := huSquare
  refine ⟨(s : Kˣ), ?_⟩
  exact congrArg ((↑) : valuationUnitSubgroup K → Kˣ) hs

/-- The endpoint filtration at depth `2e` has exactly two elements: the
trivial class and the distinguished discriminant class. -/
theorem card_principalUnitValuationClassSubgroup_two_mul_e :
    Nat.card
        (principalUnitValuationClassSubgroup K
          (2 * ramificationIndex K)) = 2 := by
  let laws : DyadicDiscriminantClassLaws K := inferInstance
  let deltaUnit : valuationUnitSubgroup K :=
    ⟨laws.discriminantUnit, laws.discriminant_isValuationUnit⟩
  let oneClass : principalUnitValuationClassSubgroup K
      (2 * ramificationIndex K) := 1
  have hdeltaMem : valuationUnitClassHom K deltaUnit ∈
      principalUnitValuationClassSubgroup K
        (2 * ramificationIndex K) := by
    apply valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
    exact laws.discriminant_defect.symm.le
  let deltaClass : principalUnitValuationClassSubgroup K
      (2 * ramificationIndex K) :=
    ⟨valuationUnitClassHom K deltaUnit, hdeltaMem⟩
  rw [Nat.card_eq_two_iff' oneClass]
  refine ⟨deltaClass, ?_, ?_⟩
  · intro hdeltaOne
    have hclass : valuationUnitClassHom K deltaUnit = 1 := by
      exact congrArg Subtype.val hdeltaOne
    exact discriminantUnit_not_isSquare K
      (isSquare_of_valuationUnitClass_eq_one K deltaUnit hclass)
  · intro c hc
    obtain ⟨u, hu⟩ := Quotient.exists_rep c.1
    change valuationUnitClassHom K u = c.1 at hu
    have huMem : valuationUnitClassHom K u ∈
        principalUnitValuationClassSubgroup K
          (2 * ramificationIndex K) := by
      rw [hu]
      exact c.property
    have huDefect :
        ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
          quadraticDefect K (u : Kˣ) :=
      natCast_le_quadraticDefect_of_unitClass_mem u
        (2 * ramificationIndex K) huMem
    rcases isSquare_or_isSquare_div_discriminant_of_defect_ge_twoE
        (u : Kˣ) huDefect with huSquare | huDeltaSquare
    · exfalso
      apply hc
      apply Subtype.ext
      change c.1 = (1 : ValuationUnitClass K)
      rw [← hu]
      apply valuationUnitClassToSquareClass_injective K
      rw [valuationUnitClassToSquareClass_apply, map_one]
      exact (QuotientGroup.eq_one_iff (u : Kˣ)).2 huSquare
    · apply Subtype.ext
      apply valuationUnitClassToSquareClass_injective K
      change valuationUnitClassToSquareClass K c.1 =
        valuationUnitClassToSquareClass K (valuationUnitClassHom K deltaUnit)
      rw [valuationUnitClassToSquareClass_apply]
      have hquotient :
          squareClass K ((u : Kˣ) / laws.discriminantUnit) = 1 :=
        (QuotientGroup.eq_one_iff _).2 huDeltaSquare
      have heq : squareClass K (u : Kˣ) =
          squareClass K laws.discriminantUnit := by
        change squareClassHom K
          ((u : Kˣ) / laws.discriminantUnit) = 1 at hquotient
        rw [map_div, div_eq_one] at hquotient
        exact hquotient
      rw [← hu]
      exact heq

/-- Each pair consisting of an even collapse and the following odd layer
contributes one residue-field factor to the filtration cardinality. -/
theorem card_principalUnitValuationClassSubgroup_even_step
    (r : Nat) (hr : r < ramificationIndex K) :
    Nat.card (principalUnitValuationClassSubgroup K (2 * r)) =
      Nat.card (normalizedResidueField K) *
        Nat.card (principalUnitValuationClassSubgroup K (2 * (r + 1))) := by
  rw [principalUnitValuationClassSubgroup_even_eq_succ K r hr]
  have hnPos : 0 < 2 * r + 1 := by omega
  have hnLt : 2 * r + 1 < 2 * ramificationIndex K := by omega
  have hnOdd : Odd (2 * r + 1) := ⟨r, by omega⟩
  rw [card_principalUnitValuationClassSubgroup_eq_layer_mul_succ K,
    card_oddUnitSquareClassLayer K hnPos hnLt hnOdd]
  congr 2

/-- After `r` paired steps, the cardinality of the full unit square-class
group is the product of `r` residue factors and the remaining filtration. -/
theorem card_valuationUnitClass_eq_pow_mul_filtration
    (r : Nat) (hr : r ≤ ramificationIndex K) :
    Nat.card (ValuationUnitClass K) =
      Nat.card (normalizedResidueField K) ^ r *
        Nat.card (principalUnitValuationClassSubgroup K (2 * r)) := by
  induction r with
  | zero =>
      rw [pow_zero, one_mul,
        principalUnitValuationClassSubgroup_zero_eq_top]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv.symm
  | succ r ih =>
      have hrLt : r < ramificationIndex K := by omega
      rw [ih hrLt.le, card_principalUnitValuationClassSubgroup_even_step K r hrLt,
        pow_succ]
      ring

/-- O'Meara 63:9: the dyadic unit square-class quotient has cardinality
`2 * q^e`, where `q` is the residue-field cardinality. -/
theorem card_valuationUnitClass :
    Nat.card (ValuationUnitClass K) =
      2 * Nat.card (normalizedResidueField K) ^ ramificationIndex K := by
  rw [card_valuationUnitClass_eq_pow_mul_filtration K
      (ramificationIndex K) le_rfl,
    card_principalUnitValuationClassSubgroup_two_mul_e]
  ring

end Bong.Dyadic
