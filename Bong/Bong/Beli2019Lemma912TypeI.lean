/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma912Profile
import Bong.Bong.Beli2019Lemma910Alpha
import Bong.Bong.Beli2019Lemma67Classification

/-!
# Beli (2019), Lemma 9.12: the Lemma 9.10 order profile

The type-I construction in the claim inside Lemma 9.12 replaces the first
ternary block by the output of Lemma 9.10.  This file records the resulting
orders and proves condition 2.1(i) relative to the third lattice.  The proof
uses only the coefficient identities supplied by Lemma 9.10 and the original
order condition; it introduces no additional local-law interface.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {M : Lattice K V} {P : Lattice K W} {Q : Lattice K U}
  {N : Nat}

namespace Beli2019Lemma910Data

/-- The orders in the replaced ternary prefix are exactly the orders of the
Lemma 9.9 realization. -/
@[simp]
theorem order_castAdd
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D) (i : Fin 3) :
    E.bong.order (Fin.castAdd N i) = D.bong.order i := by
  unfold GoodBONG.order
  rw [E.bong.toBONG.order_eq_ordUnit]
  change ordUnit K (E.bong.valueUnit (Fin.castAdd N i)) =
    D.bong.order i
  rw [E.values, ordUnit_beli2019Lemma910Values_left]

/-- Every order after the replaced ternary prefix is unchanged. -/
@[simp]
theorem order_natAdd
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D) (j : Fin N) :
    E.bong.order (Fin.natAdd 3 j) = a.order (Fin.natAdd 3 j) := by
  unfold GoodBONG.order
  rw [E.bong.toBONG.order_eq_ordUnit]
  change ordUnit K (E.bong.valueUnit (Fin.natAdd 3 j)) =
    a.order (Fin.natAdd 3 j)
  rw [E.values, ordUnit_beli2019Lemma910Values_right]

/-- From the third coordinate onward, the output of Lemma 9.10 has the same
order as the original BONG. -/
theorem order_eq_source_of_two_le
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (i : Fin (3 + N)) (hi : 2 ≤ i.val) :
    E.bong.order i = a.order i := by
  revert hi
  refine Fin.addCases (m := 3) (n := N) (fun j hi ↦ ?_)
      (fun j _ ↦ ?_) i
  · simp only [Fin.castAdd, Fin.castLE] at hi
    have hj : j = (2 : Fin 3) := by
      apply Fin.ext
      omega
    subst j
    rw [E.order_castAdd a D, D.order_two, horders (2 : Fin 3)]
    rfl
  · exact E.order_natAdd a D j

/-- Casted form of `order_eq_source_of_two_le`, with the length normalized
to `N + 3 = (N + 2) + 1` for use by the representation-condition API. -/
theorem order_castLength_eq_source_of_two_le
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3) (i : Fin (N + 3)) (hi : 2 ≤ i.val) :
    (E.bong.castLength hlength).order i =
      (a.castLength hlength).order i := by
  rw [GoodBONG.order_castLength, GoodBONG.order_castLength]
  exact E.order_eq_source_of_two_le a D horders
    ⟨i.val, by omega⟩ hi

/-- The source satisfies condition 2.1(i) relative to the Lemma 9.10
output: every coordinate is unchanged except the second, which increases by
two. -/
theorem representationOrderCondition
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3) :
    (a.castLength hlength).RepresentationOrderCondition
      (E.bong.castLength hlength) le_rfl := by
  intro i
  left
  by_cases hiZero : i.val = 0
  · have hi : i = (0 : Fin (N + 3)) := by
      apply Fin.ext
      simpa using hiZero
    subst i
    rw [GoodBONG.order_castLength, GoodBONG.order_castLength]
    have hzero : (⟨(0 : Fin (N + 3)).val, by omega⟩ : Fin (3 + N)) =
        Fin.castAdd N (0 : Fin 3) := by
      apply Fin.ext
      rfl
    rw [hzero, E.order_castAdd a D, D.order_zero,
      horders (0 : Fin 3)]
    simp
  by_cases hiOne : i.val = 1
  · have hi : i = (1 : Fin (N + 3)) := by
      apply Fin.ext
      simpa using hiOne
    subst i
    rw [GoodBONG.order_castLength, GoodBONG.order_castLength]
    have hone : (⟨(1 : Fin (N + 3)).val, by omega⟩ : Fin (3 + N)) =
        Fin.castAdd N (1 : Fin 3) := by
      apply Fin.ext
      rfl
    rw [hone, E.order_castAdd a D, D.order_one,
      horders (1 : Fin 3)]
    simp
  have hiTwo : 2 ≤ i.val := by omega
  exact le_of_eq
    (E.order_castLength_eq_source_of_two_le
      a D horders hlength i hiTwo).symm

/-- The total order sum of the Lemma 9.10 output is larger by two. -/
theorem totalOrderGap
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (hlength : 3 + N = N + 3) :
    (a.castLength hlength).orderSequence.prefixSum (N + 3) + 2 =
      (E.bong.castLength hlength).orderSequence.prefixSum (N + 3) := by
  change (a.castLength hlength).orderPrefixSum (N + 3) + 2 =
    (E.bong.castLength hlength).orderPrefixSum (N + 3)
  rw [(a.castLength hlength).orderPrefixSum_full_eq_volumeOrder,
    (E.bong.castLength hlength).orderPrefixSum_full_eq_volumeOrder]
  exact E.inclusion.volumeOrder_eq.symm

/-- The order pair produced by Lemma 9.10 is the type-I branch of Lemma
6.7.  Its first and last unequal positions are both the second coordinate;
in the paper's one-based notation this is exactly
`s = t = t' = u = 2`. -/
theorem exists_typeI_exact
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3) :
    ∃ T : Lemma67TypeI (a.castLength hlength)
        (E.bong.castLength hlength),
      T.profile.first = 1 ∧ T.profile.last = 1 := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  have horder : source.RepresentationOrderCondition target le_rfl := by
    exact E.representationOrderCondition a D horders hlength
  have htotal : source.orderSequence.prefixSum (N + 3) + 2 =
      target.orderSequence.prefixSum (N + 3) := by
    exact E.totalOrderGap a D hlength
  have hle := (source.representationOrderCondition_iff target le_rfl).mp
    horder
  have hentry : target.orderSequence.entryOrZero 1 =
      source.orderSequence.entryOrZero 1 + 2 := by
    rw [BeliOrderSequence.entryOrZero_of_lt target.orderSequence (by omega),
      BeliOrderSequence.entryOrZero_of_lt source.orderSequence (by omega)]
    change target.order (1 : Fin (N + 3)) =
      source.order (1 : Fin (N + 3)) + 2
    dsimp only [source, target]
    rw [GoodBONG.order_castLength, GoodBONG.order_castLength]
    have hone : (⟨(1 : Fin (N + 3)).val, by omega⟩ : Fin (3 + N)) =
        Fin.castAdd N (1 : Fin 3) := by
      apply Fin.ext
      rfl
    rw [hone, E.order_castAdd a D, D.order_one,
      horders (1 : Fin 3)]
    simp
  rcases hle.gapTwoAnchorConsequences htotal 1 (by omega) hentry with
    ⟨profile⟩
  let T : Lemma67TypeI source target := {
    anchor := 1
    anchor_bound := by omega
    target_le_source_add_two :=
      hle.entryOrZero_le_add_two_of_totalGap htotal
    anchor_gap := hentry
    profile := profile }
  have hzeroEq :
      source.orderSequence.entryOrZero 0 =
        target.orderSequence.entryOrZero 0 := by
    rw [source.orderSequence.entryOrZero_of_lt (by omega),
      target.orderSequence.entryOrZero_of_lt (by omega)]
    change source.order (0 : Fin (N + 3)) =
      target.order (0 : Fin (N + 3))
    dsimp only [source, target]
    rw [GoodBONG.order_castLength, GoodBONG.order_castLength]
    have hzero :
        (⟨(0 : Fin (N + 3)).val, by omega⟩ : Fin (3 + N)) =
          Fin.castAdd N (0 : Fin 3) := by
      apply Fin.ext
      rfl
    rw [hzero, E.order_castAdd a D, D.order_zero,
      horders (0 : Fin 3)]
    simp
  have hfirst : T.profile.first = 1 := by
    have hle := T.profile.first_le_anchor
    have hneZero : T.profile.first ≠ 0 := by
      intro hzero
      apply T.profile.firstDifference.ne
      simpa only [hzero] using hzeroEq
    change T.profile.first ≤ 1 at hle
    omega
  have hlast : T.profile.last = 1 := by
    have hge := T.profile.anchor_le_last
    change 1 ≤ T.profile.last at hge
    by_contra hne
    have htwo : 2 ≤ T.profile.last := by
      omega
    have heqOrder := E.order_castLength_eq_source_of_two_le
      a D horders hlength
      ⟨T.profile.last, T.profile.lastDifference.bound⟩ htwo
    apply T.profile.lastDifference.ne
    rw [BeliOrderSequence.entryOrZero_of_lt
        (a.castLength hlength).orderSequence
        T.profile.lastDifference.bound,
      BeliOrderSequence.entryOrZero_of_lt
        (E.bong.castLength hlength).orderSequence
        T.profile.lastDifference.bound]
    exact heqOrder.symm
  exact ⟨T, hfirst, hlast⟩

end Beli2019Lemma910Data

/-- Condition 2.1(i) in the claim of Lemma 9.12.  At the first coordinate
the two orders agree, at the second coordinate the hypothesis gives
`R₂ + 2 ≤ T₂`, and from the third coordinate onward the new BONG agrees with
the old one, so the original direct-or-pair alternative transports verbatim.
-/
theorem beli2019Lemma912_typeI_orderCondition
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hfirst : (c.castLength hlength).order (0 : Fin (N + 3)) = R₁)
    (hsecond : R₂ + 2 ≤
      (c.castLength hlength).order (1 : Fin (N + 3)))
    (hac : (a.castLength hlength).RepresentationOrderCondition
      (c.castLength hlength) le_rfl) :
    (E.bong.castLength hlength).RepresentationOrderCondition
      (c.castLength hlength) le_rfl := by
  intro i
  by_cases hiZero : i.val = 0
  · left
    have hi : i = (0 : Fin (N + 3)) := by
      apply Fin.ext
      simpa using hiZero
    subst i
    rw [GoodBONG.order_castLength]
    have hzero : (⟨(0 : Fin (N + 3)).val, by omega⟩ : Fin (3 + N)) =
        Fin.castAdd N (0 : Fin 3) := by
      apply Fin.ext
      rfl
    rw [hzero, E.order_castAdd a D, D.order_zero, hfirst]
  by_cases hiOne : i.val = 1
  · left
    have hi : i = (1 : Fin (N + 3)) := by
      apply Fin.ext
      simpa using hiOne
    subst i
    rw [GoodBONG.order_castLength]
    have hone : (⟨(1 : Fin (N + 3)).val, by omega⟩ : Fin (3 + N)) =
        Fin.castAdd N (1 : Fin 3) := by
      apply Fin.ext
      rfl
    rw [hone, E.order_castAdd a D, D.order_one]
    exact hsecond
  have hiTwo : 2 ≤ i.val := by omega
  rcases hac i with hcurrent | ⟨hiPos, hiNext, hpair⟩
  · left
    rw [E.order_castLength_eq_source_of_two_le a D horders hlength i hiTwo]
    simpa only using hcurrent
  · right
    refine ⟨hiPos, hiNext, ?_⟩
    have hcurrentEq : (E.bong.castLength hlength).order i =
        (a.castLength hlength).order i :=
      E.order_castLength_eq_source_of_two_le a D horders hlength i hiTwo
    let next : Fin (N + 3) := ⟨i.val + 1, hiNext⟩
    have hnextEq : (E.bong.castLength hlength).order next =
        (a.castLength hlength).order next :=
      E.order_castLength_eq_source_of_two_le a D horders hlength next (by
        dsimp only [next]
        omega)
    rw [hcurrentEq, hnextEq]
    simpa only [next] using hpair

end BONG.GoodBONG

end Bong
