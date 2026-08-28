/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma75PrefixClass

/-!
# Beli (2019), Lemma 7.17: the three endpoint cases

This file formalizes the arithmetic part of Lemma 7.17.  The paper chooses
an even integer `s` maximal with `R_s = R - 2e`.  The first `s` entries are
therefore an alternating endpoint tower, and the next entry is either absent,
strictly above `R`, or equal to `R`.  In the first two situations the signed
determinant of the tower distinguishes types I and II; equality at the next
entry is type III.

The maximal hyperbolic-splitting statement and the construction of the
replacement lattice are kept in subsequent files.  In particular, none of
those geometric conclusions is assumed here.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The paper's maximal even endpoint in zero-based Lean indexing.  The
equation `terminal` is `R_s = R - 2e`; `maximal` says that the next entry of
the same parity, when present, no longer has that order. -/
structure Lemma717StoppingData
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat) : Prop where
  even : Even s
  two_le : 2 ≤ s
  le_rank : s ≤ n + 3
  terminal : b.order ⟨s - 1, by omega⟩ =
    R - 2 * (ramificationIndex K : Int)
  maximal (hs : s + 2 ≤ n + 3) :
    b.order ⟨s + 1, by omega⟩ ≠
      R - 2 * (ramificationIndex K : Int)

/-- The endpoint alternative shared by types I and II: either the selected
prefix is the whole lattice or the following order is strictly above `R`. -/
def Lemma717EndpointAbove
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat) : Prop :=
  s = n + 3 ∨ ∃ hs : s < n + 3, R < b.order ⟨s, hs⟩

/-- Type I of Lemma 7.17: the endpoint is above and the signed determinant
of the first `s` entries is a square. -/
noncomputable def Lemma717IsTypeI
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat) : Prop :=
  Lemma717EndpointAbove b R s ∧
    IsSquare (b.toBONG.signedEvenPrefixProduct (s / 2))

/-- Type II of Lemma 7.17: the endpoint is above and the signed determinant
of the first `s` entries is in the unramified discriminant class. -/
noncomputable def Lemma717IsTypeII
    [laws : DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat) : Prop :=
  Lemma717EndpointAbove b R s ∧
    IsSquare (b.toBONG.signedEvenPrefixProduct (s / 2) *
      laws.discriminantUnit)

/-- Type III of Lemma 7.17: the next entry exists and has order exactly
`R`. -/
def Lemma717IsTypeIII
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat) : Prop :=
  ∃ hs : s < n + 3, b.order ⟨s, hs⟩ = R

/-- The first order is no larger than the order immediately after the even
prefix.  This is the two-step monotonicity used in the paper. -/
theorem lemma717_nextOrder_ge
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData b R s)
    (hfirst : b.order ⟨0, by omega⟩ = R)
    (hs : s < n + 3) :
    R ≤ b.order ⟨s, hs⟩ := by
  have hmono := b.orderSequence.entryOrZero_le_of_evenGap
    0 s (Nat.zero_le s) hs D.even
  rw [b.orderSequence_entryOrZero_eq_order ⟨0, by omega⟩,
    b.orderSequence_entryOrZero_eq_order ⟨s, hs⟩, hfirst] at hmono
  exact hmono

/-- Lemma 7.5 applied to the first `s` entries gives precisely the signed
determinant alternatives used to define types I and II. -/
theorem lemma717_signedPrefixProduct_cases
    [Beli2006AlphaLaws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData b R s)
    (hfirst : b.order ⟨0, by omega⟩ = R) :
    IsSquare (b.toBONG.signedEvenPrefixProduct (s / 2)) ∨
      IsSquare (b.toBONG.signedEvenPrefixProduct (s / 2) *
        laws.discriminantUnit) := by
  let j : Fin (n + 2) := ⟨s - 2, by
    have hsBound := D.le_rank
    omega⟩
  have hjeven : Even j.val := by
    rcases D.even with ⟨d, hd⟩
    refine ⟨d - 1, ?_⟩
    simp only [j]
    have hsTwo := D.two_le
    omega
  have hterminal : b.order j.succ =
      R - 2 * (ramificationIndex K : Int) := by
    have hindex : j.succ = (⟨s - 1, by
        have hsBound := D.le_rank
        omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      simp only [j, Fin.val_succ]
      have hsTwo := D.two_le
      omega
    rw [hindex]
    exact D.terminal
  rcases b.beli2019Lemma75_signedPrefixProduct_endpoint_cases
      j R hjeven hfirst hterminal with ⟨pairs, hpairs, hcases⟩
  have hpairs' : pairs = s / 2 := by
    rcases D.even with ⟨d, hd⟩
    simp only [j] at hpairs
    have hsTwo := D.two_le
    have hpairsD : pairs = d := by omega
    have hsMul : s = 2 * d := by omega
    calc
      pairs = d := hpairsD
      _ = 2 * d / 2 := (Nat.mul_div_cancel_left d (by decide)).symm
      _ = s / 2 := by rw [hsMul]
  rwa [hpairs'] at hcases

/-- The three cases following Lemma 7.17 are exhaustive. -/
theorem beli2019Lemma717_type_trichotomy
    [Beli2006AlphaLaws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData b R s)
    (hfirst : b.order ⟨0, by omega⟩ = R) :
    Lemma717IsTypeI b R s ∨ Lemma717IsTypeII b R s ∨
      Lemma717IsTypeIII b R s := by
  have hclasses := b.lemma717_signedPrefixProduct_cases R s D hfirst
  by_cases hend : s = n + 3
  · rcases hclasses with hsquare | hdelta
    · exact Or.inl ⟨Or.inl hend, hsquare⟩
    · exact Or.inr (Or.inl ⟨Or.inl hend, hdelta⟩)
  · have hs : s < n + 3 := lt_of_le_of_ne D.le_rank hend
    have hlower := b.lemma717_nextOrder_ge R s D hfirst hs
    by_cases heq : b.order ⟨s, hs⟩ = R
    · exact Or.inr (Or.inr ⟨hs, heq⟩)
    · have habove : R < b.order ⟨s, hs⟩ := lt_of_le_of_ne hlower
        (Ne.symm heq)
      rcases hclasses with hsquare | hdelta
      · exact Or.inl ⟨Or.inr ⟨hs, habove⟩, hsquare⟩
      · exact Or.inr (Or.inl ⟨Or.inr ⟨hs, habove⟩, hdelta⟩)

/-- The discriminant unit is not a square. -/
theorem discriminantUnit_not_isSquare
    [QuadraticDefectLaws K] [laws : DyadicDiscriminantClassLaws K] :
    ¬IsSquare laws.discriminantUnit := by
  intro hsquare
  have htop := quadraticDefect_eq_top_of_isSquare (K := K) hsquare
  rw [laws.discriminant_defect] at htop
  have hfinite : ((2 * ramificationIndex K : Nat) : ℕ∞) ≠ ⊤ :=
    ENat.coe_ne_top _
  exact hfinite htop

/-- Types I and II cannot overlap. -/
theorem lemma717_typeI_typeII_disjoint
    [QuadraticDefectLaws K] [laws : DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat) :
    ¬(Lemma717IsTypeI b R s ∧ Lemma717IsTypeII b R s) := by
  rintro ⟨⟨_, hsquare⟩, ⟨_, hdelta⟩⟩
  have hquotient := hdelta.div hsquare
  have hcancel :
      (b.toBONG.signedEvenPrefixProduct (s / 2) *
          laws.discriminantUnit) /
        b.toBONG.signedEvenPrefixProduct (s / 2) =
          laws.discriminantUnit := by
    exact mul_div_cancel_left _ _
  rw [hcancel] at hquotient
  exact discriminantUnit_not_isSquare (K := K) hquotient

/-- Type III is disjoint from each endpoint-above case. -/
theorem lemma717_endpointAbove_typeIII_disjoint
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat) :
    ¬(Lemma717EndpointAbove b R s ∧ Lemma717IsTypeIII b R s) := by
  rintro ⟨habove, hs, horder⟩
  rcases habove with hend | ⟨hs', hstrict⟩
  · omega
  · have hindex : (⟨s, hs⟩ : Fin (n + 3)) = ⟨s, hs'⟩ := by
      apply Fin.ext
      rfl
    rw [hindex, horder] at hstrict
    omega

end BONG.GoodBONG

end Bong
