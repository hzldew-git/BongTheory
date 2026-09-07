/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Mathlib.Tactic

/-!
# He (2025), Section 5: the non-dyadic local argument

The concrete lattice hierarchy in this repository is currently based on a
dyadic valuation context.  This file therefore separates the field-independent
logic of Section 5 from the non-dyadic Jordan and quadratic-space facts used by
the published proof.

`HeADC2025NonDyadicSystem` records the mathematical objects and relations.
`HeADC2025SectionFiveLaws` records precisely the earlier inputs used in Section
5: dimension monotonicity, the two maximal-space separation statements from
Section 4, the Jordan rank identities, and maximality of the two admissible
Jordan tails.  The four numbered results of Section 5 are then proved, rather
than included as fields of the law structure.

This is an explicit conditional boundary, not a concrete non-dyadic local-field
implementation.  In particular, constructing the law package for lattices over
a non-dyadic completion remains a separate task.
-/

namespace Bong

universe u

/-- The two unit square classes used throughout the non-dyadic section. -/
inductive HeADC2025NonDyadicUnitClass
  | one
  | delta
  deriving DecidableEq, Fintype

/-- The four square classes `1`, `Delta`, `pi`, and `Delta*pi`. -/
inductive HeADC2025NonDyadicSquareClass
  | one
  | delta
  | uniformizer
  | deltaUniformizer
  deriving DecidableEq, Fintype

/-- The two maximal-lattice columns `N_1` and `N_2`. -/
inductive HeADC2025NonDyadicColumn
  | one
  | two
  deriving DecidableEq, Fintype

namespace HeADC2025NonDyadicUnitClass

/-- Inclusion of unit square classes into all square classes. -/
def toSquareClass : HeADC2025NonDyadicUnitClass →
    HeADC2025NonDyadicSquareClass
  | .one => .one
  | .delta => .delta

/-- Multiplication by the square class of the uniformizer. -/
def timesUniformizer : HeADC2025NonDyadicUnitClass →
    HeADC2025NonDyadicSquareClass
  | .one => .uniformizer
  | .delta => .deltaUniformizer

end HeADC2025NonDyadicUnitClass

namespace HeADC2025NonDyadicSquareClass

/-- A unit square class different from the supplied square class. -/
def avoidingUnit : HeADC2025NonDyadicSquareClass →
    HeADC2025NonDyadicUnitClass
  | .one => .delta
  | .delta => .one
  | .uniformizer => .one
  | .deltaUniformizer => .one

/-- A nontrivial square class different from the supplied square class. -/
def avoidingNontrivial : HeADC2025NonDyadicSquareClass →
    HeADC2025NonDyadicSquareClass
  | .one => .uniformizer
  | .delta => .uniformizer
  | .uniformizer => .deltaUniformizer
  | .deltaUniformizer => .uniformizer

theorem avoidingUnit_ne (c : HeADC2025NonDyadicSquareClass) :
    (avoidingUnit c).toSquareClass ≠ c := by
  cases c <;> decide

theorem avoidingNontrivial_ne_one
    (c : HeADC2025NonDyadicSquareClass) :
    avoidingNontrivial c ≠ .one := by
  cases c <;> decide

theorem avoidingNontrivial_ne
    (c : HeADC2025NonDyadicSquareClass) :
    avoidingNontrivial c ≠ c := by
  cases c <;> decide

end HeADC2025NonDyadicSquareClass

/-- Abstract non-dyadic local lattices, their quadratic spaces, Jordan
components, and the two published maximal-lattice columns. -/
structure HeADC2025NonDyadicSystem where
  Lattice : Type u
  Space : Type u
  rank : Lattice → Nat
  integral : Lattice → Prop
  represents : Lattice → Lattice → Prop
  ambient : Lattice → Space
  jordanZero : Lattice → Space
  jordanZeroOne : Lattice → Space
  spaceRank : Space → Nat
  spaceRepresents : Space → Space → Prop
  spaceIsometric : Space → Space → Prop
  jordanOneRank : Lattice → Nat
  isJordanZeroOne : Lattice → Prop
  isMaximal : Lattice → Prop
  hasHyperbolicOneTail : Lattice → Prop
  squareClass : Lattice → HeADC2025NonDyadicSquareClass
  target : HeADC2025NonDyadicColumn → Nat →
    HeADC2025NonDyadicSquareClass → Lattice

namespace HeADC2025NonDyadicSystem

variable (S : HeADC2025NonDyadicSystem.{u})

/-- Definition 1.1(ii), expressed in the abstract non-dyadic system. -/
def IsNADC (M : S.Lattice) (n : Nat) : Prop :=
  S.integral M ∧
    ∀ N : S.Lattice, S.rank N = n → S.integral N →
      S.spaceRepresents (S.ambient M) (S.ambient N) → S.represents M N

/-- The non-dyadic Section 4 and Jordan-decomposition inputs used in the
published proofs of Theorem 5.1 and Lemmas 5.2--5.4.  None of the four
Section 5 conclusions is a field of this structure. -/
structure SectionFiveLaws : Prop where
  ambient_rank (M : S.Lattice) : S.spaceRank (S.ambient M) = S.rank M
  spaceRepresents_rank_le {X Y : S.Space} :
    S.spaceRepresents X Y → S.spaceRank Y ≤ S.spaceRank X
  spaceIsometric_symm {X Y : S.Space} :
    S.spaceIsometric X Y → S.spaceIsometric Y X
  spaceIsometric_trans {X Y Z : S.Space} :
    S.spaceIsometric X Y → S.spaceIsometric Y Z → S.spaceIsometric X Z
  spaceIsometric_of_represents_of_same_rank {X Y : S.Space} :
    S.spaceRepresents X Y → S.spaceRank X = S.spaceRank Y →
      S.spaceIsometric X Y
  represents_jordanZero {M N : S.Lattice} :
    S.represents M N →
      S.spaceRepresents (S.jordanZero M) (S.jordanZero N)
  represents_jordanZeroOne {M N : S.Lattice} :
    S.represents M N →
      S.spaceRepresents (S.jordanZeroOne M) (S.jordanZeroOne N)
  jordanZeroOne_rank_le_rank (M : S.Lattice) :
    S.spaceRank (S.jordanZeroOne M) ≤ S.rank M
  isJordanZeroOne_iff_rank (M : S.Lattice) :
    S.isJordanZeroOne M ↔ S.spaceRank (S.jordanZeroOne M) = S.rank M
  jordanZeroOne_rank_eq_add (M : S.Lattice) (hM : S.isJordanZeroOne M) :
    S.spaceRank (S.jordanZeroOne M) =
      S.spaceRank (S.jordanZero M) + S.jordanOneRank M
  target_rank (nu : HeADC2025NonDyadicColumn) (n : Nat)
      (c : HeADC2025NonDyadicSquareClass) :
    S.rank (S.target nu n c) = n
  target_integral (nu : HeADC2025NonDyadicColumn) (n : Nat)
      (c : HeADC2025NonDyadicSquareClass) :
    S.integral (S.target nu n c)
  target_jordanZeroOne_rank (nu : HeADC2025NonDyadicColumn) (n : Nat)
      (c : HeADC2025NonDyadicSquareClass) :
    S.spaceRank (S.jordanZeroOne (S.target nu n c)) = n
  target_jordanZero_rank_uniformizer (nu : HeADC2025NonDyadicColumn)
      (n : Nat) (unitClass : HeADC2025NonDyadicUnitClass) :
    S.spaceRank
        (S.jordanZero (S.target nu n unitClass.timesUniformizer)) = n - 1
  target_jordanZero_rank_firstUnit (n : Nat)
      (unitClass : HeADC2025NonDyadicUnitClass) :
    S.spaceRank
        (S.jordanZero (S.target .one n unitClass.toSquareClass)) = n
  uniformizer_targets_not_isometric (n : Nat)
      (nu mu : HeADC2025NonDyadicColumn) :
    ¬ S.spaceIsometric
        (S.jordanZeroOne
          (S.target nu n HeADC2025NonDyadicUnitClass.one.timesUniformizer))
        (S.jordanZeroOne
          (S.target mu n HeADC2025NonDyadicUnitClass.delta.timesUniformizer))
  first_unit_jordanZero_not_isometric (n : Nat) :
    ¬ S.spaceIsometric
        (S.jordanZero
          (S.target .one n HeADC2025NonDyadicUnitClass.one.toSquareClass))
        (S.jordanZero
          (S.target .one n HeADC2025NonDyadicUnitClass.delta.toSquareClass))
  columns_not_both_in_rank_le_succ (X : S.Space) (n : Nat)
      (c : HeADC2025NonDyadicSquareClass) :
    S.spaceRank X ≤ n + 1 →
      S.spaceRepresents X (S.jordanZeroOne (S.target .one n c)) →
      S.spaceRepresents X (S.jordanZeroOne (S.target .two n c)) → False
  corankOne_target_ambient (M : S.Lattice) (n : Nat)
      (hRank : S.rank M = n + 1)
      (unitClass : HeADC2025NonDyadicUnitClass) :
    ∃ nu : HeADC2025NonDyadicColumn,
      S.spaceRepresents (S.ambient M)
        (S.ambient (S.target nu n unitClass.timesUniformizer))
  corankTwo_firstUnit_ambient (M : S.Lattice) (n : Nat)
      (hRank : S.rank M = n + 2) :
    S.spaceRepresents (S.ambient M)
      (S.ambient (S.target .one n
        (S.squareClass M).avoidingUnit.toSquareClass))
  corankTwo_both_ambient (M : S.Lattice) (n : Nat)
      (hRank : S.rank M = n + 2) (nu : HeADC2025NonDyadicColumn) :
    S.spaceRepresents (S.ambient M)
      (S.ambient (S.target nu n (S.squareClass M).avoidingNontrivial))
  isMaximal_integral {M : S.Lattice} : S.isMaximal M → S.integral M
  isMaximal_represents {M N : S.Lattice} :
    S.isMaximal M → S.integral N →
      S.spaceRepresents (S.ambient M) (S.ambient N) → S.represents M N
  maximal_of_jordanZeroOne_of_oneRank_le_one (M : S.Lattice) :
    S.isJordanZeroOne M → S.jordanOneRank M ≤ 1 → S.isMaximal M
  maximal_or_hyperbolicTail_of_oneRank_eq_two (M : S.Lattice) :
    S.isJordanZeroOne M → S.jordanOneRank M = 2 →
      S.isMaximal M ∨ S.hasHyperbolicOneTail M
  hyperbolicTail_ambient_firstUnit (M : S.Lattice) (n : Nat)
      (hRank : S.rank M = n + 1 ∨ S.rank M = n + 2)
      (hTail : S.hasHyperbolicOneTail M)
      (unitClass : HeADC2025NonDyadicUnitClass) :
    S.spaceRepresents (S.ambient M)
      (S.ambient (S.target .one n unitClass.toSquareClass))

namespace SectionFiveLaws

variable {S : HeADC2025NonDyadicSystem.{u}}

/-- A maximal lattice is `n`-ADC.  This is the Section 5 use of Lemma 4.14. -/
theorem isMaximal_isNADC (H : S.SectionFiveLaws) {M : S.Lattice}
    (hM : S.isMaximal M) (n : Nat) : S.IsNADC M n := by
  refine ⟨H.isMaximal_integral hM, ?_⟩
  intro N _ hN hAmbient
  exact H.isMaximal_represents hM hN hAmbient

/-- An `n`-ADC lattice represents any one of the explicit maximal targets
whose ambient space is represented. -/
theorem isNADC_represents_target (H : S.SectionFiveLaws)
    {M : S.Lattice} {n : Nat} (hM : S.IsNADC M n)
    (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass)
    (hAmbient : S.spaceRepresents (S.ambient M)
      (S.ambient (S.target nu n c))) :
    S.represents M (S.target nu n c) :=
  hM.2 (S.target nu n c) (H.target_rank nu n c)
    (H.target_integral nu n c) hAmbient

private theorem targets_isometric_of_common_same_rank
    (H : S.SectionFiveLaws) {X Y Z : S.Space}
    (hXY : S.spaceRepresents X Y) (hXZ : S.spaceRepresents X Z)
    (hRankX : S.spaceRank X = S.spaceRank Y)
    (hRankYZ : S.spaceRank Y = S.spaceRank Z) :
    S.spaceIsometric Y Z := by
  have hIsoXY : S.spaceIsometric X Y :=
    H.spaceIsometric_of_represents_of_same_rank hXY hRankX
  have hRankXZ : S.spaceRank X = S.spaceRank Z := hRankX.trans hRankYZ
  have hIsoXZ : S.spaceIsometric X Z :=
    H.spaceIsometric_of_represents_of_same_rank hXZ hRankXZ
  exact H.spaceIsometric_trans (H.spaceIsometric_symm hIsoXY) hIsoXZ

/-- He (2025), Lemma 5.2. -/
theorem heADC2025Lemma52 (H : S.SectionFiveLaws) (M : S.Lattice) (n : Nat)
    (hJordan : S.isJordanZeroOne M) (hOne : S.jordanOneRank M ≤ 1) :
    S.isMaximal M ∧ S.IsNADC M n := by
  have hMaximal := H.maximal_of_jordanZeroOne_of_oneRank_le_one M hJordan hOne
  exact ⟨hMaximal, H.isMaximal_isNADC hMaximal n⟩

/-- He (2025), Lemma 5.3(i). -/
theorem heADC2025Lemma53i (H : S.SectionFiveLaws) (M : S.Lattice)
    (n : Nat)
    (hRepresented : ∀ unitClass : HeADC2025NonDyadicUnitClass,
      ∃ nu : HeADC2025NonDyadicColumn,
        S.represents M (S.target nu n unitClass.timesUniformizer)) :
    n - 1 ≤ S.spaceRank (S.jordanZero M) ∧
      n + 1 ≤ S.spaceRank (S.jordanZeroOne M) := by
  obtain ⟨nuOne, hOne⟩ := hRepresented .one
  obtain ⟨nuDelta, hDelta⟩ := hRepresented .delta
  have hJ0 := H.spaceRepresents_rank_le (H.represents_jordanZero hOne)
  have hJ01One := H.represents_jordanZeroOne hOne
  have hJ01Delta := H.represents_jordanZeroOne hDelta
  have hJ01Lower := H.spaceRepresents_rank_le hJ01One
  constructor
  · simpa [H.target_jordanZero_rank_uniformizer] using hJ0
  · by_contra hNot
    have hSourceRank : S.spaceRank (S.jordanZeroOne M) = n := by
      have hTargetRank := H.target_jordanZeroOne_rank nuOne n
        HeADC2025NonDyadicUnitClass.one.timesUniformizer
      omega
    have hTargetRanks :
        S.spaceRank
            (S.jordanZeroOne
              (S.target nuOne n
                HeADC2025NonDyadicUnitClass.one.timesUniformizer)) =
          S.spaceRank
            (S.jordanZeroOne
              (S.target nuDelta n
                HeADC2025NonDyadicUnitClass.delta.timesUniformizer)) := by
      rw [H.target_jordanZeroOne_rank, H.target_jordanZeroOne_rank]
    apply H.uniformizer_targets_not_isometric n nuOne nuDelta
    exact targets_isometric_of_common_same_rank H hJ01One hJ01Delta
      (hSourceRank.trans
        (H.target_jordanZeroOne_rank nuOne n
          HeADC2025NonDyadicUnitClass.one.timesUniformizer).symm)
      hTargetRanks

/-- He (2025), Lemma 5.3(ii). -/
theorem heADC2025Lemma53ii (H : S.SectionFiveLaws) (M : S.Lattice)
    (n : Nat) (unitClass : HeADC2025NonDyadicUnitClass)
    (hRepresented :
      S.represents M (S.target .one n unitClass.toSquareClass)) :
    n ≤ S.spaceRank (S.jordanZero M) := by
  have hRank := H.spaceRepresents_rank_le
    (H.represents_jordanZero hRepresented)
  simpa [H.target_jordanZero_rank_firstUnit] using hRank

/-- He (2025), Lemma 5.3(iii). -/
theorem heADC2025Lemma53iii (H : S.SectionFiveLaws) (M : S.Lattice)
    (n : Nat)
    (hRepresented : ∀ unitClass : HeADC2025NonDyadicUnitClass,
      S.represents M (S.target .one n unitClass.toSquareClass)) :
    n + 1 ≤ S.spaceRank (S.jordanZero M) := by
  have hOne := H.represents_jordanZero (hRepresented .one)
  have hDelta := H.represents_jordanZero (hRepresented .delta)
  have hLower := H.spaceRepresents_rank_le hOne
  by_contra hNot
  have hSourceRank : S.spaceRank (S.jordanZero M) = n := by
    have hTargetRank := H.target_jordanZero_rank_firstUnit n
      HeADC2025NonDyadicUnitClass.one
    omega
  apply H.first_unit_jordanZero_not_isometric n
  exact targets_isometric_of_common_same_rank H hOne hDelta
    (hSourceRank.trans
      (H.target_jordanZero_rank_firstUnit n
        HeADC2025NonDyadicUnitClass.one).symm)
    (by rw [H.target_jordanZero_rank_firstUnit,
      H.target_jordanZero_rank_firstUnit])

/-- He (2025), Lemma 5.3(iv). -/
theorem heADC2025Lemma53iv (H : S.SectionFiveLaws) (M : S.Lattice)
    (n : Nat) (c : HeADC2025NonDyadicSquareClass)
    (hFirst : S.represents M (S.target .one n c))
    (hSecond : S.represents M (S.target .two n c)) :
    n + 2 ≤ S.spaceRank (S.jordanZeroOne M) := by
  by_contra hNot
  have hFirstSpace := H.represents_jordanZeroOne hFirst
  have hSecondSpace := H.represents_jordanZeroOne hSecond
  apply H.columns_not_both_in_rank_le_succ (S.jordanZeroOne M) n c
  · omega
  · exact hFirstSpace
  · exact hSecondSpace

/-- He (2025), Lemma 5.4.  All choices of square classes used in the
published proof are made by the finite constructors above. -/
theorem heADC2025Lemma54 (H : S.SectionFiveLaws) (M : S.Lattice)
    (n : Nat) (hN : 2 ≤ n)
    (hRank : S.rank M = n + 1 ∨ S.rank M = n + 2)
    (hADC : S.IsNADC M n) :
    S.isJordanZeroOne M ∧ S.jordanOneRank M ≤ 2 := by
  rcases hRank with hCorankOne | hCorankTwo
  · have hTargets : ∀ unitClass : HeADC2025NonDyadicUnitClass,
        ∃ nu : HeADC2025NonDyadicColumn,
          S.represents M (S.target nu n unitClass.timesUniformizer) := by
      intro unitClass
      obtain ⟨nu, hAmbient⟩ :=
        H.corankOne_target_ambient M n hCorankOne unitClass
      exact ⟨nu, H.isNADC_represents_target hADC nu
        unitClass.timesUniformizer hAmbient⟩
    have hBounds := H.heADC2025Lemma53i M n hTargets
    have hJ01Le := H.jordanZeroOne_rank_le_rank M
    have hJ01Eq : S.spaceRank (S.jordanZeroOne M) = S.rank M := by
      omega
    have hJordan := (H.isJordanZeroOne_iff_rank M).2 hJ01Eq
    have hAdd := H.jordanZeroOne_rank_eq_add M hJordan
    constructor
    · exact hJordan
    · omega
  · let unitClass := (S.squareClass M).avoidingUnit
    let c := (S.squareClass M).avoidingNontrivial
    have hFirstAmbient := H.corankTwo_firstUnit_ambient M n hCorankTwo
    have hFirst : S.represents M
        (S.target .one n unitClass.toSquareClass) := by
      exact H.isNADC_represents_target hADC .one unitClass.toSquareClass
        hFirstAmbient
    have hColumnOne : S.represents M (S.target .one n c) := by
      exact H.isNADC_represents_target hADC .one c
        (H.corankTwo_both_ambient M n hCorankTwo .one)
    have hColumnTwo : S.represents M (S.target .two n c) := by
      exact H.isNADC_represents_target hADC .two c
        (H.corankTwo_both_ambient M n hCorankTwo .two)
    have hJ0Lower := H.heADC2025Lemma53ii M n unitClass hFirst
    have hJ01Lower := H.heADC2025Lemma53iv M n c hColumnOne hColumnTwo
    have hJ01Le := H.jordanZeroOne_rank_le_rank M
    have hJ01Eq : S.spaceRank (S.jordanZeroOne M) = S.rank M := by
      omega
    have hJordan := (H.isJordanZeroOne_iff_rank M).2 hJ01Eq
    have hAdd := H.jordanZeroOne_rank_eq_add M hJordan
    constructor
    · exact hJordan
    · omega

/-- He (2025), Theorem 5.1.  The theorem is proved from the explicitly
listed non-dyadic Jordan and Section 4 inputs, for both ranks `n+1` and
`n+2`. -/
theorem heADC2025Theorem51 (H : S.SectionFiveLaws) (M : S.Lattice)
    (n : Nat) (hN : 2 ≤ n)
    (hRank : S.rank M = n + 1 ∨ S.rank M = n + 2) :
    S.IsNADC M n ↔ S.isMaximal M := by
  constructor
  · intro hADC
    obtain ⟨hJordan, hOneLe⟩ := H.heADC2025Lemma54 M n hN hRank hADC
    by_cases hOneSmall : S.jordanOneRank M ≤ 1
    · exact H.maximal_of_jordanZeroOne_of_oneRank_le_one M hJordan hOneSmall
    · have hOneEq : S.jordanOneRank M = 2 := by omega
      rcases H.maximal_or_hyperbolicTail_of_oneRank_eq_two M hJordan hOneEq with
        hMaximal | hTail
      · exact hMaximal
      · exfalso
        have hRepresented : ∀ unitClass : HeADC2025NonDyadicUnitClass,
            S.represents M (S.target .one n unitClass.toSquareClass) := by
          intro unitClass
          exact H.isNADC_represents_target hADC .one unitClass.toSquareClass
            (H.hyperbolicTail_ambient_firstUnit M n hRank hTail unitClass)
        have hJ0Lower := H.heADC2025Lemma53iii M n hRepresented
        have hAdd := H.jordanZeroOne_rank_eq_add M hJordan
        have hJ01Eq := (H.isJordanZeroOne_iff_rank M).1 hJordan
        rcases hRank with hCorankOne | hCorankTwo <;> omega
  · intro hMaximal
    exact H.isMaximal_isNADC hMaximal n

end SectionFiveLaws

end HeADC2025NonDyadicSystem

end Bong
