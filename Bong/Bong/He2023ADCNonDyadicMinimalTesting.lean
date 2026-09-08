/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.He2023ADCNonDyadicTheorem110

/-!
# He (2025), non-dyadic Lemma 4.7(ii)

The published minimal-testing assertion is separated into its finite family,
the generic maximal-overlattice argument proving sufficiency, and explicit
deletion witnesses proving literal minimality.
-/

namespace Bong

universe u v

/-- The defined rows of the non-dyadic maximal-lattice table in rank `n`. -/
abbrev HeADC2025NonDyadicTestingIndex (n : Nat) :=
  {p : HeADC2025NonDyadicColumn × HeADC2025NonDyadicSquareClass //
    HeADC2025NonDyadicRowIsDefined n p.1 p.2}

/-- The published rank-one testing family has four rows. -/
theorem card_heADC2025NonDyadicTestingIndex_one :
    Fintype.card (HeADC2025NonDyadicTestingIndex 1) = 4 := by
  decide

/-- The published rank-two testing family has seven rows. -/
theorem card_heADC2025NonDyadicTestingIndex_two :
    Fintype.card (HeADC2025NonDyadicTestingIndex 2) = 7 := by
  decide

/-- From rank three onward every column/square-class pair is defined. -/
def heADC2025NonDyadicTestingIndexEquiv (n : Nat) (hN : 3 ≤ n) :
    HeADC2025NonDyadicTestingIndex n ≃
      HeADC2025NonDyadicColumn × HeADC2025NonDyadicSquareClass where
  toFun := Subtype.val
  invFun p := ⟨p, by
    unfold HeADC2025NonDyadicRowIsDefined
    omega⟩
  left_inv i := Subtype.ext (by rfl)
  right_inv _ := rfl

/-- Every published testing family in rank at least three has eight rows. -/
theorem card_heADC2025NonDyadicTestingIndex_of_three_le
    (n : Nat) (hN : 3 ≤ n) :
    Fintype.card (HeADC2025NonDyadicTestingIndex n) = 8 := by
  rw [Fintype.card_congr (heADC2025NonDyadicTestingIndexEquiv n hN)]
  decide

namespace HeADC2025NonDyadicSystem

variable (S : HeADC2025NonDyadicSystem.{u})

/-- Rank-`n` universality in the abstract non-dyadic lattice system. -/
def IsNUniversal (M : S.Lattice) (n : Nat) : Prop :=
  S.integral M ∧
    ∀ N : S.Lattice, S.rank N = n → S.integral N → S.represents M N

/-- A family tests rank-`n` universality. -/
def IsUniversalityTestingFamily {I : Type v}
    (family : I → S.Lattice) (n : Nat) : Prop :=
  ∀ M : S.Lattice, S.integral M →
    (∀ i, S.represents M (family i)) → S.IsNUniversal M n

/-- Literal deletion-minimality for a finite displayed family. -/
def IsLiteralMinimalUniversalityTestingFamily {I : Type v}
    (family : I → S.Lattice) (n : Nat) : Prop :=
  S.IsUniversalityTestingFamily family n ∧
    ∀ i, ∃ M : S.Lattice,
      S.integral M ∧ ¬ S.represents M (family i) ∧
        ∀ j, j ≠ i → S.represents M (family j)

/-- The literal family of all and only defined rows in rank `n`. -/
def nonDyadicTestingFamily (n : Nat)
    (i : HeADC2025NonDyadicTestingIndex n) : S.Lattice :=
  S.target i.1.1 n i.1.2

/-- Mathematical inputs behind the maximal-overlattice and deletion-witness
steps of Lemma 4.7(ii).  The final testing-family assertion is not a field. -/
structure MinimalTestingLaws
    (isometric : S.Lattice → S.Lattice → Prop) (n : Nat) : Prop where
  represents_trans {L M N : S.Lattice} :
    S.represents L M → S.represents M N → S.represents L N
  represents_of_isometric_target {L M N : S.Lattice} :
    isometric M N → S.represents L N → S.represents L M
  integral_has_maximal_overlattice (N : S.Lattice) :
    S.rank N = n → S.integral N →
      ∃ M : S.Lattice,
        S.rank M = n ∧ S.isMaximal M ∧ S.represents M N
  deletion_witness (i : HeADC2025NonDyadicTestingIndex n) :
    ∃ M : S.Lattice,
      S.integral M ∧ ¬ S.represents M (S.nonDyadicTestingFamily n i) ∧
        ∀ j, j ≠ i → S.represents M (S.nonDyadicTestingFamily n j)

namespace MinimalTestingLaws

variable {S : HeADC2025NonDyadicSystem.{u}}
  {I : S.Lemma45InvariantData}
  {P : S.Proposition42InvariantData I}
  {isometric : S.Lattice → S.Lattice → Prop}

/-- The defined non-dyadic maximal rows test rank-`n` universality. -/
theorem nonDyadicTestingFamily_isUniversalityTestingFamily
    (H : S.CatalogueLaws I P isometric)
    (T : S.MinimalTestingLaws isometric n) (hN : 1 ≤ n) :
    S.IsUniversalityTestingFamily (S.nonDyadicTestingFamily n) n := by
  intro L hIntegral hRows
  refine ⟨hIntegral, ?_⟩
  intro N hRankN hIntegralN
  obtain ⟨M, hRankM, hMaximalM, hMN⟩ :=
    T.integral_has_maximal_overlattice N hRankN hIntegralN
  obtain ⟨nu, c, hDefined, hIso⟩ :=
    H.maximal_complete M n hN hRankM hMaximalM
  let i : HeADC2025NonDyadicTestingIndex n :=
    ⟨(nu, c), hDefined⟩
  have hLM : S.represents L M :=
    T.represents_of_isometric_target hIso (hRows i)
  exact T.represents_trans hLM hMN

/-- He (2025), Lemma 4.7(ii), as a literal deletion-minimality theorem with
the cited maximal-overlattice and deletion-witness inputs exposed. -/
theorem heADC2025Lemma47ii
    (H : S.CatalogueLaws I P isometric)
    (T : S.MinimalTestingLaws isometric n) (hN : 1 ≤ n) :
    S.IsLiteralMinimalUniversalityTestingFamily
      (S.nonDyadicTestingFamily n) n := by
  refine ⟨T.nonDyadicTestingFamily_isUniversalityTestingFamily H hN, ?_⟩
  exact T.deletion_witness

end MinimalTestingLaws

end HeADC2025NonDyadicSystem

end Bong
