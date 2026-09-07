/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.GlobalNADC

/-!
# He (2025), Section 8: global local--global logic

This file proves the logical content of Lemma 8.1, Theorem 8.2, Corollary
8.3, Theorem 1.5(ii), Theorem 1.7, Lemma 8.4, and Corollary 8.5 in the
repository's abstract global/local lattice system.

The number-field arithmetic invoked by the published proofs is kept in the
proof-data structure `HeADC2025SectionEightLaws`.  Its fields identify the
precise remaining implementation boundary: localization of maximality,
class-number-one regularity, the Meyer--Xu distinguishing lattice, transport
inside a genus, the local rank-`n+1` classification, and scaling stability.
None of those facts is introduced as a Lean axiom.  The numbered conclusions
are theorems from a supplied law package.
-/

namespace Bong

universe u v w

/-- Global genus, isometry, maximality, and scaling data not contained in the
minimal `GlobalLocalLatticeSystem` used for Theorem 1.3. -/
structure HeADC2025GlobalData
    (S : GlobalLocalLatticeSystem.{u, v, w}) where
  inGenus : S.GlobalLattice → S.GlobalLattice → Prop
  isIsometric : S.GlobalLattice → S.GlobalLattice → Prop
  isGlobalMaximal : S.GlobalLattice → Prop
  scaleTwo : S.GlobalLattice → S.GlobalLattice
  isStable : S.GlobalLattice → Prop
  isHalfScaleOf : S.GlobalLattice → S.GlobalLattice → Prop

namespace HeADC2025GlobalData

variable {S : GlobalLocalLatticeSystem.{u, v, w}}
  (G : HeADC2025GlobalData S)

/-- Class number one, with the base lattice in the second genus argument. -/
def HasClassNumberOne (M : S.GlobalLattice) : Prop :=
  ∀ M' : S.GlobalLattice, G.inGenus M' M → G.isIsometric M' M

/-- The exact conclusion of He (2025), Theorem 8.2. -/
def HasDistinguishingRankSublattice
    (M : S.GlobalLattice) (n : Nat) : Prop :=
  ∃ N : S.GlobalLattice,
    S.globalRank N = n ∧ S.globalIntegral N ∧
      S.globalRepresents M N ∧
        ∀ M' : S.GlobalLattice, G.inGenus M' M →
          S.globalRepresents M' N → G.isIsometric M' M

/-- The arithmetic inputs used by the Section 8 proofs.  Theorem 8.2 is
isolated as the `distinguishing_rank_sublattice` field because its proof uses
Meyer, Xu, spinor genera, and O'Meara 104:5, none of which presently has a
concrete project implementation. -/
structure SectionEightLaws : Prop where
  isIsometric_symm {M N : S.GlobalLattice} :
    G.isIsometric M N → G.isIsometric N M
  inGenus_symm {M N : S.GlobalLattice} :
    G.inGenus M N → G.inGenus N M
  rank_eq_of_inGenus {M N : S.GlobalLattice} :
    G.inGenus M N → S.globalRank M = S.globalRank N
  localEquivalent_of_inGenus {M N : S.GlobalLattice} :
    G.inGenus M N → ∀ p : S.Place,
      S.localEquivalent (S.localize p M) (S.localize p N)
  local_represents_of_equivalent_target
      (p : S.Place) (M M' N : S.LocalLattice p) :
    S.localEquivalent M M' → S.localRepresents M N →
      S.localRepresents M' N
  classNumberOne_implies_nRegular (M : S.GlobalLattice) (n : Nat) :
    G.HasClassNumberOne M → S.IsNRegular M n
  globalMaximal_iff_localMaximal (M : S.GlobalLattice) :
    G.isGlobalMaximal M ↔
      ∀ p : S.Place, S.localMaximal (S.localize p M)
  localMaximal_isNADCAt (M : S.GlobalLattice) (p : S.Place) (n : Nat) :
    S.localMaximal (S.localize p M) → S.IsNADCAt M p n
  local_theorem15 (M : S.GlobalLattice) (p : S.Place) (n : Nat) :
    2 ≤ n → (S.globalRank M = n ∨ S.globalRank M = n + 1) →
      (S.IsNADCAt M p n ↔ S.localMaximal (S.localize p M))
  distinguishing_rank_sublattice (M : S.GlobalLattice) (n : Nat) :
    S.globalRank M = n + 1 → 3 ≤ S.globalRank M →
      G.HasDistinguishingRankSublattice M n
  nRegular_scaleTwo (M : S.GlobalLattice) :
    S.IsNRegular M 2 → S.IsNRegular (G.scaleTwo M) 2
  locallyTwoADC_scaleTwo_stable (M : S.GlobalLattice) :
    S.IsLocallyNADC M 2 → G.isStable (G.scaleTwo M)
  scaleTwo_halfScale (M : S.GlobalLattice) :
    G.isHalfScaleOf M (G.scaleTwo M)
  nRegular_of_halfScale {M L : S.GlobalLattice} :
    S.IsNRegular L 2 → G.isHalfScaleOf M L → S.IsNRegular M 2

namespace SectionEightLaws

variable {G : HeADC2025GlobalData S}

/-- He (2025), Lemma 8.1(i). -/
theorem heADC2025Lemma81i (H : G.SectionEightLaws)
    (T : S.Theorem13Laws) (M : S.GlobalLattice) (n : Nat)
    (hClass : G.HasClassNumberOne M)
    (hLocal : S.IsLocallyNADC M n) :
    S.IsGloballyNADC M n := by
  exact T.locallyNADC_and_nRegular_implies_globallyNADC M n hLocal
    (H.classNumberOne_implies_nRegular M n hClass)

/-- He (2025), Lemma 8.1(ii). -/
theorem heADC2025Lemma81ii (H : G.SectionEightLaws)
    (T : S.Theorem13Laws) (M : S.GlobalLattice) (n : Nat)
    (hClass : G.HasClassNumberOne M)
    (hMaximal : G.isGlobalMaximal M) :
    S.IsGloballyNADC M n := by
  apply H.heADC2025Lemma81i T M n hClass
  intro p
  exact H.localMaximal_isNADCAt M p n
    ((H.globalMaximal_iff_localMaximal M).mp hMaximal p)

/-- He (2025), Theorem 8.2, relative to its explicit Meyer--Xu--O'Meara
arithmetic input. -/
theorem heADC2025Theorem82 (H : G.SectionEightLaws)
    (M : S.GlobalLattice) (n : Nat)
    (hRank : S.globalRank M = n + 1) (hThree : 3 ≤ S.globalRank M) :
    G.HasDistinguishingRankSublattice M n :=
  H.distinguishing_rank_sublattice M n hRank hThree

/-- He (2025), Corollary 8.3.  The proof transports the representation of
the distinguishing lattice through the genus and then invokes `n`-regularity. -/
theorem heADC2025Corollary83 (H : G.SectionEightLaws)
    (T : S.Theorem13Laws) (M : S.GlobalLattice) (n : Nat)
    (hRank : S.globalRank M = n + 1) (hThree : 3 ≤ S.globalRank M)
    (hRegular : S.IsNRegular M n) :
    G.HasClassNumberOne M := by
  intro M' hGenus
  have hRankM' : S.globalRank M' = n + 1 :=
    (H.rank_eq_of_inGenus hGenus).trans hRank
  have hThreeM' : 3 ≤ S.globalRank M' := by
    rw [H.rank_eq_of_inGenus hGenus]
    exact hThree
  obtain ⟨N, hNRank, hNIntegral, hM'N, hUnique⟩ :=
    H.heADC2025Theorem82 M' n hRankM' hThreeM'
  have hLocal : ∀ p : S.Place,
      S.localRepresents (S.localize p M) (S.localize p N) := by
    intro p
    have hLocalized := T.representation_localize p M' N hM'N
    exact H.local_represents_of_equivalent_target p
      (S.localize p M') (S.localize p M) (S.localize p N)
      (H.localEquivalent_of_inGenus hGenus p) hLocalized
  have hMN : S.globalRepresents M N :=
    hRegular N hNRank hNIntegral hLocal
  exact H.isIsometric_symm
    (hUnique M (H.inGenus_symm hGenus) hMN)

/-- He (2025), Theorem 1.5(i), in the abstract global/local system. -/
theorem heADC2025Theorem15i (H : G.SectionEightLaws)
    (M : S.GlobalLattice) (p : S.Place) (n : Nat)
    (hN : 2 ≤ n)
    (hRank : S.globalRank M = n ∨ S.globalRank M = n + 1) :
    S.IsNADCAt M p n ↔ S.localMaximal (S.localize p M) :=
  H.local_theorem15 M p n hN hRank

/-- He (2025), Theorem 1.5(ii). -/
theorem heADC2025Theorem15ii (H : G.SectionEightLaws)
    (M : S.GlobalLattice) (n : Nat) (hN : 2 ≤ n)
    (hRank : S.globalRank M = n ∨ S.globalRank M = n + 1) :
    S.IsLocallyNADC M n ↔ G.isGlobalMaximal M := by
  rw [H.globalMaximal_iff_localMaximal]
  constructor
  · intro hLocal p
    exact (H.heADC2025Theorem15i M p n hN hRank).mp (hLocal p)
  · intro hMaximal p
    exact (H.heADC2025Theorem15i M p n hN hRank).mpr (hMaximal p)

/-- He (2025), Theorem 1.7. -/
theorem heADC2025Theorem17 (H : G.SectionEightLaws)
    (T : S.Theorem13Laws) (M : S.GlobalLattice) (n : Nat)
    (hN : 2 ≤ n) (hRank : S.globalRank M = n + 1)
    (hThree : 3 ≤ S.globalRank M) :
    S.IsGloballyNADC M n ↔
      G.isGlobalMaximal M ∧ G.HasClassNumberOne M := by
  constructor
  · intro hADC
    have hParts := T.globallyNADC_implies_locallyNADC_and_nRegular M n hADC
    have hRankCases : S.globalRank M = n ∨ S.globalRank M = n + 1 :=
      Or.inr hRank
    exact ⟨(H.heADC2025Theorem15ii M n hN hRankCases).mp hParts.1,
      H.heADC2025Corollary83 T M n hRank hThree hParts.2⟩
  · rintro ⟨hMaximal, hClass⟩
    exact H.heADC2025Lemma81ii T M n hClass hMaximal

/-- He (2025), Lemma 8.4. -/
theorem heADC2025Lemma84 (H : G.SectionEightLaws)
    (T : S.Theorem13Laws) (M : S.GlobalLattice)
    (hADC : S.IsGloballyNADC M 2) :
    S.IsNRegular (G.scaleTwo M) 2 ∧ G.isStable (G.scaleTwo M) := by
  have hParts := T.globallyNADC_implies_locallyNADC_and_nRegular M 2 hADC
  exact ⟨H.nRegular_scaleTwo M hParts.2,
    H.locallyTwoADC_scaleTwo_stable M hParts.1⟩

/-- He (2025), Corollary 8.5. -/
theorem heADC2025Corollary85 (H : G.SectionEightLaws)
    (T : S.Theorem13Laws) (M : S.GlobalLattice) :
    S.IsGloballyNADC M 2 ↔
      S.IsLocallyNADC M 2 ∧
        ∃ L : S.GlobalLattice,
          G.isStable L ∧ S.IsNRegular L 2 ∧ G.isHalfScaleOf M L := by
  constructor
  · intro hADC
    have hParts := T.globallyNADC_implies_locallyNADC_and_nRegular M 2 hADC
    have hScaled := H.heADC2025Lemma84 T M hADC
    exact ⟨hParts.1, G.scaleTwo M, hScaled.2, hScaled.1,
      H.scaleTwo_halfScale M⟩
  · rintro ⟨hLocal, L, _, hRegular, hHalf⟩
    exact T.locallyNADC_and_nRegular_implies_globallyNADC M 2 hLocal
      (H.nRegular_of_halfScale hRegular hHalf)

end SectionEightLaws

end HeADC2025GlobalData

end Bong
