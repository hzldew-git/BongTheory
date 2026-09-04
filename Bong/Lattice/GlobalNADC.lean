/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

/-!
# Global and local n-ADC logic

This file isolates the exact local--global argument in He (2025), Theorem
1.3.  It deliberately does not pretend that the repository's dyadic
`Lattice` type is already a lattice over a number field.  Instead, a
`GlobalLocalLatticeSystem` records global lattices, their finite
localizations, and the six relations used in the published proof.

`Theorem13Laws` contains the arithmetic inputs cited in that proof:
localization of integrality and representation, the quadratic-space
local--global principle, the maximal-lattice test of Lemma 2.1, and the
globalization of a local maximal lattice supplied by Lemma 2.2 together
with O'Meara 82:18 and 91:2.  The theorem below proves the remaining logic
without an axiom, `sorry`, or hidden identification of local and global
quantifiers.
-/

namespace Bong

universe u v w

/-- Abstract data common to a global quadratic-lattice category and all of
its finite localizations.  Every relation is oriented with the representing
target first. -/
structure GlobalLocalLatticeSystem where
  GlobalLattice : Type u
  Place : Type v
  LocalLattice : Place → Type w
  globalRank : GlobalLattice → Nat
  localRank : {p : Place} → LocalLattice p → Nat
  globalIntegral : GlobalLattice → Prop
  localIntegral : {p : Place} → LocalLattice p → Prop
  globalAmbientRepresents : GlobalLattice → GlobalLattice → Prop
  /-- Compatibility at the real places in Definition 1.2(i). -/
  globalAdmissible : GlobalLattice → GlobalLattice → Prop
  localAmbientRepresents : {p : Place} →
    LocalLattice p → LocalLattice p → Prop
  globalRepresents : GlobalLattice → GlobalLattice → Prop
  localRepresents : {p : Place} →
    LocalLattice p → LocalLattice p → Prop
  localize : (p : Place) → GlobalLattice → LocalLattice p
  localMaximal : {p : Place} → LocalLattice p → Prop
  localEquivalent : {p : Place} →
    LocalLattice p → LocalLattice p → Prop

namespace GlobalLocalLatticeSystem

variable (S : GlobalLocalLatticeSystem.{u, v, w})

/-- Definition 1.2(ii): global `n`-ADC-ness, with the paper's standing
integrality convention made explicit. -/
def IsGloballyNADC (M : S.GlobalLattice) (n : Nat) : Prop :=
  S.globalIntegral M ∧
    ∀ N : S.GlobalLattice, S.globalRank N = n →
      S.globalIntegral N → S.globalAmbientRepresents M N →
        S.globalRepresents M N

/-- Definition 1.2(i): global `n`-universality, including the compatible
signature restriction at real places. -/
def IsGloballyNUniversal (M : S.GlobalLattice) (n : Nat) : Prop :=
  S.globalIntegral M ∧
    ∀ N : S.GlobalLattice, S.globalRank N = n →
      S.globalIntegral N → S.globalAdmissible M N →
        S.globalRepresents M N

/-- Definition 1.1(ii) at a specified finite place. -/
def IsNADCAt (M : S.GlobalLattice) (p : S.Place) (n : Nat) : Prop :=
  S.localIntegral (S.localize p M) ∧
    ∀ N : S.LocalLattice p, S.localRank N = n →
      S.localIntegral N →
        S.localAmbientRepresents (S.localize p M) N →
          S.localRepresents (S.localize p M) N

/-- Definition 1.1 following the local clause: local `n`-ADC-ness means
`n`-ADC-ness at every finite place. -/
def IsLocallyNADC (M : S.GlobalLattice) (n : Nat) : Prop :=
  ∀ p : S.Place, S.IsNADCAt M p n

/-- Definition 1.1(i) at a specified finite place. -/
def IsNUniversalAt (M : S.GlobalLattice) (p : S.Place) (n : Nat) : Prop :=
  S.localIntegral (S.localize p M) ∧
    ∀ N : S.LocalLattice p, S.localRank N = n →
      S.localIntegral N → S.localRepresents (S.localize p M) N

/-- Local `n`-universality at every finite place. -/
def IsLocallyNUniversal (M : S.GlobalLattice) (n : Nat) : Prop :=
  ∀ p : S.Place, S.IsNUniversalAt M p n

/-- The ambient stable-range premise used in Theorem 1.4(i): the localized
ambient quadratic space represents every rank-`n` integral lattice space. -/
def RepresentsEveryLocalAmbientAt
    (M : S.GlobalLattice) (p : S.Place) (n : Nat) : Prop :=
  ∀ N : S.LocalLattice p, S.localRank N = n →
    S.localIntegral N →
      S.localAmbientRepresents (S.localize p M) N

/-- The global stable-range premise corresponding to compatible signatures
in Theorem 1.4(iii). -/
def GlobalAmbientIffAdmissibleAtRank
    (M : S.GlobalLattice) (n : Nat) : Prop :=
  ∀ N : S.GlobalLattice, S.globalRank N = n →
    S.globalIntegral N →
      (S.globalAmbientRepresents M N ↔ S.globalAdmissible M N)

/-- Definition 1.1 alone gives the easy implication from local universality
to local ADC. -/
theorem isNUniversalAt_implies_isNADCAt
    {M : S.GlobalLattice} {p : S.Place} {n : Nat}
    (h : S.IsNUniversalAt M p n) : S.IsNADCAt M p n := by
  refine ⟨h.1, ?_⟩
  intro N hRank hIntegral _
  exact h.2 N hRank hIntegral

/-- He (2025), Theorem 1.4(i), reduced exactly to the cited stable-range
quadratic-space theorem. -/
theorem isNADCAt_iff_isNUniversalAt_of_representsEveryAmbient
    {M : S.GlobalLattice} {p : S.Place} {n : Nat}
    (hAmbient : S.RepresentsEveryLocalAmbientAt M p n) :
    S.IsNADCAt M p n ↔ S.IsNUniversalAt M p n := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro N hRank hIntegral
    exact h.2 N hRank hIntegral (hAmbient N hRank hIntegral)
  · exact isNUniversalAt_implies_isNADCAt S

/-- He (2025), Theorem 1.4(ii): the pointwise stable-range result at every
finite place is equivalent to the local statement. -/
theorem locallyNADC_iff_locallyNUniversal_of_representsEveryAmbient
    {M : S.GlobalLattice} {n : Nat}
    (hAmbient : ∀ p : S.Place,
      S.RepresentsEveryLocalAmbientAt M p n) :
    S.IsLocallyNADC M n ↔ S.IsLocallyNUniversal M n := by
  constructor <;> intro h p
  · exact (S.isNADCAt_iff_isNUniversalAt_of_representsEveryAmbient
      (hAmbient p)).mp (h p)
  · exact (S.isNADCAt_iff_isNUniversalAt_of_representsEveryAmbient
      (hAmbient p)).mpr (h p)

/-- He (2025), Theorem 1.4(iii), with the signature/ambient stable-range
input isolated explicitly. -/
theorem globallyNADC_iff_globallyNUniversal_of_ambient_iff_admissible
    {M : S.GlobalLattice} {n : Nat}
    (hAmbient : S.GlobalAmbientIffAdmissibleAtRank M n) :
    S.IsGloballyNADC M n ↔ S.IsGloballyNUniversal M n := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro N hRank hIntegral hAdmissible
    exact h.2 N hRank hIntegral
      ((hAmbient N hRank hIntegral).mpr hAdmissible)
  · intro h
    refine ⟨h.1, ?_⟩
    intro N hRank hIntegral hRepresents
    exact h.2 N hRank hIntegral
      ((hAmbient N hRank hIntegral).mp hRepresents)

/-- The maximal-lattice test family occurring in Lemma 2.1. -/
def RepresentsAllRelevantLocalMaximalAt
    (M : S.GlobalLattice) (p : S.Place) (n : Nat) : Prop :=
  ∀ N : S.LocalLattice p, S.localRank N = n →
    S.localMaximal N →
      S.localAmbientRepresents (S.localize p M) N →
        S.localRepresents (S.localize p M) N

/-- The paper's `n`-regularity condition. -/
def IsNRegular (M : S.GlobalLattice) (n : Nat) : Prop :=
  ∀ N : S.GlobalLattice, S.globalRank N = n →
    S.globalIntegral N →
      (∀ p : S.Place,
        S.localRepresents (S.localize p M) (S.localize p N)) →
          S.globalRepresents M N

/-- The cited arithmetic and localization results used by the proof of
Theorem 1.3.  These are fields of a proof-data structure, not project axioms:
an eventual number-field implementation must construct this structure. -/
structure Theorem13Laws : Prop where
  globalIntegral_iff_local (M : S.GlobalLattice) :
    S.globalIntegral M ↔
      ∀ p : S.Place, S.localIntegral (S.localize p M)
  rank_localize (p : S.Place) (N : S.GlobalLattice) :
    S.localRank (S.localize p N) = S.globalRank N
  integral_localize (p : S.Place) (N : S.GlobalLattice) :
    S.globalIntegral N → S.localIntegral (S.localize p N)
  ambient_localize (p : S.Place) (M N : S.GlobalLattice) :
    S.globalAmbientRepresents M N →
      S.localAmbientRepresents (S.localize p M) (S.localize p N)
  ambient_of_forall_local (M N : S.GlobalLattice) :
    (∀ p : S.Place,
      S.localAmbientRepresents (S.localize p M) (S.localize p N)) →
        S.globalAmbientRepresents M N
  representation_localize (p : S.Place) (M N : S.GlobalLattice) :
    S.globalRepresents M N →
      S.localRepresents (S.localize p M) (S.localize p N)
  local_representation_implies_ambient
      (p : S.Place) (M N : S.LocalLattice p) :
    S.localRepresents M N → S.localAmbientRepresents M N
  local_nadc_iff_maximal (M : S.GlobalLattice)
      (p : S.Place) (n : Nat) :
    S.IsNADCAt M p n ↔
      S.localIntegral (S.localize p M) ∧
        S.RepresentsAllRelevantLocalMaximalAt M p n
  globalize_local_maximal
      (M : S.GlobalLattice) (p : S.Place) (n : Nat)
      (N : S.LocalLattice p) :
    S.localRank N = n → S.localMaximal N →
      S.localAmbientRepresents (S.localize p M) N →
        ∃ N₀ : S.GlobalLattice,
          S.globalRank N₀ = n ∧ S.globalIntegral N₀ ∧
            S.globalAmbientRepresents M N₀ ∧
              S.localEquivalent (S.localize p N₀) N
  local_represents_of_equivalent_source
      (p : S.Place) (M N N' : S.LocalLattice p) :
    S.localEquivalent N N' → S.localRepresents M N →
      S.localRepresents M N'

namespace Theorem13Laws

variable {S : GlobalLocalLatticeSystem.{u, v, w}}

/-- Necessity in He (2025), Theorem 1.3: global `n`-ADC-ness implies both
local `n`-ADC-ness and `n`-regularity. -/
theorem globallyNADC_implies_locallyNADC_and_nRegular
    (H : S.Theorem13Laws) (M : S.GlobalLattice) (n : Nat)
    (hM : S.IsGloballyNADC M n) :
    S.IsLocallyNADC M n ∧ S.IsNRegular M n := by
  constructor
  · intro p
    rw [H.local_nadc_iff_maximal]
    refine ⟨(H.globalIntegral_iff_local M).mp hM.1 p, ?_⟩
    intro N hRank hMaximal hAmbient
    obtain ⟨N₀, hN₀Rank, hN₀Integral, hN₀Ambient, hN₀N⟩ :=
      H.globalize_local_maximal M p n N hRank hMaximal hAmbient
    have hGlobal : S.globalRepresents M N₀ :=
      hM.2 N₀ hN₀Rank hN₀Integral hN₀Ambient
    exact H.local_represents_of_equivalent_source p
      (S.localize p M) (S.localize p N₀) N hN₀N
      (H.representation_localize p M N₀ hGlobal)
  · intro N hRank hIntegral hEverywhere
    apply hM.2 N hRank hIntegral
    apply H.ambient_of_forall_local M N
    intro p
    exact H.local_representation_implies_ambient p
      (S.localize p M) (S.localize p N) (hEverywhere p)

/-- Sufficiency in He (2025), Theorem 1.3. -/
theorem locallyNADC_and_nRegular_implies_globallyNADC
    (H : S.Theorem13Laws) (M : S.GlobalLattice) (n : Nat)
    (hLocal : S.IsLocallyNADC M n) (hRegular : S.IsNRegular M n) :
    S.IsGloballyNADC M n := by
  refine ⟨(H.globalIntegral_iff_local M).mpr (fun p => (hLocal p).1), ?_⟩
  intro N hRank hIntegral hAmbient
  apply hRegular N hRank hIntegral
  intro p
  exact (hLocal p).2 (S.localize p N)
    ((H.rank_localize p N).trans hRank)
    (H.integral_localize p N hIntegral)
    (H.ambient_localize p M N hAmbient)

/-- He (2025), Theorem 1.3, with every cited local--global input exposed in
`Theorem13Laws`. -/
theorem globallyNADC_iff_locallyNADC_and_nRegular
    (H : S.Theorem13Laws) (M : S.GlobalLattice) (n : Nat) :
    S.IsGloballyNADC M n ↔
      S.IsLocallyNADC M n ∧ S.IsNRegular M n := by
  constructor
  · exact H.globallyNADC_implies_locallyNADC_and_nRegular M n
  · rintro ⟨hLocal, hRegular⟩
    exact H.locallyNADC_and_nRegular_implies_globallyNADC
      M n hLocal hRegular

end Theorem13Laws

end GlobalLocalLatticeSystem

end Bong
