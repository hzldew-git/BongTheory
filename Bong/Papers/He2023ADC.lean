/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.NADC
import Bong.Lattice.GlobalNADC
import Bong.Bong.He2023ADCSectionThree

/-!
# He: n-ADC integral quadratic lattices

Canonical review and distribution entry point for Zilong He, *On n-ADC
integral quadratic lattices over algebraic number fields*, Doc. Math. 30
(2025), no. 4, 981--1022.  The publisher version of record is the sole
semantic authority.

The present layer covers the local dyadic specialization of Definition 1.1,
Lemma 2.1, Lemma 4.14, and Proposition 4.15.  Global localization,
`n`-regularity, and the remaining classification theorems are separate proof
obligations.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- He, Lemma 2.1, specialized to the repository's dyadic local-field
interface. -/
theorem heADCLemma21LocalDyadic
    (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat) (_hn : 0 < n) :
    IsNADC.{u, v, w} q L n ↔
      IsIntegral q L ∧
        RepresentsAllRelevantOMaximalOfRank.{u, v, w} q L n :=
  isNADC_iff_representsAllRelevantOMaximal q L n

/-- He, Lemma 4.14, specialized to the repository's dyadic local-field
interface. -/
theorem heADCLemma414LocalDyadic
    {V : Type u} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (hL : IsOMaximal q L) (n : Nat) :
    IsNADC.{u, u, u} q L n :=
  hL.isNADC n

/-- He, Proposition 4.15, specialized to dyadic local fields. -/
theorem heADCProposition415LocalDyadic
    {V : Type u} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat)
    (hrank : Module.finrank K V = n) :
    IsNADC.{u, u, u} q L n ↔ IsOMaximal q L :=
  isNADC_iff_isOMaximal_of_finrank_eq q L n hrank

end Lattice

namespace GlobalLocalLatticeSystem

universe u v w

/-- He, Theorem 1.3.  The proof is complete relative to the explicitly
bundled number-field localization results in `Theorem13Laws`; no such result
is silently postulated as a project axiom. -/
theorem heADCTheorem13
    (S : GlobalLocalLatticeSystem.{u, v, w})
    (H : S.Theorem13Laws) (M : S.GlobalLattice) (n : Nat) :
    S.IsGloballyNADC M n ↔ S.IsLocallyNADC M n ∧ S.IsNRegular M n :=
  H.globallyNADC_iff_locallyNADC_and_nRegular M n

/-- He, Theorem 1.4(i), with the cited stable-range ambient-space
representation theorem supplied as an explicit premise. -/
theorem heADCTheorem14i
    (S : GlobalLocalLatticeSystem.{u, v, w})
    {M : S.GlobalLattice} {p : S.Place} {n : Nat}
    (hAmbient : S.RepresentsEveryLocalAmbientAt M p n) :
    S.IsNADCAt M p n ↔ S.IsNUniversalAt M p n :=
  S.isNADCAt_iff_isNUniversalAt_of_representsEveryAmbient hAmbient

/-- He, Theorem 1.4(ii). -/
theorem heADCTheorem14ii
    (S : GlobalLocalLatticeSystem.{u, v, w})
    {M : S.GlobalLattice} {n : Nat}
    (hAmbient : ∀ p : S.Place,
      S.RepresentsEveryLocalAmbientAt M p n) :
    S.IsLocallyNADC M n ↔ S.IsLocallyNUniversal M n :=
  S.locallyNADC_iff_locallyNUniversal_of_representsEveryAmbient hAmbient

/-- He, Theorem 1.4(iii), retaining the compatible-signature condition from
the published Definition 1.2(i). -/
theorem heADCTheorem14iii
    (S : GlobalLocalLatticeSystem.{u, v, w})
    {M : S.GlobalLattice} {n : Nat}
    (hAmbient : S.GlobalAmbientIffAdmissibleAtRank M n) :
    S.IsGloballyNADC M n ↔ S.IsGloballyNUniversal M n :=
  S.globallyNADC_iff_globallyNUniversal_of_ambient_iff_admissible hAmbient

end GlobalLocalLatticeSystem

end Bong
