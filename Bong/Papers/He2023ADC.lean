/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.NADC

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

end Bong
