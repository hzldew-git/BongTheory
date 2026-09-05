/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.NADC
import Bong.Lattice.GlobalNADC
import Bong.Bong.He2023ADCSectionThree
import Bong.Bong.He2023ADCPublishedRepresentation
import Bong.Bong.He2023ADCSectionFour
import Bong.Bong.He2023ADCMaximalProfiles
import Bong.Bong.He2023ADCGenericProfiles
import Bong.Bong.He2023ADCOddMaximalStructure
import Bong.Bong.He2023ADCQuaternaryMaximal
import Bong.Bong.He2023ADCEvenRepresentationBounds
import Bong.Bong.He2023ADCEvenFirstTests
import Bong.Bong.He2023ADCEvenFirstDefects
import Bong.Bong.He2023ADCEvenSecondTests
import Bong.Bong.He2023ADCEvenMixedTests
import Bong.Bong.He2023ADCEvenTerminalObstruction
import Bong.Bong.He2023ADCEvenPenultimateObstruction
import Bong.Bong.He2023ADCEvenCorankOneTests
import Bong.Bong.He2023ADCEvenCorankOne
import Bong.Bong.He2023ADCEvenCentralTrigger
import Bong.Bong.He2023ADCEvenCentralPrefix
import Bong.Bong.He2023ADCEvenCentralObstruction
import Bong.Bong.He2023ADCEvenCentralAlpha
import Bong.Bong.He2023ADCEvenCorankTwoFirst
import Bong.Bong.He2023ADCEvenCorankTwoGeneric
import Bong.Bong.He2023ADCPublishedParameterDomain
import Bong.Bong.He2023ADCEvenCorankTwoSecond
import Bong.Bong.He2023ADCQuaternaryBoundaryCandidate
import Bong.Bong.He2023ADCQuaternaryBoundaryConditions
import Bong.Bong.He2023ADCQuaternaryBoundaryTests
import Bong.Bong.He2023ADCQuaternaryBoundaryEndpoint
import Bong.Bong.He2023ADCQuaternaryBoundaryGeneric
import Bong.Bong.He2023ADCQuaternaryBoundaryNormalization
import Bong.Bong.He2023ADCQuaternaryBoundaryTesting
import Bong.Bong.He2023ADCQuaternaryBoundaryDiscrepancy
import Bong.Bong.He2023ADCTheorem71
import Bong.Bong.He2023ADCExceptionalQuaternaryNonThree
import Bong.Bong.He2023ADCLemma611
import Bong.Bong.He2023ADCRemark63

/-!
# He: n-ADC integral quadratic lattices

Canonical review and distribution entry point for Zilong He, *On n-ADC
integral quadratic lattices over algebraic number fields*, Doc. Math. 30
(2025), no. 4, 981--1022.  The publisher version of record is the sole
semantic authority.

The present layer covers the local dyadic specialization of Definition 1.1,
Lemma 2.1, Section 3, and the checked Section 4 endpoints, together with the
logical local--global reductions in Theorems 1.3--1.4.  Number-field
localization laws remain explicit proof data rather than hidden axioms.
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

/-- He, Theorem 1.4(i), specialized to a dyadic local field and discharged
from the proved rank-`n+3` ambient-space theorem. -/
theorem heADCTheorem14iLocalDyadic
    [FiniteDimensional K V]
    (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat)
    (hRank : n + 3 ≤ Module.finrank K V) :
    IsNADC.{u, v, w} q L n ↔ IsNUniversal.{u, v, w} q L n :=
  isNADC_iff_isNUniversal_of_rank_add_three_le q L n hRank

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
