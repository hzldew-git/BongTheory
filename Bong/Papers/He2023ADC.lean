/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.NADC
import Bong.Lattice.GlobalNADC
import Bong.QuadraticSpace.He2025SubspaceDescentTopology
import Bong.Dyadic.PowerIdealResidueQuotient
import Bong.Dyadic.PrincipalUnitResidueQuotient
import Bong.Dyadic.UnitSquareClassOddLayer
import Bong.Dyadic.UnitSquareClassCount
import Bong.Lattice.He2023ADCSectionEight
import Bong.Lattice.He2023ADCEnumerativeMain
import Bong.Bong.He2023ADCSectionThree
import Bong.Bong.He2023ADCPublishedRepresentation
import Bong.Bong.He2023ADCSectionFour
import Bong.Bong.He2023ADCLemma46
import Bong.Bong.He2023ADCNonDyadicLemma45
import Bong.Bong.He2023ADCNonDyadicProposition42
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
import Bong.Bong.He2023ADCTheorem74
import Bong.Bong.He2023ADCLemma79
import Bong.Bong.He2023ADCLemma710
import Bong.Bong.He2023ADCLemma712
import Bong.Bong.He2023ADCLemma714
import Bong.Bong.He2023ADCLemma715
import Bong.Bong.He2023ADCDefinition716
import Bong.Bong.He2023ADCLemma718
import Bong.Bong.He2023ADCLemma719Models
import Bong.Bong.He2023ADCTheorem72Published
import Bong.Bong.He2023ADCRemark73
import Bong.Bong.He2023ADCUnitRepresentativeCount
import Bong.Bong.He2023ADCCorollary721
import Bong.Bong.He2023ADCQuaternaryCatalogue
import Bong.Bong.He2023ADCTheorem110
import Bong.Bong.He2023ADCExceptionalQuaternaryNonThree
import Bong.Bong.He2023ADCLemma611
import Bong.Bong.He2023ADCRemark63
import Bong.Bong.He2023ADCSectionFive
import Bong.Bong.He2023ADCNonDyadicTable
import Bong.Bong.He2023ADCNonDyadicTheorem110
import Bong.Bong.He2023ADCNonDyadicLemma46
import Bong.Bong.He2023ADCNonDyadicProposition416
import Bong.Bong.He2023ADCNonDyadicMinimalTesting
import Bong.Bong.He2023ADCUnaryTesting

/-!
# He: n-ADC integral quadratic lattices

Canonical review and distribution entry point for Zilong He, *On n-ADC
integral quadratic lattices over algebraic number fields*, Doc. Math. 30
(2025), no. 4, 981--1022.  The publisher version of record is the sole
semantic authority.

The present layer covers the local dyadic specialization of Definition 1.1,
Lemma 2.1, and Sections 3--4.  It also proves the algebraic induction and
literal subspace conclusion of Lemma 2.2.  The one-dimensional case is reduced
to density and open nonzero square classes; mathlib supplies density for every
number-field finite completion, while the inverse function theorem supplies
square-class openness.
In particular, the rank-one table in
Definition 4.1, Proposition 4.2 and Remark 4.3, together with its literal
deletion-minimality in Lemma 4.9(ii), is included.  It also covers the
corrected local classifications in Theorems
6.2 and 7.1, and the odd-rank characterization in Theorem 7.4 together with
the complete proof chain through Lemmas 7.5--7.10 and 7.12, the
complete normalized two-row form of Lemma 7.11, the corrected quantifier
form of Lemma 7.13, and the complete classification proof through Lemmas
7.14--7.15.  It further formalizes Definition 7.16, Remark 7.17, and
Lemmas 7.18--7.20 and Theorem 7.2, including integral-isometry bridges from the explicit
Lemma 7.19 construction to both named `N`-families and the complete
Hilbert-symbol-selected classification in Lemma 7.20.  Theorem 7.2 is
available both independently of representatives and in the literal finite
form with parameters in `U \ {1, Delta}` and `epsilon*pi^k`; its final
maximal-overlap assertion is proved as an integral-isometry classification.
All three literal integral-isometry formulas of Remark 7.3 are also proved,
including their prescribed powers of the uniformizer and the ordered ternary
tail `pi A perp <Delta epsilon>`.  Corollary 7.21 is proved as a finite,
complete, and irredundant integral-isometry catalogue, with an exact maximal
versus nonmaximal partition.  Its numerical counts isolate the unit
square-class cardinality quoted from O'Meara 63:9 as an explicit premise.
At the binary rank-four boundary, the formalization proves a corrected exact
catalogue with two nonmaximal classes and count `8 * (N p)^e + 2`; it also
machine-checks that the single-exception formulations printed in Theorems
1.9(ii), 1.10, and 6.2 are false.
All dyadic branches of Theorem 1.10 are assembled as exact, complete, and
irredundant integral-isometry catalogues, including equal rank, corank one,
stable even corank two, odd corank two, and the corrected binary boundary.
The non-dyadic branch is likewise assembled into exact seven- and eight-row
catalogues, including all three rank branches and the specialization of the
printed formula at ramification index zero, relative to an explicit
non-dyadic maximal-lattice catalogue law package.  The literal block rows of
Lemma 4.7(i) are transcribed separately: their total ranks, scale-zero and
scale-one ranks, the missing row `N_2^2(1)`, and the table-level identity
`J_{0,1}(N)=N` are kernel-checked.  The exact rank-four table dichotomy used
by non-dyadic Proposition 4.16 is also proved; the proposition itself is
derived from explicit maximal-catalogue and actual-lattice realization laws.
Corollary 1.8 is formalized as the exact finite-cardinality deduction from
the two cited external catalogues.  For Theorem 1.11, all 48 integral Gram
matrices in the publisher's Table 1 are transcribed literally.  Their
symmetry, printed discriminants, positive definiteness over `ℚ`, and the
21 occurrences of `None` in the last column are kernel-checked; the last
column is then identified with the abstract Table 2 selection predicate.
Relative to the remaining Oh-catalogue and prime-by-prime local-verification
inputs, Theorem 1.11 is formalized as an exact, complete, and irredundant
21-row catalogue, while global `2`-ADC is derived from Corollary 8.5 rather
than assumed as a table field.
It also records the logical local--global
reductions in Theorems 1.3--1.4.  The complete logical derivations of all four
numbered Section 5 results and of the Section 8 local--global chain are also
formalized over explicit non-dyadic Jordan and number-field arithmetic law
packages.  In Section 8, class-number-one regularity is derived from genus
lifting and isometry transport, while local maximal-implies-ADC and the local
Theorem 1.5 equivalence are derived from lower maximal-extension,
representation, and classification laws.  Theorem 8.2 is derived by splitting
the definite Meyer input from the indefinite Xu spinor-genus construction
and O'Meara 104:5 single-class input.  Concrete constructions of the
non-dyadic and number-field law
packages, and imports of the Hanke--Kirschmer--Oh external enumerations,
remain open;
number-field localization, Meyer--Xu genus separation, and non-dyadic Jordan
classification and representation facts are therefore visible proof data
rather than hidden axioms.
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
