/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicTheorem15
import Bong.Lattice.GlobalNADC
import Bong.Lattice.He2022ClassicNumberFieldDiscriminant

/-!
# He (2024), Section 8: global applications

This file formalizes the global--local deductions in Section 8 of Zilong He,
*On classic n-universal quadratic forms over dyadic local fields*, using the
author-corrected v6 manuscript as semantic authority.

The repository does not yet identify its dyadic `Lattice` type with lattices
over number fields and all their completions.  Accordingly, the arithmetic
inputs used in the paper--localization, ramification and discriminant,
coefficient transport, and strong approximation--are fields of ordinary
proof-data structures.  They are not Lean axioms.  The theorems below check
the remaining logical deductions while leaving construction of concrete
number-field instances as an explicit implementation boundary.
-/

namespace Bong

universe u v w u' v' w'

/-! ## Lemma 8.1: local-extension data -/

/-- The numerical and good-BONG predicates occurring when coefficients from
one dyadic local field are viewed in a finite extension.  `Element` denotes
the nonzero coefficients from the base field. -/
structure HeClassic2024LocalExtensionData where
  Element : Type u
  baseOrder : Element → Int
  extensionOrder : Element → Int
  baseDefect : Element → WithTop ℚ
  extensionDefect : Element → WithTop ℚ
  baseRamificationIndex : Nat
  extensionRamificationIndex : Nat
  relativeRamificationIndex : Nat
  BaseGoodBONG : {m : Nat} → (Fin m → Element) → Prop
  ExtensionGoodBONG : {m : Nat} → (Fin m → Element) → Prop

namespace HeClassic2024LocalExtensionData

variable (D : HeClassic2024LocalExtensionData)

/-- The three arithmetic inputs in the proof of He, Lemma 8.1.  The first
field also records the tower identity for the absolute ramification index,
which is used in the good-BONG calculation.  Here `goodBONG_transfer` is the
coefficient-criterion consequence proved in the manuscript; it does not by
itself identify the resulting lattice with a separately specified scalar
extension. -/
structure Lemma81Laws : Prop where
  relativeRamificationIndex_pos : 0 < D.relativeRamificationIndex
  ramificationIndex_tower :
    D.extensionRamificationIndex =
      D.baseRamificationIndex * D.relativeRamificationIndex
  order_scale (a : D.Element) :
    D.extensionOrder a =
      D.baseOrder a * (D.relativeRamificationIndex : Int)
  defect_scale (a : D.Element) :
    (((D.relativeRamificationIndex : Nat) : ℚ) : WithTop ℚ) * D.baseDefect a ≤
      D.extensionDefect a
  goodBONG_transfer {m : Nat} (a : Fin m → D.Element) :
    D.BaseGoodBONG a → D.ExtensionGoodBONG a

namespace Lemma81Laws

variable {D : HeClassic2024LocalExtensionData}

/-- He (2024), Lemma 8.1(i). -/
theorem he2022ClassicLemma81i (H : D.Lemma81Laws) (a : D.Element) :
    D.extensionOrder a =
      D.baseOrder a * (D.relativeRamificationIndex : Int) :=
  H.order_scale a

/-- He (2024), Lemma 8.1(ii), on the defect-order scale. -/
theorem he2022ClassicLemma81ii (H : D.Lemma81Laws) (a : D.Element) :
    (((D.relativeRamificationIndex : Nat) : ℚ) : WithTop ℚ) * D.baseDefect a ≤
      D.extensionDefect a :=
  H.defect_scale a

/-- The coefficient-criterion interface for revised v6 Lemma 8.1(iii).
Its concrete realization is in `He2022ClassicNumberFieldBONGBridge`; this
abstract predicate alone does not identify an ambient scalar extension. -/
theorem he2022ClassicLemma81iii (H : D.Lemma81Laws)
    {m : Nat} (a : Fin m → D.Element) (hGood : D.BaseGoodBONG a) :
    D.ExtensionGoodBONG a :=
  H.goodBONG_transfer a hGood

end Lemma81Laws

end HeClassic2024LocalExtensionData

/-! ## Proposition 8.2 and the global results -/

/-- Extra number-field data used by the global applications.  The underlying
global/local representation relations and localization operation are supplied
by `GlobalLocalLatticeSystem`. -/
structure HeClassic2024GlobalData
    (S : GlobalLocalLatticeSystem.{u, v, w}) where
  positiveDefinite : S.GlobalLattice → Prop
  isDyadic : S.Place → Prop
  ramificationIndexAt : S.Place → Nat
  discriminantOdd : Prop
  isDiagonalIntegerLattice : S.GlobalLattice → Prop
  localAdjacentDefectsLarge : S.GlobalLattice → S.Place → Prop
  sumOfSquares : Nat → S.GlobalLattice
  notTotallyReal : Prop

namespace HeClassic2024GlobalData

variable {S : GlobalLocalLatticeSystem.{u, v, w}}
  (G : HeClassic2024GlobalData S)

/-- The first hypothesis of Proposition 8.2: representation of every positive
definite classic integral global lattice of the indicated rank. -/
def RepresentsAllPositiveDefiniteClassicAtRank
    (M : S.GlobalLattice) (n : Nat) : Prop :=
  S.globalIntegral M ∧
    ∀ N : S.GlobalLattice, S.globalRank N = n →
      S.globalIntegral N → G.positiveDefinite N →
        S.globalRepresents M N

/-- The globalization and localization inputs in the proof of He,
Proposition 8.2.  The field `positiveDefinite_globalization` isolates the use
of O'Meara 81:14: a prescribed integral lattice at one finite place is the
localization of a positive definite integral global lattice. -/
structure Proposition82Laws : Prop where
  integral_localize (p : S.Place) (M : S.GlobalLattice) :
    S.globalIntegral M → S.localIntegral (S.localize p M)
  positiveDefinite_globalization
      (p : S.Place) (N : S.LocalLattice p) :
    S.localIntegral N →
      ∃ N₀ : S.GlobalLattice,
        S.globalRank N₀ = S.localRank N ∧
          S.globalIntegral N₀ ∧ G.positiveDefinite N₀ ∧
            S.localEquivalent (S.localize p N₀) N
  representation_localize
      (p : S.Place) (M N : S.GlobalLattice) :
    S.globalRepresents M N →
      S.localRepresents (S.localize p M) (S.localize p N)
  local_represents_of_equivalent_target
      (p : S.Place) (M N N' : S.LocalLattice p) :
    S.localEquivalent N N' → S.localRepresents M N →
      S.localRepresents M N'

namespace Proposition82Laws

variable {G : HeClassic2024GlobalData S}

/-- The first, stronger sentence of He (2024), Proposition 8.2, derived from
the positive-definite globalization used in the published proof. -/
theorem he2022ClassicProposition82_positive
    (H : G.Proposition82Laws) (M : S.GlobalLattice) (n : Nat)
    (hPositive : G.RepresentsAllPositiveDefiniteClassicAtRank M n) :
    ∀ p : S.Place, S.IsNUniversalAt M p n := by
  intro p
  refine ⟨H.integral_localize p M hPositive.1, ?_⟩
  intro N hRank hIntegral
  obtain ⟨N₀, hGlobalRank, hGlobalIntegral, hGlobalPositive,
      hEquivalent⟩ := H.positiveDefinite_globalization p N hIntegral
  have hGlobal : S.globalRepresents M N₀ :=
    hPositive.2 N₀ (hGlobalRank.trans hRank) hGlobalIntegral hGlobalPositive
  exact H.local_represents_of_equivalent_target p
    (S.localize p M) (S.localize p N₀) N hEquivalent
    (H.representation_localize p M N₀ hGlobal)

end Proposition82Laws

/-- The local-to-global inputs used in the sufficiency proof of Theorem 1.9.
The last field isolates strong approximation after all finite-place
representations and the real-place compatibility condition have been
supplied. -/
structure SumOfSquaresLocalGlobalLaws : Prop where
  sumOfSquares_integral (m : Nat) :
    S.globalIntegral (G.sumOfSquares m)
  rank_localize (p : S.Place) (N : S.GlobalLattice) :
    S.localRank (S.localize p N) = S.globalRank N
  integral_localize (p : S.Place) (N : S.GlobalLattice) :
    S.globalIntegral N → S.localIntegral (S.localize p N)
  strong_approximation
      (m n : Nat) (N : S.GlobalLattice) :
    G.notTotallyReal → n + 3 ≤ m →
      S.globalAdmissible (G.sumOfSquares m) N →
        (∀ p : S.Place,
          S.localRepresents
            (S.localize p (G.sumOfSquares m)) (S.localize p N)) →
          S.globalRepresents (G.sumOfSquares m) N

namespace SumOfSquaresLocalGlobalLaws

variable {G : HeClassic2024GlobalData S}

/-- The local-to-global step in the sufficiency direction of He (2024),
Theorem 1.9, derived from the explicitly separated strong-approximation
inputs. -/
theorem sumOfSquares_local_to_global
    (H : G.SumOfSquaresLocalGlobalLaws) (m n : Nat)
    (hNotTotallyReal : G.notTotallyReal) (hRank : n + 3 ≤ m)
    (hLocal : ∀ p : S.Place,
      S.IsNUniversalAt (G.sumOfSquares m) p n) :
    S.IsGloballyNUniversal (G.sumOfSquares m) n := by
  refine ⟨H.sumOfSquares_integral m, ?_⟩
  intro N hNRank hNIntegral hAdmissible
  apply H.strong_approximation m n N hNotTotallyReal hRank hAdmissible
  intro p
  exact (hLocal p).2 (S.localize p N)
    ((H.rank_localize p N).trans hNRank)
    (H.integral_localize p N hNIntegral)

end SumOfSquaresLocalGlobalLaws

/-- The direction of the discriminant/ramification criterion actually used
by the global applications. -/
structure DiscriminantRamificationLaws : Prop where
  discriminantOdd_of_unramified :
    (∀ p : S.Place, G.isDyadic p → G.ramificationIndexAt p = 1) →
      G.discriminantOdd

namespace DiscriminantRamificationLaws

variable {G : HeClassic2024GlobalData S}

/-- An even discriminant forces a dyadic place whose ramification index is
not one.  Positivity of that index is kept separate in `SectionEightLaws`. -/
theorem exists_ramifiedDyadic_of_not_discriminantOdd
    (H : G.DiscriminantRamificationLaws)
    (hOdd : ¬ G.discriminantOdd) :
    ∃ p : S.Place,
      G.isDyadic p ∧ G.ramificationIndexAt p ≠ 1 := by
  by_contra hExists
  apply hOdd
  apply H.discriminantOdd_of_unramified
  intro p hpDyadic
  by_contra hpNe
  exact hExists ⟨p, hpDyadic, hpNe⟩

end DiscriminantRamificationLaws

/-! ## Concrete number-field realization of the discriminant package -/

/-- Identification of the abstract finite places in `GlobalData` with prime
ideals of a number field.  Once this structural bridge is supplied, the two
discriminant directions and positivity of ramification indices follow from
the concrete theorems in `He2022ClassicNumberFieldDiscriminant`; they are not
additional arithmetic assumptions. -/
structure NumberFieldDiscriminantBridge
    (K : Type u') [Field K] [NumberField K] where
  idealAt : S.Place → Ideal (NumberField.RingOfIntegers K)
  idealAt_isPrime (p : S.Place) : (idealAt p).IsPrime
  isDyadic_iff (p : S.Place) :
    G.isDyadic p ↔
      HeClassic2024NumberField.IsDyadicPrime K (idealAt p)
  ramificationIndexAt_eq (p : S.Place) :
    G.ramificationIndexAt p = (idealAt p).ramificationIdx ℤ
  discriminantOdd_iff :
    G.discriminantOdd ↔
      HeClassic2024NumberField.DiscriminantOdd K
  exists_place_of_dyadicPrime
      (P : Ideal (NumberField.RingOfIntegers K)) :
    P.IsPrime → HeClassic2024NumberField.IsDyadicPrime K P →
      ∃ p : S.Place, idealAt p = P

/-- Identification of the abstract place type with the standard height-one
spectrum of the ring of integers.  Unlike `NumberFieldDiscriminantBridge`,
this interface does not ask callers to re-prove primality or coverage of
prime ideals: those follow from the equivalence and the dyadic condition. -/
structure HeightOneSpectrumIdentification
    (K : Type u') [Field K] [NumberField K] where
  placeEquiv :
    S.Place ≃
      IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K)
  isDyadic_iff (p : S.Place) :
    G.isDyadic p ↔
      HeClassic2024NumberField.IsDyadicPrime K
        (placeEquiv p).asIdeal
  ramificationIndexAt_eq (p : S.Place) :
    G.ramificationIndexAt p =
      (placeEquiv p).asIdeal.ramificationIdx ℤ
  discriminantOdd_iff :
    G.discriminantOdd ↔
      HeClassic2024NumberField.DiscriminantOdd K

namespace HeightOneSpectrumIdentification

variable {G : HeClassic2024GlobalData S}
  {K : Type u'} [Field K] [NumberField K]

/-- Construct the discriminant bridge from the canonical finite-place type.
The only nontrivial coverage step observes that a prime ideal containing two
is nonzero, hence is a point of the height-one spectrum. -/
def numberFieldDiscriminantBridge
    (I : G.HeightOneSpectrumIdentification K) :
    G.NumberFieldDiscriminantBridge K where
  idealAt p := (I.placeEquiv p).asIdeal
  idealAt_isPrime p := (I.placeEquiv p).isPrime
  isDyadic_iff p := I.isDyadic_iff p
  ramificationIndexAt_eq p := I.ramificationIndexAt_eq p
  discriminantOdd_iff := I.discriminantOdd_iff
  exists_place_of_dyadicPrime P hP hDyadic := by
    have hPne : P ≠ ⊥ := by
      intro hPbot
      rw [HeClassic2024NumberField.IsDyadicPrime, hPbot] at hDyadic
      simp at hDyadic
    let q : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K) := ⟨P, hP, hPne⟩
    refine ⟨I.placeEquiv.symm q, ?_⟩
    simp [q]

end HeightOneSpectrumIdentification

namespace NumberFieldDiscriminantBridge

variable {G : HeClassic2024GlobalData S}
  {K : Type u'} [Field K] [NumberField K]

/-- The abstract necessity-side law constructed from the actual
number-field discriminant theorem and the place bridge. -/
theorem discriminantRamificationLaws
    (B : G.NumberFieldDiscriminantBridge K) :
    G.DiscriminantRamificationLaws := by
  refine ⟨?_⟩
  intro hUnramified
  apply B.discriminantOdd_iff.mpr
  apply
    HeClassic2024NumberField.discriminantOdd_of_forall_ramificationIdx_eq_one K
  intro P hP hDyadic
  obtain ⟨p, hp⟩ := B.exists_place_of_dyadicPrime P hP hDyadic
  subst P
  rw [← B.ramificationIndexAt_eq]
  exact hUnramified p ((B.isDyadic_iff p).mpr hDyadic)

/-- The unary sufficiency-side implication constructed from the actual
number-field discriminant theorem and the place bridge. -/
theorem ramificationIndexAt_one_of_discriminantOdd
    (B : G.NumberFieldDiscriminantBridge K) (p : S.Place)
    (hpDyadic : G.isDyadic p) (hOdd : G.discriminantOdd) :
    G.ramificationIndexAt p = 1 := by
  rw [B.ramificationIndexAt_eq]
  apply
    HeClassic2024NumberField.ramificationIdx_eq_one_of_discriminantOdd K
  · exact B.discriminantOdd_iff.mp hOdd
  · exact B.idealAt_isPrime p
  · exact (B.isDyadic_iff p).mp hpDyadic

/-- Positivity of the abstract ramification index follows from the actual
prime-ideal ramification index. -/
theorem ramificationIndexAt_pos
    (B : G.NumberFieldDiscriminantBridge K) (p : S.Place) :
    0 < G.ramificationIndexAt p := by
  rw [B.ramificationIndexAt_eq]
  exact HeClassic2024NumberField.ramificationIdx_pos K
    (B.idealAt p) (B.idealAt_isPrime p)

end NumberFieldDiscriminantBridge

/-- The three finite-place arithmetic branches in the sufficiency proof of
Theorem 1.9.  The dyadic unary branch is separated from the `n >= 2` branch
because the paper invokes different local criteria. -/
structure SumOfSquaresLocalUniversalityLaws : Prop where
  ramificationIndexAt_one_of_discriminantOdd (p : S.Place) :
    G.isDyadic p → G.discriminantOdd → G.ramificationIndexAt p = 1
  nonDyadic_localUniversal (m n : Nat) (p : S.Place) :
    1 ≤ n → n + 3 ≤ m → ¬ G.isDyadic p →
      S.IsNUniversalAt (G.sumOfSquares m) p n
  dyadic_unary_localUniversal (m : Nat) (p : S.Place) :
    4 ≤ m → G.isDyadic p → G.ramificationIndexAt p = 1 →
      S.IsNUniversalAt (G.sumOfSquares m) p 1
  dyadic_higherRank_localUniversal (m n : Nat) (p : S.Place) :
    2 ≤ n → n + 3 ≤ m → G.isDyadic p →
      G.ramificationIndexAt p = 1 →
        S.IsNUniversalAt (G.sumOfSquares m) p n

namespace SumOfSquaresLocalUniversalityLaws

variable {G : HeClassic2024GlobalData S}

/-- Construct the finite-place package from its three genuinely local
representation branches and the concrete number-field discriminant bridge.
The odd-discriminant-to-index-one implication is supplied by the proved
number-field theorem. -/
theorem ofNumberFieldDiscriminantBridge
    {K : Type u'} [Field K] [NumberField K]
    (B : G.NumberFieldDiscriminantBridge K)
    (hNonDyadic : ∀ (m n : Nat) (p : S.Place),
      1 ≤ n → n + 3 ≤ m → ¬ G.isDyadic p →
        S.IsNUniversalAt (G.sumOfSquares m) p n)
    (hDyadicUnary : ∀ (m : Nat) (p : S.Place),
      4 ≤ m → G.isDyadic p → G.ramificationIndexAt p = 1 →
        S.IsNUniversalAt (G.sumOfSquares m) p 1)
    (hDyadicHigherRank : ∀ (m n : Nat) (p : S.Place),
      2 ≤ n → n + 3 ≤ m → G.isDyadic p →
        G.ramificationIndexAt p = 1 →
          S.IsNUniversalAt (G.sumOfSquares m) p n) :
    G.SumOfSquaresLocalUniversalityLaws where
  ramificationIndexAt_one_of_discriminantOdd :=
    B.ramificationIndexAt_one_of_discriminantOdd
  nonDyadic_localUniversal := hNonDyadic
  dyadic_unary_localUniversal := hDyadicUnary
  dyadic_higherRank_localUniversal := hDyadicHigherRank

/-- Finite-place local universality in the sufficiency direction of He
(2024), Theorem 1.9, derived by the source's dyadic/unary case split. -/
theorem sumOfSquares_localUniversal_of_oddDiscriminant
    (H : G.SumOfSquaresLocalUniversalityLaws) (m n : Nat)
    (hn : 1 ≤ n) (hRank : n + 3 ≤ m) (hOdd : G.discriminantOdd) :
    ∀ p : S.Place, S.IsNUniversalAt (G.sumOfSquares m) p n := by
  intro p
  by_cases hpDyadic : G.isDyadic p
  · have hpOne : G.ramificationIndexAt p = 1 :=
      H.ramificationIndexAt_one_of_discriminantOdd p hpDyadic hOdd
    by_cases hnOne : n = 1
    · subst n
      exact H.dyadic_unary_localUniversal m p hRank hpDyadic hpOne
    · exact H.dyadic_higherRank_localUniversal m n p (by omega)
        hRank hpDyadic hpOne
  · exact H.nonDyadic_localUniversal m n p hn hRank hpDyadic

end SumOfSquaresLocalUniversalityLaws

/-- Arithmetic inputs used in Proposition 8.2 and Theorems 1.5, 1.7 and 1.9.
Each field corresponds to a specific localization, ramification, or strong-
approximation step in the v5 proof. -/
structure SectionEightLaws : Prop where
  positiveDefinite_admissible (M N : S.GlobalLattice) :
    G.positiveDefinite N → S.globalAdmissible M N
  proposition82 : G.Proposition82Laws
  discriminantRamification : G.DiscriminantRamificationLaws
  ramificationIndexAt_pos (p : S.Place) :
    G.isDyadic p → 0 < G.ramificationIndexAt p
  theorem15_local (M : S.GlobalLattice) (p : S.Place) (n : Nat) :
    G.isDyadic p → 1 ≤ n → n + 3 ≤ S.globalRank M →
      S.IsNUniversalAt M p n → G.localAdjacentDefectsLarge M p →
        G.ramificationIndexAt p = 1
  diagonal_localAdjacentDefectsLarge_of_universal_even
      (M : S.GlobalLattice) (p : S.Place) (n : Nat) :
    Even n → G.isDiagonalIntegerLattice M → G.isDyadic p →
      1 < G.ramificationIndexAt p → S.globalRank M = n + 3 →
        S.IsNUniversalAt M p n → G.localAdjacentDefectsLarge M p
  sumOfSquares_rank (m : Nat) :
    S.globalRank (G.sumOfSquares m) = m
  sumOfSquares_localAdjacentDefectsLarge (m : Nat) (p : S.Place) :
    G.isDyadic p → G.localAdjacentDefectsLarge (G.sumOfSquares m) p
  sumOfSquaresLocalUniversality : G.SumOfSquaresLocalUniversalityLaws
  sumOfSquaresGlobalization : G.SumOfSquaresLocalGlobalLaws

namespace SectionEightLaws

variable {G : HeClassic2024GlobalData S}

/-- Compatibility endpoint for the local-to-global step in Theorem 1.9. -/
theorem sumOfSquares_local_to_global (H : G.SectionEightLaws)
    (m n : Nat) (hNotTotallyReal : G.notTotallyReal)
    (hRank : n + 3 ≤ m)
    (hLocal : ∀ p : S.Place,
      S.IsNUniversalAt (G.sumOfSquares m) p n) :
    S.IsGloballyNUniversal (G.sumOfSquares m) n :=
  H.sumOfSquaresGlobalization.sumOfSquares_local_to_global
    m n hNotTotallyReal hRank hLocal

/-- Compatibility endpoint for the finite-place analysis in Theorem 1.9. -/
theorem sumOfSquares_localUniversal_of_oddDiscriminant
    (H : G.SectionEightLaws) (m n : Nat) (hn : 1 ≤ n)
    (_hNotTotallyReal : G.notTotallyReal) (hRank : n + 3 ≤ m)
    (hOdd : G.discriminantOdd) :
    ∀ p : S.Place, S.IsNUniversalAt (G.sumOfSquares m) p n :=
  SumOfSquaresLocalUniversalityLaws.sumOfSquares_localUniversal_of_oddDiscriminant
    H.sumOfSquaresLocalUniversality m n hn hRank hOdd

/-- The first, stronger sentence of He (2024), Proposition 8.2. -/
theorem he2022ClassicProposition82_positive (H : G.SectionEightLaws)
    (M : S.GlobalLattice) (n : Nat) (_hn : 1 ≤ n)
    (hPositive : G.RepresentsAllPositiveDefiniteClassicAtRank M n) :
    ∀ p : S.Place, S.IsNUniversalAt M p n := by
  exact H.proposition82.he2022ClassicProposition82_positive M n hPositive

/-- He (2024), Proposition 8.2, for a lattice already known to be globally
classic `n`-universal.  The stronger positive-definite premise printed first
in the proposition is exposed by `he2022ClassicProposition82_positive`. -/
theorem he2022ClassicProposition82 (H : G.SectionEightLaws)
    (M : S.GlobalLattice) (p : S.Place) (n : Nat) (hn : 1 ≤ n)
    (hUniversal : S.IsGloballyNUniversal M n) :
    S.IsNUniversalAt M p n := by
  apply H.he2022ClassicProposition82_positive M n hn
  refine ⟨hUniversal.1, ?_⟩
  intro N hRank hIntegral hPositive
  exact hUniversal.2 N hRank hIntegral
    (H.positiveDefinite_admissible M N hPositive)

/-- The local assertion and conclusion of He (2024), Theorem 1.5 at one
dyadic prime, after localization has supplied the paper's hypotheses. -/
theorem he2022ClassicTheorem15_atPlace (H : G.SectionEightLaws)
    (M : S.GlobalLattice) (p : S.Place) (n : Nat)
    (hp : G.isDyadic p) (hn : 1 ≤ n)
    (hRank : n + 3 ≤ S.globalRank M)
    (hUniversal : S.IsNUniversalAt M p n)
    (hDefects : G.localAdjacentDefectsLarge M p) :
    G.ramificationIndexAt p = 1 :=
  H.theorem15_local M p n hp hn hRank hUniversal hDefects

/-- The final global sentence of He (2024), Theorem 1.5: if its local
hypotheses hold at every dyadic prime, then the field discriminant is odd. -/
theorem he2022ClassicTheorem15_discriminantOdd
    (H : G.SectionEightLaws) (M : S.GlobalLattice) (n : Nat)
    (hn : 1 ≤ n) (hRank : n + 3 ≤ S.globalRank M)
    (hUniversal : ∀ p : S.Place, G.isDyadic p → S.IsNUniversalAt M p n)
    (hDefects : ∀ p : S.Place,
      G.isDyadic p → G.localAdjacentDefectsLarge M p) :
    G.discriminantOdd := by
  apply H.discriminantRamification.discriminantOdd_of_unramified
  intro p hp
  exact H.he2022ClassicTheorem15_atPlace M p n hp hn hRank
    (hUniversal p hp) (hDefects p hp)

/-- The rank-independent contradiction at the end of He (2024), Theorem 1.7.
The omitted parity-dependent coefficient calculation is an explicit premise. -/
theorem he2022ClassicTheorem17_of_localAdjacentDefectsLarge
    (H : G.SectionEightLaws)
    (M : S.GlobalLattice) (n : Nat) (hn : 1 ≤ n)
    (hRank : S.globalRank M = n + 3)
    (hLocalDefects : ∀ p : S.Place,
      G.isDyadic p → 1 < G.ramificationIndexAt p →
        S.IsNUniversalAt M p n → G.localAdjacentDefectsLarge M p)
    (hDiscriminantEven : ¬ G.discriminantOdd) :
    ¬ S.IsGloballyNUniversal M n := by
  intro hUniversal
  obtain ⟨p, hpDyadic, hpNe⟩ :=
    DiscriminantRamificationLaws.exists_ramifiedDyadic_of_not_discriminantOdd
      H.discriminantRamification hDiscriminantEven
  have hpRamified : 1 < G.ramificationIndexAt p := by
    have hpPos := H.ramificationIndexAt_pos p hpDyadic
    omega
  have hLocal : S.IsNUniversalAt M p n :=
    H.he2022ClassicProposition82 M p n hn hUniversal
  have hDefects : G.localAdjacentDefectsLarge M p :=
    hLocalDefects p hpDyadic hpRamified hLocal
  have hpOne : G.ramificationIndexAt p = 1 :=
    H.he2022ClassicTheorem15_atPlace M p n hpDyadic hn (by omega)
      hLocal hDefects
  omega

/-- The even-rank scope now stated in v6 Theorem 1.7. The local coefficient
calculation remains an explicit package premise, not a concrete global proof. -/
theorem he2022ClassicTheorem17_even (H : G.SectionEightLaws)
    (M : S.GlobalLattice) (n : Nat) (hn : 2 ≤ n) (hnEven : Even n)
    (hRank : S.globalRank M = n + 3)
    (hDiagonal : G.isDiagonalIntegerLattice M)
    (hDiscriminantEven : ¬ G.discriminantOdd) :
    ¬ S.IsGloballyNUniversal M n := by
  apply H.he2022ClassicTheorem17_of_localAdjacentDefectsLarge M n
    (by omega) hRank _ hDiscriminantEven
  intro p hpDyadic hpRamified hLocal
  exact H.diagonal_localAdjacentDefectsLarge_of_universal_even
    M p n hnEven hDiagonal hpDyadic hpRamified hRank hLocal

/-- He (2024), Theorem 1.9 (the generalized sums-of-squares criterion),
with the paper's non-totally-real and stable-rank hypotheses explicit. -/
theorem he2022ClassicTheorem19 (H : G.SectionEightLaws)
    (m n : Nat) (hn : 1 ≤ n) (hRank : n + 3 ≤ m)
    (hNotTotallyReal : G.notTotallyReal) :
    S.IsGloballyNUniversal (G.sumOfSquares m) n ↔ G.discriminantOdd := by
  constructor
  · intro hUniversal
    apply H.discriminantRamification.discriminantOdd_of_unramified
    intro p hp
    have hLocal : S.IsNUniversalAt (G.sumOfSquares m) p n :=
      H.he2022ClassicProposition82 (G.sumOfSquares m) p n hn hUniversal
    apply H.he2022ClassicTheorem15_atPlace (G.sumOfSquares m) p n hp hn
    · rw [H.sumOfSquares_rank]
      exact hRank
    · exact hLocal
    · exact H.sumOfSquares_localAdjacentDefectsLarge m p hp
  · intro hOdd
    apply H.sumOfSquares_local_to_global m n hNotTotallyReal hRank
    exact H.sumOfSquares_localUniversal_of_oddDiscriminant m n
      hn hNotTotallyReal hRank hOdd

end SectionEightLaws

end HeClassic2024GlobalData

/-! ## Lemma 8.3 and Theorem 1.8 under a finite extension -/

/-- A selected ramified pair of dyadic places in a finite extension `E/K`,
together with scalar extension of global lattices. -/
structure HeClassic2024ExtensionData
    (Sbase : GlobalLocalLatticeSystem.{u, v, w})
    (Sextension : GlobalLocalLatticeSystem.{u', v', w'}) where
  baseChangeGlobal : Sbase.GlobalLattice → Sextension.GlobalLattice
  basePlace : Sbase.Place
  extensionPlace : Sextension.Place
  relativeRamificationIndex : Nat

namespace HeClassic2024ExtensionData

variable
  {Sbase : GlobalLocalLatticeSystem.{u, v, w}}
  {Sextension : GlobalLocalLatticeSystem.{u', v', w'}}

variable (X : HeClassic2024ExtensionData Sbase Sextension)

/-- The even-rank local scalar-extension obstruction sought by v6 Lemma 8.3.
Its concrete implementation requires localization, transport of the mapped
good BONG into the scalar-extension ambient, and the new carrier equality;
these are represented by this explicit field, not claimed as proved here. -/
structure Lemma83Laws : Prop where
  local_ramified_obstruction (L : Sbase.GlobalLattice) (n : Nat) :
    2 ≤ n → Even n → Sbase.globalRank L = n + 3 →
      1 < X.relativeRamificationIndex →
        Sbase.IsNUniversalAt L X.basePlace n →
          ¬ Sextension.IsNUniversalAt
            (X.baseChangeGlobal L) X.extensionPlace n

namespace Lemma83Laws

variable
  {X : HeClassic2024ExtensionData Sbase Sextension}

/-- The even-rank statement of v6 Lemma 8.3, with the chosen ramified pair
of dyadic places stored in `X`. Its local obstruction is an explicit premise. -/
theorem he2022ClassicLemma83_even (H : X.Lemma83Laws)
    (L : Sbase.GlobalLattice) (n : Nat)
    (hn : 2 ≤ n) (hEven : Even n)
    (hRank : Sbase.globalRank L = n + 3)
    (hRamified : 1 < X.relativeRamificationIndex)
    (hUniversal : Sbase.IsNUniversalAt L X.basePlace n) :
    ¬ Sextension.IsNUniversalAt
      (X.baseChangeGlobal L) X.extensionPlace n :=
  H.local_ramified_obstruction L n hn hEven hRank hRamified hUniversal

/-- The even-rank part of He (2024), Theorem 1.8.  Global universality on
either side is localized by Proposition 8.2, and the proved-scope part of
Lemma 8.3 supplies the contradiction at the selected ramified pair of
places. -/
theorem he2022ClassicTheorem18_even
    {Gbase : HeClassic2024GlobalData Sbase}
    {Gextension : HeClassic2024GlobalData Sextension}
    (H : X.Lemma83Laws)
    (Hbase : Gbase.SectionEightLaws)
    (Hextension : Gextension.SectionEightLaws)
    (L : Sbase.GlobalLattice) (n : Nat) (hn : 2 ≤ n) (hEven : Even n)
    (hRank : Sbase.globalRank L = n + 3)
    (hRamified : 1 < X.relativeRamificationIndex)
    (hUniversal : Sbase.IsGloballyNUniversal L n) :
    ¬ Sextension.IsGloballyNUniversal (X.baseChangeGlobal L) n := by
  have hBaseLocal : Sbase.IsNUniversalAt L X.basePlace n :=
    Hbase.he2022ClassicProposition82 L X.basePlace n (by omega) hUniversal
  have hNotExtensionLocal :
      ¬ Sextension.IsNUniversalAt
        (X.baseChangeGlobal L) X.extensionPlace n :=
    H.he2022ClassicLemma83_even L n hn hEven hRank hRamified hBaseLocal
  intro hExtensionUniversal
  exact hNotExtensionLocal
    (Hextension.he2022ClassicProposition82
      (X.baseChangeGlobal L) X.extensionPlace n (by omega)
      hExtensionUniversal)

end Lemma83Laws

end HeClassic2024ExtensionData

end Bong
