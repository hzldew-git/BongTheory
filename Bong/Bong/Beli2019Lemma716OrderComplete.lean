/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716TypeIIGeometry
import Bong.Bong.Beli2019Lemma716OrderCondition
import Bong.Bong.Beli2019Lemma716OrderFailure
import Bong.Bong.Beli2019Lemma716ExceptionalRepresentation

/-!
# Beli (2019), Lemma 7.16: condition 2.1(i)

This module closes the order-condition part of Lemma 7.16.  Failure at an
exceptional coordinate produces the rigid profile computed in the paper.
Condition (iii') for the original representation supplies the corresponding
prefix representation, and the type-I or type-II geometric obstruction rules
that profile out.  The elementary ranges then assemble the full condition.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

variable [Beli2006AlphaLaws.{u, v} K]
variable [laws : DyadicDiscriminantClassLaws K]
variable [DyadicUnramifiedNormLaws K]
variable [HilbertSymbolLaws K]
variable [DyadicAlternatingEndpointTowerRepresentationLaws K]

/-- Complete proof of condition 2.1(i) in the type-I branch of Lemma 7.16. -/
theorem lemma716_typeI_orderCondition
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hdiscriminant : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hI : Lemma714IsTypeI a R s)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j) :
    b.RepresentationOrderCondition c le_rfl := by
  have hleft : Beli2019Lemma716OrderClause b c
      ⟨s - 2, by
        have := D.le_rank
        omega⟩ := by
    by_contra hfail
    have P := a.lemma716_typeI_left_failureProfile b c R s D hfirst
      hsecond hnorm hvalues hfail
    have hrep := a.lemma716_typeI_failureProfile_prefixRepresents_all c
      R s D hfirst hsecond hthird hac hI P
    exact a.lemma716_typeI_failureProfile_false c R s D hfirst hthird
      hdiscriminant P hrep
  have hright : Beli2019Lemma716OrderClause b c
      ⟨s - 1, by
        have := D.le_rank
        omega⟩ := by
    by_contra hfail
    have P := a.lemma716_typeI_right_failureProfile b c R s D hfirst
      hsecond hnorm hvalues hfail
    have hrep := a.lemma716_typeI_failureProfile_prefixRepresents_all c
      R s D hfirst hsecond hthird hac hI P
    exact a.lemma716_typeI_failureProfile_false c R s D hfirst hthird
      hdiscriminant P hrep
  exact a.lemma716_typeI_orderCondition_of_exception_clauses b c R s D
    hfirst hthird hnorm hac.orderCondition hvalues horders hleft hright

/-- Complete proof of condition 2.1(i) in the type-II branch of Lemma 7.16. -/
theorem lemma716_typeII_orderCondition
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hdiscriminant : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hII : Lemma714IsTypeII a R s) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) ε η j)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j) :
    b.RepresentationOrderCondition c le_rfl := by
  have hexception : Beli2019Lemma716OrderClause b c
      ⟨s - 1, by
        have := D.le_rank
        omega⟩ := by
    by_contra hfail
    have P := a.lemma716_typeII_failureProfile b c R s D hfirst hnorm hII
      ε η hεUnit hηUnit hvalues hfail
    have hrep := a.lemma716_typeII_failureProfile_prefixRepresents c R s D
      hfirst hsecond hthird hac hII P
    exact a.lemma716_typeII_failureProfile_false c R s D hfirst hsecond
      hthird hdiscriminant hII P hrep
  exact a.lemma716_typeII_orderCondition_of_exception_clause b c R s D
    hfirst hthird hnorm hac.orderCondition hII ε η hεUnit hηUnit hvalues
      horders hexception

end BONG.GoodBONG

end Bong
