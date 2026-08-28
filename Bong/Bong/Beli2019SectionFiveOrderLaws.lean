/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrimeChainDecoration
import Bong.Bong.Beli2019AlmostJordanWeakUnaryShiftEntries

/-!
# Beli (2019), Section 5.4: concrete order-law instance

The common-complement construction of Lemma 5.1 and the weak Jordan-profile
calculation give the order certificate for every literal index-uniformizer
inclusion.  Weak profiles include both endpoint-amalgamation cases mentioned
at the end of Section 5.4.

Only Beli (2003), Lemma 4.7 remains as an input: it identifies the order
sequence of a good BONG with the alternating profile of a Jordan splitting.
The defect and representation-valued parts of Sections 5--6 are not used.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- The complete Section 5.4 order datum constructed from Lemma 5.1,
including rank one, rank two, and endpoint scale collisions. -/
theorem sectionFiveOrderData
    [BeliLemma47Laws.{u, v} K]
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (inclusion : Beli2019IndexPInclusion q M N) :
    Beli2019SectionFiveOrderData a b where
  certificate :=
    (Lattice.beli2019Lemma51Data q M N inclusion).weakAllRanks_orderCertificate
      a b

end BONG.GoodBONG

/-- Beli (2019), Section 5.4, discharged by the explicit weak-profile
calculation rather than by the complete Section 5 law package. -/
noncomputable instance beli2019SectionFiveOrderLaws
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [BeliLemma47Laws.{u, v} K] :
    Beli2019SectionFiveOrderLaws.{u, v} K where
  data a b inclusion := a.sectionFiveOrderData b inclusion

end Bong
