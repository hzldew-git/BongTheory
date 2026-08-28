/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralRegions
import Bong.Bong.Beli2019Lemma79CentralTypeIRightComplete
import Bong.Bong.Beli2019Lemma79CentralTypeIIRight
import Bong.Bong.Beli2019Lemma79CentralTypeIIIRight

/-!
# Beli (2019), Lemma 7.9(iii): the complete difference prefix

This file assembles cases 1, 2, 3, 5, 6, 7, 8, and 9 of the printed proof.
The type-III middle interval is empty, so the nine constructors of
`Lemma79CentralRegion` reduce to eight proof branches.  The common boundary
and common suffix (cases 4 and 10) are assembled separately.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 10000000 in
-- The proof elaborates all normalized profiles and their finite-index regions.
/-- All direct-or-certificate witnesses required on the finite difference
prefix in Lemma 7.9(iii). -/
theorem Lemma79NormalizedClassification.differencePrefixCentralWitnesses
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    (D : Lemma79NormalizedClassification a b)
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2)) :
    Lemma79DifferencePrefixCentralWitnesses a b c D := by
  refine ⟨?_⟩
  intro i hprefix htrigger
  rcases hprefix with ⟨last, hlast, hiLast⟩
  cases D with
  | typeI E hfirst =>
      have hlastEq : last = E.profile.last :=
        hlast.eq E.profile.lastDifference
      have hiProfileLast : i.val ≤ E.profile.last := by omega
      rcases a.lemma67TypeICanonicalData b E hfirst with ⟨C⟩
      by_cases hearly : i.val ≤ C.leftSwitch
      · exact lemma79CentralWitness_typeIEarly
          a b c E C hfirst horderBC hdefectBC hnorm i hearly htrigger
      · by_cases hmiddle : i.val ≤ C.rightSwitch
        · exact lemma79CentralWitness_typeIMiddle
            a b c E C hfirst hab hac horderBC hdefectBC i (by omega)
              hmiddle htrigger
        · exact lemma79CentralWitness_typeIRight
            a b c E C hfirst hab hac horderBC hdefectBC i (by omega)
              hiProfileLast htrigger
  | typeII E hfirst =>
      have hlastEq : last = E.outer.last :=
        hlast.eq E.outer.lastDifference
      have hiProfileLast : i.val ≤ E.outer.last := by omega
      by_cases hearly : i.val ≤ E.outer.transition.lastZero + 1
      · exact lemma79CentralWitness_typeIIEarly
          a b c E hfirst hdefectBC hnorm i hearly htrigger
      · by_cases hmiddle : i.val < E.outer.transition.firstTwo
        · exact lemma79CentralWitness_typeIIMiddle
            a b c E hfirst hdefectBC hnorm i (by omega) hmiddle htrigger
        · exact lemma79CentralWitness_typeIIRight
            a b c E hfirst hab htotal hdefectBC hnorm i (by omega)
              hiProfileLast htrigger
  | typeIII E hfirst hinitial =>
      have hlastEq : last = E.outer.last :=
        hlast.eq E.outer.lastDifference
      have hiProfileLast : i.val ≤ E.outer.last := by omega
      by_cases hearly : i.val ≤ E.outer.transition.lastZero + 1
      · exact lemma79CentralWitness_typeIIIEarly
          a b c E hfirst hab.orderCondition hab.defectCondition htotal
            hinitial hdefectBC hnorm i hearly htrigger
      · have hright : E.outer.transition.firstTwo ≤ i.val := by
          rw [E.adjacent]
          omega
        exact lemma79CentralWitness_typeIIIRight
          a b c E hfirst hab htotal hinitial hdefectBC hnorm i hright
            hiProfileLast htrigger

end BONG.GoodBONG

end Bong
