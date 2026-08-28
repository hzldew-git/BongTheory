/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralTypeIMiddleEven

/-!
# Beli (2019), Lemma 7.9(iii): completion of the type-I middle region

The odd parity class is case 2 and supplies the first Lemma 1.5
certificate.  The even parity class is case 6 and cannot satisfy the
central trigger.  Together they discharge the entire interval between the
two canonical type-I switches.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The complete witness family on the type-I middle interval. -/
theorem lemma79CentralWitness_typeIMiddle
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : C.leftSwitch < i.val) (hright : i.val ≤ C.rightSwitch)
    (htriggerBC : b.centralAlphaTrigger c i) :
    Lemma79CentralWitness a b c i := by
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · exact False.elim
      (lemma79Central_typeIMiddle_even_not_trigger
        a b c D C hfirst horderBC hdefectBC i hleft hright hiEven
          htriggerBC)
  · exact .viaCertificate
      (lemma79CentralCertificate_typeIMiddle_odd
        a b c D C hfirst hab hac horderBC hdefectBC i hleft hright
          hiOdd htriggerBC)

end BONG.GoodBONG

end Bong
