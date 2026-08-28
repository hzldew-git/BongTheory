/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma720Long

/-!
# Beli (2019), Lemma 7.20: preservation of the four representation conditions

This file assembles conditions 2.1(i), (ii), (iii'), and (iv) for each
normal form produced by Lemma 7.18. It also converts the revised central
condition back to the original condition using Lemma 2.16.
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
variable [Beli2009AlphaParityLaws.{u, v} K]
variable [laws : DyadicDiscriminantClassLaws K]

/-- The revised four-condition package in Lemma 7.20. -/
theorem Beli2019Lemma718NormalForm.representationConditionsPrime
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Beli2019Lemma718NormalForm a b R s)
    (hac : RepresentationConditions a c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    RepresentationConditionsPrime b c le_rfl := by
  exact ⟨D.representationOrderCondition a b c R s
      hac.orderCondition hnorm,
    D.representationDefectCondition a b c R s hac hnorm,
    D.centralRepresentationConditionsPrime a b c R s hac hnorm,
    D.longRepresentationConditions a b c R s hac⟩

/-- Lemma 7.20 in the original four-condition formulation. -/
theorem Beli2019Lemma718NormalForm.representationConditions
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Beli2019Lemma718NormalForm a b R s)
    (hac : RepresentationConditions a c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    RepresentationConditions b c le_rfl := by
  have hprime := D.representationConditionsPrime a b c R s hac hnorm
  have htriggers := b.beli2019Lemma216 c le_rfl
    hprime.orderCondition hprime.defectCondition
  exact (representationConditions_iff_prime b c le_rfl htriggers).mpr hprime

end BONG.GoodBONG

end Bong
