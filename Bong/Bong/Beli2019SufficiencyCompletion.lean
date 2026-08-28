/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019AmbientEnvelope
import Bong.Bong.Beli2019DeepCompletionRepresentation
import Bong.Bong.Beli2019RankCompletionSufficiency
import Bong.Bong.GoodExistence

/-!
# Beli (2019), Lemmas 2.20--2.21 in the sufficiency proof

For strict unequal rank, enlarge the target lattice enough to contain the
ambient image of the source lattice, choose a good BONG of that envelope, and
adjoin a uniformly deep orthogonal complement.  The numerical completion
theorem transfers all four conditions to the resulting equal-rank pair.  An
equal-rank sufficiency theorem then represents the completion, whose initial
block represents the original source lattice.
-/

namespace Bong

open Dyadic

universe u v w

/-- Lemmas 2.20--2.21 reduce strict unequal-rank sufficiency to the already
proved equal-rank theorem.  The `equalRank` argument is a theorem parameter,
not a typeclass or an axiom; the concrete Sections 7--9 theorem is substituted
for it in `Beli2019SufficiencyComplete`. -/
theorem beli2019_strictRank_sufficiency_of_equalRank
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [goodV : BONGGoodExistenceLaws.{u, v} K]
    [deepVW : GoodBONGDeepIntegralExtensionLaws.{u, v, w} K]
    (a : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (hRank : n < m) (ambient : q.Represents r)
    (conditions : RepresentationConditions a b hRank.le)
    (equalRank : ∀ {C : Lattice K V}
      (c : BONG.GoodBONG q C (m + 1)),
      RepresentationConditions a c (Nat.le_refl m) →
        Lattice.Represents q q L C) :
    Lattice.Represents q r L M := by
  rcases ambient with ⟨f⟩
  let E : Lattice K V := Lattice.representationEnvelope f L M
  let fE : Lattice.Representation r q M E :=
    Lattice.Representation.ofAmbientToEnvelope f L M
  rcases exists_good_bong q E with ⟨dRaw⟩
  let d : BONG.GoodBONG q E (m + 1) :=
    dRaw.castLength a.toBONG.length_eq_finrank.symm
  obtain ⟨D⟩ := GoodBONGDeepIntegralExtensionLaws.extension
    d b hRank fE a.rankCompletionTailOrderBound
      (a.representationAlphaValue b
        (BONG.GoodBONG.rankCompletionBoundaryIndex hRank))
  have completedConditions : RepresentationConditions a D.completedBONG
      (Nat.le_refl m) :=
    a.representationConditions_toSameRank_of_prefixAgreement
      (alphaV := alphaV) (alphaW := alphaW) (alphaU := alphaV)
      D.prefixAgreement hRank D.tailOrder D.boundaryAlpha.le conditions
  have hcompleted : Lattice.Represents q q L D.completedLattice :=
    equalRank D.completedBONG completedConditions
  exact hcompleted.trans D.completed_represents_original

end Bong
