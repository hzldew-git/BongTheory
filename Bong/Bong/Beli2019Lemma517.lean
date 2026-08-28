/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma513
import Bong.Bong.Beli2019PrefixConsequences

/-!
# Beli (2019), Lemma 5.17

At a boundary in the direct Section 5.2 range where the two order sequences
have the same current entry, Lemma 5.17 proves two facts: the left alpha cap
is at most the right one, and every preceding order agrees.  The range
hypothesis is essential: after the distinguished block the accumulated
volume difference may already be two.  The prefix conclusion is exactly the
prefix part of Corollary 5.10.  Its remaining four-way trigger is recorded
separately, because it is selected by the surrounding Jordan-component case
split.

This file turns those statements into the common-prefix and minimum
simplifications used in the proof of condition 2.1(ii).  It does not assume
the representation theorem.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- The two conclusions of Lemma 5.17 at every equal-order boundary in the
direct reduced range. -/
structure Beli2019Lemma517Data
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (InReducedRange : RepresentationIndex (m + 1) (n + 1) → Prop) : Prop where
  alphaCap_le
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : InReducedRange i) :
    a.orderSequence.entryOrZero (i.val - 1) =
        b.orderSequence.entryOrZero (i.val - 1) →
      a.prefixAlphaCap i.val ≤ b.prefixAlphaCap i.val
  prefixAgreement
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : InReducedRange i) :
    a.orderSequence.entryOrZero (i.val - 1) =
        b.orderSequence.entryOrZero (i.val - 1) →
      a.orderSequence.PrefixAgreement b.orderSequence i.val

namespace Beli2019Lemma517Data

/-- In the equal-order case the minimum of the two caps is the left cap. -/
theorem min_prefixAlphaCap_eq_left
    {a : GoodBONG q L (m + 1)} {b : GoodBONG r M (n + 1)}
    {InReducedRange : RepresentationIndex (m + 1) (n + 1) → Prop}
    (D : Beli2019Lemma517Data a b InReducedRange)
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : InReducedRange i)
    (hcurrent : a.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val - 1)) :
    min (a.prefixAlphaCap i.val) (b.prefixAlphaCap i.val) =
      a.prefixAlphaCap i.val :=
  min_eq_left (D.alphaCap_le i hi hcurrent)

/-- A left-alpha estimate is the complete common-approximation bound in the
equal-order case of the proof following Lemma 5.17. -/
theorem commonBound_of_leftCap
    {a : GoodBONG q L (m + 1)} {b : GoodBONG r M (n + 1)}
    {InReducedRange : RepresentationIndex (m + 1) (n + 1) → Prop}
    (D : Beli2019Lemma517Data a b InReducedRange)
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : InReducedRange i)
    (hcurrent : a.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val - 1))
    (hbound : a.representationAlpha b i ≤ a.prefixAlphaCap i.val) :
    a.representationAlpha b i ≤
      min (a.prefixAlphaCap i.val) (b.prefixAlphaCap i.val) := by
  rw [D.min_prefixAlphaCap_eq_left i hi hcurrent]
  exact hbound

end Beli2019Lemma517Data

/-- The Corollary 5.10 trigger selected in the equal-order subcase following
Lemma 5.17. -/
structure Beli2019Lemma517PrefixData
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (InReducedRange : RepresentationIndex (m + 1) (n + 1) → Prop) : Prop
    extends Beli2019Lemma517Data a b InReducedRange where
  trigger
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : InReducedRange i) :
    a.orderSequence.entryOrZero (i.val - 1) =
        b.orderSequence.entryOrZero (i.val - 1) →
      BeliPrefixExtensionTrigger (ramificationIndex K : Int)
        a.orderSequence b.orderSequence i.val

namespace Beli2019Lemma517PrefixData

/-- Lemma 5.17(ii) and the surrounding case split supply precisely the full
hypothesis of Corollary 5.10. -/
theorem prefixExtensionHypothesis
    {a : GoodBONG q L (m + 1)} {b : GoodBONG r M (n + 1)}
    {InReducedRange : RepresentationIndex (m + 1) (n + 1) → Prop}
    (D : Beli2019Lemma517PrefixData a b InReducedRange)
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : InReducedRange i)
    (hcurrent : a.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val - 1)) :
    BeliPrefixExtensionHypothesis (ramificationIndex K : Int)
      a.orderSequence b.orderSequence i.val where
  agreement := D.prefixAgreement i hi hcurrent
  trigger := D.trigger i hi hcurrent

end Beli2019Lemma517PrefixData

/-- Geometric form of the equal-order conclusion: the good BONG of the
larger lattice may be chosen with the prescribed common ambient prefix. -/
theorem exists_goodBONG_with_ambientPrefix_of_lemma517
    [BONGStructuralLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q L (n + 1))
    (hLM : L ≤ M)
    {InReducedRange : RepresentationIndex (n + 1) (n + 1) → Prop}
    (D : Beli2019Lemma517PrefixData a b InReducedRange)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : InReducedRange i)
    (hcurrent : a.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val - 1)) :
    ∃ c : GoodBONG q M (n + 1),
      BONG.AmbientPrefixAgreement c.toBONG b.toBONG i.val :=
  a.exists_goodBONG_with_ambientPrefix b hLM
    (D.prefixExtensionHypothesis i hi hcurrent)

/-- The literal Corollary 5.10 step used in the paper after Lemma 5.17(ii).
Equality through the current order makes the `nextOrder` alternative
automatic one boundary earlier, so no additional profile trigger is needed
to prescribe the first `i - 1` ambient vectors. -/
theorem exists_goodBONG_with_previousAmbientPrefix_of_lemma517
    [BONGStructuralLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q L (n + 1))
    (hLM : L ≤ M)
    {InReducedRange : RepresentationIndex (n + 1) (n + 1) → Prop}
    (D : Beli2019Lemma517Data a b InReducedRange)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : InReducedRange i)
    (hcurrent : a.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val - 1)) :
    ∃ c : GoodBONG q M (n + 1),
      BONG.AmbientPrefixAgreement c.toBONG b.toBONG (i.val - 1) := by
  let p := i.val - 1
  have hp : p < n + 1 := by
    have := i.lt_large
    dsimp only [p]
    omega
  have hagreement :
      a.orderSequence.PrefixAgreement b.orderSequence p :=
    (D.prefixAgreement i hi hcurrent).mono (by
      dsimp only [p]
      omega)
  have htrigger : BeliPrefixExtensionTrigger
      (ramificationIndex K : Int) a.orderSequence b.orderSequence p :=
    BeliPrefixExtensionTrigger.nextOrder hp hp (by
      simpa only [p] using hcurrent)
  exact a.exists_goodBONG_with_ambientPrefix b hLM
    { agreement := hagreement, trigger := htrigger }

end BONG.GoodBONG

end Bong
