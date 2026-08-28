/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourComplete
import Bong.Bong.Beli2019Lemma93TailCentral

/-!
# Beli (2019), Section 4: the essential boundary forced by condition (iii)

Lemma 2.13 makes the paper index `i` essential for the outer pair.  This
file identifies that index with the right endpoint of the preceding ordinary
boundary and the left endpoint of the current one, then exposes both halves
of Lemma 4.2 in the exact form used in the proof of 2.1(iii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  {L M N : Lattice K V} {n : Nat}

/-- The exact local hypotheses used by Section 4.  The central and long
representation fields of `RepresentationConditions` play no role in Lemmas
4.2--4.5; recording only conditions 2.1(i)--(ii) also makes reverse-dual
transport faithful to the paper. -/
structure SectionFourLocalConditions
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1)) : Prop where
  habOrder : a.RepresentationOrderCondition b le_rfl
  habDefect : a.RepresentationDefectCondition b
  hbcOrder : b.RepresentationOrderCondition c le_rfl
  hbcDefect : b.RepresentationDefectCondition c

namespace SectionFourLocalConditions

/-- Every pair of full representation-condition packages supplies the local
Section 4 interface. -/
def ofRepresentationConditions
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl) :
    SectionFourLocalConditions a b c :=
  ⟨hab.orderCondition, hab.defectCondition,
    hbc.orderCondition, hbc.defectCondition⟩

end SectionFourLocalConditions

/-- The essential index from Lemma 2.13 is the next endpoint of the
preceding representation boundary. -/
theorem isNextEssential_previous_of_centralAlphaTrigger
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i) :
    a.IsNextEssential c i.previous := by
  have hessential := a.isEssentialFor_of_centralAlphaTrigger c i htrigger
  simpa only [IsNextEssential, nextEssentialIndex,
    CentralRepresentationIndex.previous] using hessential

/-- The same essential index is the current endpoint of the following
ordinary representation boundary. -/
theorem isCurrentEssential_current_of_centralAlphaTrigger
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i) :
    a.IsCurrentEssential c (i.current i.lt_large.le) := by
  have hessential := a.isEssentialFor_of_centralAlphaTrigger c i htrigger
  simpa only [IsCurrentEssential, currentEssentialIndex,
    CentralRepresentationIndex.current] using hessential

/-- Lemma 4.2(i) at the preceding boundary of an active condition-(iii)
index, retaining its direct/fallback distinction. -/
theorem sectionFourPreviousBounds_of_centralAlphaTrigger
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hlocal : SectionFourLocalConditions a b c)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i) :
    (a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex i.previous) →
        a.representationAlpha c i.previous ≤
            a.representationAlpha b i.previous ∧
          a.representationAlpha c i.previous ≤
            b.representationAlpha c i.previous) ∧
      (¬a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex i.previous) →
        ∃ hnext : i.previous.val + 1 < n + 1,
          a.representationAlpha c i.previous ≤
            a.nextFallbackBound b i.previous hnext) := by
  have hkey := a.sectionFourKeyLemmaBounds b c
    hlocal.habOrder hlocal.habDefect
    hlocal.hbcOrder hlocal.hbcDefect
  exact hkey.next i.previous
    (a.isNextEssential_previous_of_centralAlphaTrigger c i htrigger)

/-- Lemma 4.2(ii) at the current boundary of an active condition-(iii)
index, again retaining the paper's two exhaustive branches. -/
theorem sectionFourCurrentBounds_of_centralAlphaTrigger
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hlocal : SectionFourLocalConditions a b c)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i) :
    (a.KeyLemmaRightDirectTrigger b c
          (currentEssentialIndex (i.current i.lt_large.le)) →
        a.representationAlpha c (i.current i.lt_large.le) ≤
            a.representationAlpha b (i.current i.lt_large.le) ∧
          a.representationAlpha c (i.current i.lt_large.le) ≤
            b.representationAlpha c (i.current i.lt_large.le)) ∧
      (¬a.KeyLemmaRightDirectTrigger b c
          (currentEssentialIndex (i.current i.lt_large.le)) →
        ∃ hprev : 1 < (i.current i.lt_large.le).val,
          a.representationAlpha c (i.current i.lt_large.le) ≤
            a.currentFallbackBound b c
              (i.current i.lt_large.le) hprev) := by
  have hkey := a.sectionFourKeyLemmaBounds b c
    hlocal.habOrder hlocal.habDefect
    hlocal.hbcOrder hlocal.hbcDefect
  exact hkey.current (i.current i.lt_large.le)
    (a.isCurrentEssential_current_of_centralAlphaTrigger c i htrigger)

end BONG.GoodBONG

end Bong
