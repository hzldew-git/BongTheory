/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixFirstParity
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityTypeIIAssembly
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityTypeIIIAssembly

/-!
# Beli (2019), Lemma 7.9(ii), case 6: complete assembly

The source and target prefixes in the case-6 parity class have opposite
order parity.  Comparing both with the third BONG therefore gives exactly
the two alternatives settled by the first- and second-parity arguments.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Lemma 7.9(ii), case 6, for a type-II transition interval. -/
theorem beli2019Lemma79_ii_typeII_caseSix
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 <= i.val)
    (hbeforeLast : i.val < D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hprefix := beli2019Lemma79_typeII_caseSix_prefix_opposite
    a b D hfirst i hright hbeforeLast.le heven
  rcases caseSix_comparisonPrefix_parity_dichotomy a b c i hprefix with
      hfirstParity | hsecondParity
  · exact beli2019Lemma79_typeII_caseSix_firstParity
      a b c D hfirst hlast hab hac hdefectAB hdefectAC htotal hnorm
        i hright hbeforeLast heven hfirstParity.1 hfirstParity.2
  · exact beli2019Lemma79_typeII_caseSix_secondParity
      a b c D hfirst hnorm i hright hbeforeLast.le heven hsecondParity.1

/-- Lemma 7.9(ii), case 6, for a nonoverlapping type-III transition. -/
theorem beli2019Lemma79_ii_typeIII_caseSix
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnotOverlap : a.orderGap
      (Fin.mk D.outer.transition.lastZero (by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega)) ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap (Fin.mk 0 (by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega)))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 <= i.val)
    (hbeforeLast : i.val < D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hprefix := beli2019Lemma79_typeIII_caseSix_prefix_opposite
    a b D hfirst hdefectAB hnotOverlap i hright hbeforeLast.le heven
  rcases caseSix_comparisonPrefix_parity_dichotomy a b c i hprefix with
      hfirstParity | hsecondParity
  · exact beli2019Lemma79_typeIII_caseSix_firstParity
      a b c D hfirst hlast hab hac hdefectAB hdefectAC htotal
        hnotOverlap hinitial hnorm i hright hbeforeLast heven
          hfirstParity.1 hfirstParity.2
  · exact beli2019Lemma79_typeIII_caseSix_secondParity
      a b c D hfirst hlast hab hdefectAB htotal hnotOverlap hinitial
        hnorm i hright hbeforeLast.le heven hsecondParity.1

end BONG.GoodBONG

end Bong
