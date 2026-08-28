/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716TypeISMinusTwoCentral

/-!
# Beli (2019), Lemma 7.16(iii'): the type-II boundary `i = s - 1`

Lemmas 2.16 and 2.13 turn the revised trigger into essentiality of the
zero-based boundary `s - 2`.  The endpoint-profile argument already used for
condition (ii) then shows that both length-`s - 2` prefixes are alternating
endpoint towers at scale `R + 1`.  The constructed coefficient at the next
position has the same order.  The unary-extension endpoint-tower theorem is
therefore exactly the representation asserted in the paper.
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
variable [DyadicDiscriminantClassLaws K]
variable [DyadicAlternatingEndpointTowerRepresentationLaws K]

/-- Two rigid endpoint towers of the same length and scale, with one extra
target line at that scale, give the codimension-one representation used in
the type-II branch. -/
theorem lemma716_endpointTower_unaryExtension_prefixRepresents
    (b : GoodBONG q M (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (pairs : Nat) (hpairs : 0 < pairs)
    (hInterior : 2 * pairs < n + 3)
    (Ptarget : Beli2019Lemma716TypeIIFailureProfile b R (2 * pairs)
      (by omega) hInterior)
    (Pcomparison : Beli2019Lemma716TypeIIFailureProfile c R (2 * pairs)
      (by omega) hInterior)
    (hextraOrder : b.order ⟨2 * pairs, by omega⟩ = R + 1) :
    DiagonalRepresents
      (c.prefixValues (2 * pairs) (Nat.le_of_lt hInterior))
      (b.prefixValues (2 * pairs + 1) (by omega)) := by
  let target : Fin (2 * pairs) → Kˣ :=
    b.prefixValueUnits (2 * pairs) (Nat.le_of_lt hInterior)
  let comparison : Fin (2 * pairs) → Kˣ :=
    c.prefixValueUnits (2 * pairs) (Nat.le_of_lt hInterior)
  let extraIndex : Fin (n + 3) := ⟨2 * pairs, by omega⟩
  let extra : Kˣ := b.valueUnit extraIndex
  have htargetClasses : AlternatingEndpointPairClasses target := by
    simpa only [target] using
      b.lemma716_typeIIFailureProfile_pairClasses R pairs hpairs
        hInterior Ptarget
  have hcomparisonClasses : AlternatingEndpointPairClasses comparison := by
    simpa only [comparison] using
      c.lemma716_typeIIFailureProfile_pairClasses R pairs hpairs
        hInterior Pcomparison
  have hextra : ordUnit K extra = R + 1 := by
    calc
      ordUnit K extra = b.order extraIndex := by
        exact (b.toBONG.order_eq_ordUnit extraIndex).symm
      _ = R + 1 := by simpa only [extraIndex] using hextraOrder
  have htargetOrders : ∀ t : Fin pairs,
      ordUnit K (target ⟨2 * t.val, by omega⟩) = ordUnit K extra := by
    intro t
    calc
      ordUnit K (target ⟨2 * t.val, by omega⟩) = R + 1 := by
        simpa only [target] using
          b.lemma716_typeIIFailureProfile_leadingOrders R pairs hpairs
            hInterior Ptarget t
      _ = ordUnit K extra := hextra.symm
  have hcomparisonOrders : ∀ t : Fin pairs,
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) = ordUnit K extra := by
    intro t
    calc
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) = R + 1 := by
        simpa only [comparison] using
          c.lemma716_typeIIFailureProfile_leadingOrders R pairs hpairs
            hInterior Pcomparison t
      _ = ordUnit K extra := hextra.symm
  have hrep := alternatingEndpointTower_representationInUnaryExtension
    target comparison extra htargetClasses hcomparisonClasses
      htargetOrders hcomparisonOrders
  have hcomparisonCoefficients : diagonalUnitCoefficients comparison =
      c.prefixValues (2 * pairs) (Nat.le_of_lt hInterior) := by
    simpa only [comparison, diagonalUnitCoefficients_prefixValueUnits]
  have htargetCoefficients :
      diagonalUnitCoefficients (Fin.snoc target extra) =
        b.prefixValues (2 * pairs + 1) (by omega) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [target, extra, extraIndex, diagonalUnitCoefficients,
        prefixValues, GoodBONG.valueUnit, GoodBONG.value]
    · simp [target, diagonalUnitCoefficients, prefixValues,
        prefixValueUnits, GoodBONG.valueUnit, GoodBONG.value]
  rwa [hcomparisonCoefficients, htargetCoefficients] at hrep

/-- Condition (iii') at the type-II boundary with paper index `s - 1`. -/
theorem lemma716_typeII_sMinusOne_centralRepresentationAt
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hII : Lemma714IsTypeII a R s) (epsilon eta : Kˣ)
    (hepsilonUnit : IsValuationUnit K (epsilon : K))
    (hetaUnit : IsValuationUnit K (eta : K))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) epsilon eta j)
    (horder : b.RepresentationOrderCondition c le_rfl)
    (hdefect : b.RepresentationDefectCondition c)
    (hsFour : 4 ≤ s)
    (htrigger : b.centralDefectTrigger c
      { val := s - 1
        one_lt := by omega
        lt_large := by have := D.le_rank; omega
        le_small_succ := by have := D.le_rank; omega }) :
    DiagonalRepresents
      (c.prefixValues (s - 2) (by have := D.le_rank; omega))
      (b.prefixValues (s - 1) (by have := D.le_rank; omega)) := by
  let i : CentralRepresentationIndex (n + 3) (n + 3) :=
    { val := s - 1
      one_lt := by omega
      lt_large := by have := D.le_rank; omega
      le_small_succ := by have := D.le_rank; omega }
  have halpha : b.centralAlphaTrigger c i :=
    ((b.beli2019Lemma216 c le_rfl horder hdefect) i).mpr (by
      simpa only [i] using htrigger)
  have hessentialRaw :=
    b.isEssentialFor_of_centralAlphaTrigger c i halpha
  have hessential : b.IsEssentialFor c ⟨s - 2, by
      have := D.le_rank
      omega⟩ := by
    have hindex : (⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : Fin (n + 3)) =
        ⟨s - 2, by have := D.le_rank; omega⟩ := by
      apply Fin.ext
      dsimp only [i]
      change (s - 1) - 1 = s - 2
      omega
    rw [hindex] at hessentialRaw
    exact hessentialRaw
  have PtargetRaw := a.lemma716_typeII_sMinusTwo_sourceProfile
    b R s D hthird hII epsilon eta hvalues hsFour
  have PcomparisonRaw :=
    a.lemma716_typeII_sMinusTwo_comparisonProfile_of_essential
      b c R s D hfirst hnorm hII epsilon eta hepsilonUnit hetaUnit
        hvalues hsFour hessential
  rcases D.even with ⟨d, hd⟩
  let pairs := d - 1
  have hpairs : 0 < pairs := by
    dsimp only [pairs]
    omega
  have hlength : 2 * pairs = s - 2 := by
    dsimp only [pairs]
    omega
  have hInterior : 2 * pairs < n + 3 := by
    rw [hlength]
    have := D.le_rank
    omega
  have Ptarget : Beli2019Lemma716TypeIIFailureProfile b R (2 * pairs)
      (by omega) hInterior := by
    simpa only [hlength] using PtargetRaw
  have Pcomparison : Beli2019Lemma716TypeIIFailureProfile c R (2 * pairs)
      (by omega) hInterior := by
    simpa only [hlength] using PcomparisonRaw
  have hextraOrder : b.order ⟨2 * pairs, by omega⟩ = R + 1 := by
    have hboundary := a.lemma716_typeII_leftBoundary_order_eq
      b R s D hII epsilon eta hepsilonUnit hetaUnit hvalues
    have hindex : (⟨2 * pairs, by omega⟩ : Fin (n + 3)) =
        ⟨s - 2, by have := D.le_rank; omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      rw [hlength]
    rw [hindex]
    exact hboundary
  have hrep := b.lemma716_endpointTower_unaryExtension_prefixRepresents
    c R pairs hpairs hInterior Ptarget Pcomparison hextraOrder
  exact prefixRepresents_cast c b hlength (by omega) hrep

end BONG.GoodBONG

end Bong
