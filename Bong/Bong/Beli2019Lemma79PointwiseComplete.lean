/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma67TypeICanonical
import Bong.Bong.Beli2019Lemma79TypeIPointwiseComplete
import Bong.Bong.Beli2019Lemma79TypeIIPointwiseCompleteLocal
import Bong.Bong.Beli2019Lemma79TypeIIIPointwiseCompleteLocal

/-!
# Beli (2019), Lemma 7.9(ii): the three-type assembly

The construction of `M'` in Section 7 normalizes the first unequal
coordinate to zero.  Type III additionally retains the strict initial-gap
hypothesis used in the nonoverlapping branch.

`Lemma79NormalizedClassification` records exactly the normalization supplied
by Section 7: the first unequal coordinate is zero.  In type III it also keeps
the strict initial-gap hypothesis.  The paper does **not** assert that the last
unequal coordinate is the final coordinate.  The stronger
`Lemma79FullSpanClassification` remains as a compatibility interface.  The
main theorem now works with the paper's normalized classification and permits
an arbitrary common suffix.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The three Lemma 6.7 profiles with exactly the normalization data supplied
by Section 7's construction of `M'`. -/
inductive Lemma79NormalizedClassification
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2)) : Prop
  | typeI (data : Lemma67TypeI a b)
      (first_eq_zero : data.profile.first = 0)
  | typeII (data : Lemma67TypeII a b)
      (first_eq_zero : data.outer.first = 0)
  | typeIII (data : Lemma67TypeIII a b)
      (first_eq_zero : data.outer.first = 0)
      (initial_gap : -(2 * (ramificationIndex K : Int)) <
        a.orderGap ⟨0, by
          have hbound := data.outer.transition.firstTwo_le_rank
          rw [data.adjacent] at hbound
          omega⟩)

/-- The special case in which the type-II or type-III difference profile
continues through the final coordinate.  This is useful for the endpoint
proofs already formalized below, but is strictly stronger than the hypotheses
of Lemma 7.9. -/
inductive Lemma79FullSpanClassification
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2)) : Prop
  | typeI (data : Lemma67TypeI a b)
      (first_eq_zero : data.profile.first = 0)
  | typeII (data : Lemma67TypeII a b)
      (first_eq_zero : data.outer.first = 0)
      (last_eq_final : data.outer.last = n + 1)
  | typeIII (data : Lemma67TypeIII a b)
      (first_eq_zero : data.outer.first = 0)
      (last_eq_final : data.outer.last = n + 1)
      (initial_gap : -(2 * (ramificationIndex K : Int)) <
        a.orderGap ⟨0, by
          have hbound := data.outer.transition.firstTwo_le_rank
          rw [data.adjacent] at hbound
          omega⟩)

/-- Forget the full-span restriction while retaining the normalization used
in the paper. -/
theorem Lemma79FullSpanClassification.toNormalized
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    (D : Lemma79FullSpanClassification a b) :
    Lemma79NormalizedClassification a b := by
  cases D with
  | typeI E hfirst => exact .typeI E hfirst
  | typeII E hfirst _ => exact .typeII E hfirst
  | typeIII E hfirst _ hinitial => exact .typeIII E hfirst hinitial

/-- Forgetting the Section 7 normalization recovers Lemma 6.7's exhaustive
three-type classification. -/
theorem Lemma79NormalizedClassification.toLemma67Classification
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    (D : Lemma79NormalizedClassification a b) :
    Lemma67Classification a b := by
  cases D with
  | typeI E _ => exact .typeI E
  | typeII E _ => exact .typeII E
  | typeIII E _ _ => exact .typeIII E

/-- Strict containment of norm ideals makes coordinate zero unequal, hence
any first-difference witness is necessarily zero. -/
theorem firstDifference_eq_zero_of_normIdeal_lt
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    {first : Nat}
    (D : BeliOrderSequence.IsFirstDifferenceAt
      a.orderSequence b.orderSequence first)
    (hnorm : Lattice.normIdeal q M < Lattice.normIdeal q L) :
    first = 0 := by
  have hzeroOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    b.toBONG hnorm
  change a.order (0 : Fin (n + 2)) + 1 ≤
    b.order (0 : Fin (n + 2)) at hzeroOrder
  have hzeroNe : a.orderSequence.entryOrZero 0 ≠
      b.orderSequence.entryOrZero 0 := by
    intro hzeroEq
    have hzeroEq' : a.order (0 : Fin (n + 2)) =
        b.order (0 : Fin (n + 2)) := by
      calc
        a.order (0 : Fin (n + 2)) =
            a.orderSequence.entryOrZero 0 := by
          rw [a.orderSequence.entryOrZero_of_lt (by omega)]
          rfl
        _ = b.orderSequence.entryOrZero 0 := hzeroEq
        _ = b.order (0 : Fin (n + 2)) := by
          rw [b.orderSequence.entryOrZero_of_lt (by omega)]
          rfl
    omega
  by_contra hfirst
  exact hzeroNe (D.before 0 (Nat.pos_of_ne_zero hfirst))

/-- The actual normalized Lemma 6.7 classification used in Lemma 7.9.
Unlike the full-span interface, this theorem derives the first-index
normalization from the strict norm-ideal hypothesis and places no restriction
on the last unequal coordinate. -/
theorem beli2019Lemma79_normalizedClassification
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnorm : Lattice.normIdeal q M < Lattice.normIdeal q L)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by omega⟩) :
    Lemma79NormalizedClassification a b := by
  cases beli2019Lemma67 a b horder hdefect htotal with
  | typeI E =>
      exact .typeI E
        (firstDifference_eq_zero_of_normIdeal_lt
          a b E.profile.firstDifference hnorm)
  | typeII E =>
      exact .typeII E
        (firstDifference_eq_zero_of_normIdeal_lt
          a b E.outer.firstDifference hnorm)
  | typeIII E =>
      exact .typeIII E
        (firstDifference_eq_zero_of_normIdeal_lt
          a b E.outer.firstDifference hnorm)
        (by simpa using hinitial)

/-- Lemma 7.9(ii): under the exact normalized Lemma 6.7 classification
supplied by Section 7, every ordinary boundary of the BONG of `N` satisfies
Condition 2.1(ii) relative to the BONG of `M`. -/
theorem beli2019Lemma79_ii_of_normalizedClassification
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma79NormalizedClassification a b)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hcentralAB : a.CentralRepresentationConditions b)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hcentralAC : a.CentralRepresentationConditions c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2)) :
    b.RepresentationDefectCondition c := by
  intro i
  cases D with
  | typeI E hfirst =>
      rcases lemma67TypeICanonicalData a b E hfirst with ⟨C⟩
      exact beli2019Lemma79_ii_typeI_pointwise_complete
        a b c E C hfirst horderAB hdefectAB hcentralAB horderAC
          hdefectAC hcentralAC horderBC hnorm htotal i
  | typeII E hfirst =>
      exact beli2019Lemma79_ii_typeII_pointwise_complete_local
        a b c E hfirst horderAB horderAC horderBC hdefectAB
          hdefectAC htotal hnorm i
  | typeIII E hfirst hinitial =>
      exact beli2019Lemma79_ii_typeIII_pointwise_complete_local
        a b c E hfirst horderAB horderAC horderBC hdefectAB
          hdefectAC htotal hinitial hnorm i

/-- Compatibility wrapper for the former full-span interface. -/
theorem beli2019Lemma79_ii_of_fullSpanClassification
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma79FullSpanClassification a b)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hcentralAB : a.CentralRepresentationConditions b)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hcentralAC : a.CentralRepresentationConditions c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2)) :
    b.RepresentationDefectCondition c := by
  exact beli2019Lemma79_ii_of_normalizedClassification
    a b c D.toNormalized horderAB hdefectAB hcentralAB horderAC
      hdefectAC hcentralAC horderBC hnorm htotal

end BONG.GoodBONG

end Bong
