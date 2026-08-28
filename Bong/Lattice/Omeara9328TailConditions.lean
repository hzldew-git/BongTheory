/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.UnitsCongruentModuloAlgebra
import Bong.Lattice.Omeara9328GeneratorChoice
import Bong.Lattice.OmearaHeadTailPrefix
import Bong.Lattice.OrthogonalDecompositionDeterminant
import Bong.QuadraticSpace.OrthogonalSumCancellation

/-!
# Passing O'Meara 93:28 conditions to aligned tails

Once the first Jordan components have been integrally aligned, the three
semantic conditions of 93:28 pass to the exact suffixes.  Condition (i) uses
multiplicativity and cancellation of the common head determinant.  Conditions
(ii) and (iii) use cancellation of the common head quadratic summand.
-/

namespace Bong

open Dyadic Module

namespace QuadraticSpace

universe u v w z

variable {K : Type u} [Field K]
  {U : Type v} [AddCommGroup U] [Module K U]
  {V : Type w} [AddCommGroup V] [Module K V]
  {W : Type z} [AddCommGroup W] [Module K W]

/-- Reassociate three quadratic spaces. -/
noncomputable def orthogonalSumAssoc
    (p : QuadraticSpace K U) (q : QuadraticSpace K V)
    (r : QuadraticSpace K W) :
    Isometry ((p.orthogonalSum q).orthogonalSum r)
      (p.orthogonalSum (q.orthogonalSum r)) where
  toLinearEquiv := LinearEquiv.prodAssoc K U V W
  map_bilin := by
    intro x y
    change p.bilin x.1.1 y.1.1 +
        (q.bilin x.1.2 y.1.2 + r.bilin x.2 y.2) =
      (p.bilin x.1.1 y.1.1 + q.bilin x.1.2 y.1.2) +
        r.bilin x.2 y.2
    ring

end QuadraticSpace

namespace Lattice

universe u v w z

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {Z : Type z} [AddCommGroup Z] [Module K Z]
  [FiniteDimensional K Z]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K Z}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

namespace JordanDecomposition

/-- The orthogonal decomposition underlying the recursively defined Jordan
tail is literally the exact suffix decomposition. -/
@[simp]
theorem tail_toOrthogonalDecomposition
    (J : JordanDecomposition q L (n + 1)) :
    J.tail.toOrthogonalDecomposition =
      J.toOrthogonalDecomposition.tailDecomposition :=
  rfl

/-- Prefix sublattices formed after taking the Jordan tail agree literally
with prefixes of the exact suffix decomposition. -/
@[simp]
theorem tail_prefixQuadraticSublattice
    (J : JordanDecomposition q L (n + 1)) (k : Nat) :
    J.tail.toOrthogonalDecomposition.prefixQuadraticSublattice k =
      J.toOrthogonalDecomposition.tailDecomposition.prefixQuadraticSublattice k :=
  rfl

end JordanDecomposition

namespace OrthogonalDecomposition

/-- The refined determinant class of a full prefix is the product of its
head determinant class and the determinant class of the corresponding tail
prefix. -/
theorem unitSquareClass_prefixDeterminantUnit_split
    (D : OrthogonalDecomposition q L (n + 2)) (k : Nat) :
    unitSquareClass K
        (D.prefixQuadraticSublattice (k + 1)).refinedDeterminantUnit =
      unitSquareClass K
        ((D.component 0).refinedDeterminantUnit *
          (D.tailDecomposition.prefixQuadraticSublattice k).refinedDeterminantUnit) := by
  have hdet := determinantClass_eq_of_isometry
    (D.headTailPrefixLatticeIsometry k)
  rw [determinantClass_orthogonalProduct] at hdet
  change
    unitSquareClass K
        (D.prefixQuadraticSublattice (k + 1)).refinedDeterminantUnit =
      unitSquareClass K (D.component 0).refinedDeterminantUnit *
        unitSquareClass K
          (D.tailDecomposition.prefixQuadraticSublattice k).refinedDeterminantUnit
  rw [← unitSquareClass_mul]
  exact hdet.symm

/-- Cancel aligned head spaces from a representation of corresponding full
prefixes, leaving a representation of the tail prefixes. -/
theorem tailPrefix_embedsInto_of_head
    (D : OrthogonalDecomposition q L (n + 2))
    (E : OrthogonalDecomposition r M (n + 2))
    (head : Isometry (D.component 0).space (E.component 0).space
      (D.component 0).lattice (E.component 0).lattice)
    (k : Nat)
    (h : QuadraticSublattice.EmbedsIntoOrthogonalSum
      (D.prefixQuadraticSublattice (k + 1))
      (E.prefixQuadraticSublattice (k + 1)) s) :
    QuadraticSublattice.EmbedsIntoOrthogonalSum
      (D.tailDecomposition.prefixQuadraticSublattice k)
      (E.tailDecomposition.prefixQuadraticSublattice k) s := by
  letI : Module.Finite K (D.component 0).carrier :=
    (D.component 0).lattice.moduleFinite
  letI : Module.Finite K (E.component 0).carrier :=
    (E.component 0).lattice.moduleFinite
  letI : Module.Finite K
      (D.tailDecomposition.prefixQuadraticSublattice k).carrier :=
    (D.tailDecomposition.prefixQuadraticSublattice k).lattice.moduleFinite
  letI : Module.Finite K
      (E.tailDecomposition.prefixQuadraticSublattice k).carrier :=
    (E.tailDecomposition.prefixQuadraticSublattice k).lattice.moduleFinite
  rcases h with ⟨f⟩
  let sourceSplit := (D.headTailPrefixLatticeIsometry k).toQuadraticSpaceIsometry
  let targetSplit := (E.headTailPrefixLatticeIsometry k).toQuadraticSpaceIsometry
  let targetReframe :=
    (targetSplit.symm.orthogonalSum (QuadraticSpace.Isometry.refl s)).trans
      (QuadraticSpace.orthogonalSumAssoc
        (E.component 0).space
        (E.tailDecomposition.prefixQuadraticSublattice k).space s)
  have total :
      ((E.component 0).space.orthogonalSum
        ((E.tailDecomposition.prefixQuadraticSublattice k).space.orthogonalSum s)).Represents
      ((D.component 0).space.orthogonalSum
        (D.tailDecomposition.prefixQuadraticSublattice k).space) :=
    ⟨targetReframe.toRepresentation.trans
      (f.trans sourceSplit.toRepresentation)⟩
  exact QuadraticSpace.orthogonalSumCancelRepresents
    (D.component 0).space (E.component 0).space
    (D.tailDecomposition.prefixQuadraticSublattice k).space
    ((E.tailDecomposition.prefixQuadraticSublattice k).space.orthogonalSum s)
    head.toQuadraticSpaceIsometry total

end OrthogonalDecomposition

namespace JordanDecomposition

open BONG.GoodBONG

variable {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

/-- The determinant congruence 93:28(i) passes to aligned saturated tails. -/
theorem omeara9328ConditionI_tail
    (hJ : J.IsSaturated)
    (head : Isometry (J.component 0).space (H.component 0).space
      (J.component 0).lattice (H.component 0).lattice)
    (hI : J.Omeara9328ConditionI H) :
    J.tail.Omeara9328ConditionI H.tail := by
  intro i
  rw [IsSaturated.tail_fundamentalIdeal_eq hJ i]
  let dJ := (J.component 0).refinedDeterminantUnit
  let dH := (H.component 0).refinedDeterminantUnit
  let pJ := J.tail.prefixDeterminantUnit i
  let pH := H.tail.prefixDeterminantUnit i
  have hsplitJ : unitSquareClass K (J.prefixDeterminantUnit i.succ) =
      unitSquareClass K (dJ * pJ) := by
    dsimp only [prefixDeterminantUnit, dJ, pJ]
    rw [JordanDecomposition.tail_prefixQuadraticSublattice]
    simpa only [Fin.val_succ, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      J.toOrthogonalDecomposition.unitSquareClass_prefixDeterminantUnit_split
        (i.val + 1)
  have hsplitH : unitSquareClass K (H.prefixDeterminantUnit i.succ) =
      unitSquareClass K (dH * pH) := by
    dsimp only [prefixDeterminantUnit, dH, pH]
    rw [JordanDecomposition.tail_prefixQuadraticSublattice]
    simpa only [Fin.val_succ, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      H.toOrthogonalDecomposition.unitSquareClass_prefixDeterminantUnit_split
        (i.val + 1)
  have hhead : unitSquareClass K dH = unitSquareClass K dJ := by
    change determinantClass (H.component 0).space (H.component 0).lattice =
      determinantClass (J.component 0).space (J.component 0).lattice
    exact (determinantClass_eq_of_isometry head).symm
  have hproduct : UnitsCongruentModulo (dH * pH) (dJ * pJ)
      (J.fundamentalIdeal i.succ) :=
    BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
      (H.prefixDeterminantUnit i.succ) (dH * pH)
      (J.prefixDeterminantUnit i.succ) (dJ * pJ)
      (J.fundamentalIdeal i.succ) hsplitH hsplitJ (hI i.succ)
  have hleft : unitSquareClass K (dH * pH) =
      unitSquareClass K (dJ * pH) := by
    rw [unitSquareClass_mul, unitSquareClass_mul, hhead]
  have hcommon : UnitsCongruentModulo (dJ * pH) (dJ * pJ)
      (J.fundamentalIdeal i.succ) :=
    BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
      (dH * pH) (dJ * pH) (dJ * pJ) (dJ * pJ)
      (J.fundamentalIdeal i.succ) hleft rfl hproduct
  exact (BONG.GoodBONG.unitsCongruentModulo_mul_left_iff dJ pH pJ
    (J.fundamentalIdeal i.succ)).mp hcommon

/-- Condition 93:28(ii), with coherent generators, passes to aligned tails. -/
theorem omeara9328ConditionIIWith_tail
    (hJ : J.IsSaturated)
    (head : Isometry (J.component 0).space (H.component 0).space
      (J.component 0).lattice (H.component 0).lattice)
    (A : FundamentalNormGeneratorChoice J)
    (hII : J.Omeara9328ConditionIIWith H A) :
    J.tail.Omeara9328ConditionIIWith H.tail (A.tail hJ) := by
  intro i htrigger
  rw [IsSaturated.tail_fundamentalIdeal_eq hJ i,
    IsSaturated.tail_fourNormOverWeightIdealWith_eq hJ A,
    boundaryRightIndex_succ] at htrigger
  have hfull := hII i.succ htrigger
  have htail := J.toOrthogonalDecomposition.tailPrefix_embedsInto_of_head
    H.toOrthogonalDecomposition head (i.val + 1) hfull
  simpa only [JordanDecomposition.tail_prefixQuadraticSublattice,
    Fin.val_succ, Nat.add_assoc,
    FundamentalNormGeneratorChoice.tail_value,
    boundaryRightIndex_succ] using htail

/-- Condition 93:28(iii), with coherent generators, passes to aligned tails. -/
theorem omeara9328ConditionIIIWith_tail
    (hJ : J.IsSaturated)
    (head : Isometry (J.component 0).space (H.component 0).space
      (J.component 0).lattice (H.component 0).lattice)
    (A : FundamentalNormGeneratorChoice J)
    (hIII : J.Omeara9328ConditionIIIWith H A) :
    J.tail.Omeara9328ConditionIIIWith H.tail (A.tail hJ) := by
  intro i htrigger
  rw [IsSaturated.tail_fundamentalIdeal_eq hJ i,
    IsSaturated.tail_fourNormOverWeightIdealWith_eq hJ A,
    boundaryLeftIndex_succ] at htrigger
  have hfull := hIII i.succ htrigger
  have htail := J.toOrthogonalDecomposition.tailPrefix_embedsInto_of_head
    H.toOrthogonalDecomposition head (i.val + 1) hfull
  simpa only [JordanDecomposition.tail_prefixQuadraticSublattice,
    Fin.val_succ, Nat.add_assoc,
    FundamentalNormGeneratorChoice.tail_value,
    boundaryLeftIndex_succ] using htail

/-- All three coherent 93:28 conditions pass to aligned saturated tails. -/
theorem omeara9328ConditionsWith_tail
    (hJ : J.IsSaturated)
    (head : Isometry (J.component 0).space (H.component 0).space
      (J.component 0).lattice (H.component 0).lattice)
    (A : FundamentalNormGeneratorChoice J)
    (h : J.Omeara9328ConditionsWith H A) :
    J.tail.Omeara9328ConditionsWith H.tail (A.tail hJ) :=
  ⟨omeara9328ConditionI_tail hJ head h.1,
    omeara9328ConditionIIWith_tail hJ head A h.2.1,
    omeara9328ConditionIIIWith_tail hJ head A h.2.2⟩

end JordanDecomposition

end Lattice

end Bong
