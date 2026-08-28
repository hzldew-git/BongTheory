/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.JordanReverseDualGeneratorChoice
import Bong.Lattice.JordanReverseDualDeterminant
import Bong.Lattice.JordanReverseDualPrefixes
import Bong.Lattice.OrthogonalDecompositionDeterminant
import Bong.Lattice.OrthogonalDecompositionPrefixSuffix
import Bong.Lattice.Omeara9328PrefixTransport
import Bong.QuadraticSpace.OrthogonalComplementRepresentation

/-!
# Exchanging O'Meara 93:28(ii) and (iii) by reverse duality

The ideal triggers are exchanged by 93:24.  At the geometric level, a
reverse-dual prefix is the complementary original suffix.  A representation
of the swapped suffixes therefore yields the desired representation of the
original prefixes after adjoining the full ambient isometry and applying
Witt cancellation.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {t : Nat}

/-- Condition 93:28(i) for the reverse-dual pair implies condition (i) for
the original pair.  Reverse-dual prefix determinants are inverse suffix
determinants; equality of the whole determinant classes then cancels the
common suffix factor. -/
theorem omeara9328ConditionI_of_reverseDual_conditionI
    {J : JordanDecomposition q L (t + 1)}
    {H : JordanDecomposition r M (t + 1)}
    (f : Lattice.Isometry q r L M)
    (hI : J.reverseDual.Omeara9328ConditionI H.reverseDual) :
    J.Omeara9328ConditionI H := by
  intro j
  let JP := J.toOrthogonalDecomposition
    |>.prefixQuadraticSublattice (j.val + 1)
  let HP := H.toOrthogonalDecomposition
    |>.prefixQuadraticSublattice (j.val + 1)
  let JS := J.toOrthogonalDecomposition
    |>.suffixQuadraticSublattice (j.val + 1)
  let HS := H.toOrthogonalDecomposition
    |>.suffixQuadraticSublattice (j.val + 1)
  let dJP : Kˣ := J.prefixDeterminantUnit j
  let dHP : Kˣ := H.prefixDeterminantUnit j
  let dJS : Kˣ := determinantUnit JS.space JS.lattice
  let dHS : Kˣ := determinantUnit HS.space HS.lattice
  have hrev := hI (Fin.rev j)
  rw [J.reverseDual_fundamentalIdeal, Fin.rev_rev] at hrev
  have hx : unitSquareClass K
        (H.reverseDual.prefixDeterminantUnit (Fin.rev j)) =
      unitSquareClass K dHS⁻¹ := by
    change determinantClass
        (H.reverseDual.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice ((Fin.rev j).val + 1)).space
        (H.reverseDual.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice ((Fin.rev j).val + 1)).lattice =
      (determinantClass HS.space HS.lattice)⁻¹
    exact H.reverseDualBoundaryPrefix_determinantClass j
  have hy : unitSquareClass K
        (J.reverseDual.prefixDeterminantUnit (Fin.rev j)) =
      unitSquareClass K dJS⁻¹ := by
    change determinantClass
        (J.reverseDual.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice ((Fin.rev j).val + 1)).space
        (J.reverseDual.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice ((Fin.rev j).val + 1)).lattice =
      (determinantClass JS.space JS.lattice)⁻¹
    exact J.reverseDualBoundaryPrefix_determinantClass j
  have hinv : BONG.GoodBONG.UnitsCongruentModulo
      dHS⁻¹ dJS⁻¹ (J.fundamentalIdeal j) :=
    BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
      (H.reverseDual.prefixDeterminantUnit (Fin.rev j)) dHS⁻¹
      (J.reverseDual.prefixDeterminantUnit (Fin.rev j)) dJS⁻¹
      (J.fundamentalIdeal j) hx hy hrev
  have hsuffix : BONG.GoodBONG.UnitsCongruentModulo
      dJS dHS (J.fundamentalIdeal j) :=
    (BONG.GoodBONG.unitsCongruentModulo_inv_swap_iff
      dHS dJS (J.fundamentalIdeal j)).1 hinv
  have hsplitJ : unitSquareClass K (dJP * dJS) =
      determinantClass q L := by
    rw [unitSquareClass_mul]
    change determinantClass JP.space JP.lattice *
      determinantClass JS.space JS.lattice = determinantClass q L
    have h := determinantClass_eq_of_isometry
      (J.toOrthogonalDecomposition.prefixSuffixLatticeIsometry
        (j.val + 1))
    rw [determinantClass_orthogonalProduct] at h
    exact h
  have hsplitH : unitSquareClass K (dHP * dHS) =
      determinantClass r M := by
    rw [unitSquareClass_mul]
    change determinantClass HP.space HP.lattice *
      determinantClass HS.space HS.lattice = determinantClass r M
    have h := determinantClass_eq_of_isometry
      (H.toOrthogonalDecomposition.prefixSuffixLatticeIsometry
        (j.val + 1))
    rw [determinantClass_orthogonalProduct] at h
    exact h
  have hwhole : unitSquareClass K (dJP * dJS) =
      unitSquareClass K (dHP * dHS) :=
    hsplitJ.trans ((determinantClass_eq_of_isometry f).trans hsplitH.symm)
  have hproduct : BONG.GoodBONG.UnitsCongruentModulo
      (dJP * dJS) (dJP * dHS) (J.fundamentalIdeal j) :=
    (BONG.GoodBONG.unitsCongruentModulo_mul_left_iff
      dJP dJS dHS (J.fundamentalIdeal j)).2 hsuffix
  have hreplaced : BONG.GoodBONG.UnitsCongruentModulo
      (dHP * dHS) (dJP * dHS) (J.fundamentalIdeal j) :=
    BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
      (dJP * dJS) (dHP * dHS) (dJP * dHS) (dJP * dHS)
      (J.fundamentalIdeal j) hwhole rfl hproduct
  have hcommon : BONG.GoodBONG.UnitsCongruentModulo
      (dHS * dHP) (dHS * dJP) (J.fundamentalIdeal j) := by
    simpa only [mul_comm] using hreplaced
  exact (BONG.GoodBONG.unitsCongruentModulo_mul_left_iff
    dHS dHP dJP (J.fundamentalIdeal j)).1 hcommon

/-- Condition 93:28(ii) for the swapped reverse-dual pair implies condition
93:28(iii) for the original pair. -/
theorem omeara9328ConditionIIIWith_of_reverseDual_conditionIIWith
    {J : JordanDecomposition q L (t + 1)}
    {H : JordanDecomposition r M (t + 1)}
    (ambient : q.IsIsometric r)
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J)
    (hII : H.reverseDual.Omeara9328ConditionIIWith J.reverseDual
      ((A.ofSameFundamentalType F).reverseDual)) :
    J.Omeara9328ConditionIIIWith H A := by
  intro j htrigger
  let B : FundamentalNormGeneratorChoice H := A.ofSameFundamentalType F
  let i : Fin t := Fin.rev j
  have htriggerDual :
      H.reverseDual.fundamentalIdeal i <
        H.reverseDual.fourNormOverWeightIdealWith B.reverseDual
          (boundaryRightIndex i) := by
    rw [H.reverseDual_fundamentalIdeal,
      H.reverseDual_fourNormOverWeightIdealWith,
      rev_boundaryRightIndex, Fin.rev_rev,
      F.fundamentalIdeal_eq j,
      F.fourNormOverWeightIdealWith_eq A (boundaryLeftIndex j)]
    exact htrigger
  have hdual := hII i htriggerDual
  let sourceDual :=
    H.reverseDualBoundaryPrefixSpaceIsometry j
  let targetDual :=
    J.reverseDualBoundaryPrefixSpaceIsometry j
  let lineDual :=
    H.reverseDualGeneratorLineIsometry B (boundaryRightIndex i)
  have hlineIndex :
      Fin.rev (boundaryRightIndex i) = boundaryLeftIndex j := by
    simp only [i, rev_boundaryRightIndex, Fin.rev_rev]
  let lineIdentify : QuadraticSpace.Isometry
      (QuadraticSpace.scaledLine
        (B.reverseDual.value (boundaryRightIndex i)))
      (QuadraticSpace.scaledLine (A.value (boundaryLeftIndex j))) := by
    rw [← FundamentalNormGeneratorChoice.ofSameFundamentalType_value
      A F (boundaryLeftIndex j), ← hlineIndex]
    exact lineDual
  have suffixRepresentation :
      QuadraticSpace.EmbedsInto
        (H.toOrthogonalDecomposition
          |>.suffixQuadraticSublattice (j.val + 1)).space
        ((J.toOrthogonalDecomposition
          |>.suffixQuadraticSublattice (j.val + 1)).space.orthogonalSum
          (QuadraticSpace.scaledLine (A.value (boundaryLeftIndex j)))) := by
    rcases hdual with ⟨f⟩
    exact ⟨(targetDual.orthogonalSum lineIdentify).toRepresentation.trans
      (f.trans sourceDual.symm.toRepresentation)⟩
  let sourceSplit :=
    J.toOrthogonalDecomposition.prefixSuffixLatticeIsometry (j.val + 1)
  let targetSplit :=
    H.toOrthogonalDecomposition.prefixSuffixLatticeIsometry (j.val + 1)
  let total : QuadraticSpace.Isometry
      ((J.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (j.val + 1)).space.orthogonalSum
        (J.toOrthogonalDecomposition
          |>.suffixQuadraticSublattice (j.val + 1)).space)
      ((H.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (j.val + 1)).space.orthogonalSum
        (H.toOrthogonalDecomposition
          |>.suffixQuadraticSublattice (j.val + 1)).space) :=
    sourceSplit.toQuadraticSpaceIsometry.trans <|
      (Classical.choice ambient).trans
        targetSplit.symm.toQuadraticSpaceIsometry
  letI : Module.Finite K
      (J.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (j.val + 1)).carrier :=
    (J.toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (j.val + 1)).lattice.moduleFinite
  letI : Module.Finite K
      (J.toOrthogonalDecomposition
        |>.suffixQuadraticSublattice (j.val + 1)).carrier :=
    (J.toOrthogonalDecomposition
      |>.suffixQuadraticSublattice (j.val + 1)).lattice.moduleFinite
  letI : Module.Finite K
      (H.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (j.val + 1)).carrier :=
    (H.toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (j.val + 1)).lattice.moduleFinite
  letI : Module.Finite K
      (H.toOrthogonalDecomposition
        |>.suffixQuadraticSublattice (j.val + 1)).carrier :=
    (H.toOrthogonalDecomposition
      |>.suffixQuadraticSublattice (j.val + 1)).lattice.moduleFinite
  exact QuadraticSpace.embedsInto_first_of_embedsInto_second
    total suffixRepresentation

end Lattice.JordanDecomposition

end Bong
