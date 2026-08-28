/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaCommonAdjunctionPrefixes
import Bong.Lattice.OmearaFundamentalScaleNormAlgebra
import Bong.Lattice.OrthogonalDecompositionDeterminant
import Bong.Dyadic.UnitsCongruentModuloAlgebra

/-!
# O'Meara 93:28 conditions under common adjunction

Adjoining one saturated Jordan splitting componentwise to both sides keeps
the boundary ideals and the explicit representation thresholds unchanged.
Corresponding prefix determinants acquire the same common factor, and every
prefix representation extends by the identity on the common prefix.
-/

namespace Bong

open Dyadic Module

namespace Lattice
namespace JordanDecomposition

universe u v w x z

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {X : Type x} [AddCommGroup X] [Module K X]
  {Z : Type z} [AddCommGroup Z] [Module K Z]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K X} {e : QuadraticSpace K Z}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K X}
  {t : Nat}

/-- The common adjunction has the same displayed scale orders as its
right-hand summand. -/
theorem commonAdjunctionJordan_scaleOrder_eq_right
    (P : JordanDecomposition q L (t + 2))
    (J : JordanDecomposition r M (t + 2))
    (F : SameFundamentalType P J) (hP : P.IsSaturated)
    (i : Fin (t + 2)) :
    (P.commonAdjunctionJordan J F hP).fundamentalScaleOrder i =
      J.fundamentalScaleOrder i := by
  unfold fundamentalScaleOrder
  rw [P.commonAdjunctionJordan_scaleGenerator J F hP]
  exact (F.scaleGenerator_order_eq_sameIndex i).symm

/-- The common adjunction has the same fundamental norm groups as its
right-hand summand. -/
theorem commonAdjunctionJordan_normGroup_eq_right
    (P : JordanDecomposition q L (t + 2))
    (J : JordanDecomposition r M (t + 2))
    (F : SameFundamentalType P J) (hP : P.IsSaturated)
    (i : Fin (t + 2)) :
    (P.commonAdjunctionJordan J F hP).fundamentalNormGroup i =
      J.fundamentalNormGroup i := by
  rw [P.commonAdjunctionJordan_fundamentalNormGroup J F hP]
  have h := F.normGroup_eq i
  rw [F.indexEquiv_apply_eq_self] at h
  exact h.symm

/-- The boundary ideals are unchanged by common adjunction. -/
theorem commonAdjunctionJordan_fundamentalIdeal_eq_right
    (P : JordanDecomposition q L (t + 2))
    (J : JordanDecomposition r M (t + 2))
    (F : SameFundamentalType P J) (hP : P.IsSaturated)
    (i : Fin (t + 1)) :
    (P.commonAdjunctionJordan J F hP).fundamentalIdeal i =
      J.fundamentalIdeal i :=
  fundamentalIdeal_eq_of_scaleOrder_normGroup_eq
    (P.commonAdjunctionJordan_scaleOrder_eq_right J F hP)
    (P.commonAdjunctionJordan_normGroup_eq_right J F hP) i

namespace FundamentalNormGeneratorChoice

/-- Reuse a coherent generator choice from the right-hand summand on the
common adjunction. -/
noncomputable def commonAdjunction
    {P : JordanDecomposition q L (t + 2)}
    {J : JordanDecomposition r M (t + 2)}
    (A : FundamentalNormGeneratorChoice J)
    (F : SameFundamentalType P J) (hP : P.IsSaturated) :
    FundamentalNormGeneratorChoice (P.commonAdjunctionJordan J F hP) where
  value := A.value
  spec i := by
    apply isNormGeneratorValue_of_normGroupSet_eq (A.spec i)
    · simpa only [fundamentalNormGroup] using
        (P.commonAdjunctionJordan_normGroup_eq_right J F hP i).symm
    · exact (P.commonAdjunctionJordan J F hP).exists_fundamentalNormGenerator i

@[simp]
theorem commonAdjunction_value
    {P : JordanDecomposition q L (t + 2)}
    {J : JordanDecomposition r M (t + 2)}
    (A : FundamentalNormGeneratorChoice J)
    (F : SameFundamentalType P J) (hP : P.IsSaturated)
    (i : Fin (t + 2)) :
    (A.commonAdjunction F hP).value i = A.value i :=
  rfl

end FundamentalNormGeneratorChoice

/-- The explicit threshold formed with a coherent choice is unchanged by
common adjunction. -/
theorem commonAdjunctionJordan_fourNormOverWeightIdealWith_eq_right
    (P : JordanDecomposition q L (t + 2))
    (J : JordanDecomposition r M (t + 2))
    (F : SameFundamentalType P J) (hP : P.IsSaturated)
    (A : FundamentalNormGeneratorChoice J) (i : Fin (t + 2)) :
    (P.commonAdjunctionJordan J F hP).fourNormOverWeightIdealWith
        (A.commonAdjunction F hP) i =
      J.fourNormOverWeightIdealWith A i :=
  fourNormOverWeightIdealWith_eq_of_scaleOrder_normGroup_eq
    (P.commonAdjunctionJordan_scaleOrder_eq_right J F hP)
    (P.commonAdjunctionJordan_normGroup_eq_right J F hP)
    A (A.commonAdjunction F hP) (fun _ => rfl) i

set_option maxHeartbeats 0 in
-- Determinants of dependent prefix products require basis normalization.
/-- A common-adjunction prefix determinant is the product of the two
original prefix determinant classes. -/
theorem unitSquareClass_commonAdjunction_prefixDeterminantUnit
    (P : JordanDecomposition q L (t + 2))
    (J : JordanDecomposition r M (t + 2))
    (F : SameFundamentalType P J) (hP : P.IsSaturated)
    (i : Fin (t + 1)) :
    unitSquareClass K
        ((P.commonAdjunctionJordan J F hP).prefixDeterminantUnit i) =
      unitSquareClass K (P.prefixDeterminantUnit i) *
        unitSquareClass K (J.prefixDeterminantUnit i) := by
  let hk : i.val + 1 ≤ t + 2 := by omega
  let f := P.commonAdjunctionPrefixGatherIsometry J F hP hk
  have hdet := determinantClass_eq_of_isometry f
  rw [determinantClass_orthogonalProduct] at hdet
  simpa only [prefixDeterminantUnit,
    QuadraticSublattice.refinedDeterminantUnit, determinantClass] using hdet

/-- A representation of corresponding prefixes extends by the identity on
the prefix of the common adjunction. -/
theorem commonAdjunctionPrefix_embedsInto
    {P : JordanDecomposition q L (t + 2)}
    {J : JordanDecomposition r M (t + 2)}
    {H : JordanDecomposition s N (t + 2)}
    (FPJ : SameFundamentalType P J)
    (FPH : SameFundamentalType P H)
    (hP : P.IsSaturated)
    {m : Nat} (hk : m + 1 ≤ t + 2)
    (e : QuadraticSpace K Z)
    (h : QuadraticSublattice.EmbedsIntoOrthogonalSum
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1))
      (H.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1)) e) :
    QuadraticSublattice.EmbedsIntoOrthogonalSum
      ((P.commonAdjunctionJordan J FPJ hP).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 1))
      ((P.commonAdjunctionJordan H FPH hP).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 1)) e := by
  rcases h with ⟨f⟩
  let sourceGather := P.commonAdjunctionPrefixGatherIsometry J FPJ hP hk
  let targetGather := P.commonAdjunctionPrefixGatherIsometry H FPH hP hk
  let commonPrefix :=
    P.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1)
  let sourcePrefix :=
    J.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1)
  let targetPrefix :=
    H.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1)
  let middle : QuadraticSpace.Representation
      (commonPrefix.space.orthogonalSum sourcePrefix.space)
      (commonPrefix.space.orthogonalSum (targetPrefix.space.orthogonalSum e)) :=
    (QuadraticSpace.Representation.refl commonPrefix.space).orthogonalSum f
  let targetReframe : QuadraticSpace.Isometry
      (commonPrefix.space.orthogonalSum (targetPrefix.space.orthogonalSum e))
      (((P.commonAdjunctionJordan H FPH hP).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 1)).space.orthogonalSum e) :=
    (QuadraticSpace.orthogonalSumAssoc
      commonPrefix.space targetPrefix.space e).symm |>.trans
        (targetGather.symm.toQuadraticSpaceIsometry.orthogonalSum
          (QuadraticSpace.Isometry.refl e))
  exact ⟨targetReframe.toRepresentation.trans
    (middle.trans sourceGather.toQuadraticSpaceIsometry.toRepresentation)⟩

/-- O'Meara 93:28(i) survives a common saturated adjunction. -/
theorem omeara9328ConditionI_commonAdjunction
    {P : JordanDecomposition q L (t + 2)}
    {J : JordanDecomposition r M (t + 2)}
    {H : JordanDecomposition s N (t + 2)}
    (FPJ : SameFundamentalType P J)
    (FPH : SameFundamentalType P H)
    (hP : P.IsSaturated)
    (hI : J.Omeara9328ConditionI H) :
    (P.commonAdjunctionJordan J FPJ hP).Omeara9328ConditionI
      (P.commonAdjunctionJordan H FPH hP) := by
  intro i
  rw [P.commonAdjunctionJordan_fundamentalIdeal_eq_right J FPJ hP]
  let dP : Kˣ := P.prefixDeterminantUnit i
  let dJ : Kˣ := J.prefixDeterminantUnit i
  let dH : Kˣ := H.prefixDeterminantUnit i
  let dPJ : Kˣ :=
    (P.commonAdjunctionJordan J FPJ hP).prefixDeterminantUnit i
  let dPH : Kˣ :=
    (P.commonAdjunctionJordan H FPH hP).prefixDeterminantUnit i
  have hsource : unitSquareClass K dPJ = unitSquareClass K (dP * dJ) := by
    rw [unitSquareClass_mul]
    exact P.unitSquareClass_commonAdjunction_prefixDeterminantUnit J FPJ hP i
  have htarget : unitSquareClass K dPH = unitSquareClass K (dP * dH) := by
    rw [unitSquareClass_mul]
    exact P.unitSquareClass_commonAdjunction_prefixDeterminantUnit H FPH hP i
  have hcommon : BONG.GoodBONG.UnitsCongruentModulo
      (dP * dH) (dP * dJ) (J.fundamentalIdeal i) :=
    (BONG.GoodBONG.unitsCongruentModulo_mul_left_iff
      dP dH dJ (J.fundamentalIdeal i)).2 (hI i)
  exact BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
    (dP * dH) dPH (dP * dJ) dPJ (J.fundamentalIdeal i)
    htarget.symm hsource.symm hcommon

/-- O'Meara 93:28(ii) survives a common saturated adjunction. -/
theorem omeara9328ConditionIIWith_commonAdjunction
    {P : JordanDecomposition q L (t + 2)}
    {J : JordanDecomposition r M (t + 2)}
    {H : JordanDecomposition s N (t + 2)}
    (FPJ : SameFundamentalType P J)
    (FPH : SameFundamentalType P H)
    (A : FundamentalNormGeneratorChoice J)
    (hP : P.IsSaturated)
    (hII : J.Omeara9328ConditionIIWith H A) :
    (P.commonAdjunctionJordan J FPJ hP).Omeara9328ConditionIIWith
      (P.commonAdjunctionJordan H FPH hP) (A.commonAdjunction FPJ hP) := by
  intro i htrigger
  rw [P.commonAdjunctionJordan_fundamentalIdeal_eq_right J FPJ hP,
    P.commonAdjunctionJordan_fourNormOverWeightIdealWith_eq_right
      J FPJ hP A] at htrigger
  exact commonAdjunctionPrefix_embedsInto FPJ FPH hP (by omega)
    (QuadraticSpace.scaledLine (A.value (boundaryRightIndex i)))
    (hII i htrigger)

/-- O'Meara 93:28(iii) survives a common saturated adjunction. -/
theorem omeara9328ConditionIIIWith_commonAdjunction
    {P : JordanDecomposition q L (t + 2)}
    {J : JordanDecomposition r M (t + 2)}
    {H : JordanDecomposition s N (t + 2)}
    (FPJ : SameFundamentalType P J)
    (FPH : SameFundamentalType P H)
    (A : FundamentalNormGeneratorChoice J)
    (hP : P.IsSaturated)
    (hIII : J.Omeara9328ConditionIIIWith H A) :
    (P.commonAdjunctionJordan J FPJ hP).Omeara9328ConditionIIIWith
      (P.commonAdjunctionJordan H FPH hP) (A.commonAdjunction FPJ hP) := by
  intro i htrigger
  rw [P.commonAdjunctionJordan_fundamentalIdeal_eq_right J FPJ hP,
    P.commonAdjunctionJordan_fourNormOverWeightIdealWith_eq_right
      J FPJ hP A] at htrigger
  exact commonAdjunctionPrefix_embedsInto FPJ FPH hP (by omega)
    (QuadraticSpace.scaledLine (A.value (boundaryLeftIndex i)))
    (hIII i htrigger)

/-- The complete condition package survives a common saturated adjunction. -/
theorem omeara9328ConditionsWith_commonAdjunction
    {P : JordanDecomposition q L (t + 2)}
    {J : JordanDecomposition r M (t + 2)}
    {H : JordanDecomposition s N (t + 2)}
    (FPJ : SameFundamentalType P J)
    (FPH : SameFundamentalType P H)
    (A : FundamentalNormGeneratorChoice J)
    (hP : P.IsSaturated)
    (h : J.Omeara9328ConditionsWith H A) :
    (P.commonAdjunctionJordan J FPJ hP).Omeara9328ConditionsWith
      (P.commonAdjunctionJordan H FPH hP) (A.commonAdjunction FPJ hP) :=
  ⟨omeara9328ConditionI_commonAdjunction FPJ FPH hP h.1,
    omeara9328ConditionIIWith_commonAdjunction FPJ FPH A hP h.2.1,
    omeara9328ConditionIIIWith_commonAdjunction FPJ FPH A hP h.2.2⟩

end JordanDecomposition
end Lattice

end Bong
