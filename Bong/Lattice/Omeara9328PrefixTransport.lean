/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.UnitsCongruentModuloAlgebra
import Bong.Lattice.OmearaFundamentalScaleNormAlgebra

/-!
# Transport of O'Meara 93:28 along prefix isometries

O'Meara's three conditions are invariant when the source splitting is
replaced by one of the same fundamental type and all corresponding proper
source prefixes are integrally isometric; the target splitting may likewise
be replaced along integral prefix isometries.  This is the precise transport
interface needed after an explicit stabilization or saturation construction.

Equality of fundamental type alone is deliberately not used as a substitute
for the prefix isometries: conditions 93:28(ii) and (iii) contain genuine
quadratic-space representation assertions.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w x y

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {X : Type x} [AddCommGroup X] [Module K X]
  {Y : Type y} [AddCommGroup Y] [Module K Y]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {q' : QuadraticSpace K X} {r' : QuadraticSpace K Y}
  {L : Lattice K V} {M : Lattice K W}
  {L' : Lattice K X} {M' : Lattice K Y}
  {n : Nat}

/-- Integral isometries between all corresponding proper prefixes of two
Jordan decompositions. -/
structure ProperPrefixIsometryFamily
    (J : JordanDecomposition q L (n + 1))
    (H : JordanDecomposition r M (n + 1)) where
  isometry : (i : Fin n) →
    Isometry
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice
        (i.val + 1)).space
      (H.toOrthogonalDecomposition.prefixQuadraticSublattice
        (i.val + 1)).space
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice
        (i.val + 1)).lattice
      (H.toOrthogonalDecomposition.prefixQuadraticSublattice
        (i.val + 1)).lattice

namespace ProperPrefixIsometryFamily

variable {J : JordanDecomposition q L (n + 1)}
  {H : JordanDecomposition r M (n + 1)}
  {T : JordanDecomposition q' L' (n + 1)}

/-- Reflexive prefix-isometry family. -/
noncomputable def refl (J : JordanDecomposition q L (n + 1)) :
    ProperPrefixIsometryFamily J J where
  isometry := fun _ ↦ Isometry.refl _ _

/-- Reverse every prefix isometry. -/
noncomputable def symm (P : ProperPrefixIsometryFamily J H) :
    ProperPrefixIsometryFamily H J where
  isometry := fun i ↦ (P.isometry i).symm

/-- Compose two compatible prefix-isometry families. -/
noncomputable def trans (P : ProperPrefixIsometryFamily J H)
    (Q : ProperPrefixIsometryFamily H T) :
    ProperPrefixIsometryFamily J T where
  isometry := fun i ↦ (P.isometry i).trans (Q.isometry i)

end ProperPrefixIsometryFamily

namespace FundamentalNormGeneratorChoice

variable {J : JordanDecomposition q L (n + 1)}
  {H : JordanDecomposition r M (n + 1)}

/-- Reuse exactly the same scalar generators on a decomposition of the same
fundamental type. -/
noncomputable def ofSameFundamentalType
    (A : FundamentalNormGeneratorChoice J)
    (F : SameFundamentalType J H) :
    FundamentalNormGeneratorChoice H where
  value := A.value
  spec := by
    intro i
    simpa only [F.indexEquiv_apply_eq_self] using A.spec_right F i

@[simp]
theorem ofSameFundamentalType_value
    (A : FundamentalNormGeneratorChoice J)
    (F : SameFundamentalType J H) (i : Fin (n + 1)) :
    (A.ofSameFundamentalType F).value i = A.value i :=
  rfl

end FundamentalNormGeneratorChoice

namespace SameFundamentalType

variable {J : JordanDecomposition q L (n + 1)}
  {H : JordanDecomposition r M (n + 1)}

/-- The explicit O'Meara threshold is unchanged when the same scalar norm
generator is transported along equality of fundamental type. -/
theorem fourNormOverWeightIdealWith_eq
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J) (i : Fin (n + 1)) :
    H.fourNormOverWeightIdealWith (A.ofSameFundamentalType F) i =
      J.fourNormOverWeightIdealWith A i := by
  apply fourNormOverWeightIdealWith_eq_of_scaleOrder_normGroup_eq
      (A := A) (B := A.ofSameFundamentalType F)
  · intro j
    simpa only [F.indexEquiv_apply_eq_self] using F.scaleOrder_eq j
  · intro j
    simpa only [F.indexEquiv_apply_eq_self] using F.normGroup_eq j
  · intro j
    rfl

end SameFundamentalType

variable {J : JordanDecomposition q L (n + 1)}
  {H : JordanDecomposition r M (n + 1)}
  {J' : JordanDecomposition q' L' (n + 1)}
  {H' : JordanDecomposition r' M' (n + 1)}

/-- Condition 93:28(i) is invariant under simultaneous replacement of the
source and target by integrally isometric proper prefixes. -/
theorem omeara9328ConditionI_transport
    (F : SameFundamentalType J J')
    (source : ProperPrefixIsometryFamily J' J)
    (target : ProperPrefixIsometryFamily H H')
    (hI : J.Omeara9328ConditionI H) :
    J'.Omeara9328ConditionI H' := by
  intro i
  rw [F.fundamentalIdeal_eq i]
  have htarget : unitSquareClass K (H.prefixDeterminantUnit i) =
      unitSquareClass K (H'.prefixDeterminantUnit i) := by
    change determinantClass
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).space
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).lattice =
      determinantClass
        (H'.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).space
        (H'.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).lattice
    exact determinantClass_eq_of_isometry (target.isometry i)
  have hsource : unitSquareClass K (J.prefixDeterminantUnit i) =
      unitSquareClass K (J'.prefixDeterminantUnit i) := by
    change determinantClass
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).space
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).lattice =
      determinantClass
        (J'.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).space
        (J'.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).lattice
    exact (determinantClass_eq_of_isometry (source.isometry i)).symm
  exact BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
    (H.prefixDeterminantUnit i) (H'.prefixDeterminantUnit i)
    (J.prefixDeterminantUnit i) (J'.prefixDeterminantUnit i)
    (J.fundamentalIdeal i) htarget hsource (hI i)

/-- Condition 93:28(ii) is invariant under the same transport. -/
theorem omeara9328ConditionIIWith_transport
    (F : SameFundamentalType J J')
    (source : ProperPrefixIsometryFamily J' J)
    (target : ProperPrefixIsometryFamily H H')
    (A : FundamentalNormGeneratorChoice J)
    (hII : J.Omeara9328ConditionIIWith H A) :
    J'.Omeara9328ConditionIIWith H' (A.ofSameFundamentalType F) := by
  intro i htrigger
  rw [F.fundamentalIdeal_eq i,
    F.fourNormOverWeightIdealWith_eq A] at htrigger
  rcases hII i htrigger with ⟨f⟩
  let targetReframe :=
    (target.isometry i).toQuadraticSpaceIsometry.orthogonalSum
      (QuadraticSpace.Isometry.refl
        (QuadraticSpace.scaledLine (A.value (boundaryRightIndex i))))
  exact ⟨targetReframe.toRepresentation.trans
    (f.trans (source.isometry i).toQuadraticSpaceIsometry.toRepresentation)⟩

/-- Condition 93:28(iii) is invariant under the same transport. -/
theorem omeara9328ConditionIIIWith_transport
    (F : SameFundamentalType J J')
    (source : ProperPrefixIsometryFamily J' J)
    (target : ProperPrefixIsometryFamily H H')
    (A : FundamentalNormGeneratorChoice J)
    (hIII : J.Omeara9328ConditionIIIWith H A) :
    J'.Omeara9328ConditionIIIWith H' (A.ofSameFundamentalType F) := by
  intro i htrigger
  rw [F.fundamentalIdeal_eq i,
    F.fourNormOverWeightIdealWith_eq A] at htrigger
  rcases hIII i htrigger with ⟨f⟩
  let targetReframe :=
    (target.isometry i).toQuadraticSpaceIsometry.orthogonalSum
      (QuadraticSpace.Isometry.refl
        (QuadraticSpace.scaledLine (A.value (boundaryLeftIndex i))))
  exact ⟨targetReframe.toRepresentation.trans
    (f.trans (source.isometry i).toQuadraticSpaceIsometry.toRepresentation)⟩

/-- Simultaneous source/target prefix transport of all three conditions in
O'Meara 93:28. -/
theorem omeara9328ConditionsWith_transport
    (F : SameFundamentalType J J')
    (source : ProperPrefixIsometryFamily J' J)
    (target : ProperPrefixIsometryFamily H H')
    (A : FundamentalNormGeneratorChoice J)
    (h : J.Omeara9328ConditionsWith H A) :
    J'.Omeara9328ConditionsWith H' (A.ofSameFundamentalType F) :=
  ⟨omeara9328ConditionI_transport F source target h.1,
    omeara9328ConditionIIWith_transport F source target A h.2.1,
    omeara9328ConditionIIIWith_transport F source target A h.2.2⟩

end Lattice.JordanDecomposition

end Bong
