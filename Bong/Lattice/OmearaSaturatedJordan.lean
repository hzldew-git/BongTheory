/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaFundamentalIdeals
import Bong.Lattice.OmearaModularNormClassification
import Bong.Lattice.OrthogonalDecompositionProduct
import Bong.Lattice.OrthogonalDecompositionTail
import Bong.Bong.Beli2009ComponentwiseAssembly
import Bong.QuadraticSpace.OrthogonalSumCancellation

/-!
# Saturated Jordan splittings

O'Meara calls a Jordan splitting saturated when the norm group of every
displayed modular component is the corresponding intrinsic fundamental norm
group.  This file records that semantic definition and the componentwise
classification consequence used in the induction for Theorem 93:28.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {t : Nat}

namespace JordanDecomposition

/-- Glue an isometry of the first Jordan components to an isometry of the
exact suffix lattices.  This is the geometric final step of the induction in
93:28 after the target head has been aligned with the source head. -/
noncomputable def headTailIsometry
    {n : Nat}
    (J : JordanDecomposition q L (n + 2))
    (H : JordanDecomposition r M (n + 2))
    (head : Isometry (J.component 0).space (H.component 0).space
      (J.component 0).lattice (H.component 0).lattice)
    (tail : Isometry
      (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space
      (H.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space
      (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1).lattice
      (H.toOrthogonalDecomposition.suffixQuadraticSublattice 1).lattice) :
    Isometry q r L M := by
  apply BONG.orthogonalDecompositionComponentwiseIsometry
    J.toOrthogonalDecomposition.headTailDecomposition
    H.toOrthogonalDecomposition.headTailDecomposition
  intro i
  refine Fin.cases head (fun j => ?_) i
  have hj : j = 0 := Subsingleton.elim j 0
  subst j
  exact tail

/-- Once the first component spaces have been aligned, ambient Witt
cancellation identifies the exact suffix quadratic spaces.  Thus the tail
ambient isometry used in the 93:28 induction is derived data, not a law. -/
noncomputable def tailSpaceIsometry
    {n : Nat}
    (J : JordanDecomposition q L (n + 2))
    (H : JordanDecomposition r M (n + 2))
    (ambient : QuadraticSpace.Isometry q r)
    (head : QuadraticSpace.Isometry
      (J.component 0).space (H.component 0).space) :
    QuadraticSpace.Isometry
      (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space
      (H.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space := by
  letI : Module.Finite K (J.component 0).carrier :=
    (J.component 0).lattice.moduleFinite
  letI : Module.Finite K (H.component 0).carrier :=
    (H.component 0).lattice.moduleFinite
  letI : Module.Finite K
      (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1).carrier :=
    (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1).lattice.moduleFinite
  letI : Module.Finite K
      (H.toOrthogonalDecomposition.suffixQuadraticSublattice 1).carrier :=
    (H.toOrthogonalDecomposition.suffixQuadraticSublattice 1).lattice.moduleFinite
  let sourcePair :=
    J.toOrthogonalDecomposition.headTailDecomposition
  let targetPair :=
    H.toOrthogonalDecomposition.headTailDecomposition
  let totalProduct : QuadraticSpace.Isometry
      ((J.component 0).space.orthogonalSum
        (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space)
      ((H.component 0).space.orthogonalSum
        (H.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space) :=
    sourcePair.pairProductLatticeIsometry.toQuadraticSpaceIsometry.trans <|
      ambient.trans
        targetPair.pairProductLatticeIsometry.symm.toQuadraticSpaceIsometry
  exact QuadraticSpace.orthogonalSumCancel
    (J.component 0).space (H.component 0).space
    (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space
    (H.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space
    head totalProduct

/-- O'Meara's definition of a saturated Jordan splitting (93:20). -/
noncomputable def IsSaturated (J : JordanDecomposition q L t) : Prop :=
  ∀ i : Fin t,
    normGroupSet (J.component i).space (J.component i).lattice =
      J.fundamentalNormGroup i

namespace IsSaturated

variable {J : JordanDecomposition q L t}
  {H : JordanDecomposition r M t}

/-- Corresponding components of saturated splittings of the same
fundamental type have the same scalar norm group. -/
theorem componentNormGroup_eq
    (hJ : J.IsSaturated) (hH : H.IsSaturated)
    (F : SameFundamentalType J H) (i : Fin t) :
    normGroupSet (H.component i).space (H.component i).lattice =
      normGroupSet (J.component i).space (J.component i).lattice := by
  have hfundamental := F.normGroup_eq i
  rw [F.indexEquiv_apply_eq_self] at hfundamental
  calc
    normGroupSet (H.component i).space (H.component i).lattice =
        H.fundamentalNormGroup i := hH i
    _ = J.fundamentalNormGroup i := hfundamental
    _ = normGroupSet (J.component i).space
          (J.component i).lattice := (hJ i).symm

/-- Once the two component quadratic spaces are identified, saturation and
equality of fundamental type classify the two modular component lattices by
O'Meara 93:16. -/
noncomputable def componentIsometry
    (hJ : J.IsSaturated) (hH : H.IsSaturated)
    (F : SameFundamentalType J H) (i : Fin t)
    (ambient : (J.component i).space.IsIsometric
      (H.component i).space) :
    Isometry (J.component i).space (H.component i).space
      (J.component i).lattice (H.component i).lattice := by
  let f : QuadraticSpace.Isometry (J.component i).space
      (H.component i).space := Classical.choice ambient
  let mapped : Lattice K (H.component i).carrier :=
    map f.toLinearEquiv (J.component i).lattice
  let lift : Isometry (J.component i).space (H.component i).space
      (J.component i).lattice mapped :=
    Isometry.toMap (J.component i).space f (J.component i).lattice
  have hscaleOrder := F.scaleOrder_eq i
  rw [F.indexEquiv_apply_eq_self] at hscaleOrder
  have hscaleIdeal :
      principalIdeal (K := K) (J.scaleGenerator i : K) =
        principalIdeal (K := K) (H.scaleGenerator i : K) :=
    (principalIdeal_eq_iff_ordUnit_eq _ _).2 hscaleOrder.symm
  have hmappedModular : IsModular (H.component i).space mapped
      (H.scaleGenerator i) :=
    ((J.modular i).mapLatticeIsometry lift).of_principalIdeal_eq hscaleIdeal
  have hgroup : normGroupSet (H.component i).space mapped =
      normGroupSet (H.component i).space (H.component i).lattice := by
    calc
      normGroupSet (H.component i).space mapped =
          normGroupSet (J.component i).space
            (J.component i).lattice :=
        normGroupSet_eq_of_latticeIsometry lift
      _ = normGroupSet (H.component i).space
            (H.component i).lattice :=
        (hJ.componentNormGroup_eq hH F i).symm
  exact lift.trans <|
    omeara9316_of_modular_normGroupSet_eq (H.scaleGenerator i)
      hmappedModular (H.modular i) hgroup

end IsSaturated

/-- If every corresponding component space is isometric, saturated Jordan
splittings of the same fundamental type assemble to an isometry of the full
lattices.  The nontrivial content remaining in 93:28 is precisely the
production of these component-space identifications. -/
noncomputable def isometryOfSaturatedComponentSpaces
    {n : Nat}
    (J : JordanDecomposition q L (n + 1))
    (H : JordanDecomposition r M (n + 1))
    (hJ : J.IsSaturated) (hH : H.IsSaturated)
    (F : SameFundamentalType J H)
    (ambient : ∀ i : Fin (n + 1),
      (J.component i).space.IsIsometric (H.component i).space) :
    Isometry q r L M :=
  BONG.orthogonalDecompositionComponentwiseIsometry
    J.toOrthogonalDecomposition H.toOrthogonalDecomposition
      (fun i => hJ.componentIsometry hH F i (ambient i))

end JordanDecomposition

end Lattice

end Bong
