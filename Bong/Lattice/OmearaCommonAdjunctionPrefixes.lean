/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaCommonAdjunction
import Bong.Lattice.Omeara9328StabilizationPrefixes

/-!
# Prefix geometry of O'Meara's common adjunction

Every prefix of a componentwise common adjunction is the orthogonal product
of the corresponding prefixes of the common saturated splitting and the
original splitting.  This is the geometric input for transporting all three
conditions of O'Meara 93:28 through the common adjunction used in Step 2.
-/

namespace Bong

open Dyadic Module

namespace Lattice
namespace JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {N m : Nat}

/-- Raw common-adjunction carrier over a component of a prefix. -/
abbrev prefixCommonAdjunctionCarrier
    (P : JordanDecomposition q L (N + 2))
    (J : JordanDecomposition r M (N + 2))
    (hk : m + 1 ≤ N + 2) (i : Fin (m + 1)) :=
  P.commonAdjunctionCarrier J
    (P.toOrthogonalDecomposition.prefixIndexEquiv (m + 1) hk i).1

/-- Raw common-adjunction form over a component of a prefix. -/
noncomputable abbrev prefixCommonAdjunctionForm
    (P : JordanDecomposition q L (N + 2))
    (J : JordanDecomposition r M (N + 2))
    (hk : m + 1 ≤ N + 2) (i : Fin (m + 1)) :=
  P.commonAdjunctionForm J
    (P.toOrthogonalDecomposition.prefixIndexEquiv (m + 1) hk i).1

/-- Raw common-adjunction lattice over a component of a prefix. -/
noncomputable abbrev prefixCommonAdjunctionLattice
    (P : JordanDecomposition q L (N + 2))
    (J : JordanDecomposition r M (N + 2))
    (hk : m + 1 ≤ N + 2) (i : Fin (m + 1)) :=
  P.commonAdjunctionLattice J
    (P.toOrthogonalDecomposition.prefixIndexEquiv (m + 1) hk i).1

/-- The raw restricted block product is the displayed prefix of the common
adjunction Jordan decomposition. -/
noncomputable def rawCommonAdjunctionPrefixIsometry
    (P : JordanDecomposition q L (N + 2))
    (J : JordanDecomposition r M (N + 2))
    (F : SameFundamentalType P J) (hP : P.IsSaturated)
    (hk : m + 1 ≤ N + 2) :
    Isometry
      (BONG.blockOrthogonalForm m
        (P.prefixCommonAdjunctionCarrier J hk)
        (P.prefixCommonAdjunctionForm J hk))
      ((P.commonAdjunctionJordan J F hP).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 1)).space
      (BONG.blockProductLattice m
        (P.prefixCommonAdjunctionCarrier J hk)
        (P.prefixCommonAdjunctionLattice J hk))
      ((P.commonAdjunctionJordan J F hP).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 1)).lattice := by
  let D := P.toOrthogonalDecomposition
  let C := (P.commonAdjunctionJordan J F hP).toOrthogonalDecomposition
  let rawComponent : ∀ i : Fin (m + 1), Isometry
      (P.prefixCommonAdjunctionForm J hk i)
      (C.component (C.prefixIndexEquiv (m + 1) hk i).1).space
      (P.prefixCommonAdjunctionLattice J hk i)
      (C.component (C.prefixIndexEquiv (m + 1) hk i).1).lattice := fun i => by
    let f := BONG.blockProductComponentIsometry
      (P.commonAdjunctionCarrier J) (P.commonAdjunctionForm J)
      (P.commonAdjunctionLattice J)
      (D.prefixIndexEquiv (m + 1) hk i).1
    have hidx := prefixIndexEquiv_component_eq D C hk i
    rw [← hidx]
    exact f
  let productIso := BONG.blockProductLatticeIsometry
    (P.prefixCommonAdjunctionForm J hk)
    (C.prefixBlockSpace hk)
    (P.prefixCommonAdjunctionLattice J hk)
    (C.prefixBlockLattice hk)
    rawComponent
  exact productIso.trans (C.prefixBlockProductIsometry hk)

/-- Distribute a raw common-adjunction prefix into the two raw prefix block
products. -/
noncomputable def gatherRawCommonAdjunctionPrefix
    (P : JordanDecomposition q L (N + 2))
    (J : JordanDecomposition r M (N + 2))
    (hk : m + 1 ≤ N + 2) :
    Isometry
      (BONG.blockOrthogonalForm m
        (P.prefixCommonAdjunctionCarrier J hk)
        (P.prefixCommonAdjunctionForm J hk))
      ((BONG.blockOrthogonalForm m
          (P.toOrthogonalDecomposition.prefixBlockCarrier hk)
          (P.toOrthogonalDecomposition.prefixBlockSpace hk)).orthogonalSum
        (BONG.blockOrthogonalForm m
          (J.toOrthogonalDecomposition.prefixBlockCarrier hk)
          (J.toOrthogonalDecomposition.prefixBlockSpace hk)))
      (BONG.blockProductLattice m
        (P.prefixCommonAdjunctionCarrier J hk)
        (P.prefixCommonAdjunctionLattice J hk))
      (product
        (BONG.blockProductLattice m
          (P.toOrthogonalDecomposition.prefixBlockCarrier hk)
          (P.toOrthogonalDecomposition.prefixBlockLattice hk))
        (BONG.blockProductLattice m
          (J.toOrthogonalDecomposition.prefixBlockCarrier hk)
          (J.toOrthogonalDecomposition.prefixBlockLattice hk))) := by
  exact BONG.blockOrthogonalPairLatticeIsometry
    (P.toOrthogonalDecomposition.prefixBlockCarrier hk)
    (J.toOrthogonalDecomposition.prefixBlockCarrier hk)
    (P.toOrthogonalDecomposition.prefixBlockSpace hk)
    (J.toOrthogonalDecomposition.prefixBlockSpace hk)
    (P.toOrthogonalDecomposition.prefixBlockLattice hk)
    (J.toOrthogonalDecomposition.prefixBlockLattice hk)

/-- Every displayed common-adjunction prefix is the orthogonal product of
the corresponding displayed prefixes. -/
noncomputable def commonAdjunctionPrefixGatherIsometry
    (P : JordanDecomposition q L (N + 2))
    (J : JordanDecomposition r M (N + 2))
    (F : SameFundamentalType P J) (hP : P.IsSaturated)
    (hk : m + 1 ≤ N + 2) :
    Isometry
      ((P.commonAdjunctionJordan J F hP).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 1)).space
      ((P.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 1)).space.orthogonalSum
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 1)).space)
      ((P.commonAdjunctionJordan J F hP).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 1)).lattice
      (product
        (P.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 1)).lattice
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 1)).lattice) :=
  (P.rawCommonAdjunctionPrefixIsometry J F hP hk).symm |>.trans
    ((P.gatherRawCommonAdjunctionPrefix J hk).trans
      ((P.toOrthogonalDecomposition.prefixBlockProductIsometry hk)
        |>.orthogonalProductBasic
          (J.toOrthogonalDecomposition.prefixBlockProductIsometry hk)))

end JordanDecomposition
end Lattice

end Bong
