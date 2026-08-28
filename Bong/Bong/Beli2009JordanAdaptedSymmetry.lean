/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanBoundaryEvenUnary

/-!
# Source-target symmetry for the adapted Jordan alignment

The Jordan alignment used in Beli (2009) is symmetric in the two lattices.
This file packages that symmetry and transfers the complete even-boundary
formula to the target side without duplicating its mathematical proof.
-/

namespace Bong

open Dyadic Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

namespace BONG.WeakJordanEndpointAlignment

/-- Swap the source and target of a weak Jordan endpoint alignment. -/
noncomputable def symm {m t : Nat}
    {a : BONG V q L (m + 1)} {b : BONG W r M (m + 1)}
    (P : WeakJordanEndpointAlignment a b t) :
    WeakJordanEndpointAlignment b a t where
  sourceWeak := P.targetWeak
  targetWeak := P.sourceWeak
  sourceParity := P.targetParity
  targetParity := P.sourceParity
  sourceEndpoints := P.targetEndpoints
  targetEndpoints := P.sourceEndpoints
  componentRankFamily_eq := P.componentRankFamily_eq.symm
  scaleOrderFamily_eq := P.scaleOrderFamily_eq.symm
  normOrderFamily_eq := P.normOrderFamily_eq.symm

end BONG.WeakJordanEndpointAlignment

namespace BONG.WeakJordanAdaptedAlignment

/-- Swap the source and target of an adapted weak Jordan alignment. -/
noncomputable def symm {m t : Nat}
    {a : BONG V q L (m + 1)} {b : BONG W r M (m + 1)}
    (P : WeakJordanAdaptedAlignment a b t) :
    WeakJordanAdaptedAlignment b a t where
  endpoint := P.endpoint.symm
  sourceAdapted := P.targetAdapted
  targetAdapted := P.sourceAdapted

end BONG.WeakJordanAdaptedAlignment

namespace BONG.StrictJordanAdaptedAlignment

/-- Swap the source and target of a strict adapted Jordan alignment. -/
noncomputable def symm {m : Nat}
    {a : BONG V q L (m + 1)} {b : BONG W r M (m + 1)}
    (S : StrictJordanAdaptedAlignment a b) :
    StrictJordanAdaptedAlignment b a where
  componentCount := S.componentCount
  weakAlignment := S.weakAlignment.symm
  sourceStrict := S.targetStrict
  targetStrict := S.sourceStrict

@[simp] theorem symm_componentCount {m : Nat}
    {a : BONG V q L (m + 1)} {b : BONG W r M (m + 1)}
    (S : StrictJordanAdaptedAlignment a b) :
    S.symm.componentCount = S.componentCount := rfl

@[simp] theorem symm_sourceJordan {m : Nat}
    {a : BONG V q L (m + 1)} {b : BONG W r M (m + 1)}
    (S : StrictJordanAdaptedAlignment a b) :
    S.symm.sourceJordan = S.targetJordan := rfl

@[simp] theorem symm_sourceProfile {m : Nat}
    {a : BONG V q L (m + 1)} {b : BONG W r M (m + 1)}
    (S : StrictJordanAdaptedAlignment a b) :
    S.symm.sourceProfile = S.targetProfile := rfl

@[simp] theorem symm_sourceJordanSucc
    {n t : Nat} {a : GoodBONG q L (n + 2)} {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (h : S.componentCount = t + 1) :
    S.symm.sourceJordanSucc h = S.targetJordanSucc h := rfl

@[simp] theorem symm_sourceProfileSucc
    {n t : Nat} {a : GoodBONG q L (n + 2)} {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (h : S.componentCount = t + 1) :
    S.symm.sourceProfileSucc h = S.targetProfileSucc h := rfl

/-- The target-side even boundary formula, obtained functorially from the
source-side theorem by symmetry of the strict adapted alignment. -/
theorem targetEvenBoundaryFundamentalOrder_eq_alpha
    {n : Nat}
    {a : GoodBONG q L (n + 2)} {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (z : Fin t)
    (heven : Even ((S.targetJordanSucc h).boundaryNormOrderSum z)) :
    let P := S.targetProfileSucc h
    let J := S.targetJordanSucc h
    let hleft := S.targetBoundaryLeftValue_isNormGeneratorValue h z
    let hright := S.targetBoundaryRightValue_isNormGeneratorValue h z
    (((J.evenOrderedFundamentalIdeal z
        (P.boundaryLeftValue z) (P.boundaryRightValue z)
        hleft hright heven).order : Int) : ℚ) =
      b.alphaValue (P.boundaryIndex z) := by
  exact S.symm.sourceEvenBoundaryFundamentalOrder_eq_alpha h z heven

end BONG.StrictJordanAdaptedAlignment

end Bong
