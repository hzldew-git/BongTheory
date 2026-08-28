/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.JordanReverseDualThresholds
import Bong.Lattice.OrthogonalDecompositionSuffix

/-!
# Prefix spaces of the reverse-dual Jordan chain

The first `k` components of the reverse-dual chain have the same ambient
vector space as the last `k` components of the original chain.  This is the
geometric part of O'Meara 93:24 needed in the necessity proof of 93:28: after
duality, a condition on a reversed prefix becomes a condition on the
corresponding original suffix.

Only the quadratic spaces are identified here.  The integral lattice on the
reverse-dual prefix is, as expected, the dual of the original suffix lattice;
the representation clauses of 93:28 depend only on the underlying quadratic
spaces.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- Reversing the component order turns a prefix of length `k` into the
original suffix beginning at `t-k`. -/
theorem reverseDual_prefixCarrier_eq_suffixCarrier
    (J : JordanDecomposition q L t) (k : Nat) (hk : k ≤ t) :
    J.reverseDual.toOrthogonalDecomposition.prefixCarrier k =
      J.toOrthogonalDecomposition.suffixCarrier (t - k) := by
  unfold Lattice.OrthogonalDecomposition.prefixCarrier
    Lattice.OrthogonalDecomposition.suffixCarrier
  apply le_antisymm
  · apply iSup_le
    intro i
    change (J.component (Fin.rev i.1)).carrier ≤ _
    let j : J.toOrthogonalDecomposition.SuffixIndex (t - k) :=
      ⟨Fin.rev i.1, by
        rw [Fin.val_rev]
        omega⟩
    exact le_iSup
      (fun h : J.toOrthogonalDecomposition.SuffixIndex (t - k) ↦
        (J.component h.1).carrier) j
  · apply iSup_le
    intro i
    let j : J.reverseDual.toOrthogonalDecomposition.PrefixIndex k :=
      ⟨Fin.rev i.1, by
        rw [Fin.val_rev]
        omega⟩
    have hj : Fin.rev j.1 = i.1 := by
      exact Fin.rev_rev i.1
    simpa only [JordanDecomposition.reverseDual_component,
      Lattice.QuadraticSublattice.dual_carrier, hj] using
        (le_iSup
          (fun h : J.reverseDual.toOrthogonalDecomposition.PrefixIndex k ↦
            (J.reverseDual.component h.1).carrier) j)

/-- Quadratic-space identification of a reverse-dual prefix with the
corresponding original suffix. -/
noncomputable def reverseDualPrefixSpaceIsometry
    (J : JordanDecomposition q L t) (k : Nat) (hk : k ≤ t) :
    QuadraticSpace.Isometry
      (J.reverseDual.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice k).space
      (J.toOrthogonalDecomposition
        |>.suffixQuadraticSublattice (t - k)).space := by
  let hcarrier := J.reverseDual_prefixCarrier_eq_suffixCarrier k hk
  let e :
      J.reverseDual.toOrthogonalDecomposition.prefixCarrier k ≃ₗ[K]
        J.toOrthogonalDecomposition.suffixCarrier (t - k) :=
    LinearEquiv.ofEq _ _ hcarrier
  refine
    { toLinearEquiv := e
      map_bilin := ?_ }
  intro x y
  subst hcarrier
  rfl

/-- Boundary-index form: the reversed prefix at `Fin.rev i` is the suffix
strictly after the original boundary `i`. -/
noncomputable def reverseDualBoundaryPrefixSpaceIsometry
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) :
    QuadraticSpace.Isometry
      (J.reverseDual.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice ((Fin.rev i).val + 1)).space
      (J.toOrthogonalDecomposition
        |>.suffixQuadraticSublattice (i.val + 1)).space := by
  have hk : (Fin.rev i).val + 1 ≤ t + 1 := by omega
  have hcut : (t + 1) - ((Fin.rev i).val + 1) = i.val + 1 := by
    rw [Fin.val_rev]
    omega
  let f := J.reverseDualPrefixSpaceIsometry ((Fin.rev i).val + 1) hk
  rw [hcut] at f
  exact f

end Lattice.JordanDecomposition

end Bong
