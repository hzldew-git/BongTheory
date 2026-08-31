/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalSectionFour
import Bong.Lattice.OmearaStableHyperbolicCancellation

/-!
# Beli's Lemma 4.3 for heterogeneous nonempty families

This file bundles the varying residual quadratic spaces in Lemma 4.3.  Its
statement therefore has the paper's actual nonempty family `I`, rather than
silently requiring every residual lattice to share one ambient carrier.
-/

namespace Bong

open Dyadic

namespace Lattice.QuadraticLatticeModel

universe u i

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Integrality of a bundled quadratic lattice. -/
def IsIntegral (X : Bong.Lattice.QuadraticLatticeModel (K := K)) : Prop := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  exact Lattice.IsIntegral X.form X.lattice

/-- Integral representability between bundled quadratic lattices. -/
def Represents (X Y : Bong.Lattice.QuadraticLatticeModel (K := K)) : Prop := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup Y.Carrier := Y.addCommGroup
  letI : Module K Y.Carrier := Y.module
  exact Lattice.Represents X.form Y.form X.lattice Y.lattice

/-- Adjoin `k` copies of `2⁻¹ A(0,0)` to a bundled lattice. -/
noncomputable def adjoinHalfHyperbolic
    (X : Bong.Lattice.QuadraticLatticeModel (K := K))
    (k : Nat) : Bong.Lattice.QuadraticLatticeModel (K := K) := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  exact
    { Carrier := HyperbolicExtension K X.Carrier k
      form := halfHyperbolicExtensionForm X.form k
      lattice := halfHyperbolicExtensionLattice X.lattice k }

/-- A representation of residual lattices extends through a common standard
half-hyperbolic tower. -/
theorem Represents.adjoinHalfHyperbolic
    {X Y : Bong.Lattice.QuadraticLatticeModel (K := K)}
    (h : X.Represents Y) :
    ∀ k : Nat, (X.adjoinHalfHyperbolic k).Represents
      (Y.adjoinHalfHyperbolic k)
  | 0 => h
  | k + 1 => by
      letI : AddCommGroup X.Carrier := X.addCommGroup
      letI : Module K X.Carrier := X.module
      letI : AddCommGroup Y.Carrier := Y.addCommGroup
      letI : Module K Y.Carrier := Y.module
      change Lattice.Represents
        (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
          (dyadicHalfUnit (K := K))).orthogonalSum
          (halfHyperbolicExtensionForm X.form k))
        (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
          (dyadicHalfUnit (K := K))).orthogonalSum
          (halfHyperbolicExtensionForm Y.form k))
        (product (hyperbolicPlaneLattice (K := K))
          (halfHyperbolicExtensionLattice X.lattice k))
        (product (hyperbolicPlaneLattice (K := K))
          (halfHyperbolicExtensionLattice Y.lattice k))
      exact Lattice.Represents.orthogonalProductBasic
        (Lattice.represents_refl _ _) (h.adjoinHalfHyperbolic k)

end Lattice.QuadraticLatticeModel

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Beli, Lemma 4.3.  The family is genuinely heterogeneous: each member is
a bundled quadratic lattice and the nonempty index type is the paper's
nonempty set `I`. -/
theorem beliUniversalLemma43
    {I : Type i} [Nonempty I]
    (k : Nat) (_hk : 1 ≤ k)
    (M : Bong.Lattice.QuadraticLatticeModel (K := K))
    (N : I → Bong.Lattice.QuadraticLatticeModel (K := K))
    (hM : M.IsIntegral) (_hN : ∀ i, (N i).IsIntegral) :
    (∀ i, M.Represents ((N i).adjoinHalfHyperbolic k)) ↔
      ∃ M' : Bong.Lattice.QuadraticLatticeModel (K := K),
        M'.IsIntegral ∧
        Nonempty ((M'.adjoinHalfHyperbolic k).Isometry M) ∧
        ∀ i, M'.Represents (N i) := by
  classical
  letI : AddCommGroup M.Carrier := M.addCommGroup
  letI : Module K M.Carrier := M.module
  letI nAddCommGroup (i : I) : AddCommGroup (N i).Carrier :=
    (N i).addCommGroup
  letI nModule (i : I) : Module K (N i).Carrier := (N i).module
  constructor
  · intro hrep
    let f (i : I) := by
      letI : AddCommGroup (N i).Carrier := (N i).addCommGroup
      letI : Module K (N i).Carrier := (N i).module
      exact Classical.choice (hrep i)
    let S (i : I) := by
      letI : AddCommGroup (N i).Carrier := (N i).addCommGroup
      letI : Module K (N i).Carrier := (N i).module
      exact halfHyperbolicRepresentationSplitting k hM (f i)
    let R (i : I) : Bong.Lattice.QuadraticLatticeModel (K := K) :=
      { Carrier := (S i).Residual
        addCommGroup := (S i).residualAddCommGroup
        module := (S i).residualModule
        form := (S i).residualForm
        lattice := (S i).residualLattice }
    let i0 : I := Classical.choice (inferInstance : Nonempty I)
    refine ⟨R i0, ?_, ?_, ?_⟩
    · exact (S i0).residualIntegral
    · exact ⟨(S i0).presentation⟩
    · intro i
      letI : AddCommGroup (N i).Carrier := (N i).addCommGroup
      letI : Module K (N i).Carrier := (N i).module
      letI : AddCommGroup (R i).Carrier := (R i).addCommGroup
      letI : Module K (R i).Carrier := (R i).module
      letI : AddCommGroup (R i0).Carrier := (R i0).addCommGroup
      letI : Module K (R i0).Carrier := (R i0).module
      let total : Isometry
          (halfHyperbolicExtensionForm (R i).form k)
          (halfHyperbolicExtensionForm (R i0).form k)
          (halfHyperbolicExtensionLattice (R i).lattice k)
          (halfHyperbolicExtensionLattice (R i0).lattice k) :=
        (S i).presentation.trans (S i0).presentation.symm
      let totalRaw : Isometry
          (omearaPlaneExtensionForm (R i).form
            (dyadicHalfUnit (K := K)) k (fun _ => 0))
          (omearaPlaneExtensionForm (R i0).form
            (dyadicHalfUnit (K := K)) k (fun _ => 0))
          (hyperbolicExtensionLattice (R i).lattice k)
          (hyperbolicExtensionLattice (R i0).lattice k) := by
        rw [← halfHyperbolicExtensionForm_eq (R i).form k,
          ← halfHyperbolicExtensionForm_eq (R i0).form k,
          ← halfHyperbolicExtensionLattice_eq (R i).lattice k,
          ← halfHyperbolicExtensionLattice_eq (R i0).lattice k]
        exact total
      let cancel : Isometry (R i).form (R i0).form
          (R i).lattice (R i0).lattice :=
        cancelScaledZeroOmearaPlaneExtension
          (dyadicHalfUnit (K := K)) k totalRaw
      change Lattice.Represents (R i0).form (N i).form
        (R i0).lattice (N i).lattice
      have htailR : Lattice.Represents (R i).form (N i).form
          (R i).lattice (N i).lattice := by
        simpa [R] using (S i).representsTail
      exact ⟨cancel.toRepresentation.trans
        (Classical.choice htailR)⟩
  · rintro ⟨M', _hM', ⟨iso⟩, htail⟩
    intro i
    letI : AddCommGroup M'.Carrier := M'.addCommGroup
    letI : Module K M'.Carrier := M'.module
    letI : AddCommGroup (N i).Carrier := (N i).addCommGroup
    letI : Module K (N i).Carrier := (N i).module
    letI : AddCommGroup (M'.adjoinHalfHyperbolic k).Carrier :=
      (M'.adjoinHalfHyperbolic k).addCommGroup
    letI : Module K (M'.adjoinHalfHyperbolic k).Carrier :=
      (M'.adjoinHalfHyperbolic k).module
    change Lattice.Represents M.form
      (halfHyperbolicExtensionForm (N i).form k) M.lattice
      (halfHyperbolicExtensionLattice (N i).lattice k)
    exact ⟨iso.toRepresentation.trans
      (Classical.choice ((htail i).adjoinHalfHyperbolic k))⟩

end Lattice

end Bong
