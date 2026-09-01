/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalSectionFourReduction
import Bong.Bong.DiagonalHeadCancellation
import Bong.Lattice.DeepRescale
import Bong.Lattice.Modular

/-!
# Beli's reduction by Witt index

This file proves Lemma 4.4 of C. N. Beli, *Universal integral quadratic
forms over dyadic local fields*.  The predicate `HasWittIndexAtLeast` uses
the paper's equivalent characterization: the ambient quadratic space splits
at least `k` hyperbolic planes.  A residual lattice is included in the
existential package only to keep all varying carrier types in one universe;
`exists_integral_rescale` below proves that this adds no integrality
assumption.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]

/-- Every full lattice can be multiplied by a sufficiently deep uniformizer
power so that all of its quadratic values are integral. -/
theorem exists_integral_rescale
    (q : QuadraticSpace K V) (A : Lattice K V) :
    ∃ c : Kˣ, IsIntegral q (rescale c A) := by
  obtain ⟨k, hk, hdual⟩ := exists_uniformizerPower_rescale_le A
    (dualLattice q A) 0
  let c : Kˣ := uniformizerPowerUnit K k
  have hcIntegral : (c : K) ∈ IntegerRing K := by
    rw [mem_integerRing_iff, Dyadic.IsIntegral, ← coe_ordUnit K c,
      ordUnit_uniformizerPowerUnit]
    exact_mod_cast hk
  have hself : rescale c A ≤ A :=
    rescale_le_self_of_mem_integerRing c A hcIntegral
  refine ⟨c, (isIntegral_iff_forall q (rescale c A)).2 ?_⟩
  intro x hx
  have hxDual : x ∈ dualLattice q A := by
    exact hdual hx
  have hpair := (mem_dualLattice_iff q A x).1 hxDual x (hself hx)
  exact (mem_integerRing_iff K).1 hpair

/-- Every finite-dimensional quadratic space already carrying a full
lattice has an `O`-maximal lattice. -/
theorem exists_oMaximal_lattice
    (q : QuadraticSpace K V) (A : Lattice K V) :
    ∃ M : Lattice K V, IsOMaximal q M := by
  obtain ⟨c, hc⟩ := exists_integral_rescale q A
  obtain ⟨M, _hcontain, hM⟩ :=
    exists_oMaximal_superlattice (q := q) (L := rescale c A) hc
  exact ⟨M, hM⟩

namespace QuadraticLatticeModel

/-- The rank of the ambient quadratic space of a bundled lattice. -/
noncomputable def rank
    (X : QuadraticLatticeModel (K := K)) : Nat := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  exact finrank K X.Carrier

/-- Maximality of a bundled integral quadratic lattice. -/
def IsOMaximal (X : QuadraticLatticeModel (K := K)) : Prop := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  exact Lattice.IsOMaximal X.form X.lattice

/-- `n`-universality of a bundled integral quadratic lattice. -/
def IsNUniversal (X : QuadraticLatticeModel (K := K)) (n : Nat) : Prop := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  exact Lattice.IsNUniversal.{u, u, u} X.form X.lattice n

/-- The ambient space splits at least `k` hyperbolic planes.  The half-scaled
integral model is field-isometric to the ordinary hyperbolic plane and is the
normalization used throughout Beli's Section 4. -/
def HasWittIndexAtLeast
    (X : QuadraticLatticeModel (K := K)) (k : Nat) : Prop :=
  ∃ R : QuadraticLatticeModel (K := K), by
    letI : AddCommGroup X.Carrier := X.addCommGroup
    letI : Module K X.Carrier := X.module
    letI : AddCommGroup R.Carrier := R.addCommGroup
    letI : Module K R.Carrier := R.module
    exact X.form.IsIsometric (halfHyperbolicExtensionForm R.form k)

/-- Beli's condition in Lemma 4.4(i). -/
def RepresentsEveryIntegralOfRankWithWittIndexAtLeast
    (M : QuadraticLatticeModel (K := K)) (n k : Nat) : Prop :=
  ∀ X : QuadraticLatticeModel (K := K),
    X.rank = n → X.IsIntegral → X.HasWittIndexAtLeast k → M.Represents X

/-- Finite generation of a general hyperbolic extension. -/
theorem hyperbolicExtensionModuleFinite
    (X : QuadraticLatticeModel (K := K)) (k : Nat) : by
    letI : AddCommGroup X.Carrier := X.addCommGroup
    letI : Module K X.Carrier := X.module
    exact Module.Finite K (HyperbolicExtension K X.Carrier k) := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  induction k with
  | zero =>
      letI : AddCommGroup X.Carrier := X.addCommGroup
      letI : Module K X.Carrier := X.module
      exact X.lattice.moduleFinite
  | succ k ih =>
      letI := ih
      exact Module.Finite.prod

/-- Adjoining `k` hyperbolic planes raises the rank by `2k`. -/
theorem rank_adjoinHalfHyperbolic
    (X : QuadraticLatticeModel (K := K)) (k : Nat) :
    (X.adjoinHalfHyperbolic k).rank = 2 * k + X.rank := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  induction k with
  | zero =>
      change finrank K X.Carrier = 2 * 0 + finrank K X.Carrier
      omega
  | succ k ih =>
      letI : Module.Finite K (HyperbolicExtension K X.Carrier k) :=
        hyperbolicExtensionModuleFinite X k
      change finrank K ((Fin 2 → K) ×
          HyperbolicExtension K X.Carrier k) =
        2 * (k + 1) + finrank K X.Carrier
      rw [Module.finrank_prod, Module.finrank_fin_fun]
      change finrank K (HyperbolicExtension K X.Carrier k) =
        2 * k + finrank K X.Carrier at ih
      omega

/-- The standard lattice on `2⁻¹A(0,0)` is integral. -/
theorem halfHyperbolicPlane_isIntegral :
    Lattice.IsIntegral
      ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
        (dyadicHalfUnit (K := K)))
      (hyperbolicPlaneLattice (K := K)) := by
  let half : Kˣ := dyadicHalfUnit (K := K)
  have hproduct : (2 : K) * (half : K) = 1 := by
    change (dyadicTwoUnit (K := K) : K) * (half : K) = 1
    rw [← Units.val_mul]
    simp [half, dyadicHalfUnit]
  have hhyper : Lattice.IsIntegral
      (QuadraticSpace.hyperbolicPlane half)
      (hyperbolicPlaneLattice (K := K)) := by
    rw [Lattice.isIntegral_iff_normIdeal_le,
      Lattice.normIdeal_hyperbolicPlaneLattice, hproduct]
    exact le_rfl
  exact (Lattice.isIntegral_iff_of_latticeIsometry
    (scaledZeroOmearaPlaneLatticeIsometry half)).2 hhyper

/-- A half-hyperbolic extension is integral exactly when its tail is
integral; only the forward construction is needed in Lemma 4.4. -/
theorem IsIntegral.adjoinHalfHyperbolic
    {X : QuadraticLatticeModel (K := K)} (hX : X.IsIntegral) :
    ∀ k : Nat, (X.adjoinHalfHyperbolic k).IsIntegral
  | 0 => hX
  | k + 1 => by
      letI : AddCommGroup X.Carrier := X.addCommGroup
      letI : Module K X.Carrier := X.module
      change Lattice.IsIntegral
        (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
          (dyadicHalfUnit (K := K))).orthogonalSum
          (halfHyperbolicExtensionForm X.form k))
        (product (hyperbolicPlaneLattice (K := K))
          (halfHyperbolicExtensionLattice X.lattice k))
      exact Lattice.orthogonalProduct_isIntegral
        halfHyperbolicPlane_isIntegral (hX.adjoinHalfHyperbolic k)

/-- Conversely, integrality of a half-hyperbolic extension restricts to its
residual lattice. -/
theorem IsIntegral.of_adjoinHalfHyperbolic
    {X : QuadraticLatticeModel (K := K)} :
    ∀ k : Nat, (X.adjoinHalfHyperbolic k).IsIntegral → X.IsIntegral
  | 0, hX => hX
  | k + 1, hX => by
      letI : AddCommGroup X.Carrier := X.addCommGroup
      letI : Module K X.Carrier := X.module
      have htail : (X.adjoinHalfHyperbolic k).IsIntegral := by
        change Lattice.IsIntegral
          (halfHyperbolicExtensionForm X.form k)
          (halfHyperbolicExtensionLattice X.lattice k)
        apply Lattice.IsIntegral.right_of_orthogonalProduct
          (q := ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
            (dyadicHalfUnit (K := K))))
          (L := hyperbolicPlaneLattice (K := K))
        exact hX
      exact IsIntegral.of_adjoinHalfHyperbolic k htail

/-- A half-hyperbolic extension is integral exactly when its residual
lattice is integral. -/
theorem isIntegral_adjoinHalfHyperbolic_iff
    (X : QuadraticLatticeModel (K := K)) (k : Nat) :
    (X.adjoinHalfHyperbolic k).IsIntegral ↔ X.IsIntegral := by
  constructor
  · exact IsIntegral.of_adjoinHalfHyperbolic k
  · intro hX
    exact hX.adjoinHalfHyperbolic k

/-- Every natural rank occurs among `O`-maximal quadratic lattices. -/
theorem exists_oMaximal_of_rank (d : Nat) :
    ∃ X : QuadraticLatticeModel (K := K), X.rank = d ∧ X.IsOMaximal := by
  let q : QuadraticSpace K (Fin d → K) :=
    QuadraticSpace.finiteDiagonal (fun _ => 1) (fun _ => one_ne_zero)
  let A : Lattice K (Fin d → K) :=
    Lattice.basisLattice (Pi.basisFun K (Fin d))
  obtain ⟨M, hM⟩ := Lattice.exists_oMaximal_lattice q A
  let X : QuadraticLatticeModel (K := K) :=
    { Carrier := Fin d → K
      form := q
      lattice := M }
  refine ⟨X, ?_, hM⟩
  change finrank K (Fin d → K) = d
  exact Module.finrank_fin_fun K

end QuadraticLatticeModel

/-- Beli, Lemma 4.4.  For `k ≥ 1` and `n ≥ 2k+1`, representing every
integral rank-`n` lattice whose ambient space has Witt index at least `k` is
equivalent to splitting `k` standard half-hyperbolic planes with an
`(n-2k)`-universal residual lattice. -/
theorem beliUniversalLemma44
    (k n : Nat) (hk : 1 ≤ k) (hn : 2 * k + 1 ≤ n)
    (M : QuadraticLatticeModel (K := K)) (hM : M.IsIntegral) :
    M.RepresentsEveryIntegralOfRankWithWittIndexAtLeast n k ↔
      ∃ M' : QuadraticLatticeModel (K := K),
        M'.IsNUniversal (n - 2 * k) ∧
        Nonempty ((M'.adjoinHalfHyperbolic k).Isometry M) := by
  classical
  letI : AddCommGroup M.Carrier := M.addCommGroup
  letI : Module K M.Carrier := M.module
  let d := n - 2 * k
  let I := {X : QuadraticLatticeModel (K := K) //
    X.rank = d ∧ X.IsOMaximal}
  let N : I → QuadraticLatticeModel (K := K) := fun i => i.1
  have hId : d = n - 2 * k := rfl
  have hnonempty : Nonempty I := by
    obtain ⟨X, hXrank, hXmax⟩ :=
      QuadraticLatticeModel.exists_oMaximal_of_rank (K := K) d
    exact ⟨⟨X, hXrank, hXmax⟩⟩
  letI : Nonempty I := hnonempty
  letI nAddCommGroup (i : I) : AddCommGroup (N i).Carrier :=
    (N i).addCommGroup
  letI nModule (i : I) : Module K (N i).Carrier := (N i).module
  constructor
  · intro hall
    have hNIntegral : ∀ i, (N i).IsIntegral := by
      intro i
      exact i.2.2.isIntegral
    have htower : ∀ i, M.Represents ((N i).adjoinHalfHyperbolic k) := by
      intro i
      letI : AddCommGroup ((N i).adjoinHalfHyperbolic k).Carrier :=
        ((N i).adjoinHalfHyperbolic k).addCommGroup
      letI : Module K ((N i).adjoinHalfHyperbolic k).Carrier :=
        ((N i).adjoinHalfHyperbolic k).module
      apply hall
      · rw [QuadraticLatticeModel.rank_adjoinHalfHyperbolic]
        rw [i.2.1]
        dsimp [d]
        omega
      · exact (hNIntegral i).adjoinHalfHyperbolic k
      · exact ⟨N i, ⟨QuadraticSpace.Isometry.refl _⟩⟩
    obtain ⟨M', hM'Integral, hsplit, hrep⟩ :=
      (beliUniversalLemma43 k hk M N hM hNIntegral).1 htower
    letI : AddCommGroup M'.Carrier := M'.addCommGroup
    letI : Module K M'.Carrier := M'.module
    refine ⟨M', ?_, hsplit⟩
    change Lattice.IsNUniversal M'.form M'.lattice (n - 2 * k)
    rw [beliUniversalLemma41]
    refine ⟨hM'Integral, ?_⟩
    intro W _ _ r A hArank hAmax
    let X : QuadraticLatticeModel (K := K) :=
      { Carrier := W
        form := r
        lattice := A }
    have hXrank : X.rank = d := by
      change finrank K W = d
      simpa [hId] using hArank
    let i : I := ⟨X, hXrank, hAmax⟩
    have hi := hrep i
    change Lattice.Represents M'.form r M'.lattice A at hi
    exact hi
  · rintro ⟨M', hM'Universal, ⟨hsplit⟩⟩
    intro X hXrank hXIntegral hXWitt
    rcases hXWitt with ⟨R, ⟨hambient⟩⟩
    letI : AddCommGroup X.Carrier := X.addCommGroup
    letI : Module K X.Carrier := X.module
    letI : AddCommGroup R.Carrier := R.addCommGroup
    letI : Module K R.Carrier := R.module
    letI : AddCommGroup M'.Carrier := M'.addCommGroup
    letI : Module K M'.Carrier := M'.module
    letI : AddCommGroup (M'.adjoinHalfHyperbolic k).Carrier :=
      (M'.adjoinHalfHyperbolic k).addCommGroup
    letI : Module K (M'.adjoinHalfHyperbolic k).Carrier :=
      (M'.adjoinHalfHyperbolic k).module
    obtain ⟨P, hXP, hPmax⟩ :=
      exists_oMaximal_superlattice (q := X.form) (L := X.lattice) hXIntegral
    obtain ⟨Nmax, hNmax⟩ := exists_oMaximal_lattice R.form R.lattice
    let Nmodel : QuadraticLatticeModel (K := K) :=
      { Carrier := R.Carrier
        form := R.form
        lattice := Nmax }
    letI : AddCommGroup Nmodel.Carrier := Nmodel.addCommGroup
    letI : Module K Nmodel.Carrier := Nmodel.module
    letI : AddCommGroup (Nmodel.adjoinHalfHyperbolic k).Carrier :=
      (Nmodel.adjoinHalfHyperbolic k).addCommGroup
    letI : Module K (Nmodel.adjoinHalfHyperbolic k).Carrier :=
      (Nmodel.adjoinHalfHyperbolic k).module
    have hRrank : R.rank = n - 2 * k := by
      have hrank := hambient.toLinearEquiv.finrank_eq
      change X.rank = (R.adjoinHalfHyperbolic k).rank at hrank
      rw [QuadraticLatticeModel.rank_adjoinHalfHyperbolic] at hrank
      rw [hXrank] at hrank
      omega
    have hNrep : M'.Represents Nmodel := by
      change Lattice.Represents M'.form R.form M'.lattice Nmax
      have hRrankRaw : finrank K R.Carrier = n - 2 * k := by
        change finrank K R.Carrier = n - 2 * k at hRrank
        exact hRrank
      exact hM'Universal.2 R.form Nmax hRrankRaw
        hNmax.isIntegral
    have htowerRep : (M'.adjoinHalfHyperbolic k).Represents
        (Nmodel.adjoinHalfHyperbolic k) :=
      hNrep.adjoinHalfHyperbolic k
    have hPiso : IsIsometric X.form
        (halfHyperbolicExtensionForm R.form k) P
        (halfHyperbolicExtensionLattice Nmax k) :=
      beliUniversalLemma42 hPmax hNmax k ⟨hambient⟩
    rcases hPiso with ⟨hPiso⟩
    change Lattice.Represents M.form X.form M.lattice X.lattice
    exact ⟨hsplit.toRepresentation.trans
      (Classical.choice htowerRep) |>.trans hPiso.toRepresentation |>.trans
      (Classical.choice (represents_of_le X.form hXP))⟩

end Lattice

end Bong
