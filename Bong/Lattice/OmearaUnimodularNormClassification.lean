/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaHyperbolicSummandCancellation
import Bong.Lattice.ModularOrthogonalProduct
import Bong.Lattice.ProjectionScaling
import Bong.Lattice.OrthogonalSupScale
import Bong.QuadraticSpace.OrthogonalSumDiagonal

/-!
# O'Meara 93:16: unimodular lattices and their norm groups

This file develops the stable-hyperbolic proof of O'Meara 93:16.  The
auxiliary results below are deliberately stated independently: negating a
form preserves duality and the norm group, the norm group of an orthogonal
product is the Minkowski sum of the two norm groups, and `q ⊥ (-q)` is
identified explicitly with a finite hyperbolic tower.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w x

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-! ## Negating the ambient form -/

/-- The scale ideal is unchanged when the quadratic form is negated. -/
theorem scaleIdeal_rescaleUnit_neg_one (q : QuadraticSpace K V)
    (L : Lattice K V) :
    scaleIdeal (q.rescaleUnit (-1 : Kˣ)) L = scaleIdeal q L := by
  apply le_antisymm
  · apply scaleIdeal_le_of_bilin_mem
    intro x y hx hy
    simpa only [QuadraticSpace.rescaleUnit_bilin_apply,
      Units.val_neg, Units.val_one, neg_one_mul] using
        (scaleIdeal q L).neg_mem
          (bilin_mem_scaleIdeal_of_mem q L hx hy)
  · apply scaleIdeal_le_of_bilin_mem
    intro x y hx hy
    have h := bilin_mem_scaleIdeal_of_mem
      (q.rescaleUnit (-1 : Kˣ)) L hx hy
    have hn := (scaleIdeal (q.rescaleUnit (-1 : Kˣ)) L).neg_mem h
    simpa only [QuadraticSpace.rescaleUnit_bilin_apply,
      Units.val_neg, Units.val_one, neg_one_mul, neg_neg] using hn

/-- The error ideal `2sL` is unchanged when the form is negated. -/
theorem twoScaleIdeal_rescaleUnit_neg_one (q : QuadraticSpace K V)
    (L : Lattice K V) :
    twoScaleIdeal (q.rescaleUnit (-1 : Kˣ)) L = twoScaleIdeal q L := by
  unfold twoScaleIdeal
  rw [scaleIdeal_rescaleUnit_neg_one]

/-- Integral duality is unchanged when the form is negated. -/
theorem dualLattice_rescaleUnit_neg_one (q : QuadraticSpace K V)
    (L : Lattice K V) :
    dualLattice (q.rescaleUnit (-1 : Kˣ)) L = dualLattice q L := by
  apply Lattice.ext
  apply Submodule.ext
  intro x
  change x ∈ dualLattice (q.rescaleUnit (-1 : Kˣ)) L ↔
    x ∈ dualLattice q L
  rw [mem_dualLattice_iff, mem_dualLattice_iff]
  constructor
  · intro hx y hy
    have h := hx y hy
    simp only [QuadraticSpace.rescaleUnit_bilin_apply,
      Units.val_neg, Units.val_one, neg_one_mul] at h
    simpa using (IntegerRing K).neg_mem (-(q.bilin x y)) h
  · intro hx y hy
    have h := hx y hy
    simpa only [QuadraticSpace.rescaleUnit_bilin_apply,
      Units.val_neg, Units.val_one, neg_one_mul] using
        ((IntegerRing K).neg_mem (q.bilin x y) h)

/-- Unimodularity is invariant under negating the form. -/
theorem isUnimodular_rescaleUnit_neg_one_iff
    (q : QuadraticSpace K V) (L : Lattice K V) :
    IsUnimodular (q.rescaleUnit (-1 : Kˣ)) L ↔ IsUnimodular q L := by
  rw [isUnimodular_iff_dualLattice_eq,
    isUnimodular_iff_dualLattice_eq,
    dualLattice_rescaleUnit_neg_one]

/-- A lattice and the same lattice equipped with the negative form have the
same norm group. -/
theorem normGroupSet_rescaleUnit_neg_one
    (q : QuadraticSpace K V) (L : Lattice K V) :
    normGroupSet (q.rescaleUnit (-1 : Kˣ)) L = normGroupSet q L := by
  rw [Set.ext_iff]
  intro z
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    rw [twoScaleIdeal_rescaleUnit_neg_one] at hy
    have hqx : q.quadratic x ∈ normGroupSet q L :=
      ⟨x, hx, 0, (twoScaleIdeal q L).zero_mem, by simp⟩
    have hy' : y ∈ normGroupSet q L :=
      twoScaleIdeal_subset_normGroupSet q L hy
    simp only [QuadraticSpace.rescaleUnit_quadratic,
      Units.val_neg, Units.val_one, neg_one_mul]
    exact add_mem_normGroupSet q L (neg_mem_normGroupSet q L hqx) hy'
  · intro hz
    have hneg : -z ∈ normGroupSet q L := neg_mem_normGroupSet q L hz
    rcases hneg with ⟨x, hx, y, hy, hvalue⟩
    refine ⟨x, hx, -y, ?_, ?_⟩
    · rw [twoScaleIdeal_rescaleUnit_neg_one]
      exact (twoScaleIdeal q L).neg_mem hy
    · simp only [QuadraticSpace.rescaleUnit_quadratic,
        Units.val_neg, Units.val_one, neg_one_mul]
      calc
        z = -(-z) := by simp
        _ = -(q.quadratic x + y) := congrArg Neg.neg hvalue
        _ = -(q.quadratic x) + -y := by ring

/-! ## Orthogonal products -/

/-- The error ideal of an orthogonal product is the supremum of the two
factor error ideals. -/
theorem twoScaleIdeal_orthogonalProduct :
    twoScaleIdeal (q.orthogonalSum r) (product L M) =
      twoScaleIdeal q L ⊔ twoScaleIdeal r M := by
  unfold twoScaleIdeal twiceIdeal
  rw [scaleIdeal_orthogonalProduct, Submodule.map_sup]

/-- The norm group of an orthogonal product is the Minkowski sum of the two
factor norm groups. -/
theorem mem_normGroupSet_orthogonalProduct_iff (z : K) :
    z ∈ normGroupSet (q.orthogonalSum r) (product L M) ↔
      ∃ a ∈ normGroupSet q L, ∃ b ∈ normGroupSet r M, z = a + b := by
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    rw [twoScaleIdeal_orthogonalProduct] at hy
    rcases Submodule.mem_sup.mp hy with ⟨yL, hyL, yM, hyM, hySum⟩
    refine ⟨q.quadratic x.1 + yL,
      ⟨x.1, (mem_product_iff.mp hx).1, yL, hyL, rfl⟩,
      r.quadratic x.2 + yM,
      ⟨x.2, (mem_product_iff.mp hx).2, yM, hyM, rfl⟩, ?_⟩
    rw [QuadraticSpace.orthogonalSum_quadratic_apply, ← hySum]
    ring
  · rintro ⟨a, ⟨x, hx, yL, hyL, rfl⟩,
      b, ⟨w, hw, yM, hyM, rfl⟩, rfl⟩
    refine ⟨(x, w), mem_product_iff.mpr ⟨hx, hw⟩,
      yL + yM, ?_, ?_⟩
    · rw [twoScaleIdeal_orthogonalProduct]
      exact Submodule.add_mem_sup hyL hyM
    · rw [QuadraticSpace.orthogonalSum_quadratic_apply]
      ring

/-- Set-valued form of the orthogonal-product norm-group formula. -/
theorem normGroupSet_orthogonalProduct :
    normGroupSet (q.orthogonalSum r) (product L M) =
      {z | ∃ a ∈ normGroupSet q L,
        ∃ b ∈ normGroupSet r M, z = a + b} := by
  ext z
  exact mem_normGroupSet_orthogonalProduct_iff z

/-! ## An explicit hyperbolic model for `q ⊥ (-q)` -/

/-- The two coordinates which turn the diagonal pair `[c,-c]` into a
standard hyperbolic plane. -/
noncomputable def diagonalDifferenceHeadLinearEquiv (c : Kˣ) :
    (K × K) ≃ₗ[K] (Fin 2 → K) where
  toFun x := ![x.1 + x.2, ((c : K) / 2) * (x.1 - x.2)]
  invFun x :=
    ((x 0 + (2 / (c : K)) * x 1) / 2,
      (x 0 - (2 / (c : K)) * x 1) / 2)
  left_inv x := by
    apply Prod.ext <;> simp
    · field_simp [Units.ne_zero c]
      ring
    · field_simp [Units.ne_zero c]
      ring
  right_inv x := by
    funext i
    fin_cases i <;> simp
    · field_simp [Units.ne_zero c]
      ring
    · field_simp [Units.ne_zero c]
      ring
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp <;> ring

/-- Regroup two head-tail pairs into a pair of heads and a pair of tails. -/
noncomputable def diagonalDifferenceRegroupLinearEquiv
    {X : Type*} [AddCommGroup X] [Module K X] :
    ((K × X) × (K × X)) ≃ₗ[K] ((K × K) × (X × X)) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' a x := rfl

/-- Interleave a diagonal form and its negative into a nested hyperbolic
tower. -/
noncomputable def diagonalDifferenceLinearEquiv :
    (n : Nat) → (c : Fin n → Kˣ) →
      ((Fin n → K) × (Fin n → K)) ≃ₗ[K]
        HyperbolicExtension K (Fin 0 → K) n
  | 0, _ =>
      { toFun := fun _ => 0
        invFun := fun _ => (0, 0)
        left_inv := by
          intro x
          apply Prod.ext <;> funext i <;> exact Fin.elim0 i
        right_inv := by
          intro x
          funext i
          exact Fin.elim0 i
        map_add' := by intros; simp
        map_smul' := by intros; simp }
  | n + 1, c => by
      let split : ((Fin (n + 1) → K) × (Fin (n + 1) → K)) ≃ₗ[K]
          ((K × (Fin n → K)) × (K × (Fin n → K))) :=
        (Fin.consLinearEquiv K (fun _ : Fin (n + 1) => K)).symm.prodCongr
          (Fin.consLinearEquiv K (fun _ : Fin (n + 1) => K)).symm
      let regroup :=
        diagonalDifferenceRegroupLinearEquiv (K := K) (X := Fin n → K)
      let headTail :=
        (diagonalDifferenceHeadLinearEquiv (K := K) (c 0)).prodCongr
          (diagonalDifferenceLinearEquiv n (Fin.tail c))
      exact split.trans (regroup.trans headTail)

@[simp]
theorem diagonalDifferenceLinearEquiv_zero_apply
    (c : Fin 0 → Kˣ) (x : (Fin 0 → K) × (Fin 0 → K)) :
    diagonalDifferenceLinearEquiv 0 c x = 0 :=
  rfl

@[simp]
theorem diagonalDifferenceLinearEquiv_succ_fst
    (n : Nat) (c : Fin (n + 1) → Kˣ)
    (x : (Fin (n + 1) → K) × (Fin (n + 1) → K)) :
    (diagonalDifferenceLinearEquiv (n + 1) c x).1 =
      diagonalDifferenceHeadLinearEquiv (K := K) (c 0) (x.1 0, x.2 0) := by
  rfl

@[simp]
theorem diagonalDifferenceLinearEquiv_succ_snd
    (n : Nat) (c : Fin (n + 1) → Kˣ)
    (x : (Fin (n + 1) → K) × (Fin (n + 1) → K)) :
    (diagonalDifferenceLinearEquiv (n + 1) c x).2 =
      diagonalDifferenceLinearEquiv n (Fin.tail c)
        (Fin.tail x.1, Fin.tail x.2) := by
  rfl

@[simp]
theorem diagonalDifferenceHeadLinearEquiv_bilin
    (c : Kˣ) (x y : K × K) :
    (QuadraticSpace.hyperbolicPlane (1 : Kˣ)).bilin
      (diagonalDifferenceHeadLinearEquiv (K := K) c x)
      (diagonalDifferenceHeadLinearEquiv (K := K) c y) =
        (c : K) * x.1 * y.1 + (-(c : K)) * x.2 * y.2 := by
  rw [QuadraticSpace.hyperbolicPlane_bilin_apply]
  simp [diagonalDifferenceHeadLinearEquiv]
  field_simp
  ring

/-- The preceding coordinate equivalence is an isometry from a diagonal
space and its negative to the standard hyperbolic tower. -/
noncomputable def diagonalDifferenceHyperbolicIsometry
    (n : Nat) (c : Fin n → Kˣ) :
    QuadraticSpace.Isometry
      ((QuadraticSpace.finiteDiagonal
        (BONG.GoodBONG.diagonalUnitCoefficients c)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero c)).orthogonalSum
       (QuadraticSpace.finiteDiagonal
        (BONG.GoodBONG.diagonalUnitCoefficients (fun i => -(c i)))
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero (fun i => -(c i)))))
      (hyperbolicExtensionForm
        (zeroCoordinateQuadraticSpace (K := K)) n) where
  toLinearEquiv := diagonalDifferenceLinearEquiv n c
  map_bilin := by
    intro x y
    induction n with
    | zero =>
        simp [hyperbolicExtensionForm,
          QuadraticSpace.orthogonalSum_bilin_apply,
          QuadraticSpace.finiteDiagonal_bilin_apply,
          zeroCoordinateQuadraticSpace]
    | succ n ih =>
        rw [QuadraticSpace.orthogonalSum_bilin_apply,
          QuadraticSpace.finiteDiagonal_bilin_apply,
          QuadraticSpace.finiteDiagonal_bilin_apply]
        simp only [Fin.sum_univ_succ, BONG.GoodBONG.diagonalUnitCoefficients]
        simp only [hyperbolicExtensionForm,
          QuadraticSpace.orthogonalSum_bilin_apply,
          diagonalDifferenceLinearEquiv_succ_fst,
          diagonalDifferenceLinearEquiv_succ_snd]
        change
          (QuadraticSpace.hyperbolicPlane (1 : Kˣ)).bilin
              (diagonalDifferenceHeadLinearEquiv (K := K) (c 0)
                (x.1 0, x.2 0))
              (diagonalDifferenceHeadLinearEquiv (K := K) (c 0)
                (y.1 0, y.2 0)) +
            (hyperbolicExtensionForm
              (zeroCoordinateQuadraticSpace (K := K)) n).bilin
              (diagonalDifferenceLinearEquiv n (Fin.tail c)
                (Fin.tail x.1, Fin.tail x.2))
              (diagonalDifferenceLinearEquiv n (Fin.tail c)
                (Fin.tail y.1, Fin.tail y.2)) = _
        rw [diagonalDifferenceHeadLinearEquiv_bilin]
        have htail := ih (c := Fin.tail c)
          (x := (Fin.tail x.1, Fin.tail x.2))
          (y := (Fin.tail y.1, Fin.tail y.2))
        simp only [QuadraticSpace.orthogonalSum_bilin_apply,
          QuadraticSpace.finiteDiagonal_bilin_apply,
          BONG.GoodBONG.diagonalUnitCoefficients,
          Units.val_neg] at htail
        rw [htail]
        simp only [Units.val_neg, Fin.tail]
        ring

/-- The chosen orthogonal coordinates for the negative form use the same
basis as those for `q`, with all diagonal coefficients negated. -/
noncomputable def negatedDiagonalizationIsometry
    [FiniteDimensional K V] (q : QuadraticSpace K V) :
    QuadraticSpace.Isometry (q.rescaleUnit (-1 : Kˣ))
      (QuadraticSpace.finiteDiagonal
        (BONG.GoodBONG.diagonalUnitCoefficients
          (fun i => -(q.diagonalUnits i)))
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero
          (fun i => -(q.diagonalUnits i)))) where
  toLinearEquiv := q.orthogonalFinBasis.equivFun
  map_bilin := by
    intro x y
    have h := q.diagonalizationIsometry.map_bilin x y
    change
      (QuadraticSpace.finiteDiagonal
        (BONG.GoodBONG.diagonalUnitCoefficients q.diagonalUnits)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero q.diagonalUnits)).bilin
          (q.orthogonalFinBasis.equivFun x)
          (q.orthogonalFinBasis.equivFun y) = q.bilin x y at h
    rw [QuadraticSpace.finiteDiagonal_bilin_apply] at h ⊢
    simp only [BONG.GoodBONG.diagonalUnitCoefficients,
      Units.val_neg]
    rw [QuadraticSpace.rescaleUnit_bilin_apply]
    simp only [Units.val_neg, Units.val_one, neg_one_mul]
    rw [← h]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [BONG.GoodBONG.diagonalUnitCoefficients]
    ring

/-- Exchange the two factors of an orthogonal sum at the quadratic-space
level. -/
noncomputable def quadraticOrthogonalSumSwap
    (q : QuadraticSpace K V) (r : QuadraticSpace K W) :
    QuadraticSpace.Isometry (q.orthogonalSum r) (r.orthogonalSum q) where
  toLinearEquiv := LinearEquiv.prodComm K V W
  map_bilin := by
    intro x y
    rw [QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.orthogonalSum_bilin_apply]
    exact add_comm _ _

/-- Every doubled space `q ⊥ (-q)` is explicitly hyperbolic. -/
noncomputable def quadraticNegativeHyperbolicIsometry
    [FiniteDimensional K V] (q : QuadraticSpace K V) :
    QuadraticSpace.Isometry
      (q.orthogonalSum (q.rescaleUnit (-1 : Kˣ)))
      (hyperbolicExtensionForm (zeroCoordinateQuadraticSpace (K := K))
        (finrank K V)) :=
  (q.diagonalizationIsometry.orthogonalSum
    (negatedDiagonalizationIsometry q)).trans
      (diagonalDifferenceHyperbolicIsometry (finrank K V) q.diagonalUnits)

/-- The same hyperbolic identification with the negative factor written
first. -/
noncomputable def negativeQuadraticHyperbolicIsometry
    [FiniteDimensional K V] (q : QuadraticSpace K V) :
    QuadraticSpace.Isometry
      ((q.rescaleUnit (-1 : Kˣ)).orthogonalSum q)
      (hyperbolicExtensionForm (zeroCoordinateQuadraticSpace (K := K))
        (finrank K V)) :=
  (quadraticOrthogonalSumSwap (q.rescaleUnit (-1 : Kˣ)) q).trans
    (quadraticNegativeHyperbolicIsometry q)

/-! ## Norm groups used in the stable proof -/

/-- If the two factors have the same norm group, their orthogonal product
has that same norm group. -/
theorem normGroupSet_orthogonalProduct_eq_of_eq
    (hgroup : normGroupSet q L = normGroupSet r M) :
    normGroupSet (q.orthogonalSum r) (product L M) =
      normGroupSet q L := by
  ext z
  rw [mem_normGroupSet_orthogonalProduct_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [← hgroup] at hb
    exact add_mem_normGroupSet q L ha hb
  · intro hz
    refine ⟨z, hz, 0, ?_, by simp⟩
    exact zero_mem_normGroupSet r M

/-- The hyperbolic double of a lattice has the same norm group as the
original lattice. -/
theorem normGroupSet_quadraticNegativeProduct
    (q : QuadraticSpace K V) (L : Lattice K V) :
    normGroupSet
      (q.orthogonalSum (q.rescaleUnit (-1 : Kˣ))) (product L L) =
        normGroupSet q L := by
  apply normGroupSet_orthogonalProduct_eq_of_eq
  exact (normGroupSet_rescaleUnit_neg_one q L).symm

/-- Mixed version used after assuming equality of the two original norm
groups. -/
theorem normGroupSet_negativeMixedProduct
    {N : Lattice K V}
    (hgroup : normGroupSet q L = normGroupSet q N) :
    normGroupSet
      ((q.rescaleUnit (-1 : Kˣ)).orthogonalSum q) (product L N) =
        normGroupSet q L := by
  calc
    normGroupSet
        ((q.rescaleUnit (-1 : Kˣ)).orthogonalSum q) (product L N) =
        normGroupSet (q.rescaleUnit (-1 : Kˣ)) L :=
      normGroupSet_orthogonalProduct_eq_of_eq
        ((normGroupSet_rescaleUnit_neg_one q L).trans hgroup)
    _ = normGroupSet q L := normGroupSet_rescaleUnit_neg_one q L

/-- At scale one, O'Meara's scale truncation of a unimodular lattice is the
lattice itself. -/
theorem omearaScaleTruncation_one_eq_of_unimodular
    (hL : IsUnimodular q L) :
    omearaScaleTruncation q L (1 : Kˣ) = L := by
  rw [omearaScaleTruncation]
  have hdual : dualLattice (q.rescaleUnit (1 : Kˣ)) L = L := by
    apply Lattice.ext
    apply Submodule.ext
    intro x
    change x ∈ dualLattice (q.rescaleUnit (1 : Kˣ)) L ↔ x ∈ L
    rw [mem_dualLattice_iff]
    have hLdual := (isUnimodular_iff_dualLattice_eq q L).mp hL
    have hxdual : x ∈ dualLattice q L ↔ x ∈ L := by rw [hLdual]
    rw [← hxdual, mem_dualLattice_iff]
    constructor <;> intro hx y hy
    · simpa only [QuadraticSpace.rescaleUnit_bilin_apply,
        Units.val_one, one_mul] using hx y hy
    · simpa only [QuadraticSpace.rescaleUnit_bilin_apply,
        Units.val_one, one_mul] using hx y hy
  simp only [inv_one]
  rw [hdual]
  apply Lattice.ext
  apply Submodule.ext
  intro x
  change x ∈ inf L L ↔ x ∈ L
  simp only [mem_inf_iff, and_self]

/-! ## Stable normalization over an external complement -/

/-- Two unimodular lattices on the same finite hyperbolic tower become
isometric after adjoining a complement whose truncated norm group contains
both tower norm groups.  This is the exact stable-normalization step used in
the proof of 93:16. -/
noncomputable def stableHyperbolicModularProductIsometry
    {n : Nat}
    {X : Type u} [AddCommGroup X] [Module K X]
    {J₁ J₂ : Lattice K
      (HyperbolicExtension K (Fin 0 → K) n)}
    (hJ₁ : IsModular
      (hyperbolicExtensionForm (zeroCoordinateQuadraticSpace (K := K)) n)
      J₁ (1 : Kˣ))
    (hJ₂ : IsModular
      (hyperbolicExtensionForm (zeroCoordinateQuadraticSpace (K := K)) n)
      J₂ (1 : Kˣ))
    (q : QuadraticSpace K X) (L : Lattice K X)
    (hgroup₁ : normGroupSet
        (hyperbolicExtensionForm (zeroCoordinateQuadraticSpace (K := K)) n)
        J₁ ⊆
      normGroupSet q (omearaScaleTruncation q L (1 : Kˣ)))
    (hgroup₂ : normGroupSet
        (hyperbolicExtensionForm (zeroCoordinateQuadraticSpace (K := K)) n)
        J₂ ⊆
      normGroupSet q (omearaScaleTruncation q L (1 : Kˣ))) :
    Isometry
      ((hyperbolicExtensionForm
        (zeroCoordinateQuadraticSpace (K := K)) n).orthogonalSum q)
      ((hyperbolicExtensionForm
        (zeroCoordinateQuadraticSpace (K := K)) n).orthogonalSum q)
      (product J₁ L) (product J₂ L) := by
  let D₁ := hyperbolicModularDecomposition
    (zeroCoordinateQuadraticSpace (K := K)) (1 : Kˣ) n J₁ hJ₁
  let D₂ := hyperbolicModularDecomposition
    (zeroCoordinateQuadraticSpace (K := K)) (1 : Kˣ) n J₂ hJ₂
  let append₁ := omearaPlaneExtensionAppendIsometry
    D₁.tailLattice q L (1 : Kˣ) n D₁.coefficient
  let append₂ := omearaPlaneExtensionAppendIsometry
    D₂.tailLattice q L (1 : Kˣ) n D₂.coefficient
  let displayed₁ := append₁.symm.trans
    (D₁.isometry.orthogonalProductBasic (Isometry.refl q L))
  let displayed₂ := append₂.symm.trans
    (D₂.isometry.orthogonalProductBasic (Isometry.refl q L))
  have hcoefficient₁ : ∀ i, ((1 : Kˣ) : K) * D₁.coefficient i ∈
      normGroupSet q (omearaScaleTruncation q L (1 : Kˣ)) := by
    intro i
    exact hgroup₁ (D₁.coefficient_mem_targetNormGroup i)
  have hcoefficient₂ : ∀ i, ((1 : Kˣ) : K) * D₂.coefficient i ∈
      normGroupSet q (omearaScaleTruncation q L (1 : Kˣ)) := by
    intro i
    exact hgroup₂ (D₂.coefficient_mem_targetNormGroup i)
  let normalize₁ := normalizeScaledOmearaPlaneExtension
    q L (1 : Kˣ) n D₁.coefficient hcoefficient₁
  let normalize₂ := normalizeScaledOmearaPlaneExtension
    q L (1 : Kˣ) n D₂.coefficient hcoefficient₂
  let zeroToJ₁ := normalize₁.symm.trans displayed₁
  let zeroToJ₂ := normalize₂.symm.trans displayed₂
  exact zeroToJ₁.symm.trans zeroToJ₂

/-! ## O'Meara 93:16 -/

section Omeara9316

variable {X : Type u} [AddCommGroup X] [Module K X]
  {p : QuadraticSpace K X} {A B : Lattice K X}

/-- O'Meara 93:16, constructive direction: unimodular lattices on the
same quadratic space with equal norm groups are integrally isometric.

The proof is O'Meara's published stable argument.  It identifies
`p ⊥ (-p)` with a hyperbolic tower, normalizes the two middle doubled
lattices by 93:13, and finally applies 93:14a to remove the common doubled
summand. -/
noncomputable def omeara9316_of_normGroupSet_eq
    (hA : IsUnimodular p A) (hB : IsUnimodular p B)
    (hgroup : normGroupSet p A = normGroupSet p B) :
    Isometry p p A B := by
  letI : FiniteDimensional K X :=
    A.ambientBasis.finiteDimensional_of_finite
  let negative := p.rescaleUnit (-1 : Kˣ)
  let hyperbolic := hyperbolicExtensionForm
    (zeroCoordinateQuadraticSpace (K := K)) (finrank K X)
  have hnegativeA : IsUnimodular negative A := by
    exact (isUnimodular_rescaleUnit_neg_one_iff p A).mpr hA
  have hnegativeB : IsUnimodular negative B := by
    exact (isUnimodular_rescaleUnit_neg_one_iff p B).mpr hB

  -- The two middle lattices `(-A) ⊥ A` and `(-A) ⊥ B`.
  let middleA : Lattice K (X × X) := product A A
  let middleB : Lattice K (X × X) := product A B
  let middleAmbient := negative.orthogonalSum p
  let middleToHyperbolic : QuadraticSpace.Isometry middleAmbient hyperbolic :=
    negativeQuadraticHyperbolicIsometry p
  let middleModelA := map middleToHyperbolic.toLinearEquiv middleA
  let middleModelB := map middleToHyperbolic.toLinearEquiv middleB
  let middleAIsometry :=
    Isometry.toMap middleAmbient middleToHyperbolic middleA
  let middleBIsometry :=
    Isometry.toMap middleAmbient middleToHyperbolic middleB
  have hmiddleA : IsUnimodular middleAmbient middleA :=
    hnegativeA.orthogonalProduct hA
  have hmiddleB : IsUnimodular middleAmbient middleB :=
    hnegativeA.orthogonalProduct hB
  have hmiddleModelA : IsModular hyperbolic middleModelA (1 : Kˣ) :=
    hmiddleA.mapLatticeIsometry middleAIsometry
  have hmiddleModelB : IsModular hyperbolic middleModelB (1 : Kˣ) :=
    hmiddleB.mapLatticeIsometry middleBIsometry
  have hmiddleGroupA : normGroupSet hyperbolic middleModelA =
      normGroupSet p A := by
    calc
      normGroupSet hyperbolic middleModelA =
          normGroupSet middleAmbient middleA :=
        normGroupSet_eq_of_latticeIsometry middleAIsometry
      _ = normGroupSet p A :=
        normGroupSet_negativeMixedProduct (L := A) (N := A) rfl
  have hmiddleGroupB : normGroupSet hyperbolic middleModelB =
      normGroupSet p A := by
    calc
      normGroupSet hyperbolic middleModelB =
          normGroupSet middleAmbient middleB :=
        normGroupSet_eq_of_latticeIsometry middleBIsometry
      _ = normGroupSet p A :=
        normGroupSet_negativeMixedProduct (L := A) (N := B) hgroup
  have htruncA : omearaScaleTruncation p A (1 : Kˣ) = A :=
    omearaScaleTruncation_one_eq_of_unimodular hA
  have hmiddleContainA : normGroupSet hyperbolic middleModelA ⊆
      normGroupSet p (omearaScaleTruncation p A (1 : Kˣ)) := by
    rw [hmiddleGroupA, htruncA]
  have hmiddleContainB : normGroupSet hyperbolic middleModelB ⊆
      normGroupSet p (omearaScaleTruncation p A (1 : Kˣ)) := by
    rw [hmiddleGroupB, htruncA]
  let middleStable := stableHyperbolicModularProductIsometry
    hmiddleModelA hmiddleModelB p A hmiddleContainA hmiddleContainB
  let middleAWithA :=
    middleAIsometry.orthogonalProductBasic (Isometry.refl p A)
  let middleBWithA :=
    middleBIsometry.orthogonalProductBasic (Isometry.refl p A)
  let stabilizedMiddle : Isometry
      (middleAmbient.orthogonalSum p) (middleAmbient.orthogonalSum p)
      (product middleA A) (product middleB A) :=
    middleAWithA.trans (middleStable.trans middleBWithA.symm)

  -- Reorder the three displayed factors so that the common summand is
  -- `(A ⊥ -A)` on both sides.
  let commonSummand : Lattice K (X × X) := product A A
  let commonAmbient := p.orthogonalSum negative
  let commonToMiddle : Isometry
      (commonAmbient.orthogonalSum p) (middleAmbient.orthogonalSum p)
      (product commonSummand A) (product middleA A) :=
    (orthogonalProductSwap
      (q := p) (r := negative) (L := A) (M := A)).orthogonalProductBasic
        (Isometry.refl p A)
  let targetAssoc : Isometry
      (middleAmbient.orthogonalSum p)
      (negative.orthogonalSum (p.orthogonalSum p))
      (product middleB A) (product A (product B A)) :=
    orthogonalProductAssoc
  let targetInnerSwap : Isometry
      (negative.orthogonalSum (p.orthogonalSum p))
      (negative.orthogonalSum (p.orthogonalSum p))
      (product A (product B A)) (product A (product A B)) :=
    (Isometry.refl negative A).orthogonalProductBasic
      (orthogonalProductSwap
        (q := p) (r := p) (L := B) (M := A))
  let targetRotate : Isometry
      (negative.orthogonalSum (p.orthogonalSum p))
      ((p.orthogonalSum negative).orthogonalSum p)
      (product A (product A B)) (product (product A A) B) :=
    orthogonalProductRotateLeft
  let targetPermutation :=
    targetAssoc.trans (targetInnerSwap.trans targetRotate)
  let total : Isometry
      (commonAmbient.orthogonalSum p) (commonAmbient.orthogonalSum p)
      (product commonSummand A) (product commonSummand B) :=
    commonToMiddle.trans (stabilizedMiddle.trans targetPermutation)

  -- Put the common doubled summand in the explicit hyperbolic model and
  -- invoke the already proved abstract form of 93:14a.
  let commonToHyperbolic : QuadraticSpace.Isometry commonAmbient hyperbolic :=
    quadraticNegativeHyperbolicIsometry p
  let commonModel := map commonToHyperbolic.toLinearEquiv commonSummand
  let commonIsometry :=
    Isometry.toMap commonAmbient commonToHyperbolic commonSummand
  have hcommon : IsUnimodular commonAmbient commonSummand :=
    hA.orthogonalProduct hnegativeA
  have hcommonModel : IsModular hyperbolic commonModel (1 : Kˣ) :=
    hcommon.mapLatticeIsometry commonIsometry
  have hcommonGroup : normGroupSet commonAmbient commonSummand =
      normGroupSet p A := normGroupSet_quadraticNegativeProduct p A
  have hcancelA : normGroupSet commonAmbient commonSummand ⊆
      normGroupSet p (omearaScaleTruncation p A (1 : Kˣ)) := by
    rw [hcommonGroup, htruncA]
  have htruncB : omearaScaleTruncation p B (1 : Kˣ) = B :=
    omearaScaleTruncation_one_eq_of_unimodular hB
  have hcancelB : normGroupSet commonAmbient commonSummand ⊆
      normGroupSet p (omearaScaleTruncation p B (1 : Kˣ)) := by
    rw [hcommonGroup, htruncB, hgroup]
  exact omeara9314a_abstract (1 : Kˣ)
    commonModel commonModel hcommonModel hcommonModel
    commonIsometry.symm commonIsometry.symm hcancelA hcancelB total

/-- O'Meara 93:16 in equivalence form. -/
theorem omeara9316
    (hA : IsUnimodular p A) (hB : IsUnimodular p B) :
    IsIsometric p p A B ↔ normGroupSet p A = normGroupSet p B := by
  constructor
  · rintro ⟨f⟩
    exact (normGroupSet_eq_of_latticeIsometry f).symm
  · intro hgroup
    exact ⟨omeara9316_of_normGroupSet_eq hA hB hgroup⟩

end Omeara9316

end Lattice

end Bong
