/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009OrthogonalIdealProof
import Bong.Bong.Beli2009BinaryWeightProof
import Bong.Bong.Beli2009AlphaLocalizationProof
import Bong.Bong.BeliCorollary44ScaleProof
import Bong.Bong.BasisLattice

/-!
# Beli (2009), Lemma 2.14: base calculations

This file evaluates O'Meara's proved weight ideal on a good BONG.  The first
part treats a unary lattice directly from its integral BONG coordinate.  The
higher-rank calculation is developed below from the one- and two-block
splittings of Beli (2003), Corollary 4.4.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice

/-- A two-element indexed supremum is an ordinary binary supremum. -/
theorem iSup_fin_two_eq_sup {α : Type*} [CompleteLattice α]
    (f : Fin 2 → α) : (⨆ i, f i) = f 0 ⊔ f 1 := by
  apply le_antisymm
  · apply iSup_le
    intro i
    fin_cases i
    · exact _root_.le_sup_left
    · exact _root_.le_sup_right
  · exact _root_.sup_le (le_iSup f 0) (le_iSup f 1)

/-- Remove a zero first component from a three-component orthogonal
decomposition.  This is the boundary form needed when Corollary 4.4(ii) is
applied to the first adjacent pair. -/
noncomputable def OrthogonalDecomposition.dropFirstZeroFinThree
    (D : OrthogonalDecomposition q L 3)
    (hzero : (D.component 0).ambientSubmodule = ⊥) :
    OrthogonalDecomposition q L 2 where
  component := fun i => D.component i.succ
  orthogonal := by
    intro i j hij x y
    apply D.orthogonal i.succ j.succ
    intro h
    exact hij (Fin.succ_inj.mp h)
  sum_eq := by
    rw [iSup_fin_two_eq_sup]
    change (D.component 1).ambientSubmodule ⊔
      (D.component 2).ambientSubmodule = L.toSubmodule
    rw [← D.sum_eq, iSup_fin_three, hzero, bot_sup_eq]

@[simp]
theorem OrthogonalDecomposition.dropFirstZeroFinThree_component_zero
    (D : OrthogonalDecomposition q L 3)
    (hzero : (D.component 0).ambientSubmodule = ⊥) :
    (D.dropFirstZeroFinThree hzero).component 0 = D.component 1 := by
  rfl

@[simp]
theorem OrthogonalDecomposition.dropFirstZeroFinThree_component_one
    (D : OrthogonalDecomposition q L 3)
    (hzero : (D.component 0).ambientSubmodule = ⊥) :
    (D.dropFirstZeroFinThree hzero).component 1 = D.component 2 := by
  rfl

namespace OrthogonalDecomposition

variable [Beli2009WeightIdealData.{u, v} K]

/-- Lemma 2.11 specialized to two components when the ambient norm
generator is also the chosen generator of the first component.  The
self-defect is a square and therefore disappears. -/
theorem weightIdeal_eq_sup_components_defect_fin_two
    (D : OrthogonalDecomposition q L 2) (a c : Kˣ)
    (ha : IsNormGeneratorValue q L a)
    (hzero : IsNormGeneratorValue
      (D.component 0).space (D.component 0).lattice a)
    (hone : IsNormGeneratorValue
      (D.component 1).space (D.component 1).lattice c) :
    weightIdeal q L =
      weightIdeal (D.component 0).space (D.component 0).lattice ⊔
        weightIdeal (D.component 1).space (D.component 1).lattice ⊔
          scalarIdeal ((a⁻¹ : Kˣ) : K)
            (quadraticDefectIdeal (a * c)) ⊔
              twoScaleIdeal q L := by
  let ak : Fin 2 → Kˣ := fun i => Fin.cases a (fun _ => c) i
  have hak : ∀ i, IsNormGeneratorValue
      (D.component i).space (D.component i).lattice (ak i) := by
    intro i
    fin_cases i
    · exact hzero
    · exact hone
  have hweight := D.weightIdeal_eq_weightIdealExpression a ha ak hak
  have hcomponent : D.componentWeightSum =
      weightIdeal (D.component 0).space (D.component 0).lattice ⊔
        weightIdeal (D.component 1).space (D.component 1).lattice := by
    unfold componentWeightSum
    exact iSup_fin_two_eq_sup _
  have hsquare : IsSquare (a * a) := by
    refine ⟨a, ?_⟩
    simp [pow_two]
  have htop : quadraticDefect K (a * a) = ⊤ :=
    quadraticDefect_eq_top_of_isSquare K hsquare
  have hdefect : D.componentDefectSum a ak =
      scalarIdeal ((a⁻¹ : Kˣ) : K)
        (quadraticDefectIdeal (a * c)) := by
    unfold componentDefectSum
    rw [iSup_fin_two_eq_sup]
    change scalarIdeal ((a⁻¹ : Kˣ) : K)
          (quadraticDefectIdeal (a * a)) ⊔
        scalarIdeal ((a⁻¹ : Kˣ) : K)
          (quadraticDefectIdeal (a * c)) = _
    rw [scaledQuadraticDefectIdeal_eq_bot_of_eq_top a a htop,
      bot_sup_eq]
  rw [hweight]
  unfold weightIdealExpression
  rw [hcomponent, hdefect]

/-- Order form of the two-component formula when the cross square class is
a square.  The ambient `2s` term is redundant once it is contained in the
first component weight. -/
theorem weightIdealOrder_eq_min_components_of_defect_eq_top_fin_two
    (D : OrthogonalDecomposition q L 2) (a c : Kˣ)
    (ha : IsNormGeneratorValue q L a)
    (hzero : IsNormGeneratorValue
      (D.component 0).space (D.component 0).lattice a)
    (hone : IsNormGeneratorValue
      (D.component 1).space (D.component 1).lattice c)
    (htwo : twoScaleIdeal q L ≤
      weightIdeal (D.component 0).space (D.component 0).lattice)
    (htop : quadraticDefect K (a * c) = ⊤) :
    weightIdealOrder q L =
      min
        (weightIdealOrder (D.component 0).space (D.component 0).lattice)
        (weightIdealOrder (D.component 1).space
          (D.component 1).lattice) := by
  have hweight := D.weightIdeal_eq_sup_components_defect_fin_two
    a c ha hzero hone
  rw [scaledQuadraticDefectIdeal_eq_bot_of_eq_top a c htop,
    sup_bot_eq] at hweight
  have htwo' : twoScaleIdeal q L ≤
      weightIdeal (D.component 0).space (D.component 0).lattice ⊔
        weightIdeal (D.component 1).space (D.component 1).lattice :=
    htwo.trans _root_.le_sup_left
  rw [sup_eq_left.mpr htwo'] at hweight
  apply powerIdeal_order_eq_of_eq (K := K)
  calc
    powerIdeal (K := K) (weightIdealOrder q L) = weightIdeal q L :=
      (weightIdeal_eq_powerIdeal q L).symm
    _ = weightIdeal (D.component 0).space (D.component 0).lattice ⊔
        weightIdeal (D.component 1).space (D.component 1).lattice := hweight
    _ = powerIdeal (K := K)
        (min
          (weightIdealOrder (D.component 0).space
            (D.component 0).lattice)
          (weightIdealOrder (D.component 1).space
            (D.component 1).lattice)) := by
      rw [weightIdeal_eq_powerIdeal, weightIdeal_eq_powerIdeal,
        sup_powerIdeal]

/-- Order form of the two-component formula for a finite cross defect. -/
theorem weightIdealOrder_eq_min_components_defect_fin_two
    (D : OrthogonalDecomposition q L 2) (a c : Kˣ)
    (ha : IsNormGeneratorValue q L a)
    (hzero : IsNormGeneratorValue
      (D.component 0).space (D.component 0).lattice a)
    (hone : IsNormGeneratorValue
      (D.component 1).space (D.component 1).lattice c)
    (htwo : twoScaleIdeal q L ≤
      weightIdeal (D.component 0).space (D.component 0).lattice)
    (hfinite : quadraticDefect K (a * c) ≠ ⊤) :
    weightIdealOrder q L =
      min
        (min
          (weightIdealOrder (D.component 0).space
            (D.component 0).lattice)
          (weightIdealOrder (D.component 1).space
            (D.component 1).lattice))
        (ordUnit K c + (quadraticDefect K (a * c)).toNat) := by
  have hweight := D.weightIdeal_eq_sup_components_defect_fin_two
    a c ha hzero hone
  rw [scaledQuadraticDefectIdeal_eq_powerIdeal_of_ne_top a c hfinite]
      at hweight
  have htwo' : twoScaleIdeal q L ≤
      (weightIdeal (D.component 0).space (D.component 0).lattice ⊔
        weightIdeal (D.component 1).space (D.component 1).lattice) ⊔
          powerIdeal (K := K)
            (ordUnit K c + (quadraticDefect K (a * c)).toNat) :=
    htwo.trans (_root_.le_sup_left.trans _root_.le_sup_left)
  rw [sup_eq_left.mpr htwo'] at hweight
  apply powerIdeal_order_eq_of_eq (K := K)
  calc
    powerIdeal (K := K) (weightIdealOrder q L) = weightIdeal q L :=
      (weightIdeal_eq_powerIdeal q L).symm
    _ = (weightIdeal (D.component 0).space (D.component 0).lattice ⊔
          weightIdeal (D.component 1).space (D.component 1).lattice) ⊔
        powerIdeal (K := K)
          (ordUnit K c + (quadraticDefect K (a * c)).toNat) := hweight
    _ = powerIdeal (K := K)
        (min
          (min
            (weightIdealOrder (D.component 0).space
              (D.component 0).lattice)
            (weightIdealOrder (D.component 1).space
              (D.component 1).lattice))
          (ordUnit K c + (quadraticDefect K (a * c)).toNat)) := by
      rw [weightIdeal_eq_powerIdeal, weightIdeal_eq_powerIdeal,
        sup_powerIdeal, sup_powerIdeal]

end OrthogonalDecomposition
end Lattice

namespace BONG

/-- In rank one, the norm group is the integral-square coset modulo `2sL`. -/
theorem normGroupSet_eq_integralSquareCoset_unary
    (b : BONG V q L 1) :
    Lattice.normGroupSet q L =
      Lattice.integralSquareCoset (b.value 0)
        (Lattice.twoScaleIdeal q L) := by
  ext z
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    have hxBasis : x ∈ Lattice.basisLattice b.basis := by
      rw [← b.lattice_eq_basisLattice]
      exact hx
    have hxIntegral :=
      (Lattice.mem_basisLattice_iff_repr_mem_integerRing b.basis x).1 hxBasis
    let c : IntegerRing K := ⟨b.basis.repr x 0, hxIntegral 0⟩
    refine ⟨c, y, hy, ?_⟩
    have hxrepr := b.basis.sum_repr x
    rw [Fin.sum_univ_one] at hxrepr
    calc
      q.quadratic x + y =
          q.quadratic ((b.basis.repr x 0) • b.basis 0) + y := by
        rw [hxrepr]
      _ = b.value 0 * (c : K) ^ 2 + y := by
        rw [q.quadratic_smul]
        change (b.basis.repr x 0) ^ 2 *
            q.quadratic (b.ambientVector 0) + y = _
        rw [b.quadratic_ambientVector]
        dsimp only [c]
        ring
  · rintro ⟨c, y, hy, rfl⟩
    let x : V := (c : K) • b.head
    have hx : x ∈ L := by
      change algebraMap (IntegerRing K) K c • b.head ∈ L
      exact L.smul_mem c b.head_isNormGenerator.mem
    refine ⟨x, hx, y, hy, ?_⟩
    dsimp only [x]
    rw [q.quadratic_smul, ← b.value_zero_eq_quadratic_head]
    ring

end BONG

namespace BONG.GoodBONG

variable [Beli2009WeightIdealData.{u, v} K]

/-- The unary weight is `2sL`. -/
theorem weightIdeal_eq_twoScaleIdeal_unary
    (b : GoodBONG q L 1) :
    Lattice.weightIdeal q L = Lattice.twoScaleIdeal q L := by
  let a : Kˣ := b.valueUnit 0
  have ha : Lattice.IsNormGeneratorValue q L a := by
    constructor
    · refine ⟨b.toBONG.head, b.toBONG.head_isNormGenerator.mem,
        0, Submodule.zero_mem _, ?_⟩
      dsimp only [a]
      rw [b.coe_valueUnit]
      change b.toBONG.value 0 = q.quadratic b.toBONG.head + 0
      rw [b.toBONG.value_zero_eq_quadratic_head, add_zero]
    · change Lattice.normIdeal q L =
        Lattice.principalIdeal (K := K) (b.toBONG.value 0)
      rw [b.toBONG.value_zero_eq_quadratic_head]
      exact b.toBONG.head_isNormGenerator.normIdeal_eq
  let w : Lattice.OrderedFractionalIdeal K := {
    carrier := Lattice.twoScaleIdeal q L
    order := b.order 0 + ramificationIndex K
    carrier_eq_powerIdeal := by
      rw [Lattice.twoScaleIdeal,
        b.toBONG.scaleIdeal_eq_principal_valueUnit_zero_unary,
        Lattice.twicePrincipalIdeal_eq_powerIdeal]
      rfl
  }
  symm
  apply (Lattice.beli2009Lemma210 a ha w le_rfl).2
  constructor
  · change Lattice.normGroupSet q L =
      Lattice.integralSquareCoset (b.toBONG.value 0)
        (Lattice.twoScaleIdeal q L)
    exact b.toBONG.normGroupSet_eq_integralSquareCoset_unary
  · exact Or.inl rfl

/-- The rank-one assertion of Beli (2009), Lemma 2.14. -/
theorem weightIdealOrder_unary_proof (b : GoodBONG q L 1) :
    Lattice.weightIdealOrder q L =
      b.order 0 + (ramificationIndex K : Int) := by
  apply Lattice.powerIdeal_order_eq_of_eq (K := K)
  calc
    Lattice.powerIdeal (K := K) (Lattice.weightIdealOrder q L) =
        Lattice.weightIdeal q L :=
      (Lattice.weightIdeal_eq_powerIdeal q L).symm
    _ = Lattice.twoScaleIdeal q L := b.weightIdeal_eq_twoScaleIdeal_unary
    _ = Lattice.powerIdeal (K := K)
        (b.order 0 + ramificationIndex K) := by
      rw [Lattice.twoScaleIdeal,
        b.toBONG.scaleIdeal_eq_principal_valueUnit_zero_unary,
        Lattice.twicePrincipalIdeal_eq_powerIdeal,
        ← b.toBONG.order_eq_ordUnit]
      rfl

/-- Endpoint form of Beli (2009), Corollary 2.5(ii).  For a BONG of rank at
least three, the first alpha is the minimum of the two candidates already
visible on the initial binary segment and the order-gap shifted first alpha
of the canonical suffix segment. -/
theorem alphaValue_zero_eq_min_binaryCandidates_suffix
    {n : Nat} (b : GoodBONG q L (n + 3)) :
    (b.alphaValue 0 : WithTop ℚ) =
      min (b.halfGapCandidate 0)
        (min (b.leftDefectCandidate 0 0)
          (((((b.order 1 - b.order 0 : Int) : ℚ) +
            (((b.suffixAlphaSegmentWitness (n := n + 1)
              (0 : Fin (n + 2)) (by
                show 1 < n + 2
                omega)).toGoodBONG b.good).alphaValue
              (suffixAlphaLocalizationIndex (n := n + 1)
                (0 : Fin (n + 2)) (by
                  show 1 < n + 2
                  omega)).localPivot : ℚ)) : ℚ) : WithTop ℚ)) := by
  rw [b.coe_alphaValue, b.beli2009Corollary25_ii 0]
  simp [segmentRecursiveAlphaCandidates, prefixSegmentAlphaCandidates,
    suffixSegmentAlphaCandidates, suffixSegmentAlphaCandidate,
    rightCompressionValue, suffixAlphaLocalizationIndex,
    AlphaLocalizationIndex.pivotFin, AlphaLocalizationIndex.localPivot]

end BONG.GoodBONG

end Bong
