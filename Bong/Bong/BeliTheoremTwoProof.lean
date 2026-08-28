/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliTheoremTwo
import Bong.Bong.BeliLemma71Proof
import Bong.Bong.BeliTheoremThreeUnconditional
import Bong.Lattice.OrthogonalDecompositionTail
import Bong.Lattice.OrthogonalDecompositionIdeals
import Bong.Lattice.OrthogonalDecompositionPrefix
import Bong.Lattice.SpinorNormIsometry
import Bong.Lattice.SpinorNormOrthogonalProduct
import Bong.Dyadic.QuadraticDefectHensel

/-!
# Proof of Beli (2003), Theorem 2

The proof first develops the functorial facts omitted from the statement:
spinor images pass to orthogonal components, norm-order data transport under
isometry, and a flat tower of displayed hyperbolic planes may be peeled off
one plane at a time.  The final instance contains no local-law assumptions.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Lattice

variable {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

namespace NormOrderDatum

/-- Transport chosen norm-order data through a lattice isometry. -/
noncomputable def mapIsometry (N : NormOrderDatum q L)
    (f : Isometry q r L M) : NormOrderDatum r M where
  generator := N.generator
  normIdeal_eq := by
    calc
      normIdeal r M = normIdeal r (map f.toLinearEquiv L) := by
        rw [f.map_eq]
      _ = normIdeal q L :=
        normIdeal_map_isometry f.toQuadraticSpaceIsometry L
      _ = principalIdeal (K := K) (N.generator : K) := N.normIdeal_eq

@[simp]
theorem mapIsometry_order (N : NormOrderDatum q L)
    (f : Isometry q r L M) :
    (N.mapIsometry f).order = N.order :=
  rfl

end NormOrderDatum

/-- Norm-order data on a component displayed as a scaled hyperbolic plane. -/
noncomputable def normOrderDatumOfScaledHyperbolicIsometry
    (scaleOrder : Int)
    (h : IsIsometric q
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K scaleOrder))
      L (hyperbolicPlaneLattice (K := K))) :
    NormOrderDatum q L := by
  let e := Classical.choice h
  let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
  let generator : Kˣ := two * uniformizerPowerUnit K scaleOrder
  refine {
    generator := generator
    normIdeal_eq := ?_ }
  have hmap := normIdeal_map_isometry e.toQuadraticSpaceIsometry L
  have heq : map e.toQuadraticSpaceIsometry.toLinearEquiv L =
      hyperbolicPlaneLattice (K := K) := e.map_eq
  rw [heq] at hmap
  calc
    normIdeal q L =
        normIdeal
          (QuadraticSpace.hyperbolicPlane
            (uniformizerPowerUnit K scaleOrder))
          (hyperbolicPlaneLattice (K := K)) := hmap.symm
    _ = principalIdeal (K := K)
        (2 * (uniformizerPowerUnit K scaleOrder : K)) :=
      normIdeal_hyperbolicPlaneLattice _
    _ = principalIdeal (K := K) (generator : K) := by
      congr 2

@[simp]
theorem normOrderDatumOfScaledHyperbolicIsometry_order
    (scaleOrder : Int)
    (h : IsIsometric q
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K scaleOrder))
      L (hyperbolicPlaneLattice (K := K))) :
    (normOrderDatumOfScaledHyperbolicIsometry scaleOrder h).order =
      scaleOrder + ramificationIndex K := by
  let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
  have htwo : ordUnit K two = (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, ramificationIndex_spec]
    rfl
  simp only [normOrderDatumOfScaledHyperbolicIsometry,
    NormOrderDatum.order]
  change ordUnit K (two * uniformizerPowerUnit K scaleOrder) =
    scaleOrder + ramificationIndex K
  rw [ordUnit_mul, ordUnit_uniformizerPowerUnit, htwo]
  omega

/-- An integral isometry with the standard scaled hyperbolic plane exhibits
that plane inside the source lattice. -/
theorem containsScaledHyperbolicPlane_of_isIsometric_hyperbolicPlane
    (scaleOrder : Int)
    (h : IsIsometric q
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K scaleOrder))
      L (hyperbolicPlaneLattice (K := K))) :
    ContainsScaledHyperbolicPlane q L scaleOrder := by
  classical
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  rcases h with ⟨f⟩
  let e₀ : Fin 2 → K := Pi.single 0 1
  let e₁ : Fin 2 → K := Pi.single 1 1
  let x : V := f.toLinearEquiv.symm e₀
  let y : V := f.toLinearEquiv.symm e₁
  have he₀ : e₀ ∈ hyperbolicPlaneLattice (K := K) := by
    rw [hyperbolicPlaneLattice,
      mem_basisLattice_iff_repr_mem_integerRing]
    simp [e₀]
  have he₁ : e₁ ∈ hyperbolicPlaneLattice (K := K) := by
    rw [hyperbolicPlaneLattice,
      mem_basisLattice_iff_repr_mem_integerRing]
    simp [e₁]
  have hxMem : x ∈ L := by
    apply (f.map_mem x).2
    simpa [x] using he₀
  have hyMem : y ∈ L := by
    apply (f.map_mem y).2
    simpa [y] using he₁
  have hxQuadratic : q.quadratic x = 0 := by
    have hq := f.map_quadratic x
    rw [show f.toLinearEquiv x = e₀ by simp [x]] at hq
    simpa [e₀, QuadraticSpace.hyperbolicPlane_quadratic_apply]
      using hq.symm
  have hyQuadratic : q.quadratic y = 0 := by
    have hq := f.map_quadratic y
    rw [show f.toLinearEquiv y = e₁ by simp [y]] at hq
    simpa [e₁, QuadraticSpace.hyperbolicPlane_quadratic_apply]
      using hq.symm
  have hsumValue : q.quadratic (x + y) =
      2 * (uniformizerPowerUnit K scaleOrder : K) := by
    have hq := f.map_quadratic (x + y)
    have hmap : f.toLinearEquiv (x + y) = e₀ + e₁ := by
      simp [x, y]
    rw [hmap] at hq
    simpa [e₀, e₁, QuadraticSpace.hyperbolicPlane_quadratic_apply]
      using hq.symm
  have hsumOrder : ord K (q.quadratic (x + y)) =
      ((scaleOrder + ramificationIndex K : Int) : WithTop Int) := by
    rw [hsumValue, ord_mul, ← ramificationIndex_spec,
      ← coe_ordUnit, ordUnit_uniformizerPowerUnit]
    norm_cast
    omega
  have hxHigh : ((scaleOrder + ramificationIndex K : Int) : WithTop Int) <
      ord K (q.quadratic x) := by
    rw [hxQuadratic, ord_zero]
    exact WithTop.coe_lt_top _
  have hyHigh : ((scaleOrder + ramificationIndex K : Int) : WithTop Int) <
      ord K (q.quadratic y) := by
    rw [hyQuadratic, ord_zero]
    exact WithTop.coe_lt_top _
  have hpair := BONG.beliLemma319 (q := q) x y
    (scaleOrder + ramificationIndex K) hxHigh hyHigh hsumOrder
  have hscale : scaleOrder + ramificationIndex K - ramificationIndex K =
      scaleOrder := by omega
  rw [hscale] at hpair
  exact ⟨x, y, hxMem, hyMem, hpair⟩

/-- Hyperbolic-plane containment for the restricted quadratic space of a
quadratic sublattice gives containment in the ambient quadratic space. -/
theorem QuadraticSublattice.containsScaledHyperbolicPlane_of_restrict
    (C : QuadraticSublattice q) (scaleOrder : Int)
    (hlocal : Lattice.ContainsScaledHyperbolicPlane
      C.space C.lattice scaleOrder) :
    C.ContainsScaledHyperbolicPlane scaleOrder := by
  classical
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  rcases BONG.exists_integral_isotropic_pair_of_containsScaledHyperbolicPlane
      hlocal with ⟨x, y, hxMem, hyMem, hxQuadratic, hyQuadratic, hxy⟩
  change q.quadratic (x : V) = 0 at hxQuadratic
  change q.quadratic (y : V) = 0 at hyQuadratic
  change q.bilin (x : V) (y : V) =
    (uniformizerPowerUnit K scaleOrder : K) at hxy
  have hsumValue : q.quadratic ((x : V) + (y : V)) =
      2 * (uniformizerPowerUnit K scaleOrder : K) := by
    rw [q.quadratic_add, hxQuadratic, hyQuadratic, hxy]
    ring
  have hsumOrder : ord K (q.quadratic ((x : V) + (y : V))) =
      ((scaleOrder + ramificationIndex K : Int) : WithTop Int) := by
    rw [hsumValue, ord_mul, ← ramificationIndex_spec,
      ← coe_ordUnit, ordUnit_uniformizerPowerUnit]
    norm_cast
    omega
  have hxHigh : ((scaleOrder + ramificationIndex K : Int) : WithTop Int) <
      ord K (q.quadratic (x : V)) := by
    rw [hxQuadratic, ord_zero]
    exact WithTop.coe_lt_top _
  have hyHigh : ((scaleOrder + ramificationIndex K : Int) : WithTop Int) <
      ord K (q.quadratic (y : V)) := by
    rw [hyQuadratic, ord_zero]
    exact WithTop.coe_lt_top _
  have hpair := BONG.beliLemma319 (q := q) (x : V) (y : V)
    (scaleOrder + ramificationIndex K) hxHigh hyHigh hsumOrder
  have hscale : scaleOrder + ramificationIndex K - ramificationIndex K =
      scaleOrder := by omega
  rw [hscale] at hpair
  exact ⟨x, y, hxMem, hyMem, hpair⟩

/-- The preceding extraction, expressed for a quadratic sublattice and hence
with the resulting pair viewed in its ambient quadratic space. -/
theorem QuadraticSublattice.containsScaledHyperbolicPlane_of_isIsometric
    (C : QuadraticSublattice q) (scaleOrder : Int)
    (h : IsIsometric C.space
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K scaleOrder))
      C.lattice (hyperbolicPlaneLattice (K := K))) :
    C.ContainsScaledHyperbolicPlane scaleOrder :=
  C.containsScaledHyperbolicPlane_of_restrict scaleOrder
    (Lattice.containsScaledHyperbolicPlane_of_isIsometric_hyperbolicPlane
      scaleOrder h)

/-- The first summand of a hyperbolic-plane splitting is a contained scaled
hyperbolic plane in the ambient lattice. -/
theorem HyperbolicPlaneSplitting.containsScaledHyperbolicPlane
    (S : HyperbolicPlaneSplitting q L) :
    ContainsScaledHyperbolicPlane q L S.scaleOrder := by
  apply S.decomposition.containsScaledHyperbolicPlane_of_component
    0 S.scaleOrder
  exact QuadraticSublattice.containsScaledHyperbolicPlane_of_isIsometric
    (S.decomposition.component 0) S.scaleOrder S.hyperbolic

/-- Unit-boundedness of the proper integral spinor image is invariant under
lattice isometry. -/
theorem spinorNormIsUnitBounded_iff_of_isometry
    (f : Isometry q r L M) :
    SpinorNormIsUnitBounded q L ↔ SpinorNormIsUnitBounded r M := by
  unfold SpinorNormIsUnitBounded
  have himage : spinorNormImageSubgroup (q := q) (L := L) =
      spinorNormImageSubgroup (q := r) (L := M) := by
    ext a
    change a ∈ spinorNormImage (q := q) (L := L) ↔
      a ∈ spinorNormImage (q := r) (L := M)
    rw [spinorNormImage_eq_of_isometry f]
  rw [himage]

namespace OrthogonalDecomposition

/-- An index whose chosen component norm order is minimal. -/
noncomputable def minimumNormIndex {t : Nat}
    (D : OrthogonalDecomposition q L (t + 1))
    (N : OrthogonalComponentNormData D) : Fin (t + 1) :=
  Classical.choose (Finset.exists_min_image Finset.univ
    (fun i ↦ (N i).order) (by simp))

/-- The selected norm order is no larger than any component norm order. -/
theorem minimumNormIndex_order_le {t : Nat}
    (D : OrthogonalDecomposition q L (t + 1))
    (N : OrthogonalComponentNormData D) (j : Fin (t + 1)) :
    (N (D.minimumNormIndex N)).order ≤ (N j).order := by
  have hspec := Classical.choose_spec
    (Finset.exists_min_image Finset.univ
      (fun i ↦ (N i).order) (by simp))
  exact hspec.2 j (Finset.mem_univ j)

/-- A norm generator for the whole orthogonal sum, chosen from a component
of minimal norm order. -/
noncomputable def totalNormOrderDatum {t : Nat}
    (D : OrthogonalDecomposition q L (t + 1))
    (N : OrthogonalComponentNormData D) : NormOrderDatum q L where
  generator := (N (D.minimumNormIndex N)).generator
  normIdeal_eq := by
    rw [D.normIdeal_eq_iSup_component]
    apply le_antisymm
    · apply iSup_le
      intro j
      rw [(N j).normIdeal_eq]
      apply (principalIdeal_le_iff_ord_ge
        (Units.ne_zero (N j).generator)
        (Units.ne_zero (N (D.minimumNormIndex N)).generator)).2
      rw [← coe_ordUnit K (N (D.minimumNormIndex N)).generator,
        ← coe_ordUnit K (N j).generator]
      exact_mod_cast D.minimumNormIndex_order_le N j
    · rw [← (N (D.minimumNormIndex N)).normIdeal_eq]
      exact le_iSup
        (fun j ↦ normIdeal (D.component j).space
          (D.component j).lattice)
        (D.minimumNormIndex N)

@[simp]
theorem totalNormOrderDatum_order {t : Nat}
    (D : OrthogonalDecomposition q L (t + 1))
    (N : OrthogonalComponentNormData D) :
    (D.totalNormOrderDatum N).order =
      (N (D.minimumNormIndex N)).order :=
  rfl

/-- A common congruence class of all component norm orders is also the class
of the norm order of the whole orthogonal sum. -/
theorem totalNormOrderDatum_modEq {t : Nat}
    (D : OrthogonalDecomposition q L (t + 1))
    (N : OrthogonalComponentNormData D) (m z : Int)
    (h : ∀ i, Int.ModEq m (N i).order z) :
    Int.ModEq m (D.totalNormOrderDatum N).order z := by
  rw [D.totalNormOrderDatum_order]
  exact h (D.minimumNormIndex N)

/-- The original final component is integrally isometric to the final
component of the positive-index tail decomposition. -/
noncomputable def tailLastComponentIsometry {t : Nat}
    (D : OrthogonalDecomposition q L (t + 2)) :
    Isometry (D.component (Fin.last (t + 1))).space
      (D.tailDecomposition.component (Fin.last t)).space
      (D.component (Fin.last (t + 1))).lattice
      (D.tailDecomposition.component (Fin.last t)).lattice := by
  have hindex : (Fin.last t).succ = Fin.last (t + 1) := by
    apply Fin.ext
    simp
  rw [show D.tailDecomposition.component (Fin.last t) =
      D.tailComponent (Fin.last t) by rfl, ← hindex]
  exact D.tailComponentIsometry (Fin.last t)

/-- The norm-order and hyperbolic-model data needed for the induction on a
flat displayed tower. -/
structure DisplayedHyperbolicTowerData {t : Nat}
    (D : OrthogonalDecomposition q L (t + 1)) where
  scaleOrder : Fin t → Int
  hyperbolic : ∀ i : Fin t,
    IsIsometric (D.component i.castSucc).space
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K (scaleOrder i)))
      (D.component i.castSucc).lattice
      (hyperbolicPlaneLattice (K := K))
  remainderNorm : NormOrderDatum (D.component (Fin.last t)).space
    (D.component (Fin.last t)).lattice

namespace DisplayedHyperbolicTowerData

/-- Norm-order data on every component of a displayed hyperbolic tower. -/
noncomputable def componentNormData {t : Nat}
    {D : OrthogonalDecomposition q L (t + 1)}
    (B : DisplayedHyperbolicTowerData D) :
    OrthogonalComponentNormData D := fun i ↦
  Fin.lastCases B.remainderNorm (fun j ↦
    normOrderDatumOfScaledHyperbolicIsometry
      (B.scaleOrder j) (B.hyperbolic j)) i

@[simp]
theorem componentNormData_last {t : Nat}
    {D : OrthogonalDecomposition q L (t + 1)}
    (B : DisplayedHyperbolicTowerData D) :
    B.componentNormData (Fin.last t) = B.remainderNorm := by
  simp [componentNormData]

@[simp]
theorem componentNormData_castSucc_order {t : Nat}
    {D : OrthogonalDecomposition q L (t + 1)}
    (B : DisplayedHyperbolicTowerData D) (i : Fin t) :
    (B.componentNormData i.castSucc).order =
      B.scaleOrder i + ramificationIndex K := by
  simp [componentNormData]

/-- Removing the head of a nonempty tower leaves a displayed tower in the
exact suffix lattice. -/
noncomputable def tail {t : Nat}
    {D : OrthogonalDecomposition q L (t + 2)}
    (B : DisplayedHyperbolicTowerData D) :
    DisplayedHyperbolicTowerData D.tailDecomposition where
  scaleOrder i := B.scaleOrder i.succ
  hyperbolic i := by
    rcases B.hyperbolic i.succ with ⟨h⟩
    have hindex : i.castSucc.succ = i.succ.castSucc := by
      apply Fin.ext
      simp
    have h' : Isometry (D.component i.castSucc.succ).space
        (QuadraticSpace.hyperbolicPlane
          (uniformizerPowerUnit K (B.scaleOrder i.succ)))
        (D.component i.castSucc.succ).lattice
        (hyperbolicPlaneLattice (K := K)) := by
      rw [hindex]
      exact h
    exact ⟨(D.tailComponentIsometry i.castSucc).symm.trans h'⟩
  remainderNorm := B.remainderNorm.mapIsometry
    D.tailLastComponentIsometry

@[simp]
theorem tail_scaleOrder {t : Nat}
    {D : OrthogonalDecomposition q L (t + 2)}
    (B : DisplayedHyperbolicTowerData D) (i : Fin t) :
    B.tail.scaleOrder i = B.scaleOrder i.succ :=
  rfl

@[simp]
theorem tail_remainderNorm_order {t : Nat}
    {D : OrthogonalDecomposition q L (t + 2)}
    (B : DisplayedHyperbolicTowerData D) :
    B.tail.remainderNorm.order = B.remainderNorm.order :=
  rfl

end DisplayedHyperbolicTowerData

/-- The right component's spinor image embeds into that of a two-block
orthogonal decomposition. -/
theorem right_spinorNormImageSubgroup_le
    (D : OrthogonalDecomposition q L 2) :
    spinorNormImageSubgroup
        (q := (D.component 1).space) (L := (D.component 1).lattice) ≤
      spinorNormImageSubgroup (q := q) (L := L) := by
  intro a ha
  rw [mem_spinorNormImageSubgroup_iff] at ha ⊢
  rcases ha with ⟨f, rfl⟩
  let productOrthogonal : IntegralOrthogonalGroup
      ((D.component 0).space.orthogonalSum (D.component 1).space)
      (product (D.component 0).lattice (D.component 1).lattice) :=
    (Isometry.refl (D.component 0).space
      (D.component 0).lattice).orthogonalProductBasic
        f.toIntegralOrthogonalGroup
  let productRotation : IntegralRotation
      ((D.component 0).space.orthogonalSum (D.component 1).space)
      (product (D.component 0).lattice (D.component 1).lattice) := {
    toIntegralOrthogonalGroup := productOrthogonal
    det_eq_one := by
      dsimp only [productOrthogonal]
      rw [Isometry.det_orthogonalProductBasic]
      have hreflDet : LinearEquiv.det
          (Isometry.refl (D.component 0).space
            (D.component 0).lattice).toLinearEquiv = 1 :=
        LinearEquiv.det_refl
      rw [hreflDet, f.det_eq_one, mul_one] }
  let ambientRotation : IntegralRotation q L :=
    productRotation.conjugateAutomorphism D.pairProductLatticeIsometry
  refine ⟨ambientRotation, ?_⟩
  calc
    ambientRotation.spinorNorm = productRotation.spinorNorm :=
      productRotation.spinorNorm_conjugateAutomorphism
        D.pairProductLatticeIsometry
    _ = f.spinorNorm := by
      change integralSpinorNorm productOrthogonal =
        integralSpinorNorm f.toIntegralOrthogonalGroup
      dsimp only [productOrthogonal]
      rw [integralSpinorNorm_orthogonalProductBasic]
      letI : Module.Finite K (D.component 0).carrier :=
        (D.component 0).lattice.moduleFinite
      have hrefl : integralSpinorNorm
          (Isometry.refl (D.component 0).space
            (D.component 0).lattice) = 1 :=
        QuadraticSpace.spinorNorm_refl
      rw [hrefl, one_mul]

/-- Unit-boundedness of a two-block lattice passes to its right component. -/
theorem right_spinorNormIsUnitBounded
    (D : OrthogonalDecomposition q L 2)
    (hunit : SpinorNormIsUnitBounded q L) :
    SpinorNormIsUnitBounded (D.component 1).space
      (D.component 1).lattice :=
  fun _ ha ↦ hunit (D.right_spinorNormImageSubgroup_le ha)

/-- Unit-boundedness of a flat orthogonal sum passes to its final component. -/
theorem lastComponent_spinorNormIsUnitBounded
    {t : Nat} (D : OrthogonalDecomposition q L (t + 1))
    (hunit : SpinorNormIsUnitBounded q L) :
    SpinorNormIsUnitBounded (D.component (Fin.last t)).space
      (D.component (Fin.last t)).lattice := by
  induction t generalizing V with
  | zero =>
      exact (spinorNormIsUnitBounded_iff_of_isometry
        D.singleComponentLatticeIsometry).2 hunit
  | succ t ih =>
      let P := D.headTailDecomposition
      have htail : SpinorNormIsUnitBounded
          (D.suffixQuadraticSublattice 1).space
          (D.suffixQuadraticSublattice 1).lattice := by
        have htail' := P.right_spinorNormIsUnitBounded hunit
        rw [show P.component 1 = D.suffixQuadraticSublattice 1 by
          exact D.headTailDecomposition_one] at htail'
        exact htail'
      have hlastTail := ih D.tailDecomposition htail
      have hindex : (Fin.last t).succ = Fin.last (t + 1) := by
        apply Fin.ext
        simp
      let e : Isometry (D.component (Fin.last (t + 1))).space
          (D.tailComponent (Fin.last t)).space
          (D.component (Fin.last (t + 1))).lattice
          (D.tailComponent (Fin.last t)).lattice := by
        rw [← hindex]
        exact D.tailComponentIsometry (Fin.last t)
      have hlastTail' : SpinorNormIsUnitBounded
          (D.tailComponent (Fin.last t)).space
          (D.tailComponent (Fin.last t)).lattice := by
        exact hlastTail
      exact (spinorNormIsUnitBounded_iff_of_isometry e).2 hlastTail'

/-- A displayed flat tower with a unit-bounded remainder and common norm
parity is unit-bounded.  If the tower is nonempty, its spinor image is the
entire valuation-unit square-class subgroup. -/
theorem spinorNormIsUnitBounded_and_eq_unit_of_displayedHyperbolicTower
    {t : Nat} (D : OrthogonalDecomposition q L (t + 1))
    (B : DisplayedHyperbolicTowerData D)
    (hrem : SpinorNormIsUnitBounded
      (D.component (Fin.last t)).space
      (D.component (Fin.last t)).lattice)
    (hparity : ∀ i : Fin t,
      Int.ModEq 2 (B.scaleOrder i + ramificationIndex K)
        B.remainderNorm.order) :
    SpinorNormIsUnitBounded q L ∧
      (0 < t → spinorNormImageSubgroup (q := q) (L := L) =
        valuationUnitSquareClassSubgroup K) := by
  induction t generalizing V with
  | zero =>
      have hindex : Fin.last 0 = (0 : Fin 1) := by
        apply Fin.ext
        simp
      rw [hindex] at hrem
      constructor
      · have hrem' : SpinorNormIsUnitBounded (D.component 0).space
            (D.component 0).lattice := by
          exact hrem
        exact (spinorNormIsUnitBounded_iff_of_isometry
          D.singleComponentLatticeIsometry).1 hrem'
      · intro ht
        omega
  | succ t ih =>
      let Btail := B.tail
      have htailRem : SpinorNormIsUnitBounded
          (D.tailDecomposition.component (Fin.last t)).space
          (D.tailDecomposition.component (Fin.last t)).lattice :=
        (spinorNormIsUnitBounded_iff_of_isometry
          D.tailLastComponentIsometry).1 hrem
      have htailParity : ∀ i : Fin t,
          Int.ModEq 2
            (Btail.scaleOrder i + ramificationIndex K)
            Btail.remainderNorm.order := by
        intro i
        change Int.ModEq 2
          (B.scaleOrder i.succ + ramificationIndex K)
          B.remainderNorm.order
        exact hparity i.succ
      rcases ih D.tailDecomposition Btail htailRem htailParity with
        ⟨htailUnit, _htailEq⟩
      let Ntail : OrthogonalComponentNormData D.tailDecomposition :=
        Btail.componentNormData
      have hNtail : ∀ j : Fin (t + 1),
          Int.ModEq 2 (Ntail j).order B.remainderNorm.order := by
        intro j
        refine Fin.lastCases ?_ (fun i ↦ ?_) j
        · rw [show (Ntail (Fin.last t)).order =
              Btail.remainderNorm.order by
              exact congrArg NormOrderDatum.order
                Btail.componentNormData_last]
          change Int.ModEq 2 B.remainderNorm.order B.remainderNorm.order
          exact Int.ModEq.refl _
        · rw [show (Ntail i.castSucc).order =
              Btail.scaleOrder i + ramificationIndex K by
              exact Btail.componentNormData_castSucc_order i]
          change Int.ModEq 2
            (B.scaleOrder i.succ + ramificationIndex K)
            B.remainderNorm.order
          exact hparity i.succ
      let tailNorm : NormOrderDatum
          (D.suffixQuadraticSublattice 1).space
          (D.suffixQuadraticSublattice 1).lattice :=
        D.tailDecomposition.totalNormOrderDatum Ntail
      have htailNormParity :
          Int.ModEq 2 tailNorm.order B.remainderNorm.order := by
        exact D.tailDecomposition.totalNormOrderDatum_modEq
          Ntail 2 B.remainderNorm.order hNtail
      let P := D.headTailDecomposition
      let S : HyperbolicPlaneSplitting q L := {
        decomposition := P
        scaleOrder := B.scaleOrder 0
        hyperbolic := by
          change IsIsometric (D.component 0).space
            (QuadraticSpace.hyperbolicPlane
              (uniformizerPowerUnit K (B.scaleOrder 0)))
            (D.component 0).lattice
            (hyperbolicPlaneLattice (K := K))
          exact B.hyperbolic 0
        remainderNorm := by
          change NormOrderDatum
            (D.suffixQuadraticSublattice 1).space
            (D.suffixQuadraticSublattice 1).lattice
          exact tailNorm }
      have hSrem : S.RemainderIsUnitBounded := by
        change SpinorNormIsUnitBounded
          (D.suffixQuadraticSublattice 1).space
          (D.suffixQuadraticSublattice 1).lattice
        exact htailUnit
      have hSparity : S.NormOrdersSameParity := by
        change Int.ModEq 2
          (B.scaleOrder 0 + ramificationIndex K) tailNorm.order
        exact (hparity 0).trans htailNormParity.symm
      have heq := beliLemma71_ii_same_proved S hSrem hSparity
      exact ⟨le_of_eq heq, fun _ ↦ heq⟩

end OrthogonalDecomposition

end Lattice

namespace BONG

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The head of a nonempty BONG supplies canonical norm-order data for its
ambient lattice. -/
noncomputable def headNormOrderDatum {n : Nat}
    (b : BONG V q L (n + 1)) : Lattice.NormOrderDatum q L where
  generator := b.valueUnit 0
  normIdeal_eq := by
    simpa only [b.coe_valueUnit, b.value_zero_eq_quadratic_head] using
      b.head_isNormGenerator.normIdeal_eq

@[simp]
theorem headNormOrderDatum_order {n : Nat}
    (b : BONG V q L (n + 1)) :
    b.headNormOrderDatum.order = b.order 0 := by
  rfl

/-- A good BONG on a unit-bounded lattice that contains no scaled
hyperbolic plane has property A.  The proof uses Theorem 3 to obtain the two
adjacent spinor conditions; any failed strict two-step inequality then gives
the Lemma 7.3 hyperbolic splitting. -/
theorem hasPropertyA_of_good_of_unitBounded_of_noScaledHyperbolicPlane
    {m : Nat} (b : BONG V q L m) (hgood : b.IsGood)
    (hunit : Lattice.SpinorNormIsUnitBounded q L)
    (hno : ∀ r : Int,
      ¬Lattice.ContainsScaledHyperbolicPlane q L r) :
    b.HasPropertyA := by
  by_cases hm : m ≤ 2
  · exact b.hasPropertyA_of_length_le_two hm
  · obtain ⟨n, hn⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
    subst m
    have hconditions : b.SatisfiesTheoremThreeConditions :=
      (beliTheoremThree_proved b hgood).1 hunit
    by_contra hA
    have hexists : ∃ (i : Fin (n + 3))
        (hi : i.1 + 2 < n + 3),
        b.order i = b.order ⟨i.1 + 2, hi⟩ := by
      by_contra hnone
      apply hA
      rw [hasPropertyA_iff_isGood_and_ne]
      refine ⟨hgood, ?_⟩
      intro i hi heq
      exact hnone ⟨i, hi, heq⟩
    rcases hexists with ⟨i, hi, heq⟩
    let j : Fin (n + 1) := ⟨i.1, by omega⟩
    have heqj : b.order (lemma73FirstIndex j) =
        b.order (lemma73LastIndex j) := by
      simpa [j, lemma73FirstIndex, lemma73LastIndex] using heq
    have hblock : b.Lemma73Hypotheses j := by
      unfold Lemma73Hypotheses
      refine ⟨heqj, ?_, ?_⟩
      · simpa [j, lemma73FirstIndex] using
          hconditions.1 i (by omega)
      · simpa [j, lemma73MiddleIndex] using
          hconditions.1 ⟨i.1 + 1, by omega⟩ (by omega)
    rcases b.exists_lemma73SplittingWitness j hgood hblock with ⟨w⟩
    exact hno (b.lemma73HyperbolicScaleOrder j)
      w.toHyperbolicPlaneSplitting.containsScaledHyperbolicPlane

end BONG

namespace Lattice

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Necessity of the residual property-A condition in Beli's Theorem 2.
The input residual BONG need not itself be assumed good: property A is first
proved for a chosen good BONG and then transported through the intrinsic
Jordan property. -/
theorem HyperbolicTowerSplitting.remainderHasPropertyA_of_fullUnitBound
    {t n : Nat} (S : HyperbolicTowerSplitting q L t n)
    (hfull : SpinorNormIsUnitBounded q L) :
    S.RemainderHasPropertyA := by
  let C := S.decomposition.component (Fin.last t)
  have hrem : SpinorNormIsUnitBounded C.space C.lattice :=
    S.decomposition.lastComponent_spinorNormIsUnitBounded hfull
  have hnoLocal : ∀ r : Int,
      ¬ContainsScaledHyperbolicPlane C.space C.lattice r := by
    intro r hlocal
    apply S.remainderDoesNotSplitHyperbolicPlane r
    exact C.containsScaledHyperbolicPlane_of_restrict r hlocal
  let raw : BONG.GoodBONG C.space C.lattice
      (Module.finrank K C.carrier) :=
    Classical.choice (exists_good_bong C.space C.lattice)
  have hlength : Module.finrank K C.carrier = n + 1 := by
    exact S.remainderBONG.length_eq_finrank.symm
  let c : BONG.GoodBONG C.space C.lattice (n + 1) :=
    raw.castLength hlength
  have hcA : c.toBONG.HasPropertyA :=
    c.toBONG.hasPropertyA_of_good_of_unitBounded_of_noScaledHyperbolicPlane
      c.good hrem hnoLocal
  have hJordan : HasJordanPropertyA C.space C.lattice :=
    (hasJordanPropertyA_iff_bongHasPropertyA c.toBONG).2 hcA
  exact (hasJordanPropertyA_iff_bongHasPropertyA S.remainderBONG).1 hJordan

/-- The displayed data underlying a hyperbolic tower, with the residual norm
generator supplied by the head of its residual BONG. -/
noncomputable def HyperbolicTowerSplitting.displayedHyperbolicTowerData
    {t n : Nat} (S : HyperbolicTowerSplitting q L t n) :
    S.decomposition.DisplayedHyperbolicTowerData where
  scaleOrder := S.scaleOrder
  hyperbolic := S.hyperbolic
  remainderNorm := S.remainderBONG.headNormOrderDatum

@[simp]
theorem HyperbolicTowerSplitting.displayedHyperbolicTowerData_scaleOrder
    {t n : Nat} (S : HyperbolicTowerSplitting q L t n) (i : Fin t) :
    S.displayedHyperbolicTowerData.scaleOrder i = S.scaleOrder i :=
  rfl

@[simp]
theorem HyperbolicTowerSplitting.displayedHyperbolicTowerData_remainder_order
    {t n : Nat} (S : HyperbolicTowerSplitting q L t n) :
    S.displayedHyperbolicTowerData.remainderNorm.order =
      S.remainderBONG.order 0 :=
  rfl

/-- A unit bound on the whole tower restricts to the residual component. -/
theorem HyperbolicTowerSplitting.remainderIsUnitBounded_of_fullUnitBound
    {t n : Nat} (S : HyperbolicTowerSplitting q L t n)
    (hfull : SpinorNormIsUnitBounded q L) :
    S.RemainderIsUnitBounded := by
  exact S.decomposition.lastComponent_spinorNormIsUnitBounded hfull

/-- Lemma 7.1(i) gives the parity condition for every displayed hyperbolic
component and the residual component. -/
theorem HyperbolicTowerSplitting.allNormOrdersSameParity_of_fullUnitBound
    {t n : Nat} (S : HyperbolicTowerSplitting q L t n)
    (hfull : SpinorNormIsUnitBounded q L) :
    S.AllNormOrdersSameParity := by
  intro i
  let B := S.displayedHyperbolicTowerData
  have hparity := beliLemma71_i_proved S.decomposition
    B.componentNormData hfull i.castSucc (Fin.last t)
  change Int.ModEq 2
    (S.scaleOrder i + ramificationIndex K)
    (S.remainderBONG.order 0)
  simpa [B] using hparity

/-- The sufficient direction of Theorem 2 follows from the proved flat-tower
induction. -/
theorem HyperbolicTowerSplitting.fullUnitBound_of_conditions
    {t n : Nat} (S : HyperbolicTowerSplitting q L t n)
    (hconditions : S.SatisfiesTheoremTwoConditions) :
    SpinorNormIsUnitBounded q L := by
  exact (OrthogonalDecomposition.spinorNormIsUnitBounded_and_eq_unit_of_displayedHyperbolicTower
      S.decomposition S.displayedHyperbolicTowerData
        hconditions.1.2 hconditions.2).1

/-- If the tower is nonempty, the same induction gives equality with the
valuation-unit square-class subgroup. -/
theorem HyperbolicTowerSplitting.spinorNorm_eq_unit_of_conditions
    {t n : Nat} (S : HyperbolicTowerSplitting q L t n)
    (hconditions : S.SatisfiesTheoremTwoConditions) (ht : 0 < t) :
    spinorNormImageSubgroup (q := q) (L := L) =
      valuationUnitSquareClassSubgroup K := by
  exact (OrthogonalDecomposition.spinorNormIsUnitBounded_and_eq_unit_of_displayedHyperbolicTower
      S.decomposition S.displayedHyperbolicTowerData
        hconditions.1.2 hconditions.2).2 ht

end Lattice

/-- Unconditional implementation of all five fields in Beli (2003),
Theorem 2. -/
instance beliTheoremTwoLawsProved : BeliTheoremTwoLaws.{u, v} K where
  remainder_propertyA_of_full_unit_bound := fun S hfull ↦
    S.remainderHasPropertyA_of_fullUnitBound hfull
  remainder_unit_bound_of_full_unit_bound := fun S hfull ↦
    S.remainderIsUnitBounded_of_fullUnitBound hfull
  norm_parity_of_full_unit_bound := fun S hfull ↦
    S.allNormOrdersSameParity_of_fullUnitBound hfull
  full_unit_bound_of_conditions := fun S hconditions ↦
    S.fullUnitBound_of_conditions hconditions
  spinorNorm_eq_unit_of_conditions_of_hyperbolic :=
    fun S hconditions ht ↦
      S.spinorNorm_eq_unit_of_conditions hconditions ht

namespace Lattice

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Public unconditional entry point for Beli (2003), Theorem 2. -/
theorem beliTheoremTwo_proved {t n : Nat}
    (S : HyperbolicTowerSplitting q L t n) :
    SpinorNormIsUnitBounded q L ↔ S.SatisfiesTheoremTwoConditions :=
  beliTheoremTwo S

/-- Public unconditional equality clause of Beli (2003), Theorem 2. -/
theorem beliTheoremTwo_eq_unit_proved {t n : Nat}
    (S : HyperbolicTowerSplitting q L t n)
    (hconditions : S.SatisfiesTheoremTwoConditions) (ht : 0 < t) :
    spinorNormImageSubgroup (q := q) (L := L) =
      valuationUnitSquareClassSubgroup K :=
  beliTheoremTwo_eq_unit S hconditions ht

end Lattice

end Bong
