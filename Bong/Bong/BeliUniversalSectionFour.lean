/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalMaximal
import Bong.Lattice.OMaximalUniqueness
import Bong.Lattice.OmearaHyperbolicTowerDecomposition
import Bong.Lattice.OmearaHyperbolicTowerNormalizationScaled
import Bong.Bong.GoodBONGDeepIntegralExtensionProof
import Bong.Lattice.OmearaScaledHyperbolicTowerInvariants
import Bong.Lattice.OrthogonalDecompositionProduct

/-!
# Beli's universal-lattice criteria: Section 4

This file begins the formalization of Section 4 of C. N. Beli,
*Universal integral quadratic forms over dyadic local fields*.  The model
`halfHyperbolicExtensionForm r k` is the paper's
`2⁻¹ A(0,0)^k ⊥ r` and `halfHyperbolicExtensionLattice M k` is the
corresponding integral lattice.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {W : Type u} [AddCommGroup W] [Module K W]

/-- The field model of `2⁻¹ A(0,0)^k ⊥ r`. -/
noncomputable def halfHyperbolicExtensionForm
    (r : QuadraticSpace K W) :
    (k : Nat) → QuadraticSpace K (HyperbolicExtension K W k) :=
  fun k => omearaPlaneExtensionForm r (dyadicHalfUnit (K := K)) k
    (fun _ => 0)

/-- The integral lattice `2⁻¹ A(0,0)^k ⊥ M`. -/
noncomputable def halfHyperbolicExtensionLattice
    (M : Lattice K W) :
    (k : Nat) → Lattice K (HyperbolicExtension K W k) :=
  hyperbolicExtensionLattice M

theorem halfHyperbolicExtensionForm_eq
    (r : QuadraticSpace K W) (k : Nat) :
    halfHyperbolicExtensionForm r k =
      omearaPlaneExtensionForm r (dyadicHalfUnit (K := K)) k
        (fun _ => 0) :=
  rfl

theorem halfHyperbolicExtensionLattice_eq
    (M : Lattice K W) (k : Nat) :
    halfHyperbolicExtensionLattice M k = hyperbolicExtensionLattice M k :=
  rfl

/-- Beli, Lemma 4.2, in the half-hyperbolic model: maximal lattices split
exactly as many copies of `2⁻¹ A(0,0)` as their ambient spaces split
hyperbolic planes. -/
theorem beliUniversalLemma42
    {q : QuadraticSpace K V} {N : Lattice K V}
    {r : QuadraticSpace K W} {N' : Lattice K W}
    (hN : IsOMaximal q N) (hN' : IsOMaximal r N') :
    ∀ k : Nat,
      q.IsIsometric (halfHyperbolicExtensionForm r k) →
        IsIsometric q (halfHyperbolicExtensionForm r k) N
          (halfHyperbolicExtensionLattice N' k) := by
  letI : Module.Finite K W := N'.moduleFinite
  intro k
  induction k generalizing V with
  | zero =>
      intro ambient
      exact oMaximal_isIsometric_of_isometric hN hN' ambient
  | succ k ih =>
      intro ambient
      rcases ambient with ⟨g⟩
      let e0 : Fin 2 → K := ![1, 0]
      let z0 : HyperbolicExtension K W (k + 1) := (e0, 0)
      have hz0Ne : z0 ≠ 0 := by
        intro hz
        have hfirst := congrArg Prod.fst hz
        have hone := congrFun hfirst 0
        change (1 : K) = 0 at hone
        exact one_ne_zero hone
      have hz0Iso :
          (halfHyperbolicExtensionForm r (k + 1)).quadratic z0 = 0 := by
        change
          ((((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
            (dyadicHalfUnit (K := K))).orthogonalSum
            (halfHyperbolicExtensionForm r k)).quadratic z0) = 0
        rw [QuadraticSpace.orthogonalSum_quadratic_apply,
          QuadraticSpace.rescaleUnit_quadratic]
        simp [z0, e0, QuadraticSpace.quadratic,
          QuadraticSpace.omearaPlane_bilin_apply]
      let z : V := g.toLinearEquiv.symm z0
      have hzNe : z ≠ 0 := by
        intro hz
        have himage := congrArg g.toLinearEquiv hz
        apply hz0Ne
        simpa [z] using himage
      have hzIso : q.quadratic z = 0 := by
        have hmap := g.symm.map_quadratic z0
        exact hmap.trans hz0Iso
      let D := oMaximalRescaledTwoDecomposition hN hzNe hzIso
      let split := oMaximalHyperbolicSplitIsometry hN hzNe hzIso
      let tailForm :=
        (D.component 1).space.rescaleUnit (dyadicHalfUnit (K := K))
      let tailLattice := (D.component 1).lattice
      letI : Module.Finite K (D.component 1).carrier := tailLattice.moduleFinite
      letI : Module.Finite K (HyperbolicExtension K W k) :=
        (halfHyperbolicExtensionLattice N' k).moduleFinite
      have htailMax : IsOMaximal tailForm tailLattice :=
        oMaximalHyperbolicSplit_residual_isOMaximal hN hzNe hzIso
      let total : QuadraticSpace.Isometry
          ((QuadraticSpace.hyperbolicPlane
            (dyadicHalfUnit (K := K))).orthogonalSum tailForm)
          (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
            (dyadicHalfUnit (K := K))).orthogonalSum
            (halfHyperbolicExtensionForm r k)) :=
        split.toQuadraticSpaceIsometry.trans g
      let tailAmbient : QuadraticSpace.Isometry tailForm
          (halfHyperbolicExtensionForm r k) :=
        QuadraticSpace.orthogonalSumCancel
          (QuadraticSpace.hyperbolicPlane (dyadicHalfUnit (K := K)))
          ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
            (dyadicHalfUnit (K := K)))
          tailForm (halfHyperbolicExtensionForm r k)
          (scaledZeroOmearaPlaneLatticeIsometry
            (dyadicHalfUnit (K := K))).symm.toQuadraticSpaceIsometry total
      have htailIso : IsIsometric tailForm
          (halfHyperbolicExtensionForm r k) tailLattice
          (halfHyperbolicExtensionLattice N' k) :=
        ih htailMax ⟨tailAmbient⟩
      let tailIso := Classical.choice htailIso
      let headIso := (scaledZeroOmearaPlaneLatticeIsometry
        (dyadicHalfUnit (K := K))).symm
      exact ⟨split.symm.trans
        (headIso.orthogonalProductBasic tailIso)⟩

/-- Integrality bounds the scale ideal by `2⁻¹ O`.  This is the ideal
calculation used at the start of the proof of Beli's Lemma 4.3. -/
theorem scaleIdeal_le_half_of_isIntegral
    {q : QuadraticSpace K V} {L : Lattice K V}
    (hL : IsIntegral q L) :
    scaleIdeal q L ≤ principalIdeal (K := K)
      (dyadicHalfUnit (K := K) : K) := by
  intro z hz
  have hscaled : (2 : K) * z ∈
      scaleIdeal (q.rescaleUnit (Units.mk0 (2 : K) (by norm_num))) L := by
    rw [scaleIdeal_rescaleQuadraticUnit]
    change (2 : K) * z ∈ scalarIdeal (2 : K) (scaleIdeal q L)
    exact Submodule.mem_map_of_mem hz
  have htwo : (2 : K) * z ∈ IntegerRing K := by
    rw [← mem_unitIdeal_iff]
    exact scaleIdeal_rescaleTwo_le_unitIdeal hL hscaled
  rw [principalIdeal, Submodule.mem_span_singleton]
  refine ⟨⟨(2 : K) * z, htwo⟩, ?_⟩
  change (((2 : K) * z) * (dyadicHalfUnit (K := K) : K)) = z
  have hprod : (2 : K) * (dyadicHalfUnit (K := K) : K) = 1 := by
    change (dyadicTwoUnit (K := K) : K) *
      (dyadicHalfUnit (K := K) : K) = 1
    rw [← Units.val_mul]
    simp [dyadicHalfUnit]
  calc
    (2 : K) * z * (dyadicHalfUnit (K := K) : K) =
        (2 * (dyadicHalfUnit (K := K) : K)) * z := by ring
    _ = z := by rw [hprod, one_mul]

/-- The canonical integral inclusion of the left lattice factor. -/
def Representation.orthogonalProductInl
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (L : Lattice K V) (M : Lattice K W) :
    Representation q (q.orthogonalSum r) L (product L M) where
  toLinearMap :=
    { toFun := fun x => (x, 0)
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp }
  injective := by
    intro x y h
    exact congrArg Prod.fst h
  map_bilin := by intro x y; simp
  map_mem := by
    intro x hx
    rw [mem_product_iff]
    exact ⟨hx, M.zero_mem⟩

/-- A representation identifies its source lattice with its image
quadratic sublattice. -/
noncomputable def Representation.imageLatticeIsometry
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W}
    (f : Representation r q M L) :
    Isometry r f.imageComponent.space M f.imageComponent.lattice where
  toLinearEquiv := f.rangeEquiv
  map_bilin := f.map_bilin
  map_mem := by
    intro x
    change x ∈ M ↔ f.rangeEquiv x ∈ map f.rangeEquiv M
    exact (map_mem_map_iff f.rangeEquiv M x).symm

/-- The image lattice of an integral representation lies in the target. -/
theorem Representation.imageComponent_le
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W}
    (f : Representation r q M L) :
    f.imageComponent.ambientSubmodule ≤ L.toSubmodule := by
  rintro _ ⟨y, hy, rfl⟩
  change (y : V) ∈ L
  have hy' : f.rangeEquiv.symm y ∈ M :=
    (mem_map_iff f.rangeEquiv M y).mp hy
  have himage : (y : V) = f.toLinearMap (f.rangeEquiv.symm y) := by
    rw [← f.coe_rangeEquiv_apply]
    exact congrArg Subtype.val (f.rangeEquiv.apply_symm_apply y).symm
  rw [himage]
  exact f.map_mem hy'

/-- The direct recursive presentation of the zero-coefficient O'Meara
tower agrees with the named scaled tower. -/
theorem zeroOmearaExtensionForm_eq_scaled (a : Kˣ) :
    ∀ k : Nat,
      omearaPlaneExtensionForm
          (zeroCoordinateQuadraticSpace (K := K)) a k (fun _ => 0) =
        QuadraticSpace.scaledZeroOmearaTowerForm a k
  | 0 => rfl
  | k + 1 => by
      change
        ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit a).orthogonalSum
            (omearaPlaneExtensionForm
              (zeroCoordinateQuadraticSpace (K := K)) a k
                (Fin.tail (fun _ : Fin (k + 1) => (0 : K)))) =
          ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit a).orthogonalSum
            (QuadraticSpace.scaledZeroOmearaTowerForm a k)
      have htail : Fin.tail (fun _ : Fin (k + 1) => (0 : K)) =
          (fun _ : Fin k => 0) := by
        funext i
        rfl
      rw [htail, zeroOmearaExtensionForm_eq_scaled a k]

/-- The complement produced after splitting the represented standard
half-hyperbolic block. -/
structure HalfHyperbolicRepresentationSplitting
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {N : Lattice K W} (k : Nat) where
  Residual : Type u
  [residualAddCommGroup : AddCommGroup Residual]
  [residualModule : Module K Residual]
  residualForm : QuadraticSpace K Residual
  residualLattice : Lattice K Residual
  residualIntegral : IsIntegral residualForm residualLattice
  presentation : Isometry
    (halfHyperbolicExtensionForm residualForm k) q
    (halfHyperbolicExtensionLattice residualLattice k) L
  representsTail : Represents residualForm r residualLattice N

set_option maxHeartbeats 0 in
-- The explicit image-lattice and modular-splitting term is elaboration-heavy.
/-- A represented standard half-hyperbolic block splits from an integral
target, and the residual target still represents the source tail. -/
noncomputable def halfHyperbolicRepresentationSplitting
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {N : Lattice K W}
    (k : Nat) (hL : IsIntegral q L)
    (f : Representation (halfHyperbolicExtensionForm r k) q
      (halfHyperbolicExtensionLattice N k) L) :
    HalfHyperbolicRepresentationSplitting
      (q := q) (r := r) (L := L) (N := N) k := by
  letI : Module.Finite K V := L.moduleFinite
  let half : Kˣ := dyadicHalfUnit (K := K)
  let zeroForm := zeroCoordinateQuadraticSpace (K := K)
  let zeroLattice := QuadraticSpace.zeroCoordinateBasisLattice (K := K)
  let blockForm := omearaPlaneExtensionForm zeroForm half k (fun _ => 0)
  let blockLattice := hyperbolicExtensionLattice zeroLattice k
  let appendSource := omearaPlaneExtensionAppendIsometry
    zeroLattice r N half k (fun _ => 0)
  let fRaw : Representation
      (omearaPlaneExtensionForm r half k (fun _ => 0)) q
      (hyperbolicExtensionLattice N k) L := by
    rw [← halfHyperbolicExtensionForm_eq,
      ← halfHyperbolicExtensionLattice_eq]
    exact f
  let fullRepresentation : Representation (blockForm.orthogonalSum r) q
      (product blockLattice N) L :=
    fRaw.trans appendSource.toRepresentation
  let headInclusion := Representation.orthogonalProductInl
    blockForm r blockLattice N
  let headRepresentation : Representation blockForm q blockLattice L :=
    fullRepresentation.trans headInclusion
  let C := headRepresentation.imageComponent
  let headIsometry := headRepresentation.imageLatticeIsometry
  have hblockModular : IsModular blockForm blockLattice half := by
    dsimp only [blockForm, blockLattice, zeroForm, zeroLattice]
    rw [zeroOmearaExtensionForm_eq_scaled half k]
    exact scaledZeroOmearaTowerLattice_isModular half k
  have hCModular : IsModular C.space C.lattice half :=
    hblockModular.mapLatticeIsometry headIsometry
  have hcontained : C.ambientSubmodule ≤ L.toSubmodule :=
    headRepresentation.imageComponent_le
  have hscale : scaleIdeal q L ≤ principalIdeal (K := K) (half : K) :=
    scaleIdeal_le_half_of_isIntegral hL
  let hpair : ∀ (y : C.carrier), y ∈ C.lattice →
      ∀ x : V, x ∈ L →
        q.bilin (y : V) x ∈ principalIdeal (K := K) (half : K) :=
    fun y hy x hx => hscale (bilin_mem_scaleIdeal_of_mem q L
      (hcontained ⟨y, hy, rfl⟩) hx)
  let D : OrthogonalDecomposition q L 2 :=
    omearaModularSplitting C hcontained hCModular hpair
  let residual := C.orthogonalSublattice hcontained hCModular hpair
  have hresidualIntegral : IsIntegral residual.space residual.lattice := by
    rw [isIntegral_iff_forall]
    intro x hx
    apply (isIntegral_iff_forall q L).mp hL (x : V)
    exact D.component_ambientSubmodule_le 1 ⟨x, hx, rfl⟩
  let appendResidual := omearaPlaneExtensionAppendIsometry
    zeroLattice residual.space residual.lattice half k (fun _ => 0)
  let displayed : Isometry
      (blockForm.orthogonalSum residual.space) q
      (product blockLattice residual.lattice) L :=
    (headIsometry.orthogonalProductBasic
      (Isometry.refl residual.space residual.lattice)).trans
        D.pairProductLatticeIsometry
  let presentation : Isometry
      (halfHyperbolicExtensionForm residual.space k) q
      (halfHyperbolicExtensionLattice residual.lattice k) L := by
    rw [halfHyperbolicExtensionForm_eq,
      halfHyperbolicExtensionLattice_eq]
    exact appendResidual.symm.trans displayed
  have tailOrthogonal (x : W) :
      fullRepresentation.toLinearMap (0, x) ∈ C.orthogonalCarrier := by
    intro y hy
    rcases hy with ⟨a, ha⟩
    subst y
    change q.bilin
      (fullRepresentation.toLinearMap (a, 0))
      (fullRepresentation.toLinearMap (0, x)) = 0
    have hmap := fullRepresentation.map_bilin (a, 0) (0, x)
    simpa using hmap
  let tailLinearMap : W →ₗ[K] C.orthogonalCarrier :=
    { toFun := fun x => ⟨fullRepresentation.toLinearMap (0, x),
        tailOrthogonal x⟩
      map_add' := by
        intro x y
        ext
        simpa using fullRepresentation.toLinearMap.map_add (0, x) (0, y)
      map_smul' := by
        intro c x
        ext
        simpa using fullRepresentation.toLinearMap.map_smul c (0, x) }
  have htailInjective : Function.Injective tailLinearMap := by
    intro x y hxy
    have hval := congrArg Subtype.val hxy
    have hin :
        ((0 : HyperbolicExtension K (Fin 0 → K) k), x) =
          ((0 : HyperbolicExtension K (Fin 0 → K) k), y) :=
      fullRepresentation.injective hval
    exact congrArg Prod.snd hin
  have htailBilin (x y : W) :
      (C.orthogonalSublattice hcontained hCModular hpair).space.bilin
          (tailLinearMap x) (tailLinearMap y) = r.bilin x y := by
    have hmap := fullRepresentation.map_bilin (0, x) (0, y)
    change q.bilin (tailLinearMap x : V) (tailLinearMap y : V) =
      r.bilin x y
    have hxcoe : (tailLinearMap x : V) =
        fullRepresentation.toLinearMap (0, x) := rfl
    have hycoe : (tailLinearMap y : V) =
        fullRepresentation.toLinearMap (0, y) := rfl
    rw [hxcoe, hycoe]
    simpa using hmap
  have htailMem {x : W} (hx : x ∈ N) : tailLinearMap x ∈
      (C.orthogonalSublattice hcontained hCModular hpair).lattice := by
    change (tailLinearMap x : V) ∈ L
    apply fullRepresentation.map_mem
    rw [mem_product_iff]
    exact ⟨blockLattice.zero_mem, hx⟩
  let tailRepresentation : Representation r
      (C.orthogonalSublattice hcontained hCModular hpair).space N
      (C.orthogonalSublattice hcontained hCModular hpair).lattice :=
    { toLinearMap := tailLinearMap
      injective := htailInjective
      map_bilin := htailBilin
      map_mem := htailMem }
  exact
    { Residual := residual.carrier
      residualForm := residual.space
      residualLattice := residual.lattice
      residualIntegral := hresidualIntegral
      presentation := presentation
      representsTail := ⟨tailRepresentation⟩ }

end Lattice

end Bong
