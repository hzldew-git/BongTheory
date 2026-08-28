/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328NecessityLastBoundary
import Bong.Lattice.VolumeInclusion

/-!
# O'Meara 93:3: norm-preserving unimodular enlargement

On a finite hyperbolic tower, every unit-scale lattice is contained in a
unimodular lattice with the same norm group.  The proof follows O'Meara's
maximal-lattice argument, replacing maximality by minimization of the
nonnegative lattice volume order.  Minimality first gives closure under all
isotropic vectors of the integral dual.  A primitive isotropic line then
has a unit partner; the resulting unimodular hyperbolic plane splits by
82:15, and the argument recurses on its orthogonal complement.

No maximal-lattice law or choice of a Jordan decomposition is assumed.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

theorem volumeOrder_nonneg_of_scaleIdeal_le_unitIdeal
    (hscale : scaleIdeal q L ≤ unitIdeal (K := K)) :
    0 ≤ volumeOrder q L := by
  let G : Matrix (Fin (finrank K V)) (Fin (finrank K V))
      (IntegerRing K) := fun i j ↦
    ⟨integralGramMatrix q L i j, by
      rw [integralGramMatrix_apply]
      exact mem_unitIdeal_iff.mp
        (hscale (bilin_mem_scaleIdeal q L
          ⟨L.standardAmbientBasis i, by
            rw [← L.coe_standardIntegralBasis_apply i]
            exact (L.standardIntegralBasis i).property⟩
          ⟨L.standardAmbientBasis j, by
            rw [← L.coe_standardIntegralBasis_apply j]
            exact (L.standardIntegralBasis j).property⟩))⟩
  have hdetIntegral : determinant q L ∈ IntegerRing K := by
    let d : IntegerRing K := G.det
    have hmap : ((d : IntegerRing K) : K) = determinant q L := by
      change algebraMap (IntegerRing K) K G.det =
        (integralGramMatrix q L).det
      rw [RingHom.map_det]
      congr 1
    rw [← hmap]
    exact d.property
  have hnonneg := ordUnit_nonneg_of_mem_integerRing
    (determinantUnit q L) (by simpa using hdetIntegral)
  have hvolume : volumeOrder q L = ordUnit K (determinantUnit q L) := by
    apply WithTop.coe_injective
    rw [coe_volumeOrder, coe_ordUnit, coe_determinantUnit]
  rwa [hvolume]

/-- Lattices allowed in the maximal-lattice argument of O'Meara 93:3. -/
structure Omeara933Candidate (q : QuadraticSpace K V)
    (L : Lattice K V) where
  lattice : Lattice K V
  contains : L ≤ lattice
  scale_eq : scaleIdeal q lattice = unitIdeal (K := K)
  normGroup_eq : normGroupSet q lattice = normGroupSet q L

namespace Omeara933Candidate

variable (q L)

def initial (hscale : scaleIdeal q L = unitIdeal (K := K)) :
    Omeara933Candidate q L where
  lattice := L
  contains := fun _ hx ↦ hx
  scale_eq := hscale
  normGroup_eq := rfl

theorem volumeOrder_nonneg (C : Omeara933Candidate q L) :
    0 ≤ volumeOrder q C.lattice :=
  volumeOrder_nonneg_of_scaleIdeal_le_unitIdeal C.scale_eq.le

end Omeara933Candidate

/-- A candidate of smallest volume order.  Since volume order is a
nonnegative integer on integral lattices, this is an ordinary application
of well-ordering of the natural numbers, not a Zorn argument. -/
structure Omeara933MinimalData (q : QuadraticSpace K V)
    (L : Lattice K V) where
  candidate : Omeara933Candidate q L
  minimal : ∀ D : Omeara933Candidate q L,
    volumeOrder q candidate.lattice ≤ volumeOrder q D.lattice

noncomputable def omeara933MinimalData
    (hscale : scaleIdeal q L = unitIdeal (K := K)) :
    Omeara933MinimalData q L := by
  classical
  let ExistsAt : Nat → Prop := fun n ↦
    ∃ C : Omeara933Candidate q L,
      volumeOrder q C.lattice = (n : Int)
  have hexists : ∃ n, ExistsAt n := by
    let C := Omeara933Candidate.initial q L hscale
    refine ⟨(volumeOrder q L).toNat, C, ?_⟩
    dsimp only [C, Omeara933Candidate.initial]
    exact (Int.toNat_of_nonneg
      (Omeara933Candidate.volumeOrder_nonneg q L C)).symm
  let n := Nat.find hexists
  have hn : ExistsAt n := Nat.find_spec hexists
  let C : Omeara933Candidate q L := Classical.choose hn
  have hC : volumeOrder q C.lattice = (n : Int) :=
    Classical.choose_spec hn
  refine ⟨C, ?_⟩
  intro D
  have hDnonneg := D.volumeOrder_nonneg q L
  have hDexists : ExistsAt (volumeOrder q D.lattice).toNat := by
    refine ⟨D, ?_⟩
    rw [Int.toNat_of_nonneg hDnonneg]
  have hnat : n ≤ (volumeOrder q D.lattice).toNat := by
    simpa only [n] using Nat.find_min' hexists hDexists
  rw [hC]
  calc
    (n : Int) ≤ ((volumeOrder q D.lattice).toNat : Nat) := by
      exact_mod_cast hnat
    _ = volumeOrder q D.lattice := by
      exact Int.toNat_of_nonneg hDnonneg

namespace Omeara933MinimalData

variable (D : Omeara933MinimalData q L)

/-- A volume-minimal candidate has no proper enlargement which is still a
candidate. -/
theorem eq_of_candidate_of_le (C : Omeara933Candidate q L)
    (hle : D.candidate.lattice ≤ C.lattice) :
    C.lattice = D.candidate.lattice := by
  apply (eq_comm.mp (eq_of_le_of_volumeOrder_eq q
    D.candidate.lattice C.lattice hle ?_))
  exact le_antisymm (D.minimal C)
    (volumeOrder_mono_of_le q hle)

end Omeara933MinimalData

/-- Twice an integral scalar belongs to `2sK` when `K` has unit scale. -/
theorem two_mul_mem_twoScaleIdeal_of_scaleIdeal_eq_unitIdeal
    {K₀ : Lattice K V}
    (hscale : scaleIdeal q K₀ = unitIdeal (K := K))
    {z : K} (hz : z ∈ IntegerRing K) :
    (2 : K) * z ∈ twoScaleIdeal q K₀ := by
  have hzScale : z ∈ scaleIdeal q K₀ := by
    rw [hscale]
    exact mem_unitIdeal_iff.mpr hz
  change (2 : K) * z ∈
    (scaleIdeal q K₀).map (twoMulLinearMap (K := K))
  refine ⟨z, hzScale, ?_⟩
  change ((2 : IntegerRing K) : K) * z = (2 : K) * z
  rfl

/-- Adjoining an isotropic vector from the integral dual preserves the
unit scale and the scalar norm group. -/
noncomputable def Omeara933Candidate.adjoinIsotropicDual
    (C : Omeara933Candidate q L) (x : V)
    (hxdual : x ∈ dualLattice q C.lattice)
    (hxisotropic : q.quadratic x = 0) :
    Omeara933Candidate q L := by
  let K' := adjoinVector C.lattice x
  have hscaleLe : scaleIdeal q K' ≤ unitIdeal (K := K) := by
    rw [scaleIdeal, Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    rcases (mem_adjoinVector_iff.mp p.1.property) with
      ⟨y, hy, a, hay⟩
    rcases (mem_adjoinVector_iff.mp p.2.property) with
      ⟨z, hz, b, hbz⟩
    have hyz : q.bilin y z ∈ IntegerRing K := by
      exact mem_unitIdeal_iff.mp (C.scale_eq.le
        (bilin_mem_scaleIdeal_of_mem q C.lattice hy hz))
    have hxy : q.bilin x y ∈ IntegerRing K :=
      (mem_dualLattice_iff q C.lattice x).mp hxdual y hy
    have hyx : q.bilin y x ∈ IntegerRing K := by
      rw [q.isSymm.eq y x]
      exact hxy
    have hxz : q.bilin x z ∈ IntegerRing K :=
      (mem_dualLattice_iff q C.lattice x).mp hxdual z hz
    have hxx : q.bilin x x = 0 := hxisotropic
    change q.bilin (p.1 : V) (p.2 : V) ∈ unitIdeal (K := K)
    rw [← hay, ← hbz]
    change q.bilin (y + (a : K) • x) (z + (b : K) • x) ∈
      unitIdeal (K := K)
    simp only [LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right]
    rw [hxx]
    apply mem_unitIdeal_iff.mpr
    have ha : (a : K) ∈ IntegerRing K := a.property
    have hb : (b : K) ∈ IntegerRing K := b.property
    have hinner : q.bilin y x + (a : K) * 0 ∈
        IntegerRing K := by
      simpa using hyx
    exact (IntegerRing K).toSubring.add_mem
      ((IntegerRing K).toSubring.add_mem hyz
        ((IntegerRing K).toSubring.mul_mem ha hxz))
      ((IntegerRing K).toSubring.mul_mem hb hinner)
  have hscaleEq : scaleIdeal q K' = unitIdeal (K := K) := by
    apply le_antisymm hscaleLe
    rw [← C.scale_eq]
    exact scaleIdeal_mono q (le_adjoinVector C.lattice x)
  have hgroupEq : normGroupSet q K' = normGroupSet q C.lattice := by
    apply Set.Subset.antisymm
    · rintro w ⟨v, hv, t, ht, rfl⟩
      rcases mem_adjoinVector_iff.mp hv with ⟨y, hy, a, rfl⟩
      have hxy : q.bilin x y ∈ IntegerRing K :=
        (mem_dualLattice_iff q C.lattice x).mp hxdual y hy
      have hay : (a : K) * q.bilin x y ∈ IntegerRing K :=
        (IntegerRing K).toSubring.mul_mem a.property hxy
      let cross : K := (2 : K) * ((a : K) * q.bilin x y)
      have hcross : cross ∈
          twoScaleIdeal q C.lattice :=
        two_mul_mem_twoScaleIdeal_of_scaleIdeal_eq_unitIdeal C.scale_eq hay
      have ht' : t ∈ twoScaleIdeal q C.lattice := by
        change t ∈ twiceIdeal (scaleIdeal q K') at ht
        rw [hscaleEq] at ht
        change t ∈ twiceIdeal (scaleIdeal q C.lattice)
        rw [C.scale_eq]
        exact ht
      have hsum : cross + t ∈ twoScaleIdeal q C.lattice :=
        (twoScaleIdeal q C.lattice).add_mem hcross ht'
      refine ⟨y, hy, cross + t, hsum, ?_⟩
      change q.quadratic (y + (a : K) • x) + t =
        q.quadratic y + (cross + t)
      rw [q.quadratic_add, q.quadratic_smul, hxisotropic]
      simp only [mul_zero]
      rw [LinearMap.BilinForm.smul_right]
      rw [q.isSymm.eq y x]
      dsimp only [cross]
      ring
    · exact normGroupSet_mono (le_adjoinVector C.lattice x)
  exact {
    lattice := K'
    contains := fun _ hz ↦ le_adjoinVector C.lattice x (C.contains hz)
    scale_eq := hscaleEq
    normGroup_eq := hgroupEq.trans C.normGroup_eq }

namespace Omeara933MinimalData

/-- Every isotropic vector in the integral dual of a volume-minimal
candidate already belongs to the candidate. -/
theorem isotropic_mem_of_mem_dual
    (D : Omeara933MinimalData q L) {x : V}
    (hxdual : x ∈ dualLattice q D.candidate.lattice)
    (hxisotropic : q.quadratic x = 0) :
    x ∈ D.candidate.lattice := by
  let C := D.candidate.adjoinIsotropicDual x hxdual hxisotropic
  have hle : D.candidate.lattice ≤ C.lattice := by
    intro z hz
    change z ∈ adjoinVector D.candidate.lattice x
    exact le_adjoinVector D.candidate.lattice x hz
  have heq := D.eq_of_candidate_of_le C hle
  have hx : x ∈ C.lattice := by
    change x ∈ adjoinVector D.candidate.lattice x
    exact mem_adjoinVector D.candidate.lattice x
  rwa [heq] at hx

end Omeara933MinimalData

/-- The division-by-uniformizer contradiction in O'Meara 93:3.  A
primitive isotropic vector in an integral lattice which contains all
isotropic vectors of its integral dual has a unit pairing with the
lattice. -/
theorem exists_isValuationUnit_pairing_of_isotropicDual_closed
    {K₀ : Lattice K V}
    (hscale : scaleIdeal q K₀ ≤ unitIdeal (K := K))
    (hclosed : ∀ {z : V}, z ∈ dualLattice q K₀ →
      q.quadratic z = 0 → z ∈ K₀)
    {x : V} (hx : x ∈ K₀)
    (hprimitive : x ∉ rescale (uniformizerUnit K) K₀)
    (hxisotropic : q.quadratic x = 0) :
    ∃ y : V, y ∈ K₀ ∧ IsValuationUnit K (q.bilin x y) := by
  classical
  by_contra hnone
  push Not at hnone
  have hscaledDual :
      (((uniformizerUnit K)⁻¹ : Kˣ) : K) • x ∈ dualLattice q K₀ := by
    rw [mem_dualLattice_iff]
    intro y hy
    have hxyIntegral : q.bilin x y ∈ IntegerRing K := by
      exact mem_unitIdeal_iff.mp (hscale
        (bilin_mem_scaleIdeal_of_mem q K₀ hx hy))
    by_cases hxy : q.bilin x y = 0
    · rw [LinearMap.BilinForm.smul_left, hxy, mul_zero]
      exact (IntegerRing K).zero_mem
    · let b : Kˣ := Units.mk0 (q.bilin x y) hxy
      have hbNonneg : 0 ≤ ordUnit K b :=
        ordUnit_nonneg_of_mem_integerRing b (by simpa [b] using hxyIntegral)
      have hbNe : ordUnit K b ≠ 0 := by
        intro hbZero
        apply hnone y hy
        simpa [b] using (isValuationUnit_iff_ordUnit_eq_zero K b).2 hbZero
      have hbOne : 1 ≤ ordUnit K b := by omega
      have hpi : ordUnit K (uniformizerUnit K) = 1 := by
        simpa [uniformizerPowerUnit] using
          (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
      have hproductNonneg :
          0 ≤ ordUnit K ((uniformizerUnit K)⁻¹ * b) := by
        rw [ordUnit_mul, ordUnit_inv, hpi]
        omega
      rw [LinearMap.BilinForm.smul_left]
      apply (mem_integerRing_iff K).2
      change (0 : WithTop Int) ≤
        ord K (((((uniformizerUnit K)⁻¹ * b : Kˣ) : K)))
      rw [← coe_ordUnit]
      exact_mod_cast hproductNonneg
  have hscaledIsotropic :
      q.quadratic ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • x) = 0 := by
    rw [q.quadratic_smul, hxisotropic, mul_zero]
  have hscaledMem := hclosed hscaledDual hscaledIsotropic
  apply hprimitive
  have hrescaled := smul_mem_rescale (uniformizerUnit K) K₀ hscaledMem
  simpa [smul_smul, uniformizer_ne_zero K] using hrescaled

/-- Over the field, every O'Meara plane `A(alpha,0)` is the standard
hyperbolic plane.  Integrality is deliberately not asserted: the shear
uses `alpha / 2`. -/
noncomputable def omearaPlaneToHyperbolicSpaceIsometry (alpha : K) :
    QuadraticSpace.Isometry
      (QuadraticSpace.omearaPlane alpha)
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ)) := by
  let c : K := alpha / 2
  let e : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) :=
    { toFun := fun x ↦ ![x 0, x 1 + c * x 0]
      invFun := fun x ↦ ![x 0, x 1 - c * x 0]
      left_inv := by
        intro x
        funext i
        fin_cases i <;> simp [c]
      right_inv := by
        intro x
        funext i
        fin_cases i <;> simp [c]
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp [c] <;> ring
      map_smul' := by
        intro a x
        funext i
        fin_cases i <;> simp [c] <;> ring }
  exact
    { toLinearEquiv := e
      map_bilin := by
        intro x y
        rw [QuadraticSpace.hyperbolicPlane_bilin_apply,
          QuadraticSpace.omearaPlane_bilin_apply]
        change (1 : K) *
            (x 0 * (y 1 + c * y 0) +
              (x 1 + c * x 0) * y 0) =
          alpha * x 0 * y 0 + x 0 * y 1 + x 1 * y 0
        dsimp only [c]
        field_simp
        <;> ring }

section PrimitivePlane

variable {K₀ : Lattice K V} {x y : V}

theorem unitPair_ne (hxy : q.bilin x y = 1) :
    q.bilin x y ≠ 0 := by
  rw [hxy]
  exact one_ne_zero

theorem unitPair_left_strict (hxy : q.bilin x y = 1)
    (hxisotropic : q.quadratic x = 0) :
    ord K (q.bilin x y) < ord K (q.quadratic x) := by
  rw [hxy, hxisotropic, ord_one, ord_zero]
  exact WithTop.coe_lt_top 0

theorem unitPair_right_weak (hxy : q.bilin x y = 1)
    (hyIntegral : q.quadratic y ∈ IntegerRing K) :
    ord K (q.bilin x y) ≤ ord K (q.quadratic y) := by
  rw [hxy, ord_one]
  exact (mem_integerRing_iff K).1 hyIntegral

/-- The binary component generated by an isotropic vector and a partner
pairing to one. -/
noncomputable def omeara933PlaneComponent
    (hxy : q.bilin x y = 1)
    (hxisotropic : q.quadratic x = 0)
    (hyIntegral : q.quadratic y ∈ IntegerRing K) :
    QuadraticSublattice q :=
  asymmetricBinaryScaleComponent (q := q)
    (unitPair_ne hxy)
    (unitPair_left_strict hxy hxisotropic)
    (unitPair_right_weak hxy hyIntegral)

/-- The displayed binary component is the O'Meara plane
`A(Q(y),0)`. -/
noncomputable def omeara933PlaneComponentIsometry
    (hxy : q.bilin x y = 1)
    (hxisotropic : q.quadratic x = 0)
    (hyIntegral : q.quadratic y ∈ IntegerRing K) :
    Isometry
      (QuadraticSpace.omearaPlane (q.quadratic y))
      (omeara933PlaneComponent hxy hxisotropic hyIntegral).space
      (hyperbolicPlaneLattice (K := K))
      (omeara933PlaneComponent hxy hxisotropic hyIntegral).lattice := by
  let hne := unitPair_ne hxy
  let hleft := unitPair_left_strict hxy hxisotropic
  let hright := unitPair_right_weak hxy hyIntegral
  let P := BONG.binaryPairSpan (K := K) x y
  let hli := binaryPair_linearIndependent_of_left_strict hne hleft hright
  let b : Basis (Fin 2) K P := BONG.binaryPairBasis (K := K) x y hli
  let C : QuadraticSublattice q :=
    asymmetricBinaryScaleComponent (q := q) hne hleft hright
  let swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  let c : Basis (Fin 2) K P := b.reindex swap
  let sourceBasis : Basis (Fin 2) K (Fin 2 → K) :=
    Pi.basisFun K (Fin 2)
  have hc0 : (c 0 : V) = y := by
    simp only [c, Basis.coe_reindex, Function.comp_apply]
    rw [show swap.symm 0 = 1 by simp [swap]]
    change ((b 1 : P) : V) = y
    rw [show ((b 1 : P) : V) = BONG.binaryPairFamily x y 1 by
      exact BONG.coe_binaryPairBasis x y hli 1]
    exact BONG.binaryPairFamily_one x y
  have hc1 : (c 1 : V) = x := by
    simp only [c, Basis.coe_reindex, Function.comp_apply]
    rw [show swap.symm 1 = 0 by simp [swap]]
    change ((b 0 : P) : V) = x
    rw [show ((b 0 : P) : V) = BONG.binaryPairFamily x y 0 by
      exact BONG.coe_binaryPairBasis x y hli 0]
    exact BONG.binaryPairFamily_zero x y
  have hgram : ∀ i j,
      C.space.bilin (c i) (c j) =
        (QuadraticSpace.omearaPlane (q.quadratic y)).bilin
          (sourceBasis i) (sourceBasis j) := by
    intro i j
    fin_cases i <;> fin_cases j
    · change q.bilin (c 0 : V) (c 0 : V) = _
      rw [hc0]
      simp [sourceBasis, QuadraticSpace.omearaPlane_bilin_apply,
        QuadraticSpace.quadratic]
    · change q.bilin (c 0 : V) (c 1 : V) = _
      rw [hc0, hc1, q.isSymm.eq y x, hxy]
      simp [sourceBasis, QuadraticSpace.omearaPlane_bilin_apply]
    · change q.bilin (c 1 : V) (c 0 : V) = _
      rw [hc0, hc1, hxy]
      simp [sourceBasis, QuadraticSpace.omearaPlane_bilin_apply]
    · change q.bilin (c 1 : V) (c 1 : V) = _
      rw [hc1]
      change q.quadratic x = _
      rw [hxisotropic]
      simp [sourceBasis, QuadraticSpace.omearaPlane_bilin_apply]
  let raw := Classical.choice
    (basisLattice_isIsometric_of_gram_eq
      (QuadraticSpace.omearaPlane (q.quadratic y))
      C.space sourceBasis c hgram)
  have hc : basisLattice c = C.lattice := by
    calc
      basisLattice c = basisLattice b := basisLattice_reindex b swap
      _ = C.lattice := by rfl
  let identify := Isometry.ofLatticeEq C.space hc
  change Isometry
    (QuadraticSpace.omearaPlane (q.quadratic y)) C.space
    (hyperbolicPlaneLattice (K := K)) C.lattice
  simpa only [hyperbolicPlaneLattice, sourceBasis] using
    raw.trans identify

end PrimitivePlane

/-- The primitive isotropic pair selected in the proof of 93:3, normalized
so that its mixed pairing is exactly one. -/
structure Omeara933PlaneData (q : QuadraticSpace K V)
    (K₀ : Lattice K V) (x : V) where
  partner : V
  partner_mem : partner ∈ K₀
  pairing_eq : q.bilin x partner = 1
  partner_quadratic_integral : q.quadratic partner ∈ IntegerRing K

/-- Select and normalize the unit partner supplied by the
division-by-uniformizer argument. -/
noncomputable def omeara933PlaneData
    {K₀ : Lattice K V}
    (hscale : scaleIdeal q K₀ ≤ unitIdeal (K := K))
    (hclosed : ∀ {z : V}, z ∈ dualLattice q K₀ →
      q.quadratic z = 0 → z ∈ K₀)
    {x : V} (hx : x ∈ K₀)
    (hprimitive : x ∉ rescale (uniformizerUnit K) K₀)
    (hxisotropic : q.quadratic x = 0) :
    Omeara933PlaneData q K₀ x := by
  let hexists := exists_isValuationUnit_pairing_of_isotropicDual_closed
    hscale hclosed hx hprimitive hxisotropic
  let y₀ := Classical.choose hexists
  have hy₀ : y₀ ∈ K₀ := (Classical.choose_spec hexists).1
  have hunit : IsValuationUnit K (q.bilin x y₀) :=
    (Classical.choose_spec hexists).2
  have hne : q.bilin x y₀ ≠ 0 := ne_zero_of_isValuationUnit hunit
  let b : Kˣ := Units.mk0 (q.bilin x y₀) hne
  have hbOrder : ordUnit K b = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K b).1 (by simpa [b] using hunit)
  have hbinvIntegral : ((b⁻¹ : Kˣ) : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    change (0 : WithTop Int) ≤ ord K ((b⁻¹ : Kˣ) : K)
    rw [← coe_ordUnit, ordUnit_inv, hbOrder]
    norm_num
  let y : V := ((b⁻¹ : Kˣ) : K) • y₀
  have hy : y ∈ K₀ := by
    let c : IntegerRing K := ⟨((b⁻¹ : Kˣ) : K), hbinvIntegral⟩
    have := K₀.smul_mem c hy₀
    rw [← IsScalarTower.algebraMap_smul K c y₀] at this
    have hcoe : algebraMap (IntegerRing K) K c = ((b⁻¹ : Kˣ) : K) := rfl
    rw [hcoe] at this
    exact this
  have hpair : q.bilin x y = 1 := by
    dsimp only [y]
    rw [LinearMap.BilinForm.smul_right]
    change ((b⁻¹ : Kˣ) : K) * (b : K) = 1
    simp
  have hyQuadratic : q.quadratic y ∈ IntegerRing K := by
    exact mem_unitIdeal_iff.mp (hscale
      (bilin_mem_scaleIdeal_of_mem q K₀ hy hy))
  exact ⟨y, hy, hpair, hyQuadratic⟩

namespace Omeara933PlaneData

variable {K₀ : Lattice K V} {x : V}
  (D : Omeara933PlaneData q K₀ x)

noncomputable def component (hxisotropic : q.quadratic x = 0) :
    QuadraticSublattice q :=
  omeara933PlaneComponent D.pairing_eq hxisotropic
    D.partner_quadratic_integral

theorem component_contained (hxisotropic : q.quadratic x = 0)
    (hx : x ∈ K₀) :
    (D.component hxisotropic).ambientSubmodule ≤ K₀.toSubmodule := by
  exact asymmetricBinaryScaleComponent_ambientSubmodule_le
    (unitPair_ne D.pairing_eq)
    (unitPair_left_strict D.pairing_eq hxisotropic)
    (unitPair_right_weak D.pairing_eq D.partner_quadratic_integral)
    hx D.partner_mem

theorem component_unimodular (hxisotropic : q.quadratic x = 0) :
    IsUnimodular (D.component hxisotropic).space
      (D.component hxisotropic).lattice := by
  have hmod := asymmetricBinaryScaleComponent_isModular
    (unitPair_ne D.pairing_eq)
    (unitPair_left_strict D.pairing_eq hxisotropic)
    (unitPair_right_weak D.pairing_eq D.partner_quadratic_integral)
  have hunitEq :
      Units.mk0 (q.bilin x D.partner) (unitPair_ne D.pairing_eq) =
        (1 : Kˣ) := by
    apply Units.ext
    simpa using D.pairing_eq
  change IsModular
    (asymmetricBinaryScaleComponent (q := q)
      (unitPair_ne D.pairing_eq)
      (unitPair_left_strict D.pairing_eq hxisotropic)
      (unitPair_right_weak D.pairing_eq
        D.partner_quadratic_integral)).space
    (asymmetricBinaryScaleComponent (q := q)
      (unitPair_ne D.pairing_eq)
      (unitPair_left_strict D.pairing_eq hxisotropic)
      (unitPair_right_weak D.pairing_eq
        D.partner_quadratic_integral)).lattice
    (1 : Kˣ)
  rw [← hunitEq]
  exact hmod

noncomputable def splitting
    (hscale : scaleIdeal q K₀ ≤ unitIdeal (K := K))
    (hxisotropic : q.quadratic x = 0) (hx : x ∈ K₀) :
    OrthogonalDecomposition q K₀ 2 :=
  omearaModularSplittingOfScaleIdealLe
    (D.component hxisotropic)
    (D.component_contained hxisotropic hx)
    (D.component_unimodular hxisotropic)
    hscale

/-- The split component is hyperbolic over the field. -/
noncomputable def componentSpaceIsometry
    (hxisotropic : q.quadratic x = 0) :
    QuadraticSpace.Isometry (D.component hxisotropic).space
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ)) :=
  (omeara933PlaneComponentIsometry D.pairing_eq hxisotropic
      D.partner_quadratic_integral).symm.toQuadraticSpaceIsometry.trans
    (omearaPlaneToHyperbolicSpaceIsometry (q.quadratic D.partner))

end Omeara933PlaneData

namespace OrthogonalDecomposition

/-- Isotropic-dual closure descends to the right component of an integral
binary orthogonal decomposition. -/
theorem right_isotropicDual_closed
    (S : OrthogonalDecomposition q L 2)
    (hclosed : ∀ {z : V}, z ∈ dualLattice q L →
      q.quadratic z = 0 → z ∈ L) :
    ∀ {z : (S.component 1).carrier},
      z ∈ dualLattice (S.component 1).space
          (S.component 1).lattice →
      (S.component 1).space.quadratic z = 0 →
      z ∈ (S.component 1).lattice := by
  intro z hzDual hzIsotropic
  have hzAmbientDual : (z : V) ∈ dualLattice q L := by
    rw [mem_dualLattice_iff]
    intro y hy
    let p := S.pairProductLatticeIsometry.toLinearEquiv.symm y
    have hpMem : p ∈ product (S.component 0).lattice
        (S.component 1).lattice := by
      apply (S.pairProductLatticeIsometry.map_mem p).mpr
      rw [show S.pairProductLatticeIsometry.toLinearEquiv p = y by
        exact S.pairProductLatticeIsometry.toLinearEquiv.apply_symm_apply y]
      exact hy
    have hpParts := mem_product_iff.mp hpMem
    have hyDecomp : (p.1 : V) + (p.2 : V) = y := by
      change S.pairProductLatticeIsometry.toLinearEquiv p = y
      exact S.pairProductLatticeIsometry.toLinearEquiv.apply_symm_apply y
    have horth : q.bilin (z : V) (p.1 : V) = 0 :=
      S.orthogonal 1 0 (by decide) z p.1
    have hright : q.bilin (z : V) (p.2 : V) ∈ IntegerRing K := by
      exact (mem_dualLattice_iff (S.component 1).space
        (S.component 1).lattice z).mp hzDual p.2 hpParts.2
    rw [← hyDecomp, LinearMap.BilinForm.add_right, horth, zero_add]
    exact hright
  have hzAmbientIsotropic : q.quadratic (z : V) = 0 := by
    exact hzIsotropic
  have hzAmbientMem : (z : V) ∈ L :=
    hclosed hzAmbientDual hzAmbientIsotropic
  have hpairMem : (0, z) ∈ product (S.component 0).lattice
      (S.component 1).lattice := by
    apply (S.pairProductLatticeIsometry.map_mem (0, z)).mpr
    simpa using hzAmbientMem
  exact (mem_product_iff.mp hpairMem).2

end OrthogonalDecomposition

/-- O'Meara 93:3, recursive core: on a finite hyperbolic tower, an
integral-scale lattice containing every isotropic vector of its integral
dual is unimodular. -/
theorem isUnimodular_of_isotropicDual_closed_of_hyperbolicTower
    (n : Nat)
    (htower : q.IsIsometric
      (hyperbolicExtensionForm
        (zeroCoordinateQuadraticSpace (K := K)) n))
    (hscale : scaleIdeal q L ≤ unitIdeal (K := K))
    (hclosed : ∀ {z : V}, z ∈ dualLattice q L →
      q.quadratic z = 0 → z ∈ L) :
    IsUnimodular q L := by
  induction n generalizing V with
  | zero =>
      letI : Module.Finite K V := L.moduleFinite
      rcases htower with ⟨f⟩
      have hfin : finrank K V = 0 := by
        have hf := f.toLinearEquiv.finrank_eq
        change finrank K V = finrank K (Fin 0 → K) at hf
        rw [Module.finrank_fin_fun] at hf
        exact hf
      letI : Subsingleton V := Module.finrank_zero_iff.mp hfin
      rw [isUnimodular_iff_dualLattice_eq]
      apply Lattice.ext
      ext z
      have hz : z = 0 := Subsingleton.elim z 0
      subst z
      simp
  | succ n ih =>
      letI : Module.Finite K V := L.moduleFinite
      rcases htower with ⟨f⟩
      let tailForm := hyperbolicExtensionForm
        (zeroCoordinateQuadraticSpace (K := K)) n
      let z : V := f.toLinearEquiv.symm
        (hyperbolicFirstInSum (K := K)
          (W := HyperbolicExtension K (Fin 0 → K) n))
      have hzNe : z ≠ 0 := by
        intro hz
        have himage := congrArg f.toLinearEquiv hz
        apply hyperbolicFirstInSum_ne
          (K := K) (W := HyperbolicExtension K (Fin 0 → K) n)
        dsimp only [z] at himage
        rw [LinearEquiv.apply_symm_apply, map_zero] at himage
        exact himage
      have hzIsotropic : q.quadratic z = 0 := by
        have hmap := f.symm.map_quadratic
          (hyperbolicFirstInSum (K := K)
            (W := HyperbolicExtension K (Fin 0 → K) n))
        change q.quadratic z =
          ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
            tailForm).quadratic
              (hyperbolicFirstInSum (K := K)
                (W := HyperbolicExtension K (Fin 0 → K) n)) at hmap
        rw [hyperbolicFirstInSum_isotropic tailForm] at hmap
        exact hmap
      obtain ⟨t, hx, hprimitive⟩ :=
        exists_unit_smul_mem_not_mem_uniformizer_rescale L hzNe
      let x : V := (t : K) • z
      have hxIsotropic : q.quadratic x = 0 := by
        dsimp only [x]
        rw [q.quadratic_smul, hzIsotropic, mul_zero]
      let P := omeara933PlaneData hscale hclosed
        (x := x) hx hprimitive hxIsotropic
      let S := P.splitting hscale hxIsotropic hx
      have htailScale :
          scaleIdeal (S.component 1).space (S.component 1).lattice ≤
            unitIdeal (K := K) := by
        exact ((S.component 1).scaleIdeal_le_of_ambientSubmodule_le
          (S.component_ambientSubmodule_le 1)).trans hscale
      have htailClosed :
          ∀ {w : (S.component 1).carrier},
            w ∈ dualLattice (S.component 1).space
                (S.component 1).lattice →
            (S.component 1).space.quadratic w = 0 →
            w ∈ (S.component 1).lattice :=
        S.right_isotropicDual_closed hclosed
      letI : Module.Finite K (S.component 0).carrier :=
        (S.component 0).lattice.moduleFinite
      letI : Module.Finite K (S.component 1).carrier :=
        (S.component 1).lattice.moduleFinite
      letI : Module.Finite K
          (HyperbolicExtension K (Fin 0 → K) n) :=
        QuadraticSpace.hyperbolicExtensionZeroModuleFinite n
      have htotal : QuadraticSpace.Isometry
          ((S.component 0).space.orthogonalSum (S.component 1).space)
          ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
            tailForm) :=
        S.pairProductLatticeIsometry.toQuadraticSpaceIsometry.trans f
      have hhead : QuadraticSpace.Isometry (S.component 0).space
          (QuadraticSpace.hyperbolicPlane (1 : Kˣ)) := by
        exact P.componentSpaceIsometry hxIsotropic
      let tailIsometry : QuadraticSpace.Isometry (S.component 1).space
          tailForm :=
        QuadraticSpace.orthogonalSumCancel
          (S.component 0).space
          (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
          (S.component 1).space tailForm hhead htotal
      have htailUnimodular : IsUnimodular
          (S.component 1).space (S.component 1).lattice :=
        ih ⟨tailIsometry⟩ htailScale htailClosed
      have hheadUnimodular : IsUnimodular
          (S.component 0).space (S.component 0).lattice := by
        exact P.component_unimodular hxIsotropic
      have hproduct : IsUnimodular
          ((S.component 0).space.orthogonalSum (S.component 1).space)
          (product (S.component 0).lattice (S.component 1).lattice) :=
        hheadUnimodular.orthogonalProduct htailUnimodular
      exact hproduct.mapLatticeIsometry S.pairProductLatticeIsometry

/-- The exact output of O'Meara 93:3 at unit scale. -/
structure Omeara933Data (q : QuadraticSpace K V) (L : Lattice K V) where
  lattice : Lattice K V
  contains : L ≤ lattice
  unimodular : IsUnimodular q lattice
  normGroup_eq : normGroupSet q lattice = normGroupSet q L

/-- O'Meara 93:3 on a displayed finite hyperbolic tower: an integral
lattice at unit scale has a unimodular superlattice with the same norm
group. -/
noncomputable def omeara933
    (n : Nat)
    (htower : q.IsIsometric
      (hyperbolicExtensionForm
        (zeroCoordinateQuadraticSpace (K := K)) n))
    (hscale : scaleIdeal q L = unitIdeal (K := K)) :
    Omeara933Data q L := by
  let D := omeara933MinimalData (q := q) (L := L) hscale
  have hclosed : ∀ {z : V},
      z ∈ dualLattice q D.candidate.lattice →
      q.quadratic z = 0 → z ∈ D.candidate.lattice := by
    intro z hz hqz
    exact D.isotropic_mem_of_mem_dual hz hqz
  have hunimodular : IsUnimodular q D.candidate.lattice :=
    isUnimodular_of_isotropicDual_closed_of_hyperbolicTower
      n htower D.candidate.scale_eq.le hclosed
  exact
    { lattice := D.candidate.lattice
      contains := D.candidate.contains
      unimodular := hunimodular
      normGroup_eq := D.candidate.normGroup_eq }

end Lattice

end Bong
