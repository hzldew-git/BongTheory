/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma64
import Bong.Bong.BeliCorollary44Proof
import Bong.Bong.BeliCorollary44ScaleProof
import Bong.Bong.BeliCorollary44ThreeBlockProof
import Bong.Bong.BeliLemma63Proof
import Bong.Bong.BinaryStrictModular
import Bong.Dyadic.QuadraticDefectHensel
import Bong.Lattice.AsymmetricBinaryModular
import Bong.Lattice.ModularVolume
import Bong.Lattice.ModularParameter
import Bong.Lattice.OrthogonalDecompositionProduct
import Bong.Lattice.OrthogonalDecompositionScale
import Bong.Lattice.VolumeRigidity

/-!
# Beli (2003), Lemma 6.4: unconditional proof

This file proves the three splitting assertions of Lemma 6.4.  The common
input is an intrinsic extraction lemma: a contained scaled hyperbolic plane
supplies two integral isotropic vectors whose mixed product is the prescribed
uniformizer power.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- A doubled scale-order computation gives the corresponding containment
in a prescribed power ideal.  This is the ideal-theoretic conversion used
for the complementary blocks in Lemma 6.4(iii). -/
theorem scaleIdeal_le_powerIdeal_of_hasDoubledScaleOrder
    {W : Type v} [AddCommGroup W] [Module K W]
    {p : QuadraticSpace K W} {M : Lattice K W}
    {d m : Int} (hscale : Lattice.HasDoubledScaleOrder p M d)
    (hbound : 2 * m ≤ d) :
    Lattice.scaleIdeal p M ≤ Lattice.powerIdeal (K := K) m := by
  rcases hscale with ⟨s, hs, hord⟩
  rw [hs, Lattice.principalIdeal_eq_powerIdeal,
    Lattice.powerIdeal_le_iff]
  omega

/-- Every two-by-two Gram determinant vanishes in a one-dimensional
quadratic space. -/
theorem quadratic_mul_quadratic_eq_bilin_sq_of_finrank_eq_one
    {W : Type v} [AddCommGroup W] [Module K W]
    (p : QuadraticSpace K W) (hfin : finrank K W = 1) (x y : W) :
    p.quadratic x * p.quadratic y = p.bilin x y ^ 2 := by
  by_cases hx : x = 0
  · subst x
    simp
  · obtain ⟨c, rfl⟩ :=
      (finrank_eq_one_iff_of_nonzero' x hx).mp hfin y
    rw [p.quadratic_smul, LinearMap.BilinForm.smul_right]
    change p.quadratic x * (c ^ 2 * p.quadratic x) =
      (c * p.quadratic x) ^ 2
    ring

/-- In a unary space, if the two diagonal values have depth at least `m`,
then their mixed value has depth at least `m` as well. -/
theorem bilin_mem_powerIdeal_of_finrank_eq_one
    {W : Type v} [AddCommGroup W] [Module K W]
    (p : QuadraticSpace K W) (hfin : finrank K W = 1)
    (m : Int) (x y : W)
    (hqx : p.quadratic x ∈ Lattice.powerIdeal (K := K) m)
    (hqy : p.quadratic y ∈ Lattice.powerIdeal (K := K) m) :
    p.bilin x y ∈ Lattice.powerIdeal (K := K) m := by
  by_cases hxy : p.bilin x y = 0
  · rw [hxy]
    exact (Lattice.powerIdeal (K := K) m).zero_mem
  · have hdet :=
      quadratic_mul_quadratic_eq_bilin_sq_of_finrank_eq_one p hfin x y
    have hqxne : p.quadratic x ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hdet
      exact hxy (sq_eq_zero_iff.mp hdet.symm)
    have hqyne : p.quadratic y ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hdet
      exact hxy (sq_eq_zero_iff.mp hdet.symm)
    let xu : Kˣ := Units.mk0 (p.quadratic x) hqxne
    let yu : Kˣ := Units.mk0 (p.quadratic y) hqyne
    let bu : Kˣ := Units.mk0 (p.bilin x y) hxy
    have hxOrder : m ≤ ordUnit K xu := by
      have h := (Lattice.mem_powerIdeal_iff (K := K) m _).1 hqx
      have h' : (m : WithTop Int) ≤
          (ordUnit K xu : WithTop Int) := by
        simpa [xu, coe_ordUnit] using h
      exact WithTop.coe_le_coe.mp h'
    have hyOrder : m ≤ ordUnit K yu := by
      have h := (Lattice.mem_powerIdeal_iff (K := K) m _).1 hqy
      have h' : (m : WithTop Int) ≤
          (ordUnit K yu : WithTop Int) := by
        simpa [yu, coe_ordUnit] using h
      exact WithTop.coe_le_coe.mp h'
    have horder : ordUnit K xu + ordUnit K yu = 2 * ordUnit K bu := by
      have hunit : xu * yu = bu ^ 2 := Units.ext hdet
      rw [← ordUnit_mul, hunit, ordUnit_pow]
      norm_num
    apply (Lattice.mem_powerIdeal_iff (K := K) m _).2
    have hbound : m ≤ ordUnit K bu := by omega
    have hbound' : (m : WithTop Int) ≤
        (ordUnit K bu : WithTop Int) := WithTop.coe_le_coe.mpr hbound
    simpa [bu, coe_ordUnit] using hbound'

/-- In a unary space, complementary lower bounds for the two diagonal
values give the corresponding half-sum bound for their mixed value.  This
asymmetric form is the one needed for the unary-head branch of Beli's
Lemma 6.5(ii). -/
theorem bilin_mem_powerIdeal_of_finrank_eq_one_of_sum
    {W : Type v} [AddCommGroup W] [Module K W]
    (p : QuadraticSpace K W) (hfin : finrank K W = 1)
    (r sx sy : Int) (x y : W)
    (hqx : p.quadratic x ∈ Lattice.powerIdeal (K := K) sx)
    (hqy : p.quadratic y ∈ Lattice.powerIdeal (K := K) sy)
    (hsum : 2 * r ≤ sx + sy) :
    p.bilin x y ∈ Lattice.powerIdeal (K := K) r := by
  by_cases hxy : p.bilin x y = 0
  · rw [hxy]
    exact (Lattice.powerIdeal (K := K) r).zero_mem
  · have hdet :=
      quadratic_mul_quadratic_eq_bilin_sq_of_finrank_eq_one p hfin x y
    have hqxne : p.quadratic x ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hdet
      exact hxy (sq_eq_zero_iff.mp hdet.symm)
    have hqyne : p.quadratic y ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hdet
      exact hxy (sq_eq_zero_iff.mp hdet.symm)
    let xu : Kˣ := Units.mk0 (p.quadratic x) hqxne
    let yu : Kˣ := Units.mk0 (p.quadratic y) hqyne
    let bu : Kˣ := Units.mk0 (p.bilin x y) hxy
    have hxOrder : sx ≤ ordUnit K xu := by
      have h := (Lattice.mem_powerIdeal_iff (K := K) sx _).1 hqx
      have h' : (sx : WithTop Int) ≤
          (ordUnit K xu : WithTop Int) := by
        simpa [xu, coe_ordUnit] using h
      exact WithTop.coe_le_coe.mp h'
    have hyOrder : sy ≤ ordUnit K yu := by
      have h := (Lattice.mem_powerIdeal_iff (K := K) sy _).1 hqy
      have h' : (sy : WithTop Int) ≤
          (ordUnit K yu : WithTop Int) := by
        simpa [yu, coe_ordUnit] using h
      exact WithTop.coe_le_coe.mp h'
    have horder : ordUnit K xu + ordUnit K yu = 2 * ordUnit K bu := by
      have hunit : xu * yu = bu ^ 2 := Units.ext hdet
      rw [← ordUnit_mul, hunit, ordUnit_pow]
      norm_num
    apply (Lattice.mem_powerIdeal_iff (K := K) r _).2
    have hbound : r ≤ ordUnit K bu := by omega
    have hbound' : (r : WithTop Int) ≤
        (ordUnit K bu : WithTop Int) := WithTop.coe_le_coe.mpr hbound
    simpa [bu, coe_ordUnit] using hbound'

/-- In an ambient binary space, an asymmetric pair is an ambient basis and
its basis lattice has volume order twice the mixed-pairing order. -/
theorem volumeOrder_basisLattice_binaryPair_of_finrank_eq_two
    {W : Type v} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (p : QuadraticSpace K W) (hfin : finrank K W = 2) (x y : W)
    (hxy : p.bilin x y ≠ 0)
    (hx : ord K (p.bilin x y) < ord K (p.quadratic x))
    (hy : ord K (p.bilin x y) ≤ ord K (p.quadratic y)) :
    let hli := Lattice.binaryPair_linearIndependent_of_left_strict
      (q := p) hxy hx hy
    let b : Basis (Fin 2) K W :=
      basisOfLinearIndependentOfCardEqFinrank'
        (binaryPairFamily x y) hli (by simpa [hfin])
    Lattice.volumeOrder p (Lattice.basisLattice b) =
      2 * ordUnit K (Units.mk0 (p.bilin x y) hxy) := by
  let hli := Lattice.binaryPair_linearIndependent_of_left_strict
    (q := p) hxy hx hy
  let b : Basis (Fin 2) K W :=
    basisOfLinearIndependentOfCardEqFinrank'
      (binaryPairFamily x y) hli (by simpa [hfin])
  let e : Fin 2 ≃ Fin (finrank K W) := finCongr hfin.symm
  let bfin : Basis (Fin (finrank K W)) K W := b.reindex e
  have hb (i : Fin 2) : b i = binaryPairFamily x y i := by
    simp [b]
  have hbfin : Lattice.basisLattice bfin = Lattice.basisLattice b :=
    Lattice.basisLattice_reindex b e
  have hmatrix :
      LinearMap.BilinForm.toMatrix bfin p.bilin =
        Matrix.reindex e e (LinearMap.BilinForm.toMatrix b p.bilin) := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, bfin, Basis.coe_reindex, Function.comp_apply]
  have hdet : Lattice.basisGramDeterminant p bfin =
      p.quadratic x * p.quadratic y - p.bilin x y ^ 2 := by
    change (LinearMap.BilinForm.toMatrix bfin p.bilin).det = _
    rw [hmatrix, Matrix.det_reindex_self, Matrix.det_fin_two]
    simp only [LinearMap.BilinForm.toMatrix_apply]
    rw [hb, hb]
    simp only [binaryPairFamily_zero, binaryPairFamily_one]
    change p.quadratic x * p.quadratic y -
      p.bilin x y * p.bilin y x = _
    rw [p.isSymm.eq y x, pow_two]
  apply WithTop.coe_injective
  rw [show Lattice.basisLattice b = Lattice.basisLattice bfin by
      exact hbfin.symm,
    Lattice.coe_volumeOrder_basisLattice_eq_ord_basisGramDeterminant,
    hdet,
    Lattice.ord_binaryGramDeterminant_eq_of_left_strict hxy hx hy,
    ord_pow]
  have hcoe := coe_ordUnit K (Units.mk0 (p.bilin x y) hxy)
  change (((ordUnit K (Units.mk0 (p.bilin x y) hxy) : Int) :
      WithTop Int)) = ord K (p.bilin x y) at hcoe
  rw [← hcoe, two_nsmul]
  rw [show (2 * ordUnit K (Units.mk0 (p.bilin x y) hxy) : Int) =
      ordUnit K (Units.mk0 (p.bilin x y) hxy) +
        ordUnit K (Units.mk0 (p.bilin x y) hxy) by omega,
    WithTop.coe_add]

/-- An integral realization of the two standard isotropic generators can be
extracted from the intrinsic scaled-hyperbolic-pair predicate. -/
theorem exists_integral_isotropic_pair_of_isScaledHyperbolicPair
    {x y : V} {r : Int} (hx : x ∈ L) (hy : y ∈ L)
    (hH : IsScaledHyperbolicPair q x y r) :
    ∃ u w : V, u ∈ L ∧ w ∈ L ∧
      q.quadratic u = 0 ∧ q.quadratic w = 0 ∧
      q.bilin u w = (uniformizerPowerUnit K r : K) := by
  rcases hH with ⟨hli, hnondeg, hisometric⟩
  rcases hisometric with ⟨f⟩
  let e₀ : Fin 2 → K := Pi.single 0 1
  let e₁ : Fin 2 → K := Pi.single 1 1
  let u' : binaryPairSpan (K := K) x y := f.toLinearEquiv.symm e₀
  let w' : binaryPairSpan (K := K) x y := f.toLinearEquiv.symm e₁
  have he₀ : e₀ ∈ Lattice.hyperbolicPlaneLattice (K := K) := by
    rw [Lattice.hyperbolicPlaneLattice,
      Lattice.mem_basisLattice_iff_repr_mem_integerRing]
    simp [e₀]
  have he₁ : e₁ ∈ Lattice.hyperbolicPlaneLattice (K := K) := by
    rw [Lattice.hyperbolicPlaneLattice,
      Lattice.mem_basisLattice_iff_repr_mem_integerRing]
    simp [e₁]
  have hu' : u' ∈ Lattice.basisLattice
      (binaryPairBasis (K := K) x y hli) := by
    apply (f.map_mem u').2
    simpa [u'] using he₀
  have hw' : w' ∈ Lattice.basisLattice
      (binaryPairBasis (K := K) x y hli) := by
    apply (f.map_mem w').2
    simpa [w'] using he₁
  have basis_mem_parent : ∀ z : binaryPairSpan (K := K) x y,
      z ∈ Lattice.basisLattice (binaryPairBasis (K := K) x y hli) →
        (z : V) ∈ L := by
    intro z hz
    let b := binaryPairBasis (K := K) x y hli
    have hzcoord :=
      (Lattice.mem_basisLattice_iff_repr_mem_integerRing b z).1 hz
    have hsum := b.sum_repr z
    rw [Fin.sum_univ_two] at hsum
    have hzero : (b.repr z 0 : K) • (b 0 : V) ∈ L := by
      have hmem := L.smul_mem ⟨b.repr z 0, hzcoord 0⟩ hx
      change (b.repr z 0 : K) • x ∈ L at hmem
      simpa [b, coe_binaryPairBasis] using hmem
    have hone : (b.repr z 1 : K) • (b 1 : V) ∈ L := by
      have hmem := L.smul_mem ⟨b.repr z 1, hzcoord 1⟩ hy
      change (b.repr z 1 : K) • y ∈ L at hmem
      simpa [b, coe_binaryPairBasis] using hmem
    have hadd := L.add_mem hzero hone
    change ((b.repr z 0 : K) • (b 0 :
      binaryPairSpan (K := K) x y) +
      (b.repr z 1 : K) • (b 1 :
        binaryPairSpan (K := K) x y) :
          binaryPairSpan (K := K) x y) = z at hsum
    have hsumCoe := congrArg Subtype.val hsum
    simpa only [map_add, SetLike.val_smul] using hsumCoe ▸ hadd
  refine ⟨(u' : V), (w' : V), basis_mem_parent u' hu',
    basis_mem_parent w' hw', ?_, ?_, ?_⟩
  · have h := f.map_quadratic u'
    rw [show f.toLinearEquiv u' = e₀ by simp [u']] at h
    change (q.restrict (binaryPairSpan (K := K) x y)
      hnondeg).quadratic u' = 0
    simpa [e₀, QuadraticSpace.hyperbolicPlane_quadratic_apply] using h.symm
  · have h := f.map_quadratic w'
    rw [show f.toLinearEquiv w' = e₁ by simp [w']] at h
    change (q.restrict (binaryPairSpan (K := K) x y)
      hnondeg).quadratic w' = 0
    simpa [e₁, QuadraticSpace.hyperbolicPlane_quadratic_apply] using h.symm
  · have h := f.map_bilin u' w'
    rw [show f.toLinearEquiv u' = e₀ by simp [u'],
      show f.toLinearEquiv w' = e₁ by simp [w']] at h
    change (q.restrict (binaryPairSpan (K := K) x y)
      hnondeg).bilin u' w' = (uniformizerPowerUnit K r : K)
    simpa [e₀, e₁,
      QuadraticSpace.hyperbolicPlane_bilin_apply] using h.symm

/-- A contained scaled hyperbolic plane has integral standard isotropic
generators in the ambient lattice. -/
theorem exists_integral_isotropic_pair_of_containsScaledHyperbolicPlane
    {r : Int} (hH : Lattice.ContainsScaledHyperbolicPlane q L r) :
    ∃ u w : V, u ∈ L ∧ w ∈ L ∧
      q.quadratic u = 0 ∧ q.quadratic w = 0 ∧
      q.bilin u w = (uniformizerPowerUnit K r : K) := by
  rcases hH with ⟨x, y, hx, hy, hxy⟩
  exact exists_integral_isotropic_pair_of_isScaledHyperbolicPair hx hy hxy

/-- Beli 6.4(i), proved directly from the one-dimensional Gram identity and
the strict scale jump on the complementary component. -/
theorem beliLemma64_unaryFirst_excludes_hyperbolic_proved
    {r : Int} (S : Lattice.UnaryFirstSplitting q L r) :
    ¬Lattice.ContainsScaledHyperbolicPlane q L r := by
  intro hH
  rcases exists_integral_isotropic_pair_of_containsScaledHyperbolicPlane hH
    with ⟨u, w, hu, hw, huq, hwq, huw⟩
  let D := S.toOrthogonalDecomposition
  let f := D.pairProductLatticeIsometry
  let U := f.toLinearEquiv.symm u
  let W := f.toLinearEquiv.symm w
  have hUmem : U ∈ Lattice.product
      (D.component 0).lattice (D.component 1).lattice := by
    apply (f.map_mem U).2
    simpa [U] using hu
  have hWmem : W ∈ Lattice.product
      (D.component 0).lattice (D.component 1).lattice := by
    apply (f.map_mem W).2
    simpa [W] using hw
  have hUcomponents : U.1 ∈ (D.component 0).lattice ∧
      U.2 ∈ (D.component 1).lattice :=
    Lattice.mem_product_iff.mp hUmem
  have hWcomponents : W.1 ∈ (D.component 0).lattice ∧
      W.2 ∈ (D.component 1).lattice :=
    Lattice.mem_product_iff.mp hWmem
  have hUtailQ : (D.component 1).space.quadratic U.2 ∈
      Lattice.powerIdeal (K := K) (r + 1) :=
    S.tail_scale_le
      (Lattice.bilin_mem_scaleIdeal_of_mem
        (D.component 1).space (D.component 1).lattice
        hUcomponents.2 hUcomponents.2)
  have hWtailQ : (D.component 1).space.quadratic W.2 ∈
      Lattice.powerIdeal (K := K) (r + 1) :=
    S.tail_scale_le
      (Lattice.bilin_mem_scaleIdeal_of_mem
        (D.component 1).space (D.component 1).lattice
        hWcomponents.2 hWcomponents.2)
  have hUdecomp : q.quadratic u =
      (D.component 0).space.quadratic U.1 +
        (D.component 1).space.quadratic U.2 := by
    simpa [U, f, QuadraticSpace.orthogonalSum_quadratic_apply] using
      f.map_quadratic U
  have hWdecomp : q.quadratic w =
      (D.component 0).space.quadratic W.1 +
        (D.component 1).space.quadratic W.2 := by
    simpa [W, f, QuadraticSpace.orthogonalSum_quadratic_apply] using
      f.map_quadratic W
  have hUfirstQ : (D.component 0).space.quadratic U.1 ∈
      Lattice.powerIdeal (K := K) (r + 1) := by
    have heq : (D.component 0).space.quadratic U.1 =
        -(D.component 1).space.quadratic U.2 := by
      linear_combination hUdecomp.symm.trans huq
    rw [heq]
    exact (Lattice.powerIdeal (K := K) (r + 1)).neg_mem hUtailQ
  have hWfirstQ : (D.component 0).space.quadratic W.1 ∈
      Lattice.powerIdeal (K := K) (r + 1) := by
    have heq : (D.component 0).space.quadratic W.1 =
        -(D.component 1).space.quadratic W.2 := by
      linear_combination hWdecomp.symm.trans hwq
    rw [heq]
    exact (Lattice.powerIdeal (K := K) (r + 1)).neg_mem hWtailQ
  have hfirstB : (D.component 0).space.bilin U.1 W.1 ∈
      Lattice.powerIdeal (K := K) (r + 1) :=
    bilin_mem_powerIdeal_of_finrank_eq_one
      (D.component 0).space S.first_rank (r + 1) U.1 W.1
      hUfirstQ hWfirstQ
  have htailB : (D.component 1).space.bilin U.2 W.2 ∈
      Lattice.powerIdeal (K := K) (r + 1) :=
    S.tail_scale_le
      (Lattice.bilin_mem_scaleIdeal_of_mem
        (D.component 1).space (D.component 1).lattice
        hUcomponents.2 hWcomponents.2)
  have hbilinDecomp : q.bilin u w =
      (D.component 0).space.bilin U.1 W.1 +
        (D.component 1).space.bilin U.2 W.2 := by
    simpa [U, W, f, QuadraticSpace.orthogonalSum_bilin_apply] using
      f.map_bilin U W
  have hpower : (uniformizerPowerUnit K r : K) ∈
      Lattice.powerIdeal (K := K) (r + 1) := by
    rw [← huw, hbilinDecomp]
    exact (Lattice.powerIdeal (K := K) (r + 1)).add_mem hfirstB htailB
  have horder :=
    (Lattice.mem_powerIdeal_iff (K := K) (r + 1)
      (uniformizerPowerUnit K r : K)).1 hpower
  have hpiOrder : ord K (uniformizerPowerUnit K r : K) =
      (r : WithTop Int) := by
    rw [← coe_ordUnit, ordUnit_uniformizerPowerUnit]
  rw [hpiOrder] at horder
  have hbad : r + 1 ≤ r := WithTop.coe_le_coe.mp horder
  omega

/-- Beli 6.4(ii), forward direction.  A contained hyperbolic pair is
projected to the binary modular component.  Proper norm containment makes
both projected diagonal values deeper than the first norm, while volume
rigidity shows that the projected pair is an integral basis.  Its norm order
is then forced to be `r + e`, so Lemma 3.19 produces the required scaled
hyperbolic plane inside the first component. -/
theorem beliLemma64_binaryFirst_full_implies_first_proved
    {r : Int} (S : Lattice.BinaryFirstModularSplitting q L r) :
    Lattice.ContainsScaledHyperbolicPlane q L r →
      (S.component 0).ContainsScaledHyperbolicPlane r := by
  classical
  intro hH
  rcases exists_integral_isotropic_pair_of_containsScaledHyperbolicPlane hH
    with ⟨u, w, hu, hw, huq, hwq, huw⟩
  let D := S.toOrthogonalDecomposition
  let f := D.pairProductLatticeIsometry
  let U := f.toLinearEquiv.symm u
  let W := f.toLinearEquiv.symm w
  have hUmem : U ∈ Lattice.product
      (D.component 0).lattice (D.component 1).lattice := by
    apply (f.map_mem U).2
    simpa [U] using hu
  have hWmem : W ∈ Lattice.product
      (D.component 0).lattice (D.component 1).lattice := by
    apply (f.map_mem W).2
    simpa [W] using hw
  have hUcomponents : U.1 ∈ (D.component 0).lattice ∧
      U.2 ∈ (D.component 1).lattice :=
    Lattice.mem_product_iff.mp hUmem
  have hWcomponents : W.1 ∈ (D.component 0).lattice ∧
      W.2 ∈ (D.component 1).lattice :=
    Lattice.mem_product_iff.mp hWmem
  have hUdecomp : q.quadratic u =
      (D.component 0).space.quadratic U.1 +
        (D.component 1).space.quadratic U.2 := by
    simpa [U, f, QuadraticSpace.orthogonalSum_quadratic_apply] using
      f.map_quadratic U
  have hWdecomp : q.quadratic w =
      (D.component 0).space.quadratic W.1 +
        (D.component 1).space.quadratic W.2 := by
    simpa [W, f, QuadraticSpace.orthogonalSum_quadratic_apply] using
      f.map_quadratic W
  have hUfirstEq : (D.component 0).space.quadratic U.1 =
      -(D.component 1).space.quadratic U.2 := by
    linear_combination hUdecomp.symm.trans huq
  have hWfirstEq : (D.component 0).space.quadratic W.1 =
      -(D.component 1).space.quadratic W.2 := by
    linear_combination hWdecomp.symm.trans hwq
  have hbilinDecomp : q.bilin u w =
      (D.component 0).space.bilin U.1 W.1 +
        (D.component 1).space.bilin U.2 W.2 := by
    simpa [U, W, f, QuadraticSpace.orthogonalSum_bilin_apply] using
      f.map_bilin U W
  have htailB : (D.component 1).space.bilin U.2 W.2 ∈
      Lattice.powerIdeal (K := K) (r + 1) :=
    S.tail_scale_le
      (Lattice.bilin_mem_scaleIdeal_of_mem
        (D.component 1).space (D.component 1).lattice
        hUcomponents.2 hWcomponents.2)
  have htailBOrder : ((r + 1 : Int) : WithTop Int) ≤
      ord K ((D.component 1).space.bilin U.2 W.2) :=
    (Lattice.mem_powerIdeal_iff (K := K) (r + 1) _).1 htailB
  have hpiOrder : ord K (uniformizerPowerUnit K r : K) =
      (r : WithTop Int) := by
    rw [← coe_ordUnit, ordUnit_uniformizerPowerUnit]
  have hpiLtTail : ord K (uniformizerPowerUnit K r : K) <
      ord K ((D.component 1).space.bilin U.2 W.2) := by
    rw [hpiOrder]
    exact (WithTop.coe_lt_coe.mpr (by omega)).trans_le htailBOrder
  have hfirstBEq : (D.component 0).space.bilin U.1 W.1 =
      (uniformizerPowerUnit K r : K) -
        (D.component 1).space.bilin U.2 W.2 := by
    linear_combination hbilinDecomp.symm.trans huw
  have hfirstBOrder :
      ord K ((D.component 0).space.bilin U.1 W.1) =
        (r : WithTop Int) := by
    rw [hfirstBEq, (ord K).map_sub_eq_of_lt_left hpiLtTail, hpiOrder]
  have hfirstBNe : (D.component 0).space.bilin U.1 W.1 ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero] at hfirstBOrder
    exact WithTop.top_ne_coe hfirstBOrder
  let d : Kˣ := Units.mk0
    ((D.component 0).space.bilin U.1 W.1) hfirstBNe
  have hdOrder : ordUnit K d = r := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    exact hfirstBOrder
  letI : Module.Finite K (D.component 0).carrier :=
    (D.component 0).lattice.moduleFinite
  have hfirstRank : finrank K (D.component 0).carrier = 2 :=
    S.first_rank
  rcases Lattice.exists_isNormGenerator_of_finrank_pos
      (D.component 0).space (D.component 0).lattice
      (by rw [hfirstRank]; norm_num :
        0 < finrank K (D.component 0).carrier) with
    ⟨z, hzGenerator, hzAnisotropic⟩
  let a : Kˣ := Units.mk0 ((D.component 0).space.quadratic z)
    hzAnisotropic
  have hfirstNorm :
      Lattice.normIdeal (D.component 0).space (D.component 0).lattice =
        Lattice.principalIdeal (K := K) (a : K) := by
    simpa [a] using hzGenerator.normIdeal_eq
  have htailNormLt :
      Lattice.normIdeal (D.component 1).space (D.component 1).lattice <
        Lattice.principalIdeal (K := K) (a : K) := by
    rw [← hfirstNorm]
    exact S.tail_norm_lt
  have hUtailNorm : (D.component 1).space.quadratic U.2 ∈
      Lattice.normIdeal (D.component 1).space (D.component 1).lattice :=
    Lattice.quadratic_mem_normIdeal_of_mem
      (D.component 1).space (D.component 1).lattice hUcomponents.2
  have hWtailNorm : (D.component 1).space.quadratic W.2 ∈
      Lattice.normIdeal (D.component 1).space (D.component 1).lattice :=
    Lattice.quadratic_mem_normIdeal_of_mem
      (D.component 1).space (D.component 1).lattice hWcomponents.2
  have hUfirstHigh : (ordUnit K a : WithTop Int) <
      ord K ((D.component 0).space.quadratic U.1) := by
    rw [hUfirstEq, ord_neg]
    exact Lattice.ordUnit_lt_ord_of_mem_of_lt_principalIdeal
      a _ hUtailNorm htailNormLt
  have hWfirstHigh : (ordUnit K a : WithTop Int) <
      ord K ((D.component 0).space.quadratic W.1) := by
    rw [hWfirstEq, ord_neg]
    exact Lattice.ordUnit_lt_ord_of_mem_of_lt_principalIdeal
      a _ hWtailNorm htailNormLt
  have hrLeNorm : r ≤ ordUnit K a := by
    have hle := Lattice.normIdeal_le_scaleIdeal
      (D.component 0).space (D.component 0).lattice
    rw [hfirstNorm, Lattice.principalIdeal_eq_powerIdeal,
      S.first_scale_eq, Lattice.powerIdeal_le_iff] at hle
    exact hle
  have hleftStrict :
      ord K ((D.component 0).space.bilin U.1 W.1) <
        ord K ((D.component 0).space.quadratic U.1) := by
    rw [hfirstBOrder]
    exact (WithTop.coe_le_coe.mpr hrLeNorm).trans_lt hUfirstHigh
  have hrightWeak :
      ord K ((D.component 0).space.bilin U.1 W.1) ≤
        ord K ((D.component 0).space.quadratic W.1) := by
    rw [hfirstBOrder]
    exact ((WithTop.coe_le_coe.mpr hrLeNorm).trans_lt hWfirstHigh).le
  let hli := Lattice.binaryPair_linearIndependent_of_left_strict
    (q := (D.component 0).space) hfirstBNe hleftStrict hrightWeak
  let b : Basis (Fin 2) K (D.component 0).carrier :=
    basisOfLinearIndependentOfCardEqFinrank'
      (binaryPairFamily U.1 W.1) hli (by simpa using hfirstRank.symm)
  have hb (i : Fin 2) : b i = binaryPairFamily U.1 W.1 i := by
    simp [b]
  have hbMem : ∀ i, b i ∈ (D.component 0).lattice := by
    intro i
    rw [hb]
    fin_cases i
    · exact hUcomponents.1
    · exact hWcomponents.1
  have hbLe : Lattice.basisLattice b ≤ (D.component 0).lattice := by
    change Submodule.span (IntegerRing K) (Set.range b) ≤
      (D.component 0).lattice.toSubmodule
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hbMem i
  have hbVolume : Lattice.volumeOrder (D.component 0).space
      (Lattice.basisLattice b) = 2 * r := by
    simpa [b, hli, hdOrder, d] using
      (volumeOrder_basisLattice_binaryPair_of_finrank_eq_two
        (D.component 0).space S.first_rank U.1 W.1 hfirstBNe
        hleftStrict hrightWeak)
  have hfirstVolume : Lattice.volumeOrder (D.component 0).space
      (D.component 0).lattice = 2 * r := by
    calc
      Lattice.volumeOrder (D.component 0).space (D.component 0).lattice =
          (finrank K (D.component 0).carrier : Int) *
            ordUnit K (uniformizerPowerUnit K r) :=
        S.first_modular.volumeOrder_eq
      _ = 2 * r := by
        rw [hfirstRank, ordUnit_uniformizerPowerUnit]
        norm_num
  have hbEq : Lattice.basisLattice b = (D.component 0).lattice :=
    Lattice.eq_of_le_of_volumeOrder_eq (D.component 0).space
      (Lattice.basisLattice b) (D.component 0).lattice hbLe
      (hbVolume.trans hfirstVolume.symm)
  have htwoDNorm : (2 : IntegerRing K) •
      (D.component 0).space.bilin U.1 W.1 ∈
        Lattice.normIdeal (D.component 0).space
          (D.component 0).lattice :=
    Lattice.two_smul_mem_normIdeal
      (D.component 0).space (D.component 0).lattice
      (Lattice.bilin_mem_scaleIdeal_of_mem
        (D.component 0).space (D.component 0).lattice
        hUcomponents.1 hWcomponents.1)
  have htwoDOrder : ord K ((2 : IntegerRing K) •
      (D.component 0).space.bilin U.1 W.1) =
        ((r + ramificationIndex K : Int) : WithTop Int) := by
    change ord K ((2 : K) *
      (D.component 0).space.bilin U.1 W.1) = _
    rw [ord_mul, ← ramificationIndex_spec, hfirstBOrder]
    norm_cast
    ring
  have hnormLe : ordUnit K a ≤ r + ramificationIndex K := by
    have hmem := htwoDNorm
    rw [hfirstNorm, Lattice.principalIdeal_eq_powerIdeal] at hmem
    have horder := (Lattice.mem_powerIdeal_iff
      (K := K) (ordUnit K a) _).1 hmem
    rw [htwoDOrder] at horder
    exact WithTop.coe_le_coe.mp horder
  have hnormGe : r + ramificationIndex K ≤ ordUnit K a := by
    by_contra hnot
    have hnormLt : ordUnit K a < r + ramificationIndex K :=
      lt_of_not_ge hnot
    have hzBasis : z ∈ Lattice.basisLattice b := by
      rw [hbEq]
      exact hzGenerator.mem
    have hzCoord :=
      (Lattice.mem_basisLattice_iff_repr_mem_integerRing b z).1 hzBasis
    let c₀O : IntegerRing K := ⟨b.repr z 0, hzCoord 0⟩
    let c₁O : IntegerRing K := ⟨b.repr z 1, hzCoord 1⟩
    have hsum := b.sum_repr z
    rw [Fin.sum_univ_two, hb, hb,
      binaryPairFamily_zero, binaryPairFamily_one] at hsum
    let I := Lattice.powerIdeal (K := K) (ordUnit K a + 1)
    have hUinI : (D.component 0).space.quadratic U.1 ∈ I := by
      apply (Lattice.mem_powerIdeal_iff (K := K) (ordUnit K a + 1) _).2
      exact Lattice.coe_int_add_one_le_of_lt hUfirstHigh
    have hWinI : (D.component 0).space.quadratic W.1 ∈ I := by
      apply (Lattice.mem_powerIdeal_iff (K := K) (ordUnit K a + 1) _).2
      exact Lattice.coe_int_add_one_le_of_lt hWfirstHigh
    have htwoDinI : (2 : IntegerRing K) •
        (D.component 0).space.bilin U.1 W.1 ∈ I := by
      apply (Lattice.mem_powerIdeal_iff (K := K) (ordUnit K a + 1) _).2
      rw [htwoDOrder]
      exact WithTop.coe_le_coe.mpr (by omega)
    have hleftTerm : (b.repr z 0) ^ 2 *
        (D.component 0).space.quadratic U.1 ∈ I := by
      have h := I.smul_mem (c₀O ^ 2) hUinI
      change ((c₀O : K) ^ 2 *
        (D.component 0).space.quadratic U.1) ∈ I at h
      simpa [c₀O] using h
    have hrightTerm : (b.repr z 1) ^ 2 *
        (D.component 0).space.quadratic W.1 ∈ I := by
      have h := I.smul_mem (c₁O ^ 2) hWinI
      change ((c₁O : K) ^ 2 *
        (D.component 0).space.quadratic W.1) ∈ I at h
      simpa [c₁O] using h
    have hcrossTerm : 2 * (b.repr z 0 * b.repr z 1 *
        (D.component 0).space.bilin U.1 W.1) ∈ I := by
      have h := I.smul_mem (c₀O * c₁O) htwoDinI
      change ((c₀O : K) * (c₁O : K)) *
        ((2 : K) * (D.component 0).space.bilin U.1 W.1) ∈ I at h
      convert h using 1 <;> simp [c₀O, c₁O]
      ring
    have hzFormula : (D.component 0).space.quadratic z =
        (b.repr z 0) ^ 2 * (D.component 0).space.quadratic U.1 +
        (b.repr z 1) ^ 2 * (D.component 0).space.quadratic W.1 +
        2 * (b.repr z 0 * b.repr z 1 *
          (D.component 0).space.bilin U.1 W.1) := by
      calc
        (D.component 0).space.quadratic z =
            (D.component 0).space.quadratic
              ((b.repr z 0) • U.1 + (b.repr z 1) • W.1) :=
          congrArg (D.component 0).space.quadratic hsum.symm
        _ = _ := by
          rw [(D.component 0).space.quadratic_add,
            (D.component 0).space.quadratic_smul,
            (D.component 0).space.quadratic_smul,
            LinearMap.BilinForm.smul_left,
            LinearMap.BilinForm.smul_right]
          ring
    have hzInI : (D.component 0).space.quadratic z ∈ I := by
      rw [hzFormula]
      exact I.add_mem (I.add_mem hleftTerm hrightTerm) hcrossTerm
    have hzOrder :=
      (Lattice.mem_powerIdeal_iff (K := K) (ordUnit K a + 1) _).1 hzInI
    have hzaOrder : ord K ((D.component 0).space.quadratic z) =
        (ordUnit K a : WithTop Int) := by
      rw [coe_ordUnit]
      rfl
    rw [hzaOrder] at hzOrder
    have hbad : ordUnit K a + 1 ≤ ordUnit K a :=
      WithTop.coe_le_coe.mp hzOrder
    omega
  have hnormEq : ordUnit K a = r + ramificationIndex K := by omega
  have hdiagHigh : (ordUnit K a : WithTop Int) <
      ord K ((D.component 0).space.quadratic U.1 +
        (D.component 0).space.quadratic W.1) :=
    (lt_min hUfirstHigh hWfirstHigh).trans_le
      (min_ord_le_ord_add K
        ((D.component 0).space.quadratic U.1)
        ((D.component 0).space.quadratic W.1))
  have hsumOrder : ord K
      ((D.component 0).space.quadratic (U.1 + W.1)) =
        (ordUnit K a : WithTop Int) := by
    rw [(D.component 0).space.quadratic_add]
    have htwoOrder' : ord K ((2 : K) *
        (D.component 0).space.bilin U.1 W.1) =
          (ordUnit K a : WithTop Int) := by
      simpa only [Algebra.smul_def, map_ofNat, hnormEq] using htwoDOrder
    rw [(ord K).map_add_eq_of_lt_right
      (htwoOrder' ▸ hdiagHigh), htwoOrder']
  have hUambientHigh : (ordUnit K a : WithTop Int) <
      ord K (q.quadratic (U.1 : V)) := hUfirstHigh
  have hWambientHigh : (ordUnit K a : WithTop Int) <
      ord K (q.quadratic (W.1 : V)) := hWfirstHigh
  have hsumAmbient : ord K (q.quadratic ((U.1 : V) + (W.1 : V))) =
      (ordUnit K a : WithTop Int) := by
    have hrestrict : (D.component 0).space.quadratic (U.1 + W.1) =
        q.quadratic ((U.1 + W.1 : (D.component 0).carrier) : V) := rfl
    rw [hrestrict] at hsumOrder
    have hcoe : ((U.1 + W.1 : (D.component 0).carrier) : V) =
        (U.1 : V) + (W.1 : V) := rfl
    rwa [hcoe] at hsumOrder
  have hpair := beliLemma319 (q := q)
    (U.1 : V) (W.1 : V) (ordUnit K a)
    hUambientHigh hWambientHigh hsumAmbient
  have hscale : ordUnit K a - ramificationIndex K = r := by omega
  rw [hscale] at hpair
  exact ⟨U.1, W.1, hUcomponents.1, hWcomponents.1, hpair⟩

/-- Beli 6.4(iii), forward direction.  If the first two orders increase,
Corollary 4.4 splits off a unary block and part (i) rules out the ambient
hyperbolic plane.  Otherwise Corollary 4.4 splits off the initial binary
modular block; its complement has strictly deeper scale and norm, so part
(ii) applies. -/
theorem beliLemma64_full_implies_binaryPrefix_proved
    {n : Nat} (b : BONG V q L (n + 3)) (hgood : b.IsGood)
    (h13 : b.order 0 < b.order 2) :
    Lattice.ContainsScaledHyperbolicPlane q L
        ((b.order 0 + b.order 1) / 2) →
      Lattice.QuadraticSublattice.ContainsScaledHyperbolicPlane
        (b.prefixWitness 2 (by omega)).quadraticSublattice
        ((b.order 0 + b.order 1) / 2) := by
  classical
  let r : Int := (b.order 0 + b.order 1) / 2
  intro hH
  change Lattice.ContainsScaledHyperbolicPlane q L r at hH
  change Lattice.QuadraticSublattice.ContainsScaledHyperbolicPlane
    (b.prefixWitness 2 (by omega)).quadraticSublattice r
  by_cases h01 : b.order 0 < b.order 1
  · rcases b.beliCorollary44_i_unconditional hgood
        (0 : Fin (n + 3)) (by simp) h01.le with ⟨S⟩
    let rightRaw := S.right.toGoodBONG hgood
    let right := rightRaw.castLength
      (by omega : n + 3 - 1 = n + 2)
    have hrightZero : right.order 0 = b.order 1 := by
      change ((S.right.toGoodBONG hgood).castLength _).order 0 = b.order 1
      exact S.right.order_toGoodBONG_castLength hgood
        (by omega : n + 3 - 1 = n + 2) (0 : Fin (n + 2))
    have hrightOne : right.order 1 = b.order 2 := by
      change ((S.right.toGoodBONG hgood).castLength _).order 1 = b.order 2
      exact S.right.order_toGoodBONG_castLength hgood
        (by omega : n + 3 - 1 = n + 2) (1 : Fin (n + 2))
    have hrightScale :=
      right.toBONG.beliCorollary44_iv_unconditional right.good
    have hstrictDoubled : 2 * r <
        min (2 * right.order 0) (right.order 0 + right.order 1) := by
      rw [hrightZero, hrightOne]
      apply lt_min <;> dsimp only [r] <;> omega
    obtain ⟨s, hs, hsOrder⟩ := hrightScale
    change 2 * ordUnit K s =
      min (2 * right.order 0) (right.order 0 + right.order 1) at hsOrder
    have hscaleBound :
        2 * (r + 1) ≤
          min (2 * right.order 0) (right.order 0 + right.order 1) := by
      rw [← hsOrder] at hstrictDoubled ⊢
      omega
    have htailScale :
        Lattice.scaleIdeal
            (q.restrict S.right.carrier S.right.nondegenerate)
            S.right.lattice ≤
          Lattice.powerIdeal (K := K) (r + 1) :=
      scaleIdeal_le_powerIdeal_of_hasDoubledScaleOrder
        ⟨s, hs, hsOrder⟩ hscaleBound
    let U : Lattice.UnaryFirstSplitting q L r := {
      toOrthogonalDecomposition := S.decomposition
      first_rank := by
        rw [S.component_zero]
        exact S.left.bong.length_eq_finrank.symm
      tail_scale_le := by
        rw [S.component_one]
        exact htailScale }
    exact (beliLemma64_unaryFirst_excludes_hyperbolic_proved U hH).elim
  · have h10 : b.order 1 ≤ b.order 0 := le_of_not_gt h01
    have h12 : b.order 1 ≤ b.order 2 := h10.trans h13.le
    rcases b.beliCorollary44_i_unconditional hgood
        (1 : Fin (n + 3)) (by simp) h12 with ⟨S⟩
    have hleftOrder : S.left.bong.order 1 ≤
        S.left.bong.order 0 := by
      simpa [SegmentWitness.sourceIndex] using h10
    let hexists :=
      (S.left.bong.exists_isModular_iff_order_one_le_order_zero).2
        hleftOrder
    let a : Kˣ := Classical.choose hexists
    have hmodular : Lattice.IsModular
        (q.restrict S.left.carrier S.left.nondegenerate)
        S.left.lattice a := Classical.choose_spec hexists
    have hleftZero : S.left.bong.order 0 = b.order 0 := by
      simpa [SegmentWitness.sourceIndex] using
        S.left.order_eq (0 : Fin 2)
    have hleftOne : S.left.bong.order 1 = b.order 1 := by
      simpa [SegmentWitness.sourceIndex] using
        S.left.order_eq (1 : Fin 2)
    have hformula := S.left.bong.order_one_eq_of_isModular a hmodular
    have hsumLeft : S.left.bong.order 0 + S.left.bong.order 1 =
        2 * ordUnit K a := by
      calc
        S.left.bong.order 0 + S.left.bong.order 1 =
            S.left.bong.order 0 +
              (2 * ordUnit K a - S.left.bong.order 0) :=
          congrArg (fun z : Int ↦ S.left.bong.order 0 + z) hformula
        _ = 2 * ordUnit K a := by ring
    have hsum : b.order 0 + b.order 1 = 2 * ordUnit K a := by
      calc
        b.order 0 + b.order 1 =
            S.left.bong.order 0 + S.left.bong.order 1 :=
          congrArg₂ (fun x y : Int ↦ x + y)
            hleftZero.symm hleftOne.symm
        _ = 2 * ordUnit K a := hsumLeft
    have hr : r = ordUnit K a := by
      dsimp only [r]
      omega
    have hfirstScale :
        Lattice.scaleIdeal
            (q.restrict S.left.carrier S.left.nondegenerate)
            S.left.lattice = Lattice.powerIdeal (K := K) r := by
      rw [hmodular.scaleIdeal_eq_principal (by
        rw [← S.left.bong.length_eq_finrank]
        norm_num), Lattice.principalIdeal_eq_powerIdeal, hr]
    have htailScale :
        Lattice.scaleIdeal
            (q.restrict S.right.carrier S.right.nondegenerate)
            S.right.lattice ≤
          Lattice.powerIdeal (K := K) (r + 1) := by
      by_cases hn : n = 0
      · subst n
        let right := S.right.bong.castLength
          (by omega : 0 + 3 - 2 = 1)
        have hrightOrder : right.order 0 = b.order 2 := by
          rw [BONG.order_castLength_index]
          simpa [SegmentWitness.sourceIndex] using
            S.right.order_eq (0 : Fin 1)
        have hrightScale :
            Lattice.scaleIdeal
                (q.restrict S.right.carrier S.right.nondegenerate)
                S.right.lattice =
              Lattice.powerIdeal (K := K) (right.order 0) := by
          calc
            Lattice.scaleIdeal
                  (q.restrict S.right.carrier S.right.nondegenerate)
                  S.right.lattice =
                Lattice.principalIdeal (K := K)
                  (right.valueUnit 0 : K) :=
              right.scaleIdeal_eq_principal_valueUnit_zero_unary
            _ = Lattice.powerIdeal (K := K)
                (ordUnit K (right.valueUnit 0)) :=
              Lattice.principalIdeal_eq_powerIdeal _
            _ = Lattice.powerIdeal (K := K) (right.order 0) := by
              rw [right.order_eq_ordUnit]
        rw [hrightScale, Lattice.powerIdeal_le_iff, hrightOrder, hr]
        omega
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 :=
          ⟨n - 1, by omega⟩
        let rightRaw := S.right.toGoodBONG hgood
        let right := rightRaw.castLength
          (by omega : (k + 1) + 3 - 2 = k + 2)
        have hrightZero : right.order 0 = b.order 2 := by
          change ((S.right.toGoodBONG hgood).castLength _).order 0 =
            b.order 2
          exact S.right.order_toGoodBONG_castLength hgood
            (by omega : (k + 1) + 3 - 2 = k + 2)
            (0 : Fin (k + 2))
        have hrightOne : right.order 1 = b.order 3 := by
          change ((S.right.toGoodBONG hgood).castLength _).order 1 =
            b.order 3
          exact S.right.order_toGoodBONG_castLength hgood
            (by omega : (k + 1) + 3 - 2 = k + 2)
            (1 : Fin (k + 2))
        have h14 : b.order 1 ≤ b.order 3 :=
          hgood (1 : Fin (k + 4)) (by simp)
        have hrightScale :=
          right.toBONG.beliCorollary44_iv_unconditional right.good
        have hstrictDoubled : 2 * ordUnit K a <
            min (2 * right.order 0)
              (right.order 0 + right.order 1) := by
          rw [hrightZero, hrightOne, ← hsum]
          apply lt_min <;> omega
        have hscaleBound : 2 * (r + 1) ≤
            min (2 * right.order 0)
              (right.order 0 + right.order 1) := by
          obtain ⟨s, hs, hsOrder⟩ := hrightScale
          change 2 * ordUnit K s =
            min (2 * right.order 0)
              (right.order 0 + right.order 1) at hsOrder
          rw [← hsOrder] at hstrictDoubled ⊢
          rw [hr]
          omega
        exact scaleIdeal_le_powerIdeal_of_hasDoubledScaleOrder
          hrightScale hscaleBound
    have htailNorm :
        Lattice.normIdeal
            (q.restrict S.right.carrier S.right.nondegenerate)
            S.right.lattice = Lattice.powerIdeal (K := K) (b.order 2) := by
      let i : Fin (n + 3 - ((1 : Fin (n + 3)).val + 1)) :=
        ⟨0, by simp⟩
      have hi : S.right.bong.order i = b.order 2 := by
        calc
          S.right.bong.order i = b.order (S.right.sourceIndex i) :=
            S.right.order_eq i
          _ = b.order 2 := by
            apply congrArg b.order
            apply Fin.ext
            simp [SegmentWitness.sourceIndex, i,
              Nat.mod_eq_of_lt (by omega : 2 < n + 3)]
      calc
        Lattice.normIdeal
              (q.restrict S.right.carrier S.right.nondegenerate)
              S.right.lattice =
            Lattice.powerIdeal (K := K) (S.right.bong.order i) :=
          normIdeal_eq_powerIdeal_order_mk_zero S.right.bong i.isLt
        _ = Lattice.powerIdeal (K := K) (b.order 2) :=
          congrArg (Lattice.powerIdeal (K := K)) hi
    have hfirstNorm :
        Lattice.normIdeal
            (q.restrict S.left.carrier S.left.nondegenerate)
            S.left.lattice = Lattice.powerIdeal (K := K) (b.order 0) := by
      have hi : S.left.bong.order 0 = b.order 0 := by
        calc
          S.left.bong.order 0 =
              b.order (S.left.sourceIndex (0 : Fin 2)) :=
            S.left.order_eq (0 : Fin 2)
          _ = b.order 0 := by
            apply congrArg b.order
            apply Fin.ext
            simp [SegmentWitness.sourceIndex]
      calc
        Lattice.normIdeal
              (q.restrict S.left.carrier S.left.nondegenerate)
              S.left.lattice =
            Lattice.powerIdeal (K := K) (S.left.bong.order 0) :=
          normIdeal_eq_powerIdeal_order_mk_zero S.left.bong (by omega)
        _ = Lattice.powerIdeal (K := K) (b.order 0) :=
          congrArg (Lattice.powerIdeal (K := K)) hi
    have htailNormLt :
        Lattice.normIdeal
            (q.restrict S.right.carrier S.right.nondegenerate)
            S.right.lattice <
          Lattice.normIdeal
            (q.restrict S.left.carrier S.left.nondegenerate)
            S.left.lattice := by
      rw [htailNorm, hfirstNorm, Lattice.powerIdeal_lt_iff]
      exact h13
    let B : Lattice.BinaryFirstModularSplitting q L r := {
      toOrthogonalDecomposition := S.decomposition
      first_rank := by
        rw [S.component_zero]
        exact S.left.bong.length_eq_finrank.symm
      first_modular := by
        rw [S.component_zero]
        apply hmodular.of_principalIdeal_eq
        rw [Lattice.principalIdeal_eq_powerIdeal, hr]
        rfl
      first_scale_eq := by
        rw [S.component_zero]
        exact hfirstScale
      tail_scale_le := by
        rw [S.component_one]
        exact htailScale
      tail_norm_lt := by
        rw [S.component_one, S.component_zero]
        exact htailNormLt }
    have hfirst :=
      beliLemma64_binaryFirst_full_implies_first_proved B hH
    let P := b.prefixWitness 2 (by omega)
    rcases hfirst with ⟨x, y, hx, hy, hpair⟩
    have hcarrier : (S.decomposition.component 0).carrier = P.carrier := by
      rw [S.component_zero]
      change S.left.carrier = P.carrier
      exact S.left.carrier_eq_segmentCarrier.trans
        P.carrier_eq_segmentCarrier.symm
    let xv : V := x
    let yv : V := y
    have hxCarrier : xv ∈ (S.decomposition.component 0).carrier :=
      x.property
    have hyCarrier : yv ∈ (S.decomposition.component 0).carrier :=
      y.property
    let xP : P.carrier := ⟨xv, hcarrier ▸ hxCarrier⟩
    let yP : P.carrier := ⟨yv, hcarrier ▸ hyCarrier⟩
    have hxParent : (x : V) ∈ L :=
      B.toOrthogonalDecomposition.component_mem_parent 0 x hx
    have hyParent : (y : V) ∈ L :=
      B.toOrthogonalDecomposition.component_mem_parent 0 y hy
    refine ⟨xP, yP, P.contains_parent xP ?_, P.contains_parent yP ?_, ?_⟩
    · simpa [xP] using hxParent
    · simpa [yP] using hyParent
    · simpa [xP, yP] using hpair

/-- Concrete, unconditional realization of Beli (2003), Lemma 6.4. -/
noncomputable instance beliLemma64LawsProved :
    BeliLemma64Laws.{u, v} K where
  unaryFirst_excludes_hyperbolic S :=
    beliLemma64_unaryFirst_excludes_hyperbolic_proved S
  full_implies_first S :=
    beliLemma64_binaryFirst_full_implies_first_proved S
  full_implies_binaryPrefix b hgood h13 :=
    b.beliLemma64_full_implies_binaryPrefix_proved hgood h13

end BONG

end Bong
