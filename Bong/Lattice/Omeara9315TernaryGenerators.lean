/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaBinaryGeneralPlane
import Bong.Lattice.OmearaGeneralPlaneChangeOfComplement
import Bong.Lattice.OmearaModularNormClassification
import Bong.Lattice.OmearaOddRankProper
import Bong.Lattice.OrthogonalDecompositionProduct
import Bong.Lattice.OrthogonalProductIsometry

/-!
# O'Meara 93:15 in the ternary form used by Beli (2019)

A proper modular ternary lattice has an orthogonal basis whose diagonal
values all generate the norm ideal.  Section 5 of Beli (2019) only needs two
of those basis vectors.  We prove precisely that smaller statement.

After normalizing the scale to one, split a represented norm-generator line.
The orthogonal complement is a binary unimodular general plane
`A(alpha,beta)`.  If either diagonal coefficient is a valuation unit, that
coordinate and the split line give the required pair.  Otherwise add the
split norm-generator vector to the first plane coordinate.  O'Meara 82:15a
then supplies a new unary complement; both the new first coordinate and the
new complement generator have unit value.  This is the three-dimensional
calculation in the proof of O'Meara 93:15.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The two orthogonal norm-generator vectors needed from O'Meara 93:15. -/
structure TernaryOrthogonalNormGeneratorPairData
    (q : QuadraticSpace K V) (L : Lattice K V) where
  first : V
  second : V
  first_generator : IsNormGenerator q L first
  second_generator : IsNormGenerator q L second
  orthogonal : q.bilin first second = 0

namespace TernaryOrthogonalNormGeneratorPairData

/-- A valuation unit is nonzero. -/
private theorem valuationUnit_ne_zero {c : K}
    (hc : IsValuationUnit K c) : c ≠ 0 := by
  intro hzero
  rw [hzero, IsValuationUnit, ord_zero] at hc
  exact WithTop.top_ne_coe hc

/-- A valuation unit generates the unit coefficient ideal. -/
private theorem principalIdeal_eq_one_of_isValuationUnit {c : K}
    (hc : IsValuationUnit K c) :
    principalIdeal (K := K) c = principalIdeal (K := K) (1 : K) := by
  let u : Kˣ := Units.mk0 c (valuationUnit_ne_zero hc)
  simpa only [one_mul, u, Units.val_mk0] using
    principalIdeal_mul_eq_of_isValuationUnit (K := K) (1 : K) u hc

/-- Equal principal ideal to the unit ideal implies valuation-unit value. -/
private theorem isValuationUnit_of_principalIdeal_eq_one
    {c : K} (hc : c ≠ 0)
    (hideal : principalIdeal (K := K) c =
      principalIdeal (K := K) (1 : K)) :
    IsValuationUnit K c := by
  let cu : Kˣ := Units.mk0 c hc
  have hord := (principalIdeal_eq_iff_ordUnit_eq cu (1 : Kˣ)).mp (by
    simpa only [cu, Units.val_mk0, Units.val_one] using hideal)
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have honeMul := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at honeMul
    omega
  rw [hone] at hord
  change IsValuationUnit K (cu : K)
  exact (isValuationUnit_iff_ordUnit_eq_zero K cu).2 hord

/-- Removing a trivial form rescaling does not change a lattice. -/
private noncomputable def rescaleUnitOneIsometry
    (p : QuadraticSpace K V) (A : Lattice K V) :
    Isometry (p.rescaleUnit (1 : Kˣ)) p A A where
  toLinearEquiv := LinearEquiv.refl K V
  map_bilin := by
    intro y z
    simp only [LinearEquiv.refl_apply,
      QuadraticSpace.rescaleUnit_bilin_apply, Units.val_one, one_mul]
  map_mem := by intro y; rfl

/-- Rescaling first by `a⁻¹` and then by `a` is the original form. -/
private noncomputable def rescaleInverseIsometry
    (p : QuadraticSpace K V) (A : Lattice K V) (a : Kˣ) :
    Isometry ((p.rescaleUnit a⁻¹).rescaleUnit a) p A A where
  toLinearEquiv := LinearEquiv.refl K V
  map_bilin := by
    intro y z
    simp only [LinearEquiv.refl_apply,
      QuadraticSpace.rescaleUnit_bilin_apply, Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero a]
  map_mem := by intro y; rfl

/-- The standard first vector of an O'Meara general plane. -/
private def planeFirst : Fin 2 → K := ![1, 0]

/-- The standard second vector of an O'Meara general plane. -/
private def planeSecond : Fin 2 → K := ![0, 1]

private theorem planeFirst_mem :
    planeFirst (K := K) ∈ hyperbolicPlaneLattice (K := K) := by
  rw [mem_omearaPlaneLattice_iff]
  simp [planeFirst]

private theorem planeSecond_mem :
    planeSecond (K := K) ∈ hyperbolicPlaneLattice (K := K) := by
  rw [mem_omearaPlaneLattice_iff]
  simp [planeSecond]

private theorem generalPlane_quadratic_planeFirst
    (alpha beta : K) (h : alpha * beta ≠ 1) :
    (QuadraticSpace.omearaGeneralPlane alpha beta h).quadratic
        (planeFirst (K := K)) = alpha := by
  simp [QuadraticSpace.quadratic,
    QuadraticSpace.omearaGeneralPlane_bilin_apply, planeFirst]

private theorem generalPlane_quadratic_planeSecond
    (alpha beta : K) (h : alpha * beta ≠ 1) :
    (QuadraticSpace.omearaGeneralPlane alpha beta h).quadratic
        (planeSecond (K := K)) = beta := by
  simp [QuadraticSpace.quadratic,
    QuadraticSpace.omearaGeneralPlane_bilin_apply, planeSecond]

set_option maxHeartbeats 0 in
/-- Unimodular ternary case of O'Meara 93:15, in the two-vector form used
in Beli's exceptional Section 5 adjacency. -/
noncomputable def ofUnimodular
    (hmodular : IsModular q L (1 : Kˣ))
    (hrank : finrank K V = 3) :
    TernaryOrthogonalNormGeneratorPairData q L := by
  letI : Module.Finite K V := L.moduleFinite
  have hodd : Odd (finrank K V) := by
    rw [hrank]
    norm_num
  have hproper : normIdeal q L = scaleIdeal q L :=
    normIdeal_eq_scaleIdeal_of_modular_of_odd_rank
      q L (1 : Kˣ) hmodular hodd
  have hnorm : normIdeal q L = principalIdeal (K := K) (1 : K) :=
    hproper.trans (hmodular.scaleIdeal_eq_principal (by omega))
  let hexists := exists_isNormGenerator_of_finrank_pos q L (by omega)
  let x : V := Classical.choose hexists
  have hxgen : IsNormGenerator q L x :=
    (Classical.choose_spec hexists).1
  have hxne : q.quadratic x ≠ 0 :=
    (Classical.choose_spec hexists).2
  have hxanisotropic : q.IsAnisotropic x := hxne
  have hxunit : IsValuationUnit K (q.quadratic x) := by
    apply isValuationUnit_of_principalIdeal_eq_one hxne
    exact hxgen.normIdeal_eq.symm.trans hnorm
  let C := unaryScaleComponent (q := q) x hxne
  have hCL : C.ambientSubmodule ≤ L.toSubmodule :=
    unaryScaleComponent_ambientSubmodule_le hxanisotropic hxgen.mem
  have hCmodular : IsModular C.space C.lattice
      (Units.mk0 (q.quadratic x) hxne) :=
    unaryScaleComponent_isModular hxanisotropic
  have hscale : scaleIdeal q L ≤
      principalIdeal (K := K) (q.quadratic x) := by
    rw [← hxgen.normIdeal_eq, hproper]
  let S : OrthogonalDecomposition q L 2 :=
    omearaModularSplittingOfScaleIdealLe C hCL hCmodular hscale
  have hCeq : S.component 0 = C := rfl
  have hCrank : finrank K (S.component 0).carrier = 1 := by
    rw [hCeq]
    change finrank K (K ∙ x) = 1
    simpa using Module.finrank_eq_card_basis
      (unarySpanBasis (K := K) x hxanisotropic.ne_zero)
  let B := S.component 1
  letI : Module.Finite K (S.component 0).carrier :=
    (S.component 0).lattice.moduleFinite
  letI : Module.Finite K B.carrier := B.lattice.moduleFinite
  have hBrank : finrank K B.carrier = 2 := by
    have htotal := S.pairProductLatticeIsometry.toLinearEquiv.finrank_eq
    change finrank K ((S.component 0).carrier × B.carrier) =
      finrank K V at htotal
    rw [Module.finrank_prod, hCrank, hrank] at htotal
    omega
  have hBmodular : IsModular B.space B.lattice (1 : Kˣ) :=
    S.component_modular_of_ambient hmodular 1
  let G := BinaryModularGeneralPlaneData.ofModular
    B.space B.lattice (1 : Kˣ) hBmodular hBrank
  let plane := QuadraticSpace.omearaGeneralPlane
    G.leftCoefficient G.rightCoefficient G.nondegenerate
  let g : Isometry B.space plane B.lattice
      (hyperbolicPlaneLattice (K := K)) :=
    G.isometry.trans
      (rescaleUnitOneIsometry plane (hyperbolicPlaneLattice (K := K)))
  let expose : Isometry q
      ((S.component 0).space.orthogonalSum B.space) L
      (product (S.component 0).lattice B.lattice) :=
    S.pairProductLatticeIsometry.symm
  let identify :=
    (Isometry.refl (S.component 0).space (S.component 0).lattice)
      |>.orthogonalProductBasic g
  let swap : Isometry
      ((S.component 0).space.orthogonalSum plane)
      (plane.orthogonalSum (S.component 0).space)
      (product (S.component 0).lattice
        (hyperbolicPlaneLattice (K := K)))
      (product (hyperbolicPlaneLattice (K := K))
        (S.component 0).lattice) := orthogonalProductSwap
  let displayed := expose.trans (identify.trans swap)
  have hdisplayedModular : IsModular
      (plane.orthogonalSum (S.component 0).space)
      (product (hyperbolicPlaneLattice (K := K))
        (S.component 0).lattice) (1 : Kˣ) :=
    hmodular.mapLatticeIsometry displayed
  have hdisplayedNorm :
      normIdeal (plane.orthogonalSum (S.component 0).space)
          (product (hyperbolicPlaneLattice (K := K))
            (S.component 0).lattice) =
        principalIdeal (K := K) (1 : K) := by
    calc
      normIdeal (plane.orthogonalSum (S.component 0).space)
          (product (hyperbolicPlaneLattice (K := K))
            (S.component 0).lattice) = normIdeal q L := by
        rw [← displayed.map_eq]
        exact normIdeal_map_isometry displayed.toQuadraticSpaceIsometry L
      _ = principalIdeal (K := K) (1 : K) := hnorm
  let z : (S.component 0).carrier :=
    ⟨x, by
      change x ∈ K ∙ x
      exact Submodule.mem_span_singleton_self x⟩
  have hzmem : z ∈ (S.component 0).lattice := by
    change z ∈ basisLattice
      (unarySpanBasis (K := K) x hxanisotropic.ne_zero)
    have hb : unarySpanBasis (K := K) x hxanisotropic.ne_zero 0 = z := by
      apply Subtype.ext
      exact coe_unarySpanBasis (K := K) x hxanisotropic.ne_zero 0
    rw [← hb]
    exact Submodule.subset_span ⟨0, rfl⟩
  have hqz : (S.component 0).space.quadratic z = q.quadratic x := by
    rfl
  have hzunit : IsValuationUnit K
      ((S.component 0).space.quadratic z) := by
    rw [hqz]
    exact hxunit
  have makePair
      (F : Isometry q
        (plane.orthogonalSum (S.component 0).space) L
        (product (hyperbolicPlaneLattice (K := K))
          (S.component 0).lattice))
      (e : Fin 2 → K) (he : e ∈ hyperbolicPlaneLattice (K := K))
      (heunit : IsValuationUnit K (plane.quadratic e)) :
      TernaryOrthogonalNormGeneratorPairData q L := by
    let u : (Fin 2 → K) × (S.component 0).carrier := (e, 0)
    let v : (Fin 2 → K) × (S.component 0).carrier := (0, z)
    have huMem : u ∈ product (hyperbolicPlaneLattice (K := K))
        (S.component 0).lattice := by
      exact inl_mem_product_iff.mpr he
    have hvMem : v ∈ product (hyperbolicPlaneLattice (K := K))
        (S.component 0).lattice := by
      exact inr_mem_product_iff.mpr hzmem
    have huQuad : (plane.orthogonalSum (S.component 0).space).quadratic u =
        plane.quadratic e := by simp [u]
    have hvQuad : (plane.orthogonalSum (S.component 0).space).quadratic v =
        (S.component 0).space.quadratic z := by simp [v]
    have huGen : IsNormGenerator
        (plane.orthogonalSum (S.component 0).space)
        (product (hyperbolicPlaneLattice (K := K))
          (S.component 0).lattice) u := by
      refine ⟨huMem, ?_⟩
      rw [hdisplayedNorm, huQuad]
      exact (principalIdeal_eq_one_of_isValuationUnit heunit).symm
    have hvGen : IsNormGenerator
        (plane.orthogonalSum (S.component 0).space)
        (product (hyperbolicPlaneLattice (K := K))
          (S.component 0).lattice) v := by
      refine ⟨hvMem, ?_⟩
      rw [hdisplayedNorm, hvQuad]
      exact (principalIdeal_eq_one_of_isValuationUnit hzunit).symm
    refine
      { first := F.symm.toLinearEquiv u
        second := F.symm.toLinearEquiv v
        first_generator := huGen.mapLatticeIsometry F.symm
        second_generator := hvGen.mapLatticeIsometry F.symm
        orthogonal := ?_ }
    have horth :
        (plane.orthogonalSum (S.component 0).space).bilin u v = 0 := by
      simp [u, v]
    simpa only using F.symm.map_bilin u v |>.trans horth
  by_cases halpha : IsValuationUnit K G.leftCoefficient
  · apply makePair displayed (planeFirst (K := K)) planeFirst_mem
    simpa only [plane, generalPlane_quadratic_planeFirst] using halpha
  · by_cases hbeta : IsValuationUnit K G.rightCoefficient
    · apply makePair displayed (planeSecond (K := K)) planeSecond_mem
      simpa only [plane, generalPlane_quadratic_planeSecond] using hbeta
    · have halphaMax : IsInMaximalIdeal K G.leftCoefficient :=
        isInMaximalIdeal_of_mem_integerRing_of_not_isValuationUnit
          G.left_integral halpha
      have hbetaMax : IsInMaximalIdeal K G.rightCoefficient :=
        isInMaximalIdeal_of_mem_integerRing_of_not_isValuationUnit
          G.right_integral hbeta
      have hnewIntegral : G.leftCoefficient +
          (S.component 0).space.quadratic z ∈ IntegerRing K :=
        (IntegerRing K).toSubring.add_mem G.left_integral
          ((mem_integerRing_iff K).2 hzunit.ge)
      have hnewUnit : IsValuationUnit K
          (G.leftCoefficient + (S.component 0).space.quadratic z) := by
        change ord K (G.leftCoefficient +
          (S.component 0).space.quadratic z) = 0
        have hlt : ord K ((S.component 0).space.quadratic z) <
            ord K G.leftCoefficient := by
          rw [hzunit]
          exact halphaMax
        rw [(ord K).map_add_eq_of_lt_right hlt, hzunit]
      have hproductMax : IsInMaximalIdeal K
          ((G.leftCoefficient + (S.component 0).space.quadratic z) *
            G.rightCoefficient) :=
        isIntegral_mul_isInMaximalIdeal K
          ((mem_integerRing_iff K).1 hnewIntegral) hbetaMax
      have hnewDetUnit : IsValuationUnit K
          ((G.leftCoefficient + (S.component 0).space.quadratic z) *
              G.rightCoefficient - 1) := by
        have hnegMax : IsInMaximalIdeal K
            (-((G.leftCoefficient + (S.component 0).space.quadratic z) *
              G.rightCoefficient)) := by
          simpa only [IsInMaximalIdeal, ord_neg] using hproductMax
        have hone := isValuationUnit_one_add_of_isInMaximalIdeal hnegMax
        have hrearrange :
            (G.leftCoefficient + (S.component 0).space.quadratic z) *
                G.rightCoefficient - 1 =
              -(1 + -((G.leftCoefficient +
                (S.component 0).space.quadratic z) * G.rightCoefficient)) := by
          ring
        rw [hrearrange, IsValuationUnit, ord_neg]
        exact hone
      let E := omearaGeneralPlaneChangeOfComplement
        (S.component 0).space (S.component 0).lattice
        G.leftCoefficient G.rightCoefficient G.nondegenerate z
        G.left_integral G.right_integral hzmem hnewIntegral hnewDetUnit
        hdisplayedModular
      let newPlane := QuadraticSpace.omearaGeneralPlane
        (G.leftCoefficient + (S.component 0).space.quadratic z)
        G.rightCoefficient (by
          exact sub_ne_zero.mp (by
            intro hzero
            rw [hzero] at hnewDetUnit
            simp [IsValuationUnit] at hnewDetUnit))
      let final := displayed.trans E.displayedIsometry
      let R := E.decomposition.component 1
      letI : Module.Finite K (E.decomposition.component 0).carrier :=
        (E.decomposition.component 0).lattice.moduleFinite
      letI : Module.Finite K R.carrier := R.lattice.moduleFinite
      have hfirstRank : finrank K (E.decomposition.component 0).carrier = 2 := by
        exact E.first.toLinearEquiv.finrank_eq.trans (by simp)
      have hRrank : finrank K R.carrier = 1 := by
        have htotal := E.decomposition.pairProductLatticeIsometry
          |>.toLinearEquiv.finrank_eq
        change finrank K ((E.decomposition.component 0).carrier × R.carrier) =
          finrank K ((Fin 2 → K) × (S.component 0).carrier) at htotal
        have hfinTwo : finrank K (Fin 2 → K) = 2 := by simp
        rw [Module.finrank_prod, Module.finrank_prod, hfirstRank, hCrank,
          hfinTwo] at htotal
        omega
      have hRmodular : IsModular R.space R.lattice (1 : Kˣ) :=
        E.decomposition.component_modular_of_ambient hdisplayedModular 1
      have hRnorm : normIdeal R.space R.lattice =
          principalIdeal (K := K) (1 : K) :=
        (normIdeal_eq_scaleIdeal_of_finrank_eq_one
          R.space R.lattice hRrank).trans
            (hRmodular.scaleIdeal_eq_principal (by omega))
      let hyExists := exists_isNormGenerator_of_finrank_pos
        R.space R.lattice (by omega)
      let y : R.carrier := Classical.choose hyExists
      have hyGen : IsNormGenerator R.space R.lattice y :=
        (Classical.choose_spec hyExists).1
      have hyNe : R.space.quadratic y ≠ 0 :=
        (Classical.choose_spec hyExists).2
      have hyUnit : IsValuationUnit K (R.space.quadratic y) := by
        apply isValuationUnit_of_principalIdeal_eq_one hyNe
        exact hyGen.normIdeal_eq.symm.trans hRnorm
      let u : (Fin 2 → K) × R.carrier := (planeFirst (K := K), 0)
      let v : (Fin 2 → K) × R.carrier := (0, y)
      have huMem : u ∈ product (hyperbolicPlaneLattice (K := K))
          R.lattice := inl_mem_product_iff.mpr planeFirst_mem
      have hvMem : v ∈ product (hyperbolicPlaneLattice (K := K))
          R.lattice := inr_mem_product_iff.mpr hyGen.mem
      have hfinalNorm :
          normIdeal (newPlane.orthogonalSum R.space)
              (product (hyperbolicPlaneLattice (K := K)) R.lattice) =
            principalIdeal (K := K) (1 : K) := by
        calc
          normIdeal (newPlane.orthogonalSum R.space)
              (product (hyperbolicPlaneLattice (K := K)) R.lattice) =
              normIdeal q L := by
            rw [← final.map_eq]
            exact normIdeal_map_isometry final.toQuadraticSpaceIsometry L
          _ = principalIdeal (K := K) (1 : K) := hnorm
      have huQuad : (newPlane.orthogonalSum R.space).quadratic u =
          G.leftCoefficient + (S.component 0).space.quadratic z := by
        simp [u, newPlane, generalPlane_quadratic_planeFirst]
      have hvQuad : (newPlane.orthogonalSum R.space).quadratic v =
          R.space.quadratic y := by simp [v]
      have huGen : IsNormGenerator (newPlane.orthogonalSum R.space)
          (product (hyperbolicPlaneLattice (K := K)) R.lattice) u := by
        refine ⟨huMem, ?_⟩
        rw [hfinalNorm, huQuad]
        exact (principalIdeal_eq_one_of_isValuationUnit hnewUnit).symm
      have hvGen : IsNormGenerator (newPlane.orthogonalSum R.space)
          (product (hyperbolicPlaneLattice (K := K)) R.lattice) v := by
        refine ⟨hvMem, ?_⟩
        rw [hfinalNorm, hvQuad]
        exact (principalIdeal_eq_one_of_isValuationUnit hyUnit).symm
      refine
        { first := final.symm.toLinearEquiv u
          second := final.symm.toLinearEquiv v
          first_generator := huGen.mapLatticeIsometry final.symm
          second_generator := hvGen.mapLatticeIsometry final.symm
          orthogonal := ?_ }
      have horth : (newPlane.orthogonalSum R.space).bilin u v = 0 := by
        simp [u, v]
      simpa only using final.symm.map_bilin u v |>.trans horth

set_option maxHeartbeats 0 in
/-- Arbitrary-scale ternary form of O'Meara 93:15. -/
noncomputable def ofModular
    (a : Kˣ) (hmodular : IsModular q L a)
    (hrank : finrank K V = 3) :
    TernaryOrthogonalNormGeneratorPairData q L := by
  let q0 := q.rescaleUnit a⁻¹
  have hunit : IsModular q0 L (1 : Kˣ) := by
    have h := hmodular.isUnimodular_rescaleQuadraticInverse
    change IsModular q0 L (1 : Kˣ) at h
    exact h
  let D := ofUnimodular (q := q0) (L := L) hunit hrank
  have hfirst : IsNormGenerator q L D.first := by
    have h := D.first_generator.rescaleQuadraticUnit a
    exact h.mapLatticeIsometry (rescaleInverseIsometry q L a)
  have hsecond : IsNormGenerator q L D.second := by
    have h := D.second_generator.rescaleQuadraticUnit a
    exact h.mapLatticeIsometry (rescaleInverseIsometry q L a)
  refine
    { first := D.first
      second := D.second
      first_generator := hfirst
      second_generator := hsecond
      orthogonal := ?_ }
  have h := D.orthogonal
  have h' : (a⁻¹ : K) * q.bilin D.first D.second = 0 := by
    simpa only [q0, QuadraticSpace.rescaleUnit_bilin_apply,
      Units.val_inv_eq_inv_val] using h
  exact (mul_eq_zero.mp h').resolve_left (inv_ne_zero (Units.ne_zero a))

end TernaryOrthogonalNormGeneratorPairData

end Lattice

end Bong
