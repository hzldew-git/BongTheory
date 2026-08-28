/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma318
import Bong.Lattice.BasisUnits
import Bong.Lattice.Isometry
import Bong.QuadraticSpace.HyperbolicPlane
import Mathlib.Tactic.FinCases

/-!
# Beli (2003), Lemma 3.19

Two vectors whose individual norms have order above `R`, while the norm of
their sum has order exactly `R`, generate the scaled hyperbolic plane
`π^(R-e) A(0, 0)`.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}

namespace Dyadic

/-- A square root of a principal unit of depth above `2e` can be signed so
that its sum with one has order exactly `e`. -/
theorem exists_squareRoot_one_sub_with_order_one_add_eq_ord_two
    [QuadraticDefectLaws K]
    (a : Kˣ)
    (hlarge : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    ∃ s : Kˣ,
      (s : K) ^ 2 = 1 - (a : K) ∧
      ord K (1 + (s : K)) = ord K (2 : K) ∧
      ordUnit K s = 0 := by
  let b : Kˣ := Units.mk0 (1 - (a : K))
    (BONG.one_sub_ne_zero_of_two_e_lt_order a hlarge)
  have hbSquare : IsSquare b :=
    BONG.isSquare_one_sub_of_two_e_lt_order a hlarge
  rcases hbSquare with ⟨s, hs⟩
  have hsField : (s : K) ^ 2 = 1 - (a : K) := by
    have hsValue : (b : K) = (s : K) ^ 2 := by
      simpa [pow_two] using congrArg Units.val hs
    exact hsValue.symm
  have hbOrder : ordUnit K b = 0 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    change ord K (1 - (a : K)) = 0
    exact BONG.ord_one_sub_eq_zero_of_two_e_lt_order a hlarge
  have hsOrder : ordUnit K s = 0 := by
    rw [hs, ordUnit_mul] at hbOrder
    omega
  have hfactor : 1 - (s : K) ^ 2 = (a : K) := by
    rw [hsField]
    ring
  have hvaluation : ord K (2 : K) + ord K (2 : K) <
      ord K (1 - (s : K) ^ 2) := by
    rw [hfactor, ← coe_ordUnit, ← ramificationIndex_spec]
    apply WithTop.coe_lt_coe.mpr
    simpa [two_mul] using hlarge
  rcases one_sub_one_add_order_dichotomy_of_two_ord_two_lt
      (K := K) (s : K) hvaluation with hminus | hplus
  · refine ⟨-s, ?_, ?_, ?_⟩
    · change (-((s : K))) ^ 2 = 1 - (a : K)
      simpa using hsField
    · simpa only [Units.val_neg, sub_eq_add_neg] using hminus.1
    · have hsNegOrder : ordUnit K (-s) = ordUnit K s := by
        apply WithTop.coe_injective
        rw [coe_ordUnit, coe_ordUnit]
        simpa only [Units.val_neg] using ord_neg K (s : K)
      exact hsNegOrder.trans hsOrder
  · exact ⟨s, hsField, hplus.1, hsOrder⟩

end Dyadic

namespace Lattice

/-- A basis of two isotropic vectors with mixed coefficient `s` identifies
its basis lattice with the standard lattice in the scaled hyperbolic plane. -/
theorem basisLattice_isIsometric_hyperbolicPlane
    (q : QuadraticSpace K V) (b : Basis (Fin 2) K V) (s : Kˣ)
    (hzero : q.quadratic (b 0) = 0)
    (hone : q.quadratic (b 1) = 0)
    (hmixed : q.bilin (b 0) (b 1) = (s : K)) :
    IsIsometric q (QuadraticSpace.hyperbolicPlane s)
      (basisLattice b) (hyperbolicPlaneLattice (K := K)) := by
  let f : V ≃ₗ[K] (Fin 2 → K) := b.equivFun
  refine ⟨{
    toLinearEquiv := f
    map_bilin := ?_
    map_mem := ?_
  }⟩
  · intro x y
    let x0 := b.repr x 0
    let x1 := b.repr x 1
    let y0 := b.repr y 0
    let y1 := b.repr y 1
    have hx := b.sum_repr x
    have hy := b.sum_repr y
    rw [Fin.sum_univ_two] at hx hy
    change x0 • b 0 + x1 • b 1 = x at hx
    change y0 • b 0 + y1 • b 1 = y at hy
    rw [QuadraticSpace.hyperbolicPlane_bilin_apply]
    simp only [f, Basis.equivFun_apply]
    change (s : K) * (x0 * y1 + x1 * y0) = q.bilin x y
    rw [← hx, ← hy]
    simp only [LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right]
    rw [show q.bilin (b 0) (b 0) = 0 from hzero,
      show q.bilin (b 1) (b 1) = 0 from hone,
      hmixed, q.isSymm.eq (b 1) (b 0), hmixed]
    ring
  · intro x
    change x ∈ basisLattice b ↔
      b.equivFun x ∈ hyperbolicPlaneLattice (K := K)
    rw [mem_basisLattice_iff_repr_mem_integerRing,
      hyperbolicPlaneLattice,
      mem_basisLattice_iff_repr_mem_integerRing]
    simp only [Pi.basisFun_repr, Basis.equivFun_apply]

end Lattice

namespace BONG

/-- The ordered pair used to model the lattice `𝒪x + 𝒪y`. -/
def binaryPairFamily (x y : V) : Fin 2 → V :=
  ![x, y]

omit [AddCommGroup V] in
@[simp]
theorem binaryPairFamily_zero (x y : V) :
    binaryPairFamily x y 0 = x :=
  rfl

omit [AddCommGroup V] in
@[simp]
theorem binaryPairFamily_one (x y : V) :
    binaryPairFamily x y 1 = y :=
  rfl

/-- The ambient two-dimensional span of an ordered pair. -/
def binaryPairSpan (x y : V) : Submodule K V :=
  Submodule.span K (Set.range (binaryPairFamily x y))

/-- The pair itself as a basis of its span. -/
noncomputable def binaryPairBasis (x y : V)
    (hli : LinearIndependent K (binaryPairFamily x y)) :
    Basis (Fin 2) K (binaryPairSpan (K := K) x y) :=
  Module.Basis.span hli

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
@[simp]
theorem coe_binaryPairBasis (x y : V)
    (hli : LinearIndependent K (binaryPairFamily x y)) (i : Fin 2) :
    ((binaryPairBasis (K := K) x y hli i :
      binaryPairSpan (K := K) x y) : V) = binaryPairFamily x y i := by
  exact congrArg Subtype.val (Module.Basis.span_apply hli i)

/-- The polarization step in Lemma 3.19: the mixed coefficient has order
`R-e`. -/
theorem mixedPairing_order_eq_sub_ramificationIndex
    (x y : V) (R : Int)
    (hx : (R : WithTop Int) < ord K (q.quadratic x))
    (hy : (R : WithTop Int) < ord K (q.quadratic y))
    (hsum : ord K (q.quadratic (x + y)) = (R : WithTop Int)) :
    ∃ hne : q.bilin x y ≠ 0,
      ordUnit K (Units.mk0 (q.bilin x y) hne) =
        R - ramificationIndex K := by
  let A := q.quadratic x
  let C := q.quadratic y
  let D := q.bilin x y
  let S := q.quadratic (x + y)
  have hACHigh : (R : WithTop Int) < ord K (A + C) := by
    exact (lt_min hx hy).trans_le (min_ord_le_ord_add K A C)
  have hSlt : ord K S < ord K (A + C) := by
    rw [hsum]
    exact hACHigh
  have hpolar : (2 : K) * D = S - (A + C) := by
    dsimp [A, C, D, S]
    rw [q.quadratic_add]
    ring
  have htwoD : ord K ((2 : K) * D) = (R : WithTop Int) := by
    rw [hpolar]
    rw [(ord K).map_sub_eq_of_lt_left hSlt, hsum]
  have hDne : D ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero, ord_zero] at htwoD
    exact WithTop.top_ne_coe htwoD
  let Du : Kˣ := Units.mk0 D hDne
  have horder : ordUnit K Du = R - ramificationIndex K := by
    rw [ord_mul, ← ramificationIndex_spec] at htwoD
    change (((ramificationIndex K : Int) : WithTop Int) +
      ord K (Du : K)) = (R : WithTop Int) at htwoD
    rw [← coe_ordUnit] at htwoD
    have hfinite :
        (((ramificationIndex K : Int) + ordUnit K Du : Int) :
          WithTop Int) = (R : WithTop Int) := by
      simpa only [WithTop.coe_add] using htwoD
    have hint : (ramificationIndex K : Int) + ordUnit K Du = R :=
      WithTop.coe_injective hfinite
    omega
  exact ⟨hDne, horder⟩

/-- The normalized binary discriminant has a square root whose sign is
adapted to an integral isotropic shear. -/
theorem exists_adapted_binary_discriminant_root
    [QuadraticDefectLaws K]
    (A C D : K) (R : Int) (hDne : D ≠ 0)
    (hA : (R : WithTop Int) < ord K A)
    (hC : (R : WithTop Int) ≤ ord K C)
    (hD : ordUnit K (Units.mk0 D hDne) =
      R - ramificationIndex K) :
    ∃ s : Kˣ,
      (s : K) ^ 2 = 1 - A * C / D ^ 2 ∧
      ord K (1 + (s : K)) = ord K (2 : K) ∧
      ordUnit K s = 0 := by
  by_cases hAC : A * C = 0
  · refine ⟨1, ?_, ?_, ?_⟩
    · simp [hAC]
    · norm_num
    · apply WithTop.coe_injective
      rw [coe_ordUnit]
      simp
  · have hAne : A ≠ 0 := by
      intro hzero
      exact hAC (by simp [hzero])
    have hCne : C ≠ 0 := by
      intro hzero
      exact hAC (by simp [hzero])
    let Au : Kˣ := Units.mk0 A hAne
    let Cu : Kˣ := Units.mk0 C hCne
    let Du : Kˣ := Units.mk0 D hDne
    let a : Kˣ := Au * Cu / Du ^ 2
    have hAu : R < ordUnit K Au := by
      apply WithTop.coe_lt_coe.mp
      rw [coe_ordUnit]
      exact hA
    have hCu : R ≤ ordUnit K Cu := by
      apply WithTop.coe_le_coe.mp
      rw [coe_ordUnit]
      exact hC
    have haOrder :
        2 * (ramificationIndex K : Int) < ordUnit K a := by
      dsimp [a]
      simp only [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
        ordUnit_pow]
      change 2 * (ramificationIndex K : Int) <
        ordUnit K Au + ordUnit K Cu + -(2 * ordUnit K Du)
      change ordUnit K Du = R - ramificationIndex K at hD
      omega
    rcases
        exists_squareRoot_one_sub_with_order_one_add_eq_ord_two
          a haOrder with ⟨s, hs, hsum, hsOrder⟩
    have haField : (a : K) = A * C / D ^ 2 := by
      dsimp [a, Au, Cu, Du]
      simp only [Units.val_div_eq_div_val, Units.val_mul,
        Units.val_mk0, Units.val_pow_eq_pow_val]
    exact ⟨s, by rwa [haField] at hs, hsum, hsOrder⟩

/-- The first integral shear used to split a binary hyperbolic plane. -/
def binaryFirstIsotropicShear (A D delta : K) : K :=
  -A / (D + delta)

/-- The second integral shear used after the first vector is isotropic. -/
def binarySecondIsotropicShear (C delta : K) : K :=
  C / (2 * delta)

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
theorem binaryFirstIsotropicShear_quadratic_identity
    (A C D delta : K)
    (hdisc : delta ^ 2 = D ^ 2 - A * C)
    (hdenom : D + delta ≠ 0) :
    A + 2 * binaryFirstIsotropicShear A D delta * D +
        binaryFirstIsotropicShear A D delta ^ 2 * C = 0 := by
  dsimp [binaryFirstIsotropicShear]
  field_simp [hdenom]
  linear_combination A * hdisc

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
theorem binaryFirstIsotropicShear_mixed_identity
    (A C D delta : K)
    (hdisc : delta ^ 2 = D ^ 2 - A * C)
    (hdenom : D + delta ≠ 0) :
    D + binaryFirstIsotropicShear A D delta * C = delta := by
  dsimp [binaryFirstIsotropicShear]
  field_simp [hdenom]
  linear_combination -hdisc

omit [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
theorem binarySecondIsotropicShear_quadratic_identity
    (C delta : K) (hdelta : delta ≠ 0) :
    C - 2 * binarySecondIsotropicShear C delta * delta = 0 := by
  dsimp [binarySecondIsotropicShear]
  field_simp
  ring

/-- Intrinsic reading of `𝒪x + 𝒪y ≅ π^r A(0,0)`: the ordered pair is a
basis of its nondegenerate span, and its basis lattice is isometric to the
standard lattice in the hyperbolic plane with mixed coefficient `π^r`. -/
def IsScaledHyperbolicPair (q : QuadraticSpace K V) (x y : V)
    (r : Int) : Prop :=
  ∃ hli : LinearIndependent K (binaryPairFamily x y),
    ∃ hnondeg :
        (q.bilin.restrict (binaryPairSpan (K := K) x y)).Nondegenerate,
      Lattice.IsIsometric
        (q.restrict (binaryPairSpan (K := K) x y) hnondeg)
        (QuadraticSpace.hyperbolicPlane (uniformizerPowerUnit K r))
        (Lattice.basisLattice (binaryPairBasis (K := K) x y hli))
        (Lattice.hyperbolicPlaneLattice (K := K))

/-- Asymmetric form of Beli (2003), Lemma 3.19.  If the mixed pairing has
order `R-e`, one diagonal value has order strictly above `R`, and the other
has order at least `R`, the pair still generates the scaled hyperbolic plane.
This is the exact one-strict-inequality form used in Lemma 7.3. -/
theorem beliLemma319_of_mixedPairing [QuadraticDefectLaws K]
    (x y : V) (R : Int)
    (hDne : q.bilin x y ≠ 0)
    (hDorder :
      ordUnit K (Units.mk0 (q.bilin x y) hDne) =
        R - ramificationIndex K)
    (hx : (R : WithTop Int) < ord K (q.quadratic x))
    (hy : (R : WithTop Int) ≤ ord K (q.quadratic y)) :
    IsScaledHyperbolicPair q x y
      (R - ramificationIndex K) := by
  let A := q.quadratic x
  let C := q.quadratic y
  let D := q.bilin x y
  let r : Int := R - ramificationIndex K
  change (R : WithTop Int) < ord K A at hx
  change (R : WithTop Int) ≤ ord K C at hy
  change D ≠ 0 at hDne
  let Du : Kˣ := Units.mk0 D hDne
  change ordUnit K Du = r at hDorder
  rcases exists_adapted_binary_discriminant_root
      A C D R hDne hx hy hDorder with
    ⟨s, hsDisc, hsAdd, hsOrder⟩
  let deltaUnit : Kˣ := Du * s
  let delta : K := (deltaUnit : K)
  have hdeltaNe : delta ≠ 0 := Units.ne_zero deltaUnit
  have hdeltaOrder : ordUnit K deltaUnit = r := by
    dsimp [deltaUnit]
    rw [ordUnit_mul, hDorder, hsOrder, add_zero]
  have hdisc : delta ^ 2 = D ^ 2 - A * C := by
    dsimp [delta, deltaUnit, Du]
    rw [mul_pow, hsDisc]
    field_simp [hDne]
  have hdenomFactor : D + delta = D * (1 + (s : K)) := by
    dsimp [delta, deltaUnit, Du]
    ring
  have hdenomOrder : ord K (D + delta) = (R : WithTop Int) := by
    rw [hdenomFactor, ord_mul, hsAdd]
    change ord K (Du : K) + ord K (2 : K) = (R : WithTop Int)
    rw [← coe_ordUnit, hDorder, ← ramificationIndex_spec]
    norm_cast
    dsimp [r]
    omega
  have hdenomNe : D + delta ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero] at hdenomOrder
    exact WithTop.top_ne_coe hdenomOrder
  let t := binaryFirstIsotropicShear A D delta
  have htIntegral : t ∈ IntegerRing K := by
    rw [mem_integerRing_iff]
    change 0 ≤ ord K t
    dsimp [t, binaryFirstIsotropicShear]
    rw [div_eq_mul_inv, ord_mul, ord_neg,
      AddValuation.map_inv, hdenomOrder]
    have h := add_le_add_right hx.le (-(R : WithTop Int))
    simpa [add_comm] using h
  let u : V := x + t • y
  have huQuadratic : q.quadratic u = 0 := by
    have hid := binaryFirstIsotropicShear_quadratic_identity
      A C D delta hdisc hdenomNe
    dsimp [u]
    rw [q.quadratic_add, q.quadratic_smul,
      LinearMap.BilinForm.smul_right]
    change A + t ^ 2 * C + 2 * (t * D) = 0
    change A + 2 * t * D + t ^ 2 * C = 0 at hid
    calc
      A + t ^ 2 * C + 2 * (t * D) =
          A + 2 * t * D + t ^ 2 * C := by ring
      _ = 0 := hid
  have huMixed : q.bilin u y = delta := by
    have hid := binaryFirstIsotropicShear_mixed_identity
      A C D delta hdisc hdenomNe
    dsimp [u]
    rw [LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.smul_left]
    change D + t * C = delta
    exact hid
  let k := binarySecondIsotropicShear C delta
  have htwoDeltaOrder : ord K ((2 : K) * delta) =
      (R : WithTop Int) := by
    rw [ord_mul, ← ramificationIndex_spec]
    change (((ramificationIndex K : Int) : WithTop Int) +
      ord K (deltaUnit : K)) = (R : WithTop Int)
    rw [← coe_ordUnit, hdeltaOrder]
    norm_cast
    dsimp [r]
    omega
  have hkIntegral : k ∈ IntegerRing K := by
    rw [mem_integerRing_iff]
    change 0 ≤ ord K k
    dsimp [k, binarySecondIsotropicShear]
    rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv,
      htwoDeltaOrder]
    have h := add_le_add_right hy (-(R : WithTop Int))
    simpa [add_comm] using h
  let v0 : V := y - k • u
  have hvQuadratic : q.quadratic v0 = 0 := by
    have hid := binarySecondIsotropicShear_quadratic_identity
      C delta hdeltaNe
    have hrewrite : v0 = y + (-k) • u := by
      simp only [v0, sub_eq_add_neg, neg_smul]
    rw [hrewrite, q.quadratic_add, q.quadratic_smul,
      LinearMap.BilinForm.smul_right, huQuadratic,
      q.isSymm.eq y u, huMixed]
    change C + (-k) ^ 2 * 0 + 2 * (-k * delta) = 0
    change C - 2 * k * delta = 0 at hid
    calc
      C + (-k) ^ 2 * 0 + 2 * (-k * delta) =
          C - 2 * k * delta := by ring
      _ = 0 := hid
  have huvMixed : q.bilin u v0 = delta := by
    dsimp [v0]
    rw [LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.smul_right]
    change q.bilin u y - k * q.quadratic u = delta
    rw [huMixed, huQuadratic]
    ring
  have hpairLI : LinearIndependent K (binaryPairFamily x y) := by
    rw [linearIndependent_fin2]
    constructor
    · intro hyzero
      change y = 0 at hyzero
      have : D = 0 := by
        dsimp [D]
        rw [hyzero]
        simp
      exact hDne this
    · intro a haxy
      change a • y = x at haxy
      have hAeq : A = a ^ 2 * C := by
        dsimp [A, C]
        rw [← haxy, q.quadratic_smul]
      have hDeq : D = a * C := by
        dsimp [D, C]
        rw [← haxy, LinearMap.BilinForm.smul_left]
        rfl
      have hdetZero : D ^ 2 - A * C = 0 := by
        rw [hAeq, hDeq]
        ring
      have hdeltaSq : delta ^ 2 = 0 := by
        rw [hdisc, hdetZero]
      apply hdeltaNe
      exact (sq_eq_zero_iff).mp (by simpa [pow_two] using hdeltaSq)
  let P := binaryPairSpan (K := K) x y
  have hxP : x ∈ P :=
    Submodule.subset_span ⟨0, by simp [binaryPairFamily]⟩
  have hyP : y ∈ P :=
    Submodule.subset_span ⟨1, by simp [binaryPairFamily]⟩
  let X : P := ⟨x, hxP⟩
  let Y : P := ⟨y, hyP⟩
  have huP : u ∈ P := P.add_mem hxP (P.smul_mem t hyP)
  let U : P := ⟨u, huP⟩
  have hvP : v0 ∈ P := P.sub_mem hyP (P.smul_mem k huP)
  let W : P := ⟨v0, hvP⟩
  have hUeq : U = X + t • Y := by
    apply Subtype.ext
    rfl
  have hWeq : W = Y - k • U := by
    apply Subtype.ext
    rfl
  let pairBasis := binaryPairBasis (K := K) x y hpairLI
  have hpairBasisZero : pairBasis 0 = X := by
    apply Subtype.ext
    simp [pairBasis, X]
  have hpairBasisOne : pairBasis 1 = Y := by
    apply Subtype.ext
    simp [pairBasis, Y]
  have hnondeg : (q.bilin.restrict P).Nondegenerate := by
    apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
      pairBasis).2
    rw [Matrix.det_fin_two]
    simp only [LinearMap.BilinForm.toMatrix_apply]
    rw [hpairBasisZero, hpairBasisOne]
    change q.bilin x x * q.bilin y y -
      q.bilin x y * q.bilin y x ≠ 0
    rw [q.isSymm.eq y x]
    change A * C - D * D ≠ 0
    intro hzero
    have hdetZero : D ^ 2 - A * C = 0 := by
      calc
        D ^ 2 - A * C = -(A * C - D * D) := by ring
        _ = 0 := by rw [hzero]; simp
    have hdeltaSq : delta ^ 2 = 0 := by
      rw [hdisc, hdetZero]
    exact hdeltaNe ((sq_eq_zero_iff).mp
      (by simpa [pow_two] using hdeltaSq))
  let qP := q.restrict P hnondeg
  have hUQuadratic : qP.quadratic U = 0 := huQuadratic
  have hWQuadratic : qP.quadratic W = 0 := hvQuadratic
  have hUWMixed : qP.bilin U W = delta := huvMixed
  let uvFamily : Fin 2 → P := ![U, W]
  have huvLI : LinearIndependent K uvFamily := by
    rw [linearIndependent_fin2]
    constructor
    · intro hWzero
      change W = 0 at hWzero
      have hzero : delta = 0 := by
        rw [← hUWMixed, hWzero]
        simp
      exact hdeltaNe hzero
    · intro a ha
      change a • W = U at ha
      have hzero : delta = 0 := by
        rw [← hUWMixed, ← ha,
          LinearMap.BilinForm.smul_left]
        change a * qP.quadratic W = 0
        rw [hWQuadratic, mul_zero]
      exact hdeltaNe hzero
  have hYeq : Y = W + k • U := by
    apply Subtype.ext
    dsimp [Y, W, U, v0]
    module
  have hXeq : X = U - t • Y := by
    apply Subtype.ext
    dsimp [X, U, Y, u]
    module
  let S := Submodule.span K (Set.range uvFamily)
  have hUmem : U ∈ S :=
    Submodule.subset_span ⟨0, by simp [uvFamily]⟩
  have hWmem : W ∈ S :=
    Submodule.subset_span ⟨1, by simp [uvFamily]⟩
  have hYmem : Y ∈ S := by
    rw [hYeq]
    exact S.add_mem hWmem (S.smul_mem k hUmem)
  have hXmem : X ∈ S := by
    rw [hXeq]
    exact S.sub_mem hUmem (S.smul_mem t hYmem)
  have hspan : (⊤ : Submodule K P) ≤ S := by
    intro z _
    have hz := pairBasis.sum_repr z
    rw [Fin.sum_univ_two] at hz
    rw [hpairBasisZero, hpairBasisOne] at hz
    rw [← hz]
    exact S.add_mem (S.smul_mem _ hXmem) (S.smul_mem _ hYmem)
  let uvBasis : Basis (Fin 2) K P := Module.Basis.mk huvLI hspan
  have huvBasisZero : uvBasis 0 = U := by
    have h : uvBasis 0 = uvFamily 0 := by
      change (Module.Basis.mk huvLI hspan) 0 = uvFamily 0
      exact congrFun (Module.Basis.coe_mk huvLI hspan) 0
    rw [h]
    simp [uvFamily]
  have huvBasisOne : uvBasis 1 = W := by
    have h : uvBasis 1 = uvFamily 1 := by
      change (Module.Basis.mk huvLI hspan) 1 = uvFamily 1
      exact congrFun (Module.Basis.coe_mk huvLI hspan) 1
    rw [h]
    simp [uvFamily]
  have hlattice : Lattice.basisLattice uvBasis =
      Lattice.basisLattice pairBasis := by
    apply Lattice.ext
    change Submodule.span (IntegerRing K) (Set.range uvBasis) =
      Submodule.span (IntegerRing K) (Set.range pairBasis)
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro z ⟨i, rfl⟩
      fin_cases i
      · change uvBasis 0 ∈ Submodule.span (IntegerRing K)
          (Set.range pairBasis)
        rw [huvBasisZero]
        have ht := (Submodule.span (IntegerRing K)
          (Set.range pairBasis)).smul_mem
            (⟨t, htIntegral⟩ : IntegerRing K)
            (Submodule.subset_span ⟨1, rfl⟩)
        change t • pairBasis 1 ∈ _ at ht
        rw [hpairBasisOne] at ht
        have hxmem := Submodule.subset_span
          (R := IntegerRing K) (s := Set.range pairBasis)
          ⟨0, rfl⟩
        rw [hpairBasisZero] at hxmem
        rw [hUeq]
        exact (Submodule.span (IntegerRing K)
          (Set.range pairBasis)).add_mem hxmem ht
      · change uvBasis 1 ∈ Submodule.span (IntegerRing K)
          (Set.range pairBasis)
        rw [huvBasisOne]
        have hkmem := (Submodule.span (IntegerRing K)
          (Set.range pairBasis)).smul_mem
            (⟨k, hkIntegral⟩ : IntegerRing K)
            (show U ∈ Submodule.span (IntegerRing K)
              (Set.range pairBasis) by
                rw [hUeq]
                exact (Submodule.span (IntegerRing K)
                  (Set.range pairBasis)).add_mem
                    (by rw [← hpairBasisZero]
                        exact Submodule.subset_span ⟨0, rfl⟩)
                    (by
                      have ht := (Submodule.span (IntegerRing K)
                        (Set.range pairBasis)).smul_mem
                          (⟨t, htIntegral⟩ : IntegerRing K)
                          (Submodule.subset_span ⟨1, rfl⟩)
                      change t • pairBasis 1 ∈ _ at ht
                      rwa [hpairBasisOne] at ht))
        change k • U ∈ _ at hkmem
        have hymem : Y ∈ Submodule.span (IntegerRing K)
            (Set.range pairBasis) := by
          rw [← hpairBasisOne]
          exact Submodule.subset_span ⟨1, rfl⟩
        rw [hWeq]
        exact (Submodule.span (IntegerRing K)
          (Set.range pairBasis)).sub_mem hymem hkmem
    · rw [Submodule.span_le]
      rintro z ⟨i, rfl⟩
      fin_cases i
      · change pairBasis 0 ∈ Submodule.span (IntegerRing K)
          (Set.range uvBasis)
        rw [hpairBasisZero, hXeq]
        have ht := (Submodule.span (IntegerRing K)
          (Set.range uvBasis)).smul_mem
            (⟨t, htIntegral⟩ : IntegerRing K)
            (show Y ∈ Submodule.span (IntegerRing K)
              (Set.range uvBasis) by
                rw [hYeq]
                exact (Submodule.span (IntegerRing K)
                  (Set.range uvBasis)).add_mem
                    (by rw [← huvBasisOne]
                        exact Submodule.subset_span ⟨1, rfl⟩)
                    (by
                      have hk := (Submodule.span (IntegerRing K)
                        (Set.range uvBasis)).smul_mem
                          (⟨k, hkIntegral⟩ : IntegerRing K)
                          (Submodule.subset_span ⟨0, rfl⟩)
                      change k • uvBasis 0 ∈ _ at hk
                      rwa [huvBasisZero] at hk))
        change t • Y ∈ _ at ht
        exact (Submodule.span (IntegerRing K)
          (Set.range uvBasis)).sub_mem
            (by rw [← huvBasisZero]
                exact Submodule.subset_span ⟨0, rfl⟩) ht
      · change pairBasis 1 ∈ Submodule.span (IntegerRing K)
          (Set.range uvBasis)
        rw [hpairBasisOne, hYeq]
        have hk := (Submodule.span (IntegerRing K)
          (Set.range uvBasis)).smul_mem
            (⟨k, hkIntegral⟩ : IntegerRing K)
            (Submodule.subset_span ⟨0, rfl⟩)
        change k • uvBasis 0 ∈ _ at hk
        rw [huvBasisZero] at hk
        exact (Submodule.span (IntegerRing K)
          (Set.range uvBasis)).add_mem
            (by rw [← huvBasisOne]
                exact Submodule.subset_span ⟨1, rfl⟩) hk
  let piUnit := uniformizerPowerUnit K r
  let lambda : Kˣ := piUnit / deltaUnit
  have hlambdaOrder : ordUnit K lambda = 0 := by
    dsimp [lambda]
    simp only [div_eq_mul_inv, ordUnit_mul, ordUnit_inv]
    rw [hdeltaOrder]
    simp [piUnit]
  let scale : Fin 2 → Kˣ := ![1, lambda]
  let wBasis := uvBasis.unitsSMul scale
  have hscaleUnit : ∀ i, IsValuationUnit K (scale i : K) := by
    intro i
    fin_cases i
    · simp [scale, IsValuationUnit]
    · exact (isValuationUnit_iff_ordUnit_eq_zero (K := K) lambda).2
        hlambdaOrder
  have hwLattice : Lattice.basisLattice wBasis =
      Lattice.basisLattice uvBasis :=
    Lattice.basisLattice_unitsSMul_eq uvBasis scale hscaleUnit
  have hwZero : wBasis 0 = U := by
    change uvBasis.unitsSMul scale 0 = U
    rw [Basis.unitsSMul_apply, huvBasisZero]
    simp [scale]
  have hwOne : wBasis 1 = (lambda : K) • W := by
    change uvBasis.unitsSMul scale 1 = (lambda : K) • W
    rw [Basis.unitsSMul_apply, huvBasisOne]
    rfl
  have hwQuadraticZero : qP.quadratic (wBasis 0) = 0 := by
    rw [hwZero]
    exact hUQuadratic
  have hwQuadraticOne : qP.quadratic (wBasis 1) = 0 := by
    rw [hwOne, qP.quadratic_smul, hWQuadratic, mul_zero]
  have hwMixed : qP.bilin (wBasis 0) (wBasis 1) =
      (piUnit : K) := by
    rw [hwZero, hwOne, LinearMap.BilinForm.smul_right, hUWMixed]
    dsimp [lambda, delta]
    simp
  have hisometric := Lattice.basisLattice_isIsometric_hyperbolicPlane
    qP wBasis piUnit hwQuadraticZero hwQuadraticOne hwMixed
  rw [hwLattice, hlattice] at hisometric
  exact ⟨hpairLI, hnondeg, hisometric⟩

/-- Beli (2003), Lemma 3.19. -/
theorem beliLemma319 [QuadraticDefectLaws K]
    (x y : V) (R : Int)
    (hx : (R : WithTop Int) < ord K (q.quadratic x))
    (hy : (R : WithTop Int) < ord K (q.quadratic y))
    (hsum : ord K (q.quadratic (x + y)) = (R : WithTop Int)) :
    IsScaledHyperbolicPair q x y
      (R - ramificationIndex K) := by
  rcases mixedPairing_order_eq_sub_ramificationIndex
      (q := q) x y R hx hy hsum with ⟨hDne, hDorder⟩
  exact beliLemma319_of_mixedPairing x y R hDne hDorder hx hy.le

end BONG

end Bong
