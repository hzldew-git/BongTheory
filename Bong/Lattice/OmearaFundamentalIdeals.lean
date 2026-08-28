/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaFundamentalInvariants
import Bong.Bong.Beli2009OrthogonalIdealProof

/-!
# O'Meara's fundamental boundary ideals

This file begins the direct formalization of O'Meara 93:20 and 93:26.  It
first proves that the scale of the intrinsic lattice `L^s` at a Jordan scale
is exactly `s`.  Together with O'Meara 93A this shows that equality of
fundamental norm groups and scales also identifies the fundamental weights;
the latter are therefore consequences of `SameFundamentalType`, rather than
additional data.

The final definitions model O'Meara's original ideal

`s_i^2 f_i = sum_{alpha in g_i, beta in g_(i+1)} d(alpha beta)`

with the extra dyadic summand in the even-parity case.  In particular,
`fundamentalIdeal` is not an arbitrary field of a reduction structure.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- Rescaling a lattice by `c` multiplies its scale ideal by `c^2`. -/
theorem scaleIdeal_rescale_eq_scalarIdeal_sq
    (q : QuadraticSpace K V) (L : Lattice K V) (c : Kˣ) :
    scaleIdeal q (rescale c L) =
      scalarIdeal ((c ^ 2 : Kˣ) : K) (scaleIdeal q L) := by
  rw [scaleIdeal, scalarIdeal, scaleIdeal, Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    rcases (mem_rescale_iff c L (p.1 : V)).mp p.1.property with
      ⟨x, hx, hcx⟩
    rcases (mem_rescale_iff c L (p.2 : V)).mp p.2.property with
      ⟨y, hy, hcy⟩
    refine ⟨q.bilin x y, ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩, ?_⟩
    change ((c ^ 2 : Kˣ) : K) * q.bilin x y =
      q.bilin (p.1 : V) (p.2 : V)
    rw [← hcx, ← hcy]
    simp only [LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right, Units.val_mul, pow_two]
    ac_rfl
  · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
    let x : (rescale c L).toSubmodule :=
      ⟨(c : K) • (p.1 : V), smul_mem_rescale c L p.1.property⟩
    let y : (rescale c L).toSubmodule :=
      ⟨(c : K) • (p.2 : V), smul_mem_rescale c L p.2.property⟩
    refine ⟨(x, y), ?_⟩
    simp only [x, y, coefficientMulLinearMap_apply,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      Units.val_mul, pow_two]
    ac_rfl

/-- The intrinsic lattice at the scale of a Jordan component has exactly
that scale ideal. -/
theorem JordanDecomposition.scaleIdeal_scaleTruncation_at_component
    {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}
    (J : JordanDecomposition q L t) (i : Fin t) :
    scaleIdeal q
        (scaleTruncation q L (ordUnit K (J.scaleGenerator i))) =
      powerIdeal (K := K) (ordUnit K (J.scaleGenerator i)) := by
  let r : Int := ordUnit K (J.scaleGenerator i)
  let D := J.scaleTruncationDecomposition r
  rw [D.scaleIdeal_eq_iSup_component]
  change (⨆ j, scaleIdeal (J.component j).space
      (rescale (J.scaleTruncationFactor r j)
        (J.component j).lattice)) = powerIdeal (K := K) r
  have hcomponent : ∀ j : Fin t,
      scaleIdeal (J.component j).space
          (rescale (J.scaleTruncationFactor r j)
            (J.component j).lattice) =
        powerIdeal (K := K)
          (2 * max 0 (r - ordUnit K (J.scaleGenerator j)) +
            ordUnit K (J.scaleGenerator j)) := by
    intro j
    rw [scaleIdeal_rescale_eq_scalarIdeal_sq,
      J.scaleIdeal_eq j, scalarIdeal_principalIdeal_units,
      principalIdeal_eq_powerIdeal]
    congr 1
    rw [ordUnit_mul, ordUnit_pow,
      J.ordUnit_scaleTruncationFactor]
    omega
  simp_rw [hcomponent]
  apply le_antisymm
  · apply iSup_le
    intro j
    apply (powerIdeal_le_iff _ _).2
    omega
  · have hi :
        2 * max 0 (r - ordUnit K (J.scaleGenerator i)) +
            ordUnit K (J.scaleGenerator i) = r := by
      dsimp [r]
      simp
    calc
      powerIdeal (K := K) r =
          powerIdeal (K := K)
            (2 * max 0 (r - ordUnit K (J.scaleGenerator i)) +
              ordUnit K (J.scaleGenerator i)) := by rw [hi]
      _ ≤ ⨆ j : Fin t,
          powerIdeal (K := K)
            (2 * max 0 (r - ordUnit K (J.scaleGenerator j)) +
              ordUnit K (J.scaleGenerator j)) :=
        le_iSup
          (fun j : Fin t ↦
            powerIdeal (K := K)
              (2 * max 0 (r - ordUnit K (J.scaleGenerator j)) +
                ordUnit K (J.scaleGenerator j))) i

variable {W : Type w} [AddCommGroup W] [Module K W]

/-- O'Meara's weight is determined by its norm group and doubled scale. -/
theorem weightIdeal_eq_of_normGroupSet_eq_of_twoScaleIdeal_eq
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {a : Kˣ}
    (ha : IsNormGeneratorValue q L a)
    (hexists : ∃ b : Kˣ, IsNormGeneratorValue r M b)
    (hgroup : normGroupSet q L = normGroupSet r M)
    (htwo : twoScaleIdeal q L = twoScaleIdeal r M) :
    weightIdeal q L = weightIdeal r M := by
  have haM : IsNormGeneratorValue r M a :=
    JordanDecomposition.isNormGeneratorValue_of_normGroupSet_eq
      ha hgroup hexists
  let sourceWeight : OrderedFractionalIdeal K :=
    Beli2009WeightIdealData.weight q L
  have hsourceTwo : twoScaleIdeal q L ≤ sourceWeight.carrier :=
    Beli2009WeightIdealData.twoScale_le_weight q L
  have hsource : SatisfiesWeightIdealConditions q L a sourceWeight :=
    (beli2009Lemma210 a ha sourceWeight hsourceTwo).1 rfl
  have htargetTwo : twoScaleIdeal r M ≤ sourceWeight.carrier := by
    rw [← htwo]
    exact hsourceTwo
  have htarget : SatisfiesWeightIdealConditions r M a sourceWeight := by
    rcases hsource with ⟨hsourceGroup, hbranch⟩
    constructor
    · rw [← hgroup]
      exact hsourceGroup
    · rcases hbranch with hscale | hodd
      · exact Or.inl (hscale.trans htwo)
      · exact Or.inr hodd
  have hweight :=
    (beli2009Lemma210 a haM sourceWeight htargetTwo).2 htarget
  simpa only [sourceWeight, weightIdeal] using hweight

/-- Multiplication of a coefficient ideal by two nonzero scalars of the same
valuation gives the same coefficient ideal. -/
theorem scalarIdeal_units_eq_of_ordUnit_eq
    (a b : Kˣ) (I : CoefficientIdeal (K := K))
    (hord : ordUnit K a = ordUnit K b) :
    scalarIdeal (a : K) I = scalarIdeal (b : K) I := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    let u : Kˣ := b⁻¹ * a
    have huOrder : ordUnit K u = 0 := by
      dsimp [u]
      rw [ordUnit_mul, ordUnit_inv, hord]
      omega
    have huIntegral : (u : K) ∈ IntegerRing K := by
      rw [mem_integerRing_iff, Dyadic.IsIntegral, ← coe_ordUnit, huOrder]
      simp
    let uO : IntegerRing K := ⟨(u : K), huIntegral⟩
    refine ⟨uO • x, I.smul_mem uO hx, ?_⟩
    simp only [coefficientMulLinearMap_apply, Algebra.smul_def]
    change (b : K) * ((uO : K) * x) = (a : K) * x
    change (b : K) * ((u : K) * x) = (a : K) * x
    dsimp [u]
    simp only [Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero b]
  · rintro _ ⟨x, hx, rfl⟩
    let u : Kˣ := a⁻¹ * b
    have huOrder : ordUnit K u = 0 := by
      dsimp [u]
      rw [ordUnit_mul, ordUnit_inv, hord]
      omega
    have huIntegral : (u : K) ∈ IntegerRing K := by
      rw [mem_integerRing_iff, Dyadic.IsIntegral, ← coe_ordUnit, huOrder]
      simp
    let uO : IntegerRing K := ⟨(u : K), huIntegral⟩
    refine ⟨uO • x, I.smul_mem uO hx, ?_⟩
    simp only [coefficientMulLinearMap_apply, Algebra.smul_def]
    change (a : K) * ((uO : K) * x) = (b : K) * x
    change (a : K) * ((u : K) * x) = (b : K) * x
    dsimp [u]
    simp only [Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero a]

namespace JordanDecomposition.SameFundamentalType

variable {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {s t : Nat}
  {J : JordanDecomposition q L t} {H : JordanDecomposition r M s}

/-- When both decompositions are indexed by the same finite ordinal, the
order-preserving index equivalence fixes every index. -/
theorem indexEquiv_apply_eq_self
    {n : Nat} {J : JordanDecomposition q L n}
    {H : JordanDecomposition r M n}
    (F : JordanDecomposition.SameFundamentalType J H) (i : Fin n) :
    F.indexEquiv i = i := by
  apply Fin.ext
  exact F.index_val i

/-- Equal fundamental type identifies the orders of the independently
chosen fundamental norm generators. -/
theorem fundamentalNormGenerator_order_eq
    (F : JordanDecomposition.SameFundamentalType J H) (i : Fin t) :
    ordUnit K (H.fundamentalNormGenerator (F.indexEquiv i)) =
      ordUnit K (J.fundamentalNormGenerator i) := by
  have hcommon := F.fundamentalNormGenerator_spec_right i
  have hown := H.fundamentalNormGenerator_spec (F.indexEquiv i)
  apply (principalIdeal_eq_iff_ordUnit_eq
    (H.fundamentalNormGenerator (F.indexEquiv i))
    (J.fundamentalNormGenerator i)).mp
  exact hown.2.symm.trans hcommon.2

/-- Equal fundamental type also identifies all fundamental weight ideals. -/
theorem fundamentalWeightIdeal_eq
    (F : JordanDecomposition.SameFundamentalType J H) (i : Fin t) :
    H.fundamentalWeightIdeal (F.indexEquiv i) =
      J.fundamentalWeightIdeal i := by
  have htwo : twoScaleIdeal q (J.fundamentalLattice i) =
      twoScaleIdeal r (H.fundamentalLattice (F.indexEquiv i)) := by
    unfold twoScaleIdeal
    congr 1
    unfold fundamentalLattice fundamentalScaleOrder
    rw [J.scaleIdeal_scaleTruncation_at_component,
      H.scaleIdeal_scaleTruncation_at_component]
    have hs := F.scaleOrder_eq i
    change ordUnit K (H.scaleGenerator (F.indexEquiv i)) =
      ordUnit K (J.scaleGenerator i) at hs
    rw [hs]
  apply (weightIdeal_eq_of_normGroupSet_eq_of_twoScaleIdeal_eq
    (J.fundamentalNormGenerator_spec i)
    (H.exists_fundamentalNormGenerator (F.indexEquiv i))
    (F.normGroup_eq i).symm htwo).symm

/-- Equal fundamental type identifies the integral orders of the fundamental
weight ideals as well. -/
theorem fundamentalWeightOrder_eq
    (F : JordanDecomposition.SameFundamentalType J H) (i : Fin t) :
    H.fundamentalWeightOrder (F.indexEquiv i) =
      J.fundamentalWeightOrder i := by
  unfold fundamentalWeightOrder
  apply powerIdeal_order_eq_of_eq (K := K)
  rw [← weightIdeal_eq_powerIdeal, ← weightIdeal_eq_powerIdeal]
  simpa only [fundamentalWeightIdeal] using F.fundamentalWeightIdeal_eq i

end JordanDecomposition.SameFundamentalType

/-! ## The original definition of the boundary ideals in O'Meara 93:20 -/

/-- The absolute quadratic-defect ideal of a scalar, with zero assigned the
zero ideal.  This extension lets us sum `d(alpha beta)` over norm groups,
which contain zero. -/
noncomputable def scalarQuadraticDefectIdeal (x : K) :
    CoefficientIdeal (K := K) := by
  classical
  exact if hx : x = 0 then ⊥
    else quadraticDefectIdeal (Units.mk0 x hx)

@[simp]
theorem scalarQuadraticDefectIdeal_zero :
    scalarQuadraticDefectIdeal (K := K) 0 = ⊥ := by
  simp [scalarQuadraticDefectIdeal]

theorem scalarQuadraticDefectIdeal_eq_quadraticDefectIdeal
    (x : Kˣ) :
    scalarQuadraticDefectIdeal (K := K) (x : K) =
      quadraticDefectIdeal x := by
  simp only [scalarQuadraticDefectIdeal, Units.ne_zero, dite_false]
  congr 1
  apply Units.ext
  rfl

/-- An absolute quadratic-defect ideal is contained in the principal ideal
of its scalar. -/
theorem quadraticDefectIdeal_le_principalIdeal (a : Kˣ) :
    quadraticDefectIdeal a ≤ principalIdeal (K := K) (a : K) := by
  by_cases htop : quadraticDefect K a = ⊤
  · simp [quadraticDefectIdeal, htop]
  · rw [quadraticDefectIdeal, if_neg htop,
      principalIdeal_eq_powerIdeal, powerIdeal_le_iff]
    have hd : 0 ≤ Int.ofNat (quadraticDefect K a).toNat := by
      exact Int.natCast_nonneg _
    omega

/-- The absolute quadratic-defect ideal is contained in the principal
ideal of every square-approximation error `a - x²`.  Equivalently, the
absolute defect ideal is the greatest common divisor of all such errors.
This is the ideal-valued approximation lemma used in the even branch of
O'Meara 93:26. -/
theorem quadraticDefectIdeal_le_principalIdeal_sub_sq
    (a : Kˣ) (x : K) :
    quadraticDefectIdeal a ≤
      principalIdeal (K := K) ((a : K) - x ^ 2) := by
  by_cases herror : (a : K) - x ^ 2 = 0
  · have hx : x ≠ 0 := by
      intro hx
      rw [hx] at herror
      simp at herror
    let xu : Kˣ := Units.mk0 x hx
    have haSquare : IsSquare a := by
      refine ⟨xu, Units.ext ?_⟩
      change (a : K) = x * x
      rw [pow_two] at herror
      exact sub_eq_zero.mp herror
    have htop : quadraticDefect K a = ⊤ :=
      quadraticDefect_eq_top_of_isSquare K haSquare
    simp [quadraticDefectIdeal, htop, herror]
  · let error : Kˣ := Units.mk0 ((a : K) - x ^ 2) herror
    change quadraticDefectIdeal a ≤
      principalIdeal (K := K) (error : K)
    rw [principalIdeal_eq_powerIdeal]
    by_cases htop : quadraticDefect K a = ⊤
    · simp [quadraticDefectIdeal, htop]
    · rw [quadraticDefectIdeal, if_neg htop, powerIdeal_le_iff]
      by_cases hsmall : ordUnit K error ≤ ordUnit K a
      · have hdnonneg :
            0 ≤ Int.ofNat (quadraticDefect K a).toNat := by
          exact Int.natCast_nonneg _
        omega
      · have haLe : ordUnit K a ≤ ordUnit K error :=
          le_of_not_ge hsmall
        let k : Nat := Int.toNat (ordUnit K error - ordUnit K a)
        have hkInt : (k : Int) = ordUnit K error - ordUnit K a := by
          exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr haLe)
        have herrorOrder :
            ord K ((a : K) - x ^ 2) =
              (ordUnit K error : WithTop Int) := by
          change ord K (error : K) = _
          rw [← coe_ordUnit]
        have happrox : (k : ℕ∞) ≤ quadraticDefect K a := by
          apply quadraticDefect_ge_of_absolute_square_approximation
            K a x (ordUnit K a) k rfl
          rw [herrorOrder]
          exact_mod_cast (show ordUnit K a + (k : Int) ≤
              ordUnit K error by omega)
        rw [← ENat.coe_toNat htop] at happrox
        have hkNat : k ≤ (quadraticDefect K a).toNat := by
          exact_mod_cast happrox
        change ordUnit K error ≤ ordUnit K a +
          ((quadraticDefect K a).toNat : Int)
        omega

/-- Some square approximation realizes an error in the absolute
quadratic-defect ideal.  In the finite case we use attainment of the
relative defect; in the square case the error is zero. -/
theorem exists_sub_sq_mem_quadraticDefectIdeal (a : Kˣ) :
    ∃ x : K, (a : K) - x ^ 2 ∈ quadraticDefectIdeal a := by
  by_cases htop : quadraticDefect K a = ⊤
  · rcases (quadraticDefect_eq_top_iff_isSquare (K := K) a).mp htop with
      ⟨s, hs⟩
    refine ⟨(s : K), ?_⟩
    have hsval : (a : K) = (s : K) ^ 2 := by
      have h := congrArg Units.val hs
      simpa only [Units.val_mul, pow_two] using h
    simp [quadraticDefectIdeal, htop, hsval]
  · rcases BONG.exists_quadraticApproximation_exact_order a htop with
      ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [quadraticDefectIdeal, if_neg htop, mem_powerIdeal_iff]
    have hfactor :
        (a : K) - x ^ 2 =
          (a : K) * (1 - x ^ 2 / (a : K)) := by
      field_simp [Units.ne_zero a]
    rw [hfactor, ord_mul, ← coe_ordUnit, hx]
    norm_cast

/-- A scalar of odd valuation has absolute defect equal to its principal
ideal. -/
theorem quadraticDefectIdeal_eq_principalIdeal_of_odd
    (a : Kˣ) (hodd : Odd (ordUnit K a)) :
    quadraticDefectIdeal a = principalIdeal (K := K) (a : K) := by
  have hzero := quadraticDefect_eq_zero_of_odd_ordUnit (K := K) a hodd
  simp [quadraticDefectIdeal, hzero, principalIdeal_eq_powerIdeal]

/-- The ideal sum of all defects `d(alpha beta)` with `alpha in A` and
`beta in B`. -/
noncomputable def productDefectSum (A B : Set K) :
    CoefficientIdeal (K := K) :=
  ⨆ (a : A) (b : B), scalarQuadraticDefectIdeal (a.1 * b.1)

/-- The sum of all product defects is symmetric in the two scalar sets. -/
theorem productDefectSum_comm (A B : Set K) :
    productDefectSum A B = productDefectSum B A := by
  unfold productDefectSum
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro y
    have hcomm : scalarQuadraticDefectIdeal (x.1 * y.1) =
        scalarQuadraticDefectIdeal (y.1 * x.1) := by rw [mul_comm]
    rw [hcomm]
    exact le_trans (le_iSup (fun z : A ↦
      scalarQuadraticDefectIdeal (y.1 * z.1)) x)
      (le_iSup (fun z : B ↦
        ⨆ w : A, scalarQuadraticDefectIdeal (z.1 * w.1)) y)
  · apply iSup_le
    intro x
    apply iSup_le
    intro y
    have hcomm : scalarQuadraticDefectIdeal (x.1 * y.1) =
        scalarQuadraticDefectIdeal (y.1 * x.1) := by rw [mul_comm]
    rw [hcomm]
    exact le_trans (le_iSup (fun z : B ↦
      scalarQuadraticDefectIdeal (y.1 * z.1)) x)
      (le_iSup (fun z : A ↦
        ⨆ w : B, scalarQuadraticDefectIdeal (z.1 * w.1)) y)

/-- Multiplying two integral-square cosets gives the upper half of
O'Meara's even 93:26 formula.  The defect of every product is absorbed by
`d(ab) + a wB + b wA`.

The containment of `wA` in `aO` absorbs the quadratic error term `xy`;
the symmetric hypothesis is retained because it is the natural norm-ideal
hypothesis and is used by the symmetric applications below. -/
theorem productDefectSum_integralSquareCoset_le
    (a b : Kˣ) (wA wB : CoefficientIdeal (K := K))
    (hA : wA ≤ principalIdeal (K := K) (a : K))
    (_hB : wB ≤ principalIdeal (K := K) (b : K)) :
    productDefectSum
        (integralSquareCoset (a : K) wA)
        (integralSquareCoset (b : K) wB) ≤
      (quadraticDefectIdeal (a * b) ⊔
        scalarIdeal (a : K) wB) ⊔
        scalarIdeal (b : K) wA := by
  let T : CoefficientIdeal (K := K) :=
    (quadraticDefectIdeal (a * b) ⊔ scalarIdeal (a : K) wB) ⊔
      scalarIdeal (b : K) wA
  change productDefectSum
      (integralSquareCoset (a : K) wA)
      (integralSquareCoset (b : K) wB) ≤ T
  apply iSup_le
  intro alpha
  apply iSup_le
  intro beta
  by_cases hzero : (alpha.1 : K) * beta.1 = 0
  · simp [scalarQuadraticDefectIdeal, hzero]
  · let product : Kˣ := Units.mk0 (alpha.1 * beta.1) hzero
    have hdefect : scalarQuadraticDefectIdeal (alpha.1 * beta.1) =
        quadraticDefectIdeal product := by
      change scalarQuadraticDefectIdeal (product : K) = _
      exact scalarQuadraticDefectIdeal_eq_quadraticDefectIdeal product
    rw [hdefect]
    rcases alpha.2 with ⟨c, x, hx, halpha⟩
    rcases beta.2 with ⟨d, y, hy, hbeta⟩
    rcases exists_sub_sq_mem_quadraticDefectIdeal (a * b) with
      ⟨s, hs⟩
    apply (quadraticDefectIdeal_le_principalIdeal_sub_sq
      product (s * (c : K) * (d : K))).trans
    rw [principalIdeal, Submodule.span_singleton_le_iff_mem]
    have hbase :
        ((a * b : Kˣ) : K) - s ^ 2 ∈ quadraticDefectIdeal (a * b) := hs
    have hbaseScaled :
        (((a * b : Kˣ) : K) - s ^ 2) *
            (c : K) ^ 2 * (d : K) ^ 2 ∈
          quadraticDefectIdeal (a * b) := by
      have h := (quadraticDefectIdeal (a * b)).smul_mem
        ((c ^ 2) * (d ^ 2)) hbase
      change (((c ^ 2) * (d ^ 2) : IntegerRing K) : K) *
          (((a * b : Kˣ) : K) - s ^ 2) ∈
        quadraticDefectIdeal (a * b) at h
      have hcoe : (((c ^ 2) * (d ^ 2) : IntegerRing K) : K) =
          (c : K) ^ 2 * (d : K) ^ 2 := by norm_cast
      rw [hcoe] at h
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h
    have hAy : (a : K) * (c : K) ^ 2 * y ∈
        scalarIdeal (a : K) wB := by
      refine ⟨(c ^ 2) • y, wB.smul_mem (c ^ 2) hy, ?_⟩
      simp only [coefficientMulLinearMap_apply, Algebra.smul_def]
      rw [map_pow]
      have hcCoe : algebraMap (IntegerRing K) K c = (c : K) := rfl
      rw [hcCoe]
      ring
    have hBx : (b : K) * (d : K) ^ 2 * x ∈
        scalarIdeal (b : K) wA := by
      refine ⟨(d ^ 2) • x, wA.smul_mem (d ^ 2) hx, ?_⟩
      simp only [coefficientMulLinearMap_apply, Algebra.smul_def]
      rw [map_pow]
      have hdCoe : algebraMap (IntegerRing K) K d = (d : K) := rfl
      rw [hdCoe]
      ring
    have hxPrincipal : x ∈ principalIdeal (K := K) (a : K) := hA hx
    rw [principalIdeal, Submodule.mem_span_singleton] at hxPrincipal
    rcases hxPrincipal with ⟨z, hz⟩
    have hxy : x * y ∈ scalarIdeal (a : K) wB := by
      refine ⟨z • y, wB.smul_mem z hy, ?_⟩
      simp only [coefficientMulLinearMap_apply, Algebra.smul_def]
      have hxEq : x = algebraMap (IntegerRing K) K z * (a : K) := by
        simpa only [Algebra.smul_def] using hz.symm
      rw [hxEq]
      ring
    have hQFirst : quadraticDefectIdeal (a * b) ≤
        quadraticDefectIdeal (a * b) ⊔ scalarIdeal (a : K) wB := by
      exact _root_.le_sup_left
    have hFirstT :
        quadraticDefectIdeal (a * b) ⊔ scalarIdeal (a : K) wB ≤ T := by
      exact _root_.le_sup_left
    have hAyFirst : scalarIdeal (a : K) wB ≤
        quadraticDefectIdeal (a * b) ⊔ scalarIdeal (a : K) wB := by
      exact _root_.le_sup_right
    have hBxTIncl : scalarIdeal (b : K) wA ≤ T := by
      exact _root_.le_sup_right
    have hbaseT :
        (((a * b : Kˣ) : K) - s ^ 2) *
            (c : K) ^ 2 * (d : K) ^ 2 ∈ T :=
      hFirstT (hQFirst hbaseScaled)
    have hAyT : (a : K) * (c : K) ^ 2 * y ∈ T :=
      hFirstT (hAyFirst hAy)
    have hBxT : (b : K) * (d : K) ^ 2 * x ∈ T :=
      hBxTIncl hBx
    have hxyT : x * y ∈ T :=
      hFirstT (hAyFirst hxy)
    have hsum :
        (((a * b : Kˣ) : K) - s ^ 2) *
              (c : K) ^ 2 * (d : K) ^ 2 +
            (a : K) * (c : K) ^ 2 * y +
          (b : K) * (d : K) ^ 2 * x + x * y ∈ T :=
      T.add_mem (T.add_mem (T.add_mem hbaseT hAyT) hBxT) hxyT
    change alpha.1 * beta.1 - (s * (c : K) * (d : K)) ^ 2 ∈ T
    rw [halpha, hbeta]
    change ((a : K) * (b : K) - s ^ 2) *
              (c : K) ^ 2 * (d : K) ^ 2 +
            (a : K) * (c : K) ^ 2 * y +
          (b : K) * (d : K) ^ 2 * x + x * y ∈ T at hsum
    convert hsum using 1 <;> ring

/-- The defect of a distinguished product is one of the summands in the
sum of all product defects. -/
theorem quadraticDefectIdeal_product_le_productDefectSum
    {A B : Set K} (a b : Kˣ)
    (ha : (a : K) ∈ A) (hb : (b : K) ∈ B) :
    quadraticDefectIdeal (a * b) ≤ productDefectSum A B := by
  let alpha : A := ⟨(a : K), ha⟩
  let beta : B := ⟨(b : K), hb⟩
  have hterm : scalarQuadraticDefectIdeal (alpha.1 * beta.1) ≤
      productDefectSum A B :=
    le_trans (le_iSup (fun y : B ↦
      scalarQuadraticDefectIdeal (alpha.1 * y.1)) beta)
      (le_iSup (fun x : A ↦
        ⨆ y : B, scalarQuadraticDefectIdeal (x.1 * y.1)) alpha)
  calc
    quadraticDefectIdeal (a * b) =
        scalarQuadraticDefectIdeal (alpha.1 * beta.1) := by
      symm
      change scalarQuadraticDefectIdeal (((a * b : Kˣ) : K)) = _
      exact scalarQuadraticDefectIdeal_eq_quadraticDefectIdeal (a * b)
    _ ≤ productDefectSum A B := hterm

/-- If a product of distinguished elements has odd valuation, its defect
already generates the corresponding scaled principal ideal. -/
theorem scalarIdeal_le_productDefectSum_of_odd
    {A B : Set K} (a g : Kˣ)
    (ha : (a : K) ∈ A) (hg : (g : K) ∈ B)
    (hodd : Odd (ordUnit K a + ordUnit K g)) :
    scalarIdeal (a : K) (principalIdeal (K := K) (g : K)) ≤
      productDefectSum A B := by
  calc
    scalarIdeal (a : K) (principalIdeal (K := K) (g : K)) =
        principalIdeal (K := K) ((a * g : Kˣ) : K) :=
      scalarIdeal_principalIdeal_units a g
    _ = quadraticDefectIdeal (a * g) :=
      (quadraticDefectIdeal_eq_principalIdeal_of_odd
        (a * g) (by simpa only [ordUnit_mul] using hodd)).symm
    _ ≤ productDefectSum A B :=
      quadraticDefectIdeal_product_le_productDefectSum a g ha hg

/-- O'Meara 93:26 in the odd norm-order case.  Every product defect is
contained in `ab O`, while the chosen norm generators themselves attain
that ideal because `ord(ab)` is odd. -/
theorem productDefectSum_eq_principalIdeal_of_odd
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W}
    (a b : Kˣ) (ha : IsNormGeneratorValue q L a)
    (hb : IsNormGeneratorValue r M b)
    (hodd : Odd (ordUnit K a + ordUnit K b)) :
    productDefectSum (normGroupSet q L) (normGroupSet r M) =
      principalIdeal (K := K) ((a * b : Kˣ) : K) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro y
    by_cases hx : (x.1 : K) = 0
    · simp [scalarQuadraticDefectIdeal, hx]
    by_cases hy : (y.1 : K) = 0
    · simp [scalarQuadraticDefectIdeal, hy]
    let xu : Kˣ := Units.mk0 x.1 hx
    let yu : Kˣ := Units.mk0 y.1 hy
    have hxIdeal : (x.1 : K) ∈ normIdeal q L :=
      normGroupSet_subset_normIdeal q L x.2
    have hyIdeal : (y.1 : K) ∈ normIdeal r M :=
      normGroupSet_subset_normIdeal r M y.2
    have hax : ordUnit K a ≤ ordUnit K xu := by
      rw [ha.2, principalIdeal_eq_powerIdeal,
        mem_powerIdeal_iff] at hxIdeal
      change ((ordUnit K a : Int) : WithTop Int) ≤
        ord K (xu : K) at hxIdeal
      rw [← coe_ordUnit] at hxIdeal
      exact WithTop.coe_le_coe.mp hxIdeal
    have hby : ordUnit K b ≤ ordUnit K yu := by
      rw [hb.2, principalIdeal_eq_powerIdeal,
        mem_powerIdeal_iff] at hyIdeal
      change ((ordUnit K b : Int) : WithTop Int) ≤
        ord K (yu : K) at hyIdeal
      rw [← coe_ordUnit] at hyIdeal
      exact WithTop.coe_le_coe.mp hyIdeal
    have hdefect : scalarQuadraticDefectIdeal (x.1 * y.1) =
        quadraticDefectIdeal (xu * yu) := by
      change scalarQuadraticDefectIdeal ((xu : K) * (yu : K)) = _
      rw [← Units.val_mul]
      exact scalarQuadraticDefectIdeal_eq_quadraticDefectIdeal (xu * yu)
    rw [hdefect]
    exact (quadraticDefectIdeal_le_principalIdeal (xu * yu)).trans <| by
      rw [principalIdeal_eq_powerIdeal, principalIdeal_eq_powerIdeal,
        powerIdeal_le_iff, ordUnit_mul, ordUnit_mul]
      omega
  · have haGroup : (a : K) ∈ normGroupSet q L := ha.1
    have hbGroup : (b : K) ∈ normGroupSet r M := hb.1
    let x : normGroupSet q L := ⟨(a : K), haGroup⟩
    let y : normGroupSet r M := ⟨(b : K), hbGroup⟩
    have hxy : scalarQuadraticDefectIdeal (x.1 * y.1) ≤
        productDefectSum (normGroupSet q L) (normGroupSet r M) :=
      le_trans (le_iSup (fun z : normGroupSet r M ↦
        scalarQuadraticDefectIdeal (x.1 * z.1)) y)
        (le_iSup (fun z : normGroupSet q L ↦
          ⨆ w : normGroupSet r M,
            scalarQuadraticDefectIdeal (z.1 * w.1)) x)
    have hproductOdd : Odd (ordUnit K (a * b)) := by
      simpa only [ordUnit_mul] using hodd
    calc
      principalIdeal (K := K) ((a * b : Kˣ) : K) =
          quadraticDefectIdeal (a * b) :=
        (quadraticDefectIdeal_eq_principalIdeal_of_odd
          (a * b) hproductOdd).symm
      _ = scalarQuadraticDefectIdeal (x.1 * y.1) := by
        symm
        change scalarQuadraticDefectIdeal (((a * b : Kˣ) : K)) = _
        exact scalarQuadraticDefectIdeal_eq_quadraticDefectIdeal (a * b)
      _ ≤ productDefectSum (normGroupSet q L) (normGroupSet r M) := hxy

/-- A selected weight ideal is contained in the principal norm ideal. -/
theorem weightIdeal_le_principalIdeal
    {q : QuadraticSpace K V} {L : Lattice K V}
    (a : Kˣ) (ha : IsNormGeneratorValue q L a) :
    weightIdeal q L ≤ principalIdeal (K := K) (a : K) := by
  rw [weightIdeal_eq_powerIdeal, principalIdeal_eq_powerIdeal,
    powerIdeal_le_iff]
  exact normGeneratorOrder_le_weightIdealOrder a ha

/-- Every element of the selected weight ideal belongs to the norm group. -/
theorem weightIdeal_subset_normGroupSet
    {q : QuadraticSpace K V} {L : Lattice K V}
    (a : Kˣ) (ha : IsNormGeneratorValue q L a) :
    (weightIdeal q L : Set K) ⊆ normGroupSet q L := by
  rw [weightIdeal_eq_canonicalWeightIdeal a ha]
  exact canonicalWeightIdeal_subset_normGroupSet ha

/-- The selected weight satisfies O'Meara's `2s`/odd alternative. -/
theorem weightIdeal_eq_twoScale_or_odd
    {q : QuadraticSpace K V} {L : Lattice K V}
    (a : Kˣ) (ha : IsNormGeneratorValue q L a) :
    weightIdeal q L = twoScaleIdeal q L ∨
      Odd (ordUnit K a + weightIdealOrder q L) := by
  have hconditions := (beli2009Lemma210 a ha
    (Beli2009WeightIdealData.weight q L)
    (twoScaleIdeal_le_weightIdeal q L)).mp rfl
  exact hconditions.2

namespace JordanDecomposition

variable {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- The chosen fundamental norm generator has the effective Jordan norm
order at its scale. -/
theorem fundamentalNormGenerator_order_eq_effective
    (J : JordanDecomposition q L t) (i : Fin t) :
    ordUnit K (J.fundamentalNormGenerator i) =
      BONG.jordanEffectiveNormOrder J i := by
  have hgenerator := J.fundamentalNormGenerator_spec i
  apply powerIdeal_order_eq_of_eq (K := K)
  calc
    powerIdeal (K := K) (ordUnit K (J.fundamentalNormGenerator i)) =
        principalIdeal (K := K) (J.fundamentalNormGenerator i : K) :=
      (principalIdeal_eq_powerIdeal (J.fundamentalNormGenerator i)).symm
    _ = normIdeal q (J.fundamentalLattice i) := hgenerator.2.symm
    _ = powerIdeal (K := K) (BONG.jordanEffectiveNormOrder J i) := by
      exact J.normIdeal_scaleTruncation_eq_powerIdeal i
        (J.fundamentalScaleOrder i)

/-- O'Meara 93:25, first inequality: fundamental norm orders are
nondecreasing with the fundamental scale. -/
theorem fundamentalNormGenerator_order_mono
    (J : JordanDecomposition q L t) {i j : Fin t} (hij : i ≤ j) :
    ordUnit K (J.fundamentalNormGenerator i) ≤
      ordUnit K (J.fundamentalNormGenerator j) := by
  rw [J.fundamentalNormGenerator_order_eq_effective i,
    J.fundamentalNormGenerator_order_eq_effective j]
  unfold BONG.jordanEffectiveNormOrder BONG.jordanEffectiveNormOrderAt
  apply JordanProfileOrder.effectiveAt_mono_target
  by_cases hEq : i = j
  · subst j
    exact le_rfl
  · exact (J.scaleOrder_strict (lt_of_le_of_ne hij hEq)).le

/-- O'Meara 93:25, dual inequality: `u_j - 2s_j` is nonincreasing. -/
theorem fundamentalNormGenerator_order_sub_two_scale_anti
    (J : JordanDecomposition q L t) {i j : Fin t} (hij : i ≤ j) :
    ordUnit K (J.fundamentalNormGenerator j) -
        2 * J.fundamentalScaleOrder j ≤
      ordUnit K (J.fundamentalNormGenerator i) -
        2 * J.fundamentalScaleOrder i := by
  rw [J.fundamentalNormGenerator_order_eq_effective i,
    J.fundamentalNormGenerator_order_eq_effective j]
  have hscale : J.fundamentalScaleOrder i ≤
      J.fundamentalScaleOrder j := by
    unfold fundamentalScaleOrder
    by_cases hEq : i = j
    · subst j
      exact le_rfl
    · exact (J.scaleOrder_strict (lt_of_le_of_ne hij hEq)).le
  have hbound := JordanProfileOrder.effectiveAt_target_le_add_two_mul_sub
    (fun k : Fin t ↦ ordUnit K (J.scaleGenerator k))
    (fun k : Fin t ↦ ordUnit K (J.normGenerator k)) i j hscale
  unfold BONG.jordanEffectiveNormOrder BONG.jordanEffectiveNormOrderAt
  unfold fundamentalScaleOrder at hscale hbound ⊢
  omega

/-- The doubled scale of the intrinsic lattice at a fundamental scale is
the power ideal of order `s_i + e`. -/
theorem fundamentalTwoScaleIdeal_eq_powerIdeal
    (J : JordanDecomposition q L t) (i : Fin t) :
    twoScaleIdeal q (J.fundamentalLattice i) =
      powerIdeal (K := K)
        (J.fundamentalScaleOrder i + ramificationIndex K) := by
  unfold twoScaleIdeal fundamentalLattice fundamentalScaleOrder
  rw [J.scaleIdeal_scaleTruncation_at_component,
    twiceIdeal_powerIdeal]

/-- The left fundamental index at boundary `i` of a decomposition with
`t+1` components. -/
def boundaryLeftIndex (i : Fin t) : Fin (t + 1) := i.castSucc

/-- The right fundamental index at boundary `i` of a decomposition with
`t+1` components. -/
def boundaryRightIndex (i : Fin t) : Fin (t + 1) := i.succ

/-- The left endpoint of a fundamental boundary precedes its right
endpoint. -/
theorem boundaryLeftIndex_le_rightIndex (i : Fin t) :
    boundaryLeftIndex i ≤ boundaryRightIndex i := by
  apply Fin.le_iff_val_le_val.mpr
  simp [boundaryLeftIndex, boundaryRightIndex]

/-- The norm-order sum `u_i + u_(i+1)` at a fundamental boundary. -/
noncomputable def boundaryNormOrderSum
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) : Int :=
  ordUnit K (J.fundamentalNormGenerator (boundaryLeftIndex i)) +
    ordUnit K (J.fundamentalNormGenerator (boundaryRightIndex i))

/-- The unscaled defect sum in O'Meara's definition of `f_i`. -/
noncomputable def boundaryProductDefectSum
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) :
    CoefficientIdeal (K := K) :=
  productDefectSum
    (J.fundamentalNormGroup (boundaryLeftIndex i))
    (J.fundamentalNormGroup (boundaryRightIndex i))

/-- The extra dyadic term in the even-parity definition of `f_i`. -/
noncomputable def boundaryParityIdeal
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) :
    CoefficientIdeal (K := K) :=
  twiceIdeal (powerIdeal (K := K)
    (J.boundaryNormOrderSum i / 2 +
      J.fundamentalScaleOrder (boundaryLeftIndex i)))

/-- O'Meara's original definition of `s_i^2 f_i` (93:20). -/
noncomputable def scaledFundamentalIdeal
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) :
    CoefficientIdeal (K := K) := by
  classical
  exact if Even (J.boundaryNormOrderSum i) then
      J.boundaryProductDefectSum i ⊔ J.boundaryParityIdeal i
    else J.boundaryProductDefectSum i

/-- O'Meara's fundamental boundary ideal `f_i`. -/
noncomputable def fundamentalIdeal
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) :
    CoefficientIdeal (K := K) :=
  scalarIdeal
    (((J.scaleGenerator (boundaryLeftIndex i))⁻¹ ^ 2 : Kˣ) : K)
    (J.scaledFundamentalIdeal i)

/-- In the even boundary case, the right cross ideal `a_i w_(i+1)` is
already generated by product defects, unless the right weight is `2s`; in
that exceptional branch 93:25 places it in the extra dyadic boundary
ideal. -/
theorem rightCrossIdeal_le_productDefect_sup_parity_of_even
    (J : JordanDecomposition q L (t + 1)) (i : Fin t)
    (heven : Even (J.boundaryNormOrderSum i)) :
    scalarIdeal
        (J.fundamentalNormGenerator (boundaryLeftIndex i) : K)
        (J.fundamentalWeightIdeal (boundaryRightIndex i)) ≤
      J.boundaryProductDefectSum i ⊔ J.boundaryParityIdeal i := by
  let li : Fin (t + 1) := boundaryLeftIndex i
  let ri : Fin (t + 1) := boundaryRightIndex i
  let a : Kˣ := J.fundamentalNormGenerator li
  let b : Kˣ := J.fundamentalNormGenerator ri
  have ha := J.fundamentalNormGenerator_spec li
  have hb := J.fundamentalNormGenerator_spec ri
  rcases weightIdeal_eq_twoScale_or_odd b hb with htwo | hodd
  · have hdual := J.fundamentalNormGenerator_order_sub_two_scale_anti
        (i := li) (j := ri) (boundaryLeftIndex_le_rightIndex i)
    change scalarIdeal (a : K)
      (weightIdeal q (J.fundamentalLattice ri)) ≤ _
    rw [htwo, J.fundamentalTwoScaleIdeal_eq_powerIdeal,
      scalarIdeal_powerIdeal_units]
    apply le_trans ?_ _root_.le_sup_right
    unfold boundaryParityIdeal
    rw [twiceIdeal_powerIdeal, powerIdeal_le_iff]
    dsimp only [a, b, li, ri] at hdual ⊢
    unfold boundaryNormOrderSum at heven ⊢
    unfold fundamentalScaleOrder at hdual ⊢
    rcases heven with ⟨m, hm⟩
    omega
  · let g : Kˣ := uniformizerPowerUnit K
      (weightIdealOrder q (J.fundamentalLattice ri))
    have hw : J.fundamentalWeightIdeal ri =
        principalIdeal (K := K) (g : K) := by
      change weightIdeal q (J.fundamentalLattice ri) = _
      rw [weightIdeal_eq_powerIdeal, principalIdeal_eq_powerIdeal,
        ordUnit_uniformizerPowerUnit]
    have hgWeight : (g : K) ∈ J.fundamentalWeightIdeal ri := by
      rw [hw]
      exact generator_mem_principalIdeal _
    have hgGroup : (g : K) ∈ J.fundamentalNormGroup ri := by
      change (g : K) ∈ weightIdeal q (J.fundamentalLattice ri) at hgWeight
      change (g : K) ∈ normGroupSet q (J.fundamentalLattice ri)
      exact weightIdeal_subset_normGroupSet b hb hgWeight
    have hproductOdd : Odd (ordUnit K a + ordUnit K g) := by
      dsimp only [g]
      rw [ordUnit_uniformizerPowerUnit]
      change Even (ordUnit K a + ordUnit K b) at heven
      rcases heven with ⟨m, hm⟩
      rcases hodd with ⟨k, hk⟩
      refine ⟨m + k - ordUnit K b, ?_⟩
      omega
    have hle : scalarIdeal (a : K) (principalIdeal (K := K) (g : K)) ≤
        productDefectSum
          (J.fundamentalNormGroup li) (J.fundamentalNormGroup ri) := by
      exact scalarIdeal_le_productDefectSum_of_odd
        a g ha.1 hgGroup hproductOdd
    rw [← hw] at hle
    unfold boundaryProductDefectSum
    exact hle.trans _root_.le_sup_left

/-- Symmetric left-cross containment for the even branch of 93:26. -/
theorem leftCrossIdeal_le_productDefect_sup_parity_of_even
    (J : JordanDecomposition q L (t + 1)) (i : Fin t)
    (heven : Even (J.boundaryNormOrderSum i)) :
    scalarIdeal
        (J.fundamentalNormGenerator (boundaryRightIndex i) : K)
        (J.fundamentalWeightIdeal (boundaryLeftIndex i)) ≤
      J.boundaryProductDefectSum i ⊔ J.boundaryParityIdeal i := by
  let li : Fin (t + 1) := boundaryLeftIndex i
  let ri : Fin (t + 1) := boundaryRightIndex i
  let a : Kˣ := J.fundamentalNormGenerator li
  let b : Kˣ := J.fundamentalNormGenerator ri
  have ha := J.fundamentalNormGenerator_spec li
  have hb := J.fundamentalNormGenerator_spec ri
  rcases weightIdeal_eq_twoScale_or_odd a ha with htwo | hodd
  · have hmono := J.fundamentalNormGenerator_order_mono
        (i := li) (j := ri) (boundaryLeftIndex_le_rightIndex i)
    change scalarIdeal (b : K)
      (weightIdeal q (J.fundamentalLattice li)) ≤ _
    rw [htwo, J.fundamentalTwoScaleIdeal_eq_powerIdeal,
      scalarIdeal_powerIdeal_units]
    apply le_trans ?_ _root_.le_sup_right
    unfold boundaryParityIdeal
    rw [twiceIdeal_powerIdeal, powerIdeal_le_iff]
    dsimp only [a, b, li, ri] at hmono ⊢
    unfold boundaryNormOrderSum at heven ⊢
    rcases heven with ⟨m, hm⟩
    omega
  · let g : Kˣ := uniformizerPowerUnit K
      (weightIdealOrder q (J.fundamentalLattice li))
    have hw : J.fundamentalWeightIdeal li =
        principalIdeal (K := K) (g : K) := by
      change weightIdeal q (J.fundamentalLattice li) = _
      rw [weightIdeal_eq_powerIdeal, principalIdeal_eq_powerIdeal,
        ordUnit_uniformizerPowerUnit]
    have hgWeight : (g : K) ∈ J.fundamentalWeightIdeal li := by
      rw [hw]
      exact generator_mem_principalIdeal _
    have hgGroup : (g : K) ∈ J.fundamentalNormGroup li := by
      change (g : K) ∈ weightIdeal q (J.fundamentalLattice li) at hgWeight
      change (g : K) ∈ normGroupSet q (J.fundamentalLattice li)
      exact weightIdeal_subset_normGroupSet a ha hgWeight
    have hproductOdd : Odd (ordUnit K b + ordUnit K g) := by
      dsimp only [g]
      rw [ordUnit_uniformizerPowerUnit]
      change Even (ordUnit K a + ordUnit K b) at heven
      rcases heven with ⟨m, hm⟩
      rcases hodd with ⟨k, hk⟩
      refine ⟨m + k - ordUnit K a, ?_⟩
      omega
    have hle : scalarIdeal (b : K) (principalIdeal (K := K) (g : K)) ≤
        productDefectSum
          (J.fundamentalNormGroup ri) (J.fundamentalNormGroup li) := by
      exact scalarIdeal_le_productDefectSum_of_odd
        b g hb.1 hgGroup hproductOdd
    rw [← hw] at hle
    rw [productDefectSum_comm] at hle
    unfold boundaryProductDefectSum
    dsimp only [a, b, li, ri] at hle ⊢
    exact hle.trans _root_.le_sup_left

/-- O'Meara 93:26, even branch:

`s_i² f_i = d(a_i a_(i+1)) + a_i w_(i+1) + a_(i+1) w_i
  + 2 p^((u_i+u_(i+1))/2+s_i)`.

Unlike the previous interface version, every ideal in this identity is the
semantic ideal constructed from the Jordan decomposition. -/
theorem scaledFundamentalIdeal_eq_even_formula
    (J : JordanDecomposition q L (t + 1)) (i : Fin t)
    (heven : Even (J.boundaryNormOrderSum i)) :
    J.scaledFundamentalIdeal i =
      (((quadraticDefectIdeal
            (J.fundamentalNormGenerator (boundaryLeftIndex i) *
              J.fundamentalNormGenerator (boundaryRightIndex i)) ⊔
          scalarIdeal
            (J.fundamentalNormGenerator (boundaryLeftIndex i) : K)
            (J.fundamentalWeightIdeal (boundaryRightIndex i))) ⊔
        scalarIdeal
          (J.fundamentalNormGenerator (boundaryRightIndex i) : K)
          (J.fundamentalWeightIdeal (boundaryLeftIndex i))) ⊔
        J.boundaryParityIdeal i) := by
  let li : Fin (t + 1) := boundaryLeftIndex i
  let ri : Fin (t + 1) := boundaryRightIndex i
  let a : Kˣ := J.fundamentalNormGenerator li
  let b : Kˣ := J.fundamentalNormGenerator ri
  have ha := J.fundamentalNormGenerator_spec li
  have hb := J.fundamentalNormGenerator_spec ri
  have hA : J.fundamentalWeightIdeal li ≤
      principalIdeal (K := K) (a : K) := by
    change weightIdeal q (J.fundamentalLattice li) ≤ _
    exact weightIdeal_le_principalIdeal a ha
  have hB : J.fundamentalWeightIdeal ri ≤
      principalIdeal (K := K) (b : K) := by
    change weightIdeal q (J.fundamentalLattice ri) ≤ _
    exact weightIdeal_le_principalIdeal b hb
  have hprodUpper : J.boundaryProductDefectSum i ≤
      (quadraticDefectIdeal (a * b) ⊔
        scalarIdeal (a : K) (J.fundamentalWeightIdeal ri)) ⊔
        scalarIdeal (b : K) (J.fundamentalWeightIdeal li) := by
    unfold boundaryProductDefectSum fundamentalNormGroup
    change productDefectSum
        (normGroupSet q (J.fundamentalLattice li))
        (normGroupSet q (J.fundamentalLattice ri)) ≤ _
    rw [normGroupSet_eq_integralSquareCoset_weightIdeal a ha,
      normGroupSet_eq_integralSquareCoset_weightIdeal b hb]
    exact productDefectSum_integralSquareCoset_le a b
      (J.fundamentalWeightIdeal li) (J.fundamentalWeightIdeal ri) hA hB
  have hdefectLower : quadraticDefectIdeal (a * b) ≤
      J.boundaryProductDefectSum i := by
    unfold boundaryProductDefectSum
    exact quadraticDefectIdeal_product_le_productDefectSum
      a b ha.1 hb.1
  have hrightCross : scalarIdeal (a : K)
      (J.fundamentalWeightIdeal ri) ≤
        J.boundaryProductDefectSum i ⊔ J.boundaryParityIdeal i :=
    J.rightCrossIdeal_le_productDefect_sup_parity_of_even i heven
  have hleftCross : scalarIdeal (b : K)
      (J.fundamentalWeightIdeal li) ≤
        J.boundaryProductDefectSum i ⊔ J.boundaryParityIdeal i :=
    J.leftCrossIdeal_le_productDefect_sup_parity_of_even i heven
  rw [scaledFundamentalIdeal, if_pos heven]
  change J.boundaryProductDefectSum i ⊔ J.boundaryParityIdeal i =
    (((quadraticDefectIdeal (a * b) ⊔
        scalarIdeal (a : K) (J.fundamentalWeightIdeal ri)) ⊔
      scalarIdeal (b : K) (J.fundamentalWeightIdeal li)) ⊔
      J.boundaryParityIdeal i)
  apply le_antisymm
  · exact _root_.sup_le (hprodUpper.trans _root_.le_sup_left)
      _root_.le_sup_right
  · apply _root_.sup_le
    · apply _root_.sup_le
      · apply _root_.sup_le
        · exact hdefectLower.trans _root_.le_sup_left
        · exact hrightCross
      · exact hleftCross
    · exact _root_.le_sup_right

/-- O'Meara 93:26, odd branch:
`s_i^2 f_i = a_i a_(i+1) O`. -/
theorem scaledFundamentalIdeal_eq_principalIdeal_of_odd
    (J : JordanDecomposition q L (t + 1)) (i : Fin t)
    (hodd : Odd (J.boundaryNormOrderSum i)) :
    J.scaledFundamentalIdeal i =
      principalIdeal (K := K)
        (((J.fundamentalNormGenerator (boundaryLeftIndex i)) *
          J.fundamentalNormGenerator (boundaryRightIndex i) : Kˣ) : K) := by
  have hnotEven : ¬ Even (J.boundaryNormOrderSum i) := by
    rintro ⟨m, hm⟩
    rcases hodd with ⟨n, hn⟩
    omega
  rw [scaledFundamentalIdeal, if_neg hnotEven,
    boundaryProductDefectSum]
  apply productDefectSum_eq_principalIdeal_of_odd
    (J.fundamentalNormGenerator (boundaryLeftIndex i))
    (J.fundamentalNormGenerator (boundaryRightIndex i))
    (J.fundamentalNormGenerator_spec (boundaryLeftIndex i))
    (J.fundamentalNormGenerator_spec (boundaryRightIndex i))
  simpa only [boundaryNormOrderSum] using hodd

/-- Unscaled form of the odd branch of O'Meara 93:26. -/
theorem fundamentalIdeal_eq_principalIdeal_of_odd
    (J : JordanDecomposition q L (t + 1)) (i : Fin t)
    (hodd : Odd (J.boundaryNormOrderSum i)) :
    J.fundamentalIdeal i =
      principalIdeal (K := K)
        ((((J.scaleGenerator (boundaryLeftIndex i))⁻¹ ^ 2) *
          J.fundamentalNormGenerator (boundaryLeftIndex i) *
          J.fundamentalNormGenerator (boundaryRightIndex i) : Kˣ) : K) := by
  rw [fundamentalIdeal,
    J.scaledFundamentalIdeal_eq_principalIdeal_of_odd i hodd,
    scalarIdeal_principalIdeal_units]
  congr 2
  apply Units.ext
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  ac_rfl

end JordanDecomposition

namespace JordanDecomposition.SameFundamentalType

variable {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {t : Nat}
  {J : JordanDecomposition q L (t + 1)}
  {H : JordanDecomposition r M (t + 1)}

/-- Equal fundamental type identifies the boundary norm-order sums. -/
theorem boundaryNormOrderSum_eq
    (F : JordanDecomposition.SameFundamentalType J H) (i : Fin t) :
    H.boundaryNormOrderSum i = J.boundaryNormOrderSum i := by
  unfold JordanDecomposition.boundaryNormOrderSum
  have hleft := F.fundamentalNormGenerator_order_eq
    (JordanDecomposition.boundaryLeftIndex i)
  have hright := F.fundamentalNormGenerator_order_eq
    (JordanDecomposition.boundaryRightIndex i)
  rw [F.indexEquiv_apply_eq_self] at hleft hright
  rw [hleft, hright]

/-- Equal fundamental type identifies the scale order occurring at a
boundary. -/
theorem boundaryScaleOrder_eq
    (F : JordanDecomposition.SameFundamentalType J H) (i : Fin t) :
    H.fundamentalScaleOrder (JordanDecomposition.boundaryLeftIndex i) =
      J.fundamentalScaleOrder
        (JordanDecomposition.boundaryLeftIndex i) := by
  have h := F.scaleOrder_eq (JordanDecomposition.boundaryLeftIndex i)
  rw [F.indexEquiv_apply_eq_self] at h
  exact h

/-- Equal fundamental type identifies the unscaled sum of product defects
at every boundary. -/
theorem boundaryProductDefectSum_eq
    (F : JordanDecomposition.SameFundamentalType J H) (i : Fin t) :
    H.boundaryProductDefectSum i = J.boundaryProductDefectSum i := by
  unfold JordanDecomposition.boundaryProductDefectSum
  have hleft := F.normGroup_eq (JordanDecomposition.boundaryLeftIndex i)
  have hright := F.normGroup_eq (JordanDecomposition.boundaryRightIndex i)
  rw [F.indexEquiv_apply_eq_self] at hleft hright
  rw [hleft, hright]

/-- Equal fundamental type identifies the even-parity dyadic boundary
term. -/
theorem boundaryParityIdeal_eq
    (F : JordanDecomposition.SameFundamentalType J H) (i : Fin t) :
    H.boundaryParityIdeal i = J.boundaryParityIdeal i := by
  unfold JordanDecomposition.boundaryParityIdeal
  rw [F.boundaryNormOrderSum_eq i, F.boundaryScaleOrder_eq i]

/-- The ideals `s_i^2 f_i` depend only on the fundamental type, directly
from O'Meara's original definition. -/
theorem scaledFundamentalIdeal_eq
    (F : JordanDecomposition.SameFundamentalType J H) (i : Fin t) :
    H.scaledFundamentalIdeal i = J.scaledFundamentalIdeal i := by
  unfold JordanDecomposition.scaledFundamentalIdeal
  rw [F.boundaryNormOrderSum_eq i,
    F.boundaryProductDefectSum_eq i,
    F.boundaryParityIdeal_eq i]

/-- O'Meara's boundary ideals `f_i` depend only on the fundamental type. -/
theorem fundamentalIdeal_eq
    (F : JordanDecomposition.SameFundamentalType J H) (i : Fin t) :
    H.fundamentalIdeal i = J.fundamentalIdeal i := by
  unfold JordanDecomposition.fundamentalIdeal
  rw [F.scaledFundamentalIdeal_eq i]
  apply scalarIdeal_units_eq_of_ordUnit_eq
  have hs := F.scaleOrder_eq (JordanDecomposition.boundaryLeftIndex i)
  rw [F.indexEquiv_apply_eq_self] at hs
  change ordUnit K
      ((H.scaleGenerator (JordanDecomposition.boundaryLeftIndex i))⁻¹ ^ 2) =
    ordUnit K
      ((J.scaleGenerator (JordanDecomposition.boundaryLeftIndex i))⁻¹ ^ 2)
  rw [ordUnit_pow, ordUnit_inv, ordUnit_pow, ordUnit_inv]
  have hs' : ordUnit K
        (H.scaleGenerator (JordanDecomposition.boundaryLeftIndex i)) =
      ordUnit K
        (J.scaleGenerator (JordanDecomposition.boundaryLeftIndex i)) := by
    simpa only [JordanDecomposition.fundamentalScaleOrder] using hs
  rw [hs']

end JordanDecomposition.SameFundamentalType

end Lattice
end Bong
