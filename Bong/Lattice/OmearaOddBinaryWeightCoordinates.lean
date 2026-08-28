/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009BinaryWeightProof
import Bong.Bong.BinaryDualModular
import Bong.Lattice.OmearaBinaryGeneralPlane
import Bong.Lattice.OmearaHyperbolicCancellation
import Bong.Lattice.OrthogonalDecompositionVolume

/-!
# Binary O'Meara coordinates in the nonterminal odd-weight branch

For a binary unimodular lattice, prescribe an actual norm-generator vector
as the first basis vector and apply O'Meara 93:4 to the second vector.  If
the canonical weight is strictly below `2sL`, the resulting second
quadratic value has exactly the weight order.  The unimodular Gram
determinant forces the mixed pairing to be a unit, so an integral unit
rescaling puts the basis in the exact general-plane form `A(a,b)`.

This is the nonterminal counterpart of `OmearaBinaryWeightCoordinates`.
No classification hypothesis is used.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- In a positive-rank unimodular lattice the canonical scale order is
zero, hence the order of `2sL` is the ramification index. -/
theorem canonicalTwoScaleOrder_eq_ramificationIndex_of_unimodular
    (hmodular : IsModular q L (1 : Kˣ))
    (a : Kˣ) (ha : IsNormGeneratorValue q L a) :
    canonicalTwoScaleOrder q L = (ramificationIndex K : Int) := by
  have hpos : 0 < finrank K V := finrank_pos_of_isNormGeneratorValue ha
  have hscaleOrder : canonicalScaleOrder q L = 0 := by
    apply powerIdeal_order_eq_of_eq (K := K)
    calc
      powerIdeal (K := K) (canonicalScaleOrder q L) =
          scaleIdeal q L :=
        (scaleIdeal_eq_powerIdeal_canonicalScaleOrder ha).symm
      _ = principalIdeal (K := K) (1 : K) :=
        hmodular.scaleIdeal_eq_principal hpos
      _ = powerIdeal (K := K) (0 : Int) := by
        let one : Kˣ := 1
        simpa [one, ordUnit] using
          (principalIdeal_eq_powerIdeal one)
  simp [canonicalTwoScaleOrder, hscaleOrder]

/-- A weight-adapted integral binary basis in the strict nonterminal branch
has unit mixed pairing.  The proof is the binary Gram-determinant argument:
the product of the diagonal entries is in the maximal ideal, while the
Gram determinant is a unit. -/
theorem isValuationUnit_pairing_of_binary_weight_basis
    (hmodular : IsModular q L (1 : Kˣ))
    (a : Kˣ) (ha : IsNormGeneratorValue q L a)
    (hodd : Odd (ordUnit K a + weightIdealOrder q L))
    (b : Basis (Fin 2) K V) (hbL : basisLattice b = L)
    (hfirst : q.quadratic (b 0) = (a : K))
    (hbeta : q.quadratic (b 1) ∈ weightIdeal q L) :
    IsValuationUnit K (q.bilin (b 0) (b 1)) := by
  have hnormNonneg : 0 ≤ ordUnit K a := by
    have hnormScale := normIdeal_le_scaleIdeal q L
    rw [ha.2, hmodular.scaleIdeal_eq_principal
      (finrank_pos_of_isNormGeneratorValue ha)] at hnormScale
    have hord : ord K (1 : K) ≤ ord K (a : K) :=
      (principalIdeal_le_iff_ord_ge
        (Units.ne_zero a) (one_ne_zero : (1 : K) ≠ 0)).1 hnormScale
    rw [ord_one, ← coe_ordUnit K a] at hord
    exact WithTop.coe_le_coe.mp hord
  have hnormLeWeight : ordUnit K a ≤ weightIdealOrder q L :=
    normGeneratorOrder_le_weightIdealOrder a ha
  have hnormLtWeight : ordUnit K a < weightIdealOrder q L := by
    apply lt_of_le_of_ne hnormLeWeight
    intro heq
    have heven : Even (ordUnit K a + weightIdealOrder q L) := by
      refine ⟨ordUnit K a, ?_⟩
      omega
    exact (Int.not_odd_iff_even.mpr heven hodd).elim
  have hweightPos : 0 < weightIdealOrder q L :=
    lt_of_le_of_lt hnormNonneg hnormLtWeight
  have hbetaLower :
      ((weightIdealOrder q L : Int) : WithTop Int) ≤
        ord K (q.quadratic (b 1)) := by
    rw [weightIdeal_eq_powerIdeal] at hbeta
    exact (mem_powerIdeal_iff _ _).1 hbeta
  have hbetaMax : IsInMaximalIdeal K (q.quadratic (b 1)) := by
    rw [IsInMaximalIdeal]
    have hpos : (0 : WithTop Int) <
        ((weightIdealOrder q L : Int) : WithTop Int) := by
      exact_mod_cast hweightPos
    exact hpos.trans_le hbetaLower
  have hscale : scaleIdeal q L = principalIdeal (K := K) (1 : K) :=
    hmodular.scaleIdeal_eq_principal
      (finrank_pos_of_isNormGeneratorValue ha)
  have hfirstIntegral : q.quadratic (b 0) ∈ IntegerRing K := by
    change q.bilin (b 0) (b 0) ∈ IntegerRing K
    apply mem_integerRing_of_mul_mem_principalIdeal
      (one_ne_zero : (1 : K) ≠ 0)
    simpa only [one_mul, ← hscale] using
      (bilin_mem_scaleIdeal_of_mem q L
        (by rw [← hbL]; exact Submodule.subset_span ⟨0, rfl⟩)
        (by rw [← hbL]; exact Submodule.subset_span ⟨0, rfl⟩))
  have hpairIntegral : q.bilin (b 0) (b 1) ∈ IntegerRing K := by
    apply mem_integerRing_of_mul_mem_principalIdeal
      (one_ne_zero : (1 : K) ≠ 0)
    simpa only [one_mul, ← hscale] using
      (bilin_mem_scaleIdeal_of_mem q L
        (by rw [← hbL]; exact Submodule.subset_span ⟨0, rfl⟩)
        (by rw [← hbL]; exact Submodule.subset_span ⟨1, rfl⟩))
  have hvolumeZero : volumeOrder q (basisLattice b) = 0 := by
    rw [hbL, hmodular.volumeOrder_eq]
    simp [ordUnit]
  have hgramOrder : ord K
      (LinearMap.BilinForm.toMatrix b q.bilin).det = 0 := by
    rw [← coe_volumeOrder_basisLattice_eq_ord_det_toMatrix q b,
      hvolumeZero]
    rfl
  have hgram :
      (LinearMap.BilinForm.toMatrix b q.bilin).det =
        q.quadratic (b 0) * q.quadratic (b 1) -
          q.bilin (b 0) (b 1) ^ 2 := by
    rw [Matrix.det_fin_two]
    simp only [LinearMap.BilinForm.toMatrix_apply]
    change q.quadratic (b 0) * q.quadratic (b 1) -
      q.bilin (b 0) (b 1) * q.bilin (b 1) (b 0) = _
    rw [q.isSymm.eq (b 1) (b 0), pow_two]
  have hgramUnit : IsValuationUnit K
      (q.quadratic (b 0) * q.quadratic (b 1) -
        q.bilin (b 0) (b 1) ^ 2) := by
    rw [← hgram]
    exact hgramOrder
  have hproductMax : IsInMaximalIdeal K
      (q.quadratic (b 0) * q.quadratic (b 1)) := by
    exact isIntegral_mul_isInMaximalIdeal K
      ((mem_integerRing_iff K).1 hfirstIntegral) hbetaMax
  by_contra hnot
  have hpairNonneg : (0 : WithTop Int) ≤
      ord K (q.bilin (b 0) (b 1)) :=
    (mem_integerRing_iff K).1 hpairIntegral
  have hpairMax : IsInMaximalIdeal K (q.bilin (b 0) (b 1)) := by
    rw [IsInMaximalIdeal]
    exact lt_of_le_of_ne hpairNonneg (Ne.symm hnot)
  have hpairSqMax : IsInMaximalIdeal K
      (q.bilin (b 0) (b 1) ^ 2) := by
    rw [pow_two]
    exact isInMaximalIdeal_mul_isIntegral K hpairMax
      ((mem_integerRing_iff K).1 hpairIntegral)
  have hdetMax := isInMaximalIdeal_sub hproductMax hpairSqMax
  rw [IsInMaximalIdeal, hgramUnit] at hdetMax
  exact (lt_irrefl 0 hdetMax)

/-- Exactness of the sheared weight coefficient once the two integral
basis vectors pair by a valuation unit. -/
theorem quadratic_order_eq_weightIdealOrder_of_binary_weight_basis
    (hmodular : IsModular q L (1 : Kˣ))
    (a : Kˣ) (ha : IsNormGeneratorValue q L a)
    (b : Basis (Fin 2) K V) (hbL : basisLattice b = L)
    (hfirst : q.quadratic (b 0) = (a : K))
    (hbeta : q.quadratic (b 1) ∈ weightIdeal q L)
    (hpairUnit : IsValuationUnit K (q.bilin (b 0) (b 1)))
    (hlt : weightIdealOrder q L < canonicalTwoScaleOrder q L) :
    ord K (q.quadratic (b 1)) =
      ((weightIdealOrder q L : Int) : WithTop Int) := by
  let W : Int := weightIdealOrder q L
  let T : Int := canonicalTwoScaleOrder q L
  have hbetaLower : ((W : Int) : WithTop Int) ≤
      ord K (q.quadratic (b 1)) := by
    rw [weightIdeal_eq_powerIdeal] at hbeta
    exact (mem_powerIdeal_iff _ _).1 hbeta
  by_contra hne
  have hbetaStrict : ((W : Int) : WithTop Int) <
      ord K (q.quadratic (b 1)) :=
    lt_of_le_of_ne hbetaLower (Ne.symm hne)
  rcases exists_quadratic_order_eq_weightIdealOrder_of_lt_twoScale
      a ha hlt with ⟨x, hx, hxne, hxOrder, hxOdd⟩
  have hxBasis : x ∈ basisLattice b := by simpa only [hbL] using hx
  have hxCoords := (mem_basisLattice_iff_repr_mem_integerRing b x).1 hxBasis
  let r : IntegerRing K := ⟨b.repr x 0, hxCoords 0⟩
  let s : IntegerRing K := ⟨b.repr x 1, hxCoords 1⟩
  have hxRep : x = (r : K) • b 0 + (s : K) • b 1 := by
    have hsum := b.sum_repr x
    rw [Fin.sum_univ_two] at hsum
    simpa only [r, s] using hsum.symm
  have hrNonneg : (0 : WithTop Int) ≤ ord K (r : K) :=
    (mem_integerRing_iff K).1 r.property
  have hsNonneg : (0 : WithTop Int) ≤ ord K (s : K) :=
    (mem_integerRing_iff K).1 s.property
  let headTerm : K := (r : K) ^ 2 * q.quadratic (b 0)
  let betaTerm : K := (s : K) ^ 2 * q.quadratic (b 1)
  let crossTerm : K :=
    (2 : K) * (r : K) * (s : K) * q.bilin (b 0) (b 1)
  have hbetaTermGt : ((W : Int) : WithTop Int) <
      ord K betaTerm := by
    have hle : ord K (q.quadratic (b 1)) ≤ ord K betaTerm := by
      dsimp [betaTerm]
      rw [ord_mul, ord_pow]
      have htwoS : (0 : WithTop Int) ≤ 2 • ord K (s : K) :=
        nsmul_nonneg hsNonneg 2
      simpa [add_comm] using
        add_le_add_right htwoS (ord K (q.quadratic (b 1)))
    exact hbetaStrict.trans_le hle
  have hcrossTermGt : ((W : Int) : WithTop Int) <
      ord K crossTerm := by
    have hTFormula : T = (ramificationIndex K : Int) := by
      exact canonicalTwoScaleOrder_eq_ramificationIndex_of_unimodular
        hmodular a ha
    have hTLe : ((T : Int) : WithTop Int) ≤ ord K crossTerm := by
      dsimp [crossTerm]
      rw [ord_mul, ord_mul, ord_mul, ← ramificationIndex_spec]
      have hpairOrder : ord K (q.bilin (b 0) (b 1)) = 0 := hpairUnit
      rw [hpairOrder, add_zero]
      have hcoeff : (0 : WithTop Int) ≤
          ord K (r : K) + ord K (s : K) :=
        add_nonneg hrNonneg hsNonneg
      rw [hTFormula]
      calc
        ((ramificationIndex K : Int) : WithTop Int) ≤
            ((ramificationIndex K : Int) : WithTop Int) +
              (ord K (r : K) + ord K (s : K)) :=
          by
            calc
              ((ramificationIndex K : Int) : WithTop Int) =
                  0 + ((ramificationIndex K : Int) : WithTop Int) := by simp
              _ ≤ (ord K (r : K) + ord K (s : K)) +
                  ((ramificationIndex K : Int) : WithTop Int) :=
                add_le_add_left hcoeff _
              _ = ((ramificationIndex K : Int) : WithTop Int) +
                  (ord K (r : K) + ord K (s : K)) := by ac_rfl
        _ = ((ramificationIndex K : Int) : WithTop Int) +
              ord K (r : K) + ord K (s : K) := by ac_rfl
    have hltCast : ((W : Int) : WithTop Int) <
        ((T : Int) : WithTop Int) := by
      exact WithTop.coe_lt_coe.mpr (by simpa only [W, T] using hlt)
    exact hltCast.trans_le hTLe
  have hremainderGt : ((W : Int) : WithTop Int) <
      ord K (betaTerm + crossTerm) := by
    exact (lt_min hbetaTermGt hcrossTermGt).trans_le
      (min_ord_le_ord_add K betaTerm crossTerm)
  have hxFormula : q.quadratic x =
      headTerm + betaTerm + crossTerm := by
    rw [hxRep, q.quadratic_add, q.quadratic_smul,
      q.quadratic_smul, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right]
    dsimp [headTerm, betaTerm, crossTerm]
    ring
  have hheadEq : headTerm = q.quadratic x -
      (betaTerm + crossTerm) := by
    rw [hxFormula]
    ring
  have hxOrderW : ord K (q.quadratic x) =
      ((W : Int) : WithTop Int) := hxOrder
  have hxLtRemainder : ord K (q.quadratic x) <
      ord K (betaTerm + crossTerm) := by
    rw [hxOrderW]
    exact hremainderGt
  have hheadOrder : ord K headTerm =
      ((W : Int) : WithTop Int) := by
    rw [hheadEq, (ord K).map_sub_eq_of_lt_left hxLtRemainder, hxOrderW]
  have hrNe : (r : K) ≠ 0 := by
    intro hrZero
    dsimp [headTerm] at hheadOrder
    rw [hrZero, zero_pow (by norm_num), zero_mul, ord_zero] at hheadOrder
    exact WithTop.top_ne_coe hheadOrder
  let ru : Kˣ := Units.mk0 (r : K) hrNe
  have hfirstOrder : ord K (q.quadratic (b 0)) =
      ((ordUnit K a : Int) : WithTop Int) := by
    rw [hfirst, ← coe_ordUnit]
  have hheadOrderInt : W = 2 * ordUnit K ru + ordUnit K a := by
    have hrOrder : ord K (r : K) =
        ((ordUnit K ru : Int) : WithTop Int) := by
      change ord K (ru : K) = _
      exact (coe_ordUnit K ru).symm
    apply WithTop.coe_injective
    rw [← hheadOrder]
    dsimp [headTerm]
    rw [ord_mul, ord_pow, hrOrder, hfirstOrder]
    norm_cast
  have hxEven : Even (ordUnit K a + W) := by
    refine ⟨ordUnit K a + ordUnit K ru, ?_⟩
    omega
  exact (Int.not_odd_iff_even.mpr hxEven hxOdd).elim

/-- Exact output of O'Meara 93:10 in the strict nonterminal branch. -/
structure Omeara9310OddWeightCoordinatesData
    (q : QuadraticSpace K V) (L : Lattice K V) (x : V) where
  beta : K
  beta_mem_weight : beta ∈ weightIdeal q L
  beta_ne : beta ≠ 0
  beta_order : ord K beta =
    ((weightIdealOrder q L : Int) : WithTop Int)
  nondegenerate : q.quadratic x * beta ≠ 1
  isometry : Isometry q
    (QuadraticSpace.omearaGeneralPlane
      (q.quadratic x) beta nondegenerate)
    L (hyperbolicPlaneLattice (K := K))

/-- The integral basis obtained directly from the O'Meara 93:4 shear. -/
structure OddWeightShearedBinaryBasisData
    (q : QuadraticSpace K V) (L : Lattice K V) (x : V) where
  basis : Basis (Fin 2) K V
  basis_lattice : basisLattice basis = L
  first_eq : basis 0 = x
  second_mem_weight : q.quadratic (basis 1) ∈ weightIdeal q L
  second_order : ord K (q.quadratic (basis 1)) =
    ((weightIdealOrder q L : Int) : WithTop Int)
  pairing_unit : IsValuationUnit K (q.bilin (basis 0) (basis 1))

set_option maxHeartbeats 800000 in

/-- Perform the 93:4 shear and prove both the exact weight order and the
unit mixed-pairing assertion. -/
noncomputable def oddWeightShearedBinaryBasisData
    (hmodular : IsModular q L (1 : Kˣ))
    (hrank : finrank K V = 2)
    (x : V) (hx : IsNormGenerator q L x)
    (hxne : q.quadratic x ≠ 0)
    (hodd : Odd (ordUnit K (Units.mk0 (q.quadratic x) hxne) +
      weightIdealOrder q L))
    (hlt : weightIdealOrder q L < canonicalTwoScaleOrder q L) :
    OddWeightShearedBinaryBasisData q L x := by
  let a : Kˣ := Units.mk0 (q.quadratic x) hxne
  have ha : IsNormGeneratorValue q L a :=
    hx.isNormGeneratorValue hxne
  let B := BONG.ofNormGeneratorBinary q L x hx hxne hrank
  let hex := B.exists_weight_shear
  let c : IntegerRing K := Classical.choose hex
  have hcSpec := Classical.choose_spec hex
  let y : V := B.binarySecondVector + (c : K) • B.head
  have hbeta : q.quadratic y ∈ weightIdeal q L := hcSpec.2.1
  let b₀ : Basis (Fin 2) K V := B.binaryAdaptedFinBasis
  let b : Basis (Fin 2) K V := basisSecondShearBy b₀ (c : K)
  have hbzero : b 0 = x := by
    rw [basisSecondShearBy_zero]
    change B.binaryAdaptedFinBasis 0 = x
    rw [B.binaryAdaptedFinBasis_zero]
    simpa only [B] using
      (BONG.head_ofNormGeneratorBinary q L x hx hxne hrank)
  have hbone : b 1 = y := by
    rw [basisSecondShearBy_one, B.binaryAdaptedFinBasis_one]
    rw [B.binaryAdaptedFinBasis_zero]
  have hbL : basisLattice b = L := by
    calc
      basisLattice b = basisLattice b₀ :=
        basisLattice_basisSecondShearBy b₀ c
      _ = L := B.basisLattice_binaryAdaptedFinBasis
  have hfirst : q.quadratic (b 0) = (a : K) := by
    rw [hbzero]
    rfl
  have hbeta' : q.quadratic (b 1) ∈ weightIdeal q L := by
    simpa only [hbone, y] using hbeta
  have hpairUnit := isValuationUnit_pairing_of_binary_weight_basis
    hmodular a ha hodd b hbL hfirst hbeta'
  have hbetaOrder := quadratic_order_eq_weightIdealOrder_of_binary_weight_basis
    hmodular a ha b hbL hfirst hbeta' hpairUnit hlt
  exact
    { basis := b
      basis_lattice := hbL
      first_eq := hbzero
      second_mem_weight := hbeta'
      second_order := hbetaOrder
      pairing_unit := hpairUnit }

/-- The sheared basis after rescaling its second vector by the inverse of
the unit mixed pairing. -/
structure OddWeightNormalizedBinaryBasisData
    (q : QuadraticSpace K V) (L : Lattice K V) (x : V) where
  basis : Basis (Fin 2) K V
  basis_lattice : basisLattice basis = L
  first_eq : basis 0 = x
  pairing_eq : q.bilin (basis 0) (basis 1) = 1
  second_mem_weight : q.quadratic (basis 1) ∈ weightIdeal q L
  second_ne : q.quadratic (basis 1) ≠ 0
  second_order : ord K (q.quadratic (basis 1)) =
    ((weightIdealOrder q L : Int) : WithTop Int)

set_option maxHeartbeats 800000 in

/-- Unit-normalize a sheared basis without changing its integral lattice or
the order of its weight coefficient. -/
noncomputable def OddWeightShearedBinaryBasisData.normalize
    (D : OddWeightShearedBinaryBasisData q L x) :
    OddWeightNormalizedBinaryBasisData q L x := by
  let b := D.basis
  have hpairNe : q.bilin (b 0) (b 1) ≠ 0 :=
    ne_zero_of_isValuationUnit D.pairing_unit
  let pair : Kˣ := Units.mk0 (q.bilin (b 0) (b 1)) hpairNe
  let weights : Fin 2 → Kˣ := fun i ↦ if i = 1 then pair⁻¹ else 1
  let b' : Basis (Fin 2) K V := b.unitsSMul weights
  have hweights : ∀ i, IsValuationUnit K (weights i : K) := by
    intro i
    by_cases hi : i = 1
    · subst i
      change IsValuationUnit K ((pair⁻¹ : Kˣ) : K)
      rw [IsValuationUnit, Units.val_inv_eq_inv_val,
        AddValuation.map_inv]
      change -ord K (q.bilin (b 0) (b 1)) = 0
      rw [D.pairing_unit]
      simp
    · simp [weights, hi, IsValuationUnit]
  have hb'L : basisLattice b' = L := by
    rw [show basisLattice b' = basisLattice b from
      basisLattice_unitsSMul_eq b weights hweights, D.basis_lattice]
  have hb'zero : b' 0 = x := by
    change (b.unitsSMul weights) 0 = x
    rw [Basis.unitsSMul_apply]
    have hweightsZero : weights 0 = 1 := by simp [weights]
    rw [hweightsZero, one_smul]
    exact D.first_eq
  have hb'one : b' 1 = (q.bilin (b 0) (b 1))⁻¹ • b 1 := by
    change (b.unitsSMul weights) 1 = _
    rw [Basis.unitsSMul_apply]
    simp [weights, pair, Units.smul_def]
  have hpair : q.bilin (b' 0) (b' 1) = 1 := by
    rw [hb'zero, hb'one, ← D.first_eq,
      LinearMap.BilinForm.smul_right]
    change (q.bilin (b 0) (b 1))⁻¹ * q.bilin (b 0) (b 1) = 1
    exact inv_mul_cancel₀ hpairNe
  let beta : K := q.quadratic (b' 1)
  have hbetaFormula : beta =
      (q.bilin (b 0) (b 1))⁻¹ ^ 2 * q.quadratic (b 1) := by
    dsimp only [beta]
    rw [hb'one, q.quadratic_smul]
  have hpairInvIntegral : (q.bilin (b 0) (b 1))⁻¹ ∈ IntegerRing K := by
    have hpairInvUnit : IsValuationUnit K
        (q.bilin (b 0) (b 1))⁻¹ := by
      rw [IsValuationUnit, AddValuation.map_inv]
      change -ord K (q.bilin (b 0) (b 1)) = 0
      rw [D.pairing_unit]
      simp
    exact (mem_integerRing_iff K).2 hpairInvUnit.ge
  have hbetaMem : beta ∈ weightIdeal q L := by
    rw [hbetaFormula]
    let uO : IntegerRing K :=
      ⟨(q.bilin (b 0) (b 1))⁻¹ ^ 2,
        (IntegerRing K).toSubring.pow_mem hpairInvIntegral 2⟩
    have := (weightIdeal q L).smul_mem uO D.second_mem_weight
    change (q.bilin (b 0) (b 1))⁻¹ ^ 2 *
      q.quadratic (b 1) ∈ weightIdeal q L at this
    exact this
  have hbetaExact : ord K beta =
      ((weightIdealOrder q L : Int) : WithTop Int) := by
    rw [hbetaFormula, ord_mul, ord_pow, AddValuation.map_inv,
      D.pairing_unit]
    simpa using D.second_order
  have hbetaNe : beta ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero] at hbetaExact
    exact WithTop.top_ne_coe hbetaExact
  exact
    { basis := b'
      basis_lattice := hb'L
      first_eq := hb'zero
      pairing_eq := hpair
      second_mem_weight := hbetaMem
      second_ne := hbetaNe
      second_order := hbetaExact }

set_option maxHeartbeats 800000 in

/-- Construct the exact odd-weight coordinates with a prescribed actual
norm-generator vector. -/
noncomputable def omeara9310OddWeightCoordinatesData
    (hmodular : IsModular q L (1 : Kˣ))
    (hrank : finrank K V = 2)
    (x : V) (hx : IsNormGenerator q L x)
    (hxne : q.quadratic x ≠ 0)
    (hodd : Odd (ordUnit K (Units.mk0 (q.quadratic x) hxne) +
      weightIdealOrder q L))
    (hlt : weightIdealOrder q L < canonicalTwoScaleOrder q L) :
    Omeara9310OddWeightCoordinatesData q L x := by
  let D := oddWeightShearedBinaryBasisData
    hmodular hrank x hx hxne hodd hlt
  let N := D.normalize
  let beta : K := q.quadratic (N.basis 1)
  let C := BinaryModularGeneralPlaneData.ofBasis
    q L (1 : Kˣ) hmodular N.basis N.basis_lattice N.pairing_eq
  have hleft : C.leftCoefficient = q.quadratic x := by
    rw [C.leftCoefficient_eq]
    have hCbasis : C.basis = N.basis := rfl
    rw [hCbasis]
    simp [omearaLeftCoefficient, N.first_eq]
  have hright : C.rightCoefficient = beta := by
    rw [C.rightCoefficient_eq]
    have hCbasis : C.basis = N.basis := rfl
    rw [hCbasis]
    simp [omearaRightCoefficient, beta]
  have hnondegenerate : q.quadratic x * beta ≠ 1 := by
    simpa only [hleft, hright] using C.nondegenerate
  let model := QuadraticSpace.omearaGeneralPlane
    C.leftCoefficient C.rightCoefficient C.nondegenerate
  let identify : Isometry (model.rescaleUnit (1 : Kˣ)) model
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) :=
    Isometry.rescaleUnitOne model (hyperbolicPlaneLattice (K := K))
  let displayed := C.isometry.trans identify
  let adjusted : Isometry q
      (QuadraticSpace.omearaGeneralPlane
        (q.quadratic x) beta hnondegenerate)
      L (hyperbolicPlaneLattice (K := K)) := by
    exact
      { toLinearEquiv := displayed.toLinearEquiv
        map_bilin := by
          intro z w
          have h := displayed.map_bilin z w
          rw [QuadraticSpace.omearaGeneralPlane_bilin_apply] at h ⊢
          simpa only [hleft, hright] using h
        map_mem := displayed.map_mem }
  exact
    { beta := beta
      beta_mem_weight := N.second_mem_weight
      beta_ne := N.second_ne
      beta_order := N.second_order
      nondegenerate := hnondegenerate
      isometry := adjusted }

end Lattice

end Bong
