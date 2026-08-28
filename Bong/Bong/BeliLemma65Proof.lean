/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma65
import Bong.Bong.BeliLemma64Proof
import Bong.Bong.BeliLemma317
import Bong.Bong.BeliLemma61Proof
import Bong.Bong.BinaryHyperbolicEndpoint
import Bong.Lattice.OmearaIntegralReflection
import Bong.Lattice.VolumeInclusion

/-!
# Proof of Beli (2003), Lemma 6.5

The proof follows Beli's case split through Lemma 3.17.  The preliminary
parity lemma below isolates the fact used throughout the low range: an
admissible binary parameter which has an equal-value norm-generator basis
and whose order is at most `2e` necessarily has even order.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace Lattice

/-- Rescaling the first entry of a mixed pairing translates a scale-ideal
bound by the valuation of the rescaling factor. -/
theorem bilin_mem_powerIdeal_of_mem_rescale
    {W : Type v} [AddCommGroup W] [Module K W]
    {p : QuadraticSpace K W} {M : Lattice K W}
    (a : Kˣ) (s : Int)
    (hscale : scaleIdeal p M ≤ powerIdeal (K := K) s)
    {x y : W} (hx : x ∈ rescale a M) (hy : y ∈ M) :
    p.bilin x y ∈ powerIdeal (K := K) (s + ordUnit K a) := by
  rw [mem_rescale_iff] at hx
  rcases hx with ⟨z, hz, rfl⟩
  have hbase : p.bilin z y ∈ powerIdeal (K := K) s :=
    hscale (bilin_mem_scaleIdeal_of_mem p M hz hy)
  rw [LinearMap.BilinForm.smul_left, mem_powerIdeal_iff, ord_mul,
    ← coe_ordUnit]
  have hbaseOrder := (mem_powerIdeal_iff (K := K) s _).1 hbase
  have hadd := add_le_add_left hbaseOrder (ordUnit K a : WithTop Int)
  have hcast : ((s + ordUnit K a : Int) : WithTop Int) =
      (s : WithTop Int) + (ordUnit K a : WithTop Int) := by
    norm_cast
  rw [hcast]
  simpa only [add_comm] using hadd

/-- A uniformizer factor can be cancelled from a power-ideal membership,
provided the target exponent is translated by the same amount. -/
theorem mem_powerIdeal_of_uniformizerPower_mul_mem
    (k : Nat) (r : Int) (z : K)
    (hmem :
      ((uniformizerPowerUnit K (k : Int) : Kˣ) : K) * z ∈
        powerIdeal (K := K) (r + (k : Int))) :
    z ∈ powerIdeal (K := K) r := by
  rw [mem_powerIdeal_iff] at hmem ⊢
  rw [ord_mul, ← coe_ordUnit, ordUnit_uniformizerPowerUnit] at hmem
  have hcast :
      ((r + (k : Int) : Int) : WithTop Int) =
        (r : WithTop Int) + ((k : Int) : WithTop Int) := by
    norm_cast
  rw [hcast] at hmem
  exact (WithTop.add_le_add_iff_right
    (z := ((k : Int) : WithTop Int)) (by simp)).mp (by
      simpa only [add_comm] using hmem)

/-- The dyadic inclusion `2 sM ⊆ nM` converts a norm-order bound into the
standard lower bound `ord(sM) ≥ ord(nM)-e` for the scale ideal. -/
theorem scaleIdeal_le_powerIdeal_sub_ramification_of_normIdeal_eq
    {W : Type v} [AddCommGroup W] [Module K W]
    {p : QuadraticSpace K W} {M : Lattice K W} (a : Int)
    (hnorm : normIdeal p M = powerIdeal (K := K) a) :
    scaleIdeal p M ≤
      powerIdeal (K := K) (a - ramificationIndex K) := by
  intro z hz
  have htwo := two_smul_mem_normIdeal p M hz
  rw [hnorm] at htwo
  by_cases hzZero : z = 0
  · subst z
    exact (powerIdeal (K := K)
      (a - ramificationIndex K)).zero_mem
  · let zu : Kˣ := Units.mk0 z hzZero
    have hzOrder : ord K z = (ordUnit K zu : WithTop Int) := by
      simpa only [zu, coe_ordUnit, Units.val_mk0]
    have htwoOrder :=
      (mem_powerIdeal_iff (K := K) a _).1 htwo
    change (a : WithTop Int) ≤ ord K ((2 : K) * z) at htwoOrder
    rw [ord_mul, ← ramificationIndex_spec, hzOrder] at htwoOrder
    apply (mem_powerIdeal_iff (K := K)
      (a - ramificationIndex K) z).2
    rw [hzOrder]
    norm_cast at htwoOrder ⊢
    omega

end Lattice

namespace Lattice.OrthogonalDecomposition

/-- Componentwise pairing bounds in a two-block orthogonal decomposition
put the sum of the two selected vectors in O'Meara's intrinsic scale
truncation.  This is the basis-free assembly step used in Lemma 6.5(ii). -/
theorem add_mem_scaleTruncation_of_component_pairings
    (D : Lattice.OrthogonalDecomposition q L 2) (r : Int)
    (x₀ : (D.component 0).carrier) (hx₀ : x₀ ∈ (D.component 0).lattice)
    (x₁ : (D.component 1).carrier) (hx₁ : x₁ ∈ (D.component 1).lattice)
    (hpair₀ : ∀ y₀ : (D.component 0).carrier,
      y₀ ∈ (D.component 0).lattice →
        q.bilin (x₀ : V) (y₀ : V) ∈ Lattice.powerIdeal (K := K) r)
    (hpair₁ : ∀ y₁ : (D.component 1).carrier,
      y₁ ∈ (D.component 1).lattice →
        q.bilin (x₁ : V) (y₁ : V) ∈ Lattice.powerIdeal (K := K) r) :
    (x₀ : V) + (x₁ : V) ∈ Lattice.scaleTruncation q L r := by
  let f := D.pairProductLatticeIsometry
  have hxProduct : (x₀, x₁) ∈
      Lattice.product (D.component 0).lattice (D.component 1).lattice :=
    Lattice.mem_product_iff.mpr ⟨hx₀, hx₁⟩
  have hxL : (x₀ : V) + (x₁ : V) ∈ L := by
    have hmap := (f.map_mem (x₀, x₁)).1 hxProduct
    change D.pairToAmbientLinearEquiv (x₀, x₁) ∈ L at hmap
    exact hmap
  apply Lattice.mem_scaleTruncation_of_pairing_mem_powerIdeal hxL
  intro y hy
  let z := f.toLinearEquiv.symm y
  have hzProduct : z ∈
      Lattice.product (D.component 0).lattice (D.component 1).lattice := by
    exact (f.symm.map_mem y).1 hy
  have hz := Lattice.mem_product_iff.mp hzProduct
  have hyEq : (z.1 : V) + (z.2 : V) = y := by
    change f.toLinearEquiv z = y
    exact f.toLinearEquiv.apply_symm_apply y
  rw [← hyEq, LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.add_right,
    D.orthogonal 0 1 (by decide) x₀ z.2,
    D.orthogonal 1 0 (by decide) x₁ z.1]
  simp only [add_zero, zero_add]
  exact (Lattice.powerIdeal (K := K) r).add_mem
    (hpair₀ z.1 hz.1) (hpair₁ z.2 hz.2)

/-- Unary-head specialization of the preceding assembly lemma.  A deep
quadratic value in the unary component is paired with the ordinary norm
bound of that component; the complementary component is controlled by its
scale ideal. -/
theorem add_mem_scaleTruncation_of_unary_first
    (D : Lattice.OrthogonalDecomposition q L 2)
    (r sx sy : Int)
    (hfin : finrank K (D.component 0).carrier = 1)
    (x₀ : (D.component 0).carrier) (hx₀ : x₀ ∈ (D.component 0).lattice)
    (x₁ : (D.component 1).carrier) (hx₁ : x₁ ∈ (D.component 1).lattice)
    (hqx₀ : (D.component 0).space.quadratic x₀ ∈
      Lattice.powerIdeal (K := K) sx)
    (hnorm₀ : Lattice.normIdeal (D.component 0).space
        (D.component 0).lattice ≤ Lattice.powerIdeal (K := K) sy)
    (hscale₁ : Lattice.scaleIdeal (D.component 1).space
        (D.component 1).lattice ≤ Lattice.powerIdeal (K := K) r)
    (hsum : 2 * r ≤ sx + sy) :
    (x₀ : V) + (x₁ : V) ∈ Lattice.scaleTruncation q L r := by
  apply D.add_mem_scaleTruncation_of_component_pairings r x₀ hx₀ x₁ hx₁
  · intro y₀ hy₀
    have hqy₀ : (D.component 0).space.quadratic y₀ ∈
        Lattice.powerIdeal (K := K) sy :=
      hnorm₀ (Lattice.quadratic_mem_normIdeal_of_mem
        (D.component 0).space (D.component 0).lattice hy₀)
    exact BONG.bilin_mem_powerIdeal_of_finrank_eq_one_of_sum
      (D.component 0).space hfin r sx sy x₀ y₀ hqx₀ hqy₀ hsum
  · intro y₁ hy₁
    exact hscale₁ (Lattice.bilin_mem_scaleIdeal_of_mem
      (D.component 1).space (D.component 1).lattice hx₁ hy₁)

end Lattice.OrthogonalDecomposition

namespace BONG

/-- A vector of the left component lattice is an ambient lattice vector. -/
theorem TwoBlockSplitWitness.coe_left_mem
    {m cut : Nat} {b : BONG V q L m} {hcut : cut ≤ m}
    (S : TwoBlockSplitWitness b cut hcut)
    (x : S.left.carrier) (hx : x ∈ S.left.lattice) :
    (x : V) ∈ L := by
  have hpair : (x, 0) ∈
      Lattice.product S.left.lattice S.right.lattice :=
    Lattice.mem_product_iff.mpr ⟨hx, S.right.lattice.zero_mem⟩
  have hmap := (S.toProductLatticeIsometry.map_mem (x, 0)).1 hpair
  change (x : V) + 0 ∈ L at hmap
  simpa using hmap

/-- A vector of the right component lattice is an ambient lattice vector. -/
theorem TwoBlockSplitWitness.coe_right_mem
    {m cut : Nat} {b : BONG V q L m} {hcut : cut ≤ m}
    (S : TwoBlockSplitWitness b cut hcut)
    (x : S.right.carrier) (hx : x ∈ S.right.lattice) :
    (x : V) ∈ L := by
  have hpair : (0, x) ∈
      Lattice.product S.left.lattice S.right.lattice :=
    Lattice.mem_product_iff.mpr ⟨S.left.lattice.zero_mem, hx⟩
  have hmap := (S.toProductLatticeIsometry.map_mem (0, x)).1 hpair
  change (0 : V) + (x : V) ∈ L at hmap
  simpa using hmap

/-- Ambient membership of a vector already in the left carrier is
equivalent to membership in the left component lattice. -/
theorem TwoBlockSplitWitness.left_mem_of_coe_mem
    {m cut : Nat} {b : BONG V q L m} {hcut : cut ≤ m}
    (S : TwoBlockSplitWitness b cut hcut)
    (x : S.left.carrier) (hx : (x : V) ∈ L) :
    x ∈ S.left.lattice := by
  let f := S.toProductLatticeIsometry
  have hproduct : f.toLinearEquiv.symm (x : V) ∈
      Lattice.product S.left.lattice S.right.lattice :=
    (f.symm.map_mem (x : V)).1 hx
  have heq : f.toLinearEquiv.symm (x : V) = (x, 0) := by
    apply f.toLinearEquiv.injective
    rw [f.toLinearEquiv.apply_symm_apply]
    change (x : V) = (x : V) + 0
    simp
  rw [heq, Lattice.mem_product_iff] at hproduct
  exact hproduct.1

/-- The analogous carrier-to-lattice principle for the right component. -/
theorem TwoBlockSplitWitness.right_mem_of_coe_mem
    {m cut : Nat} {b : BONG V q L m} {hcut : cut ≤ m}
    (S : TwoBlockSplitWitness b cut hcut)
    (x : S.right.carrier) (hx : (x : V) ∈ L) :
    x ∈ S.right.lattice := by
  let f := S.toProductLatticeIsometry
  have hproduct : f.toLinearEquiv.symm (x : V) ∈
      Lattice.product S.left.lattice S.right.lattice :=
    (f.symm.map_mem (x : V)).1 hx
  have heq : f.toLinearEquiv.symm (x : V) = (0, x) := by
    apply f.toLinearEquiv.injective
    rw [f.toLinearEquiv.apply_symm_apply]
    change (x : V) = 0 + (x : V)
    simp
  rw [heq, Lattice.mem_product_iff] at hproduct
  exact hproduct.2

/-- At the first cut, the head of the left unary segment is the head of the
ambient BONG. -/
theorem TwoBlockSplitWitness.coe_left_head_eq_head_of_cut_one
    {m : Nat} {b : BONG V q L (m + 1)}
    (S : TwoBlockSplitWitness b 1 (by omega)) :
    (S.left.bong.head : V) = b.head := by
  calc
    (S.left.bong.head : V) =
        (S.left.bong.ambientVector 0 : V) := by
          rw [S.left.bong.ambientVector_zero_eq_head]
    _ = b.ambientVector (S.left.sourceIndex 0) :=
      S.left.ambientVector_eq 0
    _ = b.head := by
      have hindex : S.left.sourceIndex 0 = (0 : Fin (m + 1)) := by
        apply Fin.ext
        simp [SegmentWitness.sourceIndex]
      rw [hindex, b.ambientVector_zero_eq_head]

/-- The right carrier at the first cut is contained in the orthogonal
complement of the ambient BONG head. -/
theorem TwoBlockSplitWitness.right_mem_vectorOrthogonal_head_of_cut_one
    {m : Nat} {b : BONG V q L (m + 1)}
    (S : TwoBlockSplitWitness b 1 (by omega))
    (y : S.right.carrier) :
    (y : V) ∈ q.vectorOrthogonal b.head := by
  rw [q.mem_vectorOrthogonal_iff,
    ← S.coe_left_head_eq_head_of_cut_one]
  exact S.left_right_orthogonal S.left.bong.head y

/-- The same head identification for the initial binary cut. -/
theorem TwoBlockSplitWitness.coe_left_head_eq_head_of_cut_two
    {m : Nat} {b : BONG V q L (m + 2)}
    (S : TwoBlockSplitWitness b 2 (by omega)) :
    (S.left.bong.head : V) = b.head := by
  calc
    (S.left.bong.head : V) =
        (S.left.bong.ambientVector 0 : V) := by
          rw [S.left.bong.ambientVector_zero_eq_head]
    _ = b.ambientVector (S.left.sourceIndex 0) :=
      S.left.ambientVector_eq 0
    _ = b.head := by
      have hindex : S.left.sourceIndex 0 = (0 : Fin (m + 2)) := by
        apply Fin.ext
        simp [SegmentWitness.sourceIndex]
      rw [hindex, b.ambientVector_zero_eq_head]

/-- The complementary carrier at the initial binary cut is orthogonal to
the ambient BONG head. -/
theorem TwoBlockSplitWitness.right_mem_vectorOrthogonal_head_of_cut_two
    {m : Nat} {b : BONG V q L (m + 2)}
    (S : TwoBlockSplitWitness b 2 (by omega))
    (y : S.right.carrier) :
    (y : V) ∈ q.vectorOrthogonal b.head := by
  rw [q.mem_vectorOrthogonal_iff,
    ← S.coe_left_head_eq_head_of_cut_two]
  exact S.left_right_orthogonal S.left.bong.head y

/-- At a unary first cut, the second product coordinate is the intrinsic
orthogonal projection to the complement of the BONG head. -/
theorem TwoBlockSplitWitness.coe_projection_eq_rightCoordinate_of_cut_one
    {m : Nat} {b : BONG V q L (m + 1)}
    (S : TwoBlockSplitWitness b 1 (by omega)) (z : V) :
    (q.projectionToOrthogonal b.head b.head_isAnisotropic z : V) =
      ((S.toProductLatticeIsometry.toLinearEquiv.symm z).2 : V) := by
  let xy := S.toProductLatticeIsometry.toLinearEquiv.symm z
  have hdecomp : (xy.1 : V) + (xy.2 : V) = z := by
    change S.toProductLatticeIsometry.toLinearEquiv xy = z
    exact S.toProductLatticeIsometry.toLinearEquiv.apply_symm_apply z
  have hleftHead : (S.left.bong.head : V) = b.head :=
    S.coe_left_head_eq_head_of_cut_one
  have hleftNe : S.left.bong.head ≠ 0 := by
    intro hzero
    apply S.left.bong.head_isAnisotropic
    rw [hzero]
    simp
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' S.left.bong.head hleftNe).mp
      S.left.bong.length_eq_finrank.symm xy.1
  have hcAmbient : (xy.1 : V) = c • (S.left.bong.head : V) := by
    exact congrArg (fun w : S.left.carrier ↦ (w : V)) hc.symm
  have hprojLeft : q.orthogonalProjection b.head (xy.1 : V) = 0 := by
    rw [hcAmbient, hleftHead,
      map_smul, q.orthogonalProjection_self b.head_isAnisotropic, smul_zero]
  have hrightMem : (xy.2 : V) ∈ q.vectorOrthogonal b.head := by
    rw [q.mem_vectorOrthogonal_iff]
    rw [← hleftHead]
    exact S.left_right_orthogonal S.left.bong.head xy.2
  have hprojRight : q.orthogonalProjection b.head (xy.2 : V) =
      (xy.2 : V) := q.orthogonalProjection_eq_self hrightMem
  change q.orthogonalProjection b.head z = (xy.2 : V)
  rw [← hdecomp, map_add, hprojLeft, hprojRight, zero_add]

/-- Multiplying every vector of the parent lattice by the same
uniformizer power lands in any witness which rescales only its head by that
power.  The exact carrier theorem from Lemma 6.1 makes this independent of
the particular realization of the witness. -/
theorem HeadRescaleWitness.uniformizerPower_smul_mem
    {m k : Nat} {b : BONG V q L (m + 2)}
    (w : b.HeadRescaleWitness k) (y : V) (hy : y ∈ L) :
    ((uniformizerPowerUnit K (k : Int) : Kˣ) : K) • y ∈ w.lattice := by
  rw [w.mem_lattice_iff_ord_ge_head_depth]
  constructor
  · let aO : IntegerRing K :=
      ⟨(uniformizerPowerUnit K (k : Int) : K),
        uniformizerPowerUnit_nat_mem_integerRing k⟩
    exact L.smul_mem aO hy
  · have hyIdeal := Lattice.quadratic_mem_normIdeal_of_mem q L hy
    rw [b.head_isNormGenerator.normIdeal_eq,
      ← b.value_zero_eq_quadratic_head] at hyIdeal
    have hyOrder : (b.order 0 : WithTop Int) ≤
        ord K (q.quadratic y) := by
      rw [b.coe_order]
      exact Lattice.ord_le_of_mem_principalIdeal
        (b.value_ne_zero 0) hyIdeal
    have hpowerOrder :
        ord K (((uniformizerPowerUnit K (k : Int) : Kˣ) : K) ^ 2) =
          ((2 * (k : Int) : Int) : WithTop Int) := by
      rw [ord_pow, ← coe_ordUnit, ordUnit_uniformizerPowerUnit]
      norm_cast
    rw [q.quadratic_smul, ord_mul, hpowerOrder]
    have hshift := add_le_add_left hyOrder
      ((2 * (k : Int) : Int) : WithTop Int)
    have hthreshold :
        ((b.order 0 + 2 * (k : Int) - 1 : Int) : WithTop Int) ≤
          ((2 * (k : Int) : Int) : WithTop Int) +
            (b.order 0 : WithTop Int) := by
      norm_cast
      omega
    exact hthreshold.trans (by simpa only [add_comm] using hshift)

/-- The low-order alternatives in Beli's Lemma 3.17 all have even order. -/
theorem even_ordUnit_of_hasSomeEqualNormGeneratorBasis_of_le_two_e
    [QuadraticDefectLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicSquareDifferenceLaws K]
    (a : Kˣ) (ha : IsBinaryParameterAdmissible a)
    (hsome : HasSomeEqualNormGeneratorBasis a)
    (hupper : ordUnit K a ≤ 2 * (ramificationIndex K : Int)) :
    Even (ordUnit K a) := by
  let R : Int := ordUnit K a
  let ε : Kˣ := normalizedUnitPart K a
  have hε : IsValuationUnit K (ε : K) := by
    simpa only [ε] using normalizedUnitPart_isValuationUnit K a
  have hfactor : uniformizerPowerUnit K R * ε = a := by
    simpa only [R, ε] using uniformizerPower_mul_normalizedUnitPart K a
  have ha' : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε) := by
    rwa [hfactor]
  have hsome' : HasSomeEqualNormGeneratorBasis
      (uniformizerPowerUnit K R * ε) := by
    rwa [hfactor]
  have hall : HasEveryEqualNormGeneratorBasis
      (uniformizerPowerUnit K R * ε) :=
    (hasSomeEqualNormGeneratorBasis_iff_hasEvery
      (uniformizerPowerUnit K R * ε) ha').1 hsome'
  have hcases : BeliLemma317ParameterCases (K := K) R ε :=
    beliLemma317ParameterCases_of_hasEvery R ε hε ha' hall
  have horder : ordUnit K (uniformizerPowerUnit K R * ε) = R :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have hRupper : R ≤ 2 * (ramificationIndex K : Int) := by
    rw [hfactor] at horder
    simpa only [R] using hupper
  simp only [BeliLemma317ParameterCases] at hcases
  rcases hcases with hhigh | hboundary | hinterior | hendpoint
  · omega
  · rcases hboundary with ⟨_, hR⟩
    refine ⟨(ramificationIndex K : Int) -
      ((quadraticDefect K (-ε)).toNat : Int), ?_⟩
    omega
  · exact hinterior.2.2.1
  · rcases hendpoint.1 with hR | hquarter
    · refine ⟨ramificationIndex K, ?_⟩
      omega
    · have hord := ordUnit_eq_of_unitSquareClass_eq (K := K) hquarter
      rw [horder, ordUnit_negativeQuarterUnit] at hord
      refine ⟨-(ramificationIndex K : Int), ?_⟩
      omega

/-- At even order, removing the uniformizer power does not change Beli's
parameter defect. -/
theorem beliParameterDefect_eq_normalizedUnitPart_of_even
    [QuadraticDefectLaws K] (a : Kˣ) (heven : Even (ordUnit K a)) :
    quadraticDefect K (-a) =
      quadraticDefect K (-(normalizedUnitPart K a)) := by
  let ε : Kˣ := normalizedUnitPart K a
  have hε : IsValuationUnit K (ε : K) :=
    normalizedUnitPart_isValuationUnit K a
  have hfactor : uniformizerPowerUnit K (ordUnit K a) * ε = a := by
    simpa only [ε] using uniformizerPower_mul_normalizedUnitPart K a
  have h := beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
    (K := K) (ordUnit K a) ε hε heven
  rw [hfactor] at h
  exact h

/-- Two nonzero elements of the same valuation whose difference is `m`
orders deeper have quotient defect at least `m`. -/
theorem quadraticDefect_div_ge_of_sub_order
    [QuadraticDefectLaws K] (u v : Kˣ) (m : Nat)
    (hord : ordUnit K u = ordUnit K v)
    (hsub : ((ordUnit K u + (m : Int) : Int) : WithTop Int) ≤
      ord K ((u : K) - (v : K))) :
    (m : ℕ∞) ≤ quadraticDefect K (u * v⁻¹) := by
  apply natCast_le_quadraticDefect K
  refine ⟨1, ?_⟩
  have heq :
      1 - (1 : K) ^ 2 / ((u * v⁻¹ : Kˣ) : K) =
        ((u : K) - (v : K)) / (u : K) := by
    simp only [one_pow, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero u, Units.ne_zero v]
  rw [heq, div_eq_mul_inv, ord_mul, AddValuation.map_inv]
  by_cases hdiff : (u : K) - (v : K) = 0
  · simp [hdiff]
  · let error : Kˣ := Units.mk0 ((u : K) - (v : K)) hdiff
    have herror : ord K ((u : K) - (v : K)) =
        (ordUnit K error : WithTop Int) := by
      simpa only [error, Units.val_mk0] using (coe_ordUnit K error).symm
    rw [herror] at hsub
    rw [herror, (coe_ordUnit K u).symm]
    norm_cast at hsub ⊢
    omega

/-- If `ord(1-a^2)=g≤2e` and `g` is even, both linear factors have
order `g/2`.  This is the valuation calculation in the middle of Beli's
proof of Lemma 6.5. -/
theorem ord_one_sub_and_add_eq_half_of_order_one_sub_sq
    (a : K) (g : Int) (heven : Even g)
    (hupper : g ≤ 2 * (ramificationIndex K : Int))
    (horder : ord K (1 - a ^ 2) = (g : WithTop Int)) :
    ord K (1 - a) = ((g / 2 : Int) : WithTop Int) ∧
      ord K (1 + a) = ((g / 2 : Int) : WithTop Int) := by
  have hfactorNe : 1 - a ^ 2 ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero] at horder
    exact WithTop.top_ne_coe horder
  have hfactor : (1 - a) * (1 + a) = 1 - a ^ 2 := by ring
  have hmulNe : (1 - a) * (1 + a) ≠ 0 := by
    rwa [hfactor]
  have hminusNe : 1 - a ≠ 0 := (mul_ne_zero_iff.mp hmulNe).1
  have hplusNe : 1 + a ≠ 0 := (mul_ne_zero_iff.mp hmulNe).2
  let minus : Kˣ := Units.mk0 (1 - a) hminusNe
  let plus : Kˣ := Units.mk0 (1 + a) hplusNe
  have hminusOrder : ord K (1 - a) =
      (ordUnit K minus : WithTop Int) := by
    simpa only [minus, Units.val_mk0] using (coe_ordUnit K minus).symm
  have hplusOrder : ord K (1 + a) =
      (ordUnit K plus : WithTop Int) := by
    simpa only [plus, Units.val_mk0] using (coe_ordUnit K plus).symm
  have hsum : ordUnit K minus + ordUnit K plus = g := by
    have h := congrArg (ord K) hfactor
    rw [ord_mul, horder, hminusOrder, hplusOrder] at h
    exact WithTop.coe_injective h
  have hhalfUpper : g / 2 ≤ (ramificationIndex K : Int) := by
    rcases heven with ⟨r, hr⟩
    omega
  have hminusLower : g / 2 ≤ ordUnit K minus := by
    by_contra hnot
    have hminusLtHalf : ordUnit K minus < g / 2 := lt_of_not_ge hnot
    have hminusLtE : ordUnit K minus < (ramificationIndex K : Int) :=
      lt_of_lt_of_le hminusLtHalf hhalfUpper
    have hminusLtTwo : ord K (1 - a) < ord K (2 : K) := by
      rw [hminusOrder, ← ramificationIndex_spec]
      exact_mod_cast hminusLtE
    have hplusEq : ord K (1 + a) = ord K (1 - a) := by
      have hid : (1 + a : K) = 2 - (1 - a) := by ring
      rw [hid]
      exact (ord K).map_sub_eq_of_lt_right hminusLtTwo
    have hplusUnitEq : ordUnit K plus = ordUnit K minus := by
      apply WithTop.coe_injective
      simpa only [hplusOrder, hminusOrder] using hplusEq
    rcases heven with ⟨r, hr⟩
    omega
  have hplusLower : g / 2 ≤ ordUnit K plus := by
    by_contra hnot
    have hplusLtHalf : ordUnit K plus < g / 2 := lt_of_not_ge hnot
    have hplusLtE : ordUnit K plus < (ramificationIndex K : Int) :=
      lt_of_lt_of_le hplusLtHalf hhalfUpper
    have hplusLtTwo : ord K (1 + a) < ord K (2 : K) := by
      rw [hplusOrder, ← ramificationIndex_spec]
      exact_mod_cast hplusLtE
    have hminusEq : ord K (1 - a) = ord K (1 + a) := by
      have hid : (1 - a : K) = 2 - (1 + a) := by ring
      rw [hid]
      exact (ord K).map_sub_eq_of_lt_right hplusLtTwo
    have hminusUnitEq : ordUnit K minus = ordUnit K plus := by
      apply WithTop.coe_injective
      simpa only [hminusOrder, hplusOrder] using hminusEq
    rcases heven with ⟨r, hr⟩
    omega
  have hminusEqHalf : ordUnit K minus = g / 2 := by
    rcases heven with ⟨r, hr⟩
    omega
  have hplusEqHalf : ordUnit K plus = g / 2 := by
    rcases heven with ⟨r, hr⟩
    omega
  constructor
  · rw [hminusOrder, hminusEqHalf]
  · rw [hplusOrder, hplusEqHalf]

/-- If `ord(1-a²)` is strictly above an even `g ≤ 2e`, both linear
factors have order at least `g/2`, and at least one is strictly deeper. -/
theorem ord_one_sub_or_add_gt_half_of_order_one_sub_sq_gt
    (a : K) (g : Int) (heven : Even g)
    (hupper : g ≤ 2 * (ramificationIndex K : Int))
    (horder : ((g + 1 : Int) : WithTop Int) ≤ ord K (1 - a ^ 2)) :
    (((g / 2 : Int) : WithTop Int) < ord K (1 - a) ∧
        ((g / 2 : Int) : WithTop Int) ≤ ord K (1 + a)) ∨
      (((g / 2 : Int) : WithTop Int) ≤ ord K (1 - a) ∧
        ((g / 2 : Int) : WithTop Int) < ord K (1 + a)) := by
  have hhalfUpper : g / 2 ≤ (ramificationIndex K : Int) := by
    rcases heven with ⟨r, hr⟩
    omega
  by_cases hminusZero : 1 - a = 0
  · left
    constructor
    · rw [hminusZero, ord_zero]
      exact WithTop.coe_lt_top _
    · have hplus : (1 + a : K) = 2 := by
        have ha : a = 1 := by linear_combination -hminusZero
        rw [ha]
        norm_num
      rw [hplus, ← ramificationIndex_spec]
      exact_mod_cast hhalfUpper
  by_cases hplusZero : 1 + a = 0
  · right
    constructor
    · have hminus : (1 - a : K) = 2 := by
        have ha : a = -1 := by linear_combination hplusZero
        rw [ha]
        norm_num
      rw [hminus, ← ramificationIndex_spec]
      exact_mod_cast hhalfUpper
    · rw [hplusZero, ord_zero]
      exact WithTop.coe_lt_top _
  let minus : Kˣ := Units.mk0 (1 - a) hminusZero
  let plus : Kˣ := Units.mk0 (1 + a) hplusZero
  have hminusOrder : ord K (1 - a) =
      (ordUnit K minus : WithTop Int) := by
    simpa only [minus, Units.val_mk0] using (coe_ordUnit K minus).symm
  have hplusOrder : ord K (1 + a) =
      (ordUnit K plus : WithTop Int) := by
    simpa only [plus, Units.val_mk0] using (coe_ordUnit K plus).symm
  have hfactor : (1 - a) * (1 + a) = 1 - a ^ 2 := by ring
  have hsumLower : g + 1 ≤ ordUnit K minus + ordUnit K plus := by
    rw [← hfactor, ord_mul, hminusOrder, hplusOrder] at horder
    exact_mod_cast horder
  have hminusLower : g / 2 ≤ ordUnit K minus := by
    by_contra hnot
    have hminusLtHalf : ordUnit K minus < g / 2 := lt_of_not_ge hnot
    have hminusLtE : ordUnit K minus < (ramificationIndex K : Int) :=
      lt_of_lt_of_le hminusLtHalf hhalfUpper
    have hminusLtTwo : ord K (1 - a) < ord K (2 : K) := by
      rw [hminusOrder, ← ramificationIndex_spec]
      exact_mod_cast hminusLtE
    have hplusEq : ord K (1 + a) = ord K (1 - a) := by
      have hid : (1 + a : K) = 2 - (1 - a) := by ring
      rw [hid]
      exact (ord K).map_sub_eq_of_lt_right hminusLtTwo
    have hplusUnitEq : ordUnit K plus = ordUnit K minus := by
      apply WithTop.coe_injective
      simpa only [hplusOrder, hminusOrder] using hplusEq
    rcases heven with ⟨r, hr⟩
    omega
  have hplusLower : g / 2 ≤ ordUnit K plus := by
    by_contra hnot
    have hplusLtHalf : ordUnit K plus < g / 2 := lt_of_not_ge hnot
    have hplusLtE : ordUnit K plus < (ramificationIndex K : Int) :=
      lt_of_lt_of_le hplusLtHalf hhalfUpper
    have hplusLtTwo : ord K (1 + a) < ord K (2 : K) := by
      rw [hplusOrder, ← ramificationIndex_spec]
      exact_mod_cast hplusLtE
    have hminusEq : ord K (1 - a) = ord K (1 + a) := by
      have hid : (1 - a : K) = 2 - (1 + a) := by ring
      rw [hid]
      exact (ord K).map_sub_eq_of_lt_right hplusLtTwo
    have hminusUnitEq : ordUnit K minus = ordUnit K plus := by
      apply WithTop.coe_injective
      simpa only [hminusOrder, hplusOrder] using hminusEq
    rcases heven with ⟨r, hr⟩
    omega
  have hstrict : g / 2 < ordUnit K minus ∨
      g / 2 < ordUnit K plus := by
    rcases heven with ⟨r, hr⟩
    omega
  rcases hstrict with hminusStrict | hplusStrict
  · left
    rw [hminusOrder, hplusOrder]
    exact ⟨by exact_mod_cast hminusStrict,
      by exact_mod_cast hplusLower⟩
  · right
    rw [hminusOrder, hplusOrder]
    exact ⟨by exact_mod_cast hminusLower,
      by exact_mod_cast hplusStrict⟩

/-- Rescaling the second vector by a nonnegative uniformizer power preserves
binary admissibility of the first parameter. -/
theorem headSecondRescaledParameter_isBinaryParameterAdmissible
    (b : BONG V q L (n + 3)) (k : Nat) :
    IsBinaryParameterAdmissible (b.headSecondRescaledParameter k) := by
  unfold headSecondRescaledParameter
  exact
    (b.adjacentParameter_isBinaryParameterAdmissible 0 (by simp)).mul_integral_square
      (uniformizerPowerUnit_nat_mem_integerRing k)

/-- All second-vector rescalings have one common normalized unit part; only
their order changes by `2k`. -/
theorem headSecondRescaledParameter_eq_normalized
    (b : BONG V q L (n + 3)) (k : Nat) :
    b.headSecondRescaledParameter k =
      uniformizerPowerUnit K (b.lemma62Gap + 2 * (k : Int)) *
        normalizedUnitPart K (b.adjacentParameter 0 (by simp)) := by
  let a : Kˣ := b.adjacentParameter 0 (by simp)
  let ε : Kˣ := normalizedUnitPart K a
  have horder : ordUnit K a = b.lemma62Gap :=
    b.ordUnit_adjacentParameter_zero
  have hfactor : uniformizerPowerUnit K b.lemma62Gap * ε = a := by
    rw [← horder]
    exact uniformizerPower_mul_normalizedUnitPart K a
  unfold headSecondRescaledParameter
  change a * uniformizerPowerUnit K (k : Int) ^ 2 = _
  rw [← hfactor]
  change
    (uniformizerPowerUnit K b.lemma62Gap * ε) *
        uniformizerPowerUnit K (k : Int) ^ 2 =
      uniformizerPowerUnit K (b.lemma62Gap + 2 * (k : Int)) * ε
  calc
    (uniformizerPowerUnit K b.lemma62Gap * ε) *
          uniformizerPowerUnit K (k : Int) ^ 2 =
        (uniformizerPowerUnit K b.lemma62Gap *
          uniformizerPowerUnit K (k : Int) ^ 2) * ε := by
            ac_rfl
    _ = uniformizerPowerUnit K (b.lemma62Gap + 2 * (k : Int)) * ε := by
      unfold uniformizerPowerUnit
      rw [pow_two, ← zpow_add, ← zpow_add]
      congr 2
      omega

/-- A Lemma 3.17 parameter case at the shifted order gives the corresponding
admissible second-vector rescaling. -/
theorem headSecondRescaleAdmissible_of_parameterCases
    (b : BONG V q L (n + 3)) (j : Nat)
    (hcases : BeliLemma317ParameterCases (K := K)
      (b.lemma62Gap + 2 * (j : Int))
      (normalizedUnitPart K (b.adjacentParameter 0 (by simp)))) :
    b.HeadSecondRescaleAdmissible j := by
  let ε : Kˣ := normalizedUnitPart K (b.adjacentParameter 0 (by simp))
  have hε : IsValuationUnit K (ε : K) :=
    normalizedUnitPart_isValuationUnit K _
  have hadmissible : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K (b.lemma62Gap + 2 * (j : Int)) * ε) := by
    rw [← b.headSecondRescaledParameter_eq_normalized j]
    exact b.headSecondRescaledParameter_isBinaryParameterAdmissible j
  unfold HeadSecondRescaleAdmissible
  rw [b.headSecondRescaledParameter_eq_normalized]
  exact hasSomeEqualNormGeneratorBasis_of_parameterCases
    (b.lemma62Gap + 2 * (j : Int)) ε hε hadmissible hcases

/-- Some nonnegative rescaling of the second BONG vector always reaches the
high-order alternative of Lemma 3.17 and therefore has an equal-value
norm-generator basis. -/
theorem exists_headSecondRescaleAdmissible
    (b : BONG V q L (n + 3)) :
    ∃ k : Nat, b.HeadSecondRescaleAdmissible k := by
  let threshold : Int :=
    2 * (ramificationIndex K : Int) - b.lemma62Gap + 1
  let k : Nat := Int.toNat threshold
  have hlarge : 2 * (ramificationIndex K : Int) <
      b.lemma62Gap + 2 * (k : Int) := by
    by_cases hthreshold : 0 ≤ threshold
    · rw [show (k : Int) = threshold by
        exact_mod_cast Int.toNat_of_nonneg hthreshold]
      simp only [threshold]
      omega
    · have hthresholdNonpos : threshold ≤ 0 := le_of_not_ge hthreshold
      have hk : k = 0 := by
        simp only [k]
        exact Int.toNat_eq_zero.mpr hthresholdNonpos
      rw [hk]
      norm_num
      simp only [threshold] at hthresholdNonpos
      omega
  refine ⟨k, b.headSecondRescaleAdmissible_of_parameterCases k ?_⟩
  simp only [BeliLemma317ParameterCases]
  exact Or.inl hlarge

/-- The admissible second-vector rescalings have a least exponent. -/
theorem exists_least_headSecondRescaleAdmissible
    (b : BONG V q L (n + 3)) :
    ∃ k : Nat,
      b.HeadSecondRescaleAdmissible k ∧
        ∀ j : Nat, b.HeadSecondRescaleAdmissible j → k ≤ j := by
  classical
  let hexists := b.exists_headSecondRescaleAdmissible
  refine ⟨Nat.find hexists, Nat.find_spec hexists, ?_⟩
  intro j hj
  exact Nat.find_min' hexists hj

/-- The least exponent and its minimality are canonical once the original
binary prefix is known to be nonhyperbolic.  No shifted-tail BONG is chosen at
this stage. -/
noncomputable def lemma65MinimalityData
    (b : BONG V q L (n + 3))
    (hnot : ¬b.FirstBinaryIsHyperbolic) : b.Lemma65MinimalityData := by
  classical
  let hexists := b.exists_headSecondRescaleAdmissible
  exact {
    k := Nat.find hexists
    admissible := Nat.find_spec hexists
    least := fun j hj => Nat.find_min' hexists hj
    firstBinary_not_hyperbolic := hnot
  }

namespace Lemma65MinimalityData

variable {b : BONG V q L (n + 3)}

/-- The least final parameter satisfies one of the four alternatives in
Beli's Lemma 3.17.  This numerical classification does not require a concrete
realization of the shifted tail. -/
theorem finalParameterCases (M : b.Lemma65MinimalityData) :
    BeliLemma317ParameterCases (K := K)
      (b.lemma62Gap + 2 * (M.k : Int))
      (normalizedUnitPart K (b.adjacentParameter 0 (by simp))) := by
  let R : Int := b.lemma62Gap + 2 * (M.k : Int)
  let epsilon : Kˣ := normalizedUnitPart K
    (b.adjacentParameter 0 (by simp))
  have hepsilon : IsValuationUnit K (epsilon : K) :=
    normalizedUnitPart_isValuationUnit K _
  have hparameter :
      uniformizerPowerUnit K R * epsilon =
        b.headSecondRescaledParameter M.k := by
    simpa only [R, epsilon] using
      (b.headSecondRescaledParameter_eq_normalized M.k).symm
  have hadmissible : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * epsilon) := by
    rw [hparameter]
    exact b.headSecondRescaledParameter_isBinaryParameterAdmissible M.k
  have hsome : HasSomeEqualNormGeneratorBasis
      (uniformizerPowerUnit K R * epsilon) := by
    rw [hparameter]
    exact M.admissible
  have hall : HasEveryEqualNormGeneratorBasis
      (uniformizerPowerUnit K R * epsilon) :=
    (hasSomeEqualNormGeneratorBasis_iff_hasEvery
      (uniformizerPowerUnit K R * epsilon) hadmissible).1 hsome
  simpa only [R, epsilon] using
    beliLemma317ParameterCases_of_hasEvery
      R epsilon hepsilon hadmissible hall

/-- Minimality alone reduces the high range to the first admissible order
strictly above `2e`: unless `k=0`, the final shifted gap is `2e+1` or
`2e+2`. -/
theorem highRange_k_eq_zero_or_final_eq
    (M : b.Lemma65MinimalityData) (hhigh : b.Lemma65HighRangeAt M.k) :
    M.k = 0 ∨
      b.lemma62Gap + 2 * (M.k : Int) =
        2 * (ramificationIndex K : Int) + 1 ∨
      b.lemma62Gap + 2 * (M.k : Int) =
        2 * (ramificationIndex K : Int) + 2 := by
  by_cases hkZero : M.k = 0
  · exact Or.inl hkZero
  · right
    have hkPos : 0 < M.k := Nat.pos_of_ne_zero hkZero
    let j : Nat := M.k - 1
    have hjLt : j < M.k := by omega
    have hjCast : (j : Int) = (M.k : Int) - 1 := by
      simp only [j]
      omega
    let Rprev : Int := b.lemma62Gap + 2 * (j : Int)
    have hRprevEq : Rprev =
        b.lemma62Gap + 2 * (M.k : Int) - 2 := by
      simp only [Rprev]
      rw [hjCast]
      ring
    have hRprevLe : Rprev ≤ 2 * (ramificationIndex K : Int) := by
      by_contra hnot
      have hgreater : 2 * (ramificationIndex K : Int) < Rprev :=
        lt_of_not_ge hnot
      have hcases : BeliLemma317ParameterCases (K := K) Rprev
          (normalizedUnitPart K (b.adjacentParameter 0 (by simp))) := by
        simp only [BeliLemma317ParameterCases]
        exact Or.inl hgreater
      have hadmissible : b.HeadSecondRescaleAdmissible j := by
        apply b.headSecondRescaleAdmissible_of_parameterCases j
        simpa only [Rprev] using hcases
      exact M.not_admissible_of_lt j hjLt hadmissible
    have hRHigh : 2 * (ramificationIndex K : Int) + 1 ≤
        b.lemma62Gap + 2 * (M.k : Int) := by
      change 2 * (ramificationIndex K : Int) + 1 ≤
        b.order 1 + 2 * (M.k : Int) - b.order 0 at hhigh
      unfold lemma62Gap
      omega
    omega

/-- Subtracting the even shift from the odd high endpoint preserves odd
parity of the original first gap. -/
theorem lemma62Gap_odd_of_final_eq_two_e_add_one
    (M : b.Lemma65MinimalityData)
    (hfinal : b.lemma62Gap + 2 * (M.k : Int) =
      2 * (ramificationIndex K : Int) + 1) :
    Odd b.lemma62Gap := by
  refine ⟨(ramificationIndex K : Int) - (M.k : Int), ?_⟩
  omega

/-- If the least positive shift lands at `2e+2`, the residue field has two
elements; otherwise the preceding order `2e` is already admissible. -/
theorem residue_two_of_final_eq_two_e_add_two
    (M : b.Lemma65MinimalityData) (hkNe : M.k ≠ 0)
    (hfinal : b.lemma62Gap + 2 * (M.k : Int) =
      2 * (ramificationIndex K : Int) + 2) :
    ¬HasResidueFieldMoreThanTwoElements (K := K) := by
  intro hresidue
  have hkPos : 0 < M.k := Nat.pos_of_ne_zero hkNe
  let j : Nat := M.k - 1
  have hjLt : j < M.k := by omega
  have hjCast : (j : Int) = (M.k : Int) - 1 := by
    simp only [j]
    omega
  have hRj : b.lemma62Gap + 2 * (j : Int) =
      2 * (ramificationIndex K : Int) := by
    rw [hjCast]
    omega
  have hcases : BeliLemma317ParameterCases (K := K)
      (b.lemma62Gap + 2 * (j : Int))
      (normalizedUnitPart K (b.adjacentParameter 0 (by simp))) := by
    simp only [BeliLemma317ParameterCases]
    exact Or.inr (Or.inr (Or.inr ⟨Or.inl hRj, hresidue⟩))
  exact M.not_admissible_of_lt j hjLt
    (b.headSecondRescaleAdmissible_of_parameterCases j hcases)

end Lemma65MinimalityData

/-- The projected tail needs no reconstruction at exponent zero. -/
noncomputable def tailHeadRescaleWitness_of_k_eq_zero
    (b : BONG V q L (n + 3)) (k : Nat) (hk : k = 0) :
    b.tail.HeadRescaleWitness k := by
  subst k
  exact b.tail.headRescaleWitness_zero

/-- If the rescaled second BONG order remains below the third order, the
projected-tail witness is obtained by directly adjoining the unchanged
suffix to the rescaled unary head. -/
noncomputable def tailHeadRescaleWitness_of_order_le_third
    (b : BONG V q L (n + 3)) (k : Nat)
    (hle : b.order 1 + 2 * (k : Int) ≤ b.order 2) :
    b.tail.HeadRescaleWitness k := by
  apply b.tail.headRescaleWitness_of_headOrder_le_second k
  have hzero : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
    rw [b.order_tail]
    congr 1
  have hone : b.tail.order (1 : Fin (n + 2)) = b.order 2 := by
    rw [b.order_tail]
    congr 1
  rw [hzero, hone]
  exact hle

/-- If the preceding gap `R₂-R₁` is at most `2e`, Property B prevents the
first adjacent pair of the projected tail from triggering Property B: such a
trigger would force the preceding gap to be at least `2e+1`.  The negated
trigger is exactly the numerical alternative needed in Lemma 6.1(iii). -/
theorem tail_headRescaleCriterion_of_previousGap_le_two_e
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (hprevious : b.order 1 - b.order 0 ≤
      2 * (ramificationIndex K : Int)) :
    b.tail.HeadRescaleCriterion := by
  have hnotTrigger :
      ¬b.tail.propertyBTrigger (0 : Fin (n + 1)) := by
    intro htriggerTail
    have htrigger : b.propertyBTrigger (1 : Fin (n + 2)) := by
      unfold propertyBTrigger at htriggerTail ⊢
      dsimp only at htriggerTail ⊢
      have htailLeft :
          b.tail.order (Fin.castSucc (0 : Fin (n + 1))) =
            b.order (Fin.castSucc (1 : Fin (n + 2))) := by
        rw [b.order_tail]
        congr 1
      have htailRight :
          b.tail.order (Fin.succ (0 : Fin (n + 1))) =
            b.order (Fin.succ (1 : Fin (n + 2))) := by
        rw [b.order_tail]
        congr 1
      have htailDefect :
          b.tail.normalizedAdjacentDefectOrder (0 : Fin (n + 1)) =
            b.normalizedAdjacentDefectOrder (1 : Fin (n + 2)) := by
        simpa using b.normalizedAdjacentDefectOrder_tail
          (0 : Fin (n + 1))
      rwa [htailLeft, htailRight, htailDefect] at htriggerTail
    have hleft := (hB.2 (1 : Fin (n + 2)) htrigger).1
      (0 : Fin (n + 3)) (by simp)
    have hlarge : 2 * (ramificationIndex K : Int) + 1 ≤
        b.order 1 - b.order 0 := by
      simpa using hleft
    omega
  have hcases := b.tail.not_propertyBTrigger_iff_large_or_even_high
    (0 : Fin (n + 1)) hnotTrigger
  have hlower : -(2 * (ramificationIndex K : Int)) <
      b.tail.order (1 : Fin (n + 2)) -
        b.tail.order (0 : Fin (n + 2)) := by
    have htwoStep : b.order 0 < b.order 2 :=
      hB.hasPropertyA (0 : Fin (n + 3)) (by simp)
    rw [b.order_tail, b.order_tail]
    change -(2 * (ramificationIndex K : Int)) < b.order 2 - b.order 1
    omega
  unfold HeadRescaleCriterion
  rcases hcases with hlarge | ⟨heven, _hupper, hdefect⟩
  · exact Or.inl (le_of_lt hlarge)
  · exact Or.inr ⟨hlower, heven, hdefect⟩

/-- Under the same preceding-gap bound, Lemma 6.1 constructs the literal
once-rescaled projected-tail BONG.  Property B supplies the only possible
two-step order bound needed to attach the unchanged suffix. -/
noncomputable def tailHeadRescaleWitness_one_of_previousGap_le_two_e
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (hprevious : b.order 1 - b.order 0 ≤
      2 * (ramificationIndex K : Int)) :
    b.tail.HeadRescaleWitness 1 := by
  classical
  let hcriterion :=
    b.tail_headRescaleCriterion_of_previousGap_le_two_e hB hprevious
  let binary : b.tail.HeadBinaryRescaleWitness 1 :=
    Classical.choice
      (b.tail.headBinaryRescaleExists_of_criterion_proved hcriterion)
  apply b.tail.headRescaleWitness_of_binary 1 binary
  intro hn
  cases n with
  | zero => omega
  | succ m =>
      rw [b.order_tail, b.order_tail]
      let i : Fin (m + 4) := ⟨1, by omega⟩
      let j : Fin (m + 4) := ⟨3, by omega⟩
      change b.order i + 2 ≤ b.order j
      have hi : i.1 + 2 < m + 4 := by simp [i]
      have htwoStep := hB.twoStep_add_two_le i hi
      have hidx : (⟨i.1 + 2, hi⟩ : Fin (m + 4)) = j := by
        apply Fin.ext
        simp [i, j]
      rw [hidx] at htwoStep
      exact htwoStep

/-- Ambient hyperbolic-plane containment in a quadratic sublattice is the
same concrete containment after restricting the quadratic space to its
carrier.  We extract integral isotropic generators from the given lattice
isometry, retain their integral coordinates in the component lattice, and
reconstruct the intrinsic pair with Lemma 3.19. -/
theorem containsScaledHyperbolicPlane_restrict
    (C : Lattice.QuadraticSublattice q) (r : Int)
    (hH : C.ContainsScaledHyperbolicPlane r) :
    Lattice.ContainsScaledHyperbolicPlane C.space C.lattice r := by
  classical
  rcases hH with ⟨x, y, hx, hy, hxy⟩
  rcases hxy with ⟨hli, hnondeg, ⟨f⟩⟩
  let e₀ : Fin 2 → K := Pi.single 0 1
  let e₁ : Fin 2 → K := Pi.single 1 1
  let u' : binaryPairSpan (K := K) (x : V) (y : V) :=
    f.toLinearEquiv.symm e₀
  let w' : binaryPairSpan (K := K) (x : V) (y : V) :=
    f.toLinearEquiv.symm e₁
  have he₀ : e₀ ∈ Lattice.hyperbolicPlaneLattice (K := K) := by
    rw [Lattice.hyperbolicPlaneLattice,
      Lattice.mem_basisLattice_iff_repr_mem_integerRing]
    simp [e₀]
  have he₁ : e₁ ∈ Lattice.hyperbolicPlaneLattice (K := K) := by
    rw [Lattice.hyperbolicPlaneLattice,
      Lattice.mem_basisLattice_iff_repr_mem_integerRing]
    simp [e₁]
  have hu' : u' ∈ Lattice.basisLattice
      (binaryPairBasis (K := K) (x : V) (y : V) hli) := by
    apply (f.map_mem u').2
    simpa [u'] using he₀
  have hw' : w' ∈ Lattice.basisLattice
      (binaryPairBasis (K := K) (x : V) (y : V) hli) := by
    apply (f.map_mem w').2
    simpa [w'] using he₁
  have hspanLe : binaryPairSpan (K := K) (x : V) (y : V) ≤
      C.carrier := by
    rw [binaryPairSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact x.property
    · exact y.property
  let liftToCarrier
      (z : binaryPairSpan (K := K) (x : V) (y : V)) : C.carrier :=
    ⟨(z : V), hspanLe z.property⟩
  have lift_mem : ∀ z : binaryPairSpan (K := K) (x : V) (y : V),
      z ∈ Lattice.basisLattice
          (binaryPairBasis (K := K) (x : V) (y : V) hli) →
        liftToCarrier z ∈ C.lattice := by
    intro z hz
    let pairBasis := binaryPairBasis (K := K) (x : V) (y : V) hli
    have hzcoord :=
      (Lattice.mem_basisLattice_iff_repr_mem_integerRing pairBasis z).1 hz
    have hsum := pairBasis.sum_repr z
    rw [Fin.sum_univ_two] at hsum
    have hzero : (pairBasis.repr z 0) • x ∈ C.lattice := by
      exact C.lattice.smul_mem ⟨pairBasis.repr z 0, hzcoord 0⟩ hx
    have hone : (pairBasis.repr z 1) • y ∈ C.lattice := by
      exact C.lattice.smul_mem ⟨pairBasis.repr z 1, hzcoord 1⟩ hy
    have hadd := C.lattice.add_mem hzero hone
    have hsumCoe := congrArg
      (Submodule.subtype
        (binaryPairSpan (K := K) (x : V) (y : V))) hsum
    have hsumCarrier :
        (pairBasis.repr z 0) • x + (pairBasis.repr z 1) • y =
          liftToCarrier z := by
      apply Subtype.ext
      change (pairBasis.repr z 0) • (x : V) +
          (pairBasis.repr z 1) • (y : V) = (z : V)
      have hzero : ((pairBasis 0 :
          binaryPairSpan (K := K) (x : V) (y : V)) : V) = (x : V) := by
        simp [pairBasis]
      have hone : ((pairBasis 1 :
          binaryPairSpan (K := K) (x : V) (y : V)) : V) = (y : V) := by
        simp [pairBasis]
      have htermZero : (pairBasis.repr z 0) • (x : V) =
          (pairBasis.repr z 0) •
            ((pairBasis 0 :
              binaryPairSpan (K := K) (x : V) (y : V)) : V) :=
        congrArg (fun t : V ↦ (pairBasis.repr z 0) • t) hzero.symm
      have htermOne : (pairBasis.repr z 1) • (y : V) =
          (pairBasis.repr z 1) •
            ((pairBasis 1 :
              binaryPairSpan (K := K) (x : V) (y : V)) : V) :=
        congrArg (fun t : V ↦ (pairBasis.repr z 1) • t) hone.symm
      rw [htermZero, htermOne]
      change (pairBasis.repr z 0) •
            (Submodule.subtype
              (binaryPairSpan (K := K) (x : V) (y : V))) (pairBasis 0) +
          (pairBasis.repr z 1) •
            (Submodule.subtype
              (binaryPairSpan (K := K) (x : V) (y : V))) (pairBasis 1) =
        (Submodule.subtype
          (binaryPairSpan (K := K) (x : V) (y : V))) z
      calc
        (pairBasis.repr z 0) •
              (Submodule.subtype
                (binaryPairSpan (K := K) (x : V) (y : V))) (pairBasis 0) +
            (pairBasis.repr z 1) •
              (Submodule.subtype
                (binaryPairSpan (K := K) (x : V) (y : V))) (pairBasis 1) =
            (Submodule.subtype
              (binaryPairSpan (K := K) (x : V) (y : V)))
              ((pairBasis.repr z 0) • pairBasis 0 +
                (pairBasis.repr z 1) • pairBasis 1) := by
          rw [map_add, map_smul, map_smul]
        _ = (Submodule.subtype
              (binaryPairSpan (K := K) (x : V) (y : V))) z := hsumCoe
    rwa [← hsumCarrier]
  let u : C.carrier := liftToCarrier u'
  let w : C.carrier := liftToCarrier w'
  have hu : u ∈ C.lattice := by
    exact lift_mem u' hu'
  have hw : w ∈ C.lattice := by
    exact lift_mem w' hw'
  have hqu : C.space.quadratic u = 0 := by
    have h := f.map_quadratic u'
    rw [show f.toLinearEquiv u' = e₀ by simp [u']] at h
    have hsource :
        (q.restrict (binaryPairSpan (K := K) (x : V) (y : V))
          hnondeg).quadratic u' = 0 := by
      simpa [e₀, QuadraticSpace.hyperbolicPlane_quadratic_apply] using h.symm
    change q.quadratic (u' : V) = 0
    exact hsource
  have hqw : C.space.quadratic w = 0 := by
    have h := f.map_quadratic w'
    rw [show f.toLinearEquiv w' = e₁ by simp [w']] at h
    have hsource :
        (q.restrict (binaryPairSpan (K := K) (x : V) (y : V))
          hnondeg).quadratic w' = 0 := by
      simpa [e₁, QuadraticSpace.hyperbolicPlane_quadratic_apply] using h.symm
    change q.quadratic (w' : V) = 0
    exact hsource
  have huw : C.space.bilin u w =
      (uniformizerPowerUnit K r : K) := by
    have h := f.map_bilin u' w'
    rw [show f.toLinearEquiv u' = e₀ by simp [u'],
      show f.toLinearEquiv w' = e₁ by simp [w']] at h
    have hsource :
        (q.restrict (binaryPairSpan (K := K) (x : V) (y : V))
          hnondeg).bilin u' w' = (uniformizerPowerUnit K r : K) := by
      simpa [e₀, e₁,
        QuadraticSpace.hyperbolicPlane_bilin_apply] using h.symm
    change q.bilin (u' : V) (w' : V) =
      (uniformizerPowerUnit K r : K)
    exact hsource
  have huHigh : ((r + ramificationIndex K : Int) : WithTop Int) <
      ord K (C.space.quadratic u) := by
    rw [hqu, ord_zero]
    exact WithTop.coe_lt_top _
  have hwHigh : ((r + ramificationIndex K : Int) : WithTop Int) <
      ord K (C.space.quadratic w) := by
    rw [hqw, ord_zero]
    exact WithTop.coe_lt_top _
  have hsumValue : C.space.quadratic (u + w) =
      2 * (uniformizerPowerUnit K r : K) := by
    rw [C.space.quadratic_add, hqu, hqw, huw]
    ring
  have hsumOrder : ord K (C.space.quadratic (u + w)) =
      ((r + ramificationIndex K : Int) : WithTop Int) := by
    rw [hsumValue, ord_mul, ← ramificationIndex_spec,
      ← coe_ordUnit, ordUnit_uniformizerPowerUnit]
    norm_cast
    ring
  have hpair := beliLemma319 (q := C.space) u w
    (r + ramificationIndex K) huHigh hwHigh hsumOrder
  have hscale : r + ramificationIndex K - ramificationIndex K = r := by
    omega
  rw [hscale] at hpair
  exact ⟨u, w, hu, hw, hpair⟩

/-- A binary lattice which contains a scaled hyperbolic plane at the
half-volume scale has the hyperbolic endpoint order gap `-2e`.  The key
point is volume rigidity: integral isotropic generators of the contained
plane already span a sublattice with the same volume as the ambient binary
lattice, hence form an integral basis. -/
theorem binaryOrderGap_eq_neg_two_mul_ramificationIndex_of_contains_natural
    {W : Type v} [AddCommGroup W] [Module K W]
    {p : QuadraticSpace K W} {M : Lattice K W}
    (c : BONG W p M 2)
    (hH : Lattice.ContainsScaledHyperbolicPlane p M
      ((c.order 0 + c.order 1) / 2)) :
    c.binaryOrderGap = -(2 * (ramificationIndex K : Int)) := by
  classical
  let r : Int := (c.order 0 + c.order 1) / 2
  rcases exists_integral_isotropic_pair_of_containsScaledHyperbolicPlane
      hH with ⟨u, w, hu, hw, hqu, hqw, huw⟩
  have huwNe : p.bilin u w ≠ 0 := by
    rw [huw]
    exact Units.ne_zero (uniformizerPowerUnit K r)
  have huwOrder : ord K (p.bilin u w) = (r : WithTop Int) := by
    rw [huw, ← coe_ordUnit, ordUnit_uniformizerPowerUnit]
  have huStrict : ord K (p.bilin u w) < ord K (p.quadratic u) := by
    rw [huwOrder, hqu, ord_zero]
    exact WithTop.coe_lt_top r
  have hwWeak : ord K (p.bilin u w) ≤ ord K (p.quadratic w) := by
    rw [huwOrder, hqw, ord_zero]
    exact le_top
  let hli := Lattice.binaryPair_linearIndependent_of_left_strict
    (q := p) huwNe huStrict hwWeak
  letI : Module.Finite K W := M.moduleFinite
  have hfin : finrank K W = 2 := by
    simpa using c.length_eq_finrank.symm
  let e : Fin 2 ≃ Fin (finrank K W) := finCongr hfin.symm
  let pairBasis : Basis (Fin 2) K W :=
    basisOfLinearIndependentOfCardEqFinrank'
      (binaryPairFamily u w) hli (by simpa using hfin.symm)
  have hpairBasis (i : Fin 2) :
      pairBasis i = binaryPairFamily u w i := by
    simp [pairBasis]
  have hpairBasisMem : ∀ i, pairBasis i ∈ M := by
    intro i
    rw [hpairBasis]
    fin_cases i
    · exact hu
    · exact hw
  have hpairLe : Lattice.basisLattice pairBasis ≤ M := by
    change Submodule.span (IntegerRing K) (Set.range pairBasis) ≤
      M.toSubmodule
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hpairBasisMem i
  have huwUnitOrder :
      ordUnit K (Units.mk0 (p.bilin u w) huwNe) = r := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    exact huwOrder
  have hpairVolume :
      Lattice.volumeOrder p (Lattice.basisLattice pairBasis) = 2 * r := by
    simpa only [pairBasis, hli, huwUnitOrder] using
      (volumeOrder_basisLattice_binaryPair_of_finrank_eq_two
        p hfin u w huwNe huStrict hwWeak)
  have hMVolumeSum : Lattice.volumeOrder p M =
      c.order 0 + c.order 1 := by
    rw [c.volumeOrder_eq_ordUnit_valueProduct,
      c.valueProduct_fin_two, ordUnit_mul,
      ← c.order_eq_ordUnit (0 : Fin 2),
      ← c.order_eq_ordUnit (1 : Fin 2)]
  have hvolumeLe : c.order 0 + c.order 1 ≤ 2 * r := by
    have hmono := Lattice.volumeOrder_mono_of_le p hpairLe
    rwa [hMVolumeSum, hpairVolume] at hmono
  have htwiceR : 2 * r = c.order 0 + c.order 1 := by
    have hfloor : 2 * r ≤ c.order 0 + c.order 1 := by
      dsimp only [r]
      omega
    omega
  have hMVolume : Lattice.volumeOrder p M = 2 * r := by
    rw [c.volumeOrder_eq_ordUnit_valueProduct,
      c.valueProduct_fin_two, ordUnit_mul,
      ← c.order_eq_ordUnit (0 : Fin 2),
      ← c.order_eq_ordUnit (1 : Fin 2), htwiceR]
  have hpairEq : Lattice.basisLattice pairBasis = M :=
    Lattice.eq_of_le_of_volumeOrder_eq p
      (Lattice.basisLattice pairBasis) M hpairLe
      (hpairVolume.trans hMVolume.symm)
  have hheadInPair : c.head ∈ Lattice.basisLattice pairBasis := by
    rw [hpairEq]
    exact c.head_isNormGenerator.mem
  have hheadCoord :=
    (Lattice.mem_basisLattice_iff_repr_mem_integerRing
      pairBasis c.head).1 hheadInPair
  have hheadExpansion := pairBasis.sum_repr c.head
  rw [Fin.sum_univ_two, hpairBasis, hpairBasis,
    binaryPairFamily_zero, binaryPairFamily_one] at hheadExpansion
  have hheadFormula : p.quadratic c.head =
      (pairBasis.repr c.head 0 * pairBasis.repr c.head 1) *
        (2 * (uniformizerPowerUnit K r : K)) := by
    calc
      p.quadratic c.head =
          p.quadratic
            ((pairBasis.repr c.head 0) • u +
              (pairBasis.repr c.head 1) • w) :=
        congrArg p.quadratic hheadExpansion.symm
      _ = _ := by
        rw [p.quadratic_add, p.quadratic_smul, p.quadratic_smul,
          hqu, hqw, LinearMap.BilinForm.smul_left,
          LinearMap.BilinForm.smul_right, huw]
        ring
  have hbasePower : 2 * (uniformizerPowerUnit K r : K) ∈
      Lattice.powerIdeal (K := K) (r + ramificationIndex K) := by
    rw [Lattice.mem_powerIdeal_iff, ord_mul, ← ramificationIndex_spec,
      ← coe_ordUnit, ordUnit_uniformizerPowerUnit]
    norm_cast
    omega
  let coefficient : IntegerRing K :=
    ⟨pairBasis.repr c.head 0 * pairBasis.repr c.head 1,
      (IntegerRing K).mul_mem _ _ (hheadCoord 0) (hheadCoord 1)⟩
  have hheadPower : p.quadratic c.head ∈
      Lattice.powerIdeal (K := K) (r + ramificationIndex K) := by
    rw [hheadFormula]
    exact (Lattice.powerIdeal (K := K)
      (r + ramificationIndex K)).smul_mem coefficient hbasePower
  have hheadOrder : ord K (p.quadratic c.head) =
      (c.order 0 : WithTop Int) := by
    rw [← c.value_zero_eq_quadratic_head, ← c.coe_order]
  have hnormLower : r + ramificationIndex K ≤ c.order 0 := by
    have h := (Lattice.mem_powerIdeal_iff (K := K)
      (r + ramificationIndex K) (p.quadratic c.head)).1 hheadPower
    rw [hheadOrder] at h
    exact WithTop.coe_le_coe.mp h
  have huAddW : u + w ∈ M := M.add_mem hu hw
  have hsumValue : p.quadratic (u + w) =
      2 * (uniformizerPowerUnit K r : K) := by
    rw [p.quadratic_add, hqu, hqw, huw]
    ring
  have hsumNorm := Lattice.quadratic_mem_normIdeal_of_mem p M huAddW
  rw [c.normIdeal_eq_powerIdeal_order_zero,
    Lattice.mem_powerIdeal_iff, hsumValue, ord_mul,
    ← ramificationIndex_spec, ← coe_ordUnit,
    ordUnit_uniformizerPowerUnit] at hsumNorm
  have hnormUpper : c.order 0 ≤ r + ramificationIndex K := by
    have h : c.order 0 ≤ (ramificationIndex K : Int) + r := by
      exact_mod_cast hsumNorm
    simpa only [add_comm] using h
  have hnormEq : c.order 0 = r + ramificationIndex K := by omega
  unfold binaryOrderGap
  omega

/-- At the natural half-volume scale, containing a hyperbolic plane is
already equality with the standard scaled hyperbolic lattice.  The contained
isotropic pair spans a full sublattice of the same volume as the ambient
binary lattice, so volume rigidity upgrades containment to an isometry. -/
theorem isIsometric_hyperbolicPlane_of_contains_natural
    {W : Type v} [AddCommGroup W] [Module K W]
    {p : QuadraticSpace K W} {M : Lattice K W}
    (c : BONG W p M 2)
    (hH : Lattice.ContainsScaledHyperbolicPlane p M
      ((c.order 0 + c.order 1) / 2)) :
    Lattice.IsIsometric p
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K ((c.order 0 + c.order 1) / 2)))
      M (Lattice.hyperbolicPlaneLattice (K := K)) := by
  classical
  let r : Int := (c.order 0 + c.order 1) / 2
  rcases exists_integral_isotropic_pair_of_containsScaledHyperbolicPlane
      hH with ⟨u, w, hu, hw, hqu, hqw, huw⟩
  have hqu' : p.bilin u u = 0 := hqu
  have hqw' : p.bilin w w = 0 := hqw
  have huw' : p.bilin u w = (uniformizerPowerUnit K r : K) := by
    simpa only [r] using huw
  have huwNe : p.bilin u w ≠ 0 := by
    rw [huw']
    exact Units.ne_zero (uniformizerPowerUnit K r)
  have huwOrder : ord K (p.bilin u w) = (r : WithTop Int) := by
    rw [huw', ← coe_ordUnit, ordUnit_uniformizerPowerUnit]
  have huStrict : ord K (p.bilin u w) < ord K (p.quadratic u) := by
    rw [huwOrder, hqu, ord_zero]
    exact WithTop.coe_lt_top r
  have hwWeak : ord K (p.bilin u w) ≤ ord K (p.quadratic w) := by
    rw [huwOrder, hqw, ord_zero]
    exact le_top
  let hli := Lattice.binaryPair_linearIndependent_of_left_strict
    (q := p) huwNe huStrict hwWeak
  letI : Module.Finite K W := M.moduleFinite
  have hfin : finrank K W = 2 := by
    simpa using c.length_eq_finrank.symm
  let pairBasis : Basis (Fin 2) K W :=
    basisOfLinearIndependentOfCardEqFinrank'
      (binaryPairFamily u w) hli (by simpa using hfin.symm)
  have hpairBasis (i : Fin 2) :
      pairBasis i = binaryPairFamily u w i := by
    simp [pairBasis]
  have hpairBasisMem : ∀ i, pairBasis i ∈ M := by
    intro i
    rw [hpairBasis]
    fin_cases i
    · exact hu
    · exact hw
  have hpairLe : Lattice.basisLattice pairBasis ≤ M := by
    change Submodule.span (IntegerRing K) (Set.range pairBasis) ≤
      M.toSubmodule
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hpairBasisMem i
  have huwUnitOrder :
      ordUnit K (Units.mk0 (p.bilin u w) huwNe) = r := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    exact huwOrder
  have hpairVolume :
      Lattice.volumeOrder p (Lattice.basisLattice pairBasis) = 2 * r := by
    simpa only [pairBasis, hli, huwUnitOrder] using
      (volumeOrder_basisLattice_binaryPair_of_finrank_eq_two
        p hfin u w huwNe huStrict hwWeak)
  have hgap :=
    c.binaryOrderGap_eq_neg_two_mul_ramificationIndex_of_contains_natural hH
  have htwiceR : 2 * r = c.order 0 + c.order 1 := by
    dsimp only [r]
    unfold binaryOrderGap at hgap
    omega
  have hMVolume : Lattice.volumeOrder p M = 2 * r := by
    rw [c.volumeOrder_eq_ordUnit_valueProduct,
      c.valueProduct_fin_two, ordUnit_mul,
      ← c.order_eq_ordUnit (0 : Fin 2),
      ← c.order_eq_ordUnit (1 : Fin 2), ← htwiceR]
  have hpairEq : Lattice.basisLattice pairBasis = M :=
    Lattice.eq_of_le_of_volumeOrder_eq p
      (Lattice.basisLattice pairBasis) M hpairLe
      (hpairVolume.trans hMVolume.symm)
  have hiso := Lattice.basisLattice_isIsometric_of_gram_eq
    p
    (QuadraticSpace.hyperbolicPlane (uniformizerPowerUnit K r))
    pairBasis (Pi.basisFun K (Fin 2)) (by
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [QuadraticSpace.hyperbolicPlane_bilin_apply,
          Pi.basisFun_apply, hpairBasis, hqu', hqw', huw', p.isSymm.eq])
  rw [hpairEq] at hiso
  simpa only [r, Lattice.hyperbolicPlaneLattice] using hiso

/-- The refined endpoint class `-1/4` makes the initial binary prefix the
scaled hyperbolic plane excluded in Lemma 6.5. -/
theorem firstBinaryIsHyperbolic_of_adjacentParameter_class_eq_negativeQuarter
    (b : BONG V q L (n + 3))
    (hclass : unitSquareClass K (b.adjacentParameter 0 (by simp)) =
      unitSquareClass K (negativeQuarterUnit K)) :
    b.FirstBinaryIsHyperbolic := by
  let P := b.prefixWitness 2 (by omega)
  have hparameter : P.bong.binaryParameter =
      b.adjacentParameter 0 (by simp) := by
    unfold binaryParameter adjacentParameter
    rw [P.valueUnit_eq, P.valueUnit_eq]
    congr 2
  have hPclass : P.bong.binaryUnitSquareClass =
      unitSquareClass K (negativeQuarterUnit K) := by
    rw [binaryUnitSquareClass, hparameter]
    exact hclass
  rcases P.bong.isIsometric_hyperbolicPlane_of_binaryUnitSquareClass_eq_negativeQuarter
      hPclass with ⟨f⟩
  let e₀ : Fin 2 → K := Pi.single 0 1
  let e₁ : Fin 2 → K := Pi.single 1 1
  let u : P.carrier := f.toLinearEquiv.symm e₀
  let w : P.carrier := f.toLinearEquiv.symm e₁
  have he₀ : e₀ ∈ Lattice.hyperbolicPlaneLattice (K := K) := by
    rw [Lattice.hyperbolicPlaneLattice,
      Lattice.mem_basisLattice_iff_repr_mem_integerRing]
    simp [e₀]
  have he₁ : e₁ ∈ Lattice.hyperbolicPlaneLattice (K := K) := by
    rw [Lattice.hyperbolicPlaneLattice,
      Lattice.mem_basisLattice_iff_repr_mem_integerRing]
    simp [e₁]
  have hu : u ∈ P.lattice := by
    apply (f.map_mem u).2
    simpa [u] using he₀
  have hw : w ∈ P.lattice := by
    apply (f.map_mem w).2
    simpa [w] using he₁
  have hqu : q.quadratic (u : V) = 0 := by
    have h := f.map_quadratic u
    rw [show f.toLinearEquiv u = e₀ by simp [u]] at h
    change (q.restrict P.carrier P.nondegenerate).quadratic u = 0
    simpa [e₀, QuadraticSpace.hyperbolicPlane_quadratic_apply] using h.symm
  have hqw : q.quadratic (w : V) = 0 := by
    have h := f.map_quadratic w
    rw [show f.toLinearEquiv w = e₁ by simp [w]] at h
    change (q.restrict P.carrier P.nondegenerate).quadratic w = 0
    simpa [e₁, QuadraticSpace.hyperbolicPlane_quadratic_apply] using h.symm
  have hsumValue : q.quadratic ((u : V) + (w : V)) =
      2 * (uniformizerPowerUnit K
        (P.bong.order 0 - ramificationIndex K) : K) := by
    have h := f.map_quadratic (u + w)
    have hmap : f.toLinearEquiv (u + w) = e₀ + e₁ := by
      simp [u, w]
    rw [hmap] at h
    change (q.restrict P.carrier P.nondegenerate).quadratic (u + w) = _
    simpa [e₀, e₁, QuadraticSpace.hyperbolicPlane_quadratic_apply]
      using h.symm
  have hsumOrder : ord K (q.quadratic ((u : V) + (w : V))) =
      (P.bong.order 0 : WithTop Int) := by
    rw [hsumValue, ord_mul, ← ramificationIndex_spec,
      ← coe_ordUnit, ordUnit_uniformizerPowerUnit]
    norm_cast
    omega
  have huHigh : (P.bong.order 0 : WithTop Int) <
      ord K (q.quadratic (u : V)) := by
    rw [hqu, ord_zero]
    exact WithTop.coe_lt_top _
  have hwHigh : (P.bong.order 0 : WithTop Int) <
      ord K (q.quadratic (w : V)) := by
    rw [hqw, ord_zero]
    exact WithTop.coe_lt_top _
  have hpair := beliLemma319 (q := q) (u : V) (w : V)
    (P.bong.order 0) huHigh hwHigh hsumOrder
  have hgap := ordUnit_eq_of_unitSquareClass_eq (K := K) hclass
  rw [b.ordUnit_adjacentParameter_zero,
    ordUnit_negativeQuarterUnit] at hgap
  have hscale : P.bong.order 0 - ramificationIndex K =
      (b.order 0 + b.order 1) / 2 := by
    have hPzero : P.bong.order 0 = b.order 0 := by
      simpa [P, SegmentWitness.sourceIndex] using
        P.order_eq (0 : Fin 2)
    rw [hPzero]
    unfold lemma62Gap at hgap
    omega
  rw [hscale] at hpair
  exact ⟨u, w, hu, hw, hpair⟩

namespace Lemma65Setup

variable {b : BONG V q L (n + 3)}

/-- The scale `s = R₁ + (R₂+2k-R₁)/2` used in parts (ii) and (iii). -/
noncomputable def reflectionScaleOrder (S : b.Lemma65Setup) : Int :=
  b.order 0 +
    (b.order 1 + 2 * (S.k : Int) - b.order 0) / 2

/-- When the final binary gap is even, the scale used in Lemma 6.5 is the
literal half-sum of the two rescaled initial orders. -/
theorem two_mul_reflectionScaleOrder
    (S : b.Lemma65Setup)
    (heven : Even
      (b.order 1 + 2 * (S.k : Int) - b.order 0)) :
    2 * S.reflectionScaleOrder =
      b.order 0 + b.order 1 + 2 * (S.k : Int) := by
  rcases heven with ⟨c, hc⟩
  simp only [reflectionScaleOrder]
  have hhalf :
      (b.order 1 + 2 * (S.k : Int) - b.order 0) / 2 = c := by
    omega
  rw [hhalf]
  omega

/-- The minimal final parameter satisfies one of the four alternatives in
Beli's Lemma 3.17. -/
theorem finalParameterCases (S : b.Lemma65Setup) :
    BeliLemma317ParameterCases (K := K)
      (b.lemma62Gap + 2 * (S.k : Int))
      (normalizedUnitPart K (b.adjacentParameter 0 (by simp))) := by
  exact S.toMinimalityData.finalParameterCases

/-- In the low range, the rescaled initial binary order gap is even. -/
theorem lowRange_gap_even (S : b.Lemma65Setup)
    (hlow : b.Lemma65LowRange S) :
    Even (b.order 1 + 2 * (S.k : Int) - b.order 0) := by
  have heven :=
    even_ordUnit_of_hasSomeEqualNormGeneratorBasis_of_le_two_e
      (b.headSecondRescaledParameter S.k)
      (b.headSecondRescaledParameter_isBinaryParameterAdmissible S.k)
      S.admissible
      (by
        rw [b.ordUnit_headSecondRescaledParameter]
        exact hlow)
  simpa only [b.ordUnit_headSecondRescaledParameter] using heven

end Lemma65Setup

namespace Lemma65MinimalityData

variable {b : BONG V q L (n + 3)}

/-- In the low range, minimality leaves precisely Beli's case (3), the
finite-defect boundary, or the short-shift case (4), where `k ≤ 1`. -/
theorem lowRange_boundary_or_k_le_one (M : b.Lemma65MinimalityData)
    (hlow : b.Lemma65LowRangeAt M.k) :
    ((quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (M.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int)) ∨
      M.k ≤ 1 := by
  let R : Int := b.lemma62Gap + 2 * (M.k : Int)
  let ε : Kˣ := normalizedUnitPart K (b.adjacentParameter 0 (by simp))
  let d := quadraticDefect K (-ε)
  have hε : IsValuationUnit K (ε : K) :=
    normalizedUnitPart_isValuationUnit K _
  have hR : R = b.order 1 + 2 * (M.k : Int) - b.order 0 := by
    simp only [R, lemma62Gap]
    omega
  have hRle : R ≤ 2 * (ramificationIndex K : Int) := by
    rw [hR]
    exact hlow
  have hbaseLower : -(2 * (ramificationIndex K : Int)) ≤ b.lemma62Gap := by
    let i0 : Fin (n + 3) := ⟨0, by omega⟩
    have hi0 : i0.1 + 1 < n + 3 := by simp [i0]
    have h := b.adjacentOrderGap_ge_neg_two_mul_e i0 hi0
    have hi0Eq : i0 = (0 : Fin (n + 3)) := by
      apply Fin.ext
      simp [i0]
    have hi1Eq : (⟨i0.1 + 1, hi0⟩ : Fin (n + 3)) = 1 := by
      apply Fin.ext
      simp [i0]
    rw [hi1Eq, hi0Eq] at h
    simpa only [lemma62Gap] using h
  have hadmissible_lt : ∀ (j : Nat), j < M.k →
      BeliLemma317ParameterCases (K := K)
        (b.lemma62Gap + 2 * (j : Int)) ε → False := by
    intro j hj hcases
    exact (M.not_admissible_of_lt j hj)
      (b.headSecondRescaleAdmissible_of_parameterCases j hcases)
  have htop_short : d = ⊤ → Even R →
      Even (R / 2 + (ramificationIndex K : Int)) → M.k ≤ 1 := by
    intro htop hEvenR hEvenHigh
    by_contra hnot
    have hkTwo : 2 ≤ M.k := by omega
    let j : Nat := M.k - 2
    have hj : j < M.k := by omega
    have hjCast : (j : Int) = (M.k : Int) - 2 := by
      simp only [j]
      omega
    let Rj : Int := b.lemma62Gap + 2 * (j : Int)
    have hRj : Rj = R - 4 := by
      simp only [Rj, R]
      rw [hjCast]
      ring
    have hRjUpper : Rj < 2 * (ramificationIndex K : Int) := by
      rw [hRj]
      omega
    have hEvenRj : Even Rj := by
      rw [hRj]
      exact hEvenR.sub (by norm_num)
    have hEvenHighJ :
        Even (Rj / 2 + (ramificationIndex K : Int)) := by
      have hhalf : Rj / 2 + (ramificationIndex K : Int) =
          R / 2 + (ramificationIndex K : Int) - 2 := by
        rw [hRj]
        rcases hEvenR with ⟨m, hm⟩
        omega
      rw [hhalf]
      exact hEvenHigh.sub (by norm_num)
    by_cases hendpoint : Rj = -(2 * (ramificationIndex K : Int))
    · have hjZero : j = 0 := by
        have hjNonneg : (0 : Int) ≤ (j : Int) := by exact_mod_cast Nat.zero_le j
        simp only [Rj] at hendpoint
        omega
      have hbaseEq : b.lemma62Gap =
          -(2 * (ramificationIndex K : Int)) := by
        simp only [Rj, hjZero] at hendpoint
        norm_num at hendpoint
        exact hendpoint
      have hsquare : IsSquare (-ε) :=
        (quadraticDefect_eq_top_iff_isSquare (K := K) (-ε)).1 htop
      have hendpointClass :
          unitSquareClass K
              (uniformizerPowerUnit K b.lemma62Gap * ε) =
            unitSquareClass K (negativeQuarterUnit K) :=
        unitSquareClass_uniformizerPower_mul_eq_negativeQuarter
          b.lemma62Gap ε hε hbaseEq hsquare
      have hfactor := uniformizerPower_mul_normalizedUnitPart K
        (b.adjacentParameter 0 (by simp))
      rw [b.ordUnit_adjacentParameter_zero] at hfactor
      have horiginalClass :
          unitSquareClass K (b.adjacentParameter 0 (by simp)) =
            unitSquareClass K (negativeQuarterUnit K) := by
        rw [← hfactor]
        exact hendpointClass
      exact M.firstBinary_not_hyperbolic
        (b.firstBinaryIsHyperbolic_of_adjacentParameter_class_eq_negativeQuarter
          horiginalClass)
    · have hquarter :
          unitSquareClass K (uniformizerPowerUnit K Rj * ε) ≠
            unitSquareClass K (negativeQuarterUnit K) := by
        intro heq
        have hord := ordUnit_eq_of_unitSquareClass_eq (K := K) heq
        rw [ordUnit_uniformizerPower_mul_valuationUnit ε hε Rj,
          ordUnit_negativeQuarterUnit] at hord
        exact hendpoint hord
      apply hadmissible_lt j hj
      simp only [BeliLemma317ParameterCases]
      exact Or.inr (Or.inr (Or.inl
        ⟨Or.inl htop, hRjUpper, hEvenRj, hEvenHighJ, hquarter⟩))
  have hfinite_short : d ≠ ⊤ →
      2 * (ramificationIndex K : Int) - 2 * (d.toNat : Int) < R →
      Even R → Even (R / 2 + (ramificationIndex K : Int)) →
      M.k ≤ 1 := by
    intro hfinite habove hEvenR hEvenHigh
    by_contra hnot
    have hkTwo : 2 ≤ M.k := by omega
    let boundary : Int :=
      2 * (ramificationIndex K : Int) - 2 * (d.toNat : Int)
    by_cases hprevious : R - 2 = boundary
    · let j : Nat := M.k - 1
      have hj : j < M.k := by omega
      have hjCast : (j : Int) = (M.k : Int) - 1 := by
        simp only [j]
        omega
      have hRj : b.lemma62Gap + 2 * (j : Int) = boundary := by
        simp only [R] at hprevious
        rw [hjCast]
        omega
      apply hadmissible_lt j hj
      simp only [BeliLemma317ParameterCases]
      exact Or.inr (Or.inl ⟨hfinite, by simpa only [boundary] using hRj⟩)
    · let j : Nat := M.k - 2
      have hj : j < M.k := by omega
      have hjCast : (j : Int) = (M.k : Int) - 2 := by
        simp only [j]
        omega
      let Rj : Int := b.lemma62Gap + 2 * (j : Int)
      have hRj : Rj = R - 4 := by
        simp only [Rj, R]
        rw [hjCast]
        ring
      have hboundaryEven : Even boundary := by
        refine ⟨(ramificationIndex K : Int) - (d.toNat : Int), ?_⟩
        simp only [boundary]
        ring
      have hboundaryLe : boundary ≤ Rj := by
        rcases hEvenR with ⟨m, hm⟩
        rcases hboundaryEven with ⟨c, hc⟩
        rw [hRj]
        omega
      by_cases hboundaryEq : Rj = boundary
      · apply hadmissible_lt j hj
        simp only [BeliLemma317ParameterCases]
        exact Or.inr (Or.inl
          ⟨hfinite, by simpa only [boundary] using hboundaryEq⟩)
      · have hboundaryLt : boundary < Rj := by omega
        have hRjUpper : Rj < 2 * (ramificationIndex K : Int) := by
          rw [hRj]
          omega
        have hEvenRj : Even Rj := by
          rw [hRj]
          exact hEvenR.sub (by norm_num)
        have hEvenHighJ :
            Even (Rj / 2 + (ramificationIndex K : Int)) := by
          have hhalf : Rj / 2 + (ramificationIndex K : Int) =
              R / 2 + (ramificationIndex K : Int) - 2 := by
            rw [hRj]
            rcases hEvenR with ⟨m, hm⟩
            omega
          rw [hhalf]
          exact hEvenHigh.sub (by norm_num)
        have hnonsquare : ¬IsSquare (-ε) := by
          intro hsquare
          exact hfinite
            ((quadraticDefect_eq_top_iff_isSquare (K := K) (-ε)).2 hsquare)
        have hdBound := quadraticDefect_le_two_mul_e_of_not_isSquare
          (K := K) hnonsquare
        have hdLe : d.toNat ≤ 2 * ramificationIndex K := by
          change d ≤ _ at hdBound
          rw [← ENat.coe_toNat hfinite] at hdBound
          exact ENat.coe_le_coe.mp hdBound
        have hdLeInt : (d.toNat : Int) ≤
            2 * (ramificationIndex K : Int) := by
          exact_mod_cast hdLe
        have hboundaryLower :
            -(2 * (ramificationIndex K : Int)) ≤ boundary := by
          simp only [boundary]
          omega
        have hquarter :
            unitSquareClass K (uniformizerPowerUnit K Rj * ε) ≠
              unitSquareClass K (negativeQuarterUnit K) := by
          intro heq
          have hord := ordUnit_eq_of_unitSquareClass_eq (K := K) heq
          rw [ordUnit_uniformizerPower_mul_valuationUnit ε hε Rj,
            ordUnit_negativeQuarterUnit] at hord
          omega
        apply hadmissible_lt j hj
        simp only [BeliLemma317ParameterCases]
        exact Or.inr (Or.inr (Or.inl
          ⟨Or.inr ⟨hfinite, by simpa only [boundary] using hboundaryLt⟩,
            hRjUpper, hEvenRj, hEvenHighJ, hquarter⟩))
  have hcases := M.finalParameterCases
  simp only [BeliLemma317ParameterCases] at hcases
  rcases hcases with hhigh | hboundary | hinterior | hendpoint
  · exfalso
    exact (not_lt_of_ge hRle) hhigh
  · left
    simpa only [R, ε, d] using hboundary
  · right
    rcases hinterior with
      ⟨hboundaryData, hupper, hEvenR, hEvenHigh, _hquarter⟩
    rcases hboundaryData with htop | hfiniteAbove
    · exact htop_short htop hEvenR hEvenHigh
    · exact hfinite_short hfiniteAbove.1 hfiniteAbove.2
        hEvenR hEvenHigh
  · right
    rcases hendpoint with ⟨hparameter, _hresidue⟩
    rcases hparameter with hREnd | hquarter
    · by_cases hfinite : d = ⊤
      · exact htop_short hfinite (by
          simp only [R]
          rw [hREnd]
          exact even_two_mul _) (by
          simp only [R]
          rw [hREnd]
          refine ⟨ramificationIndex K, ?_⟩
          omega)
      · have hnegUnit : IsValuationUnit K ((-ε : Kˣ) : K) := by
          change ord K (-((ε : K))) = 0
          change ord K (ε : K) = 0 at hε
          simpa only [ord_neg] using hε
        have hdPos : 0 < d.toNat :=
          quadraticDefect_toNat_pos_of_unit_of_ne_top
            (-ε) hnegUnit hfinite
        have hdPosInt : (0 : Int) < (d.toNat : Int) := by
          exact_mod_cast hdPos
        have habove :
            2 * (ramificationIndex K : Int) -
                2 * (d.toNat : Int) < R := by
          simp only [R]
          rw [hREnd]
          omega
        exact hfinite_short hfinite habove (by
          simp only [R]
          rw [hREnd]
          exact even_two_mul _) (by
          simp only [R]
          rw [hREnd]
          refine ⟨ramificationIndex K, ?_⟩
          omega)
    · have hord := ordUnit_eq_of_unitSquareClass_eq (K := K) hquarter
      rw [ordUnit_uniformizerPower_mul_valuationUnit ε hε R,
        ordUnit_negativeQuarterUnit] at hord
      simp only [R] at hord
      omega

end Lemma65MinimalityData

namespace Lemma65Setup

variable {b : BONG V q L (n + 3)}

/-- Compatibility wrapper for the original concrete setup API. -/
theorem lowRange_boundary_or_k_le_one (S : b.Lemma65Setup)
    (hlow : b.Lemma65LowRange S) :
    ((quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int)) ∨
      S.k ≤ 1 :=
  S.toMinimalityData.lowRange_boundary_or_k_le_one hlow

/-- The order inequalities extracted from Beli's finite-defect boundary
case (3).  They record exactly what is used geometrically later: the third
BONG vector is deeper than the critical norm, and its complementary block
has scale strictly deeper than the reflection scale. -/
structure BoundaryOrderData (S : b.Lemma65Setup) : Prop where
  finalGap_even : Even
    (b.order 1 + 2 * (S.k : Int) - b.order 0)
  baseGap_even : Even b.lemma62Gap
  baseGap_add_defect_nonneg :
    0 ≤ b.lemma62Gap +
      ((quadraticDefect K
        (-(normalizedUnitPart K
          (b.adjacentParameter 0 (by simp))))).toNat : Int)
  thirdGap :
    2 * (ramificationIndex K : Int) + 1 ≤
      b.order 2 - b.order 1
  tailOrder_le_critical :
    b.order 1 + 2 * (S.k : Int) ≤
      S.reflectionScaleOrder + ramificationIndex K
  headRescaledOrder_le_critical :
    b.order 0 + 2 * (S.k : Int) ≤
      S.reflectionScaleOrder + ramificationIndex K
  tailOrder_lt_third :
    b.order 1 + 2 * (S.k : Int) < b.order 2
  critical_lt_third :
    S.reflectionScaleOrder + ramificationIndex K < b.order 2
  reflection_lt_third_sub_ramification :
    S.reflectionScaleOrder < b.order 2 - ramificationIndex K

/-- Property B and the admissible-parameter defect bound imply all of the
order data used in the boundary branch of Claim (a). -/
theorem boundaryOrderData
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hboundary :
      (quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int)) :
    S.BoundaryOrderData := by
  let a₀ : Kˣ := b.adjacentParameter 0 (by simp)
  let ε₀ : Kˣ := normalizedUnitPart K a₀
  let d := quadraticDefect K (-ε₀)
  have hdFinite : d ≠ ⊤ := by
    simpa only [d, ε₀, a₀] using hboundary.1
  have hfinalEq : b.lemma62Gap + 2 * (S.k : Int) =
      2 * (ramificationIndex K : Int) - 2 * (d.toNat : Int) := by
    simpa only [d, ε₀, a₀] using hboundary.2
  have hfinalEven : Even (b.lemma62Gap + 2 * (S.k : Int)) := by
    refine ⟨(ramificationIndex K : Int) - (d.toNat : Int), ?_⟩
    omega
  have hbaseEven : Even b.lemma62Gap := by
    rcases hfinalEven with ⟨r, hr⟩
    refine ⟨r - (S.k : Int), ?_⟩
    omega
  have hbaseUpper : b.lemma62Gap ≤
      2 * (ramificationIndex K : Int) := by
    have hkNonneg : (0 : Int) ≤ (S.k : Int) := by positivity
    omega
  have ha₀DefectEq : quadraticDefect K (-a₀) = d := by
    simpa only [d, ε₀] using
      beliParameterDefect_eq_normalizedUnitPart_of_even
        (K := K) a₀ (by
          simpa only [a₀, b.ordUnit_adjacentParameter_zero] using
            hbaseEven)
  have ha₀ParameterDefect : beliParameterDefect K a₀ = d := by
    simpa only [beliParameterDefect] using ha₀DefectEq
  have ha₀ParameterFinite : beliParameterDefect K a₀ ≠ ⊤ := by
    rw [ha₀ParameterDefect]
    exact hdFinite
  have hbaseDefectNonneg :
      0 ≤ b.lemma62Gap + (d.toNat : Int) := by
    have hadmissible :=
      b.adjacentParameter_isBinaryParameterAdmissible 0 (by simp)
    have h := hadmissible.order_add_parameterDefect_nonneg (by
      simpa only [a₀] using ha₀ParameterFinite)
    rw [b.ordUnit_adjacentParameter_zero] at h
    simpa only [a₀, ha₀ParameterDefect] using h
  have hdLeNat : d.toNat ≤ 2 * ramificationIndex K := by
    have hnotSquare : ¬IsSquare (-ε₀) := by
      intro hsquare
      exact hdFinite
        ((quadraticDefect_eq_top_iff_isSquare (K := K) (-ε₀)).2
          hsquare)
    have hbound :=
      quadraticDefect_le_two_mul_e_of_not_isSquare (K := K) hnotSquare
    change d ≤ _ at hbound
    rw [← ENat.coe_toNat hdFinite] at hbound
    exact_mod_cast hbound
  have hcutCast : (b.lemma62DefectCutoff : Int) =
      (ramificationIndex K : Int) - b.lemma62Gap / 2 :=
    b.lemma62DefectCutoff_cast hbaseEven hbaseUpper
  have hdLeCutNat : d.toNat ≤ b.lemma62DefectCutoff := by
    rcases hbaseEven with ⟨r, hr⟩
    omega
  have hdefectLow :
      beliParameterDefect K (b.adjacentParameter 0 (by simp)) ≤
        (b.lemma62DefectCutoff : ℕ∞) := by
    change beliParameterDefect K a₀ ≤ _
    rw [ha₀ParameterDefect, ← ENat.coe_toNat hdFinite]
    exact_mod_cast hdLeCutNat
  have hthirdGap :
      2 * (ramificationIndex K : Int) + 1 ≤
        b.order 2 - b.order 1 :=
    b.thirdGap_ge_of_propertyB_lemma62_low
      hB hbaseEven hbaseUpper hdefectLow
  have hfinalGap :
      b.order 1 + 2 * (S.k : Int) - b.order 0 =
        2 * (ramificationIndex K : Int) - 2 * (d.toNat : Int) := by
    unfold lemma62Gap at hfinalEq
    omega
  have hfinalGapEven : Even
      (b.order 1 + 2 * (S.k : Int) - b.order 0) := by
    rcases hfinalEven with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    unfold lemma62Gap at hr
    omega
  have hreflection := S.two_mul_reflectionScaleOrder hfinalGapEven
  have hgapDefect :
      0 ≤ b.order 1 - b.order 0 + (d.toNat : Int) := by
    simpa only [lemma62Gap] using hbaseDefectNonneg
  have htailCritical :
      b.order 1 + 2 * (S.k : Int) ≤
        S.reflectionScaleOrder + ramificationIndex K := by
    have hdNonneg : (0 : Int) ≤ (d.toNat : Int) := by positivity
    omega
  have hheadCritical :
      b.order 0 + 2 * (S.k : Int) ≤
        S.reflectionScaleOrder + ramificationIndex K := by
    omega
  have htailThird :
      b.order 1 + 2 * (S.k : Int) < b.order 2 := by
    have hdNonneg : (0 : Int) ≤ (d.toNat : Int) := by positivity
    omega
  have hcriticalThird :
      S.reflectionScaleOrder + ramificationIndex K < b.order 2 := by
    omega
  refine {
    finalGap_even := hfinalGapEven
    baseGap_even := hbaseEven
    baseGap_add_defect_nonneg := ?_
    thirdGap := hthirdGap
    tailOrder_le_critical := htailCritical
    headRescaledOrder_le_critical := hheadCritical
    tailOrder_lt_third := htailThird
    critical_lt_third := hcriticalThird
    reflection_lt_third_sub_ramification := by omega }
  simpa only [d, ε₀, a₀] using hbaseDefectNonneg

/-- The projection of every vector of the parent lattice lies in the original
projected tail lattice. -/
theorem projection_mem_tail (S : b.Lemma65Setup) (x : V) (hx : x ∈ L) :
    S.projection x ∈
      L.projectedLattice q b.head b.head_isAnisotropic := by
  exact Lattice.projection_mem_projectedLattice
    q L b.head b.head_isAnisotropic hx

/-- Every projected lattice vector has quadratic order at least the first
tail order. -/
theorem tail_order_zero_le_ord_quadratic_projection
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L) :
    (b.tail.order 0 : WithTop Int) ≤
      ord K ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
        (S.projection x)) := by
  have hmem := S.projection_mem_tail x hx
  have hideal := Lattice.quadratic_mem_normIdeal_of_mem
    (q.orthogonalSpace b.head b.head_isAnisotropic)
    (L.projectedLattice q b.head b.head_isAnisotropic) hmem
  have hnorm : Lattice.normIdeal
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic) =
        Lattice.principalIdeal (K := K) (b.tail.value 0) := by
    simpa [b.tail.value_zero_eq_quadratic_head] using
      b.tail.head_isNormGenerator.normIdeal_eq
  rw [hnorm] at hideal
  rw [b.tail.coe_order]
  exact Lattice.ord_le_of_mem_principalIdeal
    (b.tail.value_ne_zero 0) hideal

/-- At depth zero the rescaled-tail carrier is the original projected tail,
so every projection belongs to it. -/
theorem projection_mem_tailRescale_of_k_eq_zero
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L) (hk : S.k = 0) :
    S.projection x ∈ S.tailRescale.lattice := by
  have hmem := S.projection_mem_tail x hx
  have hlower := S.tail_order_zero_le_ord_quadratic_projection x hx
  rw [S.tailRescale.mem_lattice_iff_ord_ge_head_depth]
  refine ⟨hmem, ?_⟩
  have hthreshold :
      ((b.tail.order 0 + 2 * (S.k : Int) - 1 : Int) : WithTop Int) ≤
        (b.tail.order 0 : WithTop Int) := by
    norm_cast
    rw [hk]
    norm_num
  exact hthreshold.trans hlower

/-- The rescaled projected tail is a genuine sublattice of the original
projected tail.  This is the inclusion needed to apply the inverse-image
construction from Beli's Lemma 2.7(ii). -/
theorem tailRescale_lattice_le_tail (S : b.Lemma65Setup) :
    S.tailRescale.lattice ≤
      L.projectedLattice q b.head b.head_isAnisotropic := by
  intro y hy
  exact (S.tailRescale.mem_lattice_iff_ord_ge_head_depth y).1 hy |>.1

/-- The paper's intermediate lattice
`L₀ = ⟨x₁, πᵏx₂, x₃, ..., xₙ⟩`, defined intrinsically as the inverse image
of the rescaled projected tail. -/
noncomputable def intermediateLattice (S : b.Lemma65Setup) : Lattice K V :=
  Lattice.projectionPreimage q L b.head b.head_isAnisotropic
    b.head_isNormGenerator.mem S.tailRescale.lattice
    S.tailRescale_lattice_le_tail

/-- The literal BONG `x₁, πᵏx₂, x₃, ...` of the intermediate lattice. -/
noncomputable def intermediateBONG (S : b.Lemma65Setup) :
    BONG V q S.intermediateLattice (n + 3) :=
  (BONG.prependProjectionPreimage b.head_isNormGenerator
    S.tailRescale.lattice S.tailRescale_lattice_le_tail
    S.tailRescale.bong).castLength (by omega)

@[simp]
theorem mem_intermediateLattice_iff (S : b.Lemma65Setup) (x : V) :
    x ∈ S.intermediateLattice ↔ x ∈ L ∧ S.projection x ∈ S.tailRescale.lattice :=
  Iff.rfl

/-- A vector with projection in the rescaled tail belongs to `L₀`. -/
theorem mem_intermediateLattice (S : b.Lemma65Setup) (x : V)
    (hx : x ∈ L) (hprojection : S.projection x ∈ S.tailRescale.lattice) :
    x ∈ S.intermediateLattice :=
  (S.mem_intermediateLattice_iff x).2 ⟨hx, hprojection⟩

@[simp]
theorem intermediateBONG_ambientVector_zero (S : b.Lemma65Setup) :
    S.intermediateBONG.ambientVector 0 = b.head := by
  simp only [intermediateBONG, intermediateLattice,
    BONG.ambientVector_castLength]
  change
    (BONG.prependProjectionPreimage b.head_isNormGenerator
      S.tailRescale.lattice S.tailRescale_lattice_le_tail
      S.tailRescale.bong).ambientVector
        ⟨(0 : Fin (n + 3)).val, by omega⟩ = b.head
  have hindex :
      (⟨(0 : Fin (n + 3)).val, by omega⟩ : Fin (n + 2 + 1)) = 0 :=
    Fin.ext rfl
  rw [hindex, BONG.ambientVector_prependProjectionPreimage_zero]

@[simp]
theorem intermediateBONG_ambientVector_one (S : b.Lemma65Setup) :
    S.intermediateBONG.ambientVector 1 =
      ((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K) •
        b.ambientVector 1 := by
  simp only [intermediateBONG, intermediateLattice,
    BONG.ambientVector_castLength]
  change
    (BONG.prependProjectionPreimage b.head_isNormGenerator
      S.tailRescale.lattice S.tailRescale_lattice_le_tail
      S.tailRescale.bong).ambientVector (0 : Fin (n + 2)).succ = _
  rw [BONG.ambientVector_prependProjectionPreimage_succ,
    S.coe_tailRescale_ambientVector_zero]

@[simp]
theorem intermediateBONG_ambientVector_two (S : b.Lemma65Setup) :
    S.intermediateBONG.ambientVector 2 = b.ambientVector 2 := by
  simp only [intermediateBONG, intermediateLattice,
    BONG.ambientVector_castLength]
  change
    (BONG.prependProjectionPreimage b.head_isNormGenerator
      S.tailRescale.lattice S.tailRescale_lattice_le_tail
      S.tailRescale.bong).ambientVector (1 : Fin (n + 2)).succ = _
  rw [BONG.ambientVector_prependProjectionPreimage_succ]
  have hindex :
      (1 : Fin (n + 2)) = (0 : Fin (n + 1)).succ := Fin.ext rfl
  rw [hindex, S.tailRescale.ambientVector_succ,
    b.coe_ambientVector_tail]
  congr 1

/-- From the third vector onward the intermediate BONG is literally the
original BONG. -/
@[simp]
theorem intermediateBONG_ambientVector_succ_succ
    (S : b.Lemma65Setup) (i : Fin (n + 1)) :
    S.intermediateBONG.ambientVector i.succ.succ =
      b.ambientVector i.succ.succ := by
  simp only [intermediateBONG, intermediateLattice,
    BONG.ambientVector_castLength]
  change
    (BONG.prependProjectionPreimage b.head_isNormGenerator
      S.tailRescale.lattice S.tailRescale_lattice_le_tail
      S.tailRescale.bong).ambientVector
        (i.succ : Fin (n + 2)).succ = _
  rw [BONG.ambientVector_prependProjectionPreimage_succ,
    S.tailRescale.ambientVector_succ,
    b.coe_ambientVector_tail]

/-- Rescaling the second vector does not change the ambient two-dimensional
prefix carrier.  This identifies the initial binary component of `L` with
that of the intermediate lattice `L₀` at the vector-space level. -/
theorem intermediateBONG_prefixTwo_segmentCarrier_eq
    (S : b.Lemma65Setup) :
    S.intermediateBONG.segmentCarrier 0 2 (by omega) =
      b.segmentCarrier 0 2 (by omega) := by
  change
    Submodule.span K
        (Set.range (S.intermediateBONG.segmentVector 0 2 (by omega))) =
      Submodule.span K (Set.range (b.segmentVector 0 2 (by omega)))
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · have hbase := Submodule.subset_span (R := K)
          (s := Set.range (b.segmentVector 0 2 (by omega)))
          (Set.mem_range_self (0 : Fin 2))
      change S.intermediateBONG.segmentVector 0 2
          (by omega) (0 : Fin 2) ∈ _
      have hzero : S.intermediateBONG.segmentVector 0 2
          (by omega) (0 : Fin 2) =
            b.segmentVector 0 2 (by omega) (0 : Fin 2) := by
        change S.intermediateBONG.ambientVector 0 = b.ambientVector 0
        rw [S.intermediateBONG_ambientVector_zero,
          b.ambientVector_zero_eq_head]
      rw [hzero]
      exact hbase
    · have hbase := Submodule.subset_span (R := K)
          (s := Set.range (b.segmentVector 0 2 (by omega)))
          (Set.mem_range_self (1 : Fin 2))
      change S.intermediateBONG.segmentVector 0 2
          (by omega) (1 : Fin 2) ∈ _
      have hvec :
          S.intermediateBONG.segmentVector 0 2 (by omega) (1 : Fin 2) =
            ((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K) •
              b.segmentVector 0 2 (by omega) (1 : Fin 2) := by
        change S.intermediateBONG.ambientVector 1 =
          ((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K) •
            b.ambientVector 1
        exact S.intermediateBONG_ambientVector_one
      rw [hvec]
      exact Submodule.smul_mem _ _ hbase
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · have hbase := Submodule.subset_span (R := K)
          (s := Set.range
            (S.intermediateBONG.segmentVector 0 2 (by omega)))
          (Set.mem_range_self (0 : Fin 2))
      change b.segmentVector 0 2 (by omega) (0 : Fin 2) ∈ _
      have hzero : S.intermediateBONG.segmentVector 0 2
          (by omega) (0 : Fin 2) =
            b.segmentVector 0 2 (by omega) (0 : Fin 2) := by
        change S.intermediateBONG.ambientVector 0 = b.ambientVector 0
        rw [S.intermediateBONG_ambientVector_zero,
          b.ambientVector_zero_eq_head]
      rwa [hzero] at hbase
    · have hbase := Submodule.subset_span (R := K)
          (s := Set.range
            (S.intermediateBONG.segmentVector 0 2 (by omega)))
          (Set.mem_range_self (1 : Fin 2))
      change b.segmentVector 0 2 (by omega) (1 : Fin 2) ∈ _
      have hvec :
          S.intermediateBONG.segmentVector 0 2 (by omega) (1 : Fin 2) =
            ((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K) •
              b.segmentVector 0 2 (by omega) (1 : Fin 2) := by
        change S.intermediateBONG.ambientVector 1 =
          ((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K) •
            b.ambientVector 1
        exact S.intermediateBONG_ambientVector_one
      have hinverse : b.segmentVector 0 2 (by omega) (1 : Fin 2) =
          (((uniformizerPowerUnit K (S.k : Int))⁻¹ : Kˣ) : K) •
            S.intermediateBONG.segmentVector 0 2
              (by omega) (1 : Fin 2) := by
        rw [hvec]
        rw [smul_smul]
        simp [uniformizer_ne_zero K]
      rw [hinverse]
      exact Submodule.smul_mem _ _ hbase

/-- A two-vector segment is automatically good: there is no pair of indices
at distance two inside it. -/
theorem SegmentWitness.isGood_of_length_two
    {m start : Nat} {b : BONG V q L m}
    {bound : start + 2 ≤ m}
    (w : SegmentWitness b start 2 bound) : w.bong.IsGood := by
  intro i hi
  omega

/-- At the initial binary cut, head rescaling computes the same first
parameter in the left segment as in the ambient BONG. -/
theorem TwoBlockSplitWitness.left_headRescaledFirstParameter_eq_of_cut_two
    {m k : Nat} {b : BONG V q L (m + 2)}
    (T : TwoBlockSplitWitness b 2 (by omega)) :
    T.left.bong.headRescaledFirstParameter k =
      b.headRescaledFirstParameter k := by
  rw [T.left.bong.headRescaledFirstParameter_eq_mul_inv_square,
    b.headRescaledFirstParameter_eq_mul_inv_square]
  congr 1
  unfold adjacentParameter
  rw [T.left.valueUnit_eq, T.left.valueUnit_eq]
  congr 2 <;>
    apply congrArg b.valueUnit <;>
    apply Fin.ext <;>
    simp [SegmentWitness.sourceIndex]

@[simp]
theorem intermediateBONG_valueUnit_zero (S : b.Lemma65Setup) :
    S.intermediateBONG.valueUnit 0 = b.valueUnit 0 := by
  apply Units.ext
  rw [S.intermediateBONG.coe_valueUnit, b.coe_valueUnit,
    ← S.intermediateBONG.quadratic_ambientVector,
    ← b.quadratic_ambientVector,
    S.intermediateBONG_ambientVector_zero,
    b.ambientVector_zero_eq_head]

@[simp]
theorem intermediateBONG_valueUnit_one (S : b.Lemma65Setup) :
    S.intermediateBONG.valueUnit 1 =
      uniformizerPowerUnit K (S.k : Int) ^ 2 * b.valueUnit 1 := by
  apply Units.ext
  rw [S.intermediateBONG.coe_valueUnit, Units.val_mul,
    Units.val_pow_eq_pow_val, b.coe_valueUnit,
    ← S.intermediateBONG.quadratic_ambientVector,
    ← b.quadratic_ambientVector,
    S.intermediateBONG_ambientVector_one, q.quadratic_smul]

@[simp]
theorem intermediateBONG_order_zero (S : b.Lemma65Setup) :
    S.intermediateBONG.order 0 = b.order 0 := by
  rw [S.intermediateBONG.order_eq_ordUnit,
    S.intermediateBONG_valueUnit_zero, ← b.order_eq_ordUnit]

@[simp]
theorem intermediateBONG_order_one (S : b.Lemma65Setup) :
    S.intermediateBONG.order 1 = b.order 1 + 2 * (S.k : Int) := by
  rw [S.intermediateBONG.order_eq_ordUnit]
  rw [S.intermediateBONG_valueUnit_one, ordUnit_mul, ordUnit_pow,
    ordUnit_uniformizerPowerUnit, ← b.order_eq_ordUnit]
  omega

@[simp]
theorem intermediateBONG_order_two (S : b.Lemma65Setup) :
    S.intermediateBONG.order 2 = b.order 2 := by
  apply WithTop.coe_injective
  rw [S.intermediateBONG.coe_order, b.coe_order,
    ← S.intermediateBONG.quadratic_ambientVector,
    ← b.quadratic_ambientVector,
    S.intermediateBONG_ambientVector_two]

/-- From the third vector onward all BONG orders are unchanged. -/
@[simp]
theorem intermediateBONG_order_succ_succ
    (S : b.Lemma65Setup) (i : Fin (n + 1)) :
    S.intermediateBONG.order i.succ.succ = b.order i.succ.succ := by
  apply WithTop.coe_injective
  rw [S.intermediateBONG.coe_order, b.coe_order,
    ← S.intermediateBONG.quadratic_ambientVector,
    ← b.quadratic_ambientVector,
    S.intermediateBONG_ambientVector_succ_succ]

/-- Index-free form of `intermediateBONG_order_succ_succ`. -/
theorem intermediateBONG_order_eq_of_two_le
    (S : b.Lemma65Setup) (i : Fin (n + 3)) (hi : 2 ≤ i.1) :
    S.intermediateBONG.order i = b.order i := by
  let j : Fin (n + 1) := ⟨i.1 - 2, by omega⟩
  have hindex : j.succ.succ = i := by
    apply Fin.ext
    simp only [Fin.val_succ, j]
    omega
  rw [← hindex, S.intermediateBONG_order_succ_succ]

/-- The rescaled initial binary block of `L₀` cannot be hyperbolic at its
natural scale.  If it were, binary volume rigidity would force its order
gap to be `-2e`.  The universal BONG lower bound then forces `k = 0`, and
the resulting hyperbolic pair lies in the original binary prefix, contrary
to the setup hypothesis. -/
theorem intermediateBONG_prefix_not_contains_hyperbolic
    (S : b.Lemma65Setup)
    (heven : Even
      (b.order 1 + 2 * (S.k : Int) - b.order 0)) :
    ¬Lattice.QuadraticSublattice.ContainsScaledHyperbolicPlane
      (S.intermediateBONG.prefixWitness 2 (by omega)).quadraticSublattice
      S.reflectionScaleOrder := by
  classical
  intro hH
  let P := S.intermediateBONG.prefixWitness 2 (by omega)
  have hPzero : P.bong.order 0 = b.order 0 := by
    calc
      P.bong.order 0 =
          S.intermediateBONG.order (P.sourceIndex 0) := P.order_eq 0
      _ = S.intermediateBONG.order 0 := by congr 1
      _ = b.order 0 := S.intermediateBONG_order_zero
  have hPone : P.bong.order 1 =
      b.order 1 + 2 * (S.k : Int) := by
    calc
      P.bong.order 1 =
          S.intermediateBONG.order (P.sourceIndex 1) := P.order_eq 1
      _ = S.intermediateBONG.order 1 := by congr 1
      _ = b.order 1 + 2 * (S.k : Int) :=
        S.intermediateBONG_order_one
  have hsumEven : Even (P.bong.order 0 + P.bong.order 1) := by
    rcases heven with ⟨z, hz⟩
    refine ⟨z + b.order 0, ?_⟩
    rw [hPzero, hPone]
    omega
  have hnatural :
      (P.bong.order 0 + P.bong.order 1) / 2 =
        S.reflectionScaleOrder := by
    have hreflection := S.two_mul_reflectionScaleOrder heven
    rw [hPzero, hPone]
    rcases hsumEven with ⟨z, hz⟩
    omega
  have hH' : P.quadraticSublattice.ContainsScaledHyperbolicPlane
      S.reflectionScaleOrder := by
    simpa only [P] using hH
  have hrestricted : Lattice.ContainsScaledHyperbolicPlane
      (q.restrict P.carrier P.nondegenerate) P.lattice
      S.reflectionScaleOrder :=
    containsScaledHyperbolicPlane_restrict
      P.quadraticSublattice S.reflectionScaleOrder hH'
  have hgapP :=
    P.bong.binaryOrderGap_eq_neg_two_mul_ramificationIndex_of_contains_natural
      (by simpa only [hnatural] using hrestricted)
  have hfinalGap :
      b.order 1 + 2 * (S.k : Int) - b.order 0 =
        -(2 * (ramificationIndex K : Int)) := by
    simpa only [binaryOrderGap, hPzero, hPone] using hgapP
  have hbaseLower : -(2 * (ramificationIndex K : Int)) ≤
      b.order 1 - b.order 0 := by
    let i0 : Fin (n + 3) := ⟨0, by omega⟩
    have hi0 : i0.1 + 1 < n + 3 := by simp [i0]
    have h := b.adjacentOrderGap_ge_neg_two_mul_e i0 hi0
    have hi0Eq : i0 = (0 : Fin (n + 3)) := Fin.ext rfl
    have hi1Eq : (⟨i0.1 + 1, hi0⟩ : Fin (n + 3)) = 1 := Fin.ext rfl
    rw [hi1Eq, hi0Eq] at h
    exact h
  have hkZero : S.k = 0 := by
    have hkNonneg : (0 : Int) ≤ (S.k : Int) := by positivity
    omega
  apply S.firstBinary_not_hyperbolic
  let Q := b.prefixWitness 2 (by omega)
  rcases hH' with ⟨x, y, hx, hy, hpair⟩
  have hcarrier : P.carrier = Q.carrier := by
    rw [P.carrier_eq_segmentCarrier, Q.carrier_eq_segmentCarrier]
    exact S.intermediateBONG_prefixTwo_segmentCarrier_eq
  let xQ : Q.carrier := ⟨(x : V), by
    rw [← hcarrier]
    exact x.property⟩
  let yQ : Q.carrier := ⟨(y : V), by
    rw [← hcarrier]
    exact y.property⟩
  have hxIntermediate : (x : V) ∈ S.intermediateLattice :=
    P.contained x hx
  have hyIntermediate : (y : V) ∈ S.intermediateLattice :=
    P.contained y hy
  have hxL : (xQ : V) ∈ L := by
    change (x : V) ∈ L
    exact ((S.mem_intermediateLattice_iff (x : V)).1 hxIntermediate).1
  have hyL : (yQ : V) ∈ L := by
    change (y : V) ∈ L
    exact ((S.mem_intermediateLattice_iff (y : V)).1 hyIntermediate).1
  have hxQ : xQ ∈ Q.lattice := Q.contains_parent xQ hxL
  have hyQ : yQ ∈ Q.lattice := Q.contains_parent yQ hyL
  have hscale : S.reflectionScaleOrder =
      (b.order 0 + b.order 1) / 2 := by
    have hbaseEven : Even (b.order 1 - b.order 0) := by
      simpa only [hkZero, Nat.cast_zero, mul_zero, add_zero] using heven
    rcases hbaseEven with ⟨z, hz⟩
    simp only [reflectionScaleOrder, hkZero, Nat.cast_zero,
      mul_zero, add_zero]
    omega
  refine ⟨xQ, yQ, hxQ, hyQ, ?_⟩
  rw [hscale] at hpair
  simpa only [xQ, yQ] using hpair

/-- In the short-shift branch (`k = 0` or `1`), Property B supplies the
extra two-step inequalities needed for the intermediate BONG to remain
good. -/
theorem intermediateBONG_isGood_of_k_le_one
    (S : b.Lemma65Setup) (hB : b.HasPropertyB) (hk : S.k ≤ 1) :
    S.intermediateBONG.IsGood := by
  intro i hi
  by_cases hiZero : i.1 = 0
  · have hiEq : i = 0 := Fin.ext hiZero
    subst i
    have htarget :
        (⟨(0 : Fin (n + 3)).1 + 2, hi⟩ : Fin (n + 3)) = 2 :=
      Fin.ext rfl
    rw [S.intermediateBONG_order_zero, htarget,
      S.intermediateBONG_order_two]
    exact hB.isGood 0 hi
  by_cases hiOne : i.1 = 1
  · have hiEq : i = 1 := Fin.ext hiOne
    subst i
    let target : Fin (n + 3) :=
      ⟨(1 : Fin (n + 3)).1 + 2, hi⟩
    have htargetTwo : 2 ≤ target.1 := by
      simp only [target, Fin.val_one]
      omega
    rw [S.intermediateBONG_order_one,
      S.intermediateBONG_order_eq_of_two_le target htargetTwo]
    have htwo := hB.twoStep_add_two_le (1 : Fin (n + 3)) hi
    change b.order 1 + 2 ≤ b.order target at htwo
    omega
  · rw [S.intermediateBONG_order_eq_of_two_le i (by omega),
      S.intermediateBONG_order_eq_of_two_le ⟨i.1 + 2, hi⟩ (by simp)]
    exact hB.isGood i hi

/-- After the second vector has been multiplied by `πᵏ`, multiplying the
first vector by the same power restores the original first binary
parameter. -/
theorem intermediateBONG_headRescaledFirstParameter_eq
    (S : b.Lemma65Setup) :
    S.intermediateBONG.headRescaledFirstParameter S.k =
      b.adjacentParameter 0 (by simp) := by
  rw [headRescaledFirstParameter_eq_mul_inv_square]
  unfold adjacentParameter
  change
    (S.intermediateBONG.valueUnit 1 /
        S.intermediateBONG.valueUnit 0) *
        (uniformizerPowerUnit K (S.k : Int))⁻¹ ^ 2 =
      b.valueUnit 1 / b.valueUnit 0
  rw [S.intermediateBONG_valueUnit_zero,
    S.intermediateBONG_valueUnit_one]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Rescaling the head of the intermediate binary block by the same exponent
recovers the original admissible adjacent parameter, hence the binary block
required by Lemma 6.1 exists. -/
theorem intermediateBONG_headBinaryRescaleExists
    (S : b.Lemma65Setup) :
    S.intermediateBONG.HeadBinaryRescaleExists S.k := by
  refine ⟨S.intermediateBONG.headBinaryRescaleWitnessOfAdmissible S.k ?_⟩
  change IsBinaryParameterAdmissible
    (S.intermediateBONG.headRescaledFirstParameter S.k)
  rw [S.intermediateBONG_headRescaledFirstParameter_eq]
  exact b.adjacentParameter_isBinaryParameterAdmissible 0 (by simp)

/-- Lemma 6.1(ii) applied only to the initial binary component of the
intermediate lattice.  Its third-vector hypothesis is vacuous. -/
theorem exists_initialBinaryHeadDepth
    (S : b.Lemma65Setup)
    (T : TwoBlockSplitWitness S.intermediateBONG 2 (by omega)) :
    Nonempty (T.left.bong.HeadDepthWitness S.k) := by
  have hparameter :
      T.left.bong.headRescaledFirstParameter S.k =
        b.adjacentParameter 0 (by simp) := by
    rw [TwoBlockSplitWitness.left_headRescaledFirstParameter_eq_of_cut_two T,
      S.intermediateBONG_headRescaledFirstParameter_eq]
  have hexists : T.left.bong.HeadBinaryRescaleExists S.k := by
    refine ⟨T.left.bong.headBinaryRescaleWitnessOfAdmissible S.k ?_⟩
    change IsBinaryParameterAdmissible
      (T.left.bong.headRescaledFirstParameter S.k)
    rw [hparameter]
    exact b.adjacentParameter_isBinaryParameterAdmissible 0 (by simp)
  exact T.left.bong.beliLemma61_headDepth_proved
    (SegmentWitness.isGood_of_length_two T.left) S.k hexists (by
      intro h
      omega)

/-- In the finite-defect boundary branch the first two vectors of the
intermediate BONG split from the deeper complement. -/
theorem exists_intermediateInitialBinarySplit_of_boundaryOrderData
    (S : b.Lemma65Setup) (D : S.BoundaryOrderData) :
    S.intermediateBONG.HasTwoBlockSplit 2 (by omega) := by
  apply S.intermediateBONG.exists_twoBlockSplit_of_leftOrders_le_rightHead
    2 (by omega) (by omega)
  intro i
  rw [SegmentWitness.order_eq, SegmentWitness.order_eq]
  fin_cases i
  · change S.intermediateBONG.order 0 ≤
      S.intermediateBONG.order 2
    rw [S.intermediateBONG_order_zero,
      S.intermediateBONG_order_two]
    have hkNonneg : (0 : Int) ≤ (S.k : Int) := by positivity
    have hhead := D.headRescaledOrder_le_critical
    have hthird := D.critical_lt_third
    omega
  · change S.intermediateBONG.order 1 ≤
      S.intermediateBONG.order 2
    rw [S.intermediateBONG_order_one,
      S.intermediateBONG_order_two]
    exact le_of_lt D.tailOrder_lt_third

/-- In the short-shift branch, Lemma 6.1 supplies the concrete lattice
`<πᵏx₁,πᵏx₂,x₃,…>`. -/
theorem exists_intermediateHeadDepth_of_k_le_one
    (S : b.Lemma65Setup) (hB : b.HasPropertyB) (hk : S.k ≤ 1) :
    Nonempty (S.intermediateBONG.HeadDepthWitness S.k) := by
  have hthird : ∀ _h : 1 ≤ n + 1,
      S.intermediateBONG.order 0 + 2 * (S.k : Int) ≤
        S.intermediateBONG.order ⟨2, by omega⟩ := by
    intro _h
    let target : Fin (n + 3) := ⟨2, by omega⟩
    have htargetTwo : 2 ≤ target.1 := by
      simp [target]
    rw [S.intermediateBONG_order_zero,
      S.intermediateBONG_order_eq_of_two_le target htargetTwo]
    have htwo := hB.twoStep_add_two_le (0 : Fin (n + 3)) (by
      simp)
    have htwo' : b.order 0 + 2 ≤ b.order target := by
      simpa [target] using htwo
    omega
  exact S.intermediateBONG.beliLemma61_ii
    (S.intermediateBONG_isGood_of_k_le_one hB hk) S.k
    S.intermediateBONG_headBinaryRescaleExists hthird

/-- The order occurring in Lemma 6.5(ii) is above the carrier threshold of
the twice-rescaled initial block. -/
theorem headDepth_threshold_le_reflection_order
    (S : b.Lemma65Setup) (hlow : b.Lemma65LowRange S)
    (hk : S.k ≤ 1) :
    b.order 0 + 2 * (S.k : Int) - 1 ≤
      S.reflectionScaleOrder + ramificationIndex K := by
  have hlower := b.adjacentOrderGap_ge_neg_two_mul_e
    (0 : Fin (n + 3)) (by simp)
  have heven := S.lowRange_gap_even hlow
  rcases heven with ⟨m, hm⟩
  simp only [reflectionScaleOrder]
  change -(2 * (ramificationIndex K : Int)) ≤
      b.order 1 - b.order 0 at hlower
  omega

/-- Consequently every vector of `L₀` having the critical norm order lies
in the explicit twice-rescaled BONG lattice furnished by Lemma 6.1. -/
theorem mem_intermediateHeadDepth_of_critical_order
    (S : b.Lemma65Setup) (hlow : b.Lemma65LowRange S) (hk : S.k ≤ 1)
    (W : S.intermediateBONG.HeadDepthWitness S.k)
    (v : V) (hv : v ∈ S.intermediateLattice)
    (horder : ord K (q.quadratic v) =
      ((S.reflectionScaleOrder + ramificationIndex K : Int) :
        WithTop Int)) :
    v ∈ W.lattice := by
  rw [W.mem_lattice_iff]
  refine ⟨hv, ?_⟩
  rw [S.intermediateBONG_order_zero, horder]
  exact_mod_cast S.headDepth_threshold_le_reflection_order hlow hk

/-- Multiplication by `πᵏ` sends the original lattice into the
intermediate lattice `L₀`: on the projected tail this is exactly the head
rescaling already recorded by `S.tailRescale`. -/
theorem uniformizerPower_smul_mem_intermediateLattice
    (S : b.Lemma65Setup) (y : V) (hy : y ∈ L) :
    ((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K) • y ∈
      S.intermediateLattice := by
  rw [S.mem_intermediateLattice_iff]
  constructor
  · let aO : IntegerRing K :=
      ⟨(uniformizerPowerUnit K (S.k : Int) : K),
        uniformizerPowerUnit_nat_mem_integerRing S.k⟩
    exact L.smul_mem aO hy
  · have hprojection := S.tailRescale.uniformizerPower_smul_mem
      (S.projection y) (S.projection_mem_tail y hy)
    simpa only [projection, lemma65Projection, map_smul] using hprojection

/-- The same uniformizer multiple already lies in the twice-rescaled
head-depth lattice furnished by Lemma 6.1.  Its quadratic order is one unit
deeper than the exact carrier threshold. -/
theorem uniformizerPower_smul_mem_intermediateHeadDepth
    (S : b.Lemma65Setup)
    (W : S.intermediateBONG.HeadDepthWitness S.k)
    (y : V) (hy : y ∈ L) :
    ((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K) • y ∈
      W.lattice := by
  rw [W.mem_lattice_iff_ord_ge_head_depth]
  constructor
  · exact S.uniformizerPower_smul_mem_intermediateLattice y hy
  · have hyIdeal := Lattice.quadratic_mem_normIdeal_of_mem q L hy
    rw [b.head_isNormGenerator.normIdeal_eq,
      ← b.value_zero_eq_quadratic_head] at hyIdeal
    have hyOrder : (b.order 0 : WithTop Int) ≤
        ord K (q.quadratic y) := by
      rw [b.coe_order]
      exact Lattice.ord_le_of_mem_principalIdeal
        (b.value_ne_zero 0) hyIdeal
    have hpowerOrder :
        ord K (((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K) ^ 2) =
          ((2 * (S.k : Int) : Int) : WithTop Int) := by
      rw [ord_pow, ← coe_ordUnit, ordUnit_uniformizerPowerUnit]
      norm_cast
    rw [q.quadratic_smul, ord_mul, hpowerOrder,
      S.intermediateBONG_order_zero]
    have hshift := add_le_add_left hyOrder
      ((2 * (S.k : Int) : Int) : WithTop Int)
    have hthreshold :
        ((b.order 0 + 2 * (S.k : Int) - 1 : Int) : WithTop Int) ≤
          ((2 * (S.k : Int) : Int) : WithTop Int) +
            (b.order 0 : WithTop Int) := by
      norm_cast
      omega
    exact hthreshold.trans (by simpa only [add_comm] using hshift)

/-- In the short-shift branch with a unary first Jordan component, the
rescaled projected tail has scale at least `s+k`.  Property B supplies the
only new two-step inequality needed after rescaling its head. -/
theorem tailRescale_scaleIdeal_le_powerIdeal_of_short_of_first_lt_second
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hlow : b.Lemma65LowRange S) (hk : S.k ≤ 1)
    (hfirst : b.order 0 < b.order 1) :
    Lattice.scaleIdeal
        (q.orthogonalSpace b.head b.head_isAnisotropic)
        S.tailRescale.lattice ≤
      Lattice.powerIdeal (K := K)
        (S.reflectionScaleOrder + (S.k : Int)) := by
  have htailGood : S.tailRescale.bong.IsGood :=
    S.tailRescale.isGood_of_original hB.tail_for_lemma62.isGood (by
      intro hn
      let i1 : Fin (n + 3) := ⟨1, by omega⟩
      have htwo := hB.twoStep_add_two_le
        i1 (by simp [i1]; omega)
      have hi1 : i1 = (1 : Fin (n + 3)) := by
        apply Fin.ext
        simp [i1]
      have htailZero : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
        rw [b.order_tail]
        congr 1
      let i2 : Fin (n + 2) := ⟨2, by omega⟩
      change b.tail.order 0 + 2 * (S.k : Int) ≤ b.tail.order i2
      rw [htailZero, b.order_tail]
      have hindex : i2.succ =
          (⟨i1.1 + 2, by simp [i1]; omega⟩ :
            Fin (n + 3)) := by
        apply Fin.ext
        simp [i1, i2]
      have htwo' : b.order (1 : Fin (n + 3)) + 2 ≤
          b.order i2.succ := by
        calc
          b.order (1 : Fin (n + 3)) + 2 = b.order i1 + 2 := by
            rw [hi1]
          _ ≤ b.order ⟨i1.1 + 2, by simp [i1]; omega⟩ := htwo
          _ = b.order i2.succ := by rw [hindex]
      omega)
  have hscaleDoubled := beliCorollary44_iv_unconditional
    S.tailRescale.bong htailGood
  have heven := S.lowRange_gap_even hlow
  have htailZero : S.tailRescale.bong.order 0 =
      b.order 1 + 2 * (S.k : Int) := by
    rw [S.tailRescale.order_zero_eq, b.order_tail]
    congr 1
  have htailOne : S.tailRescale.bong.order 1 = b.order 2 := by
    have h := S.tailRescale.order_succ_eq (0 : Fin (n + 1))
    change S.tailRescale.bong.order 1 = b.tail.order 1 at h
    rw [h, b.order_tail]
    congr 1
  have htwoStep := hB.twoStep_add_two_le
    (0 : Fin (n + 3)) (by simp)
  change b.order 0 + 2 ≤ b.order 2 at htwoStep
  have hbound :
      2 * (S.reflectionScaleOrder + (S.k : Int)) ≤
        min (2 * S.tailRescale.bong.order 0)
          (S.tailRescale.bong.order 0 +
            S.tailRescale.bong.order 1) := by
    rw [htailZero, htailOne, le_min_iff]
    have hreflection := S.two_mul_reflectionScaleOrder heven
    constructor <;> omega
  exact scaleIdeal_le_powerIdeal_of_hasDoubledScaleOrder
    hscaleDoubled hbound

/-- A norm-generating projection has precisely the order of the rescaled
first tail vector. -/
theorem ord_quadratic_projection_of_isNormGenerator
    (S : b.Lemma65Setup) (x : V)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x)) :
    ord K ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
      (S.projection x)) =
      ((b.order 1 + 2 * (S.k : Int) : Int) : WithTop Int) := by
  have horder :=
    S.tailRescale.bong.ord_quadratic_isNormGenerator_eq_order_zero
      (S.projection x) hgenerator
  rw [S.tailRescale.order_zero_eq, b.order_tail] at horder
  simpa using horder

/-- Equal head value and orthogonal projection give the normalized identity
`Q(pr(x)) = (1-a^2)Q(x₁)`. -/
theorem quadratic_projection_eq_one_sub_sq_mul
    (S : b.Lemma65Setup) (x : V)
    (heq : q.quadratic x = q.quadratic b.head) :
    (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
        (S.projection x) =
      (1 - (q.bilin b.head x / q.quadratic b.head) ^ 2) *
        q.quadratic b.head := by
  let a : K := q.bilin b.head x / q.quadratic b.head
  have hdecomp := Lattice.quadratic_projection_decomposition
    q b.head b.head_isAnisotropic x
  change q.quadratic x =
      a ^ 2 * q.quadratic b.head +
        (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (S.projection x) at hdecomp
  rw [heq] at hdecomp
  change (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
      (S.projection x) = (1 - a ^ 2) * q.quadratic b.head
  have hsub :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (S.projection x) =
        q.quadratic b.head - a ^ 2 * q.quadratic b.head := by
    apply (eq_sub_iff_add_eq).2
    simpa only [add_comm] using hdecomp.symm
  rw [hsub]
  ring

/-- The normalized quadratic value of a nonisotropic projection.  In the
notation of the paper this is the unit parameter `Q(y)/Q(x₁)=1-a²` attached
to the binary lattice spanned by `x₁` and `x`. -/
noncomputable def projectionFactorUnit
    (S : b.Lemma65Setup) (x : V)
    (hne : 1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0) : Kˣ :=
  Units.mk0
    (1 - (q.bilin b.head x / q.quadratic b.head) ^ 2) hne

@[simp]
theorem coe_projectionFactorUnit
    (S : b.Lemma65Setup) (x : V)
    (hne : 1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0) :
    ((S.projectionFactorUnit x hne : Kˣ) : K) =
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 :=
  rfl

/-- The order of the projected quadratic value is the head order plus the
order of its normalized projection factor. -/
theorem ord_quadratic_projection_eq_head_add_projectionFactor
    (S : b.Lemma65Setup) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (hne : 1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0) :
    ord K ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
        (S.projection x)) =
      ((b.order 0 + ordUnit K (S.projectionFactorUnit x hne) : Int) :
        WithTop Int) := by
  rw [S.quadratic_projection_eq_one_sub_sq_mul x heq, ord_mul,
    ← S.coe_projectionFactorUnit x hne, ← coe_ordUnit,
    ← b.value_zero_eq_quadratic_head, ← b.coe_order]
  norm_cast
  omega

/-- The projection parameter is an admissible binary parameter.  The shear
is the coefficient `a=B(x₁,x)/Q(x₁)`; its two integrality conditions are the
mixed-pairing lemma and the identity `a²+(1-a²)=1`. -/
theorem projectionFactorUnit_isBinaryParameterAdmissible
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (hne : 1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0) :
    IsBinaryParameterAdmissible (S.projectionFactorUnit x hne) := by
  let a : K := q.bilin b.head x / q.quadratic b.head
  refine ⟨a, ?_, ?_⟩
  · exact Lattice.two_projectionCoefficient_mem_integerRing
      q L b.head x b.head_isNormGenerator b.head_isAnisotropic hx
  · have hone : (1 : K) ∈ IntegerRing K := (IntegerRing K).one_mem
    convert hone using 1 <;>
      simp only [a, coe_projectionFactorUnit] <;> ring

/-- The same presentation has an equal-value norm-generator basis: the
second standard vector itself is a companion, because `a²+(1-a²)=1`. -/
theorem projectionFactorUnit_hasSomeEqualNormGeneratorBasis
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (hne : 1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0) :
    HasSomeEqualNormGeneratorBasis (S.projectionFactorUnit x hne) := by
  let a : K := q.bilin b.head x / q.quadratic b.head
  refine ⟨a, ?_, ?_, ?_⟩
  · exact Lattice.two_projectionCoefficient_mem_integerRing
      q L b.head x b.head_isNormGenerator b.head_isAnisotropic hx
  · have hone : (1 : K) ∈ IntegerRing K := (IntegerRing K).one_mem
    convert hone using 1 <;>
      simp only [a, coe_projectionFactorUnit] <;> ring
  · refine ⟨0, 1, (IntegerRing K).zero_mem, ?_, ?_⟩
    · simp [IsValuationUnit]
    · simp only [zero_pow, OfNat.ofNat_ne_zero, zero_mul, add_zero,
        one_pow, mul_one, a, coe_projectionFactorUnit]
      ring

/-- Therefore the normalized value of every nonisotropic projection falls
under the exhaustive four-way classification of Lemma 3.17. -/
theorem projectionFactorUnit_parameterCases
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (hne : 1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0) :
    BeliLemma317ParameterCases (K := K)
      (ordUnit K (S.projectionFactorUnit x hne))
      (normalizedUnitPart K (S.projectionFactorUnit x hne)) := by
  let p : Kˣ := S.projectionFactorUnit x hne
  have hadmissible : IsBinaryParameterAdmissible p := by
    simpa only [p] using
      S.projectionFactorUnit_isBinaryParameterAdmissible x hx hne
  have hsome : HasSomeEqualNormGeneratorBasis p := by
    simpa only [p] using
      S.projectionFactorUnit_hasSomeEqualNormGeneratorBasis x hx hne
  have hall : HasEveryEqualNormGeneratorBasis p :=
    (hasSomeEqualNormGeneratorBasis_iff_hasEvery p hadmissible).1 hsome
  let R : Int := ordUnit K p
  let epsilon : Kˣ := normalizedUnitPart K p
  have hepsilon : IsValuationUnit K (epsilon : K) :=
    normalizedUnitPart_isValuationUnit K p
  have hfactor : uniformizerPowerUnit K R * epsilon = p := by
    simpa only [R, epsilon] using
      uniformizerPower_mul_normalizedUnitPart K p
  have hadmissible' : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * epsilon) := by
    rwa [hfactor]
  have hall' : HasEveryEqualNormGeneratorBasis
      (uniformizerPowerUnit K R * epsilon) := by
    rwa [hfactor]
  simpa only [p, R, epsilon] using
    beliLemma317ParameterCases_of_hasEvery R epsilon hepsilon
      hadmissible' hall'

/-- In the nonendpoint even branch, Property B forces every norm-generator
value ratio of the original projected tail to have defect strictly deeper
than the first-pair cutoff.  This is the estimate denoted
`d(x/ε₂) > e-R₂/2` in case (4) of Beli's proof. -/
theorem tailNormGeneratorRatio_defect_ge_cutoff_succ_intrinsic
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hne : b.lemma62Gap ≠ 2 * (ramificationIndex K : Int))
    (y : q.vectorOrthogonal b.head)
    (hy : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic) y) :
    ((b.lemma62DefectCutoff + 1 : Nat) : ℕ∞) ≤
      quadraticDefect K (b.tail.normGeneratorValueRatioUnit y hy) := by
  let w := b.headInverseRescaleWitness
  let wt := b.tail.headInverseRescaleWitness
  have hBInv : b.HasPropertyBOrInverse w := Or.inl hB
  have htailB : b.tail.HasPropertyB := hB.tail_for_lemma62
  have htailBInv : b.tail.HasPropertyBOrInverse wt := Or.inl htailB
  have hcutCast : (b.lemma62DefectCutoff : Int) =
      (ramificationIndex K : Int) - b.lemma62Gap / 2 :=
    b.lemma62DefectCutoff_cast heven hupper
  have hbranches := b.lemma62_tail_large_or_even_high
    w hBInv heven hupper hne
  rcases hbranches with hlarge | ⟨hevenTail, hupperTail, hdefectTail⟩
  · have htailOrder : b.tail.order 0 ≤ b.tail.order 1 := by
      unfold lemma62Gap at hlarge
      omega
    have hvalues := b.tail.beliLemma62_ii_a
      wt htailBInv htailOrder
    have hrelative : (b.lemma62DefectCutoff + 1 : Int) ≤
        b.tail.lemma62Gap := by
      rw [hcutCast]
      have hfirstLower :=
        (b.adjacentParameter_isBinaryParameterAdmissible 0 (by simp)).ordUnit_ge_neg_two_mul_e
      rw [b.ordUnit_adjacentParameter_zero] at hfirstLower
      have heNonneg : (0 : Int) ≤ ramificationIndex K := by positivity
      rcases heven with ⟨r, hr⟩
      omega
    have hexponent : b.tail.order 0 +
        (b.lemma62DefectCutoff + 1 : Int) ≤ b.tail.order 1 := by
      unfold lemma62Gap at hrelative
      omega
    have hclass :=
      b.tail.normGeneratorValueRatioClass_mem_principal_of_quadraticValues
        (b.tail.order 1) (b.lemma62DefectCutoff + 1)
        hexponent hvalues y hy
    exact natCast_le_quadraticDefect_of_unitClass_mem
      (b.tail.normGeneratorValueRatioValuationUnit y hy)
      (b.lemma62DefectCutoff + 1) hclass
  · have hvalues := b.tail.beliLemma62_ii_c
      wt htailBInv hevenTail hupperTail hdefectTail
    have hzeroTwo : b.order (0 : Fin (n + 3)) <
        b.order (2 : Fin (n + 3)) := by
      exact hB.hasPropertyA (0 : Fin (n + 3)) (by simp)
    have htailZero : b.tail.order (0 : Fin (n + 2)) =
        b.order (1 : Fin (n + 3)) := by
      rw [b.order_tail]
      congr 1
    have htailOne : b.tail.order (1 : Fin (n + 2)) =
        b.order (2 : Fin (n + 3)) := by
      rw [b.order_tail]
      congr 1
    have hgapSumPos : 0 < b.lemma62Gap + b.tail.lemma62Gap := by
      unfold lemma62Gap
      rw [htailZero, htailOne]
      omega
    have hexponent : b.tail.order 0 +
        (b.lemma62DefectCutoff + 1 : Int) ≤
          b.tail.lemma62HighExponent := by
      rw [hcutCast]
      unfold lemma62HighExponent
      unfold lemma62Gap at hgapSumPos
      rcases heven with ⟨r, hr⟩
      rcases hevenTail with ⟨t, ht⟩
      unfold lemma62Gap at hr ht ⊢
      omega
    have hclass :=
      b.tail.normGeneratorValueRatioClass_mem_principal_of_quadraticValues
        b.tail.lemma62HighExponent (b.lemma62DefectCutoff + 1)
        hexponent hvalues y hy
    exact natCast_le_quadraticDefect_of_unitClass_mem
      (b.tail.normGeneratorValueRatioValuationUnit y hy)
      (b.lemma62DefectCutoff + 1) hclass

/-- Compatibility wrapper for the original concrete-setup API. -/
theorem tailNormGeneratorRatio_defect_ge_cutoff_succ
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hne : b.lemma62Gap ≠ 2 * (ramificationIndex K : Int))
    (y : q.vectorOrthogonal b.head)
    (hy : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic) y) :
    ((b.lemma62DefectCutoff + 1 : Nat) : ℕ∞) ≤
      quadraticDefect K (b.tail.normGeneratorValueRatioUnit y hy) :=
  tailNormGeneratorRatio_defect_ge_cutoff_succ_intrinsic
    b hB heven hupper hne y hy

/-- A norm-generating projection is anisotropic, hence its normalized factor
`1-a²` is nonzero. -/
theorem projectionFactor_ne_zero_of_originalTail_isNormGenerator
    (S : b.Lemma65Setup) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic)
      (S.projection x)) :
    1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0 := by
  intro hzero
  have hprojectionEq := S.quadratic_projection_eq_one_sub_sq_mul x heq
  rw [hzero, zero_mul] at hprojectionEq
  exact b.tail.isAnisotropic_of_isNormGenerator_binary hgenerator
    hprojectionEq

/-- Exact multiplicative relation used in case (4): the projection factor is
the first adjacent parameter times the norm-generator value ratio in the
original projected tail. -/
theorem projectionFactorUnit_eq_adjacentParameter_mul_tailRatio
    (S : b.Lemma65Setup) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic)
      (S.projection x)) :
    S.projectionFactorUnit x
        (S.projectionFactor_ne_zero_of_originalTail_isNormGenerator
          x heq hgenerator) =
      b.adjacentParameter 0 (by simp) *
        b.tail.normGeneratorValueRatioUnit (S.projection x) hgenerator := by
  apply Units.ext
  have hprojectionEq := S.quadratic_projection_eq_one_sub_sq_mul x heq
  simp only [coe_projectionFactorUnit, Units.val_mul,
    adjacentParameter, Units.val_div_eq_div_val,
    normGeneratorValueRatioUnit, Units.val_mk0, coe_valueUnit]
  have hnext :
      (⟨(0 : Fin (n + 3)).1 + 1, by simp⟩ : Fin (n + 3)) = 1 :=
    Fin.ext rfl
  rw [hnext]
  rw [← b.value_zero_eq_quadratic_head]
  rw [b.value_tail (0 : Fin (n + 2))]
  have hindex : (0 : Fin (n + 2)).succ = (1 : Fin (n + 3)) :=
    Fin.ext rfl
  rw [hindex]
  rw [← b.value_zero_eq_quadratic_head] at hprojectionEq
  rw [hprojectionEq]
  field_simp [b.value_ne_zero 0, b.value_ne_zero 1]

/-- Hence that factor has the original first adjacent order. -/
theorem ordUnit_projectionFactorUnit_of_originalTail_isNormGenerator
    (S : b.Lemma65Setup) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic)
      (S.projection x)) :
    ordUnit K (S.projectionFactorUnit x
      (S.projectionFactor_ne_zero_of_originalTail_isNormGenerator
        x heq hgenerator)) = b.lemma62Gap := by
  rw [S.projectionFactorUnit_eq_adjacentParameter_mul_tailRatio
    x heq hgenerator, ordUnit_mul, b.ordUnit_adjacentParameter_zero]
  have hratio := b.tail.normGeneratorValueRatioUnit_isValuationUnit
    (S.projection x) hgenerator
  rw [(isValuationUnit_iff_ordUnit_eq_zero K _).1 hratio]
  omega

/-! ### Intrinsic projection API

The following variants deliberately do not take a `Lemma65Setup`.  They are
used in the exceptional branch, where the least admissible exponent is two
but the paper constructs only the once-rescaled tail. -/

/-- Every intrinsic projection of a parent-lattice vector belongs to the
original projected tail. -/
theorem lemma65Projection_mem_tail_intrinsic
    (b : BONG V q L (n + 3)) (x : V) (hx : x ∈ L) :
    b.lemma65Projection x ∈
      L.projectedLattice q b.head b.head_isAnisotropic := by
  exact Lattice.projection_mem_projectedLattice
    q L b.head b.head_isAnisotropic hx

/-- Equal head value gives the intrinsic normalized projection identity. -/
theorem quadratic_lemma65Projection_eq_one_sub_sq_mul_intrinsic
    (b : BONG V q L (n + 3)) (x : V)
    (heq : q.quadratic x = q.quadratic b.head) :
    (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
        (b.lemma65Projection x) =
      (1 - (q.bilin b.head x / q.quadratic b.head) ^ 2) *
        q.quadratic b.head := by
  let a : K := q.bilin b.head x / q.quadratic b.head
  have hdecomp := Lattice.quadratic_projection_decomposition
    q b.head b.head_isAnisotropic x
  change q.quadratic x =
      a ^ 2 * q.quadratic b.head +
        (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (b.lemma65Projection x) at hdecomp
  rw [heq] at hdecomp
  change (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
      (b.lemma65Projection x) = (1 - a ^ 2) * q.quadratic b.head
  have hsub :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (b.lemma65Projection x) =
        q.quadratic b.head - a ^ 2 * q.quadratic b.head := by
    apply (eq_sub_iff_add_eq).2
    simpa only [add_comm] using hdecomp.symm
  rw [hsub]
  ring

/-- The normalized quadratic factor of an anisotropic intrinsic projection. -/
noncomputable def lemma65ProjectionFactorUnitIntrinsic
    (b : BONG V q L (n + 3)) (x : V)
    (hne : 1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0) : Kˣ :=
  Units.mk0
    (1 - (q.bilin b.head x / q.quadratic b.head) ^ 2) hne

@[simp]
theorem coe_lemma65ProjectionFactorUnitIntrinsic
    (b : BONG V q L (n + 3)) (x : V)
    (hne : 1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0) :
    ((lemma65ProjectionFactorUnitIntrinsic b x hne : Kˣ) : K) =
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 :=
  rfl

/-- The intrinsic projection factor is an admissible binary parameter. -/
theorem lemma65ProjectionFactorUnitIntrinsic_isBinaryParameterAdmissible
    (b : BONG V q L (n + 3)) (x : V) (hx : x ∈ L)
    (hne : 1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0) :
    IsBinaryParameterAdmissible
      (lemma65ProjectionFactorUnitIntrinsic b x hne) := by
  let a : K := q.bilin b.head x / q.quadratic b.head
  refine ⟨a, ?_, ?_⟩
  · exact Lattice.two_projectionCoefficient_mem_integerRing
      q L b.head x b.head_isNormGenerator b.head_isAnisotropic hx
  · have hone : (1 : K) ∈ IntegerRing K := (IntegerRing K).one_mem
    convert hone using 1 <;>
      simp only [a, coe_lemma65ProjectionFactorUnitIntrinsic] <;> ring

/-- The intrinsic projection factor has an equal-value generator basis. -/
theorem lemma65ProjectionFactorUnitIntrinsic_hasSomeEqualNormGeneratorBasis
    (b : BONG V q L (n + 3)) (x : V) (hx : x ∈ L)
    (hne : 1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0) :
    HasSomeEqualNormGeneratorBasis
      (lemma65ProjectionFactorUnitIntrinsic b x hne) := by
  let a : K := q.bilin b.head x / q.quadratic b.head
  refine ⟨a, ?_, ?_, ?_⟩
  · exact Lattice.two_projectionCoefficient_mem_integerRing
      q L b.head x b.head_isNormGenerator b.head_isAnisotropic hx
  · have hone : (1 : K) ∈ IntegerRing K := (IntegerRing K).one_mem
    convert hone using 1 <;>
      simp only [a, coe_lemma65ProjectionFactorUnitIntrinsic] <;> ring
  · refine ⟨0, 1, (IntegerRing K).zero_mem, ?_, ?_⟩
    · simp [IsValuationUnit]
    · simp only [zero_pow, OfNat.ofNat_ne_zero, zero_mul, add_zero,
        one_pow, mul_one, a, coe_lemma65ProjectionFactorUnitIntrinsic]
      ring

/-- Exhaustive Lemma 3.17 classification for the intrinsic factor. -/
theorem lemma65ProjectionFactorUnitIntrinsic_parameterCases
    (b : BONG V q L (n + 3)) (x : V) (hx : x ∈ L)
    (hne : 1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0) :
    BeliLemma317ParameterCases (K := K)
      (ordUnit K (lemma65ProjectionFactorUnitIntrinsic b x hne))
      (normalizedUnitPart K
        (lemma65ProjectionFactorUnitIntrinsic b x hne)) := by
  let p : Kˣ := lemma65ProjectionFactorUnitIntrinsic b x hne
  have hadmissible : IsBinaryParameterAdmissible p := by
    simpa only [p] using
      lemma65ProjectionFactorUnitIntrinsic_isBinaryParameterAdmissible
        b x hx hne
  have hsome : HasSomeEqualNormGeneratorBasis p := by
    simpa only [p] using
      lemma65ProjectionFactorUnitIntrinsic_hasSomeEqualNormGeneratorBasis
        b x hx hne
  have hall : HasEveryEqualNormGeneratorBasis p :=
    (hasSomeEqualNormGeneratorBasis_iff_hasEvery p hadmissible).1 hsome
  let R : Int := ordUnit K p
  let epsilon : Kˣ := normalizedUnitPart K p
  have hepsilon : IsValuationUnit K (epsilon : K) :=
    normalizedUnitPart_isValuationUnit K p
  have hfactor : uniformizerPowerUnit K R * epsilon = p := by
    simpa only [R, epsilon] using
      uniformizerPower_mul_normalizedUnitPart K p
  have hadmissible' : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * epsilon) := by
    rwa [hfactor]
  have hall' : HasEveryEqualNormGeneratorBasis
      (uniformizerPowerUnit K R * epsilon) := by
    rwa [hfactor]
  simpa only [p, R, epsilon] using
    beliLemma317ParameterCases_of_hasEvery R epsilon hepsilon
      hadmissible' hall'

/-- The quadratic order of the intrinsic projection is the head order plus
the order of its normalized factor. -/
theorem ord_quadratic_lemma65Projection_eq_head_add_factorIntrinsic
    (b : BONG V q L (n + 3)) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (hne : 1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0) :
    ord K ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
        (b.lemma65Projection x)) =
      ((b.order 0 + ordUnit K
        (lemma65ProjectionFactorUnitIntrinsic b x hne) : Int) :
          WithTop Int) := by
  rw [quadratic_lemma65Projection_eq_one_sub_sq_mul_intrinsic b x heq,
    ord_mul, ← coe_lemma65ProjectionFactorUnitIntrinsic b x hne,
    ← coe_ordUnit, ← b.value_zero_eq_quadratic_head, ← b.coe_order]
  norm_cast
  omega

/-- Over a residue-two field, an intrinsic nonzero projection factor cannot
have order exactly `2e`. -/
theorem ordUnit_lemma65ProjectionFactorUnitIntrinsic_ne_two_e_of_residue_two
    (b : BONG V q L (n + 3)) (x : V) (hx : x ∈ L)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hresidue : ¬HasResidueFieldMoreThanTwoElements (K := K)) :
    ordUnit K (lemma65ProjectionFactorUnitIntrinsic b x hfactorNe) ≠
      2 * (ramificationIndex K : Int) := by
  intro hpOrder
  let p : Kˣ := lemma65ProjectionFactorUnitIntrinsic b x hfactorNe
  let εp : Kˣ := normalizedUnitPart K p
  have hpOrder' : ordUnit K p =
      2 * (ramificationIndex K : Int) := by
    simpa only [p] using hpOrder
  have hεpUnit : IsValuationUnit K (εp : K) := by
    simpa only [εp] using normalizedUnitPart_isValuationUnit K p
  have hdefectOne : (1 : ℕ∞) ≤ quadraticDefect K (-εp) := by
    have hnegUnit : IsValuationUnit K ((-εp : Kˣ) : K) := by
      change ord K (-((εp : Kˣ) : K)) = 0
      rw [ord_neg]
      exact hεpUnit
    exact one_le_quadraticDefect_of_unit (-εp) hnegUnit
  have hcases : BeliLemma317ParameterCases (K := K)
      (2 * (ramificationIndex K : Int)) εp := by
    have h := lemma65ProjectionFactorUnitIntrinsic_parameterCases
      b x hx hfactorNe
    simpa only [p, εp, hpOrder'] using h
  simp only [BeliLemma317ParameterCases] at hcases
  rcases hcases with hhigh | hboundary | hinterior | hendpoint
  · omega
  · have hfinite : quadraticDefect K (-εp) ≠ ⊤ := hboundary.1
    have hzero : (quadraticDefect K (-εp)).toNat = 0 := by
      omega
    have hpositive : 1 ≤ (quadraticDefect K (-εp)).toNat := by
      rw [← ENat.coe_toNat hfinite] at hdefectOne
      exact_mod_cast hdefectOne
    omega
  · omega
  · exact hresidue hendpoint.2

/-- A norm-generating intrinsic projection has a nonzero factor. -/
theorem lemma65ProjectionFactor_ne_zero_of_originalTail_isNormGenerator
    (b : BONG V q L (n + 3)) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic)
      (b.lemma65Projection x)) :
    1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0 := by
  intro hzero
  have hprojectionEq :=
    quadratic_lemma65Projection_eq_one_sub_sq_mul_intrinsic b x heq
  rw [hzero, zero_mul] at hprojectionEq
  exact b.tail.isAnisotropic_of_isNormGenerator_binary hgenerator
    hprojectionEq

/-- The intrinsic projection factor is the adjacent parameter times the
norm-generator value ratio in the original projected tail. -/
theorem lemma65ProjectionFactorUnitIntrinsic_eq_adjacentParameter_mul_tailRatio
    (b : BONG V q L (n + 3)) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic)
      (b.lemma65Projection x)) :
    lemma65ProjectionFactorUnitIntrinsic b x
        (lemma65ProjectionFactor_ne_zero_of_originalTail_isNormGenerator
          b x heq hgenerator) =
      b.adjacentParameter 0 (by simp) *
        b.tail.normGeneratorValueRatioUnit
          (b.lemma65Projection x) hgenerator := by
  apply Units.ext
  have hprojectionEq :=
    quadratic_lemma65Projection_eq_one_sub_sq_mul_intrinsic b x heq
  simp only [coe_lemma65ProjectionFactorUnitIntrinsic, Units.val_mul,
    adjacentParameter, Units.val_div_eq_div_val,
    normGeneratorValueRatioUnit, Units.val_mk0, coe_valueUnit]
  have hnext :
      (⟨(0 : Fin (n + 3)).1 + 1, by simp⟩ : Fin (n + 3)) = 1 :=
    Fin.ext rfl
  rw [hnext]
  rw [← b.value_zero_eq_quadratic_head]
  rw [b.value_tail (0 : Fin (n + 2))]
  have hindex : (0 : Fin (n + 2)).succ = (1 : Fin (n + 3)) :=
    Fin.ext rfl
  rw [hindex]
  rw [← b.value_zero_eq_quadratic_head] at hprojectionEq
  rw [hprojectionEq]
  field_simp [b.value_ne_zero 0, b.value_ne_zero 1]

/-- Hence the intrinsic projection factor has the original adjacent order. -/
theorem ordUnit_lemma65ProjectionFactorUnitIntrinsic_of_originalTail_isNormGenerator
    (b : BONG V q L (n + 3)) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic)
      (b.lemma65Projection x)) :
    ordUnit K (lemma65ProjectionFactorUnitIntrinsic b x
      (lemma65ProjectionFactor_ne_zero_of_originalTail_isNormGenerator
        b x heq hgenerator)) = b.lemma62Gap := by
  rw [lemma65ProjectionFactorUnitIntrinsic_eq_adjacentParameter_mul_tailRatio
    b x heq hgenerator, ordUnit_mul, b.ordUnit_adjacentParameter_zero]
  have hratio := b.tail.normGeneratorValueRatioUnit_isValuationUnit
    (b.lemma65Projection x) hgenerator
  rw [(isValuationUnit_iff_ordUnit_eq_zero K _).1 hratio]
  omega

/-- In the short-shift, nonboundary branch with `k=1`, the unshifted
half-gap has the wrong parity for Lemma 3.17(iii).  This is the parity
calculation in case (4) of the paper. -/
theorem originalHalfGap_odd_of_low_nonboundary_k_eq_one
    (S : b.Lemma65Setup) (hlow : b.Lemma65LowRange S)
    (hk : S.k = 1)
    (hnotBoundary : ¬(
      (quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int))) :
    Odd (b.lemma62Gap / 2 + (ramificationIndex K : Int)) := by
  let R : Int := b.lemma62Gap + 2 * (S.k : Int)
  let epsilon : Kˣ :=
    normalizedUnitPart K (b.adjacentParameter 0 (by simp))
  let d := quadraticDefect K (-epsilon)
  have hRle : R ≤ 2 * (ramificationIndex K : Int) := by
    change b.order 1 + 2 * (S.k : Int) - b.order 0 ≤
      2 * (ramificationIndex K : Int) at hlow
    dsimp only [R]
    unfold lemma62Gap
    omega
  have hbaseLower : -(2 * (ramificationIndex K : Int)) ≤
      b.lemma62Gap := by
    have h :=
      (b.adjacentParameter_isBinaryParameterAdmissible 0 (by simp)).ordUnit_ge_neg_two_mul_e
    rwa [b.ordUnit_adjacentParameter_zero] at h
  have hcases : BeliLemma317ParameterCases (K := K) R epsilon := by
    simpa only [R, epsilon] using S.finalParameterCases
  simp only [BeliLemma317ParameterCases] at hcases
  rcases hcases with hhigh | hboundary | hinterior | hendpoint
  · omega
  · exact (hnotBoundary (by simpa only [R, epsilon, d] using hboundary)).elim
  · have hEvenFinal := hinterior.2.2.2.1
    have hbaseEven : Even b.lemma62Gap := by
      rcases hinterior.2.2.1 with ⟨r, hr⟩
      refine ⟨r - 1, ?_⟩
      dsimp only [R] at hr
      rw [hk] at hr
      norm_num at hr
      omega
    rcases hEvenFinal with ⟨m, hm⟩
    rcases hbaseEven with ⟨r, hr⟩
    refine ⟨m - 1, ?_⟩
    dsimp only [R] at hm
    rw [hk] at hm
    norm_num at hm
    omega
  · rcases hendpoint.1 with hREq | hquarter
    · refine ⟨ramificationIndex K - 1, ?_⟩
      dsimp only [R] at hREq
      rw [hk] at hREq
      norm_num at hREq
      have hdiv :
          (b.lemma62Gap / 2 : Int) = ramificationIndex K - 1 := by
        omega
      rw [hdiv]
      omega
    · have hepsilon : IsValuationUnit K (epsilon : K) :=
        normalizedUnitPart_isValuationUnit K _
      have hord := ordUnit_eq_of_unitSquareClass_eq (K := K) hquarter
      rw [ordUnit_uniformizerPower_mul_valuationUnit epsilon hepsilon R,
        ordUnit_negativeQuarterUnit] at hord
      dsimp only [R] at hord
      rw [hk] at hord
      norm_num at hord
      omega

/-- The same branch forces the original normalized parameter defect to be
strictly above its cutoff.  Equality would make the unshifted parameter a
Lemma 3.17(ii) parameter, contradicting the minimality of `k=1`. -/
theorem originalDefect_ge_cutoff_succ_of_low_nonboundary_k_eq_one
    (S : b.Lemma65Setup) (hlow : b.Lemma65LowRange S)
    (hk : S.k = 1)
    (hnotBoundary : ¬(
      (quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int))) :
    ((b.lemma62DefectCutoff + 1 : Nat) : ℕ∞) ≤
      quadraticDefect K
        (-(normalizedUnitPart K
          (b.adjacentParameter 0 (by simp)))) := by
  let R : Int := b.lemma62Gap + 2 * (S.k : Int)
  let epsilon : Kˣ :=
    normalizedUnitPart K (b.adjacentParameter 0 (by simp))
  let d := quadraticDefect K (-epsilon)
  change ((b.lemma62DefectCutoff + 1 : Nat) : ℕ∞) ≤ d
  have hfinalUpper : R ≤ 2 * (ramificationIndex K : Int) := by
    change b.order 1 + 2 * (S.k : Int) - b.order 0 ≤
      2 * (ramificationIndex K : Int) at hlow
    dsimp only [R]
    unfold lemma62Gap
    omega
  have hbaseUpper : b.lemma62Gap ≤
      2 * (ramificationIndex K : Int) := by
    dsimp only [R] at hfinalUpper
    rw [hk] at hfinalUpper
    norm_num at hfinalUpper
    omega
  have hbaseEven : Even b.lemma62Gap := by
    have hfinalEven := S.lowRange_gap_even hlow
    rcases hfinalEven with ⟨m, hm⟩
    refine ⟨m - 1, ?_⟩
    rw [hk] at hm
    norm_num at hm
    rw [← b.order_eq_ordUnit 1, ← b.order_eq_ordUnit 0] at hm
    unfold lemma62Gap
    omega
  have hcutCast : (b.lemma62DefectCutoff : Int) =
      (ramificationIndex K : Int) - b.lemma62Gap / 2 :=
    b.lemma62DefectCutoff_cast hbaseEven hbaseUpper
  have hbaseLower : -(2 * (ramificationIndex K : Int)) ≤
      b.lemma62Gap := by
    have h :=
      (b.adjacentParameter_isBinaryParameterAdmissible 0 (by simp)).ordUnit_ge_neg_two_mul_e
    rwa [b.ordUnit_adjacentParameter_zero] at h
  have hnotOriginal : ¬b.HeadSecondRescaleAdmissible 0 := by
    apply S.not_admissible_of_lt
    omega
  have hboundaryNotBase : d ≠ ⊤ →
      b.lemma62Gap ≠
        2 * (ramificationIndex K : Int) - 2 * (d.toNat : Int) := by
    intro hfinite heq
    apply hnotOriginal
    apply b.headSecondRescaleAdmissible_of_parameterCases 0
    simp only [BeliLemma317ParameterCases]
    exact Or.inr (Or.inl ⟨by simpa only [d, epsilon] using hfinite, by
      norm_num
      simpa only [d, epsilon] using heq⟩)
  have hcases : BeliLemma317ParameterCases (K := K) R epsilon := by
    simpa only [R, epsilon] using S.finalParameterCases
  simp only [BeliLemma317ParameterCases] at hcases
  rcases hcases with hhigh | hboundary | hinterior | hendpoint
  · exact (by omega)
  · exact (hnotBoundary (by simpa only [R, epsilon, d] using hboundary)).elim
  · rcases hinterior.1 with htop | ⟨hfinite, hboundaryLtFinal⟩
    · change d = ⊤ at htop
      simp [htop]
    · change d ≠ ⊤ at hfinite
      change 2 * (ramificationIndex K : Int) - 2 * (d.toNat : Int) < R
        at hboundaryLtFinal
      have hboundaryLeBase :
          2 * (ramificationIndex K : Int) - 2 * (d.toNat : Int) ≤
            b.lemma62Gap := by
        dsimp only [R] at hboundaryLtFinal
        rw [hk] at hboundaryLtFinal
        norm_num at hboundaryLtFinal
        have hboundaryEven : Even
            (2 * (ramificationIndex K : Int) - 2 * (d.toNat : Int)) := by
          exact ⟨(ramificationIndex K : Int) - (d.toNat : Int), by ring⟩
        rcases hboundaryEven with ⟨r, hr⟩
        rcases hbaseEven with ⟨s, hs⟩
        omega
      have hboundaryLtBase :
          2 * (ramificationIndex K : Int) - 2 * (d.toNat : Int) <
            b.lemma62Gap :=
        lt_of_le_of_ne hboundaryLeBase
          (Ne.symm (hboundaryNotBase hfinite))
      have hnat : b.lemma62DefectCutoff + 1 ≤ d.toNat := by
        have hcut := hcutCast
        rcases hbaseEven with ⟨s, hs⟩
        omega
      rw [← ENat.coe_toNat hfinite]
      exact_mod_cast hnat
  · rcases hendpoint.1 with hREq | hquarter
    · by_cases htop : d = ⊤
      · simp [htop]
      · have hepsilon : IsValuationUnit K ((-epsilon : Kˣ) : K) := by
          change ord K (-((epsilon : Kˣ) : K)) = 0
          rw [ord_neg]
          exact normalizedUnitPart_isValuationUnit K
            (b.adjacentParameter 0 (by simp))
        have hone : (1 : ℕ∞) ≤ d := by
          simpa only [d] using
            one_le_quadraticDefect_of_unit (-epsilon) hepsilon
        have honeNat : 1 ≤ d.toNat := by
          rw [← ENat.coe_toNat htop] at hone
          exact_mod_cast hone
        have hdNotOne : d.toNat ≠ 1 := by
          intro hdOne
          apply hboundaryNotBase htop
          dsimp only [R] at hREq
          rw [hk] at hREq
          norm_num at hREq
          omega
        have hnat : b.lemma62DefectCutoff + 1 ≤ d.toNat := by
          have hcut := hcutCast
          dsimp only [R] at hREq
          rw [hk] at hREq
          norm_num at hREq
          omega
        rw [← ENat.coe_toNat htop]
        exact_mod_cast hnat
    · have hepsilon : IsValuationUnit K (epsilon : K) :=
        normalizedUnitPart_isValuationUnit K _
      have hord := ordUnit_eq_of_unitSquareClass_eq (K := K) hquarter
      rw [ordUnit_uniformizerPower_mul_valuationUnit epsilon hepsilon R,
        ordUnit_negativeQuarterUnit] at hord
      dsimp only [R] at hord
      rw [hk] at hord
      norm_num at hord
      omega

/-- In Beli's case (4), the projection cannot already be a norm generator of
the unshifted projected tail.  The two factors in its value ratio both have
defect strictly deeper than the first-pair cutoff, whereas every possible
Lemma 3.17 presentation of the projection parameter is excluded by the
minimality and parity of the short shift. -/
theorem projection_not_originalTailGenerator_of_low_nonboundary_k_eq_one
    (S : b.Lemma65Setup) (hB : b.HasPropertyB) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hlow : b.Lemma65LowRange S) (hk : S.k = 1)
    (hnotBoundary : ¬(
      (quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int))) :
    ¬Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic)
      (S.projection x) := by
  intro hgenerator
  let a₀ : Kˣ := b.adjacentParameter 0 (by simp)
  let ratio : Kˣ :=
    b.tail.normGeneratorValueRatioUnit (S.projection x) hgenerator
  have hfactorNe :=
    S.projectionFactor_ne_zero_of_originalTail_isNormGenerator
      x heq hgenerator
  let p : Kˣ := S.projectionFactorUnit x hfactorNe
  let ε₀ : Kˣ := normalizedUnitPart K a₀
  let εp : Kˣ := normalizedUnitPart K p
  have hpEq : p = a₀ * ratio := by
    simpa only [p, a₀, ratio] using
      S.projectionFactorUnit_eq_adjacentParameter_mul_tailRatio
        x heq hgenerator
  have hpOrder : ordUnit K p = b.lemma62Gap := by
    simpa only [p] using
      S.ordUnit_projectionFactorUnit_of_originalTail_isNormGenerator
        x heq hgenerator
  have hfinalUpper : b.lemma62Gap + 2 * (S.k : Int) ≤
      2 * (ramificationIndex K : Int) := by
    change b.order 1 + 2 * (S.k : Int) - b.order 0 ≤
      2 * (ramificationIndex K : Int) at hlow
    unfold lemma62Gap
    omega
  have hbaseStrict : b.lemma62Gap <
      2 * (ramificationIndex K : Int) := by
    rw [hk] at hfinalUpper
    norm_num at hfinalUpper
    omega
  have hbaseUpper : b.lemma62Gap ≤
      2 * (ramificationIndex K : Int) := hbaseStrict.le
  have hbaseNe : b.lemma62Gap ≠
      2 * (ramificationIndex K : Int) := ne_of_lt hbaseStrict
  have hbaseEven : Even b.lemma62Gap := by
    have hfinalEven := S.lowRange_gap_even hlow
    rcases hfinalEven with ⟨m, hm⟩
    refine ⟨m - 1, ?_⟩
    rw [hk] at hm
    norm_num at hm
    rw [← b.order_eq_ordUnit 1, ← b.order_eq_ordUnit 0] at hm
    unfold lemma62Gap
    omega
  have hhalfOdd :
      Odd (b.lemma62Gap / 2 + (ramificationIndex K : Int)) :=
    S.originalHalfGap_odd_of_low_nonboundary_k_eq_one
      hlow hk hnotBoundary
  have horiginalDefect :=
    S.originalDefect_ge_cutoff_succ_of_low_nonboundary_k_eq_one
      hlow hk hnotBoundary
  have hratioDefect :
      ((b.lemma62DefectCutoff + 1 : Nat) : ℕ∞) ≤
        quadraticDefect K ratio := by
    simpa only [ratio] using
      S.tailNormGeneratorRatio_defect_ge_cutoff_succ
        hB hbaseEven hbaseUpper hbaseNe (S.projection x) hgenerator
  have hε₀Unit : IsValuationUnit K (ε₀ : K) := by
    simpa only [ε₀, a₀] using
      normalizedUnitPart_isValuationUnit K a₀
  have ha₀Factor : uniformizerPowerUnit K b.lemma62Gap * ε₀ = a₀ := by
    simpa only [a₀, ε₀, b.ordUnit_adjacentParameter_zero] using
      uniformizerPower_mul_normalizedUnitPart K a₀
  have ha₀DefectEq :
      quadraticDefect K (-a₀) = quadraticDefect K (-ε₀) := by
    have h :=
      beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
        (K := K) b.lemma62Gap ε₀ hε₀Unit hbaseEven
    rw [ha₀Factor] at h
    exact h
  have ha₀Defect :
      ((b.lemma62DefectCutoff + 1 : Nat) : ℕ∞) ≤
        quadraticDefect K (-a₀) := by
    rw [ha₀DefectEq]
    simpa only [ε₀, a₀] using horiginalDefect
  have hproductDefect :
      ((b.lemma62DefectCutoff + 1 : Nat) : ℕ∞) ≤
        quadraticDefect K ((-a₀) * ratio) := by
    exact le_trans (le_min ha₀Defect hratioDefect)
      (quadraticDefect_mul_ge_min K (-a₀) ratio)
  have hpNeg : -p = (-a₀) * ratio := by
    rw [hpEq]
    simp
  have hpDefect :
      ((b.lemma62DefectCutoff + 1 : Nat) : ℕ∞) ≤
        quadraticDefect K (-p) := by
    rw [hpNeg]
    exact hproductDefect
  have hεpUnit : IsValuationUnit K (εp : K) := by
    simpa only [εp] using normalizedUnitPart_isValuationUnit K p
  have hpFactor : uniformizerPowerUnit K b.lemma62Gap * εp = p := by
    rw [← hpOrder]
    simpa only [εp] using uniformizerPower_mul_normalizedUnitPart K p
  have hpDefectEq :
      quadraticDefect K (-p) = quadraticDefect K (-εp) := by
    have h :=
      beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
        (K := K) b.lemma62Gap εp hεpUnit hbaseEven
    rw [hpFactor] at h
    exact h
  have hεpDefect :
      ((b.lemma62DefectCutoff + 1 : Nat) : ℕ∞) ≤
        quadraticDefect K (-εp) := by
    rw [← hpDefectEq]
    exact hpDefect
  have hcases : BeliLemma317ParameterCases (K := K)
      b.lemma62Gap εp := by
    have h := S.projectionFactorUnit_parameterCases x hx hfactorNe
    simpa only [p, εp, hpOrder] using h
  have hcutCast : (b.lemma62DefectCutoff : Int) =
      (ramificationIndex K : Int) - b.lemma62Gap / 2 :=
    b.lemma62DefectCutoff_cast hbaseEven hbaseUpper
  simp only [BeliLemma317ParameterCases] at hcases
  rcases hcases with hhigh | hboundary | hinterior | hendpoint
  · omega
  · let dp := quadraticDefect K (-εp)
    have hfinite : dp ≠ ⊤ := by
      simpa only [dp] using hboundary.1
    have hboundNat : b.lemma62DefectCutoff + 1 ≤ dp.toNat := by
      change ((b.lemma62DefectCutoff + 1 : Nat) : ℕ∞) ≤ dp at hεpDefect
      rw [← ENat.coe_toNat hfinite] at hεpDefect
      exact_mod_cast hεpDefect
    have hboundaryEq : b.lemma62Gap =
        2 * (ramificationIndex K : Int) - 2 * (dp.toNat : Int) := by
      simpa only [dp] using hboundary.2
    have hdpEq : (dp.toNat : Int) =
        (b.lemma62DefectCutoff : Int) := by
      rcases hbaseEven with ⟨r, hr⟩
      omega
    omega
  · exact (Int.not_even_iff_odd.mpr hhalfOdd hinterior.2.2.2.1).elim
  · rcases hendpoint.1 with hbaseEq | hquarter
    · omega
    · have hord := ordUnit_eq_of_unitSquareClass_eq (K := K) hquarter
      rw [ordUnit_uniformizerPower_mul_valuationUnit εp hεpUnit
          b.lemma62Gap,
        ordUnit_negativeQuarterUnit] at hord
      have hhalfEven :
          Even (b.lemma62Gap / 2 + (ramificationIndex K : Int)) := by
        refine ⟨0, ?_⟩
        omega
      exact (Int.not_even_iff_odd.mpr hhalfOdd hhalfEven).elim

/-- Thus, in case (4), every relevant projection belongs to the shifted tail
lattice.  For `k=1` the carrier threshold is exactly one order above the
original tail norm, which is equivalent to not being a norm generator. -/
theorem projection_mem_tailRescale_of_low_nonboundary_k_eq_one
    (S : b.Lemma65Setup) (hB : b.HasPropertyB) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hlow : b.Lemma65LowRange S) (hk : S.k = 1)
    (hnotBoundary : ¬(
      (quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int))) :
    S.projection x ∈ S.tailRescale.lattice := by
  have htailMem : S.projection x ∈
      L.projectedLattice q b.head b.head_isAnisotropic :=
    S.projection_mem_tail x hx
  have hnotGenerator :=
    S.projection_not_originalTailGenerator_of_low_nonboundary_k_eq_one
      hB x hx heq hlow hk hnotBoundary
  have hdeep :=
    (b.tail.mem_and_not_isNormGenerator_iff_ord_ge_head_add_one
      (S.projection x)).1 ⟨htailMem, hnotGenerator⟩
  rw [S.tailRescale.mem_lattice_iff_ord_ge_head_depth]
  refine ⟨htailMem, ?_⟩
  convert hdeep.2 using 1
  norm_cast
  rw [hk]
  norm_num
  omega

/-- The whole nonboundary low branch is now closed: minimality gives
`k ≤ 1`, and the two possible depths are handled by the depth-zero carrier
identity and the case-(4) defect argument, respectively. -/
theorem projection_mem_tailRescale_of_low_nonboundary
    (S : b.Lemma65Setup) (hB : b.HasPropertyB) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hlow : b.Lemma65LowRange S)
    (hnotBoundary : ¬(
      (quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int))) :
    S.projection x ∈ S.tailRescale.lattice := by
  have hkLe : S.k ≤ 1 :=
    (S.lowRange_boundary_or_k_le_one hlow).resolve_left hnotBoundary
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hkLe with hk | hk
  · exact S.projection_mem_tailRescale_of_k_eq_zero x hx hk
  · exact S.projection_mem_tailRescale_of_low_nonboundary_k_eq_one
      hB x hx heq hlow hk hnotBoundary

/-- In the finite-defect boundary branch (case (3) in the paper), the
Lemma 6.2 square-residue description makes every hypothetical projection
below the rescaling threshold retain the original parameter defect.  Such a
lower-order parameter lies strictly below its Lemma 3.17 boundary, a
contradiction. -/
theorem projection_mem_tailRescale_of_low_boundary
    (S : b.Lemma65Setup) (hB : b.HasPropertyB) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hlow : b.Lemma65LowRange S)
    (hboundary :
      (quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int)) :
    S.projection x ∈ S.tailRescale.lattice := by
  by_contra hnotMem
  let y := S.projection x
  have hyMem : y ∈
      L.projectedLattice q b.head b.head_isAnisotropic := by
    simpa only [y] using S.projection_mem_tail x hx
  have hyNe :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic y ≠ 0 := by
    intro hyZero
    apply hnotMem
    rw [S.tailRescale.mem_lattice_iff_ord_ge_head_depth]
    refine ⟨hyMem, ?_⟩
    rw [hyZero, ord_zero]
    exact le_top
  have hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0 := by
    intro hzero
    have hprojection := S.quadratic_projection_eq_one_sub_sq_mul x heq
    rw [hzero, zero_mul] at hprojection
    exact hyNe (by simpa only [y] using hprojection)
  let p : Kˣ := S.projectionFactorUnit x hfactorNe
  let a₀ : Kˣ := b.adjacentParameter 0 (by simp)
  let ε₀ : Kˣ := normalizedUnitPart K a₀
  let d := quadraticDefect K (-ε₀)
  have hdFinite : d ≠ ⊤ := by
    simpa only [d, ε₀, a₀] using hboundary.1
  have hfinalEq : b.lemma62Gap + 2 * (S.k : Int) =
      2 * (ramificationIndex K : Int) - 2 * (d.toNat : Int) := by
    simpa only [d, ε₀, a₀] using hboundary.2
  have hordY :=
    S.ord_quadratic_projection_eq_head_add_projectionFactor
      x heq hfactorNe
  change ord K ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic y) =
      ((b.order 0 + ordUnit K p : Int) : WithTop Int) at hordY
  have hthresholdNot : ¬
      (((b.tail.order 0 + 2 * (S.k : Int) - 1 : Int) : WithTop Int) ≤
        ord K ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic y)) := by
    intro hthreshold
    apply hnotMem
    exact (S.tailRescale.mem_lattice_iff_ord_ge_head_depth y).2
      ⟨hyMem, hthreshold⟩
  have hyLtThreshold := lt_of_not_ge hthresholdNot
  have htailOrderZero : b.tail.order 0 = b.order 1 := by
    rw [b.order_tail]
    congr 1
  have htailOrderOne : b.tail.order 1 = b.order 2 := by
    rw [b.order_tail]
    congr 1
  have htailValueZero : b.tail.value 0 = b.value 1 := by
    rw [b.value_tail]
    congr 1
  have hpLt : ordUnit K p <
      b.lemma62Gap + 2 * (S.k : Int) - 1 := by
    rw [hordY] at hyLtThreshold
    norm_cast at hyLtThreshold
    rw [htailOrderZero] at hyLtThreshold
    unfold lemma62Gap
    omega
  have hpLower : b.lemma62Gap ≤ ordUnit K p := by
    have hlower := S.tail_order_zero_le_ord_quadratic_projection x hx
    change (b.tail.order 0 : WithTop Int) ≤
      ord K ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic y)
      at hlower
    rw [hordY] at hlower
    norm_cast at hlower
    rw [htailOrderZero] at hlower
    unfold lemma62Gap
    omega
  have hfinalEven : Even (b.lemma62Gap + 2 * (S.k : Int)) := by
    refine ⟨(ramificationIndex K : Int) - (d.toNat : Int), ?_⟩
    omega
  have hbaseEven : Even b.lemma62Gap := by
    rcases hfinalEven with ⟨r, hr⟩
    refine ⟨r - (S.k : Int), ?_⟩
    omega
  have hbaseUpper : b.lemma62Gap ≤
      2 * (ramificationIndex K : Int) := by
    have hkNonneg : (0 : Int) ≤ (S.k : Int) := by positivity
    omega
  have hpUpper : ordUnit K p ≤
      2 * (ramificationIndex K : Int) := by
    omega
  have hpEven : Even (ordUnit K p) := by
    exact even_ordUnit_of_hasSomeEqualNormGeneratorBasis_of_le_two_e
      p
      (by simpa only [p] using
        S.projectionFactorUnit_isBinaryParameterAdmissible x hx hfactorNe)
      (by simpa only [p] using
        S.projectionFactorUnit_hasSomeEqualNormGeneratorBasis x hx hfactorNe)
      hpUpper
  have ha₀DefectEq : quadraticDefect K (-a₀) = d := by
    simpa only [d, ε₀] using
      beliParameterDefect_eq_normalizedUnitPart_of_even
        (K := K) a₀ (by
          simpa only [a₀, b.ordUnit_adjacentParameter_zero] using hbaseEven)
  have ha₀ParameterDefect : beliParameterDefect K a₀ = d := by
    simpa only [beliParameterDefect] using ha₀DefectEq
  have ha₀ParameterFinite : beliParameterDefect K a₀ ≠ ⊤ := by
    rw [ha₀ParameterDefect]
    exact hdFinite
  have hbaseDefectNonneg :
      0 ≤ b.lemma62Gap + (d.toNat : Int) := by
    have hadmissible :=
      b.adjacentParameter_isBinaryParameterAdmissible 0 (by simp)
    have h := hadmissible.order_add_parameterDefect_nonneg (by
      simpa only [a₀] using ha₀ParameterFinite)
    rw [b.ordUnit_adjacentParameter_zero] at h
    simpa only [a₀, ha₀ParameterDefect] using h
  have hε₀Unit : IsValuationUnit K (ε₀ : K) := by
    simpa only [ε₀, a₀] using normalizedUnitPart_isValuationUnit K a₀
  have hdLeNat : d.toNat ≤ 2 * ramificationIndex K := by
    have hnotSquare : ¬IsSquare (-ε₀) := by
      intro hsquare
      exact hdFinite
        ((quadraticDefect_eq_top_iff_isSquare (K := K) (-ε₀)).2 hsquare)
    have hbound :=
      quadraticDefect_le_two_mul_e_of_not_isSquare (K := K) hnotSquare
    change d ≤ _ at hbound
    rw [← ENat.coe_toNat hdFinite] at hbound
    exact_mod_cast hbound
  have hcutCast : (b.lemma62DefectCutoff : Int) =
      (ramificationIndex K : Int) - b.lemma62Gap / 2 :=
    b.lemma62DefectCutoff_cast hbaseEven hbaseUpper
  have hdLeCutNat : d.toNat ≤ b.lemma62DefectCutoff := by
    rcases hbaseEven with ⟨r, hr⟩
    omega
  have hdefectLow :
      beliParameterDefect K (b.adjacentParameter 0 (by simp)) ≤
        (b.lemma62DefectCutoff : ℕ∞) := by
    change beliParameterDefect K a₀ ≤ _
    rw [ha₀ParameterDefect, ← ENat.coe_toNat hdFinite]
    exact_mod_cast hdLeCutNat
  have hthirdGap :
      2 * (ramificationIndex K : Int) + 1 ≤
        b.order 2 - b.order 1 :=
    b.thirdGap_ge_of_propertyB_lemma62_low
      hB hbaseEven hbaseUpper hdefectLow
  have htailOrder : b.tail.order 0 ≤ b.tail.order 1 := by
    rw [htailOrderZero, htailOrderOne]
    omega
  let wt := b.tail.headInverseRescaleWitness
  have htailB : b.tail.HasPropertyB := hB.tail_for_lemma62
  have hvalues := b.tail.beliLemma62_ii_a wt (Or.inl htailB) htailOrder
  have hyValue :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic y ∈
        Lattice.quadraticValueSet
          (q.orthogonalSpace b.head b.head_isAnisotropic)
          (L.projectedLattice q b.head b.head_isAnisotropic) := by
    rw [Lattice.mem_quadraticValueSet_iff]
    exact ⟨y, hyMem, rfl⟩
  have hyResidue := hvalues hyValue
  rcases hyResidue with ⟨c, hcError⟩
  let qy : K :=
    (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic y
  let main : K := b.value 1 * (c : K) ^ 2
  have herrorOrder : (b.order 2 : WithTop Int) ≤ ord K (qy - main) := by
    have h := (Lattice.mem_powerIdeal_iff (K := K)
      (b.tail.order 1)
      ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic y -
        b.tail.value 0 * (c : K) ^ 2)).1 hcError
    simpa only [qy, main, htailValueZero, htailOrderOne] using h
  have horderOne : b.order 1 = b.order 0 + b.lemma62Gap := by
    unfold lemma62Gap
    omega
  have hqIntLtThird : b.order 0 + ordUnit K p < b.order 2 := by
    omega
  have hqLtError : ord K qy < ord K (qy - main) := by
    have hqLtThird : ord K qy < (b.order 2 : WithTop Int) := by
      change ord K
          ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic y) < _
      rw [hordY]
      exact_mod_cast hqIntLtThird
    exact hqLtThird.trans_le herrorOrder
  have hmainOrder : ord K main = ord K qy := by
    have hidentity : main = qy - (qy - main) := by ring
    rw [hidentity]
    exact (ord K).map_sub_eq_of_lt_left hqLtError
  have hmainNe : main ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero] at hmainOrder
    have hqyFinite : ord K qy ≠ ⊤ := by
      rw [show ord K qy =
          ((b.order 0 + ordUnit K p : Int) : WithTop Int) by
        simpa only [qy] using hordY]
      exact WithTop.coe_ne_top
    exact hqyFinite hmainOrder.symm
  have hcNe : (c : K) ≠ 0 := by
    intro hzero
    apply hmainNe
    simp [main, hzero]
  let qyUnit : Kˣ := Units.mk0 qy hyNe
  let mainUnit : Kˣ := Units.mk0 main hmainNe
  let cUnit : Kˣ := Units.mk0 (c : K) hcNe
  have hunitOrders : ordUnit K qyUnit = ordUnit K mainUnit := by
    apply WithTop.coe_injective
    simpa only [qyUnit, mainUnit, coe_ordUnit, Units.val_mk0] using
      hmainOrder.symm
  have hrelativeInt :
      b.order 0 + ordUnit K p + (d.toNat : Int) + 1 ≤ b.order 2 := by
    omega
  have hqyUnitOrder : ordUnit K qyUnit = b.order 0 + ordUnit K p := by
    apply WithTop.coe_injective
    simpa only [qyUnit, coe_ordUnit, Units.val_mk0, qy] using hordY
  have hrelativeError :
      ((ordUnit K qyUnit + ((d.toNat + 1 : Nat) : Int) : Int) :
          WithTop Int) ≤
        ord K ((qyUnit : K) - (mainUnit : K)) := by
    simp only [qyUnit, mainUnit, Units.val_mk0]
    rw [hqyUnitOrder]
    have hthreshold :
        ((b.order 0 + ordUnit K p + (d.toNat : Int) + 1 : Int) :
            WithTop Int) ≤ (b.order 2 : WithTop Int) := by
      exact_mod_cast hrelativeInt
    have hnatCast : ((d.toNat + 1 : Nat) : Int) =
        (d.toNat : Int) + 1 := by
      omega
    rw [hnatCast]
    simpa only [add_assoc] using hthreshold.trans herrorOrder
  let near : Kˣ := qyUnit * mainUnit⁻¹
  have hnearDefect : ((d.toNat + 1 : Nat) : ℕ∞) ≤
      quadraticDefect K near := by
    simpa only [near] using
      quadraticDefect_div_ge_of_sub_order
        (K := K) qyUnit mainUnit (d.toNat + 1)
          hunitOrders hrelativeError
  have hdLtNear : d < quadraticDefect K near := by
    rw [← ENat.coe_toNat hdFinite]
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self d.toNat)
      hnearDefect
  have hpValue : (p : K) = qy / q.quadratic b.head := by
    have hprojection := S.quadratic_projection_eq_one_sub_sq_mul x heq
    change qy = (p : K) * q.quadratic b.head at hprojection
    exact (eq_div_iff b.head_isAnisotropic).2 hprojection.symm
  have ha₀Value : (a₀ : K) = b.value 1 / q.quadratic b.head := by
    simp only [a₀, adjacentParameter, Units.val_div_eq_div_val,
      coe_valueUnit]
    have hnext :
        (⟨(0 : Fin (n + 3)).1 + 1, by simp⟩ : Fin (n + 3)) = 1 := by
      apply Fin.ext
      rfl
    rw [hnext]
    rw [b.value_zero_eq_quadratic_head]
  have hpDecomposition :
      -p = ((-a₀) * near) * cUnit ^ 2 := by
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val,
      near, qyUnit, mainUnit, cUnit, Units.val_mk0,
      Units.val_inv_eq_inv_val, hpValue, ha₀Value, main]
    field_simp [b.head_isAnisotropic, b.value_ne_zero 1, hcNe, hmainNe]
    <;> ring
  have hproductDefect :
      quadraticDefect K ((-a₀) * near) = quadraticDefect K (-a₀) :=
    quadraticDefect_mul_eq_left_of_lt_right (K := K) (by
      simpa only [ha₀DefectEq] using hdLtNear)
  have hpDefectEq : quadraticDefect K (-p) = d := by
    rw [hpDecomposition, quadraticDefect_mul_square, hproductDefect,
      ha₀DefectEq]
  let εp : Kˣ := normalizedUnitPart K p
  have hεpDefectEq : quadraticDefect K (-εp) = d := by
    have hnormalize :=
      beliParameterDefect_eq_normalizedUnitPart_of_even (K := K) p hpEven
    simpa only [εp] using hnormalize.symm.trans hpDefectEq
  have hcases : BeliLemma317ParameterCases (K := K)
      (ordUnit K p) εp := by
    simpa only [p, εp] using
      S.projectionFactorUnit_parameterCases x hx hfactorNe
  have hboundaryAbove :
      ordUnit K p <
        2 * (ramificationIndex K : Int) - 2 * (d.toNat : Int) := by
    omega
  simp only [BeliLemma317ParameterCases] at hcases
  rcases hcases with hhigh | hpBoundary | hpInterior | hpEndpoint
  · omega
  · have hpEq : ordUnit K p =
        2 * (ramificationIndex K : Int) - 2 * (d.toNat : Int) := by
      simpa only [hεpDefectEq] using hpBoundary.2
    omega
  · have hpAbove :
        2 * (ramificationIndex K : Int) - 2 * (d.toNat : Int) <
          ordUnit K p := by
      rcases hpInterior.1 with htop | hfiniteAbove
      · exact (hdFinite (by simpa only [hεpDefectEq] using htop)).elim
      · simpa only [hεpDefectEq] using hfiniteAbove.2
    omega
  · rcases hpEndpoint.1 with hpTwoE | hpQuarter
    · omega
    · have hεpUnit : IsValuationUnit K (εp : K) := by
        simpa only [εp] using normalizedUnitPart_isValuationUnit K p
      have hpNegTwoE := ordUnit_eq_of_unitSquareClass_eq (K := K) hpQuarter
      rw [ordUnit_uniformizerPower_mul_valuationUnit εp hεpUnit
          (ordUnit K p),
        ordUnit_negativeQuarterUnit] at hpNegTwoE
      have hdLeInt : (d.toNat : Int) ≤
          2 * (ramificationIndex K : Int) := by
        exact_mod_cast hdLeNat
      omega

/-- All low-range branches of Lemma 6.5(i) place the projection in the
least rescaled tail.  This combines the finite-defect boundary with the two
short-shift alternatives left by Lemma 3.17. -/
theorem projection_mem_tailRescale_of_low
    (S : b.Lemma65Setup) (hB : b.HasPropertyB) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hlow : b.Lemma65LowRange S) :
    S.projection x ∈ S.tailRescale.lattice := by
  by_cases hboundary :
      (quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int)
  · exact S.projection_mem_tailRescale_of_low_boundary
      hB x hx heq hlow hboundary
  · exact S.projection_mem_tailRescale_of_low_nonboundary
      hB x hx heq hlow hboundary

/-- Beli's case (2): when the original first gap is odd and the least
admissible shifted gap is `2e+1`, Property B pushes the third value beyond
the projection threshold.  Lemma 6.2 then forces every hypothetical shallow
projection factor to have the same odd parity as the original gap, contrary
to Lemma 3.17. -/
theorem projection_mem_tailRescale_of_high_odd
    (S : b.Lemma65Setup) (hB : b.HasPropertyB) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hgapOdd : Odd b.lemma62Gap)
    (hfinal : b.lemma62Gap + 2 * (S.k : Int) =
      2 * (ramificationIndex K : Int) + 1) :
    S.projection x ∈ S.tailRescale.lattice := by
  by_contra hnotMem
  let y := S.projection x
  have hyMem : y ∈
      L.projectedLattice q b.head b.head_isAnisotropic := by
    simpa only [y] using S.projection_mem_tail x hx
  have hyNe :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic y ≠ 0 := by
    intro hyZero
    apply hnotMem
    rw [S.tailRescale.mem_lattice_iff_ord_ge_head_depth]
    refine ⟨hyMem, ?_⟩
    rw [hyZero, ord_zero]
    exact le_top
  have hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0 := by
    intro hzero
    have hprojection := S.quadratic_projection_eq_one_sub_sq_mul x heq
    rw [hzero, zero_mul] at hprojection
    exact hyNe (by simpa only [y] using hprojection)
  let p : Kˣ := S.projectionFactorUnit x hfactorNe
  have hordY :=
    S.ord_quadratic_projection_eq_head_add_projectionFactor
      x heq hfactorNe
  change ord K ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic y) =
      ((b.order 0 + ordUnit K p : Int) : WithTop Int) at hordY
  have htailOrderZero : b.tail.order 0 = b.order 1 := by
    rw [b.order_tail]
    congr 1
  have htailOrderOne : b.tail.order 1 = b.order 2 := by
    rw [b.order_tail]
    congr 1
  have htailValueZero : b.tail.value 0 = b.value 1 := by
    rw [b.value_tail]
    congr 1
  have hthresholdNot : ¬
      (((b.tail.order 0 + 2 * (S.k : Int) - 1 : Int) : WithTop Int) ≤
        ord K ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic y)) := by
    intro hthreshold
    apply hnotMem
    exact (S.tailRescale.mem_lattice_iff_ord_ge_head_depth y).2
      ⟨hyMem, hthreshold⟩
  have hyLtThreshold := lt_of_not_ge hthresholdNot
  have hpLtTwoE : ordUnit K p <
      2 * (ramificationIndex K : Int) := by
    rw [hordY] at hyLtThreshold
    norm_cast at hyLtThreshold
    rw [htailOrderZero] at hyLtThreshold
    unfold lemma62Gap at hfinal
    omega
  have hpUpper : ordUnit K p ≤
      2 * (ramificationIndex K : Int) := hpLtTwoE.le
  have hpEven : Even (ordUnit K p) := by
    exact even_ordUnit_of_hasSomeEqualNormGeneratorBasis_of_le_two_e
      p
      (by simpa only [p] using
        S.projectionFactorUnit_isBinaryParameterAdmissible x hx hfactorNe)
      (by simpa only [p] using
        S.projectionFactorUnit_hasSomeEqualNormGeneratorBasis x hx hfactorNe)
      hpUpper
  have hgapNonneg : 0 ≤ b.lemma62Gap := by
    have hadmissible :=
      b.adjacentParameter_isBinaryParameterAdmissible 0 (by simp)
    rw [← b.ordUnit_adjacentParameter_zero]
    exact hadmissible.ordUnit_nonneg_of_odd (by
      simpa only [b.ordUnit_adjacentParameter_zero] using hgapOdd)
  have hgapUpper : b.lemma62Gap ≤
      2 * (ramificationIndex K : Int) + 1 := by
    have hkNonneg : (0 : Int) ≤ (S.k : Int) := by positivity
    omega
  have htrigger : b.propertyBTrigger (0 : Fin (n + 2)) := by
    unfold propertyBTrigger
    left
    have hsucc : (0 : Fin (n + 2)).succ = (1 : Fin (n + 3)) :=
      Fin.ext rfl
    have hcast : (0 : Fin (n + 2)).castSucc = (0 : Fin (n + 3)) :=
      Fin.ext rfl
    rw [hsucc, hcast]
    simpa only [lemma62Gap] using And.intro hgapUpper hgapOdd
  have hthirdGap :
      2 * (ramificationIndex K : Int) + 1 ≤
        b.order 2 - b.order 1 := by
    have hright := (hB.2 (0 : Fin (n + 2)) htrigger).2
    exact hright (2 : Fin (n + 3)) rfl
  have htailOrder : b.tail.order 0 ≤ b.tail.order 1 := by
    rw [htailOrderZero, htailOrderOne]
    omega
  let wt := b.tail.headInverseRescaleWitness
  have htailB : b.tail.HasPropertyB := hB.tail_for_lemma62
  have hvalues := b.tail.beliLemma62_ii_a wt (Or.inl htailB) htailOrder
  have hyValue :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic y ∈
        Lattice.quadraticValueSet
          (q.orthogonalSpace b.head b.head_isAnisotropic)
          (L.projectedLattice q b.head b.head_isAnisotropic) := by
    rw [Lattice.mem_quadraticValueSet_iff]
    exact ⟨y, hyMem, rfl⟩
  rcases hvalues hyValue with ⟨c, hcError⟩
  let qy : K :=
    (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic y
  let main : K := b.value 1 * (c : K) ^ 2
  have herrorOrder : (b.order 2 : WithTop Int) ≤ ord K (qy - main) := by
    have h := (Lattice.mem_powerIdeal_iff (K := K)
      (b.tail.order 1)
      ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic y -
        b.tail.value 0 * (c : K) ^ 2)).1 hcError
    simpa only [qy, main, htailValueZero, htailOrderOne] using h
  have hqIntLtThird : b.order 0 + ordUnit K p < b.order 2 := by
    unfold lemma62Gap at hfinal hgapNonneg
    omega
  have hqLtError : ord K qy < ord K (qy - main) := by
    have hqLtThird : ord K qy < (b.order 2 : WithTop Int) := by
      change ord K
          ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic y) < _
      rw [hordY]
      exact_mod_cast hqIntLtThird
    exact hqLtThird.trans_le herrorOrder
  have hmainOrder : ord K main = ord K qy := by
    have hidentity : main = qy - (qy - main) := by ring
    rw [hidentity]
    exact (ord K).map_sub_eq_of_lt_left hqLtError
  have hmainNe : main ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero] at hmainOrder
    have hqyFinite : ord K qy ≠ ⊤ := by
      rw [show ord K qy =
          ((b.order 0 + ordUnit K p : Int) : WithTop Int) by
        simpa only [qy] using hordY]
      exact WithTop.coe_ne_top
    exact hqyFinite hmainOrder.symm
  have hcNe : (c : K) ≠ 0 := by
    intro hzero
    apply hmainNe
    simp [main, hzero]
  let cUnit : Kˣ := Units.mk0 (c : K) hcNe
  have hmainOrderFormula : ord K main =
      ((b.order 1 + 2 * ordUnit K cUnit : Int) : WithTop Int) := by
    rw [show main = b.value 1 * (c : K) ^ 2 by rfl,
      ord_mul, ord_pow, ← b.coe_order]
    have hcOrder : ord K (c : K) =
        (ordUnit K cUnit : WithTop Int) := by
      simpa only [cUnit, Units.val_mk0] using (coe_ordUnit K cUnit).symm
    rw [hcOrder]
    simp only [two_nsmul]
    norm_cast
    omega
  have hpOrderEq : ordUnit K p =
      b.lemma62Gap + 2 * ordUnit K cUnit := by
    apply WithTop.coe_injective
    have horders :
        ((b.order 1 + 2 * ordUnit K cUnit : Int) : WithTop Int) =
          ((b.order 0 + ordUnit K p : Int) : WithTop Int) := by
      rw [← hmainOrderFormula, hmainOrder]
      simpa only [qy] using hordY
    norm_cast at horders ⊢
    unfold lemma62Gap
    omega
  have hpOdd : Odd (ordUnit K p) := by
    rcases hgapOdd with ⟨r, hr⟩
    refine ⟨r + ordUnit K cUnit, ?_⟩
    rw [hpOrderEq, hr]
    ring
  rcases hpEven with ⟨r, hr⟩
  rcases hpOdd with ⟨s, hs⟩
  omega

/-- Beli's first case (5): over a residue-two field, a projection cannot be
a norm generator of the original tail when the first gap is exactly `2e`.
Indeed its projection parameter would also have order `2e`; the endpoint
alternative of Lemma 3.17 requires a larger residue field, while all other
alternatives are excluded by the order and the positive defect of a unit. -/
theorem projection_not_originalTailGenerator_of_gap_eq_two_e_residue_two
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hgap : b.lemma62Gap = 2 * (ramificationIndex K : Int))
    (hresidue : ¬HasResidueFieldMoreThanTwoElements (K := K)) :
    ¬Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic)
      (S.projection x) := by
  intro hgenerator
  have hfactorNe :=
    S.projectionFactor_ne_zero_of_originalTail_isNormGenerator
      x heq hgenerator
  let p : Kˣ := S.projectionFactorUnit x hfactorNe
  let εp : Kˣ := normalizedUnitPart K p
  have hpOrder : ordUnit K p = 2 * (ramificationIndex K : Int) := by
    have h :=
      S.ordUnit_projectionFactorUnit_of_originalTail_isNormGenerator
        x heq hgenerator
    simpa only [p, hgap] using h
  have hεpUnit : IsValuationUnit K (εp : K) := by
    simpa only [εp] using normalizedUnitPart_isValuationUnit K p
  have hdefectOne : (1 : ℕ∞) ≤ quadraticDefect K (-εp) := by
    have hnegUnit : IsValuationUnit K ((-εp : Kˣ) : K) := by
      change ord K (-((εp : Kˣ) : K)) = 0
      rw [ord_neg]
      exact hεpUnit
    exact one_le_quadraticDefect_of_unit (-εp) hnegUnit
  have hcases : BeliLemma317ParameterCases (K := K)
      (2 * (ramificationIndex K : Int)) εp := by
    have h := S.projectionFactorUnit_parameterCases x hx hfactorNe
    simpa only [p, εp, hpOrder] using h
  simp only [BeliLemma317ParameterCases] at hcases
  rcases hcases with hhigh | hboundary | hinterior | hendpoint
  · omega
  · have hfinite : quadraticDefect K (-εp) ≠ ⊤ := hboundary.1
    have hzero : (quadraticDefect K (-εp)).toNat = 0 := by
      omega
    have hpositive : 1 ≤ (quadraticDefect K (-εp)).toNat := by
      rw [← ENat.coe_toNat hfinite] at hdefectOne
      exact_mod_cast hdefectOne
    omega
  · omega
  · exact hresidue hendpoint.2

/-- Consequently the projection belongs to the once-rescaled tail in the
`R₂-R₁=2e` residue-two endpoint of Beli's case (5). -/
theorem projection_mem_tailRescale_of_gap_eq_two_e_residue_two
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hgap : b.lemma62Gap = 2 * (ramificationIndex K : Int))
    (hk : S.k = 1)
    (hresidue : ¬HasResidueFieldMoreThanTwoElements (K := K)) :
    S.projection x ∈ S.tailRescale.lattice := by
  have htailMem : S.projection x ∈
      L.projectedLattice q b.head b.head_isAnisotropic :=
    S.projection_mem_tail x hx
  have hnotGenerator :=
    S.projection_not_originalTailGenerator_of_gap_eq_two_e_residue_two
      x hx heq hgap hresidue
  have hdeep :=
    (b.tail.mem_and_not_isNormGenerator_iff_ord_ge_head_add_one
      (S.projection x)).1 ⟨htailMem, hnotGenerator⟩
  rw [S.tailRescale.mem_lattice_iff_ord_ge_head_depth]
  refine ⟨htailMem, ?_⟩
  convert hdeep.2 using 1
  norm_cast
  rw [hk]
  norm_num
  omega

/-- Over a residue-two field, no nonzero projection factor arising from an
equal-value pair can have order exactly `2e`. -/
theorem ordUnit_projectionFactorUnit_ne_two_e_of_residue_two
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hresidue : ¬HasResidueFieldMoreThanTwoElements (K := K)) :
    ordUnit K (S.projectionFactorUnit x hfactorNe) ≠
      2 * (ramificationIndex K : Int) := by
  intro hpOrder
  let p : Kˣ := S.projectionFactorUnit x hfactorNe
  let εp : Kˣ := normalizedUnitPart K p
  have hpOrder' : ordUnit K p =
      2 * (ramificationIndex K : Int) := by
    simpa only [p] using hpOrder
  have hεpUnit : IsValuationUnit K (εp : K) := by
    simpa only [εp] using normalizedUnitPart_isValuationUnit K p
  have hdefectOne : (1 : ℕ∞) ≤ quadraticDefect K (-εp) := by
    have hnegUnit : IsValuationUnit K ((-εp : Kˣ) : K) := by
      change ord K (-((εp : Kˣ) : K)) = 0
      rw [ord_neg]
      exact hεpUnit
    exact one_le_quadraticDefect_of_unit (-εp) hnegUnit
  have hcases : BeliLemma317ParameterCases (K := K)
      (2 * (ramificationIndex K : Int)) εp := by
    have h := S.projectionFactorUnit_parameterCases x hx hfactorNe
    simpa only [p, εp, hpOrder'] using h
  simp only [BeliLemma317ParameterCases] at hcases
  rcases hcases with hhigh | hboundary | hinterior | hendpoint
  · omega
  · have hfinite : quadraticDefect K (-εp) ≠ ⊤ := hboundary.1
    have hzero : (quadraticDefect K (-εp)).toNat = 0 := by
      omega
    have hpositive : 1 ≤ (quadraticDefect K (-εp)).toNat := by
      rw [← ENat.coe_toNat hfinite] at hdefectOne
      exact_mod_cast hdefectOne
    omega
  · omega
  · exact hresidue hendpoint.2

/-- A normalized adjacent defect strictly larger than one has quadratic
defect at least two.  This is the exact coercion bridge needed in the
exceptional part of Beli's case (5). -/
theorem two_le_quadraticDefect_normalizedAdjacentProduct_of_one_lt
    (i : Fin (n + 2))
    (h : (((1 : ℚ) : WithTop ℚ) < b.normalizedAdjacentDefectOrder i)) :
    (2 : ℕ∞) ≤ quadraticDefect K (b.normalizedAdjacentProduct i) := by
  unfold normalizedAdjacentDefectOrder at h
  cases hd : quadraticDefect K (b.normalizedAdjacentProduct i) with
  | top => exact le_top
  | coe d =>
      rw [hd] at h
      change ((1 : ℚ) : WithTop ℚ) < ((d : ℚ) : WithTop ℚ) at h
      norm_cast at h ⊢

/-- In the exceptional residue-two branch, the projection is not a norm
generator of the original projected tail.  Both factors of its normalized
value ratio have defect at least two, forcing the same lower bound for the
projection parameter; every Lemma 3.17 alternative at order `2e-2` is then
impossible. -/
theorem projection_not_originalTailGenerator_of_exceptional
    (S : b.Lemma65Setup) (hB : b.HasPropertyB) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hgap : b.lemma62Gap = 2 * (ramificationIndex K : Int) - 2)
    (hdefect : (((1 : ℚ) : WithTop ℚ) <
      b.normalizedAdjacentDefectOrder 0))
    (hresidue : ¬HasResidueFieldMoreThanTwoElements (K := K)) :
    ¬Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic)
      (S.projection x) := by
  intro hgenerator
  let a₀ : Kˣ := b.adjacentParameter 0 (by simp)
  let ratio : Kˣ :=
    b.tail.normGeneratorValueRatioUnit (S.projection x) hgenerator
  have hfactorNe :=
    S.projectionFactor_ne_zero_of_originalTail_isNormGenerator
      x heq hgenerator
  let p : Kˣ := S.projectionFactorUnit x hfactorNe
  let εp : Kˣ := normalizedUnitPart K p
  have hpEq : p = a₀ * ratio := by
    simpa only [p, a₀, ratio] using
      S.projectionFactorUnit_eq_adjacentParameter_mul_tailRatio
        x heq hgenerator
  have hpOrder : ordUnit K p = b.lemma62Gap := by
    simpa only [p] using
      S.ordUnit_projectionFactorUnit_of_originalTail_isNormGenerator
        x heq hgenerator
  have hePos : (0 : Int) < (ramificationIndex K : Int) := by
    exact_mod_cast ramificationIndex_pos K
  have hgapEven : Even b.lemma62Gap := by
    refine ⟨(ramificationIndex K : Int) - 1, ?_⟩
    omega
  have hgapUpper : b.lemma62Gap ≤
      2 * (ramificationIndex K : Int) := by omega
  have hgapNe : b.lemma62Gap ≠
      2 * (ramificationIndex K : Int) := by omega
  have hcutoff : b.lemma62DefectCutoff = 1 := by
    have hcast := b.lemma62DefectCutoff_cast hgapEven hgapUpper
    rw [hgap] at hcast
    have hcutNat : (b.lemma62DefectCutoff : Int) = 1 := by
      omega
    exact_mod_cast hcutNat
  have hratioDefect : (2 : ℕ∞) ≤ quadraticDefect K ratio := by
    have h := S.tailNormGeneratorRatio_defect_ge_cutoff_succ
      hB hgapEven hgapUpper hgapNe (S.projection x) hgenerator
    simp only [hcutoff] at h
    norm_num at h
    simpa only [ratio] using h
  have ha₀Defect : (2 : ℕ∞) ≤ quadraticDefect K (-a₀) := by
    have hnormalized : (2 : ℕ∞) ≤
        quadraticDefect K (b.normalizedAdjacentProduct (0 : Fin (n + 2))) :=
      two_le_quadraticDefect_normalizedAdjacentProduct_of_one_lt
        (b := b) 0 hdefect
    have heqDefect :=
      b.quadraticDefect_negative_adjacentParameter_eq_normalizedProduct_of_even
        (0 : Fin (n + 2)) (by
          have hsucc : (0 : Fin (n + 2)).succ =
              (1 : Fin (n + 3)) := Fin.ext rfl
          have hcast : (0 : Fin (n + 2)).castSucc =
              (0 : Fin (n + 3)) := Fin.ext rfl
          rw [hsucc, hcast]
          simpa only [lemma62Gap] using hgapEven)
    change (2 : ℕ∞) ≤ quadraticDefect K (-a₀)
    rw [show quadraticDefect K (-a₀) =
        quadraticDefect K (b.normalizedAdjacentProduct (0 : Fin (n + 2))) by
      simpa [a₀] using heqDefect]
    exact hnormalized
  have hproductDefect : (2 : ℕ∞) ≤
      quadraticDefect K ((-a₀) * ratio) := by
    exact le_trans (le_min ha₀Defect hratioDefect)
      (quadraticDefect_mul_ge_min K (-a₀) ratio)
  have hpNeg : -p = (-a₀) * ratio := by
    rw [hpEq]
    simp
  have hpDefect : (2 : ℕ∞) ≤ quadraticDefect K (-p) := by
    rw [hpNeg]
    exact hproductDefect
  have hεpUnit : IsValuationUnit K (εp : K) := by
    simpa only [εp] using normalizedUnitPart_isValuationUnit K p
  have hpFactor : uniformizerPowerUnit K b.lemma62Gap * εp = p := by
    rw [← hpOrder]
    simpa only [εp] using uniformizerPower_mul_normalizedUnitPart K p
  have hpDefectEq :
      quadraticDefect K (-p) = quadraticDefect K (-εp) := by
    have h :=
      beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
        (K := K) b.lemma62Gap εp hεpUnit hgapEven
    rw [hpFactor] at h
    exact h
  have hεpDefect : (2 : ℕ∞) ≤ quadraticDefect K (-εp) := by
    rw [← hpDefectEq]
    exact hpDefect
  have hcases : BeliLemma317ParameterCases (K := K)
      b.lemma62Gap εp := by
    have h := S.projectionFactorUnit_parameterCases x hx hfactorNe
    simpa only [p, εp, hpOrder] using h
  simp only [BeliLemma317ParameterCases] at hcases
  rcases hcases with hhigh | hboundary | hinterior | hendpoint
  · omega
  · have hfinite : quadraticDefect K (-εp) ≠ ⊤ := hboundary.1
    have hone : (quadraticDefect K (-εp)).toNat = 1 := by
      rw [hgap] at hboundary
      omega
    have htwo : 2 ≤ (quadraticDefect K (-εp)).toNat := by
      rw [← ENat.coe_toNat hfinite] at hεpDefect
      exact_mod_cast hεpDefect
    omega
  · have hhalfOdd : Odd
        (b.lemma62Gap / 2 + (ramificationIndex K : Int)) := by
      have hrewrite :
          2 * (ramificationIndex K : Int) - 2 =
            2 * ((ramificationIndex K : Int) - 1) := by ring
      have hhalf : b.lemma62Gap / 2 =
          (ramificationIndex K : Int) - 1 := by
        rw [hgap, hrewrite, Int.mul_ediv_cancel_left]
        norm_num
      refine ⟨(ramificationIndex K : Int) - 1, ?_⟩
      rw [hhalf]
      ring
    exact (Int.not_even_iff_odd.mpr hhalfOdd hinterior.2.2.2.1).elim
  · exact hresidue hendpoint.2

/-- Beli's exceptional case (5), now as the concrete witness required by
Lemma 6.5(i).  The once-rescaled tail is the predecessor of the given
two-step rescaling. -/
noncomputable def exceptionalProjectionWitness
    (S : b.Lemma65Setup) (hB : b.HasPropertyB) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hgap : b.lemma62Gap = 2 * (ramificationIndex K : Int) - 2)
    (hdefect : (((1 : ℚ) : WithTop ℚ) <
      b.normalizedAdjacentDefectOrder 0))
    (hresidue : ¬HasResidueFieldMoreThanTwoElements (K := K))
    (hk : S.k = 2) :
    Lemma65ExceptionalProjectionWitness b x := by
  have wTwo : b.tail.HeadRescaleWitness (1 + 1) := by
    simpa only [one_add_one_eq_two, hk] using S.tailRescale
  let wOne : b.tail.HeadRescaleWitness 1 := wTwo.predecessor
  have htailMem : S.projection x ∈
      L.projectedLattice q b.head b.head_isAnisotropic :=
    S.projection_mem_tail x hx
  have hnotOriginal :=
    S.projection_not_originalTailGenerator_of_exceptional
      hB x hx heq hgap hdefect hresidue
  have hdeep :=
    (b.tail.mem_and_not_isNormGenerator_iff_ord_ge_head_add_one
      (S.projection x)).1 ⟨htailMem, hnotOriginal⟩
  have hyOne : S.projection x ∈ wOne.lattice := by
    rw [wOne.mem_lattice_iff_ord_ge_head_depth]
    refine ⟨htailMem, ?_⟩
    convert hdeep.2 using 1
    norm_cast
    norm_num
    ring
  refine {
    tailRescaleOne := wOne
    projection_mem := hyOne
    projection_not_generator := ?_
  }
  intro hgeneratorOne
  have hyOrder :
      ord K ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (S.projection x)) =
        (wOne.bong.order 0 : WithTop Int) :=
    (wOne.bong.isNormGenerator_iff_ord_quadratic_eq_head
      (S.projection x) hgeneratorOne.mem).1 hgeneratorOne
  have hyNe :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (S.projection x) ≠ 0 := by
    intro hyZero
    rw [hyZero, ord_zero] at hyOrder
    exact WithTop.top_ne_coe hyOrder
  have hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0 := by
    intro hzero
    have hprojection := S.quadratic_projection_eq_one_sub_sq_mul x heq
    rw [hzero, zero_mul] at hprojection
    exact hyNe hprojection
  let p : Kˣ := S.projectionFactorUnit x hfactorNe
  have hpValueOrder :=
    S.ord_quadratic_projection_eq_head_add_projectionFactor
      x heq hfactorNe
  change ord K
      ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
        (S.projection x)) =
      ((b.order 0 + ordUnit K p : Int) : WithTop Int) at hpValueOrder
  have horderInt : b.order 0 + ordUnit K p = wOne.bong.order 0 := by
    apply WithTop.coe_injective
    exact hpValueOrder.symm.trans hyOrder
  have hwOneOrder : wOne.bong.order 0 = b.tail.order 0 + 2 := by
    have h := wOne.order_zero_eq
    norm_num at h
    exact h
  have htailOrderZero : b.tail.order 0 = b.order 1 := by
    rw [b.order_tail]
    congr 1
  have hpOrder : ordUnit K p =
      2 * (ramificationIndex K : Int) := by
    rw [hwOneOrder, htailOrderZero] at horderInt
    unfold lemma62Gap at hgap
    omega
  exact (S.ordUnit_projectionFactorUnit_ne_two_e_of_residue_two
    x hx hfactorNe hresidue) (by simpa only [p] using hpOrder)

/-- The exceptional projection is not a norm generator of the original tail,
stated intrinsically and hence without the over-strong concrete setup. -/
theorem projection_not_originalTailGenerator_of_exceptional_intrinsic
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hgap : b.lemma62Gap = 2 * (ramificationIndex K : Int) - 2)
    (hdefect : (((1 : ℚ) : WithTop ℚ) <
      b.normalizedAdjacentDefectOrder 0))
    (hresidue : ¬HasResidueFieldMoreThanTwoElements (K := K)) :
    ¬Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic)
      (b.lemma65Projection x) := by
  intro hgenerator
  let a₀ : Kˣ := b.adjacentParameter 0 (by simp)
  let ratio : Kˣ :=
    b.tail.normGeneratorValueRatioUnit (b.lemma65Projection x) hgenerator
  have hfactorNe :=
    lemma65ProjectionFactor_ne_zero_of_originalTail_isNormGenerator
      b x heq hgenerator
  let p : Kˣ := lemma65ProjectionFactorUnitIntrinsic b x hfactorNe
  let εp : Kˣ := normalizedUnitPart K p
  have hpEq : p = a₀ * ratio := by
    simpa only [p, a₀, ratio] using
      lemma65ProjectionFactorUnitIntrinsic_eq_adjacentParameter_mul_tailRatio
        b x heq hgenerator
  have hpOrder : ordUnit K p = b.lemma62Gap := by
    simpa only [p] using
      ordUnit_lemma65ProjectionFactorUnitIntrinsic_of_originalTail_isNormGenerator
        b x heq hgenerator
  have hePos : (0 : Int) < (ramificationIndex K : Int) := by
    exact_mod_cast ramificationIndex_pos K
  have hgapEven : Even b.lemma62Gap := by
    refine ⟨(ramificationIndex K : Int) - 1, ?_⟩
    omega
  have hgapUpper : b.lemma62Gap ≤
      2 * (ramificationIndex K : Int) := by omega
  have hgapNe : b.lemma62Gap ≠
      2 * (ramificationIndex K : Int) := by omega
  have hcutoff : b.lemma62DefectCutoff = 1 := by
    have hcast := b.lemma62DefectCutoff_cast hgapEven hgapUpper
    rw [hgap] at hcast
    have hcutNat : (b.lemma62DefectCutoff : Int) = 1 := by
      omega
    exact_mod_cast hcutNat
  have hratioDefect : (2 : ℕ∞) ≤ quadraticDefect K ratio := by
    have h := tailNormGeneratorRatio_defect_ge_cutoff_succ_intrinsic
      b hB hgapEven hgapUpper hgapNe (b.lemma65Projection x) hgenerator
    simp only [hcutoff] at h
    norm_num at h
    simpa only [ratio] using h
  have ha₀Defect : (2 : ℕ∞) ≤ quadraticDefect K (-a₀) := by
    have hnormalized : (2 : ℕ∞) ≤
        quadraticDefect K (b.normalizedAdjacentProduct (0 : Fin (n + 2))) :=
      two_le_quadraticDefect_normalizedAdjacentProduct_of_one_lt
        (b := b) 0 hdefect
    have heqDefect :=
      b.quadraticDefect_negative_adjacentParameter_eq_normalizedProduct_of_even
        (0 : Fin (n + 2)) (by
          have hsucc : (0 : Fin (n + 2)).succ =
              (1 : Fin (n + 3)) := Fin.ext rfl
          have hcast : (0 : Fin (n + 2)).castSucc =
              (0 : Fin (n + 3)) := Fin.ext rfl
          rw [hsucc, hcast]
          simpa only [lemma62Gap] using hgapEven)
    change (2 : ℕ∞) ≤ quadraticDefect K (-a₀)
    rw [show quadraticDefect K (-a₀) =
        quadraticDefect K (b.normalizedAdjacentProduct (0 : Fin (n + 2))) by
      simpa [a₀] using heqDefect]
    exact hnormalized
  have hproductDefect : (2 : ℕ∞) ≤
      quadraticDefect K ((-a₀) * ratio) := by
    exact le_trans (le_min ha₀Defect hratioDefect)
      (quadraticDefect_mul_ge_min K (-a₀) ratio)
  have hpNeg : -p = (-a₀) * ratio := by
    rw [hpEq]
    simp
  have hpDefect : (2 : ℕ∞) ≤ quadraticDefect K (-p) := by
    rw [hpNeg]
    exact hproductDefect
  have hεpUnit : IsValuationUnit K (εp : K) := by
    simpa only [εp] using normalizedUnitPart_isValuationUnit K p
  have hpFactor : uniformizerPowerUnit K b.lemma62Gap * εp = p := by
    rw [← hpOrder]
    simpa only [εp] using uniformizerPower_mul_normalizedUnitPart K p
  have hpDefectEq :
      quadraticDefect K (-p) = quadraticDefect K (-εp) := by
    have h :=
      beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
        (K := K) b.lemma62Gap εp hεpUnit hgapEven
    rw [hpFactor] at h
    exact h
  have hεpDefect : (2 : ℕ∞) ≤ quadraticDefect K (-εp) := by
    rw [← hpDefectEq]
    exact hpDefect
  have hcases : BeliLemma317ParameterCases (K := K)
      b.lemma62Gap εp := by
    have h := lemma65ProjectionFactorUnitIntrinsic_parameterCases
      b x hx hfactorNe
    simpa only [p, εp, hpOrder] using h
  simp only [BeliLemma317ParameterCases] at hcases
  rcases hcases with hhigh | hboundary | hinterior | hendpoint
  · omega
  · have hfinite : quadraticDefect K (-εp) ≠ ⊤ := hboundary.1
    have hone : (quadraticDefect K (-εp)).toNat = 1 := by
      rw [hgap] at hboundary
      omega
    have htwo : 2 ≤ (quadraticDefect K (-εp)).toNat := by
      rw [← ENat.coe_toNat hfinite] at hεpDefect
      exact_mod_cast hεpDefect
    omega
  · have hhalfOdd : Odd
        (b.lemma62Gap / 2 + (ramificationIndex K : Int)) := by
      have hrewrite :
          2 * (ramificationIndex K : Int) - 2 =
            2 * ((ramificationIndex K : Int) - 1) := by ring
      have hhalf : b.lemma62Gap / 2 =
          (ramificationIndex K : Int) - 1 := by
        rw [hgap, hrewrite, Int.mul_ediv_cancel_left]
        norm_num
      refine ⟨(ramificationIndex K : Int) - 1, ?_⟩
      rw [hhalf]
      ring
    exact (Int.not_even_iff_odd.mpr hhalfOdd hinterior.2.2.2.1).elim
  · exact hresidue hendpoint.2

/-- Correct exceptional realization of Lemma 6.5(i): construct the
once-rescaled tail directly, without assuming a nonexistent two-step tail
BONG. -/
noncomputable def exceptionalProjectionWitnessIntrinsic
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hgap : b.lemma62Gap = 2 * (ramificationIndex K : Int) - 2)
    (hdefect : (((1 : ℚ) : WithTop ℚ) <
      b.normalizedAdjacentDefectOrder 0))
    (hresidue : ¬HasResidueFieldMoreThanTwoElements (K := K)) :
    Lemma65ExceptionalProjectionWitness b x := by
  have hprevious : b.order 1 - b.order 0 ≤
      2 * (ramificationIndex K : Int) := by
    unfold lemma62Gap at hgap
    omega
  let wOne : b.tail.HeadRescaleWitness 1 :=
    b.tailHeadRescaleWitness_one_of_previousGap_le_two_e hB hprevious
  have htailMem : b.lemma65Projection x ∈
      L.projectedLattice q b.head b.head_isAnisotropic :=
    lemma65Projection_mem_tail_intrinsic b x hx
  have hnotOriginal :=
    projection_not_originalTailGenerator_of_exceptional_intrinsic
      b hB x hx heq hgap hdefect hresidue
  have hdeep :=
    (b.tail.mem_and_not_isNormGenerator_iff_ord_ge_head_add_one
      (b.lemma65Projection x)).1 ⟨htailMem, hnotOriginal⟩
  have hyOne : b.lemma65Projection x ∈ wOne.lattice := by
    rw [wOne.mem_lattice_iff_ord_ge_head_depth]
    refine ⟨htailMem, ?_⟩
    convert hdeep.2 using 1
    norm_cast
    norm_num
    ring
  refine {
    tailRescaleOne := wOne
    projection_mem := hyOne
    projection_not_generator := ?_
  }
  intro hgeneratorOne
  have hyOrder :
      ord K ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (b.lemma65Projection x)) =
        (wOne.bong.order 0 : WithTop Int) :=
    (wOne.bong.isNormGenerator_iff_ord_quadratic_eq_head
      (b.lemma65Projection x) hgeneratorOne.mem).1 hgeneratorOne
  have hyNe :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (b.lemma65Projection x) ≠ 0 := by
    intro hyZero
    rw [hyZero, ord_zero] at hyOrder
    exact WithTop.top_ne_coe hyOrder
  have hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0 := by
    intro hzero
    have hprojection :=
      quadratic_lemma65Projection_eq_one_sub_sq_mul_intrinsic b x heq
    rw [hzero, zero_mul] at hprojection
    exact hyNe hprojection
  let p : Kˣ := lemma65ProjectionFactorUnitIntrinsic b x hfactorNe
  have hpValueOrder :=
    ord_quadratic_lemma65Projection_eq_head_add_factorIntrinsic
      b x heq hfactorNe
  change ord K
      ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
        (b.lemma65Projection x)) =
      ((b.order 0 + ordUnit K p : Int) : WithTop Int) at hpValueOrder
  have horderInt : b.order 0 + ordUnit K p = wOne.bong.order 0 := by
    apply WithTop.coe_injective
    exact hpValueOrder.symm.trans hyOrder
  have hwOneOrder : wOne.bong.order 0 = b.tail.order 0 + 2 := by
    have h := wOne.order_zero_eq
    norm_num at h
    exact h
  have htailOrderZero : b.tail.order 0 = b.order 1 := by
    rw [b.order_tail]
    congr 1
  have hpOrder : ordUnit K p =
      2 * (ramificationIndex K : Int) := by
    rw [hwOneOrder, htailOrderZero] at horderInt
    unfold lemma62Gap at hgap
    omega
  exact
    (ordUnit_lemma65ProjectionFactorUnitIntrinsic_ne_two_e_of_residue_two
      b x hx hfactorNe hresidue) (by simpa only [p] using hpOrder)

/-- Minimality alone reduces the high range to the first admissible order
strictly above `2e`: unless `k=0`, the final shifted gap is `2e+1` or
`2e+2`. -/
theorem highRange_k_eq_zero_or_final_eq
    (S : b.Lemma65Setup) (hhigh : b.Lemma65HighRange S) :
    S.k = 0 ∨
      b.lemma62Gap + 2 * (S.k : Int) =
        2 * (ramificationIndex K : Int) + 1 ∨
      b.lemma62Gap + 2 * (S.k : Int) =
        2 * (ramificationIndex K : Int) + 2 := by
  apply S.toMinimalityData.highRange_k_eq_zero_or_final_eq
  exact hhigh

/-- Subtracting the even shift from the odd high endpoint preserves odd
parity of the original first gap. -/
theorem lemma62Gap_odd_of_final_eq_two_e_add_one
    (S : b.Lemma65Setup)
    (hfinal : b.lemma62Gap + 2 * (S.k : Int) =
      2 * (ramificationIndex K : Int) + 1) :
    Odd b.lemma62Gap := by
  exact S.toMinimalityData.lemma62Gap_odd_of_final_eq_two_e_add_one hfinal

/-- If the least positive shift lands at the even high endpoint `2e+2`,
the residue field must have two elements.  Otherwise the preceding order
`2e` is already an endpoint parameter in Lemma 3.17. -/
theorem residue_two_of_final_eq_two_e_add_two
    (S : b.Lemma65Setup) (hkNe : S.k ≠ 0)
    (hfinal : b.lemma62Gap + 2 * (S.k : Int) =
      2 * (ramificationIndex K : Int) + 2) :
    ¬HasResidueFieldMoreThanTwoElements (K := K) := by
  exact S.toMinimalityData.residue_two_of_final_eq_two_e_add_two hkNe hfinal

end Lemma65Setup

namespace Lemma65MinimalityData

variable {b : BONG V q L (n + 3)}

/-- If reaching `2e+2` requires at least two shifts, the original normalized
adjacent defect is strictly larger than one.  Otherwise the order `2e-2`
one step before the endpoint would already be the finite-defect boundary of
Lemma 3.17. -/
theorem normalizedAdjacentDefectOrder_one_lt_of_final_eq_two_e_add_two
    (M : b.Lemma65MinimalityData) (hkTwo : 2 ≤ M.k)
    (hfinal : b.lemma62Gap + 2 * (M.k : Int) =
      2 * (ramificationIndex K : Int) + 2) :
    (((1 : ℚ) : WithTop ℚ) < b.normalizedAdjacentDefectOrder 0) := by
  let a₀ : Kˣ := b.adjacentParameter 0 (by simp)
  let ε : Kˣ := normalizedUnitPart K a₀
  let dprod := quadraticDefect K
    (b.normalizedAdjacentProduct (0 : Fin (n + 2)))
  have hgapEven : Even b.lemma62Gap := by
    refine ⟨(ramificationIndex K : Int) + 1 - (M.k : Int), ?_⟩
    omega
  have hεDefectEq : quadraticDefect K (-ε) = dprod := by
    have hnormalize :=
      beliParameterDefect_eq_normalizedUnitPart_of_even
        (K := K) a₀ (by
          simpa only [a₀, b.ordUnit_adjacentParameter_zero] using hgapEven)
    have hadjacent :=
      b.quadraticDefect_negative_adjacentParameter_eq_normalizedProduct_of_even
        (0 : Fin (n + 2)) (by
          have hsucc : (0 : Fin (n + 2)).succ =
              (1 : Fin (n + 3)) := Fin.ext rfl
          have hcast : (0 : Fin (n + 2)).castSucc =
              (0 : Fin (n + 3)) := Fin.ext rfl
          rw [hsucc, hcast]
          simpa only [lemma62Gap] using hgapEven)
    have hadjacent' : quadraticDefect K (-a₀) = dprod := by
      simpa [a₀, dprod] using hadjacent
    exact hnormalize.symm.trans hadjacent'
  have hproductUnit : IsValuationUnit K
      ((b.normalizedAdjacentProduct (0 : Fin (n + 2)) : Kˣ) : K) := by
    unfold normalizedAdjacentProduct
    change ord K
      (-(((b.normalizedValue (0 : Fin (n + 3)) : Kˣ) : K) *
        ((b.normalizedValue (1 : Fin (n + 3)) : Kˣ) : K))) = 0
    rw [ord_neg, ord_mul,
      b.normalizedValue_isValuationUnit (0 : Fin (n + 3)),
      b.normalizedValue_isValuationUnit (1 : Fin (n + 3))]
    simp
  have hdprodOne : (1 : ℕ∞) ≤ dprod := by
    simpa only [dprod] using one_le_quadraticDefect_of_unit
      (b.normalizedAdjacentProduct (0 : Fin (n + 2))) hproductUnit
  by_contra hnot
  have hle : b.normalizedAdjacentDefectOrder (0 : Fin (n + 2)) ≤
      (((1 : ℚ) : WithTop ℚ)) := le_of_not_gt hnot
  cases hd : dprod with
  | top =>
      unfold normalizedAdjacentDefectOrder at hle
      change WithTop.map (fun m : Nat ↦ (m : ℚ)) dprod ≤
        (((1 : ℚ) : WithTop ℚ)) at hle
      have hmap : WithTop.map (fun m : Nat ↦ (m : ℚ)) dprod =
          (⊤ : WithTop ℚ) := by
        rw [hd]
        rfl
      rw [hmap] at hle
      exact (WithTop.not_top_le_coe (1 : ℚ)) hle
  | coe d =>
      have hdLower : 1 ≤ d := by
        rw [hd] at hdprodOne
        exact_mod_cast hdprodOne
      have hdUpper : d ≤ 1 := by
        unfold normalizedAdjacentDefectOrder at hle
        change WithTop.map (fun m : Nat ↦ (m : ℚ)) dprod ≤
          (((1 : ℚ) : WithTop ℚ)) at hle
        rw [hd] at hle
        change (((d : ℚ) : WithTop ℚ)) ≤
          (((1 : ℚ) : WithTop ℚ)) at hle
        norm_cast at hle
      have hdEq : d = 1 := by omega
      have hεDefectOne : quadraticDefect K (-ε) = (1 : ℕ∞) := by
        rw [hεDefectEq, hd, hdEq]
        exact ENat.coe_one
      let j : Nat := M.k - 2
      have hjLt : j < M.k := by omega
      have hjCast : (j : Int) = (M.k : Int) - 2 := by
        simp only [j]
        omega
      have hRj : b.lemma62Gap + 2 * (j : Int) =
          2 * (ramificationIndex K : Int) - 2 := by
        rw [hjCast]
        omega
      have hdFinite : quadraticDefect K (-ε) ≠ ⊤ := by
        rw [hεDefectOne]
        simp
      have hboundary : b.lemma62Gap + 2 * (j : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K (-ε)).toNat : Int) := by
        rw [hεDefectOne]
        norm_num
        exact hRj
      have hcases : BeliLemma317ParameterCases (K := K)
          (b.lemma62Gap + 2 * (j : Int)) ε := by
        simp only [BeliLemma317ParameterCases]
        exact Or.inr (Or.inl ⟨hdFinite, hboundary⟩)
      have hadmissible : b.HeadSecondRescaleAdmissible j := by
        apply b.headSecondRescaleAdmissible_of_parameterCases j
        simpa only [ε, a₀] using hcases
      exact M.not_admissible_of_lt j hjLt hadmissible

/-- No nonnegative second-vector shift of the first parameter can have the
refined `-1/4` class.  Such a class has order `-2e`; the universal lower
bound on the original adjacent gap then forces the shift to be zero, making
the original binary prefix hyperbolic. -/
theorem shiftedFirstParameter_class_ne_negativeQuarter
    (M : b.Lemma65MinimalityData) (j : Nat) :
    unitSquareClass K
        (uniformizerPowerUnit K
          (b.lemma62Gap + 2 * (j : Int)) *
            normalizedUnitPart K (b.adjacentParameter 0 (by simp))) ≠
      unitSquareClass K (negativeQuarterUnit K) := by
  intro hclass
  let a₀ : Kˣ := b.adjacentParameter 0 (by simp)
  let ε : Kˣ := normalizedUnitPart K a₀
  have hεUnit : IsValuationUnit K (ε : K) := by
    simpa only [ε, a₀] using normalizedUnitPart_isValuationUnit K a₀
  have horder := ordUnit_eq_of_unitSquareClass_eq (K := K) hclass
  rw [ordUnit_uniformizerPower_mul_valuationUnit
      (normalizedUnitPart K (b.adjacentParameter 0 (by simp)))
      (by simpa only [ε, a₀] using hεUnit)
      (b.lemma62Gap + 2 * (j : Int)),
    ordUnit_negativeQuarterUnit] at horder
  have hbaseLower : -(2 * (ramificationIndex K : Int)) ≤
      b.lemma62Gap := by
    let i0 : Fin (n + 3) := ⟨0, by omega⟩
    have hi0 : i0.1 + 1 < n + 3 := by simp [i0]
    have h := b.adjacentOrderGap_ge_neg_two_mul_e i0 hi0
    have hi0Eq : i0 = (0 : Fin (n + 3)) := Fin.ext rfl
    have hi1Eq : (⟨i0.1 + 1, hi0⟩ : Fin (n + 3)) = 1 := Fin.ext rfl
    rw [hi1Eq, hi0Eq] at h
    simpa only [lemma62Gap] using h
  have hjZero : j = 0 := by
    have hjNonneg : (0 : Int) ≤ (j : Int) := by positivity
    omega
  have hgapEq : b.lemma62Gap =
      -(2 * (ramificationIndex K : Int)) := by
    rw [hjZero] at horder
    norm_num at horder
    exact horder
  have hfactor : uniformizerPowerUnit K b.lemma62Gap * ε = a₀ := by
    simpa only [a₀, ε, b.ordUnit_adjacentParameter_zero] using
      uniformizerPower_mul_normalizedUnitPart K a₀
  have horiginalClass : unitSquareClass K a₀ =
      unitSquareClass K (negativeQuarterUnit K) := by
    rw [← hfactor]
    simpa only [ε, a₀, hjZero, Int.ofNat_eq_coe, Nat.cast_zero,
      mul_zero, add_zero] using hclass
  exact M.firstBinary_not_hyperbolic
    (b.firstBinaryIsHyperbolic_of_adjacentParameter_class_eq_negativeQuarter
      (by simpa only [a₀] using horiginalClass))

/-- The even high endpoint needs at most two shifts.  If a third shift were
needed, the order `2e-4` would satisfy either the finite-defect boundary or
the even interior alternative of Lemma 3.17; the only excluded interior
class is ruled out by `shiftedFirstParameter_class_ne_negativeQuarter`. -/
theorem k_le_two_of_final_eq_two_e_add_two
    (M : b.Lemma65MinimalityData)
    (hfinal : b.lemma62Gap + 2 * (M.k : Int) =
      2 * (ramificationIndex K : Int) + 2) :
    M.k ≤ 2 := by
  by_contra hnot
  have hkThree : 3 ≤ M.k := by omega
  have hdefect :=
    M.normalizedAdjacentDefectOrder_one_lt_of_final_eq_two_e_add_two
      (by omega) hfinal
  let a₀ : Kˣ := b.adjacentParameter 0 (by simp)
  let ε : Kˣ := normalizedUnitPart K a₀
  let d := quadraticDefect K (-ε)
  have hgapEven : Even b.lemma62Gap := by
    refine ⟨(ramificationIndex K : Int) + 1 - (M.k : Int), ?_⟩
    omega
  have hεDefectEq : d = quadraticDefect K
      (b.normalizedAdjacentProduct (0 : Fin (n + 2))) := by
    have hnormalize :=
      beliParameterDefect_eq_normalizedUnitPart_of_even
        (K := K) a₀ (by
          simpa only [a₀, b.ordUnit_adjacentParameter_zero] using hgapEven)
    have hadjacent :=
      b.quadraticDefect_negative_adjacentParameter_eq_normalizedProduct_of_even
        (0 : Fin (n + 2)) (by
          have hsucc : (0 : Fin (n + 2)).succ =
              (1 : Fin (n + 3)) := Fin.ext rfl
          have hcast : (0 : Fin (n + 2)).castSucc =
              (0 : Fin (n + 3)) := Fin.ext rfl
          rw [hsucc, hcast]
          simpa only [lemma62Gap] using hgapEven)
    have hadjacent' : quadraticDefect K (-a₀) =
        quadraticDefect K
          (b.normalizedAdjacentProduct (0 : Fin (n + 2))) := by
      simpa [a₀] using hadjacent
    simpa only [d, ε] using hnormalize.symm.trans hadjacent'
  have hdOrder : (((1 : ℚ) : WithTop ℚ) <
      WithTop.map (fun m : Nat ↦ (m : ℚ)) d) := by
    unfold normalizedAdjacentDefectOrder at hdefect
    rw [hεDefectEq]
    exact hdefect
  let j : Nat := M.k - 3
  have hjLt : j < M.k := by omega
  have hjCast : (j : Int) = (M.k : Int) - 3 := by
    simp only [j]
    omega
  let Rj : Int := b.lemma62Gap + 2 * (j : Int)
  have hRj : Rj = 2 * (ramificationIndex K : Int) - 4 := by
    simp only [Rj]
    rw [hjCast]
    omega
  have hRjUpper : Rj < 2 * (ramificationIndex K : Int) := by
    rw [hRj]
    omega
  have hRjEven : Even Rj := by
    refine ⟨(ramificationIndex K : Int) - 2, ?_⟩
    rw [hRj]
    ring
  have hRjHalfEven : Even
      (Rj / 2 + (ramificationIndex K : Int)) := by
    have hrewrite : 2 * (ramificationIndex K : Int) - 4 =
        2 * ((ramificationIndex K : Int) - 2) := by ring
    have hhalf : Rj / 2 = (ramificationIndex K : Int) - 2 := by
      rw [hRj, hrewrite, Int.mul_ediv_cancel_left]
      norm_num
    refine ⟨(ramificationIndex K : Int) - 1, ?_⟩
    rw [hhalf]
    ring
  have hquarter := M.shiftedFirstParameter_class_ne_negativeQuarter j
  have hcases : BeliLemma317ParameterCases (K := K) Rj ε := by
    simp only [BeliLemma317ParameterCases]
    cases hdEq : d with
    | top =>
        exact Or.inr (Or.inr (Or.inl
          ⟨Or.inl hdEq, hRjUpper, hRjEven, hRjHalfEven,
            by simpa only [Rj, ε, a₀] using hquarter⟩))
    | coe defect =>
        have hdefectTwo : 2 ≤ defect := by
          rw [hdEq] at hdOrder
          change ((1 : ℚ) : WithTop ℚ) <
            ((defect : ℚ) : WithTop ℚ) at hdOrder
          norm_cast at hdOrder
        have hdFinite : d ≠ ⊤ := by rw [hdEq]; simp
        by_cases hdefectEq : defect = 2
        · have hboundary : Rj =
              2 * (ramificationIndex K : Int) -
                2 * (d.toNat : Int) := by
            rw [hdEq, hdefectEq]
            norm_num
            exact hRj
          exact Or.inr (Or.inl ⟨hdFinite, hboundary⟩)
        · have hdefectThree : 3 ≤ defect := by omega
          have hboundaryLt :
              2 * (ramificationIndex K : Int) -
                  2 * (d.toNat : Int) < Rj := by
            rw [hdEq]
            norm_num
            rw [hRj]
            omega
          exact Or.inr (Or.inr (Or.inl
            ⟨Or.inr ⟨hdFinite, hboundaryLt⟩,
              hRjUpper, hRjEven, hRjHalfEven,
              by simpa only [Rj, ε, a₀] using hquarter⟩))
  have hadmissible : b.HeadSecondRescaleAdmissible j := by
    apply b.headSecondRescaleAdmissible_of_parameterCases j
    simpa only [Rj, ε, a₀] using hcases
  exact M.not_admissible_of_lt j hjLt hadmissible

/-- The positive even high endpoint is exactly the pair of residue-two
cases in Beli's case (5). -/
theorem cases_of_final_eq_two_e_add_two
    (M : b.Lemma65MinimalityData) (hkNe : M.k ≠ 0)
    (hfinal : b.lemma62Gap + 2 * (M.k : Int) =
      2 * (ramificationIndex K : Int) + 2) :
    (b.lemma62Gap = 2 * (ramificationIndex K : Int) ∧ M.k = 1 ∧
        ¬HasResidueFieldMoreThanTwoElements (K := K)) ∨
      (b.lemma62Gap = 2 * (ramificationIndex K : Int) - 2 ∧
        (((1 : ℚ) : WithTop ℚ) < b.normalizedAdjacentDefectOrder 0) ∧
        ¬HasResidueFieldMoreThanTwoElements (K := K) ∧ M.k = 2) := by
  have hresidue := M.residue_two_of_final_eq_two_e_add_two hkNe hfinal
  have hkLe := M.k_le_two_of_final_eq_two_e_add_two hfinal
  have hkPos := Nat.pos_of_ne_zero hkNe
  have hkCases : M.k = 1 ∨ M.k = 2 := by omega
  rcases hkCases with hk | hk
  · left
    refine ⟨by omega, hk, hresidue⟩
  · right
    have hdefect :=
      M.normalizedAdjacentDefectOrder_one_lt_of_final_eq_two_e_add_two
        (by omega) hfinal
    exact ⟨by omega, hdefect, hresidue, hk⟩

/-- Exhaustive high-range form of Beli's cases (1), (2), and (5). -/
theorem highRange_cases
    (M : b.Lemma65MinimalityData) (hhigh : b.Lemma65HighRangeAt M.k) :
    M.k = 0 ∨
      (Odd b.lemma62Gap ∧
        b.lemma62Gap + 2 * (M.k : Int) =
          2 * (ramificationIndex K : Int) + 1) ∨
      (b.lemma62Gap = 2 * (ramificationIndex K : Int) ∧ M.k = 1 ∧
        ¬HasResidueFieldMoreThanTwoElements (K := K)) ∨
      (b.Lemma65Exceptional ∧ M.k = 2) := by
  by_cases hkZero : M.k = 0
  · exact Or.inl hkZero
  · rcases M.highRange_k_eq_zero_or_final_eq hhigh with
      hk | hoddFinal | hevenFinal
    · exact (hkZero hk).elim
    · exact Or.inr (Or.inl
        ⟨M.lemma62Gap_odd_of_final_eq_two_e_add_one hoddFinal,
          hoddFinal⟩)
    · rcases M.cases_of_final_eq_two_e_add_two hkZero hevenFinal with
        htwoE | hexceptional
      · exact Or.inr (Or.inr (Or.inl htwoE))
      · exact Or.inr (Or.inr (Or.inr ⟨by
          exact ⟨hexceptional.1, hexceptional.2.1,
            hexceptional.2.2.1⟩, hexceptional.2.2.2⟩))

end Lemma65MinimalityData

namespace Lemma65Setup

variable {b : BONG V q L (n + 3)}

/-- Compatibility wrapper for the original concrete setup API. -/
theorem normalizedAdjacentDefectOrder_one_lt_of_final_eq_two_e_add_two
    (S : b.Lemma65Setup) (hkTwo : 2 ≤ S.k)
    (hfinal : b.lemma62Gap + 2 * (S.k : Int) =
      2 * (ramificationIndex K : Int) + 2) :
    (((1 : ℚ) : WithTop ℚ) < b.normalizedAdjacentDefectOrder 0) :=
  S.toMinimalityData.normalizedAdjacentDefectOrder_one_lt_of_final_eq_two_e_add_two
    hkTwo hfinal

/-- Compatibility wrapper for the original concrete setup API. -/
theorem shiftedFirstParameter_class_ne_negativeQuarter
    (S : b.Lemma65Setup) (j : Nat) :
    unitSquareClass K
        (uniformizerPowerUnit K
          (b.lemma62Gap + 2 * (j : Int)) *
            normalizedUnitPart K (b.adjacentParameter 0 (by simp))) ≠
      unitSquareClass K (negativeQuarterUnit K) :=
  S.toMinimalityData.shiftedFirstParameter_class_ne_negativeQuarter j

/-- Compatibility wrapper for the original concrete setup API. -/
theorem k_le_two_of_final_eq_two_e_add_two
    (S : b.Lemma65Setup)
    (hfinal : b.lemma62Gap + 2 * (S.k : Int) =
      2 * (ramificationIndex K : Int) + 2) :
    S.k ≤ 2 :=
  S.toMinimalityData.k_le_two_of_final_eq_two_e_add_two hfinal

/-- Compatibility wrapper for the original concrete setup API. -/
theorem cases_of_final_eq_two_e_add_two
    (S : b.Lemma65Setup) (hkNe : S.k ≠ 0)
    (hfinal : b.lemma62Gap + 2 * (S.k : Int) =
      2 * (ramificationIndex K : Int) + 2) :
    (b.lemma62Gap = 2 * (ramificationIndex K : Int) ∧ S.k = 1 ∧
        ¬HasResidueFieldMoreThanTwoElements (K := K)) ∨
      (b.lemma62Gap = 2 * (ramificationIndex K : Int) - 2 ∧
        (((1 : ℚ) : WithTop ℚ) < b.normalizedAdjacentDefectOrder 0) ∧
        ¬HasResidueFieldMoreThanTwoElements (K := K) ∧ S.k = 2) :=
  S.toMinimalityData.cases_of_final_eq_two_e_add_two hkNe hfinal

/-- Compatibility wrapper for the original concrete setup API. -/
theorem highRange_cases
    (S : b.Lemma65Setup) (hhigh : b.Lemma65HighRange S) :
    S.k = 0 ∨
      (Odd b.lemma62Gap ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) + 1) ∨
      (b.lemma62Gap = 2 * (ramificationIndex K : Int) ∧ S.k = 1 ∧
        ¬HasResidueFieldMoreThanTwoElements (K := K)) ∨
      (b.Lemma65Exceptional ∧ S.k = 2) :=
  S.toMinimalityData.highRange_cases hhigh

end Lemma65Setup

namespace Lemma65MinimalityData

variable {b : BONG V q L (n + 3)}

/-- In every nonexceptional high-range branch the least shifted tail has a
literal BONG realization.  The odd endpoint stays below the third BONG order
by Property B; the residue-two endpoint has `k=1` and is supplied by Lemma
6.1.  The excluded exceptional branch is precisely the case where the paper
only uses the once-rescaled tail although the least exponent is two. -/
theorem highTailRescaleExists_of_not_exceptional
    (M : b.Lemma65MinimalityData) (hB : b.HasPropertyB)
    (hhigh : b.Lemma65HighRangeAt M.k)
    (hnotExceptional : ¬b.Lemma65Exceptional) :
    Nonempty (b.tail.HeadRescaleWitness M.k) := by
  rcases M.highRange_cases hhigh with
    hkZero | hodd | htwoE | hexceptional
  · exact ⟨b.tailHeadRescaleWitness_of_k_eq_zero M.k hkZero⟩
  · refine ⟨b.tailHeadRescaleWitness_of_order_le_third M.k ?_⟩
    have hgapNonneg : 0 ≤ b.lemma62Gap := by
      have hadmissible :=
        b.adjacentParameter_isBinaryParameterAdmissible 0 (by simp)
      rw [← b.ordUnit_adjacentParameter_zero]
      exact hadmissible.ordUnit_nonneg_of_odd (by
        simpa only [b.ordUnit_adjacentParameter_zero] using hodd.1)
    have hgapUpper : b.lemma62Gap ≤
        2 * (ramificationIndex K : Int) + 1 := by
      have hkNonneg : (0 : Int) ≤ (M.k : Int) := by positivity
      omega
    have htrigger : b.propertyBTrigger (0 : Fin (n + 2)) := by
      unfold propertyBTrigger
      left
      have hsucc : (0 : Fin (n + 2)).succ =
          (1 : Fin (n + 3)) := Fin.ext rfl
      have hcast : (0 : Fin (n + 2)).castSucc =
          (0 : Fin (n + 3)) := Fin.ext rfl
      rw [hsucc, hcast]
      simpa only [lemma62Gap] using And.intro hgapUpper hodd.1
    have hthirdGap : 2 * (ramificationIndex K : Int) + 1 ≤
        b.order 2 - b.order 1 := by
      have hright := (hB.2 (0 : Fin (n + 2)) htrigger).2
      exact hright (2 : Fin (n + 3)) rfl
    unfold lemma62Gap at hodd hgapNonneg
    omega
  · rw [htwoE.2.1]
    refine ⟨b.tailHeadRescaleWitness_one_of_previousGap_le_two_e hB ?_⟩
    unfold lemma62Gap at htwoE
    omega
  · exact (hnotExceptional hexceptional.1).elim

/-- In the finite-defect boundary branch, the shifted second order is still
strictly below the third BONG order.  This is the numerical content needed to
assemble the shifted projected tail, and it depends only on minimality data,
not on a pre-existing tail realization. -/
theorem boundary_tailOrder_lt_third
    (M : b.Lemma65MinimalityData) (hB : b.HasPropertyB)
    (hboundary :
      (quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (M.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int)) :
    b.order 1 + 2 * (M.k : Int) < b.order 2 := by
  let a₀ : Kˣ := b.adjacentParameter 0 (by simp)
  let ε₀ : Kˣ := normalizedUnitPart K a₀
  let d := quadraticDefect K (-ε₀)
  have hdFinite : d ≠ ⊤ := by
    simpa only [d, ε₀, a₀] using hboundary.1
  have hfinalEq : b.lemma62Gap + 2 * (M.k : Int) =
      2 * (ramificationIndex K : Int) - 2 * (d.toNat : Int) := by
    simpa only [d, ε₀, a₀] using hboundary.2
  have hfinalEven : Even (b.lemma62Gap + 2 * (M.k : Int)) := by
    refine ⟨(ramificationIndex K : Int) - (d.toNat : Int), ?_⟩
    omega
  have hbaseEven : Even b.lemma62Gap := by
    rcases hfinalEven with ⟨r, hr⟩
    refine ⟨r - (M.k : Int), ?_⟩
    omega
  have hbaseUpper : b.lemma62Gap ≤
      2 * (ramificationIndex K : Int) := by
    have hkNonneg : (0 : Int) ≤ (M.k : Int) := by positivity
    omega
  have ha₀DefectEq : quadraticDefect K (-a₀) = d := by
    simpa only [d, ε₀] using
      beliParameterDefect_eq_normalizedUnitPart_of_even
        (K := K) a₀ (by
          simpa only [a₀, b.ordUnit_adjacentParameter_zero] using
            hbaseEven)
  have ha₀ParameterDefect : beliParameterDefect K a₀ = d := by
    simpa only [beliParameterDefect] using ha₀DefectEq
  have ha₀ParameterFinite : beliParameterDefect K a₀ ≠ ⊤ := by
    rw [ha₀ParameterDefect]
    exact hdFinite
  have hbaseDefectNonneg :
      0 ≤ b.lemma62Gap + (d.toNat : Int) := by
    have hadmissible :=
      b.adjacentParameter_isBinaryParameterAdmissible 0 (by simp)
    have h := hadmissible.order_add_parameterDefect_nonneg (by
      simpa only [a₀] using ha₀ParameterFinite)
    rw [b.ordUnit_adjacentParameter_zero] at h
    simpa only [a₀, ha₀ParameterDefect] using h
  have hdLeNat : d.toNat ≤ 2 * ramificationIndex K := by
    have hnotSquare : ¬IsSquare (-ε₀) := by
      intro hsquare
      exact hdFinite
        ((quadraticDefect_eq_top_iff_isSquare (K := K) (-ε₀)).2
          hsquare)
    have hbound :=
      quadraticDefect_le_two_mul_e_of_not_isSquare (K := K) hnotSquare
    change d ≤ _ at hbound
    rw [← ENat.coe_toNat hdFinite] at hbound
    exact_mod_cast hbound
  have hcutCast : (b.lemma62DefectCutoff : Int) =
      (ramificationIndex K : Int) - b.lemma62Gap / 2 :=
    b.lemma62DefectCutoff_cast hbaseEven hbaseUpper
  have hdLeCutNat : d.toNat ≤ b.lemma62DefectCutoff := by
    rcases hbaseEven with ⟨r, hr⟩
    omega
  have hdefectLow :
      beliParameterDefect K (b.adjacentParameter 0 (by simp)) ≤
        (b.lemma62DefectCutoff : ℕ∞) := by
    change beliParameterDefect K a₀ ≤ _
    rw [ha₀ParameterDefect, ← ENat.coe_toNat hdFinite]
    exact_mod_cast hdLeCutNat
  have hthirdGap :
      2 * (ramificationIndex K : Int) + 1 ≤
        b.order 2 - b.order 1 :=
    b.thirdGap_ge_of_propertyB_lemma62_low
      hB hbaseEven hbaseUpper hdefectLow
  have hdNonneg : (0 : Int) ≤ (d.toNat : Int) := by positivity
  omega

/-- Every low-range branch has a literal realization of the tail rescaled by
the least exponent.  The boundary branch lies below the third order; the only
remaining possibilities are `k=0` and `k=1`. -/
theorem lowTailRescaleExists
    (M : b.Lemma65MinimalityData) (hB : b.HasPropertyB)
    (hlow : b.Lemma65LowRangeAt M.k) :
    Nonempty (b.tail.HeadRescaleWitness M.k) := by
  rcases M.lowRange_boundary_or_k_le_one hlow with hboundary | hk
  · exact ⟨b.tailHeadRescaleWitness_of_order_le_third M.k
      (le_of_lt (M.boundary_tailOrder_lt_third hB hboundary))⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with hkZero | hkOne
    · exact ⟨b.tailHeadRescaleWitness_of_k_eq_zero M.k hkZero⟩
    · rw [hkOne] at hlow ⊢
      refine ⟨b.tailHeadRescaleWitness_one_of_previousGap_le_two_e hB ?_⟩
      unfold Lemma65LowRangeAt at hlow
      omega

/-- Outside Beli's exceptional residue-two branch, the least admissible
exponent always has a literal shifted-tail BONG realization. -/
theorem tailRescaleExists_of_not_exceptional
    (M : b.Lemma65MinimalityData) (hB : b.HasPropertyB)
    (hnotExceptional : ¬b.Lemma65Exceptional) :
    Nonempty (b.tail.HeadRescaleWitness M.k) := by
  by_cases hlow : b.Lemma65LowRangeAt M.k
  · exact M.lowTailRescaleExists hB hlow
  · apply M.highTailRescaleExists_of_not_exceptional hB
      (hnotExceptional := hnotExceptional)
    unfold Lemma65LowRangeAt at hlow
    unfold Lemma65HighRangeAt
    omega

end Lemma65MinimalityData

/-- Canonical concrete setup for every nonexceptional nonhyperbolic prefix.
The exceptional branch is intentionally excluded: there the paper uses the
once-rescaled tail while the least admissible exponent is two. -/
noncomputable def lemma65Setup_of_not_exceptional
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (hnotHyperbolic : ¬b.FirstBinaryIsHyperbolic)
    (hnotExceptional : ¬b.Lemma65Exceptional) :
    b.Lemma65Setup := by
  classical
  let M := b.lemma65MinimalityData hnotHyperbolic
  let hw := M.tailRescaleExists_of_not_exceptional hB hnotExceptional
  exact {
    k := M.k
    tailRescale := Classical.choice hw
    admissible := M.admissible
    least := M.least
    firstBinary_not_hyperbolic := M.firstBinary_not_hyperbolic
  }

namespace Lemma65Setup

variable {b : BONG V q L (n + 3)}

/-- In the exceptional situation, the defect of the normalized first binary
parameter is either infinite or is a finite integer at least two. -/
theorem exceptional_normalizedUnitPart_defect_cases
    (S : b.Lemma65Setup) (hexceptional : b.Lemma65Exceptional) :
    let d := quadraticDefect K
      (-(normalizedUnitPart K (b.adjacentParameter 0 (by simp))))
    d = ⊤ ∨ (d ≠ ⊤ ∧ 2 ≤ d.toNat) := by
  let a₀ : Kˣ := b.adjacentParameter 0 (by simp)
  let ε : Kˣ := normalizedUnitPart K a₀
  let d := quadraticDefect K (-ε)
  have hgapEven : Even b.lemma62Gap := by
    refine ⟨(ramificationIndex K : Int) - 1, ?_⟩
    rw [hexceptional.1]
    ring
  have hεDefectEq : d = quadraticDefect K
      (b.normalizedAdjacentProduct (0 : Fin (n + 2))) := by
    have hnormalize :=
      beliParameterDefect_eq_normalizedUnitPart_of_even
        (K := K) a₀ (by
          simpa only [a₀, b.ordUnit_adjacentParameter_zero] using hgapEven)
    have hadjacent :=
      b.quadraticDefect_negative_adjacentParameter_eq_normalizedProduct_of_even
        (0 : Fin (n + 2)) (by
          have hsucc : (0 : Fin (n + 2)).succ =
              (1 : Fin (n + 3)) := Fin.ext rfl
          have hcast : (0 : Fin (n + 2)).castSucc =
              (0 : Fin (n + 3)) := Fin.ext rfl
          rw [hsucc, hcast]
          simpa only [lemma62Gap] using hgapEven)
    have hadjacent' : quadraticDefect K (-a₀) =
        quadraticDefect K
          (b.normalizedAdjacentProduct (0 : Fin (n + 2))) := by
      simpa [a₀] using hadjacent
    simpa only [d, ε] using hnormalize.symm.trans hadjacent'
  have hdOrder : (((1 : ℚ) : WithTop ℚ) <
      WithTop.map (fun m : Nat ↦ (m : ℚ)) d) := by
    have h := hexceptional.2.1
    unfold normalizedAdjacentDefectOrder at h
    rw [hεDefectEq]
    exact h
  change d = ⊤ ∨ (d ≠ ⊤ ∧ 2 ≤ d.toNat)
  cases hd : d with
  | top => exact Or.inl rfl
  | coe defect =>
      right
      have htwo : 2 ≤ defect := by
        rw [hd] at hdOrder
        change ((1 : ℚ) : WithTop ℚ) <
          ((defect : ℚ) : WithTop ℚ) at hdOrder
        norm_cast at hdOrder
      refine ⟨by simp, ?_⟩
      simpa using htwo

/-- The exceptional hypotheses determine the least shift exactly: orders
`2e-2` and `2e` fail Lemma 3.17, while the two-step order `2e+2` satisfies
its high alternative. -/
theorem k_eq_two_of_exceptional
    (S : b.Lemma65Setup) (hexceptional : b.Lemma65Exceptional) :
    S.k = 2 := by
  have hcandidateCases : BeliLemma317ParameterCases (K := K)
      (b.lemma62Gap + 2 * ((2 : Nat) : Int))
      (normalizedUnitPart K (b.adjacentParameter 0 (by simp))) := by
    simp only [BeliLemma317ParameterCases]
    left
    rw [hexceptional.1]
    norm_num
    omega
  have hcandidate : b.HeadSecondRescaleAdmissible 2 :=
    b.headSecondRescaleAdmissible_of_parameterCases 2 hcandidateCases
  have hkLe : S.k ≤ 2 := S.least 2 hcandidate
  have hdefectCases := S.exceptional_normalizedUnitPart_defect_cases
    hexceptional
  let d := quadraticDefect K
    (-(normalizedUnitPart K (b.adjacentParameter 0 (by simp))))
  change d = ⊤ ∨ (d ≠ ⊤ ∧ 2 ≤ d.toNat) at hdefectCases
  have hresidue := hexceptional.2.2
  have hePos : (0 : Int) < (ramificationIndex K : Int) := by
    exact_mod_cast ramificationIndex_pos K
  have hexcludeShort : ∀ k : Nat, k = 0 ∨ k = 1 → S.k ≠ k := by
    intro k hkShort hkEq
    have hcases := S.finalParameterCases
    have hR : b.lemma62Gap + 2 * (S.k : Int) =
        if k = 0 then 2 * (ramificationIndex K : Int) - 2
        else 2 * (ramificationIndex K : Int) := by
      rw [hkEq, hexceptional.1]
      rcases hkShort with rfl | rfl <;> norm_num
    simp only [BeliLemma317ParameterCases] at hcases
    rcases hcases with hhigh | hboundary | hinterior | hendpoint
    · rcases hkShort with rfl | rfl <;> simp at hR <;> omega
    · rcases hdefectCases with hdTop | hdFinite
      · have hdNe : d ≠ ⊤ := by
          simpa only [d] using hboundary.1
        exact hdNe hdTop
      · have hboundaryEq := hboundary.2
        change b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) - 2 * (d.toNat : Int)
          at hboundaryEq
        rcases hkShort with rfl | rfl <;> simp at hR <;> omega
    · rcases hkShort with hk0 | hk1
      · have hhalfOdd : Odd
            ((b.lemma62Gap + 2 * (S.k : Int)) / 2 +
              (ramificationIndex K : Int)) := by
          have hrewrite : 2 * (ramificationIndex K : Int) - 2 =
              2 * ((ramificationIndex K : Int) - 1) := by ring
          have hhalf : (b.lemma62Gap + 2 * (S.k : Int)) / 2 =
              (ramificationIndex K : Int) - 1 := by
            simp only [hk0, if_pos] at hR
            rw [hR, hrewrite, Int.mul_ediv_cancel_left]
            norm_num
          refine ⟨(ramificationIndex K : Int) - 1, ?_⟩
          rw [hhalf]
          ring
        exact (Int.not_even_iff_odd.mpr hhalfOdd
          hinterior.2.2.2.1).elim
      · have hREq : b.lemma62Gap + 2 * (S.k : Int) =
            2 * (ramificationIndex K : Int) := by
          simp only [hk1, if_false (by omega)] at hR
          exact hR
        omega
    · exact hresidue hendpoint.2
  have hkCases : S.k = 0 ∨ S.k = 1 ∨ S.k = 2 := by omega
  rcases hkCases with hk | hk | hk
  · exact (hexcludeShort 0 (Or.inl rfl) hk).elim
  · exact (hexcludeShort 1 (Or.inr rfl) hk).elim
  · exact hk

/-- Unconditional proof of Beli (2003), Lemma 6.5(i), including the unique
exceptional residue-two branch. -/
theorem projection_alternative_proved
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head) :
    (¬b.Lemma65Exceptional → S.projection x ∈ S.tailRescale.lattice) ∧
      (b.Lemma65Exceptional →
        S.k = 2 ∧ Nonempty (Lemma65ExceptionalProjectionWitness b x)) := by
  constructor
  · intro hnotExceptional
    by_cases hlow : b.Lemma65LowRange S
    · exact S.projection_mem_tailRescale_of_low hB x hx heq hlow
    · have hhigh : b.Lemma65HighRange S := by
        change ¬(b.order 1 + 2 * (S.k : Int) - b.order 0 ≤
          2 * (ramificationIndex K : Int)) at hlow
        change 2 * (ramificationIndex K : Int) + 1 ≤
          b.order 1 + 2 * (S.k : Int) - b.order 0
        omega
      rcases S.highRange_cases hhigh with
        hkZero | hodd | htwoE | hexceptional
      · exact S.projection_mem_tailRescale_of_k_eq_zero x hx hkZero
      · exact S.projection_mem_tailRescale_of_high_odd
          hB x hx heq hodd.1 hodd.2
      · exact S.projection_mem_tailRescale_of_gap_eq_two_e_residue_two
          x hx heq htwoE.1 htwoE.2.1 htwoE.2.2
      · exact (hnotExceptional hexceptional.1).elim
  · intro hexceptional
    have hk := S.k_eq_two_of_exceptional hexceptional
    refine ⟨hk, ⟨S.exceptionalProjectionWitness hB x hx heq
      hexceptional.1 hexceptional.2.1 hexceptional.2.2 hk⟩⟩

/-- Algebraic form of the equal-norm difference identity. -/
private theorem quadratic_head_sub_eq_two_mul_one_sub_mul_of_bilin_eq
    (x : V) (a : K)
    (heq : q.quadratic x = q.quadratic b.head)
    (hpair : q.bilin b.head x = a * q.quadratic b.head) :
    q.quadratic (b.head - x) =
      2 * (1 - a) * q.quadratic b.head := by
  rw [sub_eq_add_neg, q.quadratic_add, q.quadratic_neg,
    LinearMap.BilinForm.neg_right, heq, hpair]
  ring

/-- Algebraic form of the corresponding equal-norm sum identity. -/
private theorem quadratic_head_add_eq_two_mul_one_add_mul_of_bilin_eq
    (x : V) (a : K)
    (heq : q.quadratic x = q.quadratic b.head)
    (hpair : q.bilin b.head x = a * q.quadratic b.head) :
    q.quadratic (b.head + x) =
      2 * (1 + a) * q.quadratic b.head := by
  rw [q.quadratic_add, heq, hpair]
  ring

/-- The quadratic value of the difference from the head, in normalized
projection coordinates. -/
theorem quadratic_head_sub_eq_two_mul_one_sub_mul_intrinsic
    (b : BONG V q L (n + 3)) (x : V)
    (heq : q.quadratic x = q.quadratic b.head) :
    q.quadratic (b.head - x) =
      2 * (1 - q.bilin b.head x / q.quadratic b.head) *
        q.quadratic b.head := by
  apply quadratic_head_sub_eq_two_mul_one_sub_mul_of_bilin_eq x
    (q.bilin b.head x / q.quadratic b.head) heq
  exact (div_mul_cancel₀ _ b.head_isAnisotropic).symm

/-- Compatibility wrapper for the concrete-setup API. -/
theorem quadratic_head_sub_eq_two_mul_one_sub_mul
    (S : b.Lemma65Setup) (x : V)
    (heq : q.quadratic x = q.quadratic b.head) :
    q.quadratic (b.head - x) =
      2 * (1 - q.bilin b.head x / q.quadratic b.head) *
        q.quadratic b.head :=
  quadratic_head_sub_eq_two_mul_one_sub_mul_intrinsic b x heq

/-- The corresponding formula for the sum with the head. -/
theorem quadratic_head_add_eq_two_mul_one_add_mul_intrinsic
    (b : BONG V q L (n + 3)) (x : V)
    (heq : q.quadratic x = q.quadratic b.head) :
    q.quadratic (b.head + x) =
      2 * (1 + q.bilin b.head x / q.quadratic b.head) *
        q.quadratic b.head := by
  apply quadratic_head_add_eq_two_mul_one_add_mul_of_bilin_eq x
    (q.bilin b.head x / q.quadratic b.head) heq
  exact (div_mul_cancel₀ _ b.head_isAnisotropic).symm

/-- Compatibility wrapper for the concrete-setup API. -/
theorem quadratic_head_add_eq_two_mul_one_add_mul
    (S : b.Lemma65Setup) (x : V)
    (heq : q.quadratic x = q.quadratic b.head) :
    q.quadratic (b.head + x) =
      2 * (1 + q.bilin b.head x / q.quadratic b.head) *
        q.quadratic b.head :=
  quadratic_head_add_eq_two_mul_one_add_mul_intrinsic b x heq

/-- For a norm-generating projection, the order of the normalized factor
`1-a^2` is the rescaled binary gap. -/
theorem ord_one_sub_sq_of_projection_isNormGenerator
    (S : b.Lemma65Setup) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x)) :
    ord K (1 - (q.bilin b.head x / q.quadratic b.head) ^ 2) =
      ((b.order 1 + 2 * (S.k : Int) - b.order 0 : Int) : WithTop Int) := by
  have hprojectionOrder :=
    S.ord_quadratic_projection_of_isNormGenerator x hgenerator
  have hprojectionEq := S.quadratic_projection_eq_one_sub_sq_mul x heq
  have hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0 := by
    intro hzero
    rw [hprojectionEq, hzero, zero_mul, ord_zero] at hprojectionOrder
    exact WithTop.top_ne_coe hprojectionOrder
  let factor : Kˣ := Units.mk0
    (1 - (q.bilin b.head x / q.quadratic b.head) ^ 2) hfactorNe
  have hfactorOrder :
      ord K (1 - (q.bilin b.head x / q.quadratic b.head) ^ 2) =
        (ordUnit K factor : WithTop Int) := by
    simpa only [factor, Units.val_mk0] using (coe_ordUnit K factor).symm
  have hheadOrder : ord K (q.quadratic b.head) =
      (b.order 0 : WithTop Int) := by
    rw [← b.value_zero_eq_quadratic_head, ← b.coe_order]
  rw [hprojectionEq, ord_mul, hfactorOrder,
    hheadOrder] at hprojectionOrder
  rw [hfactorOrder]
  apply WithTop.coe_injective
  norm_cast at hprojectionOrder ⊢
  omega

/-- In the low range a norm-generating projection makes both the difference
and the sum with the head have order `s+e`. -/
theorem ord_quadratic_head_sub_and_add_of_low_isNormGenerator
    (S : b.Lemma65Setup) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (hlow : b.Lemma65LowRange S)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x)) :
    ord K (q.quadratic (b.head - x)) =
        ((S.reflectionScaleOrder + ramificationIndex K : Int) : WithTop Int) ∧
      ord K (q.quadratic (b.head + x)) =
        ((S.reflectionScaleOrder + ramificationIndex K : Int) : WithTop Int) := by
  let gap : Int := b.order 1 + 2 * (S.k : Int) - b.order 0
  let a : K := q.bilin b.head x / q.quadratic b.head
  have heven : Even gap := by
    simpa only [gap] using S.lowRange_gap_even hlow
  have hupper : gap ≤ 2 * (ramificationIndex K : Int) := by
    simpa only [Lemma65LowRange, gap] using hlow
  have hfactorOrder : ord K (1 - a ^ 2) = (gap : WithTop Int) := by
    simpa only [a, gap] using
      S.ord_one_sub_sq_of_projection_isNormGenerator x heq hgenerator
  have hlinear :=
    ord_one_sub_and_add_eq_half_of_order_one_sub_sq
      a gap heven hupper hfactorOrder
  have hheadOrder : ord K (q.quadratic b.head) =
      (b.order 0 : WithTop Int) := by
    rw [← b.value_zero_eq_quadratic_head, ← b.coe_order]
  have hsubValue := S.quadratic_head_sub_eq_two_mul_one_sub_mul x heq
  have haddValue := S.quadratic_head_add_eq_two_mul_one_add_mul x heq
  constructor
  · rw [hsubValue, ord_mul, ord_mul, ← ramificationIndex_spec,
      hlinear.1, hheadOrder]
    norm_cast
    simp only [reflectionScaleOrder, gap]
    omega
  · rw [haddValue, ord_mul, ord_mul, ← ramificationIndex_spec,
      hlinear.2, hheadOrder]
    norm_cast
    simp only [reflectionScaleOrder, gap]
    omega

/-- In the low range, a projected tail vector which is not a norm generator
forces at least one of the two equal-norm sums with the head to lie strictly
deeper than the critical order. -/
theorem ord_quadratic_head_sub_or_add_gt_of_low_not_isNormGenerator
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hlow : b.Lemma65LowRange S)
    (hnotGenerator : ¬Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x)) :
    (((S.reflectionScaleOrder + ramificationIndex K : Int) :
        WithTop Int) < ord K (q.quadratic (b.head - x))) ∨
      (((S.reflectionScaleOrder + ramificationIndex K : Int) :
        WithTop Int) < ord K (q.quadratic (b.head + x))) := by
  let gap : Int := b.order 1 + 2 * (S.k : Int) - b.order 0
  let a : K := q.bilin b.head x / q.quadratic b.head
  have heven : Even gap := by
    simpa only [gap] using S.lowRange_gap_even hlow
  have hupper : gap ≤ 2 * (ramificationIndex K : Int) := by
    simpa only [Lemma65LowRange, gap] using hlow
  have hprojectionMem : S.projection x ∈ S.tailRescale.lattice :=
    S.projection_mem_tailRescale_of_low hB x hx heq hlow
  have hprojectionDeep :=
    (S.tailRescale.bong.mem_and_not_isNormGenerator_iff_ord_ge_head_add_one
      (S.projection x)).1 ⟨hprojectionMem, hnotGenerator⟩ |>.2
  have htailZero : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
    rw [b.order_tail]
    congr 1
  rw [S.tailRescale.order_zero_eq, htailZero] at hprojectionDeep
  have hprojectionEq :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (S.projection x) =
        (1 - a ^ 2) * q.quadratic b.head := by
    simpa only [a] using S.quadratic_projection_eq_one_sub_sq_mul x heq
  have hheadOrder : ord K (q.quadratic b.head) =
      (b.order 0 : WithTop Int) := by
    rw [← b.value_zero_eq_quadratic_head, ← b.coe_order]
  have hfactorLower : ((gap + 1 : Int) : WithTop Int) ≤
      ord K (1 - a ^ 2) := by
    rw [hprojectionEq, ord_mul, hheadOrder] at hprojectionDeep
    by_cases hfactorZero : 1 - a ^ 2 = 0
    · rw [hfactorZero, ord_zero]
      exact le_top
    · let factor : Kˣ := Units.mk0 (1 - a ^ 2) hfactorZero
      have hfactorOrder : ord K (1 - a ^ 2) =
          (ordUnit K factor : WithTop Int) := by
        simpa only [factor, Units.val_mk0] using
          (coe_ordUnit K factor).symm
      rw [hfactorOrder] at hprojectionDeep ⊢
      norm_cast at hprojectionDeep ⊢
      simp only [gap]
      omega
  have hlinear :=
    ord_one_sub_or_add_gt_half_of_order_one_sub_sq_gt
      a gap heven hupper hfactorLower
  have hsubValue : q.quadratic (b.head - x) =
      2 * (1 - a) * q.quadratic b.head := by
    simpa only [a] using
      S.quadratic_head_sub_eq_two_mul_one_sub_mul x heq
  have haddValue : q.quadratic (b.head + x) =
      2 * (1 + a) * q.quadratic b.head := by
    simpa only [a] using
      S.quadratic_head_add_eq_two_mul_one_add_mul x heq
  have hcriticalCast :
      ((S.reflectionScaleOrder + ramificationIndex K : Int) :
          WithTop Int) =
        (((ramificationIndex K : Int) + b.order 0 : Int) : WithTop Int) +
          ((gap / 2 : Int) : WithTop Int) := by
    norm_cast
    simp only [reflectionScaleOrder, gap]
    ring
  have hbaseCast :
      (((ramificationIndex K : Int) + b.order 0 : Int) : WithTop Int) =
        ((ramificationIndex K : Int) : WithTop Int) +
          (b.order 0 : WithTop Int) := by
    norm_cast
  rcases hlinear with hminus | hplus
  · left
    rw [hsubValue, ord_mul, ord_mul, ← ramificationIndex_spec,
      hheadOrder]
    have hadd :
        (((ramificationIndex K : Int) + b.order 0 : Int) : WithTop Int) +
            ((gap / 2 : Int) : WithTop Int) <
          (((ramificationIndex K : Int) + b.order 0 : Int) : WithTop Int) +
            ord K (1 - a) :=
      (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).2 hminus.1
    calc
      ((S.reflectionScaleOrder + ramificationIndex K : Int) :
          WithTop Int) = _ := hcriticalCast
      _ < _ := hadd
      _ = _ := by
        rw [hbaseCast]
        ac_rfl
  · right
    rw [haddValue, ord_mul, ord_mul, ← ramificationIndex_spec,
      hheadOrder]
    have hadd :
        (((ramificationIndex K : Int) + b.order 0 : Int) : WithTop Int) +
            ((gap / 2 : Int) : WithTop Int) <
          (((ramificationIndex K : Int) + b.order 0 : Int) : WithTop Int) +
            ord K (1 + a) :=
      (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).2 hplus.2
    calc
      ((S.reflectionScaleOrder + ramificationIndex K : Int) :
          WithTop Int) = _ := hcriticalCast
      _ < _ := hadd
      _ = _ := by
        rw [hbaseCast]
        ac_rfl

/-- Claim (a) of Beli's proof in the short-shift branch when the first two
orders form a binary initial Jordan component.  Lemma 6.1 gives the concrete
twice-rescaled lattice; Corollary 4.4(iv) computes its scale, and cancelling
the common factor `πᵏ` gives the required intrinsic scale-truncation
membership in the original lattice. -/
theorem mem_scaleTruncation_of_short_of_second_order_le_first
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hlow : b.Lemma65LowRange S) (hk : S.k ≤ 1)
    (v : V) (hv : v ∈ S.intermediateLattice)
    (horder : ord K (q.quadratic v) =
      ((S.reflectionScaleOrder + ramificationIndex K : Int) :
        WithTop Int))
    (hsecond : b.order 1 ≤ b.order 0) :
    v ∈ Lattice.scaleTruncation q L S.reflectionScaleOrder := by
  let W : S.intermediateBONG.HeadDepthWitness S.k :=
    Classical.choice (S.exists_intermediateHeadDepth_of_k_le_one hB hk)
  have hvW : v ∈ W.lattice :=
    S.mem_intermediateHeadDepth_of_critical_order hlow hk W v hv horder
  have heven := S.lowRange_gap_even hlow
  have hWzero : W.bong.order 0 =
      b.order 0 + 2 * (S.k : Int) := by
    rw [W.order_zero_eq, S.intermediateBONG_order_zero]
  have hWone : W.bong.order 1 =
      b.order 1 + 2 * (S.k : Int) := by
    have h := W.order_succ_eq (0 : Fin (n + 2))
    change W.bong.order 1 = S.intermediateBONG.order 1 at h
    rw [h, S.intermediateBONG_order_one]
  have hscaleDoubled :=
    beliCorollary44_iv_unconditional W.bong W.good
  have hbound :
      2 * (S.reflectionScaleOrder + (S.k : Int)) ≤
        min (2 * W.bong.order 0)
          (W.bong.order 0 + W.bong.order 1) := by
    rw [hWzero, hWone,
      min_eq_right (by omega :
        b.order 0 + 2 * (S.k : Int) +
            (b.order 1 + 2 * (S.k : Int)) ≤
          2 * (b.order 0 + 2 * (S.k : Int)))]
    have hreflection := S.two_mul_reflectionScaleOrder heven
    omega
  have hscale : Lattice.scaleIdeal q W.lattice ≤
      Lattice.powerIdeal (K := K)
        (S.reflectionScaleOrder + (S.k : Int)) :=
    scaleIdeal_le_powerIdeal_of_hasDoubledScaleOrder
      hscaleDoubled hbound
  apply Lattice.mem_scaleTruncation_of_pairing_mem_powerIdeal
    ((S.mem_intermediateLattice_iff v).1 hv).1
  intro y hy
  have hyW := S.uniformizerPower_smul_mem_intermediateHeadDepth W y hy
  have hpairScaled :
      q.bilin v
          (((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K) • y) ∈
        Lattice.powerIdeal (K := K)
          (S.reflectionScaleOrder + (S.k : Int)) :=
    hscale (Lattice.bilin_mem_scaleIdeal_of_mem q W.lattice hvW hyW)
  rw [LinearMap.BilinForm.smul_right] at hpairScaled
  exact Lattice.mem_powerIdeal_of_uniformizerPower_mul_mem
    S.k S.reflectionScaleOrder (q.bilin v y) hpairScaled

/-- Core of Claim (a) when the first Jordan component is unary.  It isolates
the two numerical facts shared by Beli's cases (3) and (4): the projected
tail begins no deeper than the critical norm, and its rescaled scale is at
least `s+k`. -/
theorem mem_scaleTruncation_of_first_lt_second_of_tail_scale
    (S : b.Lemma65Setup) (hgood : b.IsGood)
    (heven : Even
      (b.order 1 + 2 * (S.k : Int) - b.order 0))
    (hcriticalLower :
      b.order 1 + 2 * (S.k : Int) ≤
        S.reflectionScaleOrder + ramificationIndex K)
    (htailScale :
      Lattice.scaleIdeal
          (q.orthogonalSpace b.head b.head_isAnisotropic)
          S.tailRescale.lattice ≤
        Lattice.powerIdeal (K := K)
          (S.reflectionScaleOrder + (S.k : Int)))
    (v : V) (hv : v ∈ S.intermediateLattice)
    (horder : ord K (q.quadratic v) =
      ((S.reflectionScaleOrder + ramificationIndex K : Int) :
        WithTop Int))
    (hfirst : b.order 0 < b.order 1) :
    v ∈ Lattice.scaleTruncation q L S.reflectionScaleOrder := by
  rcases b.beliCorollary44_i_unconditional hgood
      (0 : Fin (n + 3)) (by simp) (le_of_lt hfirst) with ⟨T⟩
  let f := T.toProductLatticeIsometry
  let z := f.toLinearEquiv.symm v
  have hvL : v ∈ L := ((S.mem_intermediateLattice_iff v).1 hv).1
  have hzProduct : z ∈
      Lattice.product T.left.lattice T.right.lattice := by
    exact (f.symm.map_mem v).1 hvL
  have hzMem := Lattice.mem_product_iff.mp hzProduct
  have hvEq : (z.1 : V) + (z.2 : V) = v := by
    change f.toLinearEquiv z = v
    exact f.toLinearEquiv.apply_symm_apply v
  let tailOrder : Int := b.order 1 + 2 * (S.k : Int)
  have hreflection := S.two_mul_reflectionScaleOrder heven
  have hcriticalLower' :
      tailOrder ≤ S.reflectionScaleOrder + ramificationIndex K := by
    simpa only [tailOrder] using hcriticalLower
  have hvQuadratic : q.quadratic v ∈
      Lattice.powerIdeal (K := K) tailOrder := by
    rw [Lattice.mem_powerIdeal_iff, horder]
    exact_mod_cast hcriticalLower'
  have hprojectionMem : S.projection v ∈ S.tailRescale.lattice :=
    ((S.mem_intermediateLattice_iff v).1 hv).2
  have hprojectionQuadratic :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (S.projection v) ∈
        Lattice.powerIdeal (K := K) tailOrder := by
    have hnorm := Lattice.quadratic_mem_normIdeal_of_mem
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice hprojectionMem
    rw [S.tailRescale.bong.normIdeal_eq_powerIdeal_order_zero,
      S.tailRescale.order_zero_eq] at hnorm
    have htailZero : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
      rw [b.order_tail]
      congr 1
    rw [htailZero] at hnorm
    simpa only [tailOrder] using hnorm
  have hprojectionEq : (S.projection v : V) = (z.2 : V) := by
    change (q.projectionToOrthogonal b.head b.head_isAnisotropic v : V) =
      ((T.toProductLatticeIsometry.toLinearEquiv.symm v).2 : V)
    exact T.coe_projection_eq_rightCoordinate_of_cut_one v
  have hzRightQuadratic :
      (q.restrict T.right.carrier T.right.nondegenerate).quadratic z.2 ∈
        Lattice.powerIdeal (K := K) tailOrder := by
    change q.quadratic (z.2 : V) ∈
      Lattice.powerIdeal (K := K) tailOrder
    rw [← hprojectionEq]
    exact hprojectionQuadratic
  have hzLeftQuadratic :
      (q.restrict T.left.carrier T.left.nondegenerate).quadratic z.1 ∈
        Lattice.powerIdeal (K := K) tailOrder := by
    change q.quadratic (z.1 : V) ∈
      Lattice.powerIdeal (K := K) tailOrder
    have horth : q.bilin (z.1 : V) (z.2 : V) = 0 :=
      T.left_right_orthogonal z.1 z.2
    have hquadraticEq : q.quadratic (z.1 : V) =
        q.quadratic v - q.quadratic (z.2 : V) := by
      rw [← hvEq, q.quadratic_add, horth]
      ring
    rw [hquadraticEq]
    exact (Lattice.powerIdeal (K := K) tailOrder).sub_mem
      hvQuadratic (by
        change q.quadratic (z.2 : V) ∈
          Lattice.powerIdeal (K := K) tailOrder at hzRightQuadratic
        exact hzRightQuadratic)
  have hleftFinrank : finrank K T.left.carrier = 1 := by
    have h := T.left.bong.length_eq_finrank
    change 1 = finrank K T.left.carrier at h
    exact h.symm
  have hleftOrder : T.left.bong.order 0 = b.order 0 := by
    simpa [SegmentWitness.sourceIndex] using
      T.left.order_eq (0 : Fin 1)
  have hleftNorm :
      Lattice.normIdeal
          (q.restrict T.left.carrier T.left.nondegenerate)
          T.left.lattice =
        Lattice.powerIdeal (K := K) (b.order 0) := by
    rw [T.left.bong.normIdeal_eq_powerIdeal_order_zero, hleftOrder]
  have hsum :
      2 * S.reflectionScaleOrder ≤ tailOrder + b.order 0 := by
    simp only [tailOrder]
    omega
  apply Lattice.mem_scaleTruncation_of_pairing_mem_powerIdeal hvL
  intro y hy
  let w := f.toLinearEquiv.symm y
  have hwProduct : w ∈
      Lattice.product T.left.lattice T.right.lattice := by
    exact (f.symm.map_mem y).1 hy
  have hwMem := Lattice.mem_product_iff.mp hwProduct
  have hyEq : (w.1 : V) + (w.2 : V) = y := by
    change f.toLinearEquiv w = y
    exact f.toLinearEquiv.apply_symm_apply y
  have hwLeftQuadratic :
      (q.restrict T.left.carrier T.left.nondegenerate).quadratic w.1 ∈
        Lattice.powerIdeal (K := K) (b.order 0) := by
    have hnorm := Lattice.quadratic_mem_normIdeal_of_mem
      (q.restrict T.left.carrier T.left.nondegenerate)
      T.left.lattice hwMem.1
    rwa [hleftNorm] at hnorm
  have hpairLeft : q.bilin (z.1 : V) (w.1 : V) ∈
      Lattice.powerIdeal (K := K) S.reflectionScaleOrder := by
    exact BONG.bilin_mem_powerIdeal_of_finrank_eq_one_of_sum
      (q.restrict T.left.carrier T.left.nondegenerate)
      hleftFinrank S.reflectionScaleOrder tailOrder (b.order 0)
      z.1 w.1 hzLeftQuadratic hwLeftQuadratic hsum
  have hwRightL : (w.2 : V) ∈ L := by
    have hpair : (0, w.2) ∈
        Lattice.product T.left.lattice T.right.lattice :=
      Lattice.mem_product_iff.mpr ⟨T.left.lattice.zero_mem, hwMem.2⟩
    have hmap := (f.map_mem (0, w.2)).1 hpair
    change (0 : V) + (w.2 : V) ∈ L at hmap
    simpa using hmap
  have hprojectionRight :
      (S.projection (w.2 : V) : V) = (w.2 : V) := by
    exact q.orthogonalProjection_eq_self
      (T.right_mem_vectorOrthogonal_head_of_cut_one w.2)
  have hwProjectionTail : S.projection (w.2 : V) ∈
      L.projectedLattice q b.head b.head_isAnisotropic :=
    S.projection_mem_tail (w.2 : V) hwRightL
  have hwProjectionScaled :=
    S.tailRescale.uniformizerPower_smul_mem
      (S.projection (w.2 : V)) hwProjectionTail
  have hpairRightScaled :
      (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
          (S.projection v)
          (((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K) •
            S.projection (w.2 : V)) ∈
        Lattice.powerIdeal (K := K)
          (S.reflectionScaleOrder + (S.k : Int)) :=
    htailScale (Lattice.bilin_mem_scaleIdeal_of_mem
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice hprojectionMem hwProjectionScaled)
  rw [LinearMap.BilinForm.smul_right] at hpairRightScaled
  have hpairRightProjection :=
    Lattice.mem_powerIdeal_of_uniformizerPower_mul_mem
      S.k S.reflectionScaleOrder
      ((q.orthogonalSpace b.head b.head_isAnisotropic).bilin
        (S.projection v) (S.projection (w.2 : V)))
      hpairRightScaled
  have hpairRight : q.bilin (z.2 : V) (w.2 : V) ∈
      Lattice.powerIdeal (K := K) S.reflectionScaleOrder := by
    change q.bilin (S.projection v : V)
        (S.projection (w.2 : V) : V) ∈
      Lattice.powerIdeal (K := K) S.reflectionScaleOrder at hpairRightProjection
    rw [hprojectionEq, hprojectionRight] at hpairRightProjection
    exact hpairRightProjection
  rw [← hvEq, ← hyEq, LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.add_right,
    T.left_right_orthogonal z.1 w.2,
    T.right_left_orthogonal z.2 w.1]
  simp only [add_zero, zero_add]
  exact (Lattice.powerIdeal (K := K) S.reflectionScaleOrder).add_mem
    hpairLeft hpairRight

/-- Claim (a) in Beli's short-shift case (4) when the first Jordan
component is unary. -/
theorem mem_scaleTruncation_of_short_of_first_lt_second
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hlow : b.Lemma65LowRange S) (hk : S.k ≤ 1)
    (v : V) (hv : v ∈ S.intermediateLattice)
    (horder : ord K (q.quadratic v) =
      ((S.reflectionScaleOrder + ramificationIndex K : Int) :
        WithTop Int))
    (hfirst : b.order 0 < b.order 1) :
    v ∈ Lattice.scaleTruncation q L S.reflectionScaleOrder := by
  have heven := S.lowRange_gap_even hlow
  have hreflection := S.two_mul_reflectionScaleOrder heven
  have hcriticalLower :
      b.order 1 + 2 * (S.k : Int) ≤
        S.reflectionScaleOrder + ramificationIndex K := by
    simp only [Lemma65LowRange] at hlow
    omega
  have htailScale :=
    S.tailRescale_scaleIdeal_le_powerIdeal_of_short_of_first_lt_second
      hB hlow hk hfirst
  exact S.mem_scaleTruncation_of_first_lt_second_of_tail_scale
    hB.isGood heven hcriticalLower htailScale v hv horder hfirst

/-- Claim (a) in Beli's case (4), uniformly covering both possible first
Jordan components. -/
theorem mem_scaleTruncation_of_short
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hlow : b.Lemma65LowRange S) (hk : S.k ≤ 1)
    (v : V) (hv : v ∈ S.intermediateLattice)
    (horder : ord K (q.quadratic v) =
      ((S.reflectionScaleOrder + ramificationIndex K : Int) :
        WithTop Int)) :
    v ∈ Lattice.scaleTruncation q L S.reflectionScaleOrder := by
  by_cases hfirst : b.order 0 < b.order 1
  · exact S.mem_scaleTruncation_of_short_of_first_lt_second
      hB hlow hk v hv horder hfirst
  · exact S.mem_scaleTruncation_of_short_of_second_order_le_first
      hB hlow hk v hv horder (by omega)

/-- Claim (a) in the finite-defect boundary case when the first Jordan
component is unary.  The original lattice is decomposed successively as
`Ox₁ ⊥ Ox₂ ⊥ K`; the rescaled-tail carrier theorem controls the
`x₂` coordinate, while `2 sK ⊆ nK` controls the deep complement. -/
theorem mem_scaleTruncation_of_boundary_of_first_lt_second
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hboundary :
      (quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int))
    (v : V) (hv : v ∈ S.intermediateLattice)
    (horder : ord K (q.quadratic v) =
      ((S.reflectionScaleOrder + ramificationIndex K : Int) :
        WithTop Int))
    (hfirst : b.order 0 < b.order 1) :
    v ∈ Lattice.scaleTruncation q L S.reflectionScaleOrder := by
  let D := S.boundaryOrderData hB hboundary
  rcases b.beliCorollary44_i_unconditional hB.isGood
      (0 : Fin (n + 3)) (by simp) (le_of_lt hfirst) with ⟨T₀⟩
  have htailAdjacent : b.tail.order 0 ≤ b.tail.order 1 := by
    have hzero : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
      rw [b.order_tail]
      congr 1
    have hone : b.tail.order (1 : Fin (n + 2)) = b.order 2 := by
      rw [b.order_tail]
      congr 1
    have hthird := D.thirdGap
    calc
      b.tail.order 0 = b.order 1 := hzero
      _ ≤ b.order 2 := by omega
      _ = b.tail.order 1 := hone.symm
  rcases b.tail.beliCorollary44_i_unconditional
      hB.tail_for_lemma62.isGood (0 : Fin (n + 2)) (by simp)
      htailAdjacent with ⟨T₁⟩
  let f₀ := T₀.toProductLatticeIsometry
  let z := f₀.toLinearEquiv.symm v
  have hvL : v ∈ L := ((S.mem_intermediateLattice_iff v).1 hv).1
  have hzProduct : z ∈
      Lattice.product T₀.left.lattice T₀.right.lattice := by
    exact (f₀.symm.map_mem v).1 hvL
  have hzMem := Lattice.mem_product_iff.mp hzProduct
  have hvEq : (z.1 : V) + (z.2 : V) = v := by
    change f₀.toLinearEquiv z = v
    exact f₀.toLinearEquiv.apply_symm_apply v
  have hprojectionEq : (S.projection v : V) = (z.2 : V) := by
    change (q.projectionToOrthogonal b.head b.head_isAnisotropic v : V) =
      ((T₀.toProductLatticeIsometry.toLinearEquiv.symm v).2 : V)
    exact T₀.coe_projection_eq_rightCoordinate_of_cut_one v
  have hprojectionMem : S.projection v ∈ S.tailRescale.lattice :=
    ((S.mem_intermediateLattice_iff v).1 hv).2
  let f₁ := T₁.toProductLatticeIsometry
  let u := f₁.toLinearEquiv.symm (S.projection v)
  have hprojectionTail : S.projection v ∈
      L.projectedLattice q b.head b.head_isAnisotropic :=
    S.tailRescale_lattice_le_tail hprojectionMem
  have huProduct : u ∈
      Lattice.product T₁.left.lattice T₁.right.lattice := by
    exact (f₁.symm.map_mem (S.projection v)).1 hprojectionTail
  have huMem := Lattice.mem_product_iff.mp huProduct
  have hprojectionDecomp :
      (u.1 : q.vectorOrthogonal b.head) +
          (u.2 : q.vectorOrthogonal b.head) = S.projection v := by
    change f₁.toLinearEquiv u = S.projection v
    exact f₁.toLinearEquiv.apply_symm_apply (S.projection v)
  let tailOrder : Int := b.order 1 + 2 * (S.k : Int)
  have hreflection := S.two_mul_reflectionScaleOrder D.finalGap_even
  have hvQuadratic : q.quadratic v ∈
      Lattice.powerIdeal (K := K) tailOrder := by
    rw [Lattice.mem_powerIdeal_iff, horder]
    exact_mod_cast D.tailOrder_le_critical
  have hprojectionQuadratic :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (S.projection v) ∈
        Lattice.powerIdeal (K := K) tailOrder := by
    have hnorm := Lattice.quadratic_mem_normIdeal_of_mem
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice hprojectionMem
    rw [S.tailRescale.bong.normIdeal_eq_powerIdeal_order_zero,
      S.tailRescale.order_zero_eq] at hnorm
    have htailZero : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
      rw [b.order_tail]
      congr 1
    rw [htailZero] at hnorm
    simpa only [tailOrder] using hnorm
  let right := T₁.right.bong.castLength
    (by simp : n + 2 - ((0 : Fin (n + 2)).1 + 1) = n + 1)
  have hrightOrder : right.order 0 = b.order 2 := by
    rw [BONG.order_castLength_index]
    have hsegment := T₁.right.order_eq
      (⟨0, by simp⟩ : Fin (n + 2 - ((0 : Fin (n + 2)).1 + 1)))
    have htailZero : b.tail.order (1 : Fin (n + 2)) = b.order 2 := by
      rw [b.order_tail]
      congr 1
    rw [← htailZero]
    simpa [SegmentWitness.sourceIndex] using hsegment
  have hrightNorm :
      Lattice.normIdeal
          ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
            T₁.right.carrier T₁.right.nondegenerate)
          T₁.right.lattice =
        Lattice.powerIdeal (K := K) (b.order 2) := by
    rw [right.normIdeal_eq_powerIdeal_order_zero,
      hrightOrder]
  have huRightQuadratic :
      ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
        T₁.right.carrier T₁.right.nondegenerate).quadratic u.2 ∈
        Lattice.powerIdeal (K := K) (b.order 2) := by
    have hnorm := Lattice.quadratic_mem_normIdeal_of_mem
      ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
        T₁.right.carrier T₁.right.nondegenerate)
      T₁.right.lattice huMem.2
    rwa [hrightNorm] at hnorm
  have huRightTail : (u.2 : q.vectorOrthogonal b.head) ∈
      L.projectedLattice q b.head b.head_isAnisotropic := by
    have hpair : (0, u.2) ∈
        Lattice.product T₁.left.lattice T₁.right.lattice :=
      Lattice.mem_product_iff.mpr
        ⟨T₁.left.lattice.zero_mem, huMem.2⟩
    have hmap := (f₁.map_mem (0, u.2)).1 hpair
    change (0 : q.vectorOrthogonal b.head) +
      (u.2 : q.vectorOrthogonal b.head) ∈
        L.projectedLattice q b.head b.head_isAnisotropic at hmap
    simpa using hmap
  have huRightRescaled : (u.2 : q.vectorOrthogonal b.head) ∈
      S.tailRescale.lattice := by
    rw [S.tailRescale.mem_lattice_iff_ord_ge_head_depth]
    refine ⟨huRightTail, ?_⟩
    have horderRight :=
      (Lattice.mem_powerIdeal_iff (K := K) (b.order 2)
        (((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
          T₁.right.carrier T₁.right.nondegenerate).quadratic u.2)).1
        huRightQuadratic
    change (b.order 2 : WithTop Int) ≤
      ord K ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
        (u.2 : q.vectorOrthogonal b.head)) at horderRight
    have htailZero : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
      rw [b.order_tail]
      congr 1
    rw [htailZero]
    have hthreshold :
        ((b.order 1 + 2 * (S.k : Int) - 1 : Int) : WithTop Int) ≤
          (b.order 2 : WithTop Int) := by
      exact_mod_cast (show
        b.order 1 + 2 * (S.k : Int) - 1 ≤ b.order 2 by
          have hthird := D.tailOrder_lt_third
          omega)
    exact hthreshold.trans horderRight
  have huLeftRescaled : (u.1 : q.vectorOrthogonal b.head) ∈
      S.tailRescale.lattice := by
    have hsub := S.tailRescale.lattice.sub_mem
      hprojectionMem huRightRescaled
    have heq : (u.1 : q.vectorOrthogonal b.head) =
        S.projection v - (u.2 : q.vectorOrthogonal b.head) := by
      rw [← hprojectionDecomp]
      abel
    rwa [heq]
  have huLeftQuadratic :
      ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
        T₁.left.carrier T₁.left.nondegenerate).quadratic u.1 ∈
        Lattice.powerIdeal (K := K) tailOrder := by
    have hnorm := Lattice.quadratic_mem_normIdeal_of_mem
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice huLeftRescaled
    rw [S.tailRescale.bong.normIdeal_eq_powerIdeal_order_zero,
      S.tailRescale.order_zero_eq] at hnorm
    have htailZero : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
      rw [b.order_tail]
      congr 1
    rw [htailZero] at hnorm
    change
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (u.1 : q.vectorOrthogonal b.head) ∈
        Lattice.powerIdeal (K := K) tailOrder
    simpa only [tailOrder] using hnorm
  have hzLeftQuadratic :
      (q.restrict T₀.left.carrier T₀.left.nondegenerate).quadratic z.1 ∈
        Lattice.powerIdeal (K := K) tailOrder := by
    change q.quadratic (z.1 : V) ∈
      Lattice.powerIdeal (K := K) tailOrder
    have horth : q.bilin (z.1 : V) (z.2 : V) = 0 :=
      T₀.left_right_orthogonal z.1 z.2
    have hvQuadraticEq : q.quadratic v =
        q.quadratic (z.1 : V) + q.quadratic (z.2 : V) := by
      rw [← hvEq, q.quadratic_add, horth]
      ring
    have hprojectionQuadraticEq :
        (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
            (S.projection v) = q.quadratic (z.2 : V) := by
      exact congrArg q.quadratic hprojectionEq
    have hquadraticEq : q.quadratic (z.1 : V) =
        q.quadratic v -
          (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
            (S.projection v) := by
      rw [hvQuadraticEq, hprojectionQuadraticEq]
      ring
    rw [hquadraticEq]
    exact (Lattice.powerIdeal (K := K) tailOrder).sub_mem
      hvQuadratic hprojectionQuadratic
  have hheadFinrank : finrank K T₀.left.carrier = 1 := by
    have h := T₀.left.bong.length_eq_finrank
    change 1 = finrank K T₀.left.carrier at h
    exact h.symm
  have hheadOrder : T₀.left.bong.order 0 = b.order 0 := by
    simpa [SegmentWitness.sourceIndex] using
      T₀.left.order_eq (0 : Fin 1)
  have hheadNorm :
      Lattice.normIdeal
          (q.restrict T₀.left.carrier T₀.left.nondegenerate)
          T₀.left.lattice =
        Lattice.powerIdeal (K := K) (b.order 0) := by
    rw [T₀.left.bong.normIdeal_eq_powerIdeal_order_zero, hheadOrder]
  have htailLeftFinrank :
      finrank K T₁.left.carrier = 1 := by
    have h := T₁.left.bong.length_eq_finrank
    change 1 = finrank K T₁.left.carrier at h
    exact h.symm
  have htailLeftOrder : T₁.left.bong.order 0 = b.order 1 := by
    calc
      T₁.left.bong.order 0 =
          b.tail.order (T₁.left.sourceIndex 0) :=
        T₁.left.order_eq 0
      _ = b.tail.order 0 := by
        congr 1
      _ = b.order 1 := by
        rw [b.order_tail]
        congr 1
  have htailLeftNorm :
      Lattice.normIdeal
          ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
            T₁.left.carrier T₁.left.nondegenerate)
          T₁.left.lattice =
        Lattice.powerIdeal (K := K) (b.order 1) := by
    rw [T₁.left.bong.normIdeal_eq_powerIdeal_order_zero,
      htailLeftOrder]
  have hheadSum :
      2 * S.reflectionScaleOrder ≤ tailOrder + b.order 0 := by
    simp only [tailOrder]
    omega
  have hsecondSum :
      2 * S.reflectionScaleOrder ≤ tailOrder + b.order 1 := by
    simp only [tailOrder]
    omega
  have hrightScaleBase :=
    Lattice.scaleIdeal_le_powerIdeal_sub_ramification_of_normIdeal_eq
      (p := (q.orthogonalSpace b.head b.head_isAnisotropic).restrict
        T₁.right.carrier T₁.right.nondegenerate)
      (M := T₁.right.lattice) (b.order 2) hrightNorm
  have hrightScale :
      Lattice.scaleIdeal
          ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
            T₁.right.carrier T₁.right.nondegenerate)
          T₁.right.lattice ≤
        Lattice.powerIdeal (K := K) S.reflectionScaleOrder :=
    hrightScaleBase.trans (by
      rw [Lattice.powerIdeal_le_iff]
      exact le_of_lt D.reflection_lt_third_sub_ramification)
  apply Lattice.mem_scaleTruncation_of_pairing_mem_powerIdeal hvL
  intro y hy
  let w := f₀.toLinearEquiv.symm y
  have hwProduct : w ∈
      Lattice.product T₀.left.lattice T₀.right.lattice := by
    exact (f₀.symm.map_mem y).1 hy
  have hwMem := Lattice.mem_product_iff.mp hwProduct
  have hyEq : (w.1 : V) + (w.2 : V) = y := by
    change f₀.toLinearEquiv w = y
    exact f₀.toLinearEquiv.apply_symm_apply y
  have hprojectionYEq : (S.projection y : V) = (w.2 : V) := by
    change (q.projectionToOrthogonal b.head b.head_isAnisotropic y : V) =
      ((T₀.toProductLatticeIsometry.toLinearEquiv.symm y).2 : V)
    exact T₀.coe_projection_eq_rightCoordinate_of_cut_one y
  have hprojectionYTail : S.projection y ∈
      L.projectedLattice q b.head b.head_isAnisotropic :=
    S.projection_mem_tail y hy
  let t := f₁.toLinearEquiv.symm (S.projection y)
  have htProduct : t ∈
      Lattice.product T₁.left.lattice T₁.right.lattice := by
    exact (f₁.symm.map_mem (S.projection y)).1 hprojectionYTail
  have htMem := Lattice.mem_product_iff.mp htProduct
  have hprojectionYDecomp :
      (t.1 : q.vectorOrthogonal b.head) +
          (t.2 : q.vectorOrthogonal b.head) = S.projection y := by
    change f₁.toLinearEquiv t = S.projection y
    exact f₁.toLinearEquiv.apply_symm_apply (S.projection y)
  have hwHeadQuadratic :
      (q.restrict T₀.left.carrier T₀.left.nondegenerate).quadratic w.1 ∈
        Lattice.powerIdeal (K := K) (b.order 0) := by
    have hnorm := Lattice.quadratic_mem_normIdeal_of_mem
      (q.restrict T₀.left.carrier T₀.left.nondegenerate)
      T₀.left.lattice hwMem.1
    rwa [hheadNorm] at hnorm
  have hpairHead : q.bilin (z.1 : V) (w.1 : V) ∈
      Lattice.powerIdeal (K := K) S.reflectionScaleOrder :=
    BONG.bilin_mem_powerIdeal_of_finrank_eq_one_of_sum
      (q.restrict T₀.left.carrier T₀.left.nondegenerate)
      hheadFinrank S.reflectionScaleOrder tailOrder (b.order 0)
      z.1 w.1 hzLeftQuadratic hwHeadQuadratic hheadSum
  have htLeftQuadratic :
      ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
        T₁.left.carrier T₁.left.nondegenerate).quadratic t.1 ∈
        Lattice.powerIdeal (K := K) (b.order 1) := by
    have hnorm := Lattice.quadratic_mem_normIdeal_of_mem
      ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
        T₁.left.carrier T₁.left.nondegenerate)
      T₁.left.lattice htMem.1
    rwa [htailLeftNorm] at hnorm
  have hpairSecond :
      (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
          (u.1 : q.vectorOrthogonal b.head)
          (t.1 : q.vectorOrthogonal b.head) ∈
        Lattice.powerIdeal (K := K) S.reflectionScaleOrder :=
    BONG.bilin_mem_powerIdeal_of_finrank_eq_one_of_sum
      ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
        T₁.left.carrier T₁.left.nondegenerate)
      htailLeftFinrank S.reflectionScaleOrder tailOrder (b.order 1)
      u.1 t.1 huLeftQuadratic htLeftQuadratic hsecondSum
  have hpairRight :
      (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
          (u.2 : q.vectorOrthogonal b.head)
          (t.2 : q.vectorOrthogonal b.head) ∈
        Lattice.powerIdeal (K := K) S.reflectionScaleOrder :=
    hrightScale (Lattice.bilin_mem_scaleIdeal_of_mem
      ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
        T₁.right.carrier T₁.right.nondegenerate)
      T₁.right.lattice huMem.2 htMem.2)
  have hpairTail :
      (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
          (S.projection v) (S.projection y) ∈
        Lattice.powerIdeal (K := K) S.reflectionScaleOrder := by
    rw [← hprojectionDecomp, ← hprojectionYDecomp,
      LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.add_right,
      T₁.left_right_orthogonal u.1 t.2,
      T₁.right_left_orthogonal u.2 t.1]
    simp only [add_zero, zero_add]
    exact (Lattice.powerIdeal (K := K) S.reflectionScaleOrder).add_mem
      hpairSecond hpairRight
  rw [← hvEq, ← hyEq, LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.add_right,
    T₀.left_right_orthogonal z.1 w.2,
    T₀.right_left_orthogonal z.2 w.1]
  simp only [add_zero, zero_add]
  apply (Lattice.powerIdeal (K := K) S.reflectionScaleOrder).add_mem
    hpairHead
  change q.bilin (S.projection v : V) (S.projection y : V) ∈
    Lattice.powerIdeal (K := K) S.reflectionScaleOrder at hpairTail
  rw [hprojectionEq, hprojectionYEq] at hpairTail
  exact hpairTail

/-- Claim (a) in the finite-defect boundary case when the first Jordan
component is binary.  The proof separates the initial binary block from the
deep complement, applies Lemma 6.1(ii) only on that binary block, and then
cancels the common factor `πᵏ` in the scale bound. -/
theorem mem_scaleTruncation_of_boundary_of_second_order_le_first
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hboundary :
      (quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int))
    (v : V) (hv : v ∈ S.intermediateLattice)
    (horder : ord K (q.quadratic v) =
      ((S.reflectionScaleOrder + ramificationIndex K : Int) :
        WithTop Int))
    (hsecond : b.order 1 ≤ b.order 0) :
    v ∈ Lattice.scaleTruncation q L S.reflectionScaleOrder := by
  let D := S.boundaryOrderData hB hboundary
  rcases b.exists_twoBlockSplit_of_leftOrders_le_rightHead
      2 (by omega) (by omega) (by
        intro i
        rw [SegmentWitness.order_eq, SegmentWitness.order_eq]
        fin_cases i
        · change b.order 0 ≤ b.order 2
          have hkNonneg : (0 : Int) ≤ (S.k : Int) := by positivity
          have hhead := D.headRescaledOrder_le_critical
          have hthird := D.critical_lt_third
          omega
        · change b.order 1 ≤ b.order 2
          have hthird := D.thirdGap
          omega) with ⟨T⟩
  let f := T.toProductLatticeIsometry
  let z := f.toLinearEquiv.symm v
  have hvL : v ∈ L := ((S.mem_intermediateLattice_iff v).1 hv).1
  have hzProduct : z ∈
      Lattice.product T.left.lattice T.right.lattice := by
    exact (f.symm.map_mem v).1 hvL
  have hzMem := Lattice.mem_product_iff.mp hzProduct
  have hvEq : (z.1 : V) + (z.2 : V) = v := by
    change f.toLinearEquiv z = v
    exact f.toLinearEquiv.apply_symm_apply v
  let right := T.right.bong.castLength
    (by omega : n + 3 - 2 = n + 1)
  have hrightOrder : right.order 0 = b.order 2 := by
    rw [BONG.order_castLength_index]
    calc
      T.right.bong.order ⟨0, by omega⟩ =
          b.order (T.right.sourceIndex ⟨0, by omega⟩) :=
        T.right.order_eq ⟨0, by omega⟩
      _ = b.order 2 := by
        congr 1
  have hrightNorm :
      Lattice.normIdeal
          (q.restrict T.right.carrier T.right.nondegenerate)
          T.right.lattice =
        Lattice.powerIdeal (K := K) (b.order 2) := by
    rw [right.normIdeal_eq_powerIdeal_order_zero, hrightOrder]
  have hzRightQuadratic :
      (q.restrict T.right.carrier T.right.nondegenerate).quadratic z.2 ∈
        Lattice.powerIdeal (K := K) (b.order 2) := by
    have hnorm := Lattice.quadratic_mem_normIdeal_of_mem
      (q.restrict T.right.carrier T.right.nondegenerate)
      T.right.lattice hzMem.2
    rwa [hrightNorm] at hnorm
  have hzRightOrder : (b.order 2 : WithTop Int) ≤
      ord K (q.quadratic (z.2 : V)) := by
    exact (Lattice.mem_powerIdeal_iff (K := K) (b.order 2)
      (q.quadratic (z.2 : V))).1 (by
        change q.quadratic (z.2 : V) ∈
          Lattice.powerIdeal (K := K) (b.order 2) at hzRightQuadratic
        exact hzRightQuadratic)
  have hzRightL : (z.2 : V) ∈ L := T.coe_right_mem z.2 hzMem.2
  have hzRightOrth : (z.2 : V) ∈ q.vectorOrthogonal b.head :=
    T.right_mem_vectorOrthogonal_head_of_cut_two z.2
  let zRightOrth : q.vectorOrthogonal b.head := ⟨(z.2 : V), hzRightOrth⟩
  have hprojectionRight : S.projection (z.2 : V) = zRightOrth := by
    apply Subtype.ext
    exact q.orthogonalProjection_eq_self hzRightOrth
  have hzRightTail : zRightOrth ∈
      L.projectedLattice q b.head b.head_isAnisotropic := by
    have htail := S.projection_mem_tail (z.2 : V) hzRightL
    rwa [hprojectionRight] at htail
  have hzRightRescaled : zRightOrth ∈ S.tailRescale.lattice := by
    rw [S.tailRescale.mem_lattice_iff_ord_ge_head_depth]
    refine ⟨hzRightTail, ?_⟩
    have htailZero : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
      rw [b.order_tail]
      congr 1
    rw [htailZero]
    have hthreshold :
        ((b.order 1 + 2 * (S.k : Int) - 1 : Int) : WithTop Int) ≤
          (b.order 2 : WithTop Int) := by
      exact_mod_cast (show
        b.order 1 + 2 * (S.k : Int) - 1 ≤ b.order 2 by
          have hthird := D.tailOrder_lt_third
          omega)
    exact hthreshold.trans (by
      change (b.order 2 : WithTop Int) ≤
        ord K (q.quadratic (z.2 : V)) at hzRightOrder
      exact hzRightOrder)
  have hzRightIntermediate : (z.2 : V) ∈ S.intermediateLattice := by
    rw [S.mem_intermediateLattice_iff]
    refine ⟨hzRightL, ?_⟩
    rw [hprojectionRight]
    exact hzRightRescaled
  have hzLeftIntermediate : (z.1 : V) ∈ S.intermediateLattice := by
    have hsub := S.intermediateLattice.sub_mem hv hzRightIntermediate
    have heq : (z.1 : V) = v - (z.2 : V) := by
      rw [← hvEq]
      abel
    rwa [heq]
  have hvQuadraticEq : q.quadratic v =
      q.quadratic (z.1 : V) + q.quadratic (z.2 : V) := by
    rw [← hvEq, q.quadratic_add,
      T.left_right_orthogonal z.1 z.2]
    ring
  have hzLeftQuadraticEq : q.quadratic (z.1 : V) =
      q.quadratic v - q.quadratic (z.2 : V) := by
    rw [hvQuadraticEq]
    ring
  have hzLeftOrder : ord K (q.quadratic (z.1 : V)) =
      ((S.reflectionScaleOrder + ramificationIndex K : Int) :
        WithTop Int) := by
    rw [hzLeftQuadraticEq]
    have hcriticalThird :
        ((S.reflectionScaleOrder + ramificationIndex K : Int) :
            WithTop Int) < (b.order 2 : WithTop Int) := by
      exact_mod_cast D.critical_lt_third
    have hlt : ord K (q.quadratic v) <
        ord K (q.quadratic (z.2 : V)) := by
      rw [horder]
      exact hcriticalThird.trans_le hzRightOrder
    simpa only [horder] using (ord K).map_sub_eq_of_lt_left hlt
  rcases S.exists_intermediateInitialBinarySplit_of_boundaryOrderData D with ⟨U⟩
  have hzLeftCarrierU : (z.1 : V) ∈ U.left.carrier := by
    have hzOriginalSegment : (z.1 : V) ∈
        b.segmentCarrier 0 2 (by omega) := by
      let zLeftV : V := (z.1 : V)
      have hzCarrier : zLeftV ∈ T.left.carrier := z.1.property
      rw [T.left.carrier_eq_segmentCarrier] at hzCarrier
      simpa only [zLeftV] using hzCarrier
    rw [U.left.carrier_eq_segmentCarrier,
      S.intermediateBONG_prefixTwo_segmentCarrier_eq]
    exact hzOriginalSegment
  let zU : U.left.carrier := ⟨(z.1 : V), hzLeftCarrierU⟩
  have hzULattice : zU ∈ U.left.lattice :=
    U.left_mem_of_coe_mem zU hzLeftIntermediate
  let W : U.left.bong.HeadDepthWitness S.k :=
    Classical.choice (S.exists_initialBinaryHeadDepth U)
  have hUzero : U.left.bong.order 0 = b.order 0 := by
    calc
      U.left.bong.order 0 =
          S.intermediateBONG.order (U.left.sourceIndex 0) :=
        U.left.order_eq 0
      _ = S.intermediateBONG.order 0 := by congr 1
      _ = b.order 0 := S.intermediateBONG_order_zero
  have hUone : U.left.bong.order 1 =
      b.order 1 + 2 * (S.k : Int) := by
    calc
      U.left.bong.order 1 =
          S.intermediateBONG.order (U.left.sourceIndex 1) :=
        U.left.order_eq 1
      _ = S.intermediateBONG.order 1 := by congr 1
      _ = b.order 1 + 2 * (S.k : Int) :=
        S.intermediateBONG_order_one
  have hzW : zU ∈ W.lattice := by
    rw [W.mem_lattice_iff]
    refine ⟨hzULattice, ?_⟩
    change
      ((U.left.bong.order 0 + 2 * (S.k : Int) - 1 : Int) :
          WithTop Int) ≤
        ord K (q.quadratic (z.1 : V))
    rw [hUzero, hzLeftOrder]
    exact_mod_cast (show
      b.order 0 + 2 * (S.k : Int) - 1 ≤
        S.reflectionScaleOrder + ramificationIndex K by
      have hhead := D.headRescaledOrder_le_critical
      omega)
  have hWzero : W.bong.order 0 =
      b.order 0 + 2 * (S.k : Int) := by
    rw [W.order_zero_eq, hUzero]
  have hWone : W.bong.order 1 =
      b.order 1 + 2 * (S.k : Int) := by
    have h := W.order_succ_eq (0 : Fin 1)
    change W.bong.order 1 = U.left.bong.order 1 at h
    rw [h, hUone]
  have hscaleDoubled :=
    beliCorollary44_iv_unconditional W.bong W.good
  have hscaleBound :
      2 * (S.reflectionScaleOrder + (S.k : Int)) ≤
        min (2 * W.bong.order 0)
          (W.bong.order 0 + W.bong.order 1) := by
    rw [hWzero, hWone,
      min_eq_right (by omega :
        b.order 0 + 2 * (S.k : Int) +
            (b.order 1 + 2 * (S.k : Int)) ≤
          2 * (b.order 0 + 2 * (S.k : Int)))]
    have hreflection := S.two_mul_reflectionScaleOrder D.finalGap_even
    omega
  have hheadScale : Lattice.scaleIdeal
        (q.restrict U.left.carrier U.left.nondegenerate) W.lattice ≤
      Lattice.powerIdeal (K := K)
        (S.reflectionScaleOrder + (S.k : Int)) :=
    scaleIdeal_le_powerIdeal_of_hasDoubledScaleOrder
      hscaleDoubled hscaleBound
  have hrightScaleBase :=
    Lattice.scaleIdeal_le_powerIdeal_sub_ramification_of_normIdeal_eq
      (p := q.restrict T.right.carrier T.right.nondegenerate)
      (M := T.right.lattice) (b.order 2) hrightNorm
  have hrightScale :
      Lattice.scaleIdeal
          (q.restrict T.right.carrier T.right.nondegenerate)
          T.right.lattice ≤
        Lattice.powerIdeal (K := K) S.reflectionScaleOrder :=
    hrightScaleBase.trans (by
      rw [Lattice.powerIdeal_le_iff]
      exact le_of_lt D.reflection_lt_third_sub_ramification)
  apply Lattice.mem_scaleTruncation_of_pairing_mem_powerIdeal hvL
  intro y hy
  let w := f.toLinearEquiv.symm y
  have hwProduct : w ∈
      Lattice.product T.left.lattice T.right.lattice := by
    exact (f.symm.map_mem y).1 hy
  have hwMem := Lattice.mem_product_iff.mp hwProduct
  have hyEq : (w.1 : V) + (w.2 : V) = y := by
    change f.toLinearEquiv w = y
    exact f.toLinearEquiv.apply_symm_apply y
  have hwLeftL : (w.1 : V) ∈ L := T.coe_left_mem w.1 hwMem.1
  have hwLeftScaledIntermediate :
      ((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K) •
          (w.1 : V) ∈ S.intermediateLattice :=
    S.uniformizerPower_smul_mem_intermediateLattice (w.1 : V) hwLeftL
  have hwLeftScaledCarrierU :
      ((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K) •
          (w.1 : V) ∈ U.left.carrier := by
    have hwOriginalSegment : (w.1 : V) ∈
        b.segmentCarrier 0 2 (by omega) := by
      let wLeftV : V := (w.1 : V)
      have hwCarrier : wLeftV ∈ T.left.carrier := w.1.property
      rw [T.left.carrier_eq_segmentCarrier] at hwCarrier
      simpa only [wLeftV] using hwCarrier
    have hwScaledOriginalSegment :=
      (b.segmentCarrier 0 2 (by omega)).smul_mem
        (((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K))
        hwOriginalSegment
    rw [U.left.carrier_eq_segmentCarrier,
      S.intermediateBONG_prefixTwo_segmentCarrier_eq]
    exact hwScaledOriginalSegment
  let yU : U.left.carrier :=
    ⟨((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K) •
      (w.1 : V), hwLeftScaledCarrierU⟩
  have hyULattice : yU ∈ U.left.lattice :=
    U.left_mem_of_coe_mem yU hwLeftScaledIntermediate
  have hyW : yU ∈ W.lattice := by
    rw [W.mem_lattice_iff]
    refine ⟨hyULattice, ?_⟩
    have hwIdeal := Lattice.quadratic_mem_normIdeal_of_mem q L hwLeftL
    rw [b.head_isNormGenerator.normIdeal_eq,
      ← b.value_zero_eq_quadratic_head] at hwIdeal
    have hwOrder : (b.order 0 : WithTop Int) ≤
        ord K (q.quadratic (w.1 : V)) := by
      rw [b.coe_order]
      exact Lattice.ord_le_of_mem_principalIdeal
        (b.value_ne_zero 0) hwIdeal
    have hpowerOrder :
        ord K (((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K) ^ 2) =
          ((2 * (S.k : Int) : Int) : WithTop Int) := by
      rw [ord_pow, ← coe_ordUnit, ordUnit_uniformizerPowerUnit]
      norm_cast
    change
      ((U.left.bong.order 0 + 2 * (S.k : Int) - 1 : Int) :
          WithTop Int) ≤
        ord K (q.quadratic
          (((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K) •
            (w.1 : V)))
    rw [q.quadratic_smul, ord_mul, hpowerOrder, hUzero]
    have hshift := add_le_add_left hwOrder
      ((2 * (S.k : Int) : Int) : WithTop Int)
    have hthreshold :
        ((b.order 0 + 2 * (S.k : Int) - 1 : Int) : WithTop Int) ≤
          ((2 * (S.k : Int) : Int) : WithTop Int) +
            (b.order 0 : WithTop Int) := by
      norm_cast
      omega
    exact hthreshold.trans (by simpa only [add_comm] using hshift)
  have hpairLeftScaled :
      (q.restrict U.left.carrier U.left.nondegenerate).bilin zU yU ∈
        Lattice.powerIdeal (K := K)
          (S.reflectionScaleOrder + (S.k : Int)) :=
    hheadScale (Lattice.bilin_mem_scaleIdeal_of_mem
      (q.restrict U.left.carrier U.left.nondegenerate)
      W.lattice hzW hyW)
  have hpairLeftScaledAmbient :
      q.bilin (z.1 : V)
          (((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K) •
            (w.1 : V)) ∈
        Lattice.powerIdeal (K := K)
          (S.reflectionScaleOrder + (S.k : Int)) := by
    exact hpairLeftScaled
  rw [LinearMap.BilinForm.smul_right] at hpairLeftScaledAmbient
  have hpairLeft : q.bilin (z.1 : V) (w.1 : V) ∈
      Lattice.powerIdeal (K := K) S.reflectionScaleOrder :=
    Lattice.mem_powerIdeal_of_uniformizerPower_mul_mem
      S.k S.reflectionScaleOrder
      (q.bilin (z.1 : V) (w.1 : V)) hpairLeftScaledAmbient
  have hpairRight : q.bilin (z.2 : V) (w.2 : V) ∈
      Lattice.powerIdeal (K := K) S.reflectionScaleOrder :=
    hrightScale (Lattice.bilin_mem_scaleIdeal_of_mem
      (q.restrict T.right.carrier T.right.nondegenerate)
      T.right.lattice hzMem.2 hwMem.2)
  rw [← hvEq, ← hyEq, LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.add_right,
    T.left_right_orthogonal z.1 w.2,
    T.right_left_orthogonal z.2 w.1]
  simp only [add_zero, zero_add]
  exact (Lattice.powerIdeal (K := K) S.reflectionScaleOrder).add_mem
    hpairLeft hpairRight

/-- Claim (a) in Beli's finite-defect boundary case, independent of whether
the first Jordan component is unary or binary. -/
theorem mem_scaleTruncation_of_boundary
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hboundary :
      (quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int))
    (v : V) (hv : v ∈ S.intermediateLattice)
    (horder : ord K (q.quadratic v) =
      ((S.reflectionScaleOrder + ramificationIndex K : Int) :
        WithTop Int)) :
    v ∈ Lattice.scaleTruncation q L S.reflectionScaleOrder := by
  by_cases hfirst : b.order 0 < b.order 1
  · exact S.mem_scaleTruncation_of_boundary_of_first_lt_second
      hB hboundary v hv horder hfirst
  · exact S.mem_scaleTruncation_of_boundary_of_second_order_le_first
      hB hboundary v hv horder (by omega)

/-- Claim (a) throughout the low range.  Lemma 3.17 reduces it exactly to
the finite-defect boundary branch or the short-shift branch. -/
theorem mem_scaleTruncation_of_low
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hlow : b.Lemma65LowRange S)
    (v : V) (hv : v ∈ S.intermediateLattice)
    (horder : ord K (q.quadratic v) =
      ((S.reflectionScaleOrder + ramificationIndex K : Int) :
        WithTop Int)) :
    v ∈ Lattice.scaleTruncation q L S.reflectionScaleOrder := by
  rcases S.lowRange_boundary_or_k_le_one hlow with hboundary | hk
  · exact S.mem_scaleTruncation_of_boundary
      hB hboundary v hv horder
  · exact S.mem_scaleTruncation_of_short
      hB hlow hk v hv horder

/-- Claim (b) in the short-shift branch.  The intermediate BONG is good,
and Lemma 6.4(iii) forces any hyperbolic plane at its natural scale into
the initial binary prefix, where `intermediateBONG_prefix_not_contains_hyperbolic`
rules it out. -/
theorem not_containsScaledHyperbolicPlane_of_short
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hlow : b.Lemma65LowRange S) (hk : S.k ≤ 1) :
    ¬Lattice.ContainsScaledHyperbolicPlane q S.intermediateLattice
      S.reflectionScaleOrder := by
  intro hH
  have heven := S.lowRange_gap_even hlow
  have hgood := S.intermediateBONG_isGood_of_k_le_one hB hk
  have hzero : S.intermediateBONG.order 0 = b.order 0 :=
    S.intermediateBONG_order_zero
  have hone : S.intermediateBONG.order 1 =
      b.order 1 + 2 * (S.k : Int) :=
    S.intermediateBONG_order_one
  have htwo : S.intermediateBONG.order 2 = b.order 2 :=
    S.intermediateBONG_order_two
  have h13 : S.intermediateBONG.order 0 <
      S.intermediateBONG.order 2 := by
    rw [hzero, htwo]
    have h := hB.twoStep_add_two_le (0 : Fin (n + 3)) (by simp)
    have htarget :
        (⟨(0 : Fin (n + 3)).1 + 2, by simp⟩ : Fin (n + 3)) = 2 :=
      Fin.ext rfl
    rw [htarget] at h
    omega
  have hsumEven : Even
      (S.intermediateBONG.order 0 + S.intermediateBONG.order 1) := by
    rcases heven with ⟨z, hz⟩
    refine ⟨z + b.order 0, ?_⟩
    rw [hzero, hone]
    omega
  have hnatural :
      (S.intermediateBONG.order 0 + S.intermediateBONG.order 1) / 2 =
        S.reflectionScaleOrder := by
    have hreflection := S.two_mul_reflectionScaleOrder heven
    rw [hzero, hone]
    rcases hsumEven with ⟨z, hz⟩
    omega
  have hHnatural : Lattice.ContainsScaledHyperbolicPlane
      q S.intermediateLattice
        ((S.intermediateBONG.order 0 +
          S.intermediateBONG.order 1) / 2) := by
    rwa [hnatural]
  have hprefix :=
    S.intermediateBONG.beliLemma64_full_implies_binaryPrefix_proved
      hgood h13 hHnatural
  rw [hnatural] at hprefix
  exact S.intermediateBONG_prefix_not_contains_hyperbolic heven hprefix

/-- Claim (b) in the finite-defect boundary branch when the first Jordan
component is binary.  The initial two-vector block is modular at the
reflection scale, while the third order makes the complementary scale and
norm strictly deeper.  Lemma 6.4(ii) therefore pushes a hypothetical
hyperbolic plane into the excluded initial prefix. -/
theorem not_containsScaledHyperbolicPlane_of_boundary_of_second_order_le_first
    (S : b.Lemma65Setup) (D : S.BoundaryOrderData)
    (hsecond : S.intermediateBONG.order 1 ≤
      S.intermediateBONG.order 0) :
    ¬Lattice.ContainsScaledHyperbolicPlane q S.intermediateLattice
      S.reflectionScaleOrder := by
  classical
  intro hH
  rcases S.exists_intermediateInitialBinarySplit_of_boundaryOrderData D with
    ⟨U⟩
  have hleftOrder : U.left.bong.order 1 ≤ U.left.bong.order 0 := by
    calc
      U.left.bong.order 1 =
          S.intermediateBONG.order (U.left.sourceIndex 1) :=
        U.left.order_eq 1
      _ = S.intermediateBONG.order 1 := by congr 1
      _ ≤ S.intermediateBONG.order 0 := hsecond
      _ = S.intermediateBONG.order (U.left.sourceIndex 0) := by congr 1
      _ = U.left.bong.order 0 := (U.left.order_eq 0).symm
  let hexists :=
    (U.left.bong.exists_isModular_iff_order_one_le_order_zero).2
      hleftOrder
  let a : Kˣ := Classical.choose hexists
  have hmodular : Lattice.IsModular
      (q.restrict U.left.carrier U.left.nondegenerate)
      U.left.lattice a := Classical.choose_spec hexists
  have hUzero : U.left.bong.order 0 = b.order 0 := by
    calc
      U.left.bong.order 0 =
          S.intermediateBONG.order (U.left.sourceIndex 0) :=
        U.left.order_eq 0
      _ = S.intermediateBONG.order 0 := by congr 1
      _ = b.order 0 := S.intermediateBONG_order_zero
  have hUone : U.left.bong.order 1 =
      b.order 1 + 2 * (S.k : Int) := by
    calc
      U.left.bong.order 1 =
          S.intermediateBONG.order (U.left.sourceIndex 1) :=
        U.left.order_eq 1
      _ = S.intermediateBONG.order 1 := by congr 1
      _ = b.order 1 + 2 * (S.k : Int) :=
        S.intermediateBONG_order_one
  have hformula := U.left.bong.order_one_eq_of_isModular a hmodular
  have hsumLeft : U.left.bong.order 0 + U.left.bong.order 1 =
      2 * ordUnit K a := by
    calc
      U.left.bong.order 0 + U.left.bong.order 1 =
          U.left.bong.order 0 +
            (2 * ordUnit K a - U.left.bong.order 0) :=
        congrArg (fun z : Int ↦ U.left.bong.order 0 + z) hformula
      _ = 2 * ordUnit K a := by ring
  have hreflection := S.two_mul_reflectionScaleOrder D.finalGap_even
  have hr : S.reflectionScaleOrder = ordUnit K a := by
    rw [hUzero, hUone] at hsumLeft
    omega
  have hfirstScale :
      Lattice.scaleIdeal
          (q.restrict U.left.carrier U.left.nondegenerate)
          U.left.lattice =
        Lattice.powerIdeal (K := K) S.reflectionScaleOrder := by
    rw [hmodular.scaleIdeal_eq_principal (by
      rw [← U.left.bong.length_eq_finrank]
      norm_num), Lattice.principalIdeal_eq_powerIdeal, hr]
  let right := U.right.bong.castLength
    (by omega : n + 3 - 2 = n + 1)
  have hrightOrder : right.order 0 = b.order 2 := by
    rw [BONG.order_castLength_index]
    calc
      U.right.bong.order ⟨0, by omega⟩ =
          S.intermediateBONG.order
            (U.right.sourceIndex ⟨0, by omega⟩) :=
        U.right.order_eq ⟨0, by omega⟩
      _ = S.intermediateBONG.order 2 := by congr 1
      _ = b.order 2 := S.intermediateBONG_order_two
  have hrightNorm :
      Lattice.normIdeal
          (q.restrict U.right.carrier U.right.nondegenerate)
          U.right.lattice =
        Lattice.powerIdeal (K := K) (b.order 2) := by
    rw [right.normIdeal_eq_powerIdeal_order_zero, hrightOrder]
  have hrightScaleBase :=
    Lattice.scaleIdeal_le_powerIdeal_sub_ramification_of_normIdeal_eq
      (p := q.restrict U.right.carrier U.right.nondegenerate)
      (M := U.right.lattice) (b.order 2) hrightNorm
  have hrightScale :
      Lattice.scaleIdeal
          (q.restrict U.right.carrier U.right.nondegenerate)
          U.right.lattice ≤
        Lattice.powerIdeal (K := K) (S.reflectionScaleOrder + 1) :=
    hrightScaleBase.trans (by
      rw [Lattice.powerIdeal_le_iff]
      have hdepth := D.reflection_lt_third_sub_ramification
      omega)
  have hfirstNorm :
      Lattice.normIdeal
          (q.restrict U.left.carrier U.left.nondegenerate)
          U.left.lattice =
        Lattice.powerIdeal (K := K) (b.order 0) := by
    rw [U.left.bong.normIdeal_eq_powerIdeal_order_zero, hUzero]
  have hzeroLtTwo : b.order 0 < b.order 2 := by
    have hkNonneg : (0 : Int) ≤ (S.k : Int) := by positivity
    have hhead := D.headRescaledOrder_le_critical
    have hthird := D.critical_lt_third
    omega
  have htailNormLt :
      Lattice.normIdeal
          (q.restrict U.right.carrier U.right.nondegenerate)
          U.right.lattice <
        Lattice.normIdeal
          (q.restrict U.left.carrier U.left.nondegenerate)
          U.left.lattice := by
    rw [hrightNorm, hfirstNorm, Lattice.powerIdeal_lt_iff]
    exact hzeroLtTwo
  let B : Lattice.BinaryFirstModularSplitting
      q S.intermediateLattice S.reflectionScaleOrder := {
    toOrthogonalDecomposition := U.decomposition
    first_rank := by
      rw [U.component_zero]
      exact U.left.bong.length_eq_finrank.symm
    first_modular := by
      rw [U.component_zero]
      apply hmodular.of_principalIdeal_eq
      rw [Lattice.principalIdeal_eq_powerIdeal, ← hr]
      rfl
    first_scale_eq := by
      rw [U.component_zero]
      exact hfirstScale
    tail_scale_le := by
      rw [U.component_one]
      exact hrightScale
    tail_norm_lt := by
      rw [U.component_one, U.component_zero]
      exact htailNormLt }
  have hfirst :=
    beliLemma64_binaryFirst_full_implies_first_proved B hH
  let P := S.intermediateBONG.prefixWitness 2 (by omega)
  rcases hfirst with ⟨x, y, hx, hy, hpair⟩
  have hcarrier : (U.decomposition.component 0).carrier = P.carrier := by
    rw [U.component_zero]
    exact U.left.carrier_eq_segmentCarrier.trans
      P.carrier_eq_segmentCarrier.symm
  let xP : P.carrier := ⟨(x : V), hcarrier ▸ x.property⟩
  let yP : P.carrier := ⟨(y : V), hcarrier ▸ y.property⟩
  have hxParent : (x : V) ∈ S.intermediateLattice :=
    B.toOrthogonalDecomposition.component_mem_parent 0 x hx
  have hyParent : (y : V) ∈ S.intermediateLattice :=
    B.toOrthogonalDecomposition.component_mem_parent 0 y hy
  apply S.intermediateBONG_prefix_not_contains_hyperbolic D.finalGap_even
  refine ⟨xP, yP, P.contains_parent xP ?_, P.contains_parent yP ?_, ?_⟩
  · simpa only [xP] using hxParent
  · simpa only [yP] using hyParent
  · simpa only [xP, yP] using hpair

/-- Claim (b) in the finite-defect boundary branch when the first Jordan
component is unary.  We split successively after the first and second
intermediate BONG vectors.  The unary second component has scale equal to
its norm, and the remaining complement is controlled by `2 sK ⊆ nK`;
together they put the whole complement in scale `𝒭^(s+1)`, so Lemma
6.4(i) excludes a hyperbolic plane at scale `s`. -/
theorem not_containsScaledHyperbolicPlane_of_boundary_of_first_lt_second
    (S : b.Lemma65Setup) (D : S.BoundaryOrderData)
    (hfirst : S.intermediateBONG.order 0 <
      S.intermediateBONG.order 1) :
    ¬Lattice.ContainsScaledHyperbolicPlane q S.intermediateLattice
      S.reflectionScaleOrder := by
  classical
  intro hH
  have hsplitFirst : S.intermediateBONG.HasTwoBlockSplit 1 (by omega) := by
    apply S.intermediateBONG.exists_twoBlockSplit_of_leftOrders_le_rightHead
      1 (by omega) (by omega)
    intro i
    fin_cases i
    rw [SegmentWitness.order_eq, SegmentWitness.order_eq]
    simpa [SegmentWitness.sourceIndex] using hfirst.le
  rcases hsplitFirst with ⟨T₀⟩
  let rightZero : Fin (n + 3 - 1) := ⟨0, by omega⟩
  let rightOne : Fin (n + 3 - 1) := ⟨1, by omega⟩
  have hrightZero : T₀.right.bong.order rightZero =
      b.order 1 + 2 * (S.k : Int) := by
    calc
      T₀.right.bong.order rightZero =
          S.intermediateBONG.order (T₀.right.sourceIndex rightZero) :=
        T₀.right.order_eq rightZero
      _ = S.intermediateBONG.order 1 := by congr 1
      _ = b.order 1 + 2 * (S.k : Int) :=
        S.intermediateBONG_order_one
  have hrightOne : T₀.right.bong.order rightOne = b.order 2 := by
    calc
      T₀.right.bong.order rightOne =
          S.intermediateBONG.order (T₀.right.sourceIndex rightOne) :=
        T₀.right.order_eq rightOne
      _ = S.intermediateBONG.order 2 := by congr 1
      _ = b.order 2 := S.intermediateBONG_order_two
  have hrightAdjacent : T₀.right.bong.order rightZero ≤
      T₀.right.bong.order rightOne := by
    rw [hrightZero, hrightOne]
    exact D.tailOrder_lt_third.le
  have hsplitSecond : T₀.right.bong.HasTwoBlockSplit 1 (by omega) := by
    apply T₀.right.bong.exists_twoBlockSplit_of_leftOrders_le_rightHead
      1 (by omega) (by omega)
    intro i
    fin_cases i
    let A := T₀.right.bong.segmentWitness 0 1 (by omega)
    let C := T₀.right.bong.segmentWitness 1 (n + 3 - 1 - 1)
      (by omega)
    have hA : A.bong.order 0 =
        T₀.right.bong.order rightZero := by
      calc
        A.bong.order 0 =
            T₀.right.bong.order (A.sourceIndex 0) := A.order_eq 0
        _ = T₀.right.bong.order rightZero := by congr 1
    have hC : C.bong.order ⟨0, by omega⟩ =
        T₀.right.bong.order rightOne := by
      calc
        C.bong.order ⟨0, by omega⟩ =
            T₀.right.bong.order
              (C.sourceIndex ⟨0, by omega⟩) :=
          C.order_eq ⟨0, by omega⟩
        _ = T₀.right.bong.order rightOne := by congr 1
    change A.bong.order 0 ≤ C.bong.order ⟨0, by omega⟩
    rw [hA, hC]
    exact hrightAdjacent
  rcases hsplitSecond with ⟨T₁⟩
  have hsecondUnaryOrder : T₁.left.bong.order 0 =
      b.order 1 + 2 * (S.k : Int) := by
    calc
      T₁.left.bong.order 0 =
          T₀.right.bong.order (T₁.left.sourceIndex 0) :=
        T₁.left.order_eq 0
      _ = T₀.right.bong.order rightZero := by congr 1
      _ = b.order 1 + 2 * (S.k : Int) := hrightZero
  have hsecondUnaryScale :
      Lattice.scaleIdeal
          ((q.restrict T₀.right.carrier T₀.right.nondegenerate).restrict
            T₁.left.carrier T₁.left.nondegenerate)
          T₁.left.lattice =
        Lattice.powerIdeal (K := K)
          (b.order 1 + 2 * (S.k : Int)) := by
    calc
      Lattice.scaleIdeal
            ((q.restrict T₀.right.carrier T₀.right.nondegenerate).restrict
              T₁.left.carrier T₁.left.nondegenerate)
            T₁.left.lattice =
          Lattice.principalIdeal (K := K)
            (T₁.left.bong.valueUnit 0 : K) :=
        T₁.left.bong.scaleIdeal_eq_principal_valueUnit_zero_unary
      _ = Lattice.powerIdeal (K := K)
          (ordUnit K (T₁.left.bong.valueUnit 0)) :=
        Lattice.principalIdeal_eq_powerIdeal _
      _ = Lattice.powerIdeal (K := K) (T₁.left.bong.order 0) := by
        rw [T₁.left.bong.order_eq_ordUnit]
      _ = Lattice.powerIdeal (K := K)
          (b.order 1 + 2 * (S.k : Int)) := by
        rw [hsecondUnaryOrder]
  let deep := T₁.right.bong.castLength
    (by omega : n + 3 - 1 - 1 = n + 1)
  have hdeepOrder : deep.order 0 = b.order 2 := by
    rw [BONG.order_castLength_index]
    calc
      T₁.right.bong.order ⟨0, by omega⟩ =
          T₀.right.bong.order
            (T₁.right.sourceIndex ⟨0, by omega⟩) :=
        T₁.right.order_eq ⟨0, by omega⟩
      _ = T₀.right.bong.order rightOne := by congr 1
      _ = b.order 2 := hrightOne
  have hdeepNorm :
      Lattice.normIdeal
          ((q.restrict T₀.right.carrier T₀.right.nondegenerate).restrict
            T₁.right.carrier T₁.right.nondegenerate)
          T₁.right.lattice =
        Lattice.powerIdeal (K := K) (b.order 2) := by
    rw [deep.normIdeal_eq_powerIdeal_order_zero, hdeepOrder]
  have hdeepScaleBase :=
    Lattice.scaleIdeal_le_powerIdeal_sub_ramification_of_normIdeal_eq
      (p :=
        (q.restrict T₀.right.carrier T₀.right.nondegenerate).restrict
          T₁.right.carrier T₁.right.nondegenerate)
      (M := T₁.right.lattice) (b.order 2) hdeepNorm
  have hdeepScale :
      Lattice.scaleIdeal
          ((q.restrict T₀.right.carrier T₀.right.nondegenerate).restrict
            T₁.right.carrier T₁.right.nondegenerate)
          T₁.right.lattice ≤
        Lattice.powerIdeal (K := K) (S.reflectionScaleOrder + 1) :=
    hdeepScaleBase.trans (by
      rw [Lattice.powerIdeal_le_iff]
      have hdepth := D.reflection_lt_third_sub_ramification
      omega)
  have hreflection := S.two_mul_reflectionScaleOrder D.finalGap_even
  have hfirstOrders : b.order 0 <
      b.order 1 + 2 * (S.k : Int) := by
    rw [← S.intermediateBONG_order_zero,
      ← S.intermediateBONG_order_one]
    exact hfirst
  have hsecondScaleBound : S.reflectionScaleOrder + 1 ≤
      b.order 1 + 2 * (S.k : Int) := by
    omega
  have hsecondUnaryScaleLe :
      Lattice.scaleIdeal
          ((q.restrict T₀.right.carrier T₀.right.nondegenerate).restrict
            T₁.left.carrier T₁.left.nondegenerate)
          T₁.left.lattice ≤
        Lattice.powerIdeal (K := K) (S.reflectionScaleOrder + 1) := by
    rw [hsecondUnaryScale, Lattice.powerIdeal_le_iff]
    exact hsecondScaleBound
  have htailScale :
      Lattice.scaleIdeal
          (q.restrict T₀.right.carrier T₀.right.nondegenerate)
          T₀.right.lattice ≤
        Lattice.powerIdeal (K := K) (S.reflectionScaleOrder + 1) := by
    rw [T₁.decomposition.scaleIdeal_eq_sup_components_fin_two]
    apply _root_.sup_le
    · rw [T₁.component_zero]
      exact hsecondUnaryScaleLe
    · rw [T₁.component_one]
      exact hdeepScale
  let U : Lattice.UnaryFirstSplitting
      q S.intermediateLattice S.reflectionScaleOrder := {
    toOrthogonalDecomposition := T₀.decomposition
    first_rank := by
      rw [T₀.component_zero]
      exact T₀.left.bong.length_eq_finrank.symm
    tail_scale_le := by
      rw [T₀.component_one]
      exact htailScale }
  exact beliLemma64_unaryFirst_excludes_hyperbolic_proved U hH

/-- Claim (b) in the complete finite-defect boundary case. -/
theorem not_containsScaledHyperbolicPlane_of_boundary
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hboundary :
      (quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int)) :
    ¬Lattice.ContainsScaledHyperbolicPlane q S.intermediateLattice
      S.reflectionScaleOrder := by
  let D := S.boundaryOrderData hB hboundary
  by_cases hfirst : S.intermediateBONG.order 0 <
      S.intermediateBONG.order 1
  · exact S.not_containsScaledHyperbolicPlane_of_boundary_of_first_lt_second
      D hfirst
  · exact
      S.not_containsScaledHyperbolicPlane_of_boundary_of_second_order_le_first
        D (le_of_not_gt hfirst)

/-- Claim (b) throughout the low range.  Lemma 3.17 reduces it to the
finite-defect boundary branch or the short-shift branch. -/
theorem not_containsScaledHyperbolicPlane_of_low
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hlow : b.Lemma65LowRange S) :
    ¬Lattice.ContainsScaledHyperbolicPlane q S.intermediateLattice
      S.reflectionScaleOrder := by
  rcases S.lowRange_boundary_or_k_le_one hlow with hboundary | hk
  · exact S.not_containsScaledHyperbolicPlane_of_boundary hB hboundary
  · exact S.not_containsScaledHyperbolicPlane_of_short hB hlow hk

/-- Unconditional proof of Beli (2003), Lemma 6.5(ii). -/
theorem low_reflection_proved
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hlow : b.Lemma65LowRange S)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x)) :
    Nonempty (Lemma65DifferenceReflectionWitness b x) := by
  have hxIntermediate : x ∈ S.intermediateLattice :=
    S.mem_intermediateLattice x hx hgenerator.mem
  have hheadIntermediate : b.head ∈ S.intermediateLattice := by
    rw [← S.intermediateBONG_ambientVector_zero,
      S.intermediateBONG.ambientVector_zero_eq_head]
    exact S.intermediateBONG.head_isNormGenerator.mem
  have hdifferenceIntermediate : b.head - x ∈ S.intermediateLattice :=
    S.intermediateLattice.sub_mem hheadIntermediate hxIntermediate
  have hdifferenceOrder :=
    (S.ord_quadratic_head_sub_and_add_of_low_isNormGenerator
      x heq hlow hgenerator).1
  have hdifferenceScale := S.mem_scaleTruncation_of_low
    hB hlow (b.head - x) hdifferenceIntermediate hdifferenceOrder
  let anisotropic : q.IsAnisotropic (b.head - x) := by
    intro hzero
    rw [hzero, ord_zero] at hdifferenceOrder
    exact WithTop.top_ne_coe hdifferenceOrder
  refine ⟨{
    anisotropic := anisotropic
    integral := ?_
  }⟩
  exact Lattice.isIntegralReflection_of_mem_scaleTruncation
    hdifferenceScale hdifferenceOrder

/-- Unconditional proof of Beli (2003), Lemma 6.5(iii).  If the reflected
projection were also not a norm generator, the strict alternatives for
`x'` and its reflected image give four sign cases.  In every case Lemma 3.19
constructs a scaled hyperbolic pair in the intermediate lattice, contradicting
Claim (b). -/
theorem reflected_projection_generator_proved
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hlow : b.Lemma65LowRange S)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x))
    (w : Lemma65DifferenceReflectionWitness b x)
    (x' : V) (hx' : x' ∈ L)
    (heq' : q.quadratic x' = q.quadratic b.head)
    (hnotGenerator : ¬Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x')) :
    Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice
      (S.projection
        (q.reflectionLinearEquiv (b.head - x) w.anisotropic x')) := by
  classical
  let t := q.reflectionLinearEquiv (b.head - x) w.anisotropic
  have htQuadratic (z : V) : q.quadratic (t z) = q.quadratic z := by
    have h :=
      (q.reflectionIsometry (b.head - x) w.anisotropic).map_quadratic z
    change q.quadratic
      (q.reflectionLinearEquiv (b.head - x) w.anisotropic z) =
        q.quadratic z at h
    simpa only [t] using h
  let x'' : V := t x'
  change Lattice.IsNormGenerator
    (q.orthogonalSpace b.head b.head_isAnisotropic)
    S.tailRescale.lattice (S.projection x'')
  by_contra hnotGenerator''
  have hx''L : x'' ∈ L := by
    simpa only [x'', t] using w.integral x' hx'
  have heq'' : q.quadratic x'' = q.quadratic b.head := by
    calc
      q.quadratic x'' = q.quadratic x' := by
        simpa only [x''] using htQuadratic x'
      _ = q.quadratic b.head := heq'
  have hxIntermediate : x ∈ S.intermediateLattice :=
    S.mem_intermediateLattice x hx hgenerator.mem
  have hx'Projection : S.projection x' ∈ S.tailRescale.lattice :=
    S.projection_mem_tailRescale_of_low hB x' hx' heq' hlow
  have hx'Intermediate : x' ∈ S.intermediateLattice :=
    S.mem_intermediateLattice x' hx' hx'Projection
  have hx''Projection : S.projection x'' ∈ S.tailRescale.lattice :=
    S.projection_mem_tailRescale_of_low hB x'' hx''L heq'' hlow
  have hx''Intermediate : x'' ∈ S.intermediateLattice :=
    S.mem_intermediateLattice x'' hx''L hx''Projection
  have hheadIntermediate : b.head ∈ S.intermediateLattice := by
    rw [← S.intermediateBONG_ambientVector_zero,
      S.intermediateBONG.ambientVector_zero_eq_head]
    exact S.intermediateBONG.head_isNormGenerator.mem
  have htHead : t b.head = x := by
    simpa only [t] using w.map_head heq
  have htX' : t x' = x'' := rfl
  have htSub : t (b.head - x') = x - x'' := by
    rw [map_sub, htHead, htX']
  have htAdd : t (b.head + x') = x + x'' := by
    rw [map_add, htHead, htX']
  have htSubIntermediate : t (b.head - x') ∈
      S.intermediateLattice := by
    rw [htSub]
    exact S.intermediateLattice.sub_mem hxIntermediate hx''Intermediate
  have htAddIntermediate : t (b.head + x') ∈
      S.intermediateLattice := by
    rw [htAdd]
    exact S.intermediateLattice.add_mem hxIntermediate hx''Intermediate
  have hheadSubX''Intermediate : b.head - x'' ∈
      S.intermediateLattice :=
    S.intermediateLattice.sub_mem hheadIntermediate hx''Intermediate
  have hheadAddX''Intermediate : b.head + x'' ∈
      S.intermediateLattice :=
    S.intermediateLattice.add_mem hheadIntermediate hx''Intermediate
  let R : Int := S.reflectionScaleOrder + ramificationIndex K
  have hcritical :=
    S.ord_quadratic_head_sub_and_add_of_low_isNormGenerator
      x heq hlow hgenerator
  have hcriticalSub : ord K (q.quadratic (b.head - x)) =
      (R : WithTop Int) := by
    simpa only [R] using hcritical.1
  have hcriticalAdd : ord K (q.quadratic (b.head + x)) =
      (R : WithTop Int) := by
    simpa only [R] using hcritical.2
  have hnoHyperbolic :=
    S.not_containsScaledHyperbolicPlane_of_low hB hlow
  have hyperbolicContradiction
      (u v : V) (hu : u ∈ S.intermediateLattice)
      (hv : v ∈ S.intermediateLattice)
      (huHigh : (R : WithTop Int) < ord K (q.quadratic u))
      (hvHigh : (R : WithTop Int) < ord K (q.quadratic v))
      (hsumOrder : ord K (q.quadratic (u + v)) =
        (R : WithTop Int)) : False := by
    have hpair := beliLemma319 (q := q) u v R huHigh hvHigh hsumOrder
    have hscale : R - ramificationIndex K =
        S.reflectionScaleOrder := by
      simp only [R]
      omega
    rw [hscale] at hpair
    exact hnoHyperbolic ⟨u, v, hu, hv, hpair⟩
  have hstrict' :=
    S.ord_quadratic_head_sub_or_add_gt_of_low_not_isNormGenerator
      hB x' hx' heq' hlow hnotGenerator
  have hstrict'' :=
    S.ord_quadratic_head_sub_or_add_gt_of_low_not_isNormGenerator
      hB x'' hx''L heq'' hlow hnotGenerator''
  rcases hstrict' with hsub' | hadd' <;>
    rcases hstrict'' with hsub'' | hadd''
  · have htSubHigh : (R : WithTop Int) <
        ord K (q.quadratic (t (b.head - x'))) := by
      rw [htQuadratic]
      simpa only [R] using hsub'
    have hnegHigh : (R : WithTop Int) <
        ord K (q.quadratic (-(t (b.head - x')))) := by
      rw [q.quadratic_neg]
      exact htSubHigh
    have hsum : -(t (b.head - x')) + (b.head - x'') =
        b.head - x := by
      rw [htSub]
      abel
    apply hyperbolicContradiction
      (-(t (b.head - x'))) (b.head - x'')
      (S.intermediateLattice.neg_mem htSubIntermediate)
      hheadSubX''Intermediate hnegHigh (by simpa only [R] using hsub'')
    rw [hsum]
    exact hcriticalSub
  · have htSubHigh : (R : WithTop Int) <
        ord K (q.quadratic (t (b.head - x'))) := by
      rw [htQuadratic]
      simpa only [R] using hsub'
    have hsum : t (b.head - x') + (b.head + x'') =
        b.head + x := by
      rw [htSub]
      abel
    apply hyperbolicContradiction
      (t (b.head - x')) (b.head + x'')
      htSubIntermediate hheadAddX''Intermediate htSubHigh
      (by simpa only [R] using hadd'')
    rw [hsum]
    exact hcriticalAdd
  · have htAddHigh : (R : WithTop Int) <
        ord K (q.quadratic (t (b.head + x'))) := by
      rw [htQuadratic]
      simpa only [R] using hadd'
    have hsum : t (b.head + x') + (b.head - x'') =
        b.head + x := by
      rw [htAdd]
      abel
    apply hyperbolicContradiction
      (t (b.head + x')) (b.head - x'')
      htAddIntermediate hheadSubX''Intermediate htAddHigh
      (by simpa only [R] using hsub'')
    rw [hsum]
    exact hcriticalAdd
  · have htAddHigh : (R : WithTop Int) <
        ord K (q.quadratic (t (b.head + x'))) := by
      rw [htQuadratic]
      simpa only [R] using hadd'
    have hnegHigh : (R : WithTop Int) <
        ord K (q.quadratic (-(t (b.head + x')))) := by
      rw [q.quadratic_neg]
      exact htAddHigh
    have hsum : -(t (b.head + x')) + (b.head + x'') =
        b.head - x := by
      rw [htAdd]
      abel
    apply hyperbolicContradiction
      (-(t (b.head + x'))) (b.head + x'')
      (S.intermediateLattice.neg_mem htAddIntermediate)
      hheadAddX''Intermediate hnegHigh (by simpa only [R] using hadd'')
    rw [hsum]
    exact hcriticalSub

/-- In every high-range branch the original first tail order is no smaller
than the head order.  In the odd branch this is the nonnegativity part of
binary admissibility; the other three branches are immediate from their
explicit gaps. -/
theorem lemma62Gap_nonneg_of_highRange
    (S : b.Lemma65Setup) (hhigh : b.Lemma65HighRange S) :
    0 ≤ b.lemma62Gap := by
  rcases S.highRange_cases hhigh with
    hkZero | hodd | htwoE | hexceptional
  · change 2 * (ramificationIndex K : Int) + 1 ≤
      b.order 1 + 2 * (S.k : Int) - b.order 0 at hhigh
    simp only [hkZero, Nat.cast_zero, mul_zero, add_zero] at hhigh
    unfold lemma62Gap
    omega
  · have hadmissible :=
      b.adjacentParameter_isBinaryParameterAdmissible 0 (by simp)
    rw [← b.ordUnit_adjacentParameter_zero]
    exact hadmissible.ordUnit_nonneg_of_odd (by
      simpa only [b.ordUnit_adjacentParameter_zero] using hodd.1)
  · rw [htwoE.1]
    positivity
  · rw [hexceptional.1.1]
    have hePos : (0 : Int) < (ramificationIndex K : Int) := by
      exact_mod_cast ramificationIndex_pos K
    omega

/-- If the original projected tail already has norm order at least
`R₁+2e`, its ordinary scale bound controls every projected pairing at
order `R₁+e`. -/
theorem tail_pairing_mem_powerIdeal_of_gap_ge_two_e
    (S : b.Lemma65Setup) (x z : V) (hx : x ∈ L) (hz : z ∈ L)
    (hgap : b.order 0 + 2 * (ramificationIndex K : Int) ≤
      b.order 1) :
    (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
        (S.projection x) (S.projection z) ∈
      Lattice.powerIdeal (K := K)
        (b.order 0 + ramificationIndex K) := by
  have hnorm : Lattice.normIdeal
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic) =
        Lattice.powerIdeal (K := K) (b.order 1) := by
    rw [b.tail.normIdeal_eq_powerIdeal_order_zero]
    congr 1
    rw [b.order_tail]
    congr 1
  have hscaleBase :=
    Lattice.scaleIdeal_le_powerIdeal_sub_ramification_of_normIdeal_eq
      (p := q.orthogonalSpace b.head b.head_isAnisotropic)
      (M := L.projectedLattice q b.head b.head_isAnisotropic)
      (b.order 1) hnorm
  have hscale : Lattice.scaleIdeal
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic) ≤
        Lattice.powerIdeal (K := K)
          (b.order 0 + ramificationIndex K) :=
    hscaleBase.trans (by
      rw [Lattice.powerIdeal_le_iff]
      omega)
  exact hscale (Lattice.bilin_mem_scaleIdeal_of_mem
    (q.orthogonalSpace b.head b.head_isAnisotropic)
    (L.projectedLattice q b.head b.head_isAnisotropic)
    (S.projection_mem_tail x hx) (S.projection_mem_tail z hz))

/-- Mixed pairing estimate for a vector in a head-rescaled projected tail.
The original tail is split after its unary head.  The rescaling raises the
unary pairing, while `2 sK ⊆ nK` controls the unchanged deep complement.
This is the common geometric calculation in Beli's odd case and in the
`e=1`, residue-two exceptional case. -/
theorem tail_pairing_mem_powerIdeal_of_headRescale_intrinsic
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    {k : Nat} (W : b.tail.HeadRescaleWitness k)
    (y w : q.vectorOrthogonal b.head)
    (hyW : y ∈ W.lattice)
    (hw : w ∈ L.projectedLattice q b.head b.head_isAnisotropic)
    (hadjacent : b.tail.order 0 ≤ b.tail.order 1)
    (hthreshold : b.tail.order 0 + 2 * (k : Int) - 1 ≤
      b.tail.order 1)
    (m : Int)
    (hheadSum : 2 * m ≤
      (b.tail.order 0 + 2 * (k : Int)) + b.tail.order 0)
    (hdeep : m ≤ b.tail.order 1 - ramificationIndex K) :
    (q.orthogonalSpace b.head b.head_isAnisotropic).bilin y w ∈
      Lattice.powerIdeal (K := K) m := by
  rcases b.tail.beliCorollary44_i_unconditional
      hB.tail_for_lemma62.isGood (0 : Fin (n + 2)) (by simp)
      hadjacent with ⟨T⟩
  let f := T.toProductLatticeIsometry
  let u := f.toLinearEquiv.symm y
  let t := f.toLinearEquiv.symm w
  have hyOriginal : y ∈
      L.projectedLattice q b.head b.head_isAnisotropic := by
    exact (W.mem_lattice_iff_ord_ge_head_depth y).1 hyW |>.1
  have huProduct : u ∈
      Lattice.product T.left.lattice T.right.lattice := by
    exact (f.symm.map_mem y).1 hyOriginal
  have htProduct : t ∈
      Lattice.product T.left.lattice T.right.lattice := by
    exact (f.symm.map_mem w).1 hw
  have huMem := Lattice.mem_product_iff.mp huProduct
  have htMem := Lattice.mem_product_iff.mp htProduct
  have hyDecomp :
      (u.1 : q.vectorOrthogonal b.head) +
          (u.2 : q.vectorOrthogonal b.head) = y := by
    change f.toLinearEquiv u = y
    exact f.toLinearEquiv.apply_symm_apply y
  have hwDecomp :
      (t.1 : q.vectorOrthogonal b.head) +
          (t.2 : q.vectorOrthogonal b.head) = w := by
    change f.toLinearEquiv t = w
    exact f.toLinearEquiv.apply_symm_apply w
  let right := T.right.bong.castLength
    (by simp : n + 2 - ((0 : Fin (n + 2)).1 + 1) = n + 1)
  have hrightOrder : right.order 0 = b.tail.order 1 := by
    rw [BONG.order_castLength_index]
    simpa [SegmentWitness.sourceIndex] using
      T.right.order_eq
        (⟨0, by simp⟩ : Fin (n + 2 - ((0 : Fin (n + 2)).1 + 1)))
  have hrightNorm :
      Lattice.normIdeal
          ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
            T.right.carrier T.right.nondegenerate)
          T.right.lattice =
        Lattice.powerIdeal (K := K) (b.tail.order 1) := by
    rw [right.normIdeal_eq_powerIdeal_order_zero, hrightOrder]
  have huRightQuadratic :
      ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
        T.right.carrier T.right.nondegenerate).quadratic u.2 ∈
        Lattice.powerIdeal (K := K) (b.tail.order 1) := by
    have h := Lattice.quadratic_mem_normIdeal_of_mem
      ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
        T.right.carrier T.right.nondegenerate)
      T.right.lattice huMem.2
    rwa [hrightNorm] at h
  have huRightOrder : (b.tail.order 1 : WithTop Int) ≤
      ord K ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
        (u.2 : q.vectorOrthogonal b.head)) := by
    exact (Lattice.mem_powerIdeal_iff (K := K) (b.tail.order 1)
      ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
        (u.2 : q.vectorOrthogonal b.head))).1 (by
          exact huRightQuadratic)
  have huRightOriginal : (u.2 : q.vectorOrthogonal b.head) ∈
      L.projectedLattice q b.head b.head_isAnisotropic :=
    T.coe_right_mem u.2 huMem.2
  have huRightW : (u.2 : q.vectorOrthogonal b.head) ∈ W.lattice := by
    rw [W.mem_lattice_iff_ord_ge_head_depth]
    refine ⟨huRightOriginal, ?_⟩
    exact (show
      ((b.tail.order 0 + 2 * (k : Int) - 1 : Int) : WithTop Int) ≤
        (b.tail.order 1 : WithTop Int) by exact_mod_cast hthreshold).trans
          huRightOrder
  have huLeftW : (u.1 : q.vectorOrthogonal b.head) ∈ W.lattice := by
    have hsub := W.lattice.sub_mem hyW huRightW
    have heq : (u.1 : q.vectorOrthogonal b.head) =
        y - (u.2 : q.vectorOrthogonal b.head) := by
      rw [← hyDecomp]
      abel
    rwa [heq]
  have huLeftQuadratic :
      ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
        T.left.carrier T.left.nondegenerate).quadratic u.1 ∈
        Lattice.powerIdeal (K := K)
          (b.tail.order 0 + 2 * (k : Int)) := by
    have h := Lattice.quadratic_mem_normIdeal_of_mem
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      W.lattice huLeftW
    rw [W.bong.normIdeal_eq_powerIdeal_order_zero,
      W.order_zero_eq] at h
    exact h
  have hleftFinrank : finrank K T.left.carrier = 1 := by
    have h := T.left.bong.length_eq_finrank
    change 1 = finrank K T.left.carrier at h
    exact h.symm
  have hleftOrder : T.left.bong.order 0 = b.tail.order 0 := by
    simpa [SegmentWitness.sourceIndex] using
      T.left.order_eq (0 : Fin 1)
  have hleftNorm :
      Lattice.normIdeal
          ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
            T.left.carrier T.left.nondegenerate)
          T.left.lattice =
        Lattice.powerIdeal (K := K) (b.tail.order 0) := by
    rw [T.left.bong.normIdeal_eq_powerIdeal_order_zero, hleftOrder]
  have htLeftQuadratic :
      ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
        T.left.carrier T.left.nondegenerate).quadratic t.1 ∈
        Lattice.powerIdeal (K := K) (b.tail.order 0) := by
    have h := Lattice.quadratic_mem_normIdeal_of_mem
      ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
        T.left.carrier T.left.nondegenerate)
      T.left.lattice htMem.1
    rwa [hleftNorm] at h
  have hpairLeft :
      (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
          (u.1 : q.vectorOrthogonal b.head)
          (t.1 : q.vectorOrthogonal b.head) ∈
        Lattice.powerIdeal (K := K) m :=
    BONG.bilin_mem_powerIdeal_of_finrank_eq_one_of_sum
      ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
        T.left.carrier T.left.nondegenerate)
      hleftFinrank m (b.tail.order 0 + 2 * (k : Int))
      (b.tail.order 0) u.1 t.1 huLeftQuadratic htLeftQuadratic
      hheadSum
  have hrightScaleBase :=
    Lattice.scaleIdeal_le_powerIdeal_sub_ramification_of_normIdeal_eq
      (p := (q.orthogonalSpace b.head b.head_isAnisotropic).restrict
        T.right.carrier T.right.nondegenerate)
      (M := T.right.lattice) (b.tail.order 1) hrightNorm
  have hrightScale :
      Lattice.scaleIdeal
          ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
            T.right.carrier T.right.nondegenerate)
          T.right.lattice ≤
        Lattice.powerIdeal (K := K) m :=
    hrightScaleBase.trans (by
      rw [Lattice.powerIdeal_le_iff]
      exact hdeep)
  have hpairRight :
      (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
          (u.2 : q.vectorOrthogonal b.head)
          (t.2 : q.vectorOrthogonal b.head) ∈
        Lattice.powerIdeal (K := K) m :=
    hrightScale (Lattice.bilin_mem_scaleIdeal_of_mem
      ((q.orthogonalSpace b.head b.head_isAnisotropic).restrict
        T.right.carrier T.right.nondegenerate)
      T.right.lattice huMem.2 htMem.2)
  rw [← hyDecomp, ← hwDecomp,
    LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.add_right,
    T.left_right_orthogonal u.1 t.2,
    T.right_left_orthogonal u.2 t.1]
  simp only [add_zero, zero_add]
  exact (Lattice.powerIdeal (K := K) m).add_mem hpairLeft hpairRight

/-- Compatibility wrapper for the concrete-setup API. -/
theorem tail_pairing_mem_powerIdeal_of_headRescale
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    {k : Nat} (W : b.tail.HeadRescaleWitness k)
    (y w : q.vectorOrthogonal b.head)
    (hyW : y ∈ W.lattice)
    (hw : w ∈ L.projectedLattice q b.head b.head_isAnisotropic)
    (hadjacent : b.tail.order 0 ≤ b.tail.order 1)
    (hthreshold : b.tail.order 0 + 2 * (k : Int) - 1 ≤
      b.tail.order 1)
    (m : Int)
    (hheadSum : 2 * m ≤
      (b.tail.order 0 + 2 * (k : Int)) + b.tail.order 0)
    (hdeep : m ≤ b.tail.order 1 - ramificationIndex K) :
    (q.orthogonalSpace b.head b.head_isAnisotropic).bilin y w ∈
      Lattice.powerIdeal (K := K) m :=
  tail_pairing_mem_powerIdeal_of_headRescale_intrinsic
    b hB W y w hyW hw hadjacent hthreshold m hheadSum hdeep

/-- Tail estimate in Beli's odd high branch.  Property B separates the
third BONG value by at least `2e+1`; the least rescaling supplies exactly
the extra depth required in the unary first tail block. -/
theorem tail_pairing_mem_powerIdeal_of_high_odd
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x z : V) (hx : x ∈ L) (hz : z ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hgapOdd : Odd b.lemma62Gap)
    (hfinal : b.lemma62Gap + 2 * (S.k : Int) =
      2 * (ramificationIndex K : Int) + 1) :
    (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
        (S.projection x) (S.projection z) ∈
      Lattice.powerIdeal (K := K)
        (b.order 0 + ramificationIndex K) := by
  have hgapNonneg : 0 ≤ b.lemma62Gap := by
    have hadmissible :=
      b.adjacentParameter_isBinaryParameterAdmissible 0 (by simp)
    rw [← b.ordUnit_adjacentParameter_zero]
    exact hadmissible.ordUnit_nonneg_of_odd (by
      simpa only [b.ordUnit_adjacentParameter_zero] using hgapOdd)
  have hgapUpper : b.lemma62Gap ≤
      2 * (ramificationIndex K : Int) + 1 := by
    have hkNonneg : (0 : Int) ≤ (S.k : Int) := by positivity
    omega
  have htrigger : b.propertyBTrigger (0 : Fin (n + 2)) := by
    unfold propertyBTrigger
    left
    have hsucc : (0 : Fin (n + 2)).succ =
        (1 : Fin (n + 3)) := Fin.ext rfl
    have hcast : (0 : Fin (n + 2)).castSucc =
        (0 : Fin (n + 3)) := Fin.ext rfl
    rw [hsucc, hcast]
    simpa only [lemma62Gap] using And.intro hgapUpper hgapOdd
  have hthirdGap :
      2 * (ramificationIndex K : Int) + 1 ≤
        b.order 2 - b.order 1 := by
    have hright := (hB.2 (0 : Fin (n + 2)) htrigger).2
    exact hright (2 : Fin (n + 3)) rfl
  have htailZero : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
    rw [b.order_tail]
    congr 1
  have htailOne : b.tail.order (1 : Fin (n + 2)) = b.order 2 := by
    rw [b.order_tail]
    congr 1
  have hyRescaled : S.projection x ∈ S.tailRescale.lattice :=
    S.projection_mem_tailRescale_of_high_odd
      hB x hx heq hgapOdd hfinal
  apply S.tail_pairing_mem_powerIdeal_of_headRescale hB S.tailRescale
    (S.projection x) (S.projection z) hyRescaled
    (S.projection_mem_tail z hz)
  · rw [htailZero, htailOne]
    omega
  · rw [htailZero, htailOne]
    unfold lemma62Gap at hfinal hgapNonneg
    omega
  · rw [htailZero]
    unfold lemma62Gap at hfinal hgapNonneg
    omega
  · rw [htailOne]
    unfold lemma62Gap at hgapNonneg
    omega

/-- In the exceptional residue-two branch with `e ≥ 2`, Corollary 4.4(iv)
already puts the full projected-tail scale at order at least `R₁+e`.
The two terms of its doubled scale bound are supplied respectively by
`R₂-R₁=2e-2` and Property B's two-step inequality. -/
theorem tail_pairing_mem_powerIdeal_of_exceptional_of_two_le_e_intrinsic
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (x z : V) (hx : x ∈ L) (hz : z ∈ L)
    (hgap : b.lemma62Gap =
      2 * (ramificationIndex K : Int) - 2)
    (heTwo : (2 : Int) ≤ (ramificationIndex K : Int)) :
    (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
        (b.lemma65Projection x) (b.lemma65Projection z) ∈
      Lattice.powerIdeal (K := K)
        (b.order 0 + ramificationIndex K) := by
  have hscaleDoubled := beliCorollary44_iv_unconditional
    b.tail hB.tail_for_lemma62.isGood
  have htailZero : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
    rw [b.order_tail]
    congr 1
  have htailOne : b.tail.order (1 : Fin (n + 2)) = b.order 2 := by
    rw [b.order_tail]
    congr 1
  have htwoStep := hB.twoStep_add_two_le
    (0 : Fin (n + 3)) (by simp)
  change b.order 0 + 2 ≤ b.order 2 at htwoStep
  have hbound :
      2 * (b.order 0 + ramificationIndex K) ≤
        min (2 * b.tail.order 0)
          (b.tail.order 0 + b.tail.order 1) := by
    rw [htailZero, htailOne, le_min_iff]
    unfold lemma62Gap at hgap
    constructor <;> omega
  have hscale : Lattice.scaleIdeal
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic) ≤
        Lattice.powerIdeal (K := K)
          (b.order 0 + ramificationIndex K) :=
    scaleIdeal_le_powerIdeal_of_hasDoubledScaleOrder
      hscaleDoubled hbound
  exact hscale (Lattice.bilin_mem_scaleIdeal_of_mem
    (q.orthogonalSpace b.head b.head_isAnisotropic)
    (L.projectedLattice q b.head b.head_isAnisotropic)
    (lemma65Projection_mem_tail_intrinsic b x hx)
    (lemma65Projection_mem_tail_intrinsic b z hz))

/-- Compatibility wrapper for the concrete-setup API. -/
theorem tail_pairing_mem_powerIdeal_of_exceptional_of_two_le_e
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x z : V) (hx : x ∈ L) (hz : z ∈ L)
    (hgap : b.lemma62Gap =
      2 * (ramificationIndex K : Int) - 2)
    (heTwo : (2 : Int) ≤ (ramificationIndex K : Int)) :
    (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
        (S.projection x) (S.projection z) ∈
      Lattice.powerIdeal (K := K)
        (b.order 0 + ramificationIndex K) := by
  exact tail_pairing_mem_powerIdeal_of_exceptional_of_two_le_e_intrinsic
    b hB x z hx hz hgap heTwo

/-- The last exceptional subcase is `e=1`.  Its projection lies in the
once-rescaled tail furnished by Lemma 6.5(i); the common head-rescale
estimate then gives one extra unit of pairing depth. -/
theorem tail_pairing_mem_powerIdeal_of_exceptional_of_e_eq_one
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x z : V) (hx : x ∈ L) (hz : z ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hexceptional : b.Lemma65Exceptional) (hk : S.k = 2)
    (heOne : ramificationIndex K = 1) :
    (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
        (S.projection x) (S.projection z) ∈
      Lattice.powerIdeal (K := K)
        (b.order 0 + ramificationIndex K) := by
  let E := S.exceptionalProjectionWitness hB x hx heq
    hexceptional.1 hexceptional.2.1 hexceptional.2.2 hk
  have htailZero : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
    rw [b.order_tail]
    congr 1
  have htailOne : b.tail.order (1 : Fin (n + 2)) = b.order 2 := by
    rw [b.order_tail]
    congr 1
  have htwoStep := hB.twoStep_add_two_le
    (0 : Fin (n + 3)) (by simp)
  change b.order 0 + 2 ≤ b.order 2 at htwoStep
  have hgapEq := hexceptional.1
  unfold lemma62Gap at hgapEq
  apply S.tail_pairing_mem_powerIdeal_of_headRescale hB
    E.tailRescaleOne (S.projection x) (S.projection z)
    E.projection_mem (S.projection_mem_tail z hz)
  · rw [htailZero, htailOne]
    omega
  · rw [htailZero, htailOne]
    simp only [Nat.cast_one, mul_one]
    omega
  · rw [htailZero]
    simp only [Nat.cast_one, mul_one]
    omega
  · rw [htailOne]
    omega

/-- Intrinsic `e=1` exceptional tail estimate, using the directly constructed
once-rescaled tail. -/
theorem tail_pairing_mem_powerIdeal_of_exceptional_of_e_eq_one_intrinsic
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (x z : V) (hx : x ∈ L) (hz : z ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hexceptional : b.Lemma65Exceptional)
    (heOne : ramificationIndex K = 1) :
    (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
        (b.lemma65Projection x) (b.lemma65Projection z) ∈
      Lattice.powerIdeal (K := K)
        (b.order 0 + ramificationIndex K) := by
  let E := exceptionalProjectionWitnessIntrinsic b hB x hx heq
    hexceptional.1 hexceptional.2.1 hexceptional.2.2
  have htailZero : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
    rw [b.order_tail]
    congr 1
  have htailOne : b.tail.order (1 : Fin (n + 2)) = b.order 2 := by
    rw [b.order_tail]
    congr 1
  have htwoStep := hB.twoStep_add_two_le
    (0 : Fin (n + 3)) (by simp)
  change b.order 0 + 2 ≤ b.order 2 at htwoStep
  have hgapEq := hexceptional.1
  unfold lemma62Gap at hgapEq
  apply tail_pairing_mem_powerIdeal_of_headRescale_intrinsic b hB
    E.tailRescaleOne (b.lemma65Projection x) (b.lemma65Projection z)
    E.projection_mem (lemma65Projection_mem_tail_intrinsic b z hz)
  · rw [htailZero, htailOne]
    omega
  · rw [htailZero, htailOne]
    simp only [Nat.cast_one, mul_one]
    omega
  · rw [htailZero]
    simp only [Nat.cast_one, mul_one]
    omega
  · rw [htailOne]
    omega

/-- Once the first projected-tail norm order is at least the head order,
the coefficient of every lattice vector on the anisotropic head line is
integral.  This is the intrinsic replacement for writing
`L = O x₁ ⊥ <x₂,…>` in the normalized paper proof. -/
theorem projectionCoefficient_mem_integerRing_of_head_le_tail_intrinsic
    (b : BONG V q L (n + 3)) (z : V) (hz : z ∈ L)
    (hheadTail : b.order 0 ≤ b.order 1) :
    q.bilin b.head z / q.quadratic b.head ∈ IntegerRing K := by
  let c : K := q.bilin b.head z / q.quadratic b.head
  have hzValue : q.quadratic z ∈
      Lattice.powerIdeal (K := K) (b.order 0) := by
    have h := Lattice.quadratic_mem_normIdeal_of_mem q L hz
    rwa [b.normIdeal_eq_powerIdeal_order_zero] at h
  have hprojectionValue :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (b.lemma65Projection z) ∈
        Lattice.powerIdeal (K := K) (b.order 0) := by
    have h := Lattice.quadratic_mem_normIdeal_of_mem
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic)
      (lemma65Projection_mem_tail_intrinsic b z hz)
    rw [b.tail.normIdeal_eq_powerIdeal_order_zero,
      b.order_tail] at h
    have hle : Lattice.powerIdeal (K := K) (b.order 1) ≤
        Lattice.powerIdeal (K := K) (b.order 0) := by
      rw [Lattice.powerIdeal_le_iff]
      exact hheadTail
    exact hle h
  have hdecomp := Lattice.quadratic_projection_decomposition
    q b.head b.head_isAnisotropic z
  change q.quadratic z =
      c ^ 2 * q.quadratic b.head +
        (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (b.lemma65Projection z) at hdecomp
  have hcSqHead : c ^ 2 * q.quadratic b.head ∈
      Lattice.powerIdeal (K := K) (b.order 0) := by
    have heq : c ^ 2 * q.quadratic b.head =
        q.quadratic z -
          (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
            (b.lemma65Projection z) := by
      rw [hdecomp]
      ring
    rw [heq]
    exact (Lattice.powerIdeal (K := K) (b.order 0)).sub_mem
      hzValue hprojectionValue
  change c ∈ IntegerRing K
  by_cases hcZero : c = 0
  · rw [hcZero]
    exact (IntegerRing K).zero_mem
  · apply (mem_integerRing_iff K).2
    let cu : Kˣ := Units.mk0 c hcZero
    have hcOrder : ord K c = (ordUnit K cu : WithTop Int) := by
      simpa only [cu, Units.val_mk0] using (coe_ordUnit K cu).symm
    have horder := (Lattice.mem_powerIdeal_iff (K := K) (b.order 0)
      (c ^ 2 * q.quadratic b.head)).1 hcSqHead
    rw [ord_mul, ord_pow, hcOrder,
      ← b.value_zero_eq_quadratic_head, ← b.coe_order] at horder
    change 0 ≤ ord K c
    rw [hcOrder]
    simp only [two_nsmul] at horder
    norm_cast at horder ⊢
    omega

/-- Compatibility wrapper for the concrete-setup API. -/
theorem projectionCoefficient_mem_integerRing_of_head_le_tail
    (S : b.Lemma65Setup) (z : V) (hz : z ∈ L)
    (hheadTail : b.order 0 ≤ b.order 1) :
    q.bilin b.head z / q.quadratic b.head ∈ IntegerRing K :=
  projectionCoefficient_mem_integerRing_of_head_le_tail_intrinsic
    b z hz hheadTail

/-- The prescribed order of `Q(x₁-x)` is equivalent to
`ord(1-B(x₁,x)/Q(x₁))=e`. -/
theorem ord_one_sub_projectionCoefficient_eq_ramification_intrinsic
    (b : BONG V q L (n + 3)) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (horder : ord K (q.quadratic (b.head - x)) =
      ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
        WithTop Int)) :
    ord K (1 - q.bilin b.head x / q.quadratic b.head) =
      ((ramificationIndex K : Int) : WithTop Int) := by
  let a : K := q.bilin b.head x / q.quadratic b.head
  have hvalue :=
    quadratic_head_sub_eq_two_mul_one_sub_mul_intrinsic b x heq
  have honeNe : 1 - a ≠ 0 := by
    intro hzero
    have hzeroValue : q.quadratic (b.head - x) = 0 := by
      rw [hvalue]
      change 2 * (1 - a) * q.quadratic b.head = 0
      rw [hzero]
      ring
    rw [hzeroValue, ord_zero] at horder
    exact WithTop.top_ne_coe horder
  let u : Kˣ := Units.mk0 (1 - a) honeNe
  have huOrder : ord K (1 - a) = (ordUnit K u : WithTop Int) := by
    simpa only [u, Units.val_mk0] using (coe_ordUnit K u).symm
  rw [hvalue, ord_mul, ord_mul, ← ramificationIndex_spec,
    show 1 - q.bilin b.head x / q.quadratic b.head = 1 - a by rfl,
    huOrder, ← b.value_zero_eq_quadratic_head, ← b.coe_order] at horder
  rw [show 1 - q.bilin b.head x / q.quadratic b.head = 1 - a by rfl,
    huOrder]
  norm_cast at horder ⊢
  omega

/-- Compatibility wrapper for the concrete-setup API. -/
theorem ord_one_sub_projectionCoefficient_eq_ramification
    (S : b.Lemma65Setup) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (horder : ord K (q.quadratic (b.head - x)) =
      ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
        WithTop Int)) :
    ord K (1 - q.bilin b.head x / q.quadratic b.head) =
      ((ramificationIndex K : Int) : WithTop Int) :=
  ord_one_sub_projectionCoefficient_eq_ramification_intrinsic
    b x heq horder

/-- Pairing the reflection vector with a lattice vector separates into its
integral head coefficient and its orthogonal projected-tail pairing. -/
theorem bilin_head_sub_projection_decomposition_intrinsic
    (b : BONG V q L (n + 3)) (x z : V) :
    q.bilin (b.head - x) z =
      (1 - q.bilin b.head x / q.quadratic b.head) *
          (q.bilin b.head z / q.quadratic b.head) *
            q.quadratic b.head -
        (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
          (b.lemma65Projection x) (b.lemma65Projection z) := by
  let a : K := q.bilin b.head x / q.quadratic b.head
  let c : K := q.bilin b.head z / q.quadratic b.head
  have hdecomp := q.bilin_projection_decomposition
    b.head b.head_isAnisotropic x z
  change q.bilin x z = a * c * q.quadratic b.head +
      (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
        (b.lemma65Projection x) (b.lemma65Projection z) at hdecomp
  have hhead : q.bilin b.head z = c * q.quadratic b.head := by
    dsimp only [c]
    exact (div_mul_cancel₀ _ b.head_isAnisotropic).symm
  change q.bilin (b.head - x) z =
    (1 - a) * c * q.quadratic b.head -
      (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
        (b.lemma65Projection x) (b.lemma65Projection z)
  rw [LinearMap.BilinForm.sub_left, hhead, hdecomp]
  ring

/-- Compatibility wrapper for the concrete-setup API. -/
theorem bilin_head_sub_projection_decomposition
    (S : b.Lemma65Setup) (x z : V) :
    q.bilin (b.head - x) z =
      (1 - q.bilin b.head x / q.quadratic b.head) *
          (q.bilin b.head z / q.quadratic b.head) *
            q.quadratic b.head -
        (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
          (S.projection x) (S.projection z) :=
  bilin_head_sub_projection_decomposition_intrinsic b x z

/-- Reduction of Lemma 6.5(iv) to its sole tail estimate. -/
theorem head_sub_mem_scaleTruncation_of_tail_pairing
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hhigh : b.Lemma65HighRange S)
    (horder : ord K (q.quadratic (b.head - x)) =
      ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
        WithTop Int))
    (htail : ∀ z : V, z ∈ L →
      (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
          (S.projection x) (S.projection z) ∈
        Lattice.powerIdeal (K := K)
          (b.order 0 + ramificationIndex K)) :
    b.head - x ∈ Lattice.scaleTruncation q L
      (b.order 0 + ramificationIndex K) := by
  have hgapNonneg := S.lemma62Gap_nonneg_of_highRange hhigh
  have hheadTail : b.order 0 ≤ b.order 1 := by
    simpa only [lemma62Gap] using (sub_nonneg.mp hgapNonneg)
  have honeOrder :=
    S.ord_one_sub_projectionCoefficient_eq_ramification x heq horder
  apply Lattice.mem_scaleTruncation_of_pairing_mem_powerIdeal
    (L.sub_mem b.head_isNormGenerator.mem hx)
  intro z hz
  let c : K := q.bilin b.head z / q.quadratic b.head
  have hcIntegral : c ∈ IntegerRing K := by
    simpa only [c] using
      S.projectionCoefficient_mem_integerRing_of_head_le_tail
        z hz hheadTail
  have hcOrder : 0 ≤ ord K c :=
    (mem_integerRing_iff K).1 hcIntegral
  have hheadTerm :
      (1 - q.bilin b.head x / q.quadratic b.head) * c *
          q.quadratic b.head ∈
        Lattice.powerIdeal (K := K)
          (b.order 0 + ramificationIndex K) := by
    rw [Lattice.mem_powerIdeal_iff, ord_mul, ord_mul, honeOrder,
      ← b.value_zero_eq_quadratic_head, ← b.coe_order]
    calc
      ((b.order 0 + ramificationIndex K : Int) : WithTop Int) =
          ((ramificationIndex K : Int) : WithTop Int) +
            (0 : WithTop Int) + (b.order 0 : WithTop Int) := by
              norm_cast
              omega
      _ ≤ ((ramificationIndex K : Int) : WithTop Int) +
            ord K c + (b.order 0 : WithTop Int) :=
          add_le_add (add_le_add le_rfl hcOrder) le_rfl
  rw [S.bilin_head_sub_projection_decomposition x z]
  exact (Lattice.powerIdeal (K := K)
    (b.order 0 + ramificationIndex K)).sub_mem
      hheadTerm (htail z hz)

/-- Intrinsic reduction of Lemma 6.5(iv) to the projected-tail pairing
estimate.  The caller supplies the nonnegativity of the first gap directly. -/
theorem head_sub_mem_scaleTruncation_of_tail_pairing_intrinsic
    (b : BONG V q L (n + 3)) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hgapNonneg : 0 ≤ b.lemma62Gap)
    (horder : ord K (q.quadratic (b.head - x)) =
      ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
        WithTop Int))
    (htail : ∀ z : V, z ∈ L →
      (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
          (b.lemma65Projection x) (b.lemma65Projection z) ∈
        Lattice.powerIdeal (K := K)
          (b.order 0 + ramificationIndex K)) :
    b.head - x ∈ Lattice.scaleTruncation q L
      (b.order 0 + ramificationIndex K) := by
  have hheadTail : b.order 0 ≤ b.order 1 := by
    simpa only [lemma62Gap] using (sub_nonneg.mp hgapNonneg)
  have honeOrder :=
    ord_one_sub_projectionCoefficient_eq_ramification_intrinsic
      b x heq horder
  apply Lattice.mem_scaleTruncation_of_pairing_mem_powerIdeal
    (L.sub_mem b.head_isNormGenerator.mem hx)
  intro z hz
  let c : K := q.bilin b.head z / q.quadratic b.head
  have hcIntegral : c ∈ IntegerRing K := by
    simpa only [c] using
      projectionCoefficient_mem_integerRing_of_head_le_tail_intrinsic
        b z hz hheadTail
  have hcOrder : 0 ≤ ord K c :=
    (mem_integerRing_iff K).1 hcIntegral
  have hheadTerm :
      (1 - q.bilin b.head x / q.quadratic b.head) * c *
          q.quadratic b.head ∈
        Lattice.powerIdeal (K := K)
          (b.order 0 + ramificationIndex K) := by
    rw [Lattice.mem_powerIdeal_iff, ord_mul, ord_mul, honeOrder,
      ← b.value_zero_eq_quadratic_head, ← b.coe_order]
    calc
      ((b.order 0 + ramificationIndex K : Int) : WithTop Int) =
          ((ramificationIndex K : Int) : WithTop Int) +
            (0 : WithTop Int) + (b.order 0 : WithTop Int) := by
              norm_cast
              omega
      _ ≤ ((ramificationIndex K : Int) : WithTop Int) +
            ord K c + (b.order 0 : WithTop Int) :=
          add_le_add (add_le_add le_rfl hcOrder) le_rfl
  rw [bilin_head_sub_projection_decomposition_intrinsic b x z]
  exact (Lattice.powerIdeal (K := K)
    (b.order 0 + ramificationIndex K)).sub_mem
      hheadTerm (htail z hz)

/-- Exhaustive projected-tail estimate in the high range of Lemma 6.5(iv).
The four alternatives are exactly cases (1), (2), and the two residue-two
subcases of case (5) in Beli's proof. -/
theorem tail_pairing_mem_powerIdeal_of_high
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x z : V) (hx : x ∈ L) (hz : z ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hhigh : b.Lemma65HighRange S) :
    (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
        (S.projection x) (S.projection z) ∈
      Lattice.powerIdeal (K := K)
        (b.order 0 + ramificationIndex K) := by
  rcases S.highRange_cases hhigh with
    hkZero | hodd | htwoE | hexceptional
  · apply S.tail_pairing_mem_powerIdeal_of_gap_ge_two_e x z hx hz
    change 2 * (ramificationIndex K : Int) + 1 ≤
      b.order 1 + 2 * (S.k : Int) - b.order 0 at hhigh
    simp only [hkZero, Nat.cast_zero, mul_zero, add_zero] at hhigh
    omega
  · exact S.tail_pairing_mem_powerIdeal_of_high_odd
      hB x z hx hz heq hodd.1 hodd.2
  · apply S.tail_pairing_mem_powerIdeal_of_gap_ge_two_e x z hx hz
    unfold lemma62Gap at htwoE
    omega
  · by_cases heTwo : (2 : Int) ≤ (ramificationIndex K : Int)
    · exact S.tail_pairing_mem_powerIdeal_of_exceptional_of_two_le_e
        hB x z hx hz hexceptional.1.1 heTwo
    · have hePos : (0 : Int) < (ramificationIndex K : Int) := by
        exact_mod_cast ramificationIndex_pos K
      have heOneInt : (ramificationIndex K : Int) = 1 := by omega
      have heOne : ramificationIndex K = 1 := by exact_mod_cast heOneInt
      exact S.tail_pairing_mem_powerIdeal_of_exceptional_of_e_eq_one
        hB x z hx hz heq hexceptional.1 hexceptional.2 heOne

/-- Unconditional proof of Beli (2003), Lemma 6.5(iv). -/
theorem high_reflection_integral_proved
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hhigh : b.Lemma65HighRange S)
    (horder : ord K (q.quadratic (b.head - x)) =
      ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
        WithTop Int)) :
    Lattice.IsIntegralReflection (L := L)
      (lemma65Difference_isAnisotropic_of_order_eq b x horder) := by
  have htail : ∀ z : V, z ∈ L →
      (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
          (S.projection x) (S.projection z) ∈
        Lattice.powerIdeal (K := K)
          (b.order 0 + ramificationIndex K) := by
    intro z hz
    exact S.tail_pairing_mem_powerIdeal_of_high
      hB x z hx hz heq hhigh
  have hscale := S.head_sub_mem_scaleTruncation_of_tail_pairing
    x hx heq hhigh horder htail
  apply Lattice.isIntegralReflection_of_mem_scaleTruncation hscale
  convert horder using 1 <;> norm_cast <;> omega

/-- Paper-faithful exceptional branch of Beli (2003), Lemma 6.5(iv).  It uses
the once-rescaled tail directly and has no concrete setup at exponent two. -/
theorem exceptional_reflection_integral_proved
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hexceptional : b.Lemma65Exceptional)
    (horder : ord K (q.quadratic (b.head - x)) =
      ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
        WithTop Int)) :
    Lattice.IsIntegralReflection (L := L)
      (lemma65Difference_isAnisotropic_of_order_eq b x horder) := by
  have hePos : (0 : Int) < (ramificationIndex K : Int) := by
    exact_mod_cast ramificationIndex_pos K
  have hgapNonneg : 0 ≤ b.lemma62Gap := by
    rw [hexceptional.1]
    omega
  have htail : ∀ z : V, z ∈ L →
      (q.orthogonalSpace b.head b.head_isAnisotropic).bilin
          (b.lemma65Projection x) (b.lemma65Projection z) ∈
        Lattice.powerIdeal (K := K)
          (b.order 0 + ramificationIndex K) := by
    intro z hz
    by_cases heTwo : (2 : Int) ≤ (ramificationIndex K : Int)
    · exact
        tail_pairing_mem_powerIdeal_of_exceptional_of_two_le_e_intrinsic
          b hB x z hx hz hexceptional.1 heTwo
    · have heOneInt : (ramificationIndex K : Int) = 1 := by omega
      have heOne : ramificationIndex K = 1 := by exact_mod_cast heOneInt
      exact
        tail_pairing_mem_powerIdeal_of_exceptional_of_e_eq_one_intrinsic
          b hB x z hx hz heq hexceptional heOne
  have hscale := head_sub_mem_scaleTruncation_of_tail_pairing_intrinsic
    b x hx heq hgapNonneg horder htail
  apply Lattice.isIntegralReflection_of_mem_scaleTruncation hscale
  convert horder using 1 <;> norm_cast <;> omega

/-- Concrete, unconditional realization of all four parts of Beli (2003),
Lemma 6.5. -/
noncomputable instance beliLemma65LawsProved :
    BeliLemma65Laws.{u, v} K where
  projection_alternative b hB S x hx heq :=
    projection_alternative_proved b hB S x hx heq
  low_reflection b hB S x hx heq hlow hgenerator :=
    low_reflection_proved b hB S x hx heq hlow hgenerator
  reflected_projection_generator b hB S x hx heq hlow hgenerator
      w x' hx' heq' hnotGenerator :=
    reflected_projection_generator_proved b hB S x hx heq hlow
      hgenerator w x' hx' heq' hnotGenerator
  high_reflection_integral b hB S x hx heq hhigh horder :=
    high_reflection_integral_proved b hB S x hx heq hhigh horder

end Lemma65Setup

end BONG

end Bong
