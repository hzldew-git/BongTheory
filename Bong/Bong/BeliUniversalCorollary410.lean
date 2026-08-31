/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalLemma49
import Bong.Bong.BeliUniversalMain
import Bong.Bong.DiagonalHyperbolicBlocks
import Bong.QuadraticSpace.OrthogonalSumCancellation

/-!
# Beli's odd-rank Witt-index criterion

This file formalizes Corollary 4.10 of *Universal integral quadratic forms
over dyadic local fields*.  The paper's odd target rank is written as
`2 * k + 1`, with `1 ≤ k`.  If the ambient good BONG has length
`(2 * k + (tail + 1)) + 1`, then `tail = 0` is the boundary case
`m = n + 1` from the paper.
-/

namespace Bong

open Dyadic Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace QuadraticSpace

/-- A nondegenerate finite diagonal space containing a nonzero isotropic
vector represents the standard hyperbolic plane. -/
theorem finiteDiagonal_represents_hyperbolicPlane_one_of_isotropic
    {n : Nat} (c : Fin n → K) (hc : ∀ i, c i ≠ 0)
    (hiso : DiagonalIsotropic c) :
    (finiteDiagonal c hc).Represents (hyperbolicPlane (1 : Kˣ)) := by
  classical
  rcases hiso with ⟨x, hx, hxzero⟩
  have hi : ∃ i : Fin n, x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    exact h i
  rcases hi with ⟨i, hxi⟩
  let q := finiteDiagonal c hc
  let z : Fin n → K := fun j ↦ if j = i then (c i * x i)⁻¹ else 0
  have hxz : q.bilin x z = 1 := by
    rw [finiteDiagonal_bilin_apply]
    simp only [z]
    rw [Finset.sum_eq_single i]
    · simp only [if_pos]
      field_simp [hxi, hc i]
    · intro j _hj hji
      simp [hji]
    · intro hiNot
      exact (hiNot (Finset.mem_univ i)).elim
  have hzx : q.bilin z x = 1 := by
    rw [q.isSymm.eq]
    exact hxz
  have hxx : q.bilin x x = 0 := by
    simpa only [q, finiteDiagonal_bilin_apply, diagonalQuadratic,
      pow_two, mul_assoc] using hxzero
  let lambda : K := q.bilin z z / 2
  let y : Fin n → K := z - lambda • x
  have hxy : q.bilin x y = 1 := by
    simp only [y, LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.smul_right, hxz, hxx, mul_zero, sub_zero]
  have hyx : q.bilin y x = 1 := by
    rw [q.isSymm.eq]
    exact hxy
  have hyy : q.bilin y y = 0 := by
    simp only [y, LinearMap.BilinForm.sub_left,
      LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right, hxx, hxz, hzx, mul_zero,
      sub_zero, zero_mul, lambda]
    field_simp
    ring
  let f : (Fin 2 → K) →ₗ[K] (Fin n → K) :=
    { toFun := fun v ↦ v 0 • x + v 1 • y
      map_add' := by
        intro v w
        funext j
        simp only [Pi.add_apply, Pi.smul_apply]
        ring
      map_smul' := by
        intro a v
        funext j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring }
  have hfInjective : Function.Injective f := by
    intro v w hvw
    have hone := congrArg (fun t ↦ q.bilin x t) hvw
    have hzero := congrArg (fun t ↦ q.bilin y t) hvw
    have hvone : v 1 = w 1 := by
      simpa only [f, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
        hxx, hxy, mul_zero, mul_one, zero_add] using hone
    have hvzero : v 0 = w 0 := by
      simpa only [f, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
        hyx, hyy, mul_one, mul_zero, add_zero] using hzero
    funext j
    fin_cases j
    · exact hvzero
    · exact hvone
  refine ⟨{
    toLinearMap := f
    injective := hfInjective
    map_bilin := ?_ }⟩
  intro v w
  change q.bilin (f v) (f w) = _
  rw [hyperbolicPlane_bilin_apply]
  simp only [f, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    hxx, hxy, hyx, hyy, mul_zero, mul_one, zero_mul, one_mul,
    zero_add, add_zero, Units.val_one]
  ring

end QuadraticSpace

namespace Lattice

/-- Scalar universality is exactly `1`-universality.  In the forward
direction an arbitrary integral unary lattice is identified with the
standard unary model by its one-entry BONG; the reverse direction tests
the standard unary lattice with the prescribed nonzero coefficient. -/
theorem isNUniversal_one_iff_isUniversal
    {V : Type u} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) :
    IsNUniversal.{u, u, u} q L 1 ↔ IsUniversal q L := by
  constructor
  · rintro ⟨hL, hall⟩
    rw [isUniversal_iff]
    refine ⟨hL, ?_⟩
    intro c hc
    by_cases hzero : c = 0
    · subst c
      rw [representsScalar_iff]
      exact ⟨0, L.zero_mem, QuadraticSpace.quadratic_zero q⟩
    · let a : Kˣ := Units.mk0 c hzero
      have hlineIntegral :
          IsIntegral
            (QuadraticSpace.rescaleUnit a (QuadraticSpace.line K))
            (BONG.unaryModelLattice (K := K)) := by
        rw [isIntegral_iff_forall]
        intro t ht
        have htIntegral : Dyadic.IsIntegral K t := by
          rw [BONG.mem_unaryModelLattice_iff,
            mem_integerRing_iff] at ht
          exact ht
        simp only [QuadraticSpace.rescaleUnit_quadratic,
          QuadraticSpace.line_quadratic]
        have haIntegral : Dyadic.IsIntegral K (a : K) := by
          simpa [a] using hc
        simpa [pow_two] using
          Dyadic.isIntegral_mul K haIntegral
            (Dyadic.isIntegral_mul K htIntegral htIntegral)
      have hrep := hall
        (QuadraticSpace.rescaleUnit a (QuadraticSpace.line K))
        (BONG.unaryModelLattice (K := K)) (by simp) hlineIntegral
      have hscalar :=
        (represents_unaryModel_iff_representsScalar
          (q := q) (L := L) a).1 hrep
      simpa [a] using hscalar
  · intro hL
    refine ⟨hL.isIntegral, ?_⟩
    intro W _ _ r M hrank hM
    let b : BONG W r M 1 :=
      (BONG.ofLattice r M).castLength hrank
    have hvalue : Dyadic.IsIntegral K (b.valueUnit 0 : K) := by
      have hhead := (isIntegral_iff_forall r M).1 hM
        b.head b.head_isNormGenerator.mem
      simpa only [b.coe_valueUnit, b.value_zero_eq_quadratic_head] using hhead
    have hscalar : RepresentsScalar q L (b.valueUnit 0 : K) :=
      hL.representsScalar hvalue
    have hline :
        Represents q
          (QuadraticSpace.rescaleUnit (b.valueUnit 0)
            (QuadraticSpace.line K)) L
          (BONG.unaryModelLattice (K := K)) :=
      (represents_unaryModel_iff_representsScalar
        (q := q) (L := L) (b.valueUnit 0)).2 hscalar
    exact hline.trans ⟨b.unaryModelLatticeIsometry.toRepresentation⟩

namespace QuadraticLatticeModel

/-- Exact Witt index, expressed using the splitting predicate of Lemma 4.4. -/
def HasWittIndexExactly
    (X : QuadraticLatticeModel (K := K)) (k : Nat) : Prop :=
  X.HasWittIndexAtLeast k ∧ ¬X.HasWittIndexAtLeast (k + 1)

/-- The literal test family in Corollary 4.10: integral rank-`n` lattices
whose ambient quadratic space has Witt index exactly `k`. -/
def RepresentsEveryIntegralOfRankWithWittIndexExactly
    (M : QuadraticLatticeModel (K := K)) (n k : Nat) : Prop :=
  ∀ X : QuadraticLatticeModel (K := K),
    X.rank = n → X.IsIntegral → X.HasWittIndexExactly k →
      M.Represents X

/-- A nondegenerate space of rank `2k+1` cannot split `k+1`
hyperbolic planes. -/
theorem not_hasWittIndexAtLeast_succ_of_rank_two_mul_add_one
    (X : QuadraticLatticeModel (K := K)) (k : Nat)
    (hXrank : X.rank = 2 * k + 1) :
    ¬X.HasWittIndexAtLeast (k + 1) := by
  rintro ⟨R, ⟨f⟩⟩
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup R.Carrier := R.addCommGroup
  letI : Module K R.Carrier := R.module
  have hfin := f.toLinearEquiv.finrank_eq
  change X.rank = (R.adjoinHalfHyperbolic (k + 1)).rank at hfin
  rw [rank_adjoinHalfHyperbolic] at hfin
  omega

/-- In odd rank `2k+1`, "Witt index at least `k`" and "Witt index
exactly `k`" select the same test lattices. -/
theorem representsEveryIntegralOfRankWithWittIndexExactly_iff_atLeast
    (M : QuadraticLatticeModel (K := K)) (k : Nat) :
    M.RepresentsEveryIntegralOfRankWithWittIndexExactly (2 * k + 1) k ↔
      M.RepresentsEveryIntegralOfRankWithWittIndexAtLeast (2 * k + 1) k := by
  constructor
  · intro h X hXrank hXIntegral hXWitt
    exact h X hXrank hXIntegral ⟨hXWitt,
      X.not_hasWittIndexAtLeast_succ_of_rank_two_mul_add_one k hXrank⟩
  · intro h X hXrank hXIntegral hXWitt
    exact h X hXrank hXIntegral hXWitt.1

end QuadraticLatticeModel

end Lattice

namespace BONG.GoodBONG

variable {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The paper's `H^{k+1}`, displayed as the already normalized `H^k`
followed by one standard hyperbolic plane. -/
noncomputable def universalCorollary410HyperbolicPower (k : Nat) :
    QuadraticSpace K ((Fin (2 * k) → K) × (Fin 2 → K)) :=
  (standardHalfHyperbolicDiagonalSpace (K := K) k).orthogonalSum
    (QuadraticSpace.hyperbolicPlane (1 : Kˣ))

/-- The binary residual prefix is isotropic exactly when its diagonal space
is a hyperbolic plane. -/
theorem universalFirstTwoIsotropic_iff_prefixIsometricHyperbolic
    {tail : Nat} (a : GoodBONG q L (tail + 2)) :
    a.UniversalFirstTwoIsotropic ↔
      (a.prefixDiagonalSpace 2 (by omega)).IsIsometric
        (QuadraticSpace.hyperbolicPlane (1 : Kˣ)) := by
  constructor
  · intro hiso
    have hrep :=
      QuadraticSpace.finiteDiagonal_represents_hyperbolicPlane_one_of_isotropic
        (a.prefixValues 2 (by omega))
        (fun i ↦ a.toBONG.value_ne_zero ⟨i.val, by omega⟩) hiso
    rcases hrep with ⟨f⟩
    let g := f.toIsometryOfFinrankEq (by simp)
    exact ⟨g.symm⟩
  · rintro ⟨f⟩
    let e₀ : Fin 2 → K := ![1, 0]
    let x := f.symm.toLinearEquiv e₀
    refine ⟨x, ?_, ?_⟩
    · intro hx
      have : e₀ = 0 := by
        apply f.symm.toLinearEquiv.injective
        simpa [x] using hx
      have hone : (1 : K) = 0 := congrFun this 0
      simp [e₀] at hone
    · have hmap := f.symm.map_quadratic e₀
      change diagonalQuadratic (a.prefixValues 2 (by omega))
        (f.symm.toLinearEquiv e₀) = 0
      simpa only [prefixDiagonalSpace,
        QuadraticSpace.finiteDiagonal_quadratic_apply,
        QuadraticSpace.hyperbolicPlane_quadratic_apply, e₀,
        Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero]
        using hmap

/-- A ternary residual prefix is isotropic exactly when it represents a
hyperbolic plane. -/
theorem universalFirstThreeIsotropic_iff_prefixRepresentsHyperbolic
    {tail : Nat} (a : GoodBONG q L (tail + 2)) (hthree : 0 < tail) :
    a.UniversalFirstThreeIsotropic hthree ↔
      (a.prefixDiagonalSpace 3 (by omega)).Represents
        (QuadraticSpace.hyperbolicPlane (1 : Kˣ)) := by
  constructor
  · intro hiso
    exact QuadraticSpace.finiteDiagonal_represents_hyperbolicPlane_one_of_isotropic
      (a.prefixValues 3 (by omega))
      (fun i ↦ a.toBONG.value_ne_zero ⟨i.val, by omega⟩) hiso
  · rintro ⟨f⟩
    let e₀ : Fin 2 → K := ![1, 0]
    let x := f.toLinearMap e₀
    refine ⟨x, ?_, ?_⟩
    · intro hx
      have hezero : e₀ = 0 := by
        apply f.injective
        simpa [x] using hx
      have hone : (1 : K) = 0 := congrFun hezero 0
      simp [e₀] at hone
    · have hmap := f.map_quadratic e₀
      change diagonalQuadratic (a.prefixValues 3 (by omega))
        (f.toLinearMap e₀) = 0
      simpa only [prefixDiagonalSpace,
        QuadraticSpace.finiteDiagonal_quadratic_apply,
        QuadraticSpace.hyperbolicPlane_quadratic_apply, e₀,
        Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero]
        using hmap

/-- The paper assertion
`[a₁, ..., a_{n+1}] ≅ H^{(n+1)/2}` for `n = 2k+1`. -/
def UniversalCorollary410BinaryPrefixHyperbolic
    {k tail : Nat}
    (a : GoodBONG q L ((2 * k + (tail + 1)) + 1)) : Prop :=
  (a.prefixDiagonalSpace (2 * k + 2) (by omega)).IsIsometric
    (universalCorollary410HyperbolicPower (K := K) k)

/-- The paper assertion
`H^{(n+1)/2} → [a₁, ..., a_{n+2}]` for `n = 2k+1`. -/
def UniversalCorollary410TernaryPrefixRepresentsHyperbolic
    {k tail : Nat}
    (a : GoodBONG q L ((2 * k + (tail + 1)) + 1))
    (hthree : 0 < tail) : Prop :=
  (a.prefixDiagonalSpace (2 * k + 3) (by omega)).Represents
    (universalCorollary410HyperbolicPower (K := K) k)

/-- Lemma 4.9(iii) turns residual binary isotropy into the hyperbolicity of
the corresponding ambient prefix, and Witt cancellation gives the converse. -/
theorem universalFirstTwoIsotropic_iff_corollary410BinaryPrefix
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    {k tail : Nat}
    (a : GoodBONG q L ((2 * k + (tail + 1)) + 1))
    (b : GoodBONG r M (tail + 2))
    (hprefix :
      (a.prefixDiagonalSpace (2 * k + 2) (by omega)).IsIsometric
        ((standardHalfHyperbolicDiagonalSpace (K := K) k).orthogonalSum
          (b.prefixDiagonalSpace 2 (by omega)))) :
    b.UniversalFirstTwoIsotropic ↔
      a.UniversalCorollary410BinaryPrefixHyperbolic := by
  let head := standardHalfHyperbolicDiagonalSpace (K := K) k
  let binary := b.prefixDiagonalSpace 2 (by omega)
  let hyperbolic := QuadraticSpace.hyperbolicPlane (1 : Kˣ)
  constructor
  · intro hb
    rcases hprefix with ⟨f⟩
    rcases (b.universalFirstTwoIsotropic_iff_prefixIsometricHyperbolic).1 hb
      with ⟨g⟩
    refine ⟨f.trans ((QuadraticSpace.Isometry.refl head).orthogonalSum g)⟩
  · intro ha
    rcases hprefix with ⟨f⟩
    rcases ha with ⟨g⟩
    have htail : QuadraticSpace.Isometry binary hyperbolic :=
      QuadraticSpace.orthogonalSumLeftCancel head binary hyperbolic
        (f.symm.trans g)
    exact (b.universalFirstTwoIsotropic_iff_prefixIsometricHyperbolic).2
      ⟨htail⟩

/-- Lemma 4.9(iii) turns residual ternary isotropy into representation of
`H^{k+1}` by the corresponding ambient prefix, and cancellation gives the
converse. -/
theorem universalFirstThreeIsotropic_iff_corollary410TernaryPrefix
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    {k tail : Nat}
    (a : GoodBONG q L ((2 * k + (tail + 1)) + 1))
    (b : GoodBONG r M (tail + 2)) (hthree : 0 < tail)
    (hprefix :
      (a.prefixDiagonalSpace (2 * k + 3) (by omega)).IsIsometric
        ((standardHalfHyperbolicDiagonalSpace (K := K) k).orthogonalSum
          (b.prefixDiagonalSpace 3 (by omega)))) :
    b.UniversalFirstThreeIsotropic hthree ↔
      a.UniversalCorollary410TernaryPrefixRepresentsHyperbolic hthree := by
  let head := standardHalfHyperbolicDiagonalSpace (K := K) k
  let ternary := b.prefixDiagonalSpace 3 (by omega)
  let hyperbolic := QuadraticSpace.hyperbolicPlane (1 : Kˣ)
  constructor
  · intro hb
    change (a.prefixDiagonalSpace (2 * k + 3) (by omega)).Represents
      (head.orthogonalSum hyperbolic)
    rcases hprefix with ⟨f⟩
    have htail : ternary.Represents hyperbolic :=
      (b.universalFirstThreeIsotropic_iff_prefixRepresentsHyperbolic
        hthree).1 hb
    let joined : QuadraticSpace.Representation
        (head.orthogonalSum hyperbolic) (head.orthogonalSum ternary) :=
      (QuadraticSpace.Representation.refl head).orthogonalSum
        (Classical.choice htail)
    exact ⟨f.symm.toRepresentation.trans joined⟩
  · intro ha
    change (a.prefixDiagonalSpace (2 * k + 3) (by omega)).Represents
      (head.orthogonalSum hyperbolic) at ha
    rcases hprefix with ⟨f⟩
    rcases ha with ⟨g⟩
    have htotal : (head.orthogonalSum ternary).Represents
        (head.orthogonalSum hyperbolic) :=
      ⟨f.toRepresentation.trans g⟩
    have htail : ternary.Represents hyperbolic :=
      QuadraticSpace.orthogonalSumLeftCancelRepresents
        head hyperbolic ternary htotal
    exact (b.universalFirstThreeIsotropic_iff_prefixRepresentsHyperbolic
      hthree).2 htail

/-- The right-hand side in Corollary 4.10 II(b), with paper indices
`R_{n+2}` and `R_{n+1}` and `n = 2k+1`. -/
noncomputable def universalCorollary410AlphaNPlusTwoUpperBound
    {k tail : Nat}
    (a : GoodBONG q L ((2 * k + (tail + 1)) + 1))
    (hfour : 1 < tail) : ℚ :=
  2 * ((ramificationIndex K : ℚ) -
      (((a.order ⟨2 * k + 2, by omega⟩ -
        a.order ⟨2 * k + 1, by omega⟩) / 2 : Int) : ℚ)) - 1

/-- Case I in the literal boundary-safe form of Beli's Corollary 4.10. -/
structure UniversalCorollary410CaseI
    {k tail : Nat}
    (a : GoodBONG q L ((2 * k + (tail + 1)) + 1)) : Prop where
  alphaN : a.alphaValue ⟨2 * k, by omega⟩ = 0
  binaryAtMinimalRank : tail = 0 →
    a.UniversalCorollary410BinaryPrefixHyperbolic
  binaryAboveOne : ∀ hthree : 0 < tail,
    1 < a.order ⟨2 * k + 2, by omega⟩ →
      a.UniversalCorollary410BinaryPrefixHyperbolic
  binaryAtOne : ∀ hthree : 0 < tail,
    a.order ⟨2 * k + 2, by omega⟩ = 1 →
      (tail = 1 ∨ ∃ hfour : 1 < tail,
        2 * (ramificationIndex K : Int) + 1 <
          a.order ⟨2 * k + 3, by omega⟩) →
      a.UniversalCorollary410BinaryPrefixHyperbolic

/-- Case II in the literal boundary-safe form of Beli's Corollary 4.10. -/
structure UniversalCorollary410CaseII
    {k tail : Nat}
    (a : GoodBONG q L ((2 * k + (tail + 1)) + 1)) : Prop where
  rankAtLeastNPlusTwo : 0 < tail
  alphaN : a.alphaValue ⟨2 * k, by omega⟩ = 1
  alphaNPlusTwoBound :
    (a.order ⟨2 * k + 1, by omega⟩ = 1 ∨
        1 < a.order ⟨2 * k + 2, by omega⟩) →
      ∃ hfour : 1 < tail,
        a.alphaValue ⟨2 * k + 2, by omega⟩ ≤
          a.universalCorollary410AlphaNPlusTwoUpperBound hfour
  ternaryBoundary :
    a.order ⟨2 * k + 1, by omega⟩ ≤ 0 →
    a.order ⟨2 * k + 2, by omega⟩ ≤ 1 →
    (tail = 1 ∨ ∃ hfour : 1 < tail,
      2 * (ramificationIndex K : Int) <
        a.order ⟨2 * k + 3, by omega⟩ -
          a.order ⟨2 * k + 2, by omega⟩) →
    a.UniversalCorollary410TernaryPrefixRepresentsHyperbolic
      rankAtLeastNPlusTwo

/-- The complete displayed conditions of Corollary 4.10.  The ambient BONG
length enforces the paper's `m ≥ n+1`; the first two fields are
`R₁ = R₃ = ⋯ = Rₙ = 0` and
`R₂ = R₄ = ⋯ = R_{n-1} = -2e`. -/
structure UniversalCorollary410Conditions
    (k tail : Nat)
    (a : GoodBONG q L ((2 * k + (tail + 1)) + 1)) : Prop where
  oddOrders (j : Fin (k + 1)) :
    a.order ⟨2 * j.val, by omega⟩ = 0
  evenOrders (j : Fin k) :
    a.order ⟨2 * j.val + 1, by omega⟩ =
      -2 * (ramificationIndex K : Int)
  cases : UniversalCorollary410CaseI a ∨
    UniversalCorollary410CaseII a

/-- The residual upper bound in Theorem 2.1 is exactly the shifted ambient
upper bound in Corollary 4.10. -/
theorem UniversalLemma49AdaptedData.universalAlphaThreeUpperBound_shift
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    {k tail : Nat}
    {a : GoodBONG q L ((2 * k + (tail + 1)) + 1)}
    (D : UniversalLemma49AdaptedData
      (q := q) (r := r) (L := L) (M := M) k (tail + 1) a)
    (hfour : 1 < tail) :
    D.residual.universalAlphaThreeUpperBound hfour =
      a.universalCorollary410AlphaNPlusTwoUpperBound hfour := by
  unfold universalAlphaThreeUpperBound
    universalCorollary410AlphaNPlusTwoUpperBound
  rw [D.order_shift (⟨2, by omega⟩ : Fin (tail + 2)),
    D.order_shift (⟨1, by omega⟩ : Fin (tail + 2))]

set_option maxHeartbeats 0 in
-- Expanding both complete case predicates requires unrestricted normalization.
/-- Under the splitting-adapted BONG from Lemma 4.9, Theorem 2.1's two
unary alternatives are exactly the two shifted alternatives of Corollary
4.10. -/
theorem UniversalLemma49AdaptedData.universalTheorem21Conditions_iff_tail
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    {k tail : Nat}
    {a : GoodBONG q L ((2 * k + (tail + 1)) + 1)}
    (D : UniversalLemma49AdaptedData
      (q := q) (r := r) (L := L) (M := M) k (tail + 1) a)
    (hM : Lattice.IsIntegral r M) :
    D.residual.UniversalTheorem21Conditions ↔
      a.order ⟨2 * k, by omega⟩ = 0 ∧
        (UniversalCorollary410CaseI a ∨
          UniversalCorollary410CaseII a) := by
  constructor
  · rintro ⟨hzero, hI | hII⟩
    · refine ⟨?_, Or.inl ?_⟩
      · exact (D.order_shift (0 : Fin (tail + 2))).symm.trans hzero
      · refine
          { alphaN := ?_
            binaryAtMinimalRank := ?_
            binaryAboveOne := ?_
            binaryAtOne := ?_ }
        · exact (D.alpha_shift hM (0 : Fin (tail + 1))).symm.trans
            hI.alphaOne
        · intro htail
          have hp := D.prefix_split (⟨1, by omega⟩ : Fin (tail + 2))
          exact (a.universalFirstTwoIsotropic_iff_corollary410BinaryPrefix
            D.residual hp).1 (hI.binaryRankTwo htail)
        · intro hthree horder
          have horder' : 1 < D.residual.order ⟨2, by omega⟩ := by
            rw [D.order_shift (⟨2, by omega⟩ : Fin (tail + 2))]
            exact horder
          have hp := D.prefix_split (⟨1, by omega⟩ : Fin (tail + 2))
          exact (a.universalFirstTwoIsotropic_iff_corollary410BinaryPrefix
            D.residual hp).1 (hI.binaryAboveOne hthree horder')
        · intro hthree horder hbranch
          have horder' : D.residual.order ⟨2, by omega⟩ = 1 := by
            rw [D.order_shift (⟨2, by omega⟩ : Fin (tail + 2))]
            exact horder
          have hbranch' : tail = 1 ∨ ∃ hfour : 1 < tail,
              2 * (ramificationIndex K : Int) + 1 <
                D.residual.order ⟨3, by omega⟩ := by
            rcases hbranch with htail | ⟨hfour, hlarge⟩
            · exact Or.inl htail
            · refine Or.inr ⟨hfour, ?_⟩
              rw [D.order_shift (⟨3, by omega⟩ : Fin (tail + 2))]
              exact hlarge
          have hp := D.prefix_split (⟨1, by omega⟩ : Fin (tail + 2))
          exact (a.universalFirstTwoIsotropic_iff_corollary410BinaryPrefix
            D.residual hp).1 (hI.binaryAtOne hthree horder' hbranch')
    · have htailPos := hII.rankAtLeastThree
      refine ⟨?_, Or.inr ?_⟩
      · exact (D.order_shift (0 : Fin (tail + 2))).symm.trans hzero
      · refine
          { rankAtLeastNPlusTwo := hII.rankAtLeastThree
            alphaN := ?_
            alphaNPlusTwoBound := ?_
            ternaryBoundary := ?_ }
        · exact (D.alpha_shift hM (0 : Fin (tail + 1))).symm.trans
            hII.alphaOne
        · intro hbranch
          have hbranch' :
              D.residual.order ⟨1, by omega⟩ = 1 ∨
                1 < D.residual.order ⟨2, by omega⟩ := by
            rcases hbranch with hleft | hright
            · left
              rw [D.order_shift (⟨1, by omega⟩ : Fin (tail + 2))]
              exact hleft
            · right
              rw [D.order_shift (⟨2, by omega⟩ : Fin (tail + 2))]
              exact hright
          rcases hII.alphaThreeBound hbranch' with ⟨hfour, hbound⟩
          refine ⟨hfour, ?_⟩
          rw [← D.universalAlphaThreeUpperBound_shift hfour,
            ← D.alpha_shift hM (⟨2, by omega⟩ : Fin (tail + 1))]
          exact hbound
        · intro hsecond hthird hbranch
          have hsecond' : D.residual.order ⟨1, by omega⟩ ≤ 0 := by
            rw [D.order_shift (⟨1, by omega⟩ : Fin (tail + 2))]
            exact hsecond
          have hthird' : D.residual.order ⟨2, by omega⟩ ≤ 1 := by
            rw [D.order_shift (⟨2, by omega⟩ : Fin (tail + 2))]
            exact hthird
          have hbranch' : tail = 1 ∨ ∃ hfour : 1 < tail,
              2 * (ramificationIndex K : Int) <
                D.residual.order ⟨3, by omega⟩ -
                  D.residual.order ⟨2, by omega⟩ := by
            rcases hbranch with htail | ⟨hfour, hlarge⟩
            · exact Or.inl htail
            · refine Or.inr ⟨hfour, ?_⟩
              rw [D.order_shift (⟨3, by omega⟩ : Fin (tail + 2)),
                D.order_shift (⟨2, by omega⟩ : Fin (tail + 2))]
              exact hlarge
          have hp := D.prefix_split (⟨2, by omega⟩ : Fin (tail + 2))
          exact (a.universalFirstThreeIsotropic_iff_corollary410TernaryPrefix
            D.residual hII.rankAtLeastThree hp).1
              (hII.ternaryBoundary hsecond' hthird' hbranch')
  · rintro ⟨hzero, hI | hII⟩
    · refine ⟨?_, Or.inl ?_⟩
      · exact (D.order_shift (0 : Fin (tail + 2))).trans hzero
      · refine
          { alphaOne := ?_
            binaryRankTwo := ?_
            binaryAboveOne := ?_
            binaryAtOne := ?_ }
        · exact (D.alpha_shift hM (0 : Fin (tail + 1))).trans hI.alphaN
        · intro htail
          have hp := D.prefix_split (⟨1, by omega⟩ : Fin (tail + 2))
          exact (a.universalFirstTwoIsotropic_iff_corollary410BinaryPrefix
            D.residual hp).2 (hI.binaryAtMinimalRank htail)
        · intro hthree horder
          have horder' : 1 < a.order ⟨2 * k + 2, by omega⟩ := by
            rw [← D.order_shift (⟨2, by omega⟩ : Fin (tail + 2))]
            exact horder
          have hp := D.prefix_split (⟨1, by omega⟩ : Fin (tail + 2))
          exact (a.universalFirstTwoIsotropic_iff_corollary410BinaryPrefix
            D.residual hp).2 (hI.binaryAboveOne hthree horder')
        · intro hthree horder hbranch
          have horder' : a.order ⟨2 * k + 2, by omega⟩ = 1 := by
            rw [← D.order_shift (⟨2, by omega⟩ : Fin (tail + 2))]
            exact horder
          have hbranch' : tail = 1 ∨ ∃ hfour : 1 < tail,
              2 * (ramificationIndex K : Int) + 1 <
                a.order ⟨2 * k + 3, by omega⟩ := by
            rcases hbranch with htail | ⟨hfour, hlarge⟩
            · exact Or.inl htail
            · refine Or.inr ⟨hfour, ?_⟩
              rw [← D.order_shift (⟨3, by omega⟩ : Fin (tail + 2))]
              exact hlarge
          have hp := D.prefix_split (⟨1, by omega⟩ : Fin (tail + 2))
          exact (a.universalFirstTwoIsotropic_iff_corollary410BinaryPrefix
            D.residual hp).2 (hI.binaryAtOne hthree horder' hbranch')
    · have htailPos := hII.rankAtLeastNPlusTwo
      refine ⟨?_, Or.inr ?_⟩
      · exact (D.order_shift (0 : Fin (tail + 2))).trans hzero
      · refine
          { rankAtLeastThree := hII.rankAtLeastNPlusTwo
            alphaOne := ?_
            alphaThreeBound := ?_
            ternaryBoundary := ?_ }
        · exact (D.alpha_shift hM (0 : Fin (tail + 1))).trans hII.alphaN
        · intro hbranch
          have hbranch' :
              a.order ⟨2 * k + 1, by omega⟩ = 1 ∨
                1 < a.order ⟨2 * k + 2, by omega⟩ := by
            rcases hbranch with hleft | hright
            · left
              rw [← D.order_shift (⟨1, by omega⟩ : Fin (tail + 2))]
              exact hleft
            · right
              rw [← D.order_shift (⟨2, by omega⟩ : Fin (tail + 2))]
              exact hright
          rcases hII.alphaNPlusTwoBound hbranch' with ⟨hfour, hbound⟩
          refine ⟨hfour, ?_⟩
          rw [D.universalAlphaThreeUpperBound_shift hfour,
            D.alpha_shift hM (⟨2, by omega⟩ : Fin (tail + 1))]
          exact hbound
        · intro hsecond hthird hbranch
          have hsecond' : a.order ⟨2 * k + 1, by omega⟩ ≤ 0 := by
            rw [← D.order_shift (⟨1, by omega⟩ : Fin (tail + 2))]
            exact hsecond
          have hthird' : a.order ⟨2 * k + 2, by omega⟩ ≤ 1 := by
            rw [← D.order_shift (⟨2, by omega⟩ : Fin (tail + 2))]
            exact hthird
          have hbranch' : tail = 1 ∨ ∃ hfour : 1 < tail,
              2 * (ramificationIndex K : Int) <
                a.order ⟨2 * k + 3, by omega⟩ -
                  a.order ⟨2 * k + 2, by omega⟩ := by
            rcases hbranch with htail | ⟨hfour, hlarge⟩
            · exact Or.inl htail
            · refine Or.inr ⟨hfour, ?_⟩
              rw [← D.order_shift (⟨3, by omega⟩ : Fin (tail + 2)),
                ← D.order_shift (⟨2, by omega⟩ : Fin (tail + 2))]
              exact hlarge
          have hp := D.prefix_split (⟨2, by omega⟩ : Fin (tail + 2))
          exact (a.universalFirstThreeIsotropic_iff_corollary410TernaryPrefix
            D.residual hII.rankAtLeastNPlusTwo hp).2
              (hII.ternaryBoundary hsecond' hthird' hbranch')

/-- The alternating order part of Corollary 4.10 supplies precisely the
splitting conditions of Lemma 4.8.  Its final odd equality is the
non-boundary endpoint alternative. -/
theorem UniversalCorollary410Conditions.toUniversalLemma48Conditions
    {k tail : Nat}
    {a : GoodBONG q L ((2 * k + (tail + 1)) + 1)}
    (h : UniversalCorollary410Conditions k tail a) :
    UniversalLemma48Conditions a k := by
  refine
    { bound := by omega
      oddOrders := ?_
      evenOrders := ?_
      endpoint := ?_ }
  · intro j
    exact h.oddOrders ⟨j.val, by omega⟩
  · exact h.evenOrders
  · right
    refine ⟨by omega, ?_⟩
    exact h.oddOrders ⟨k, by omega⟩

set_option maxHeartbeats 0 in
-- The final equivalence composes the full splitting and residual case analyses.
/-- Beli, Corollary 4.10.  For odd target rank `n = 2k+1`, an integral
lattice with the displayed good BONG represents every integral rank-`n`
lattice whose ambient space has Witt index exactly `k` if and only if the
paper's alternating orders and its two explicit tail alternatives hold.

The ambient length is `2k + tail + 2`, so `tail = 0` is exactly the paper's
boundary case `m = n+1`. -/
theorem beliUniversalCorollary410
    {k tail : Nat} (hk : 1 ≤ k)
    (a : GoodBONG q L ((2 * k + (tail + 1)) + 1))
    (hL : Lattice.IsIntegral q L) :
    Lattice.QuadraticLatticeModel.RepresentsEveryIntegralOfRankWithWittIndexExactly
        (Lattice.quadraticLatticeModel q L) (2 * k + 1) k ↔
      UniversalCorollary410Conditions k tail a := by
  letI : AddCommGroup (Lattice.quadraticLatticeModel q L).Carrier :=
    (Lattice.quadraticLatticeModel q L).addCommGroup
  letI : Module K (Lattice.quadraticLatticeModel q L).Carrier :=
    (Lattice.quadraticLatticeModel q L).module
  constructor
  · intro hUniversal
    have hAtLeast :
        Lattice.QuadraticLatticeModel.RepresentsEveryIntegralOfRankWithWittIndexAtLeast
          (Lattice.quadraticLatticeModel q L) (2 * k + 1) k :=
      (Lattice.QuadraticLatticeModel.representsEveryIntegralOfRankWithWittIndexExactly_iff_atLeast
          (Lattice.quadraticLatticeModel q L) k).1 hUniversal
    obtain ⟨M', hM'Universal, ⟨presentation⟩⟩ :=
      (Lattice.beliUniversalLemma44 k (2 * k + 1) hk (by omega)
        (Lattice.quadraticLatticeModel q L) hL).1 hAtLeast
    letI : AddCommGroup M'.Carrier := M'.addCommGroup
    letI : Module K M'.Carrier := M'.module
    have hsub : (2 * k + 1) - 2 * k = 1 := by omega
    rw [hsub] at hM'Universal
    have hsplit :
        (Lattice.quadraticLatticeModel q L).SplitsHalfHyperbolic k :=
      ⟨M', ⟨presentation⟩⟩
    have h48 : UniversalLemma48Conditions a k :=
      universalLemma48Conditions_of_splitsHalfHyperbolic
        hk a hL hsplit
    let D := universalLemma49AdaptedData
      (n := tail + 1) hk a hL hM'Universal.1 presentation
    have hResidualUniversal :
        Lattice.IsUniversal M'.form M'.lattice :=
      (Lattice.isNUniversal_one_iff_isUniversal
        M'.form M'.lattice).1 hM'Universal
    have hResidualConditions :
        D.residual.UniversalTheorem21Conditions :=
      (isUniversal_iff_universalTheorem21Conditions
        D.residual hM'Universal.1).1 hResidualUniversal
    have htail :=
      (D.universalTheorem21Conditions_iff_tail hM'Universal.1).1
        hResidualConditions
    refine
      { oddOrders := ?_
        evenOrders := ?_
        cases := htail.2 }
    · intro j
      by_cases hj : j.val < k
      · exact h48.oddOrders ⟨j.val, hj⟩
      · have hjEq : j = ⟨k, by omega⟩ := by
          apply Fin.ext
          change j.val = k
          omega
        rw [hjEq]
        exact htail.1
    · exact h48.evenOrders
  · intro hConditions
    have h48 : UniversalLemma48Conditions a k :=
      hConditions.toUniversalLemma48Conditions
    obtain ⟨M', ⟨presentation⟩⟩ :=
      (beliUniversalLemma48 hk hL a).2 h48
    letI : AddCommGroup M'.Carrier := M'.addCommGroup
    letI : Module K M'.Carrier := M'.module
    letI : AddCommGroup (M'.adjoinHalfHyperbolic k).Carrier :=
      (M'.adjoinHalfHyperbolic k).addCommGroup
    letI : Module K (M'.adjoinHalfHyperbolic k).Carrier :=
      (M'.adjoinHalfHyperbolic k).module
    have htotal : (M'.adjoinHalfHyperbolic k).IsIntegral := by
      exact (Lattice.isIntegral_iff_of_latticeIsometry presentation).2 hL
    have hM'Integral : M'.IsIntegral :=
      Lattice.QuadraticLatticeModel.IsIntegral.of_adjoinHalfHyperbolic
        k htotal
    let D := universalLemma49AdaptedData
      (n := tail + 1) hk a hL hM'Integral presentation
    have hResidualConditions :
        D.residual.UniversalTheorem21Conditions :=
      (D.universalTheorem21Conditions_iff_tail hM'Integral).2
        ⟨hConditions.oddOrders ⟨k, by omega⟩, hConditions.cases⟩
    have hResidualUniversal :
        Lattice.IsUniversal M'.form M'.lattice :=
      (isUniversal_iff_universalTheorem21Conditions
        D.residual hM'Integral).2 hResidualConditions
    have hM'Universal : M'.IsNUniversal 1 :=
      (Lattice.isNUniversal_one_iff_isUniversal
        M'.form M'.lattice).2 hResidualUniversal
    have hAtLeast :
        Lattice.QuadraticLatticeModel.RepresentsEveryIntegralOfRankWithWittIndexAtLeast
          (Lattice.quadraticLatticeModel q L) (2 * k + 1) k := by
      apply (Lattice.beliUniversalLemma44 k (2 * k + 1) hk (by omega)
        (Lattice.quadraticLatticeModel q L) hL).2
      refine ⟨M', ?_, ⟨presentation⟩⟩
      have hsub : (2 * k + 1) - 2 * k = 1 := by omega
      simpa only [hsub] using hM'Universal
    exact
      (Lattice.QuadraticLatticeModel.representsEveryIntegralOfRankWithWittIndexExactly_iff_atLeast
          (Lattice.quadraticLatticeModel q L) k).2 hAtLeast

end BONG.GoodBONG

end Bong
