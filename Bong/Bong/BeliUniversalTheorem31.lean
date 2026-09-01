/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalCorollary410
import Bong.Bong.Beli2009JordanProfileInternal
import Bong.Bong.Beli2009JordanProfileBoundary
import Bong.Bong.Beli2009JordanProfileGap
import Bong.Bong.Beli2009JordanProfileWeightUpper
import Bong.Bong.Beli2009JordanSegmentIdentification
import Bong.Bong.Beli2009RepresentationBridge
import Bong.Bong.BeliLemmas45To47
import Bong.Bong.BeliLemma47Proof
import Bong.Bong.StructuralProof
import Bong.Lattice.OMaximalUniqueness
import Bong.Lattice.OmearaOddRankProper

/-!
# Beli's universal criterion in Jordan coordinates

This file formalizes Theorem 3.1 of Beli's *Universal integral quadratic
forms over dyadic local fields*.  The component count is written as `t + 1`,
so the first Jordan component is always present.  Later components are
carried by explicit `Fin` witnesses; this replaces the paper's informal
out-of-range conventions without changing any mathematical branch.

The ideals called `w_k` and `f_k` in the paper are respectively
`fundamentalWeightIdeal k` and `fundamentalIdeal k`.  Expressions beginning
with `4 p^s` are represented by the power ideal of order `2e + s`.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace QuadraticSpace

/-- Universe-polymorphic anisotropy transport for the varying prefix carrier
types occurring in a Jordan decomposition. -/
theorem Isometry.isAnisotropicSpace_iff_general
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} (f : Isometry q r) :
    q.IsAnisotropicSpace ↔ r.IsAnisotropicSpace := by
  constructor
  · intro hq y hy
    have hx : q.quadratic (f.toLinearEquiv.symm y) = 0 := by
      rw [← f.map_quadratic]
      simpa using hy
    have hzero := hq (f.toLinearEquiv.symm y) hx
    simpa using congrArg f.toLinearEquiv hzero
  · intro hr x hx
    have hy : r.quadratic (f.toLinearEquiv x) = 0 := by
      rw [f.map_quadratic, hx]
    have hzero := hr (f.toLinearEquiv x) hy
    exact f.toLinearEquiv.injective (by simpa using hzero)

/-- The paper's explicit diagonal isotropy is the negation of anisotropy of
the associated finite diagonal quadratic space. -/
theorem not_finiteDiagonal_isAnisotropicSpace_iff
    {n : Nat} (c : Fin n → K) (hc : ∀ i, c i ≠ 0) :
    ¬(finiteDiagonal c hc).IsAnisotropicSpace ↔ DiagonalIsotropic c := by
  classical
  simp only [IsAnisotropicSpace, DiagonalIsotropic,
    finiteDiagonal_quadratic_apply]
  push Not
  tauto

/-- A nondegenerate binary quadratic space is isotropic exactly when it is
isometric to the standard hyperbolic plane.  The proof diagonalizes the
space, constructs the hyperbolic representation from an isotropic vector,
and uses equal-rank rigidity. -/
theorem rankTwo_isIsometric_hyperbolicPlane_one_of_not_anisotropic
    [FiniteDimensional K V] (q : QuadraticSpace K V)
    (hrank : finrank K V = 2) (hiso : ¬q.IsAnisotropicSpace) :
    q.IsIsometric (hyperbolicPlane (1 : Kˣ)) := by
  let d := finiteDiagonal
    (fun i ↦ (q.diagonalUnits i : K))
    (fun i ↦ Units.ne_zero (q.diagonalUnits i))
  have htransport :=
    q.diagonalizationIsometry.isAnisotropicSpace_iff_general
  have hdNot : ¬d.IsAnisotropicSpace := by
    exact mt htransport.mpr hiso
  have hdIso : DiagonalIsotropic
      (fun i ↦ (q.diagonalUnits i : K)) :=
    (not_finiteDiagonal_isAnisotropicSpace_iff
      (fun i ↦ (q.diagonalUnits i : K))
      (fun i ↦ Units.ne_zero (q.diagonalUnits i))).mp hdNot
  rcases finiteDiagonal_represents_hyperbolicPlane_one_of_isotropic
      (fun i ↦ (q.diagonalUnits i : K))
      (fun i ↦ Units.ne_zero (q.diagonalUnits i)) hdIso with ⟨f⟩
  let g : Representation (hyperbolicPlane (1 : Kˣ)) q :=
    q.diagonalizationIsometry.symm.toRepresentation.trans f
  refine ⟨(g.toIsometryOfFinrankEq ?_).symm⟩
  simp [hrank]

end QuadraticSpace

namespace Lattice

/-- An integral modular lattice at the dyadic lower volume bound is already
maximal integral.  Its modular volume is `-rank * e`, while every integral
over-lattice has volume at least that value. -/
theorem isOMaximal_of_isModular_of_integral_of_order_eq_neg_ramification
    {a : Kˣ} (hmodular : IsModular q L a) (hintegral : IsIntegral q L)
    (horder : ordUnit K a = -(ramificationIndex K : Int)) :
    IsOMaximal q L := by
  refine ⟨hintegral, ?_⟩
  intro M hLM hM
  have hlower := integralShiftedVolumeOrder_nonneg hM
  have hmono := volumeOrder_mono_of_le q hLM
  have hvolumeL := hmodular.volumeOrder_eq
  have hvolumeEq : volumeOrder q L = volumeOrder q M := by
    unfold integralShiftedVolumeOrder at hlower
    rw [hvolumeL, horder] at hmono ⊢
    ring_nf at hlower hmono ⊢
    omega
  exact (eq_of_le_of_volumeOrder_eq q L M hLM hvolumeEq).symm

end Lattice

namespace BONG.GoodBONG

/-- The unit-valued exact diagonal prefix and the scalar-valued prefix used
in Theorem 2.1 are the same quadratic space. -/
theorem prefixExactDiagonalSpace_eq_prefixDiagonalSpace
    {n : Nat} (a : GoodBONG q L (n + 1)) (k : Nat) (hk : k ≤ n + 1) :
    a.prefixExactDiagonalSpace k hk = a.prefixDiagonalSpace k hk := by
  rfl

/-- Isotropy of a good-BONG prefix is unchanged when its length is replaced
by an equal natural number.  The two bound proofs are propositionally
irrelevant; spelling out this bridge keeps later boundary casts explicit. -/
theorem diagonalIsotropic_prefixValues_congr
    {n k l : Nat} (a : GoodBONG q L (n + 1))
    (hk : k ≤ n + 1) (hl : l ≤ n + 1) (hkl : k = l) :
    DiagonalIsotropic (a.prefixValues k hk) ↔
      DiagonalIsotropic (a.prefixValues l hl) := by
  subst l
  rfl

end BONG.GoodBONG

namespace BONG.StrictJordanAdaptedAlignment

variable {n : Nat} {a : GoodBONG q L (n + 2)}

/-- At an adapted Jordan boundary, isotropy of the exact good-BONG prefix is
literally isotropy of the corresponding Jordan prefix. -/
theorem sourceBoundaryPrefix_diagonalIsotropic_iff
    (S : StrictJordanAdaptedAlignment a.toBONG a.toBONG)
    {t : Nat} (hcount : S.componentCount = t + 1) (z : Fin t) :
    let j := (S.sourceProfileSucc hcount).boundaryIndex z
    DiagonalIsotropic (a.prefixValues (j.val + 1) (by omega)) ↔
      ¬((S.sourceJordanSucc hcount).prefixSpace
          (z.val + 1)).IsAnisotropicSpace := by
  let j := (S.sourceProfileSucc hcount).boundaryIndex z
  dsimp only
  have hf := QuadraticSpace.Isometry.isAnisotropicSpace_iff_general
    (S.sourcePrefixExactDiagonalIsometry hcount z)
  rw [a.prefixExactDiagonalSpace_eq_prefixDiagonalSpace] at hf
  have hd := QuadraticSpace.not_finiteDiagonal_isAnisotropicSpace_iff
    (a.prefixValues (j.val + 1) (by omega))
    (fun i ↦ a.toBONG.value_ne_zero ⟨i.val, by omega⟩)
  change ¬(a.prefixDiagonalSpace (j.val + 1) (by omega)).IsAnisotropicSpace ↔
    DiagonalIsotropic (a.prefixValues (j.val + 1) (by omega)) at hd
  exact hd.symm.trans (not_congr hf)

end BONG.StrictJordanAdaptedAlignment

namespace Lattice.JordanDecomposition

/-- The paper's assertion that a displayed Jordan component is isotropic. -/
def ComponentIsIsotropic {t : Nat}
    (J : JordanDecomposition q L (t + 1)) (i : Fin (t + 1)) : Prop :=
  ¬(J.component i).space.IsAnisotropicSpace

/-- The paper's assertion that the prefix `M₁ ⊥ ··· ⊥ M_k` is
isotropic.  Only the cases `k = 1,2` are used below. -/
def ComponentPrefixIsIsotropic {t : Nat}
    (J : JordanDecomposition q L (t + 1)) (k : Nat) : Prop :=
  ¬(J.toOrthogonalDecomposition.prefixQuadraticSublattice k).space.IsAnisotropicSpace

/-- The binary first component is the integral half-hyperbolic plane
`2⁻¹ A(0,0)`. -/
noncomputable def FirstComponentIsHalfHyperbolic {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop := by
  let T := QuadraticLatticeModel.halfHyperbolicTower (K := K) 1
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  exact Nonempty (Lattice.Isometry (J.component 0).space T.form
    (J.component 0).lattice T.lattice)

/-- A boundary-safe name for the paper's `u_k`. -/
noncomputable abbrev UniversalNormOrder {t : Nat}
    (J : JordanDecomposition q L (t + 1)) (i : Fin (t + 1)) : Int :=
  BONG.jordanEffectiveNormOrder J i

/-- Beli, Theorem 3.1(1). -/
noncomputable def UniversalJordanCase1 {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  4 ≤ J.componentRank 0 ∧
    powerIdeal (K := K) 1 ≤ J.fundamentalWeightIdeal 0

/-- Beli, Theorem 3.1(2), including (2.1) and (2.2). -/
noncomputable def UniversalJordanCase2 {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  J.componentRank 0 = 3 ∧
    J.fundamentalWeightIdeal 0 = powerIdeal (K := K) 1 ∧
    ((∃ i : Fin (t + 1), i.val = 1 ∧
        J.UniversalNormOrder i ≤ 2 * (ramificationIndex K : Int)) ∨
      J.ComponentIsIsotropic 0)

/-- Beli, Theorem 3.1(3.1.1). -/
noncomputable def UniversalJordanCase311 {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  ∃ i : Fin (t + 1), i.val = 1 ∧ J.UniversalNormOrder i = 0

/-- Beli, Theorem 3.1(3.1.2). -/
noncomputable def UniversalJordanCase312 {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  ∃ i : Fin (t + 1), i.val = 1 ∧ J.UniversalNormOrder i = 1 ∧
    (2 ≤ J.componentRank i ∨
      (J.componentRank i = 1 ∧
        ∃ j : Fin (t + 1), j.val = 2 ∧
          J.UniversalNormOrder j ≤ 2 * (ramificationIndex K : Int) + 1))

/-- Beli, Theorem 3.1(3.1). -/
noncomputable def UniversalJordanCase31 {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  J.fundamentalScaleOrder 0 = -(ramificationIndex K : Int) ∧
    (J.UniversalJordanCase311 ∨ J.UniversalJordanCase312 ∨
      J.FirstComponentIsHalfHyperbolic)

/-- Beli, Theorem 3.1(3.2.1). -/
noncomputable def UniversalJordanCase321 {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  ∃ i : Fin (t + 1), i.val = 1 ∧ 1 < J.UniversalNormOrder i ∧
    2 ≤ J.componentRank i ∧
    powerIdeal (K := K)
        (2 * (ramificationIndex K : Int) + J.fundamentalScaleOrder 0 +
          J.UniversalNormOrder i - 2 * (J.UniversalNormOrder i / 2)) <
      J.fundamentalWeightIdeal i

/-- Beli, Theorem 3.1(3.2.2).  The paper's `f₂` is the boundary
ideal between the second and third Jordan components, hence zero-based
boundary index `1`. -/
noncomputable def UniversalJordanCase322 {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  ∃ i : Fin (t + 1), i.val = 1 ∧ 1 < J.UniversalNormOrder i ∧
    J.componentRank i = 1 ∧
    ∃ z : Fin t, z.val = 1 ∧
      powerIdeal (K := K)
          (2 * (ramificationIndex K : Int) + J.fundamentalScaleOrder 0 -
            2 * (J.UniversalNormOrder i / 2)) < J.fundamentalIdeal z

/-- The direct translation of Theorem 2.1, II(b), in the non-unary second
component branch.  The printed exponent in Theorem 3.1(3.2.1) contains
`r₁`; substituting `R₂ = 2r₁-u₁`, with `u₁ = 0`, gives `2r₁` instead.
Keeping this predicate separate records the normalization discrepancy
without silently changing the paper-facing predicate above. -/
noncomputable def UniversalJordanCase321Direct {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  ∃ i : Fin (t + 1), i.val = 1 ∧ 1 < J.UniversalNormOrder i ∧
    2 ≤ J.componentRank i ∧
    powerIdeal (K := K)
        (2 * (ramificationIndex K : Int) +
          2 * J.fundamentalScaleOrder 0 + J.UniversalNormOrder i -
          2 * (J.UniversalNormOrder i / 2)) <
      J.fundamentalWeightIdeal i

/-- The corresponding direct translation in the unary second-component
branch.  As in `UniversalJordanCase321Direct`, the coefficient of `r₁` is
two after substituting the Jordan order profile into Theorem 2.1, II(b). -/
noncomputable def UniversalJordanCase322Direct {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  ∃ i : Fin (t + 1), i.val = 1 ∧ 1 < J.UniversalNormOrder i ∧
    J.componentRank i = 1 ∧
    ∃ z : Fin t, z.val = 1 ∧
      powerIdeal (K := K)
          (2 * (ramificationIndex K : Int) +
            2 * J.fundamentalScaleOrder 0 -
            2 * (J.UniversalNormOrder i / 2)) < J.fundamentalIdeal z

/-- Beli, Theorem 3.1(3.2.3). -/
noncomputable def UniversalJordanCase323 {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  ∃ i : Fin (t + 1), i.val = 1 ∧ J.UniversalNormOrder i ≤ 1 ∧
    2 ≤ J.componentRank i

/-- Beli, Theorem 3.1(3.2.4). -/
noncomputable def UniversalJordanCase324 {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  ∃ i : Fin (t + 1), i.val = 1 ∧ J.UniversalNormOrder i ≤ 1 ∧
    J.componentRank i = 1 ∧
    ∃ j : Fin (t + 1), j.val = 2 ∧
      J.UniversalNormOrder j ≤
        J.UniversalNormOrder i + 2 * (ramificationIndex K : Int)

/-- Beli, Theorem 3.1(3.2.5). -/
noncomputable def UniversalJordanCase325 {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  ∃ i : Fin (t + 1), i.val = 1 ∧ J.UniversalNormOrder i ≤ 1 ∧
    J.componentRank i = 1 ∧ J.ComponentPrefixIsIsotropic 2

/-- Beli, Theorem 3.1(3.2). -/
noncomputable def UniversalJordanCase32 {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  J.fundamentalWeightIdeal 0 = powerIdeal (K := K) 1 ∧
    3 ≤ finrank K V ∧
    (J.UniversalJordanCase321 ∨ J.UniversalJordanCase322 ∨
      J.UniversalJordanCase323 ∨ J.UniversalJordanCase324 ∨
      J.UniversalJordanCase325)

/-- Case (3.2) with the two exponents obtained by direct substitution into
Theorem 2.1.  All other subcases agree literally with the printed theorem. -/
noncomputable def UniversalJordanCase32Direct {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  J.fundamentalWeightIdeal 0 = powerIdeal (K := K) 1 ∧
    3 ≤ finrank K V ∧
    (J.UniversalJordanCase321Direct ∨ J.UniversalJordanCase322Direct ∨
      J.UniversalJordanCase323 ∨ J.UniversalJordanCase324 ∨
      J.UniversalJordanCase325)

/-- Beli, Theorem 3.1(3). -/
noncomputable def UniversalJordanCase3 {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  J.componentRank 0 = 2 ∧
    (J.UniversalJordanCase31 ∨ J.UniversalJordanCase32)

/-- Case (3) with the direct-translation form of Case (3.2). -/
noncomputable def UniversalJordanCase3Direct {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  J.componentRank 0 = 2 ∧
    (J.UniversalJordanCase31 ∨ J.UniversalJordanCase32Direct)

/-- Beli, Theorem 3.1(4.1). -/
noncomputable def UniversalJordanCase41 {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  ∃ i : Fin (t + 1), i.val = 1 ∧ 3 ≤ J.componentRank i

/-- Beli, Theorem 3.1(4.2). -/
noncomputable def UniversalJordanCase42 {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  ∃ i : Fin (t + 1), i.val = 1 ∧ J.componentRank i = 2 ∧
    ∃ j : Fin (t + 1), j.val = 2 ∧
      J.UniversalNormOrder j ≤ 2 * (ramificationIndex K : Int)

/-- Beli, Theorem 3.1(4.3.1). -/
noncomputable def UniversalJordanCase431 {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  ∃ i : Fin (t + 1), i.val = 1 ∧ J.componentRank i = 1 ∧
    ∃ j : Fin (t + 1), j.val = 2 ∧ 2 ≤ J.componentRank j ∧
      powerIdeal (K := K)
          (2 * (ramificationIndex K : Int) + J.UniversalNormOrder j -
            2 * ((J.UniversalNormOrder j - 1) / 2)) <
        J.fundamentalWeightIdeal j

/-- Beli, Theorem 3.1(4.3.2).  The paper's `f₃` is zero-based
boundary index `2`. -/
noncomputable def UniversalJordanCase432 {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  ∃ i : Fin (t + 1), i.val = 1 ∧ J.componentRank i = 1 ∧
    ∃ j : Fin (t + 1), j.val = 2 ∧ J.componentRank j = 1 ∧
      ∃ z : Fin t, z.val = 2 ∧
        powerIdeal (K := K)
            (2 * (ramificationIndex K : Int) -
              2 * ((J.UniversalNormOrder j - 1) / 2)) <
          J.fundamentalIdeal z

/-- Beli, Theorem 3.1(4). -/
noncomputable def UniversalJordanCase4 {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  J.componentRank 0 = 1 ∧
    (∃ i : Fin (t + 1), i.val = 1 ∧ J.UniversalNormOrder i = 1) ∧
    4 ≤ finrank K V ∧
    (J.UniversalJordanCase41 ∨ J.UniversalJordanCase42 ∨
      J.UniversalJordanCase431 ∨ J.UniversalJordanCase432)

/-- The literal disjunction of the four numbered cases in Theorem 3.1. -/
noncomputable def UniversalJordanCases {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  J.UniversalJordanCase1 ∨ J.UniversalJordanCase2 ∨
    J.UniversalJordanCase3 ∨ J.UniversalJordanCase4

/-- The four cases after replacing only (3.2.1) and (3.2.2) by their direct
Theorem 2.1 translations. -/
noncomputable def UniversalJordanCasesDirect {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  J.UniversalJordanCase1 ∨ J.UniversalJordanCase2 ∨
    J.UniversalJordanCase3Direct ∨ J.UniversalJordanCase4

/-- The complete right hand side of Theorem 3.1.  Rank at least two is
kept explicit even when a later application already fixes the rank as
`tail + 2`. -/
noncomputable def UniversalTheorem31Conditions {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  2 ≤ finrank K V ∧ J.UniversalNormOrder 0 = 0 ∧
    J.UniversalJordanCases

/-- The theorem-level predicate obtained by direct translation of Theorem
2.1.  It differs from the printed Theorem 3.1 predicate only in the two
documented coefficients in (3.2.1) and (3.2.2). -/
noncomputable def UniversalTheorem31DirectConditions {t : Nat}
    (J : JordanDecomposition q L (t + 1)) : Prop :=
  2 ≤ finrank K V ∧ J.UniversalNormOrder 0 = 0 ∧
    J.UniversalJordanCasesDirect

/-- The printed and directly translated versions of (3.2.1) coincide when
the first Jordan scale has order zero. -/
theorem universalJordanCase321Direct_iff_of_firstScaleOrder_eq_zero {t : Nat}
    (J : JordanDecomposition q L (t + 1))
    (hscale : J.fundamentalScaleOrder 0 = 0) :
    J.UniversalJordanCase321Direct ↔ J.UniversalJordanCase321 := by
  simp only [UniversalJordanCase321Direct, UniversalJordanCase321, hscale]
  norm_num

/-- The same comparison for (3.2.2). -/
theorem universalJordanCase322Direct_iff_of_firstScaleOrder_eq_zero {t : Nat}
    (J : JordanDecomposition q L (t + 1))
    (hscale : J.fundamentalScaleOrder 0 = 0) :
    J.UniversalJordanCase322Direct ↔ J.UniversalJordanCase322 := by
  simp only [UniversalJordanCase322Direct, UniversalJordanCase322, hscale]
  norm_num

/-- Consequently the two complete theorem predicates agree in the
zero-scale situation (in particular, in every application where this scale
normalization has already been imposed). -/
theorem universalTheorem31DirectConditions_iff_of_firstScaleOrder_eq_zero
    {t : Nat} (J : JordanDecomposition q L (t + 1))
    (hscale : J.fundamentalScaleOrder 0 = 0) :
    J.UniversalTheorem31DirectConditions ↔ J.UniversalTheorem31Conditions := by
  rw [UniversalTheorem31DirectConditions, UniversalTheorem31Conditions,
    UniversalJordanCasesDirect, UniversalJordanCases,
    UniversalJordanCase3Direct, UniversalJordanCase3,
    UniversalJordanCase32Direct, UniversalJordanCase32,
    J.universalJordanCase321Direct_iff_of_firstScaleOrder_eq_zero hscale,
    J.universalJordanCase322Direct_iff_of_firstScaleOrder_eq_zero hscale]

end Lattice.JordanDecomposition

namespace BONG

/-! ## The first coordinates of an arbitrary Jordan profile -/

/-- The discrete arithmetic behind Theorem 3.1(3.2.1).  If the boundary
alpha is integral and the weight order is `u + alpha`, then the Case II(b)
bound is exactly strict containment below the power-ideal order obtained by
substituting `R₂ = 2r` and `R₃ = u`.  The coefficient of `r` is therefore
two. -/
theorem alphaUpperBound_iff_weightOrder_lt_direct
    (e r u w : Int) (alpha : ℚ)
    (hw : (w : ℚ) = (u : ℚ) + alpha)
    (halpha : IsRationalInteger alpha) :
    alpha ≤
        2 * ((e : ℚ) - ((((u - 2 * r) / 2 : Int) : ℚ))) - 1 ↔
      w < 2 * e + 2 * r + u - 2 * (u / 2) := by
  have hdiv : (u - 2 * r) / 2 = u / 2 - r := by omega
  rw [hdiv]
  rcases halpha with ⟨z, rfl⟩
  have hwz : w = u + z := by
    exact_mod_cast hw
  constructor
  · intro h
    have hz : z ≤ 2 * (e - (u / 2 - r)) - 1 := by
      exact_mod_cast h
    rw [hwz]
    omega
  · intro h
    have hz : z ≤ 2 * (e - (u / 2 - r)) - 1 := by
      rw [hwz] at h
      omega
    exact_mod_cast hz

/-- A shifted version of the integer arithmetic used in Theorem 3.1(4.3.1).
If `w = u + alpha`, the bound
`alpha <= 2(e - floor((u-c)/2)) - 1` is the strict weight-ideal
inequality with threshold `2e + u - 2 floor((u-c)/2)`. -/
theorem alphaUpperBound_iff_weightOrder_lt_shift
    (e u c w : Int) (alpha : ℚ)
    (hw : (w : ℚ) = (u : ℚ) + alpha)
    (halpha : IsRationalInteger alpha) :
    alpha ≤
        2 * ((e : ℚ) - ((((u - c) / 2 : Int) : ℚ))) - 1 ↔
      w < 2 * e + u - 2 * ((u - c) / 2) := by
  rcases halpha with ⟨z, rfl⟩
  have hwz : w = u + z := by
    exact_mod_cast hw
  constructor
  · intro h
    have hz : z ≤ 2 * (e - ((u - c) / 2)) - 1 := by
      exact_mod_cast h
    rw [hwz]
    omega
  · intro h
    have hz : z ≤ 2 * (e - ((u - c) / 2)) - 1 := by
      rw [hwz] at h
      omega
    exact_mod_cast hz

/-- Because alpha is integral below the dyadic endpoint, being strictly
below `2e` is the same as being at most the integer `2e - 1`.  Property P5
then converts this to the corresponding strict order-gap inequality. -/
theorem GoodBONG.alphaValue_le_two_e_sub_one_iff_orderGap_lt_two_e
    {n : Nat} (a : GoodBONG q L (n + 1)) (i : Fin n) :
    a.alphaValue i ≤
        ((2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) ↔
      a.orderGap i < 2 * (ramificationIndex K : Int) := by
  constructor
  · intro h
    have halphaLt : a.alphaValue i <
        2 * (ramificationIndex K : ℚ) := by
      have hcast :
          ((2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) <
            2 * (ramificationIndex K : ℚ) := by
        exact_mod_cast (show
          2 * (ramificationIndex K : Int) - 1 <
            2 * (ramificationIndex K : Int) by omega)
      exact h.trans_lt hcast
    exact (a.alpha_p5 i).1.mp halphaLt
  · intro hgap
    have halphaLt : a.alphaValue i <
        2 * (ramificationIndex K : ℚ) :=
      (a.alpha_p5 i).1.mpr hgap
    have hinteger : IsRationalInteger (a.alphaValue i) := by
      rcases a.beli2009Corollary28_iii i with hinteger | hhalf
      · exact hinteger.2.2
      · exact False.elim ((not_lt_of_ge hhalf.1.le) halphaLt)
    rcases hinteger with ⟨z, hz⟩
    rw [hz] at halphaLt ⊢
    have hzlt : z < 2 * (ramificationIndex K : Int) := by
      exact_mod_cast halphaLt
    have hzle : z ≤ 2 * (ramificationIndex K : Int) - 1 := by omega
    exact_mod_cast hzle

namespace JordanOrderProfileWitness

variable {m t : Nat} {a : GoodBONG q L (m + 1)}
  {J : Lattice.JordanDecomposition q L (t + 1)}

/-- Every global coordinate lying before the end of the first Jordan
component is the coordinate with the same numerical local index in that
component. -/
theorem indexEquiv_eq_firstComponent_of_lt_rank
    (P : JordanOrderProfileWitness a.toBONG J) (i : Fin (m + 1))
    (hi : i.val < J.componentRank 0) :
    (P.indexEquiv i).1 = (0 : Fin (t + 1)) ∧
      (P.indexEquiv i).2.val = i.val := by
  let k : Fin (t + 1) := 0
  have hi' : i.val < J.componentRank k := by simpa [k] using hi
  let ell : Fin (J.componentRank k) := ⟨i.val, hi'⟩
  let g : Fin (m + 1) :=
    P.indexEquiv.symm ⟨k, ell⟩
  have hgval : g.val = i.val := by
    rw [P.inverse_index_val]
    simp [k, ell]
  have hgi : g = i := Fin.ext hgval
  have hpair : P.indexEquiv i = ⟨k, ell⟩ := by
    rw [← hgi]
    exact P.indexEquiv.apply_symm_apply _
  exact ⟨by simpa [k] using congrArg Sigma.fst hpair,
    by simpa [ell] using congrArg (fun z => z.2.val) hpair⟩

/-- The first good-BONG order is the effective norm order `u₁` of the
first Jordan component. -/
theorem order_zero_eq_firstUniversalNormOrder
    (P : JordanOrderProfileWitness a.toBONG J) :
    a.order 0 = BONG.jordanEffectiveNormOrder J 0 := by
  have hpos : 0 < J.componentRank 0 := by
    change 0 < finrank K (J.component 0).carrier
    exact J.component_finrank_pos 0
  have hcoordinates := P.indexEquiv_eq_firstComponent_of_lt_rank
    (0 : Fin (m + 1)) hpos
  have hindex : P.indexEquiv (0 : Fin (m + 1)) =
      ⟨(0 : Fin (t + 1)), ⟨0, hpos⟩⟩ := by
    apply Sigma.ext
    · exact hcoordinates.1
    · exact (Fin.heq_ext_iff (congrArg J.componentRank
        hcoordinates.1)).2 (by simpa using hcoordinates.2)
  have horder := P.order_eq (0 : Fin (m + 1))
  rw [hindex] at horder
  change a.order 0 = BONG.jordanExpectedOrder J 0
    ⟨0, hpos⟩ at horder
  rw [horder]
  unfold BONG.jordanExpectedOrder
  by_cases hproper : ordUnit K (J.scaleGenerator 0) =
      BONG.jordanEffectiveNormOrder J 0
  · rw [if_pos hproper, hproper]
  · simp only [hproper, if_false, even_iff_two_dvd, dvd_zero, if_true]

/-- At local position one in the first Jordan component the good-BONG
order is `2r₁-u₁`. -/
theorem order_one_eq_two_firstScale_sub_norm
    (P : JordanOrderProfileWitness a.toBONG J)
    (hrank : 2 ≤ J.componentRank 0) (hm : 1 < m + 1) :
    a.order (⟨1, hm⟩ : Fin (m + 1)) =
      2 * J.fundamentalScaleOrder 0 -
        BONG.jordanEffectiveNormOrder J 0 := by
  have hcoordinates := P.indexEquiv_eq_firstComponent_of_lt_rank
    (⟨1, hm⟩ : Fin (m + 1)) (by change 1 < J.componentRank 0; omega)
  have hlocal : 1 < J.componentRank (0 : Fin (t + 1)) := by omega
  have hindex : P.indexEquiv (⟨1, hm⟩ : Fin (m + 1)) =
      ⟨(0 : Fin (t + 1)), ⟨1, hlocal⟩⟩ := by
    apply Sigma.ext
    · exact hcoordinates.1
    · exact (Fin.heq_ext_iff (congrArg J.componentRank
        hcoordinates.1)).2 (by simpa using hcoordinates.2)
  have horder := P.order_eq (⟨1, hm⟩ : Fin (m + 1))
  rw [hindex] at horder
  change a.order (⟨1, hm⟩ : Fin (m + 1)) =
    BONG.jordanExpectedOrder J 0 ⟨1, hlocal⟩ at horder
  rw [horder]
  change BONG.jordanExpectedOrder J 0 ⟨1, hlocal⟩ =
    2 * ordUnit K (J.scaleGenerator 0) -
      BONG.jordanEffectiveNormOrder J 0
  unfold BONG.jordanExpectedOrder
  by_cases hproper : ordUnit K (J.scaleGenerator 0) =
      BONG.jordanEffectiveNormOrder J 0
  · rw [if_pos hproper]
    omega
  · simp only [hproper, if_false]
    norm_num

/-- At local position two in the first Jordan component the profile returns
to `u₁`. -/
theorem order_two_eq_firstUniversalNormOrder
    (P : JordanOrderProfileWitness a.toBONG J)
    (hrank : 3 ≤ J.componentRank 0) (hm : 2 < m + 1) :
    a.order (⟨2, hm⟩ : Fin (m + 1)) =
      BONG.jordanEffectiveNormOrder J 0 := by
  have hcoordinates := P.indexEquiv_eq_firstComponent_of_lt_rank
    (⟨2, hm⟩ : Fin (m + 1)) (by change 2 < J.componentRank 0; omega)
  have hlocal : 2 < J.componentRank (0 : Fin (t + 1)) := by omega
  have hindex : P.indexEquiv (⟨2, hm⟩ : Fin (m + 1)) =
      ⟨(0 : Fin (t + 1)), ⟨2, hlocal⟩⟩ := by
    apply Sigma.ext
    · exact hcoordinates.1
    · exact (Fin.heq_ext_iff (congrArg J.componentRank
        hcoordinates.1)).2 (by simpa using hcoordinates.2)
  have horder := P.order_eq (⟨2, hm⟩ : Fin (m + 1))
  rw [hindex] at horder
  change a.order (⟨2, hm⟩ : Fin (m + 1)) =
    BONG.jordanExpectedOrder J 0 ⟨2, hlocal⟩ at horder
  rw [horder]
  unfold BONG.jordanExpectedOrder
  by_cases hproper : ordUnit K (J.scaleGenerator 0) =
      BONG.jordanEffectiveNormOrder J 0
  · rw [if_pos hproper, hproper]
  · simp only [hproper, if_false]
    norm_num

/-- At local position three in the first Jordan component the profile is
again `2r₁-u₁`. -/
theorem order_three_eq_two_firstScale_sub_norm
    (P : JordanOrderProfileWitness a.toBONG J)
    (hrank : 4 ≤ J.componentRank 0) (hm : 3 < m + 1) :
    a.order (⟨3, hm⟩ : Fin (m + 1)) =
      2 * J.fundamentalScaleOrder 0 -
        BONG.jordanEffectiveNormOrder J 0 := by
  have hcoordinates := P.indexEquiv_eq_firstComponent_of_lt_rank
    (⟨3, hm⟩ : Fin (m + 1)) (by change 3 < J.componentRank 0; omega)
  have hlocal : 3 < J.componentRank (0 : Fin (t + 1)) := by omega
  have hindex : P.indexEquiv (⟨3, hm⟩ : Fin (m + 1)) =
      ⟨(0 : Fin (t + 1)), ⟨3, hlocal⟩⟩ := by
    apply Sigma.ext
    · exact hcoordinates.1
    · exact (Fin.heq_ext_iff (congrArg J.componentRank
        hcoordinates.1)).2 (by simpa using hcoordinates.2)
  have horder := P.order_eq (⟨3, hm⟩ : Fin (m + 1))
  rw [hindex] at horder
  change a.order (⟨3, hm⟩ : Fin (m + 1)) =
    BONG.jordanExpectedOrder J 0 ⟨3, hlocal⟩ at horder
  rw [horder]
  change BONG.jordanExpectedOrder J 0 ⟨3, hlocal⟩ =
    2 * ordUnit K (J.scaleGenerator 0) -
      BONG.jordanEffectiveNormOrder J 0
  unfold BONG.jordanExpectedOrder
  by_cases hproper : ordUnit K (J.scaleGenerator 0) =
      BONG.jordanEffectiveNormOrder J 0
  · rw [if_pos hproper]
    omega
  · simp only [hproper, if_false]
    norm_num

/-- The global coordinate at which a Jordan component begins. -/
noncomputable def componentFirstGlobalIndex
    (P : JordanOrderProfileWitness a.toBONG J) (k : Fin (t + 1)) :
    Fin (m + 1) :=
  P.indexEquiv.symm ⟨k, ⟨0, by
    change 0 < finrank K (J.component k).carrier
    exact J.component_finrank_pos k⟩⟩

@[simp]
theorem indexEquiv_componentFirstGlobalIndex
    (P : JordanOrderProfileWitness a.toBONG J) (k : Fin (t + 1)) :
    P.indexEquiv (P.componentFirstGlobalIndex k) =
      ⟨k, ⟨0, by
        change 0 < finrank K (J.component k).carrier
        exact J.component_finrank_pos k⟩⟩ :=
  P.indexEquiv.apply_symm_apply _

/-- Numerically, a component begins after the ranks of all preceding
components. -/
theorem componentFirstGlobalIndex_val
    (P : JordanOrderProfileWitness a.toBONG J) (k : Fin (t + 1)) :
    (P.componentFirstGlobalIndex k).val =
      ∑ z ∈ Finset.Iio k, J.componentRank z := by
  rw [componentFirstGlobalIndex]
  exact P.inverse_index_val k _

/-- The good-BONG order at the beginning of component `k` is the paper's
effective norm order `u_k`. -/
theorem order_componentFirstGlobalIndex_eq_universalNormOrder
    (P : JordanOrderProfileWitness a.toBONG J) (k : Fin (t + 1)) :
    a.order (P.componentFirstGlobalIndex k) =
      BONG.jordanEffectiveNormOrder J k := by
  change a.toBONG.order (P.componentFirstGlobalIndex k) =
    BONG.jordanEffectiveNormOrder J k
  have horder := P.order_eq (P.componentFirstGlobalIndex k)
  rw [P.indexEquiv_componentFirstGlobalIndex k] at horder
  rw [horder]
  unfold BONG.jordanExpectedOrder
  by_cases hproper : ordUnit K (J.scaleGenerator k) =
      BONG.jordanEffectiveNormOrder J k
  · rw [if_pos hproper, hproper]
  · simp only [hproper, if_false, even_iff_two_dvd, dvd_zero, if_true]

/-- If component `k` starts at the displayed global position, its effective
norm order is the corresponding good-BONG order. -/
theorem universalNormOrder_eq_order_of_componentFirst_val
    (P : JordanOrderProfileWitness a.toBONG J) (k : Fin (t + 1))
    (i : Fin (m + 1))
    (hval : (P.componentFirstGlobalIndex k).val = i.val) :
    BONG.jordanEffectiveNormOrder J k = a.order i := by
  have hindex : P.componentFirstGlobalIndex k = i := Fin.ext hval
  rw [← hindex, P.order_componentFirstGlobalIndex_eq_universalNormOrder]

/-- The second local coordinate of a Jordan component has order
`2 r_k - u_k`.  The statement is phrased using its global numerical
position so it can be applied directly to the first four coordinates in
Theorem 2.1. -/
theorem order_eq_two_scale_sub_norm_of_componentLocalOne_val
    (P : JordanOrderProfileWitness a.toBONG J) (k : Fin (t + 1))
    (hrank : 2 ≤ J.componentRank k) (i : Fin (m + 1))
    (hval : i.val = (P.componentFirstGlobalIndex k).val + 1) :
    a.order i = 2 * J.fundamentalScaleOrder k -
      BONG.jordanEffectiveNormOrder J k := by
  let ell : Fin (J.componentRank k) := ⟨1, by omega⟩
  let g : Fin (m + 1) := P.indexEquiv.symm ⟨k, ell⟩
  have hgval : g.val = (P.componentFirstGlobalIndex k).val + 1 := by
    calc
      g.val = (∑ z ∈ Finset.Iio k, J.componentRank z) + ell.val :=
        P.inverse_index_val k ell
      _ = (∑ z ∈ Finset.Iio k, J.componentRank z) + 1 := by rfl
      _ = (P.componentFirstGlobalIndex k).val + 1 := by
        rw [P.componentFirstGlobalIndex_val]
  have hgi : g = i := Fin.ext (hgval.trans hval.symm)
  have horder := P.order_eq g
  have hpair : P.indexEquiv g = ⟨k, ell⟩ :=
    P.indexEquiv.apply_symm_apply ⟨k, ell⟩
  rw [hpair] at horder
  have horder' : a.toBONG.order g =
      BONG.jordanExpectedOrder J k ell := by
    simpa only using horder
  rw [← hgi]
  change a.toBONG.order g = _
  rw [horder']
  unfold BONG.jordanExpectedOrder
  dsimp only
  by_cases heq : J.fundamentalScaleOrder k =
      BONG.jordanEffectiveNormOrder J k
  · have heq' : ordUnit K (J.scaleGenerator k) =
        BONG.jordanEffectiveNormOrder J k := by
      simpa only [Lattice.JordanDecomposition.fundamentalScaleOrder] using heq
    rw [if_pos heq', heq]
    omega
  · have heq' : ¬ordUnit K (J.scaleGenerator k) =
        BONG.jordanEffectiveNormOrder J k := by
      simpa only [Lattice.JordanDecomposition.fundamentalScaleOrder] using heq
    have hodd : ¬Even ell.val := by simp [ell]
    rw [if_neg heq', if_neg hodd]
    rfl

/-- The third local coordinate of a Jordan component has its effective norm
order `u_k`. -/
theorem order_eq_norm_of_componentLocalTwo_val
    (P : JordanOrderProfileWitness a.toBONG J) (k : Fin (t + 1))
    (hrank : 3 ≤ J.componentRank k) (i : Fin (m + 1))
    (hval : i.val = (P.componentFirstGlobalIndex k).val + 2) :
    a.order i = BONG.jordanEffectiveNormOrder J k := by
  let ell : Fin (J.componentRank k) := ⟨2, by omega⟩
  let g : Fin (m + 1) := P.indexEquiv.symm ⟨k, ell⟩
  have hgval : g.val = (P.componentFirstGlobalIndex k).val + 2 := by
    calc
      g.val = (∑ z ∈ Finset.Iio k, J.componentRank z) + ell.val :=
        P.inverse_index_val k ell
      _ = (∑ z ∈ Finset.Iio k, J.componentRank z) + 2 := by rfl
      _ = (P.componentFirstGlobalIndex k).val + 2 := by
        rw [P.componentFirstGlobalIndex_val]
  have hgi : g = i := Fin.ext (hgval.trans hval.symm)
  have horder := P.order_eq g
  have hpair : P.indexEquiv g = ⟨k, ell⟩ :=
    P.indexEquiv.apply_symm_apply ⟨k, ell⟩
  rw [hpair] at horder
  have horder' : a.toBONG.order g =
      BONG.jordanExpectedOrder J k ell := by
    simpa only using horder
  rw [← hgi]
  change a.toBONG.order g = _
  rw [horder']
  unfold BONG.jordanExpectedOrder
  dsimp only
  by_cases heq : J.fundamentalScaleOrder k =
      BONG.jordanEffectiveNormOrder J k
  · have heq' : ordUnit K (J.scaleGenerator k) =
        BONG.jordanEffectiveNormOrder J k := by
      simpa only [Lattice.JordanDecomposition.fundamentalScaleOrder] using heq
    rw [if_pos heq']
    exact heq
  · have heq' : ¬ordUnit K (J.scaleGenerator k) =
        BONG.jordanEffectiveNormOrder J k := by
      simpa only [Lattice.JordanDecomposition.fundamentalScaleOrder] using heq
    have heven : Even ell.val := by simp [ell]
    rw [if_neg heq', if_pos heven]

/-- If the first component does not exhaust the lattice, a second component
exists. -/
theorem componentTail_pos_of_firstRank_lt_length
    (P : JordanOrderProfileWitness a.toBONG J)
    (hshort : J.componentRank 0 < m + 1) : 0 < t := by
  by_contra ht
  have htzero : t = 0 := by omega
  let kZero : Fin (t + 1) := ⟨0, by omega⟩
  have hkZero : kZero = (0 : Fin (t + 1)) := by
    apply Fin.ext
    simp [kZero]
  have hshort' : J.componentRank kZero < m + 1 := by
    rw [hkZero]
    exact hshort
  have hsum := P.sum_componentRank_eq_length
  change (∑ k, J.componentRank k) = m + 1 at hsum
  have huniv : (Finset.univ : Finset (Fin (t + 1))) = {kZero} := by
    ext k
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Fin.ext
    simp only [kZero]
    omega
  rw [huniv] at hsum
  simp only [Finset.sum_singleton] at hsum
  have himpossible : m + 1 < m + 1 := by
    simpa only [hsum] using hshort'
  exact (Nat.lt_irrefl _ himpossible)

/-- The second component starts immediately after the first component. -/
theorem componentFirstGlobalIndex_one_val
    (P : JordanOrderProfileWitness a.toBONG J) (ht : 0 < t) :
    (P.componentFirstGlobalIndex (⟨1, by omega⟩ : Fin (t + 1))).val =
      J.componentRank 0 := by
  rw [P.componentFirstGlobalIndex_val]
  let kZero : Fin (t + 1) := ⟨0, by omega⟩
  have hkZero : kZero = (0 : Fin (t + 1)) := by
    apply Fin.ext
    simp [kZero]
  have hIio :
      Finset.Iio (⟨1, by omega⟩ : Fin (t + 1)) =
        {kZero} := by
    ext z
    simp only [Finset.mem_Iio, Finset.mem_singleton]
    simp only [Fin.ext_iff]
    change z.val < 1 ↔ z.val = kZero.val
    simp only [kZero]
    omega
  rw [hIio]
  simp only [Finset.sum_singleton]
  rw [hkZero]

/-- If the first two components do not exhaust the lattice, a third
component exists. -/
theorem one_lt_componentTail_of_firstTwoRanks_lt_length
    (P : JordanOrderProfileWitness a.toBONG J) (ht : 0 < t)
    (hshort : J.componentRank 0 +
      J.componentRank (⟨1, by omega⟩ : Fin (t + 1)) < m + 1) :
    1 < t := by
  by_contra hnot
  have htOne : t = 1 := by omega
  let kZero : Fin (t + 1) := ⟨0, by omega⟩
  have hsum := P.sum_componentRank_eq_length
  change (∑ k, J.componentRank k) = m + 1 at hsum
  let kOne : Fin (t + 1) := ⟨1, by omega⟩
  have hkZero : kZero = (0 : Fin (t + 1)) := by
    apply Fin.ext
    simp [kZero]
  have hkOne : kOne = (⟨1, by omega⟩ : Fin (t + 1)) := by
    apply Fin.ext
    rfl
  have hshort' : J.componentRank kZero + J.componentRank kOne <
      m + 1 := by
    rw [hkZero, hkOne]
    exact hshort
  have huniv : (Finset.univ : Finset (Fin (t + 1))) =
      {kZero, kOne} := by
    ext k
    simp only [Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_iff]
    by_cases hk0 : k.val = 0
    · left
      apply Fin.ext
      simpa [kZero] using hk0
    · right
      apply Fin.ext
      simp only [kOne]
      omega
  rw [huniv] at hsum
  have hzero_ne_one : kZero ≠ kOne := by
    intro h
    have := congrArg Fin.val h
    simp only [kZero, kOne] at this
    omega
  have hzero_not_mem : kZero ∉ ({kOne} : Finset (Fin (t + 1))) := by
    simpa only [Finset.mem_singleton] using hzero_ne_one
  rw [Finset.sum_insert hzero_not_mem] at hsum
  simp only [Finset.sum_singleton] at hsum
  have himpossible : m + 1 < m + 1 := by
    simpa only [hsum] using hshort'
  exact (Nat.lt_irrefl _ himpossible)

/-- The third component starts after the ranks of the first two. -/
theorem componentFirstGlobalIndex_two_val
    (P : JordanOrderProfileWitness a.toBONG J) (ht : 1 < t) :
    (P.componentFirstGlobalIndex (⟨2, by omega⟩ : Fin (t + 1))).val =
      J.componentRank 0 +
        J.componentRank (⟨1, by omega⟩ : Fin (t + 1)) := by
  rw [P.componentFirstGlobalIndex_val]
  let kZero : Fin (t + 1) := ⟨0, by omega⟩
  let kOne : Fin (t + 1) := ⟨1, by omega⟩
  have hkZero : kZero = (0 : Fin (t + 1)) := by
    apply Fin.ext
    simp [kZero]
  have hkOne : kOne = (⟨1, by omega⟩ : Fin (t + 1)) := by
    apply Fin.ext
    rfl
  have hIio :
      Finset.Iio (⟨2, by omega⟩ : Fin (t + 1)) =
        {kZero, kOne} := by
    ext z
    simp only [Finset.mem_Iio, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
    change z.val < 2 ↔ z.val = kZero.val ∨ z.val = kOne.val
    simp only [kZero, kOne]
    omega
  rw [hIio]
  have hzero_ne_one : kZero ≠ kOne := by
    intro h
    have := congrArg Fin.val h
    simp only [kZero, kOne] at this
    omega
  have hzero_not_mem : kZero ∉ ({kOne} : Finset (Fin (t + 1))) := by
    simpa only [Finset.mem_singleton] using hzero_ne_one
  rw [Finset.sum_insert hzero_not_mem]
  simp only [Finset.sum_singleton]
  rw [hkZero, hkOne]

/-- If the first two components have ranks two and one, respectively, the
boundary after them is the third good-BONG alpha index (zero-based index
two). -/
theorem boundaryIndex_one_val_of_firstTwoRanks
    (P : JordanOrderProfileWitness a.toBONG J) (ht : 1 < t)
    (hrank0 : J.componentRank 0 = 2)
    (hrank1 : J.componentRank
      (⟨1, by omega⟩ : Fin (t + 1)) = 1) :
    (P.boundaryIndex (⟨1, by omega⟩ : Fin t)).val = 2 := by
  have hb := P.boundaryIndex_succ_val_eq_componentRankPrefix
    (⟨1, by omega⟩ : Fin t)
  have hs := P.componentFirstGlobalIndex_two_val ht
  have hri : Lattice.JordanDecomposition.boundaryRightIndex
      (⟨1, by omega⟩ : Fin t) =
        (⟨2, by omega⟩ : Fin (t + 1)) := Fin.ext rfl
  have heq :
      (P.boundaryIndex (⟨1, by omega⟩ : Fin t)).val + 1 =
        (P.componentFirstGlobalIndex
          (⟨2, by omega⟩ : Fin (t + 1))).val := by
    calc
      _ = ∑ k ∈ Finset.Iio
          (Lattice.JordanDecomposition.boundaryRightIndex
            (⟨1, by omega⟩ : Fin t)), J.componentRank k := hb
      _ = (P.componentFirstGlobalIndex
          (⟨2, by omega⟩ : Fin (t + 1))).val := by
        rw [P.componentFirstGlobalIndex_val, hri]
  omega

/-! ## Weight ideals at component starts -/

/-- If the first Jordan component has rank at least two, its fundamental
weight order is the first BONG order plus `α₁`. -/
theorem first_fundamentalWeightOrder_eq_order_add_alpha
    {n s : Nat} {b : GoodBONG q L (n + 2)}
    {H : Lattice.JordanDecomposition q L (s + 1)}
    (P : JordanOrderProfileWitness b.toBONG H)
    (hrank : 2 ≤ H.componentRank 0) :
    (H.fundamentalWeightOrder 0 : ℚ) =
      (b.order 0 : ℚ) + b.alphaValue 0 := by
  have hpos : 0 < H.componentRank 0 := by omega
  have hcoordinates := P.indexEquiv_eq_firstComponent_of_lt_rank
    (0 : Fin (n + 2)) hpos
  have hindex : P.indexEquiv (0 : Fin (n + 2)) =
      ⟨(0 : Fin (s + 1)), ⟨0, hpos⟩⟩ := by
    apply Sigma.ext
    · exact hcoordinates.1
    · exact (Fin.heq_ext_iff (congrArg H.componentRank
        hcoordinates.1)).2 (by simpa using hcoordinates.2)
  have hlocal :
      (P.indexEquiv (0 : Fin (n + 2))).2.val + 1 <
        H.componentRank (P.indexEquiv (0 : Fin (n + 2))).1 := by
    rw [hindex]
    change 1 < H.componentRank 0
    omega
  have hcast : (0 : Fin (n + 1)).castSucc =
      (0 : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hformula := P.internal_weightOrder_eq_order_add_alpha
    (0 : Fin (n + 1)) (by simpa using hlocal)
  rw [hcast, hindex] at hformula
  simpa using hformula

/-- The same formula at the first global coordinate of an arbitrary
non-unary component. -/
theorem componentStart_fundamentalWeightOrder_eq_order_add_alpha
    {n s : Nat} {b : GoodBONG q L (n + 2)}
    {H : Lattice.JordanDecomposition q L (s + 1)}
    (P : JordanOrderProfileWitness b.toBONG H) (k : Fin (s + 1))
    (hrank : 2 ≤ H.componentRank k)
    (hnext : (P.componentFirstGlobalIndex k).val + 1 < n + 2) :
    let i : Fin (n + 1) :=
      ⟨(P.componentFirstGlobalIndex k).val, by omega⟩
    (H.fundamentalWeightOrder k : ℚ) =
      (b.order i.castSucc : ℚ) + b.alphaValue i := by
  let i : Fin (n + 1) :=
    ⟨(P.componentFirstGlobalIndex k).val, by omega⟩
  have hi : i.castSucc = P.componentFirstGlobalIndex k := by
    apply Fin.ext
    rfl
  have hpair := P.indexEquiv_componentFirstGlobalIndex k
  have hlocal : (P.indexEquiv i.castSucc).2.val + 1 <
      H.componentRank (P.indexEquiv i.castSucc).1 := by
    rw [hi, hpair]
    change 0 + 1 < H.componentRank k
    omega
  have hformula := P.internal_weightOrder_eq_order_add_alpha i hlocal
  rw [hi, hpair] at hformula
  exact hformula

/-- With `R₁ = 0`, the equality `w₁ = p` is exactly `α₁ = 1`. -/
theorem first_fundamentalWeightIdeal_eq_p_iff_alpha_eq_one
    {n s : Nat} {b : GoodBONG q L (n + 2)}
    {H : Lattice.JordanDecomposition q L (s + 1)}
    (P : JordanOrderProfileWitness b.toBONG H)
    (hrank : 2 ≤ H.componentRank 0) (hzero : b.order 0 = 0) :
    H.fundamentalWeightIdeal 0 = Lattice.powerIdeal (K := K) 1 ↔
      b.alphaValue 0 = 1 := by
  have hformula := P.first_fundamentalWeightOrder_eq_order_add_alpha hrank
  unfold Lattice.JordanDecomposition.fundamentalWeightOrder at hformula
  constructor
  · intro hideal
    have hpower : Lattice.powerIdeal (K := K)
          (Lattice.weightIdealOrder q (H.fundamentalLattice 0)) =
        Lattice.powerIdeal (K := K) 1 := by
      simpa only [Lattice.JordanDecomposition.fundamentalWeightIdeal,
        Lattice.weightIdeal_eq_powerIdeal] using hideal
    have horder : Lattice.weightIdealOrder q
        (H.fundamentalLattice 0) = 1 :=
      Lattice.powerIdeal_order_eq_of_eq hpower
    norm_num [hzero, horder] at hformula ⊢
    exact hformula.symm
  · intro halpha
    have horder : H.fundamentalWeightOrder 0 = 1 := by
      norm_num [hzero, halpha] at hformula ⊢
      exact hformula
    unfold Lattice.JordanDecomposition.fundamentalWeightOrder at horder
    change Lattice.weightIdeal q (H.fundamentalLattice 0) =
      Lattice.powerIdeal (K := K) 1
    rw [Lattice.weightIdeal_eq_powerIdeal, horder]

/-- With `R₁ = 0`, the containment `w₁ ⊇ p` is exactly the upper bound
`α₁ ≤ 1`. -/
theorem p_le_first_fundamentalWeightIdeal_iff_alpha_le_one
    {n s : Nat} {b : GoodBONG q L (n + 2)}
    {H : Lattice.JordanDecomposition q L (s + 1)}
    (P : JordanOrderProfileWitness b.toBONG H)
    (hrank : 2 ≤ H.componentRank 0) (hzero : b.order 0 = 0) :
    Lattice.powerIdeal (K := K) 1 ≤ H.fundamentalWeightIdeal 0 ↔
      b.alphaValue 0 ≤ 1 := by
  have hformula := P.first_fundamentalWeightOrder_eq_order_add_alpha hrank
  unfold Lattice.JordanDecomposition.fundamentalWeightOrder at hformula
  rw [Lattice.JordanDecomposition.fundamentalWeightIdeal,
    Lattice.weightIdeal_eq_powerIdeal, Lattice.powerIdeal_le_iff]
  norm_num [hzero] at hformula
  constructor
  · intro hle
    calc
      b.alphaValue 0 =
          (Lattice.weightIdealOrder q (H.fundamentalLattice 0) : ℚ) :=
        hformula.symm
      _ ≤ 1 := by exact_mod_cast hle
  · intro hle
    have hle' :
        (Lattice.weightIdealOrder q (H.fundamentalLattice 0) : ℚ) ≤ 1 :=
      hformula.trans_le hle
    exact_mod_cast hle'

/-- At an even Jordan boundary the O'Meara fundamental ideal has an
integer order equal to the corresponding good-BONG alpha.  This is the
even branch hidden inside the minimum formulation of Lemma 2.16(ii),
transported to an arbitrary Jordan decomposition of the lattice. -/
theorem exists_orderedFundamentalIdeal_order_eq_alpha_of_even
    {n t : Nat} {a : GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (heven : Even (J.boundaryNormOrderSum z)) :
    ∃ I : Lattice.OrderedFractionalIdeal K,
      I.carrier = J.fundamentalIdeal z ∧
        (I.order : ℚ) = a.alphaValue (P.boundaryIndex z) := by
  obtain ⟨S⟩ :=
    a.nonempty_strictJordanAdaptedAlignment a (fun _ ↦ rfl)
  let F := Lattice.JordanDecomposition.sameFundamentalTypeOfIsometry
    S.sourceJordan J (Lattice.Isometry.refl q L)
  have hcount : S.componentCount = t + 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_congr F.indexEquiv
  let Js := S.sourceJordanSucc hcount
  let Ps := S.sourceProfileSucc hcount
  let Fs : Lattice.JordanDecomposition.SameFundamentalType Js J :=
    F.castSourceComponentCount hcount
  have hRank :
      Js.toOrthogonalDecomposition.componentRank =
        J.toOrthogonalDecomposition.componentRank := by
    funext k
    have hk := Fs.componentRank_eq k
    rw [Fs.indexEquiv_apply_eq_self] at hk
    exact hk.symm
  have hboundary : Ps.boundaryIndex z = P.boundaryIndex z := by
    apply Fin.ext
    have hs := Ps.boundaryIndex_succ_val_eq_componentRankPrefix z
    have ht := P.boundaryIndex_succ_val_eq_componentRankPrefix z
    rw [hRank] at hs
    omega
  have hfundamental : J.fundamentalIdeal z = Js.fundamentalIdeal z :=
    Fs.fundamentalIdeal_eq z
  have hevenS : Even (Js.boundaryNormOrderSum z) := by
    rw [← Fs.boundaryNormOrderSum_eq z]
    exact heven
  let I := Js.evenOrderedFundamentalIdeal z
    (Ps.boundaryLeftValue z) (Ps.boundaryRightValue z)
    (S.sourceBoundaryLeftValue_isNormGeneratorValue hcount z)
    (S.sourceBoundaryRightValue_isNormGeneratorValue hcount z) hevenS
  refine ⟨I, ?_, ?_⟩
  · change Js.fundamentalIdeal z = J.fundamentalIdeal z
    exact hfundamental.symm
  · have hformula := S.sourceEvenBoundaryFundamentalOrder_eq_alpha
      (a := a) (b := a) (t := t) hcount z hevenS
    change (I.order : ℚ) = a.alphaValue (Ps.boundaryIndex z) at hformula
    rw [hboundary] at hformula
    exact hformula

/-- In the non-unary second-component branch, Theorem 2.1, II(b), is
exactly the directly translated ideal containment in (3.2.1).  No
integrality hypothesis on `alphaValue 2` is added: its integral witness is
the difference between the integral weight order and `u₂`. -/
theorem alphaThreeUpperBound_iff_secondWeightIdeal_direct
    {n t : Nat} {a : GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J)
    (hfour : 1 < n) (ht : 0 < t)
    (hzero : J.UniversalNormOrder 0 = 0)
    (hrank0 : J.componentRank 0 = 2)
    (hrank1 : 2 ≤ J.componentRank
      (⟨1, by omega⟩ : Fin (t + 1))) :
    a.alphaValue (⟨2, by omega⟩ : Fin (n + 1)) ≤
        a.universalAlphaThreeUpperBound hfour ↔
      Lattice.powerIdeal (K := K)
          (2 * (ramificationIndex K : Int) +
            2 * J.fundamentalScaleOrder 0 +
            J.UniversalNormOrder (⟨1, by omega⟩ : Fin (t + 1)) -
            2 * (J.UniversalNormOrder
              (⟨1, by omega⟩ : Fin (t + 1)) / 2)) <
        J.fundamentalWeightIdeal
          (⟨1, by omega⟩ : Fin (t + 1)) := by
  let k : Fin (t + 1) := ⟨1, by omega⟩
  change BONG.jordanEffectiveNormOrder J 0 = 0 at hzero
  have hstart : (P.componentFirstGlobalIndex k).val = 2 := by
    simpa only [k, hrank0] using P.componentFirstGlobalIndex_one_val ht
  have horder1 : a.order (⟨1, by omega⟩ : Fin (n + 2)) =
      2 * J.fundamentalScaleOrder 0 := by
    rw [P.order_one_eq_two_firstScale_sub_norm (by omega) (by omega),
      hzero, sub_zero]
  have hfirst : P.componentFirstGlobalIndex k =
      (⟨2, by omega⟩ : Fin (n + 2)) := Fin.ext hstart
  have horder2 : a.order (⟨2, by omega⟩ : Fin (n + 2)) =
      J.UniversalNormOrder k := by
    rw [← hfirst, P.order_componentFirstGlobalIndex_eq_universalNormOrder]
  have hweightRaw :=
    P.componentStart_fundamentalWeightOrder_eq_order_add_alpha
      k hrank1 (by rw [hstart]; omega)
  dsimp only at hweightRaw
  have halphaIndex :
      (⟨(P.componentFirstGlobalIndex k).val, by omega⟩ : Fin (n + 1)) =
        (⟨2, by omega⟩ : Fin (n + 1)) := Fin.ext hstart
  rw [halphaIndex] at hweightRaw
  change (J.fundamentalWeightOrder k : ℚ) =
    (a.order (⟨2, by omega⟩ : Fin (n + 2)) : ℚ) +
      a.alphaValue (⟨2, by omega⟩ : Fin (n + 1)) at hweightRaw
  rw [horder2] at hweightRaw
  have halphaInteger :
      IsRationalInteger
        (a.alphaValue (⟨2, by omega⟩ : Fin (n + 1))) := by
    refine ⟨J.fundamentalWeightOrder k - J.UniversalNormOrder k, ?_⟩
    push_cast
    linarith
  have harith := BONG.alphaUpperBound_iff_weightOrder_lt_direct
    (ramificationIndex K : Int) (J.fundamentalScaleOrder 0)
    (J.UniversalNormOrder k) (J.fundamentalWeightOrder k)
    (a.alphaValue (⟨2, by omega⟩ : Fin (n + 1)))
    hweightRaw halphaInteger
  unfold Lattice.JordanDecomposition.fundamentalWeightOrder at harith
  unfold GoodBONG.universalAlphaThreeUpperBound
  rw [horder1, horder2]
  change _ ↔ Lattice.powerIdeal (K := K) _ < _
  rw [Lattice.JordanDecomposition.fundamentalWeightIdeal,
    Lattice.weightIdeal_eq_powerIdeal, Lattice.powerIdeal_lt_iff]
  exact harith

end JordanOrderProfileWitness

end BONG

namespace Lattice.JordanDecomposition

/-! ## Intrinsic parity facts for arbitrary Jordan splittings -/

/-- The scale of a Jordan component never exceeds the effective norm at
that scale. -/
theorem fundamentalScaleOrder_le_universalNormOrder {s : Nat}
    (H : JordanDecomposition q L (s + 1)) (k : Fin (s + 1)) :
    H.fundamentalScaleOrder k ≤ BONG.jordanEffectiveNormOrder H k := by
  unfold fundamentalScaleOrder BONG.jordanEffectiveNormOrder
    BONG.jordanEffectiveNormOrderAt
  exact JordanProfileOrder.target_le_effectiveAt _ _ _ _
    (fun j ↦ H.scaleOrder_le_normOrder j)

/-- An odd-rank modular Jordan component is proper; consequently its
effective norm order equals its scale order. -/
theorem universalNormOrder_eq_scaleOrder_of_odd_componentRank {s : Nat}
    (H : JordanDecomposition q L (s + 1)) (k : Fin (s + 1))
    (hodd : Odd (H.componentRank k)) :
    BONG.jordanEffectiveNormOrder H k = H.fundamentalScaleOrder k := by
  have hproper := Lattice.normIdeal_eq_scaleIdeal_of_modular_of_odd_rank
    (H.component k).space (H.component k).lattice (H.scaleGenerator k)
    (H.modular k) hodd
  have hprincipal :
      Lattice.principalIdeal (K := K) (H.normGenerator k : K) =
        Lattice.principalIdeal (K := K) (H.scaleGenerator k : K) := by
    rw [← H.normIdeal_eq k, ← H.scaleIdeal_eq k]
    exact hproper
  have hnormScale : ordUnit K (H.normGenerator k) =
      ordUnit K (H.scaleGenerator k) :=
    (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp hprincipal
  apply le_antisymm
  · unfold BONG.jordanEffectiveNormOrder
      BONG.jordanEffectiveNormOrderAt
    calc
      JordanProfileOrder.effectiveAt
          (fun j ↦ ordUnit K (H.scaleGenerator j))
          (fun j ↦ ordUnit K (H.normGenerator j)) k
          (ordUnit K (H.scaleGenerator k)) ≤
        JordanProfileOrder.adjustedAt
          (fun j ↦ ordUnit K (H.scaleGenerator j))
          (fun j ↦ ordUnit K (H.normGenerator j))
          (ordUnit K (H.scaleGenerator k)) k :=
        JordanProfileOrder.effectiveAt_le _ _ _ _ _
      _ = ordUnit K (H.normGenerator k) := by
        simp [JordanProfileOrder.adjustedAt]
      _ = H.fundamentalScaleOrder k := by
        simpa only [fundamentalScaleOrder] using hnormScale
  · exact H.fundamentalScaleOrder_le_universalNormOrder k

/-- If the effective norm is strictly above a component scale, that
component has even rank. -/
theorem componentRank_even_of_scaleOrder_lt_universalNormOrder {s : Nat}
    (H : JordanDecomposition q L (s + 1)) (k : Fin (s + 1))
    (hstrict : H.fundamentalScaleOrder k <
      BONG.jordanEffectiveNormOrder H k) :
    Even (H.componentRank k) := by
  by_contra hnotEven
  have hodd : Odd (H.componentRank k) := Nat.not_even_iff_odd.mp hnotEven
  have heq := H.universalNormOrder_eq_scaleOrder_of_odd_componentRank k hodd
  omega

end Lattice.JordanDecomposition

namespace BONG.JordanOrderProfileWitness

/-- At a profiled Jordan boundary, every integral upper bound below `2e`
on the corresponding alpha is equivalent to strict containment by the
fundamental ideal.  For an even boundary the fundamental-ideal order is
literally alpha.  For an odd boundary alpha equals the odd order gap up to
`2e`; above `2e` both sides are false. -/
theorem alphaUpperBound_iff_powerIdeal_lt_fundamentalIdeal
    {n t : Nat} {a : GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J)
    (z : Fin t) (i : Fin (n + 1))
    (hboundary : P.boundaryIndex z = i) (B : Int)
    (hB : B ≤ 2 * (ramificationIndex K : Int)) :
    a.alphaValue i ≤ ((B - 1 : Int) : ℚ) ↔
      Lattice.powerIdeal (K := K) B < J.fundamentalIdeal z := by
  by_cases heven : Even (J.boundaryNormOrderSum z)
  · obtain ⟨I, hcarrier, halpha⟩ :=
      P.exists_orderedFundamentalIdeal_order_eq_alpha_of_even z heven
    rw [hboundary] at halpha
    rw [← hcarrier, I.carrier_eq_powerIdeal,
      Lattice.powerIdeal_lt_iff, ← halpha]
    constructor
    · intro h
      have hz : I.order ≤ B - 1 := by
        exact_mod_cast h
      omega
    · intro h
      have hz : I.order ≤ B - 1 := by omega
      exact_mod_cast hz
  · have hodd : Odd (J.boundaryNormOrderSum z) :=
      Int.not_even_iff_odd.mp heven
    let I := J.oddOrderedFundamentalIdeal z hodd
    have hgapRaw :=
      P.orderGap_boundaryIndex_eq_boundaryNormOrderSum_sub_twoScale z
    have hIgap : I.order = a.orderGap (P.boundaryIndex z) :=
      hgapRaw.symm
    have hgapOdd : Odd (a.orderGap (P.boundaryIndex z)) := by
      rw [hgapRaw]
      rcases hodd with ⟨d, hd⟩
      refine ⟨d - J.fundamentalScaleOrder
        (Lattice.JordanDecomposition.boundaryLeftIndex z), ?_⟩
      omega
    change a.alphaValue i ≤ ((B - 1 : Int) : ℚ) ↔
      Lattice.powerIdeal (K := K) B < I.carrier
    rw [I.carrier_eq_powerIdeal, Lattice.powerIdeal_lt_iff]
    by_cases hgapLe : a.orderGap (P.boundaryIndex z) ≤
        2 * (ramificationIndex K : Int)
    · have halpha :=
        (a.alpha_p3 (P.boundaryIndex z) hgapLe).2.mpr
          (Or.inr hgapOdd)
      rw [hboundary] at halpha
      have hIgapI : I.order = a.orderGap i := by
        simpa only [hboundary] using hIgap
      have halphaI : a.alphaValue i = (I.order : ℚ) := by
        calc
          a.alphaValue i = (a.orderGap i : ℚ) := halpha
          _ = (I.order : ℚ) := by rw [hIgapI]
      rw [halphaI]
      constructor
      · intro h
        have hz : I.order ≤ B - 1 := by
          exact_mod_cast h
        omega
      · intro h
        have hz : I.order ≤ B - 1 := by omega
        exact_mod_cast hz
    · have hgapGt : 2 * (ramificationIndex K : Int) <
          a.orderGap (P.boundaryIndex z) := by omega
      have halphaGt : 2 * (ramificationIndex K : ℚ) <
          a.alphaValue (P.boundaryIndex z) :=
        (a.beli2009Corollary28_ii
          (P.boundaryIndex z)).2.2.mpr hgapGt
      rw [hboundary] at halphaGt
      constructor
      · intro h
        have hupper : a.alphaValue i <
            2 * (ramificationIndex K : ℚ) := by
          have hthresholdQ : ((B - 1 : Int) : ℚ) <
              2 * (ramificationIndex K : ℚ) := by
            exact_mod_cast (show B - 1 <
              2 * (ramificationIndex K : Int) by omega)
          exact h.trans_lt hthresholdQ
        exact False.elim ((not_lt_of_ge halphaGt.le) hupper)
      · intro h
        have hIgt : 2 * (ramificationIndex K : Int) < I.order := by
          rw [hIgap]
          exact hgapGt
        omega

/-- In the unary second-component branch, Theorem 2.1, II(b), is exactly
the directly translated containment involving O'Meara's boundary ideal
`f₂`.  The proof separates even boundaries, where `ord f₂ = α₃`, from odd
boundaries; in the exceptional odd case both sides are false because
`α₃ > 2e` while the displayed threshold is at most `2e - 2`. -/
theorem alphaThreeUpperBound_iff_secondFundamentalIdeal_direct
    {n t : Nat} {a : GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J)
    (hfour : 1 < n) (ht : 1 < t)
    (hzero : J.UniversalNormOrder 0 = 0)
    (hrank0 : J.componentRank 0 = 2)
    (hrank1 : J.componentRank
      (⟨1, by omega⟩ : Fin (t + 1)) = 1)
    (hu : 1 < J.UniversalNormOrder
      (⟨1, by omega⟩ : Fin (t + 1))) :
    a.alphaValue (⟨2, by omega⟩ : Fin (n + 1)) ≤
        a.universalAlphaThreeUpperBound hfour ↔
      Lattice.powerIdeal (K := K)
          (2 * (ramificationIndex K : Int) +
            2 * J.fundamentalScaleOrder 0 -
            2 * (J.UniversalNormOrder
              (⟨1, by omega⟩ : Fin (t + 1)) / 2)) <
        J.fundamentalIdeal (⟨1, by omega⟩ : Fin t) := by
  let k : Fin (t + 1) := ⟨1, by omega⟩
  let z : Fin t := ⟨1, by omega⟩
  change 1 < J.UniversalNormOrder k at hu
  change BONG.jordanEffectiveNormOrder J 0 = 0 at hzero
  have hstart : (P.componentFirstGlobalIndex k).val = 2 := by
    simpa only [k, hrank0] using
      P.componentFirstGlobalIndex_one_val (by omega)
  have hfirst : P.componentFirstGlobalIndex k =
      (⟨2, by omega⟩ : Fin (n + 2)) := Fin.ext hstart
  have horder1 : a.order (⟨1, by omega⟩ : Fin (n + 2)) =
      2 * J.fundamentalScaleOrder 0 := by
    rw [P.order_one_eq_two_firstScale_sub_norm (by omega) (by omega),
      hzero, sub_zero]
  have horder2 : a.order (⟨2, by omega⟩ : Fin (n + 2)) =
      J.UniversalNormOrder k := by
    rw [← hfirst, P.order_componentFirstGlobalIndex_eq_universalNormOrder]
  have hboundaryVal : (P.boundaryIndex z).val = 2 := by
    simpa only [z] using
      P.boundaryIndex_one_val_of_firstTwoRanks ht hrank0 hrank1
  have hboundary : P.boundaryIndex z =
      (⟨2, by omega⟩ : Fin (n + 1)) := Fin.ext hboundaryVal
  have hrle : J.fundamentalScaleOrder 0 ≤ 0 := by
    have hs := J.fundamentalScaleOrder_le_universalNormOrder 0
    rw [hzero] at hs
    exact hs
  have hdiv :
      (J.UniversalNormOrder k - 2 * J.fundamentalScaleOrder 0) / 2 =
        J.UniversalNormOrder k / 2 - J.fundamentalScaleOrder 0 := by
    omega
  unfold GoodBONG.universalAlphaThreeUpperBound
  rw [horder1, horder2, hdiv]
  have hupperEq :
      2 * ((ramificationIndex K : ℚ) -
          ((J.UniversalNormOrder k / 2 -
            J.fundamentalScaleOrder 0 : Int) : ℚ)) - 1 =
        ((2 * (ramificationIndex K : Int) +
          2 * J.fundamentalScaleOrder 0 -
          2 * (J.UniversalNormOrder k / 2) - 1 : Int) : ℚ) := by
    push_cast
    ring
  rw [hupperEq]
  change _ ↔ Lattice.powerIdeal (K := K)
    (2 * (ramificationIndex K : Int) +
      2 * J.fundamentalScaleOrder 0 -
      2 * (J.UniversalNormOrder k / 2)) < J.fundamentalIdeal z
  by_cases heven : Even (J.boundaryNormOrderSum z)
  · obtain ⟨I, hcarrier, halpha⟩ :=
      P.exists_orderedFundamentalIdeal_order_eq_alpha_of_even z heven
    rw [hboundary] at halpha
    rw [← hcarrier, I.carrier_eq_powerIdeal,
      Lattice.powerIdeal_lt_iff]
    rw [← halpha]
    constructor
    · intro h
      have hz : I.order ≤
          2 * (ramificationIndex K : Int) +
            2 * J.fundamentalScaleOrder 0 -
            2 * (J.UniversalNormOrder k / 2) - 1 := by
        exact_mod_cast h
      omega
    · intro h
      have hz : I.order ≤
          2 * (ramificationIndex K : Int) +
            2 * J.fundamentalScaleOrder 0 -
            2 * (J.UniversalNormOrder k / 2) - 1 := by omega
      exact_mod_cast hz
  · have hodd : Odd (J.boundaryNormOrderSum z) :=
      Int.not_even_iff_odd.mp heven
    let I := J.oddOrderedFundamentalIdeal z hodd
    have hgapRaw :=
      P.orderGap_boundaryIndex_eq_boundaryNormOrderSum_sub_twoScale z
    have hIgap : I.order = a.orderGap (P.boundaryIndex z) := by
      exact hgapRaw.symm
    rw [hboundary] at hIgap
    have hgapOdd : Odd (a.orderGap (P.boundaryIndex z)) := by
      rw [hgapRaw]
      rcases hodd with ⟨d, hd⟩
      refine ⟨d - J.fundamentalScaleOrder
        (Lattice.JordanDecomposition.boundaryLeftIndex z), ?_⟩
      omega
    change _ ↔ Lattice.powerIdeal (K := K)
      (2 * (ramificationIndex K : Int) +
        2 * J.fundamentalScaleOrder 0 -
        2 * (J.UniversalNormOrder k / 2)) < I.carrier
    rw [I.carrier_eq_powerIdeal, Lattice.powerIdeal_lt_iff]
    by_cases hgapLe : a.orderGap (P.boundaryIndex z) ≤
        2 * (ramificationIndex K : Int)
    · have halpha :=
        (a.alpha_p3 (P.boundaryIndex z) hgapLe).2.mpr
          (Or.inr hgapOdd)
      rw [hboundary] at halpha
      rw [halpha, ← hIgap]
      constructor
      · intro h
        have hz : I.order ≤
            2 * (ramificationIndex K : Int) +
              2 * J.fundamentalScaleOrder 0 -
              2 * (J.UniversalNormOrder k / 2) - 1 := by
          exact_mod_cast h
        omega
      · intro h
        have hz : I.order ≤
            2 * (ramificationIndex K : Int) +
              2 * J.fundamentalScaleOrder 0 -
              2 * (J.UniversalNormOrder k / 2) - 1 := by omega
        exact_mod_cast hz
    · have hgapGt : 2 * (ramificationIndex K : Int) <
          a.orderGap (P.boundaryIndex z) := by omega
      have halphaGt : 2 * (ramificationIndex K : ℚ) <
          a.alphaValue (P.boundaryIndex z) :=
        (a.beli2009Corollary28_ii
          (P.boundaryIndex z)).2.2.mpr hgapGt
      rw [hboundary] at halphaGt
      have hthreshold :
          2 * (ramificationIndex K : Int) +
              2 * J.fundamentalScaleOrder 0 -
              2 * (J.UniversalNormOrder k / 2) ≤
            2 * (ramificationIndex K : Int) - 2 := by
        omega
      constructor
      · intro h
        have hupper :
            a.alphaValue (⟨2, by omega⟩ : Fin (n + 1)) <
              2 * (ramificationIndex K : ℚ) := by
          have hthresholdQ :
              ((2 * (ramificationIndex K : Int) +
                  2 * J.fundamentalScaleOrder 0 -
                  2 * (J.UniversalNormOrder k / 2) - 1 : Int) : ℚ) <
                2 * (ramificationIndex K : ℚ) := by
            exact_mod_cast (show
              2 * (ramificationIndex K : Int) +
                  2 * J.fundamentalScaleOrder 0 -
                  2 * (J.UniversalNormOrder k / 2) - 1 <
                2 * (ramificationIndex K : Int) by omega)
          exact h.trans_lt hthresholdQ
        exact False.elim ((not_lt_of_ge halphaGt.le) hupper)
      · intro h
        have hIgt : 2 * (ramificationIndex K : Int) < I.order := by
          rw [hIgap]
          simpa only [hboundary] using hgapGt
        omega

end BONG.JordanOrderProfileWitness

namespace BONG.StrictJordanAdaptedAlignment

variable {n : Nat} {a : GoodBONG q L (n + 2)}

/-- If the first adapted Jordan component is binary and is followed by
another component, its isotropy is exactly the binary-prefix isotropy in
Theorem 2.1. -/
theorem universalFirstTwoIsotropic_iff_sourceFirstComponentIsIsotropic
    (S : StrictJordanAdaptedAlignment a.toBONG a.toBONG)
    {t : Nat} (hcount : S.componentCount = t + 1) (ht : 0 < t)
    (hrank : (S.sourceJordanSucc hcount).componentRank 0 = 2) :
    a.UniversalFirstTwoIsotropic ↔
      (S.sourceJordanSucc hcount).ComponentIsIsotropic 0 := by
  let J := S.sourceJordanSucc hcount
  let P := S.sourceProfileSucc hcount
  let z : Fin t := ⟨0, ht⟩
  have hj : (P.boundaryIndex z).val + 1 = 2 := by
    have hraw := P.boundaryIndex_succ_val_eq_componentRankPrefix z
    have hIio :
        Finset.Iio (Lattice.JordanDecomposition.boundaryRightIndex z) =
          {(⟨0, by omega⟩ : Fin (t + 1))} := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_singleton, Fin.ext_iff]
      change k.val < 1 ↔ k.val = 0
      omega
    change (P.boundaryIndex z).val + 1 =
      ∑ k ∈ Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex z),
          J.componentRank k at hraw
    rw [hIio, Finset.sum_singleton] at hraw
    have hzero : (⟨0, by omega⟩ : Fin (t + 1)) = 0 := by
      ext
      rfl
    rw [hzero, hrank] at hraw
    exact hraw
  have hboundary := S.sourceBoundaryPrefix_diagonalIsotropic_iff hcount z
  dsimp only at hboundary
  have hj' :
      ((S.sourceProfileSucc hcount).boundaryIndex z).val + 1 = 2 := by
    simpa only [P] using hj
  have hboundary' :
      DiagonalIsotropic (a.prefixValues 2 (by omega)) ↔
        ¬(J.prefixSpace 1).IsAnisotropicSpace := by
    have hdiag := a.diagonalIsotropic_prefixValues_congr
      (k := ((S.sourceProfileSucc hcount).boundaryIndex z).val + 1)
      (l := 2) (by omega) (by omega) hj'
    have hresult := hdiag.symm.trans hboundary
    simpa only [J, z] using hresult
  have hfirst :=
    J.toOrthogonalDecomposition.firstComponentPrefixLatticeIsometry
      |>.toQuadraticSpaceIsometry
      |>.isAnisotropicSpace_iff_general
  change a.UniversalFirstTwoIsotropic ↔ ¬(J.component 0).space.IsAnisotropicSpace
  unfold GoodBONG.UniversalFirstTwoIsotropic
  exact hboundary'.trans (not_congr hfirst).symm

/-- In rank three the complete good-BONG diagonal is isotropic exactly when
the ambient quadratic space is isotropic.  This is the terminal-component
counterpart of the boundary lemmas below. -/
theorem GoodBONG.universalFirstThreeIsotropic_iff_ambientIsotropic
    (a : GoodBONG q L 3) :
    a.UniversalFirstThreeIsotropic (by omega) ↔
      ¬q.IsAnisotropicSpace := by
  have hf := QuadraticSpace.Isometry.isAnisotropicSpace_iff_general
    a.toBONG.exactDiagonalizationIsometry
  have hd := QuadraticSpace.not_finiteDiagonal_isAnisotropicSpace_iff
    a.toBONG.value a.toBONG.value_ne_zero
  have hvalues : a.prefixValues 3 (by omega) = a.toBONG.value := by
    funext i
    rfl
  unfold GoodBONG.UniversalFirstThreeIsotropic
  rw [hvalues]
  exact hd.symm.trans (not_congr hf).symm

/-- If the first adapted Jordan component is ternary and is followed by
another component, its isotropy is exactly the ternary-prefix isotropy in
Theorem 2.1. -/
theorem universalFirstThreeIsotropic_iff_sourceFirstComponentIsIsotropic
    (S : StrictJordanAdaptedAlignment a.toBONG a.toBONG)
    {t : Nat} (hcount : S.componentCount = t + 1) (ht : 0 < t)
    (hrank : (S.sourceJordanSucc hcount).componentRank 0 = 3) :
    a.UniversalFirstThreeIsotropic (by
      have hsum := (S.sourceProfileSucc hcount).sum_componentRank_eq_length
      change (∑ k, (S.sourceJordanSucc hcount).componentRank k) = n + 2 at hsum
      have hle : (S.sourceJordanSucc hcount).componentRank 0 ≤
          ∑ k, (S.sourceJordanSucc hcount).componentRank k :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_univ (0 : Fin (t + 1)))
      rw [hrank, hsum] at hle
      omega) ↔
      (S.sourceJordanSucc hcount).ComponentIsIsotropic 0 := by
  let J := S.sourceJordanSucc hcount
  let P := S.sourceProfileSucc hcount
  let z : Fin t := ⟨0, ht⟩
  have hj : (P.boundaryIndex z).val + 1 = 3 := by
    have hraw := P.boundaryIndex_succ_val_eq_componentRankPrefix z
    have hIio :
        Finset.Iio (Lattice.JordanDecomposition.boundaryRightIndex z) =
          {(⟨0, by omega⟩ : Fin (t + 1))} := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_singleton, Fin.ext_iff]
      change k.val < 1 ↔ k.val = 0
      omega
    change (P.boundaryIndex z).val + 1 =
      ∑ k ∈ Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex z),
          J.componentRank k at hraw
    rw [hIio, Finset.sum_singleton] at hraw
    have hzero : (⟨0, by omega⟩ : Fin (t + 1)) = 0 := by
      ext
      rfl
    rw [hzero, hrank] at hraw
    exact hraw
  have hboundary := S.sourceBoundaryPrefix_diagonalIsotropic_iff hcount z
  dsimp only at hboundary
  have hj' :
      ((S.sourceProfileSucc hcount).boundaryIndex z).val + 1 = 3 := by
    simpa only [P] using hj
  have hboundary' :
      DiagonalIsotropic (a.prefixValues 3 (by omega)) ↔
        ¬(J.prefixSpace 1).IsAnisotropicSpace := by
    have hdiag := a.diagonalIsotropic_prefixValues_congr
      (k := ((S.sourceProfileSucc hcount).boundaryIndex z).val + 1)
      (l := 3) (by omega) (by omega) hj'
    have hresult := hdiag.symm.trans hboundary
    simpa only [J, z] using hresult
  have hfirst :=
    J.toOrthogonalDecomposition.firstComponentPrefixLatticeIsometry
      |>.toQuadraticSpaceIsometry
      |>.isAnisotropicSpace_iff_general
  change a.UniversalFirstThreeIsotropic _ ↔
    ¬(J.component 0).space.IsAnisotropicSpace
  unfold GoodBONG.UniversalFirstThreeIsotropic
  exact hboundary'.trans (not_congr hfirst).symm

/-- If the first two adapted Jordan components have respective ranks two
and one and a third component follows, isotropy of their sum is exactly the
ternary-prefix isotropy in Theorem 2.1. -/
theorem universalFirstThreeIsotropic_iff_sourceFirstTwoComponentsIsotropic
    (S : StrictJordanAdaptedAlignment a.toBONG a.toBONG)
    {t : Nat} (hcount : S.componentCount = t + 1) (ht : 1 < t)
    (hrank0 : (S.sourceJordanSucc hcount).componentRank 0 = 2)
    (hrank1 : (S.sourceJordanSucc hcount).componentRank
      (⟨1, by omega⟩ : Fin (t + 1)) = 1) :
    a.UniversalFirstThreeIsotropic (by
      have hsum := (S.sourceProfileSucc hcount).sum_componentRank_eq_length
      change (∑ k, (S.sourceJordanSucc hcount).componentRank k) = n + 2 at hsum
      have hzeroMem : (0 : Fin (t + 1)) ∈
          (Finset.univ : Finset (Fin (t + 1))) := Finset.mem_univ _
      have honeMem : (⟨1, by omega⟩ : Fin (t + 1)) ∈
          (Finset.univ.erase (0 : Fin (t + 1))) := by
        simp only [Finset.mem_erase]
        constructor
        · norm_num
        · exact Finset.mem_univ _
      have hle1 := Finset.single_le_sum
        (fun _ _ ↦ Nat.zero_le _) honeMem
        (f := fun k ↦ (S.sourceJordanSucc hcount).componentRank k)
      have hdecomp :
          ∑ k, (S.sourceJordanSucc hcount).componentRank k =
            (S.sourceJordanSucc hcount).componentRank 0 +
              ∑ k ∈ (Finset.univ.erase (0 : Fin (t + 1))),
                (S.sourceJordanSucc hcount).componentRank k := by
        rw [← Finset.sum_erase_add _ _ hzeroMem]
        omega
      rw [hrank1] at hle1
      have htotal : 3 ≤
          ∑ k, (S.sourceJordanSucc hcount).componentRank k := by
        rw [hdecomp, hrank0]
        omega
      rw [hsum] at htotal
      omega) ↔
      (S.sourceJordanSucc hcount).ComponentPrefixIsIsotropic 2 := by
  let J := S.sourceJordanSucc hcount
  let P := S.sourceProfileSucc hcount
  let z : Fin t := ⟨1, ht⟩
  have hj : (P.boundaryIndex z).val + 1 = 3 := by
    have hraw := P.boundaryIndex_succ_val_eq_componentRankPrefix z
    let kZero : Fin (t + 1) := ⟨0, by omega⟩
    let kOne : Fin (t + 1) := ⟨1, by omega⟩
    have hIio :
        Finset.Iio (Lattice.JordanDecomposition.boundaryRightIndex z) =
          {kZero, kOne} := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_insert,
        Finset.mem_singleton, Fin.ext_iff]
      change k.val < 2 ↔ k.val = kZero.val ∨ k.val = kOne.val
      simp only [kZero, kOne]
      omega
    change (P.boundaryIndex z).val + 1 =
      ∑ k ∈ Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex z),
          J.componentRank k at hraw
    rw [hIio] at hraw
    have hne : kZero ≠ kOne := by
      intro h
      have := congrArg Fin.val h
      simp only [kZero, kOne] at this
      omega
    rw [Finset.sum_insert (by simpa only [Finset.mem_singleton] using hne),
      Finset.sum_singleton] at hraw
    have hz : kZero = (0 : Fin (t + 1)) := Fin.ext rfl
    have ho : kOne = (⟨1, by omega⟩ : Fin (t + 1)) := Fin.ext rfl
    rw [hz, ho, hrank0, hrank1] at hraw
    exact hraw
  have hboundary := S.sourceBoundaryPrefix_diagonalIsotropic_iff hcount z
  dsimp only at hboundary
  have hj' :
      ((S.sourceProfileSucc hcount).boundaryIndex z).val + 1 = 3 := by
    simpa only [P] using hj
  have hdiag := a.diagonalIsotropic_prefixValues_congr
    (k := ((S.sourceProfileSucc hcount).boundaryIndex z).val + 1)
    (l := 3) (by omega) (by omega) hj'
  have hresult := hdiag.symm.trans hboundary
  change DiagonalIsotropic (a.prefixValues 3 (by omega)) ↔
    ¬(J.toOrthogonalDecomposition.prefixQuadraticSublattice 2).space.IsAnisotropicSpace
  simpa only [J, z] using hresult

end BONG.StrictJordanAdaptedAlignment

namespace Lattice.JordanDecomposition

/-- Under the numerical hypotheses of Case (3.1), isotropy of the binary
first Jordan component is equivalent to its being the integral plane
`2⁻¹ A(0,0)`.  The forward implication uses the dyadic lower-volume
maximality lemma and O'Meara's uniqueness of maximal integral lattices. -/
theorem componentIsIsotropic_iff_firstComponentIsHalfHyperbolic
    {t : Nat} (J : JordanDecomposition q L (t + 1))
    (hrank : J.componentRank 0 = 2)
    (hscale : J.fundamentalScaleOrder 0 =
      -(ramificationIndex K : Int))
    (hnorm : J.UniversalNormOrder 0 = 0) :
    J.ComponentIsIsotropic 0 ↔ J.FirstComponentIsHalfHyperbolic := by
  let X := J.component 0
  let T := QuadraticLatticeModel.halfHyperbolicTower (K := K) 1
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  letI : Module.Finite K X.carrier := X.lattice.moduleFinite
  letI : Module.Finite K T.Carrier := T.lattice.moduleFinite
  let e0 : Fin 2 → K := ![1, 0]
  let z0 : T.Carrier :=
    (e0, (fun i : Fin 0 ↦ Fin.elim0 i))
  have hz0Ne : z0 ≠ 0 := by
    intro hz
    have hfirst := congrArg Prod.fst hz
    have hone := congrFun hfirst 0
    change (1 : K) = 0 at hone
    exact one_ne_zero hone
  have hz0Iso : T.form.quadratic z0 = 0 := by
    have htail : (fun i : Fin 0 ↦ Fin.elim0 i : Fin 0 → K) = 0 :=
      Subsingleton.elim _ _
    change
      ((((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
        (dyadicHalfUnit (K := K))).orthogonalSum
        (halfHyperbolicExtensionForm
          (zeroCoordinateQuadraticSpace (K := K)) 0)).quadratic z0) = 0
    rw [QuadraticSpace.orthogonalSum_quadratic_apply,
      QuadraticSpace.rescaleUnit_quadratic]
    simp [z0, e0, htail, QuadraticSpace.quadratic,
      QuadraticSpace.omearaPlane_bilin_apply,
      halfHyperbolicExtensionForm, omearaPlaneExtensionForm,
      zeroCoordinateQuadraticSpace]
    rfl
  have hTisotropic : ¬T.form.IsAnisotropicSpace := by
    intro h
    exact hz0Ne (h z0 hz0Iso)
  constructor
  · intro hXisotropic
    have heffectiveLeNorm : J.UniversalNormOrder 0 ≤
        ordUnit K (J.normGenerator 0) := by
      unfold UniversalNormOrder BONG.jordanEffectiveNormOrder
        BONG.jordanEffectiveNormOrderAt
      calc
        JordanProfileOrder.effectiveAt
              (fun j ↦ ordUnit K (J.scaleGenerator j))
              (fun j ↦ ordUnit K (J.normGenerator j)) 0
              (ordUnit K (J.scaleGenerator 0)) ≤
            JordanProfileOrder.adjustedAt
              (fun j ↦ ordUnit K (J.scaleGenerator j))
              (fun j ↦ ordUnit K (J.normGenerator j))
              (ordUnit K (J.scaleGenerator 0)) 0 :=
          JordanProfileOrder.effectiveAt_le _ _ _ _ _
        _ = ordUnit K (J.normGenerator 0) := by
          simp [JordanProfileOrder.adjustedAt]
    have hnormNonneg : 0 ≤ ordUnit K (J.normGenerator 0) := by
      rw [hnorm] at heffectiveLeNorm
      exact heffectiveLeNorm
    have hXintegral : IsIntegral X.space X.lattice := by
      rw [isIntegral_iff_normIdeal_le, J.normIdeal_eq]
      change principalIdeal (K := K) (J.normGenerator 0 : K) ≤
        principalIdeal (K := K) (((1 : Kˣ) : K))
      apply (principalIdeal_le_iff_ord_ge
        (Units.ne_zero (J.normGenerator 0)) (Units.ne_zero (1 : Kˣ))).2
      have hone : ord K (((1 : Kˣ) : K)) = 0 := by simp
      rw [hone, ← coe_ordUnit]
      exact WithTop.coe_le_coe.mpr hnormNonneg
    have hscaleOrder : ordUnit K (J.scaleGenerator 0) =
        ordUnit K (dyadicHalfUnit (K := K)) := by
      rw [BONG.GoodBONG.ordUnit_dyadicHalfUnit]
      simpa only [fundamentalScaleOrder] using hscale
    have hXmodular : IsModular X.space X.lattice
        (dyadicHalfUnit (K := K)) := by
      apply (J.modular 0).of_principalIdeal_eq
      exact (principalIdeal_eq_iff_ordUnit_eq _ _).2 hscaleOrder
    have hXmax : IsOMaximal X.space X.lattice :=
      isOMaximal_of_isModular_of_integral_of_order_eq_neg_ramification
        hXmodular hXintegral BONG.GoodBONG.ordUnit_dyadicHalfUnit
    have hTmax : IsOMaximal T.form T.lattice := by
      have hTi := QuadraticLatticeModel.halfHyperbolicTower_isIntegral
        (K := K) 1
      have hTm := halfHyperbolicTower_isModular (K := K) 1
      exact
        isOMaximal_of_isModular_of_integral_of_order_eq_neg_ramification
          hTm hTi BONG.GoodBONG.ordUnit_dyadicHalfUnit
    have hXhyper :=
      QuadraticSpace.rankTwo_isIsometric_hyperbolicPlane_one_of_not_anisotropic
        X.space hrank hXisotropic
    have hTrank : finrank K T.Carrier = 2 := by
      simpa only [QuadraticLatticeModel.rank] using
        QuadraticLatticeModel.halfHyperbolicTower_rank (K := K) 1
    have hThyper :=
      QuadraticSpace.rankTwo_isIsometric_hyperbolicPlane_one_of_not_anisotropic
        T.form hTrank hTisotropic
    have hambient : X.space.IsIsometric T.form := by
      rcases hXhyper with ⟨f⟩
      rcases hThyper with ⟨g⟩
      exact ⟨f.trans g.symm⟩
    exact oMaximal_isIsometric_of_isometric hXmax hTmax hambient
  · rintro ⟨f⟩
    have htransport :=
      f.toQuadraticSpaceIsometry.isAnisotropicSpace_iff_general
    exact mt htransport.mp hTisotropic

/-- With one Jordan component, isotropy of that component is isotropy of the
ambient quadratic space. -/
theorem componentIsIsotropic_zero_iff_ambientIsotropic
    (J : JordanDecomposition q L 1) :
    J.ComponentIsIsotropic 0 ↔ ¬q.IsAnisotropicSpace := by
  have h := J.toOrthogonalDecomposition.singleComponentLatticeIsometry
    |>.toQuadraticSpaceIsometry
    |>.isAnisotropicSpace_iff_general
  exact not_congr h

/-- With two Jordan components, their full prefix is the ambient quadratic
space. -/
theorem componentPrefixIsIsotropic_two_iff_ambientIsotropic
    (J : JordanDecomposition q L 2) :
    J.ComponentPrefixIsIsotropic 2 ↔ ¬q.IsAnisotropicSpace := by
  have h := J.toOrthogonalDecomposition.fullPrefixLatticeIsometry
    |>.toQuadraticSpaceIsometry
    |>.isAnisotropicSpace_iff_general
  exact not_congr h

end Lattice.JordanDecomposition

end Bong
