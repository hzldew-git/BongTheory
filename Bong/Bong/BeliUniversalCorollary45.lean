/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalLemma44
import Bong.Bong.BeliUniversalAnisotropicQuaternary
import Bong.QuadraticSpace.DyadicHighRankIsotropy

/-!
# Beli's low-rank and stable-rank universality reductions

This file proves Corollary 4.5.  The ternary clause keeps the anisotropic
test family explicit.  The stable clauses are deduced from the concrete
dyadic theorem that every quadratic space of dimension at least five is
isotropic, followed by repeated maximal-lattice hyperbolic splitting.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace QuadraticLatticeModel

/-- Anisotropy of the ambient quadratic space of a bundled lattice. -/
def IsAnisotropic (X : QuadraticLatticeModel (K := K)) : Prop := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  exact X.form.IsAnisotropicSpace

/-- A chosen `O`-maximal lattice on Beli's anisotropic quaternary space.
Uniqueness up to integral isometry is proved by O'Meara 91:1 below. -/
noncomputable def beliAnisotropicQuaternaryOMaximalLattice :
    Lattice K (Fin 4 → K) :=
  Classical.choose (Lattice.exists_oMaximal_lattice
    (beliAnisotropicQuaternaryForm (K := K))
    (Lattice.basisLattice (Pi.basisFun K (Fin 4))))

/-- The chosen lattice on Beli's quaternary space is `O`-maximal. -/
theorem beliAnisotropicQuaternaryOMaximalLattice_isOMaximal :
    Lattice.IsOMaximal (beliAnisotropicQuaternaryForm (K := K))
      (beliAnisotropicQuaternaryOMaximalLattice (K := K)) :=
  Classical.choose_spec (Lattice.exists_oMaximal_lattice
    (beliAnisotropicQuaternaryForm (K := K))
    (Lattice.basisLattice (Pi.basisFun K (Fin 4))))

/-- The bundled `O`-maximal lattice singled out in Corollary 4.5(ii). -/
noncomputable def beliAnisotropicQuaternaryOMaximalModel :
    QuadraticLatticeModel (K := K) :=
  { Carrier := Fin 4 → K
    form := beliAnisotropicQuaternaryForm (K := K)
    lattice := beliAnisotropicQuaternaryOMaximalLattice (K := K) }

theorem beliAnisotropicQuaternaryOMaximalModel_rank :
    (beliAnisotropicQuaternaryOMaximalModel (K := K)).rank = 4 := by
  change finrank K (Fin 4 → K) = 4
  simp

theorem beliAnisotropicQuaternaryOMaximalModel_isOMaximal :
    (beliAnisotropicQuaternaryOMaximalModel (K := K)).IsOMaximal := by
  exact beliAnisotropicQuaternaryOMaximalLattice_isOMaximal (K := K)

theorem beliAnisotropicQuaternaryOMaximalModel_isAnisotropic :
    (beliAnisotropicQuaternaryOMaximalModel (K := K)).IsAnisotropic := by
  exact beliAnisotropicQuaternaryForm_isAnisotropic (K := K)

/-- The bundled formulation of `n`-universality quantifies over exactly all
bundled integral rank-`n` lattices. -/
theorem isNUniversal_iff_models
    (M : QuadraticLatticeModel (K := K)) (n : Nat) :
    M.IsNUniversal n ↔
      M.IsIntegral ∧
        ∀ X : QuadraticLatticeModel (K := K),
          X.rank = n → X.IsIntegral → M.Represents X := by
  letI : AddCommGroup M.Carrier := M.addCommGroup
  letI : Module K M.Carrier := M.module
  constructor
  · rintro ⟨hM, hall⟩
    refine ⟨hM, ?_⟩
    intro X hXrank hX
    letI : AddCommGroup X.Carrier := X.addCommGroup
    letI : Module K X.Carrier := X.module
    change Lattice.Represents M.form X.form M.lattice X.lattice
    exact hall X.form X.lattice (by
      change finrank K X.Carrier = n at hXrank
      exact hXrank) hX
  · rintro ⟨hM, hall⟩
    refine ⟨hM, ?_⟩
    intro W _ _ r A hArank hA
    let X : QuadraticLatticeModel (K := K) :=
      { Carrier := W
        form := r
        lattice := A }
    have hXrank : X.rank = n := by
      change finrank K W = n
      exact hArank
    have hrep := hall X hXrank hA
    change Lattice.Represents M.form r M.lattice A at hrep
    exact hrep

/-- An isometric half-hyperbolic presentation with integral residual makes
the total lattice integral. -/
theorem integral_of_adjoinHalfHyperbolic_isometry
    {M R : QuadraticLatticeModel (K := K)} {k : Nat}
    (hR : R.IsIntegral)
    (f : (R.adjoinHalfHyperbolic k).Isometry M) : M.IsIntegral := by
  letI : AddCommGroup M.Carrier := M.addCommGroup
  letI : Module K M.Carrier := M.module
  letI : AddCommGroup R.Carrier := R.addCommGroup
  letI : Module K R.Carrier := R.module
  letI : AddCommGroup (R.adjoinHalfHyperbolic k).Carrier :=
    (R.adjoinHalfHyperbolic k).addCommGroup
  letI : Module K (R.adjoinHalfHyperbolic k).Carrier :=
    (R.adjoinHalfHyperbolic k).module
  exact (Lattice.isIntegral_iff_of_latticeIsometry f).1
    (hR.adjoinHalfHyperbolic k)

/-- Failure of anisotropy is equivalent to the existence of a nonzero
isotropic vector. -/
theorem exists_isotropic_of_not_anisotropic
    (X : QuadraticLatticeModel (K := K))
    (hX : ¬ X.IsAnisotropic) : by
    letI : AddCommGroup X.Carrier := X.addCommGroup
    letI : Module K X.Carrier := X.module
    exact ∃ z : X.Carrier, z ≠ 0 ∧ X.form.quadratic z = 0 := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  change ¬ X.form.IsAnisotropicSpace at hX
  rw [QuadraticSpace.IsAnisotropicSpace] at hX
  push Not at hX
  obtain ⟨z, hz, hzne⟩ := hX
  exact ⟨z, hzne, hz⟩

/-- A nonzero isotropic vector supplies one half-hyperbolic summand. -/
theorem hasWittIndexAtLeast_one_of_not_anisotropic
    (X : QuadraticLatticeModel (K := K))
    (hX : ¬ X.IsAnisotropic) : X.HasWittIndexAtLeast 1 := by
  classical
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  obtain ⟨z, hzNe, hzIso⟩ := X.exists_isotropic_of_not_anisotropic hX
  obtain ⟨P, hPmax⟩ := exists_oMaximal_lattice X.form X.lattice
  let D := oMaximalRescaledTwoDecomposition hPmax hzNe hzIso
  let tailForm :=
    (D.component 1).space.rescaleUnit (dyadicHalfUnit (K := K))
  let R : QuadraticLatticeModel (K := K) :=
    { Carrier := (D.component 1).carrier
      form := tailForm
      lattice := (D.component 1).lattice }
  let split := oMaximalHyperbolicSplitIsometry hPmax hzNe hzIso
  let head := scaledZeroOmearaPlaneLatticeIsometry
    (dyadicHalfUnit (K := K))
  let tail := Isometry.refl tailForm (D.component 1).lattice
  let total := (head.orthogonalProductBasic tail).trans split
  refine ⟨R, ⟨?_⟩⟩
  exact total.symm.toQuadraticSpaceIsometry

/-- Every rank `2k+r` dyadic quadratic space with `r ≥ 3` has Witt index
at least `k`.  This is the iterated form of the rank-at-least-five isotropy
theorem. -/
theorem hasWittIndexAtLeast_of_rank_eq_two_mul_add
    (r : Nat) (hr : 3 ≤ r) :
    ∀ (k : Nat) (X : QuadraticLatticeModel (K := K)),
      X.rank = 2 * k + r → X.HasWittIndexAtLeast k
  | 0, X, _ => by
      letI : AddCommGroup X.Carrier := X.addCommGroup
      letI : Module K X.Carrier := X.module
      exact ⟨X, ⟨QuadraticSpace.Isometry.refl X.form⟩⟩
  | k + 1, X, hXrank => by
      classical
      letI : AddCommGroup X.Carrier := X.addCommGroup
      letI : Module K X.Carrier := X.module
      letI : Module.Finite K X.Carrier := X.lattice.moduleFinite
      have hfive : 5 ≤ finrank K X.Carrier := by
        change finrank K X.Carrier = 2 * (k + 1) + r at hXrank
        omega
      obtain ⟨z, hzNe, hzIso⟩ :=
        X.form.exists_ne_zero_quadratic_eq_zero_of_five_le_finrank hfive
      obtain ⟨P, hPmax⟩ := exists_oMaximal_lattice X.form X.lattice
      let D := oMaximalRescaledTwoDecomposition hPmax hzNe hzIso
      let tailForm :=
        (D.component 1).space.rescaleUnit (dyadicHalfUnit (K := K))
      let R : QuadraticLatticeModel (K := K) :=
        { Carrier := (D.component 1).carrier
          form := tailForm
          lattice := (D.component 1).lattice }
      let split := oMaximalHyperbolicSplitIsometry hPmax hzNe hzIso
      let head := scaledZeroOmearaPlaneLatticeIsometry
        (dyadicHalfUnit (K := K))
      let tail := Isometry.refl tailForm (D.component 1).lattice
      let total := (head.orthogonalProductBasic tail).trans split
      have hfirst : X.form.IsIsometric
          (halfHyperbolicExtensionForm R.form 1) :=
        ⟨total.symm.toQuadraticSpaceIsometry⟩
      have hRrank : R.rank = 2 * k + r := by
        rcases hfirst with ⟨f⟩
        have hfin := f.toLinearEquiv.finrank_eq
        change X.rank = (R.adjoinHalfHyperbolic 1).rank at hfin
        rw [rank_adjoinHalfHyperbolic] at hfin
        rw [hXrank] at hfin
        omega
      obtain ⟨S, ⟨hrest⟩⟩ :=
        hasWittIndexAtLeast_of_rank_eq_two_mul_add r hr k R hRrank
      letI : AddCommGroup S.Carrier := S.addCommGroup
      letI : Module K S.Carrier := S.module
      rcases hfirst with ⟨hfirst⟩
      let headForm :=
        (QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
          (dyadicHalfUnit (K := K))
      let extendRest : QuadraticSpace.Isometry
          (halfHyperbolicExtensionForm R.form 1)
          (halfHyperbolicExtensionForm S.form (k + 1)) :=
        (QuadraticSpace.Isometry.refl headForm).orthogonalSum hrest
      exact ⟨S, ⟨hfirst.trans extendRest⟩⟩

/-- In particular, every rank `2k+3` space has Witt index at least `k`. -/
theorem hasWittIndexAtLeast_of_rank_two_mul_add_three
    (k : Nat) (X : QuadraticLatticeModel (K := K))
    (hXrank : X.rank = 2 * k + 3) : X.HasWittIndexAtLeast k :=
  hasWittIndexAtLeast_of_rank_eq_two_mul_add 3 (by omega) k X hXrank

/-- In particular, every rank `2k+4` space has Witt index at least `k`. -/
theorem hasWittIndexAtLeast_of_rank_two_mul_add_four
    (k : Nat) (X : QuadraticLatticeModel (K := K))
    (hXrank : X.rank = 2 * k + 4) : X.HasWittIndexAtLeast k :=
  hasWittIndexAtLeast_of_rank_eq_two_mul_add 4 (by omega) k X hXrank

/-- The anisotropic maximal-lattice test family in Corollary 4.5(i). -/
def RepresentsAllOMaximalAnisotropicOfRank
    (M : QuadraticLatticeModel (K := K)) (n : Nat) : Prop :=
  ∀ X : QuadraticLatticeModel (K := K),
    X.rank = n → X.IsOMaximal → X.IsAnisotropic → M.Represents X

end QuadraticLatticeModel

/-- Beli, Corollary 4.5(i): ternary universality is the isotropic splitting
condition together with the remaining anisotropic maximal-lattice tests. -/
theorem beliUniversalCorollary45i
    (M : QuadraticLatticeModel (K := K)) :
    M.IsNUniversal 3 ↔
      (∃ M' : QuadraticLatticeModel (K := K),
          M'.IsNUniversal 1 ∧
          Nonempty ((M'.adjoinHalfHyperbolic 1).Isometry M)) ∧
        M.RepresentsAllOMaximalAnisotropicOfRank 3 := by
  classical
  letI : AddCommGroup M.Carrier := M.addCommGroup
  letI : Module K M.Carrier := M.module
  constructor
  · intro hM
    have hmodels :=
      (QuadraticLatticeModel.isNUniversal_iff_models M 3).1 hM
    refine ⟨?_, ?_⟩
    · apply (beliUniversalLemma44 1 3 (by omega) (by omega) M hmodels.1).1
      intro X hXrank hXIntegral _hWitt
      exact hmodels.2 X hXrank hXIntegral
    · intro X hXrank hXmax _hAnisotropic
      letI : AddCommGroup X.Carrier := X.addCommGroup
      letI : Module K X.Carrier := X.module
      exact hmodels.2 X hXrank hXmax.isIntegral
  · rintro ⟨hsplit, hanisotropic⟩
    obtain ⟨M', hM'Universal, ⟨f⟩⟩ := hsplit
    have hMIntegral : M.IsIntegral :=
      QuadraticLatticeModel.integral_of_adjoinHalfHyperbolic_isometry
        hM'Universal.1 f
    have hisotropic :=
      (beliUniversalLemma44 1 3 (by omega) (by omega) M hMIntegral).2
        ⟨M', hM'Universal, ⟨f⟩⟩
    rw [QuadraticLatticeModel.isNUniversal_iff_models]
    refine ⟨hMIntegral, ?_⟩
    intro X hXrank hXIntegral
    by_cases hXanisotropic : X.IsAnisotropic
    · letI : AddCommGroup X.Carrier := X.addCommGroup
      letI : Module K X.Carrier := X.module
      obtain ⟨P, hXP, hPmax⟩ :=
        exists_oMaximal_superlattice (q := X.form) (L := X.lattice) hXIntegral
      let Pmodel : QuadraticLatticeModel (K := K) :=
        { Carrier := X.Carrier
          form := X.form
          lattice := P }
      have hPrep := hanisotropic Pmodel (by
        change finrank K X.Carrier = 3
        change finrank K X.Carrier = 3 at hXrank
        exact hXrank) hPmax hXanisotropic
      change Lattice.Represents M.form X.form M.lattice X.lattice
      exact hPrep.trans (represents_of_le X.form hXP)
    · exact hisotropic X hXrank hXIntegral
        (X.hasWittIndexAtLeast_one_of_not_anisotropic hXanisotropic)

/-- Beli, Corollary 4.5(ii): quaternary universality is the isotropic
splitting condition together with representation of the `O`-maximal lattice
on the unique anisotropic quaternary space `[1,-Δ,π,-Δπ]`. -/
theorem beliUniversalCorollary45ii
    (M : QuadraticLatticeModel (K := K)) :
    M.IsNUniversal 4 ↔
      (∃ M' : QuadraticLatticeModel (K := K),
          M'.IsNUniversal 2 ∧
          Nonempty ((M'.adjoinHalfHyperbolic 1).Isometry M)) ∧
        M.Represents
          (QuadraticLatticeModel.beliAnisotropicQuaternaryOMaximalModel
            (K := K)) := by
  classical
  letI : AddCommGroup M.Carrier := M.addCommGroup
  letI : Module K M.Carrier := M.module
  let A :=
    QuadraticLatticeModel.beliAnisotropicQuaternaryOMaximalModel
      (K := K)
  letI : AddCommGroup A.Carrier := A.addCommGroup
  letI : Module K A.Carrier := A.module
  constructor
  · intro hM
    have hmodels :=
      (QuadraticLatticeModel.isNUniversal_iff_models M 4).1 hM
    refine ⟨?_, ?_⟩
    · apply (beliUniversalLemma44 1 4 (by omega) (by omega)
        M hmodels.1).1
      intro X hXrank hXIntegral _hWitt
      exact hmodels.2 X hXrank hXIntegral
    · exact hmodels.2 A
        QuadraticLatticeModel.beliAnisotropicQuaternaryOMaximalModel_rank
        QuadraticLatticeModel.beliAnisotropicQuaternaryOMaximalModel_isOMaximal.isIntegral
  · rintro ⟨hsplit, hA⟩
    obtain ⟨M', hM'Universal, ⟨f⟩⟩ := hsplit
    have hMIntegral : M.IsIntegral :=
      QuadraticLatticeModel.integral_of_adjoinHalfHyperbolic_isometry
        hM'Universal.1 f
    have hisotropic :=
      (beliUniversalLemma44 1 4 (by omega) (by omega) M hMIntegral).2
        ⟨M', hM'Universal, ⟨f⟩⟩
    rw [QuadraticLatticeModel.isNUniversal_iff_models]
    refine ⟨hMIntegral, ?_⟩
    intro X hXrank hXIntegral
    by_cases hXanisotropic : X.IsAnisotropic
    · letI : AddCommGroup X.Carrier := X.addCommGroup
      letI : Module K X.Carrier := X.module
      letI : Module.Finite K X.Carrier := X.lattice.moduleFinite
      obtain ⟨P, hXP, hPmax⟩ :=
        exists_oMaximal_superlattice (q := X.form) (L := X.lattice)
          hXIntegral
      have hambient : X.form.IsIsometric
          (beliAnisotropicQuaternaryForm (K := K)) := by
        apply anisotropicQuaternary_isIsometric_beliModel X.form
        · change finrank K X.Carrier = 4 at hXrank
          exact hXrank
        · change X.form.IsAnisotropicSpace at hXanisotropic
          exact hXanisotropic
      have hPtoA : Lattice.IsIsometric X.form
          (beliAnisotropicQuaternaryForm (K := K)) P
          (QuadraticLatticeModel.beliAnisotropicQuaternaryOMaximalLattice
            (K := K)) :=
        oMaximal_isIsometric_of_isometric hPmax
          QuadraticLatticeModel.beliAnisotropicQuaternaryOMaximalLattice_isOMaximal
          hambient
      change Lattice.Represents M.form X.form M.lattice X.lattice
      have hMP : Lattice.Represents M.form X.form M.lattice P := by
        change Lattice.Represents M.form
          (beliAnisotropicQuaternaryForm (K := K)) M.lattice
          (QuadraticLatticeModel.beliAnisotropicQuaternaryOMaximalLattice
            (K := K)) at hA
        exact hA.trans hPtoA.represents
      exact hMP.trans (represents_of_le X.form hXP)
    · exact hisotropic X hXrank hXIntegral
        (X.hasWittIndexAtLeast_one_of_not_anisotropic hXanisotropic)

/-- Beli, Corollary 4.5(iii). -/
theorem beliUniversalCorollary45iii
    (k : Nat) (hk : 1 ≤ k)
    (M : QuadraticLatticeModel (K := K)) :
    M.IsNUniversal (2 * k + 3) ↔
      ∃ M' : QuadraticLatticeModel (K := K),
        M'.IsNUniversal 3 ∧
        Nonempty ((M'.adjoinHalfHyperbolic k).Isometry M) := by
  classical
  constructor
  · intro hM
    have hmodels :=
      (QuadraticLatticeModel.isNUniversal_iff_models M (2 * k + 3)).1 hM
    have h := (beliUniversalLemma44 k (2 * k + 3) hk (by omega)
      M hmodels.1).1 (by
        intro X hXrank hXIntegral _hWitt
        exact hmodels.2 X hXrank hXIntegral)
    simpa using h
  · rintro ⟨M', hM', ⟨f⟩⟩
    have hMIntegral : M.IsIntegral :=
      QuadraticLatticeModel.integral_of_adjoinHalfHyperbolic_isometry hM'.1 f
    have hrep := (beliUniversalLemma44 k (2 * k + 3) hk (by omega)
      M hMIntegral).2 (by simpa using ⟨M', hM', ⟨f⟩⟩)
    rw [QuadraticLatticeModel.isNUniversal_iff_models]
    refine ⟨hMIntegral, ?_⟩
    intro X hXrank hXIntegral
    exact hrep X hXrank hXIntegral
      (X.hasWittIndexAtLeast_of_rank_two_mul_add_three k hXrank)

/-- Beli, Corollary 4.5(iv). -/
theorem beliUniversalCorollary45iv
    (k : Nat) (hk : 1 ≤ k)
    (M : QuadraticLatticeModel (K := K)) :
    M.IsNUniversal (2 * k + 4) ↔
      ∃ M' : QuadraticLatticeModel (K := K),
        M'.IsNUniversal 4 ∧
        Nonempty ((M'.adjoinHalfHyperbolic k).Isometry M) := by
  classical
  constructor
  · intro hM
    have hmodels :=
      (QuadraticLatticeModel.isNUniversal_iff_models M (2 * k + 4)).1 hM
    have h := (beliUniversalLemma44 k (2 * k + 4) hk (by omega)
      M hmodels.1).1 (by
        intro X hXrank hXIntegral _hWitt
        exact hmodels.2 X hXrank hXIntegral)
    simpa using h
  · rintro ⟨M', hM', ⟨f⟩⟩
    have hMIntegral : M.IsIntegral :=
      QuadraticLatticeModel.integral_of_adjoinHalfHyperbolic_isometry hM'.1 f
    have hrep := (beliUniversalLemma44 k (2 * k + 4) hk (by omega)
      M hMIntegral).2 (by simpa using ⟨M', hM', ⟨f⟩⟩)
    rw [QuadraticLatticeModel.isNUniversal_iff_models]
    refine ⟨hMIntegral, ?_⟩
    intro X hXrank hXIntegral
    exact hrep X hXrank hXIntegral
      (X.hasWittIndexAtLeast_of_rank_two_mul_add_four k hXrank)

end Lattice

end Bong
