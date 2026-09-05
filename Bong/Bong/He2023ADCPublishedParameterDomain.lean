/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenCorankTwoGeneric
import Bong.Bong.HeHu2022PublishedTestingSet

/-!
# The representative convention in He (2025), Lemma 6.8(v)--(vi)

The published unit representatives are normalized by `d(delta) = ord(delta - 1)`.
This forces the square representative to be `1`. To read the literal exclusion
`V \ {1, Delta}` as an exclusion of two square classes, the chosen discriminant
representative must also belong to `U`. We expose this compatibility convention
as `hDelta`; it contains no lattice classification assumption.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG HeHuPublishedSquareClassIndex

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A normalized representative of the trivial unit square class is literally `1`. -/
theorem heADCNormalizedRepresentative_eq_one_of_isSquare (c : Kˣ)
    (hn : IsHeHuNormalizedUnitRepresentative c c) (hs : IsSquare c) : c = 1 := by
  have htop : ord K ((c : K) - 1) = ⊤ := by
    rw [← hn.2.2, quadraticDefectIntOrder,
      quadraticDefect_eq_top_of_isSquare (K := K) hs]
    rfl
  apply Units.ext
  exact sub_eq_zero.mp ((ord_eq_top_iff K).mp htop)

/-- On a compatible published representative system, literal exclusions are class exclusions. -/
theorem heADCSharpDomain_publishedParameter_iff
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem U)
    (hDelta : ∃ i, U i = (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (p : HeHuPublishedSquareClassIndex I) :
    HeHuSharpDomain (parameter U p) ↔
      parameter U p ≠ 1 ∧
        parameter U p ≠ (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit := by
  constructor
  · intro hs
    constructor
    · intro h
      apply hs.notSquare
      simp [h]
    · intro h
      apply hs.notDiscriminantSquare
      simp [h]
  · rintro ⟨hone, hdelta⟩
    rcases p with ⟨i, parity⟩
    cases parity with
    | false =>
        simp only [parameter_unit] at hone hdelta ⊢
        constructor
        · intro hs
          exact hone (heADCNormalizedRepresentative_eq_one_of_isSquare (U i) (hU.normalized i) hs)
        · intro hs
          obtain ⟨j, hj⟩ := hDelta
          have hprod : IsSquare (U i * U j) := by
            have H := hs.mul (show IsSquare (U j ^ 2) from ⟨U j, pow_two (U j)⟩)
            rw [← hj] at H
            have heq : U i / U j * U j ^ 2 = U i * U j := by
              simp [pow_two, div_eq_mul_inv, mul_assoc]
            exact heq ▸ H
          have hij := hU.irredundant hprod
          exact hdelta (hij ▸ hj)
    | true =>
        exact heADCUnitUniformizerSharpDomain (U i) (hU.isUnit i)

namespace Lattice

variable {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The printed `V \ {1, Delta}` version of Lemma 6.8(v), with compatible representatives. -/
theorem heADC2025Lemma68vPublished
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem U)
    (hDelta : ∃ i, U i = (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (p : HeHuPublishedSquareClassIndex I)
    (hone : parameter U p ≠ 1)
    (hdelta : parameter U p ≠ (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (k : Nat) (hADC : IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric
      (BONG.coefficientDiagonalSpace (heADCW1Even (k + 1) (parameter U p)))) :
    IsIsometric q (BONG.coefficientDiagonalSpace (heADCW1Even (k + 1) (parameter U p)))
      L (heADCN1Even (k + 1) (parameter U p)).lattice :=
  heADC2025Lemma68v k (parameter U p)
    ((heADCSharpDomain_publishedParameter_iff U hU hDelta p).mpr ⟨hone, hdelta⟩) hADC ambient

/-- The printed `V \ {1, Delta}` version of Lemma 6.8(vi), with compatible representatives. -/
theorem heADC2025Lemma68viPublished
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem U)
    (hDelta : ∃ i, U i = (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (p : HeHuPublishedSquareClassIndex I)
    (hone : parameter U p ≠ 1)
    (hdelta : parameter U p ≠ (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (k : Nat) (hADC : IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace
      (heADCW2Even (k + 1) (parameter U p) (Or.inl (by omega))))) :
    IsIsometric q (BONG.coefficientDiagonalSpace
        (heADCW2Even (k + 1) (parameter U p) (Or.inl (by omega))))
      L (heADCN2Even (k + 1) (parameter U p) (Or.inl (by omega))).lattice :=
  heADC2025Lemma68vi k (parameter U p)
    ((heADCSharpDomain_publishedParameter_iff U hU hDelta p).mpr ⟨hone, hdelta⟩) hADC ambient

end Lattice

end Bong
