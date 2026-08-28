/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaOddQuaternaryInvariants
import Bong.Lattice.Omeara9318DiscriminantTwist
import Bong.Bong.DiagonalHassePairScaling
import Bong.Dyadic.UnramifiedNormDirectProof

/-!
# The two odd quaternary models in O'Meara 93:18(iii)

For `d = 1 + alpha` the two printed lattices are

`J = A(a,-alpha/a) ⊥ A(b,0)`

and

`K = A(a,-(alpha-4rho)/a) ⊥ A(b,4rho/b)`.

This file packages the ordinary integrality and ideal facts needed to form
the two lattices, proves their common norm group, and records their explicit
diagonal coefficient families.  The hypotheses below are propositions about
the displayed scalars, not a new local-law interface; a later file derives
them from the norm, weight, and discriminant data of an arbitrary lattice.
-/

namespace Bong

open Dyadic BONG.GoodBONG

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [laws : DyadicDiscriminantClassLaws K]

/-- Ordinary scalar and ideal facts needed by the two models of 93:18(iii). -/
structure Omeara9318RankFourModelParameters (K : Type u)
    [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [modelLaws : DyadicDiscriminantClassLaws K] where
  a : Kˣ
  b : Kˣ
  alpha : K
  alpha_maximal : IsInMaximalIdeal K alpha
  discriminant_unit : IsValuationUnit K (1 + alpha)
  shifted_discriminant_unit :
    IsValuationUnit K (1 + alpha - 4 * modelLaws.rho)
  a_integral : (a : K) ∈ IntegerRing K
  b_integral : (b : K) ∈ IntegerRing K
  bIdeal_le_aIdeal :
    principalIdeal (K := K) (b : K) ≤ principalIdeal (K := K) (a : K)
  twoIdeal_le_bIdeal :
    principalIdeal (K := K) (2 : K) ≤ principalIdeal (K := K) (b : K)
  jLeftTail_integral : -alpha * (a : K)⁻¹ ∈ IntegerRing K
  kLeftTail_integral :
    -(alpha - 4 * modelLaws.rho) * (a : K)⁻¹ ∈ IntegerRing K
  kRightTail_integral :
    4 * modelLaws.rho * (b : K)⁻¹ ∈ IntegerRing K
  jLeftTailIdeal_le_bIdeal :
    principalIdeal (K := K) (-alpha * (a : K)⁻¹) ≤
      principalIdeal (K := K) (b : K)
  kLeftTailIdeal_le_bIdeal :
    principalIdeal (K := K)
        (-(alpha - 4 * modelLaws.rho) * (a : K)⁻¹) ≤
      principalIdeal (K := K) (b : K)
  kRightTailIdeal_le_bIdeal :
    principalIdeal (K := K) (4 * modelLaws.rho * (b : K)⁻¹) ≤
      principalIdeal (K := K) (b : K)
  odd_orders : Odd (ordUnit K a + ordUnit K b)

namespace Omeara9318RankFourModelParameters

variable (P : Omeara9318RankFourModelParameters K)

private theorem valuationUnit_ne_zero {x : K}
    (hx : IsValuationUnit K x) : x ≠ 0 := by
  intro hzero
  rw [hzero, IsValuationUnit, ord_zero] at hx
  exact WithTop.top_ne_coe hx

private theorem j_left_determinant :
    (P.a : K) * (-P.alpha * (P.a : K)⁻¹) - 1 =
      -(1 + P.alpha) := by
  field_simp [Units.ne_zero P.a]
  ring

private theorem k_left_determinant :
    (P.a : K) * (-(P.alpha - 4 * laws.rho) * (P.a : K)⁻¹) - 1 =
      -(1 + P.alpha - 4 * laws.rho) := by
  field_simp [Units.ne_zero P.a]
  ring

private theorem k_right_determinant :
    (P.b : K) * (4 * laws.rho * (P.b : K)⁻¹) - 1 =
      -(laws.discriminantUnit : K) := by
  rw [laws.discriminant_eq_one_sub_four_mul_rho]
  field_simp [Units.ne_zero P.b]
  ring

/-- O'Meara's first quaternary model `J`. -/
noncomputable def jData : OmearaOddQuaternaryModelData K where
  a := P.a
  b := P.b
  leftTail := -P.alpha * (P.a : K)⁻¹
  rightTail := 0
  left_nondegenerate := by
    apply sub_ne_zero.mp
    rw [P.j_left_determinant]
    exact neg_ne_zero.mpr (valuationUnit_ne_zero P.discriminant_unit)
  right_nondegenerate := by simp
  a_integral := P.a_integral
  b_integral := P.b_integral
  leftTail_integral := P.jLeftTail_integral
  rightTail_integral := (IntegerRing K).zero_mem
  left_determinant_unit := by
    rw [P.j_left_determinant, IsValuationUnit, ord_neg]
    exact P.discriminant_unit
  right_determinant_unit := by simp [IsValuationUnit]
  bIdeal_le_aIdeal := P.bIdeal_le_aIdeal
  twoIdeal_le_bIdeal := P.twoIdeal_le_bIdeal
  leftTailIdeal_le_bIdeal := P.jLeftTailIdeal_le_bIdeal
  rightTailIdeal_le_bIdeal := by
    rw [principalIdeal]
    simp
  odd_orders := P.odd_orders

/-- O'Meara's discriminant-twisted quaternary model `K`. -/
noncomputable def kData : OmearaOddQuaternaryModelData K where
  a := P.a
  b := P.b
  leftTail := -(P.alpha - 4 * laws.rho) * (P.a : K)⁻¹
  rightTail := 4 * laws.rho * (P.b : K)⁻¹
  left_nondegenerate := by
    apply sub_ne_zero.mp
    rw [P.k_left_determinant]
    exact neg_ne_zero.mpr
      (valuationUnit_ne_zero P.shifted_discriminant_unit)
  right_nondegenerate := by
    apply sub_ne_zero.mp
    rw [P.k_right_determinant]
    exact neg_ne_zero.mpr
      (valuationUnit_ne_zero laws.discriminant_isValuationUnit)
  a_integral := P.a_integral
  b_integral := P.b_integral
  leftTail_integral := P.kLeftTail_integral
  rightTail_integral := P.kRightTail_integral
  left_determinant_unit := by
    rw [P.k_left_determinant, IsValuationUnit, ord_neg]
    exact P.shifted_discriminant_unit
  right_determinant_unit := by
    rw [P.k_right_determinant, IsValuationUnit, ord_neg]
    exact laws.discriminant_isValuationUnit
  bIdeal_le_aIdeal := P.bIdeal_le_aIdeal
  twoIdeal_le_bIdeal := P.twoIdeal_le_bIdeal
  leftTailIdeal_le_bIdeal := P.kLeftTailIdeal_le_bIdeal
  rightTailIdeal_le_bIdeal := P.kRightTailIdeal_le_bIdeal
  odd_orders := P.odd_orders

/-- Both models have the norm group printed in O'Meara's proof. -/
theorem j_normGroupSet_eq :
    normGroupSet P.jData.space P.jData.lattice =
      integralSquareCoset (P.a : K)
        (principalIdeal (K := K) (P.b : K)) :=
  P.jData.normGroupSet_eq

theorem k_normGroupSet_eq :
    normGroupSet P.kData.space P.kData.lattice =
      integralSquareCoset (P.a : K)
        (principalIdeal (K := K) (P.b : K)) :=
  P.kData.normGroupSet_eq

/-- Unit-valued discriminant `1 + alpha`. -/
noncomputable def d : Kˣ :=
  omeara9318DiscriminantUnit P.alpha P.discriminant_unit

/-- Unit-valued shifted discriminant `1 + alpha - 4 rho`. -/
noncomputable def dShift : Kˣ :=
  omeara9318ShiftedDiscriminantUnit P.alpha
    P.shifted_discriminant_unit

/-- Explicit diagonal coefficient family of `J`. -/
noncomputable def jDiagonalUnits : Fin 4 → Kˣ :=
  ![P.a, -(P.d * P.a⁻¹), P.b, -(P.b⁻¹)]

/-- Explicit diagonal coefficient family of `K`. -/
noncomputable def kDiagonalUnits : Fin 4 → Kˣ :=
  ![P.a, -(P.dShift * P.a⁻¹), P.b,
    -(laws.discriminantUnit * P.b⁻¹)]

theorem jData_diagonalUnits_eq :
    P.jData.diagonalUnits = P.jDiagonalUnits := by
  funext i
  fin_cases i
  · rfl
  · change P.jData.diagonalUnits (1 : Fin 4) =
      P.jDiagonalUnits (1 : Fin 4)
    apply Units.ext
    rw [OmearaOddQuaternaryModelData.diagonalUnits_one]
    simp [jData, jDiagonalUnits, d,
      coe_omeara9318DiscriminantUnit]
    field_simp [Units.ne_zero P.a]
    ring
  · rfl
  · change P.jData.diagonalUnits (3 : Fin 4) =
      P.jDiagonalUnits (3 : Fin 4)
    apply Units.ext
    rw [OmearaOddQuaternaryModelData.diagonalUnits_three]
    simp [jData, jDiagonalUnits]

theorem kData_diagonalUnits_eq :
    P.kData.diagonalUnits = P.kDiagonalUnits := by
  funext i
  fin_cases i
  · rfl
  · change P.kData.diagonalUnits (1 : Fin 4) =
      P.kDiagonalUnits (1 : Fin 4)
    apply Units.ext
    rw [OmearaOddQuaternaryModelData.diagonalUnits_one]
    simp [kData, kDiagonalUnits, dShift,
      coe_omeara9318ShiftedDiscriminantUnit]
    field_simp [Units.ne_zero P.a]
    ring
  · rfl
  · change P.kData.diagonalUnits (3 : Fin 4) =
      P.kDiagonalUnits (3 : Fin 4)
    apply Units.ext
    rw [OmearaOddQuaternaryModelData.diagonalUnits_three]
    simp [kData, kDiagonalUnits,
      laws.discriminant_eq_one_sub_four_mul_rho]
    field_simp [Units.ne_zero P.b]
    ring

theorem jDiagonalUnitDeterminant_eq_d :
    diagonalUnitDeterminant P.jDiagonalUnits = P.d := by
  apply Units.ext
  simp [diagonalUnitDeterminant, Fin.prod_univ_four,
    jDiagonalUnits, d, coe_omeara9318DiscriminantUnit]

theorem kDiagonalUnitDeterminant_eq_dShift_mul_discriminant :
    diagonalUnitDeterminant P.kDiagonalUnits =
      P.dShift * laws.discriminantUnit := by
  apply Units.ext
  simp [diagonalUnitDeterminant, Fin.prod_univ_four,
    kDiagonalUnits, dShift,
    coe_omeara9318ShiftedDiscriminantUnit]
  field_simp [Units.ne_zero P.a, Units.ne_zero P.b]

theorem modelDeterminants_product_isSquare :
    IsSquare
      (diagonalUnitDeterminant P.jDiagonalUnits *
        diagonalUnitDeterminant P.kDiagonalUnits) := by
  rw [P.jDiagonalUnitDeterminant_eq_d,
    P.kDiagonalUnitDeterminant_eq_dShift_mul_discriminant]
  have h := omeara9318Discriminants_sameSquareClass
    P.alpha P.alpha_maximal P.discriminant_unit
      P.shifted_discriminant_unit
  simpa only [d, dShift, mul_assoc, mul_comm, mul_left_comm] using h

/-! ## Reordered coefficients and the Hasse comparison -/

/-- The order `[a,b,-d/a,-1/b]` exposes the final binary pair whose
simultaneous discriminant scaling changes the Hasse invariant. -/
noncomputable def jReordered : Fin 4 → Kˣ :=
  ![P.a, P.b, -(P.d * P.a⁻¹), -(P.b⁻¹)]

noncomputable def kReordered : Fin 4 → Kˣ :=
  ![P.a, P.b, -(P.dShift * P.a⁻¹),
    -(laws.discriminantUnit * P.b⁻¹)]

private def middleSwap : Equiv.Perm (Fin 4) :=
  Equiv.swap (1 : Fin 4) (2 : Fin 4)

private theorem jReordered_represents_jDiagonalUnits :
    DiagonalRepresents
      (diagonalUnitCoefficients P.jReordered)
      (diagonalUnitCoefficients P.jDiagonalUnits) := by
  have h := diagonalRepresents_reindex
    (diagonalUnitCoefficients P.jDiagonalUnits) middleSwap
  have hc :
      diagonalUnitCoefficients P.jDiagonalUnits ∘ middleSwap =
        diagonalUnitCoefficients P.jReordered := by
    funext i
    fin_cases i <;>
      simp [middleSwap, jReordered, jDiagonalUnits,
        diagonalUnitCoefficients, Equiv.swap_apply_of_ne_of_ne]
  rw [hc] at h
  exact h

private theorem kReordered_represents_kDiagonalUnits :
    DiagonalRepresents
      (diagonalUnitCoefficients P.kReordered)
      (diagonalUnitCoefficients P.kDiagonalUnits) := by
  have h := diagonalRepresents_reindex
    (diagonalUnitCoefficients P.kDiagonalUnits) middleSwap
  have hc :
      diagonalUnitCoefficients P.kDiagonalUnits ∘ middleSwap =
        diagonalUnitCoefficients P.kReordered := by
    funext i
    fin_cases i <;>
      simp [middleSwap, kReordered, kDiagonalUnits,
        diagonalUnitCoefficients, Equiv.swap_apply_of_ne_of_ne]
  rw [hc] at h
  exact h

theorem jDiagonalUnits_hasse_eq_reordered :
    diagonalHasseSymbol K P.jDiagonalUnits =
      diagonalHasseSymbol K P.jReordered := by
  exact (DiagonalIsometryInvariantLaws.hasse_eq
    P.jReordered P.jDiagonalUnits
      P.jReordered_represents_jDiagonalUnits).symm

theorem kDiagonalUnits_hasse_eq_reordered :
    diagonalHasseSymbol K P.kDiagonalUnits =
      diagonalHasseSymbol K P.kReordered := by
  exact (DiagonalIsometryInvariantLaws.hasse_eq
    P.kReordered P.kDiagonalUnits
      P.kReordered_represents_kDiagonalUnits).symm

/-- The second coefficient of the reordered `K` model differs from
`Delta` times the corresponding `J` coefficient by a square. -/
theorem kSecond_mul_discriminant_jSecond_isSquare :
    IsSquare
      (P.kReordered 2 *
        (laws.discriminantUnit * P.jReordered 2)) := by
  have htwist := omeara9318Discriminants_sameSquareClass
    P.alpha P.alpha_maximal P.discriminant_unit
      P.shifted_discriminant_unit
  have hinv : IsSquare (P.a⁻¹ ^ 2) := ⟨P.a⁻¹, pow_two P.a⁻¹⟩
  have h := htwist.mul hinv
  have heq :
      P.kReordered 2 *
          (laws.discriminantUnit * P.jReordered 2) =
        P.dShift * laws.discriminantUnit * P.d * P.a⁻¹ ^ 2 := by
    change
      (-(P.dShift * P.a⁻¹)) *
          (laws.discriminantUnit * (-(P.d * P.a⁻¹))) =
        P.dShift * laws.discriminantUnit * P.d * P.a⁻¹ ^ 2
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val]
    ring
  rw [heq]
  exact h

/-- Coefficient family obtained by multiplying the final binary pair of
`J` by the discriminant unit. -/
noncomputable def kNormalized : Fin 4 → Kˣ :=
  ![P.a, P.b,
    laws.discriminantUnit * P.jReordered 2,
    laws.discriminantUnit * P.jReordered 3]

@[simp]
theorem kNormalized_zero : P.kNormalized 0 = P.a := rfl

@[simp]
theorem kNormalized_one : P.kNormalized 1 = P.b := rfl

@[simp]
theorem kNormalized_two :
    P.kNormalized 2 = laws.discriminantUnit * P.jReordered 2 := rfl

@[simp]
theorem kNormalized_three :
    P.kNormalized 3 = laws.discriminantUnit * P.jReordered 3 := rfl

private theorem exists_eq_mul_sq_of_isSquare_mul
    (x y : Kˣ) (h : IsSquare (x * y)) :
    ∃ u : Kˣ, x = y * u ^ 2 := by
  rcases h with ⟨s, hs⟩
  refine ⟨s * y⁻¹, ?_⟩
  calc
    x = (x * y) * y⁻¹ := by group
    _ = (s * s) * y⁻¹ := by rw [hs]
    _ = y * (s * y⁻¹) ^ 2 := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_pow_eq_pow_val]
      field_simp [Units.ne_zero y]

/-- The actual `K` coefficient family is isometric to the family obtained
by scaling the final pair of `J` by `Delta`; the residual discrepancy in
the second coefficient is precisely the Hensel square proved above. -/
theorem kReordered_represents_kNormalized :
    DiagonalRepresents
      (diagonalUnitCoefficients P.kReordered)
      (diagonalUnitCoefficients P.kNormalized) := by
  let base : Fin 2 → Kˣ := ![P.a, P.b]
  let k2 : Kˣ := P.kReordered 2
  let n2 : Kˣ := laws.discriminantUnit * P.jReordered 2
  let n3 : Kˣ := laws.discriminantUnit * P.jReordered 3
  obtain ⟨u, hu⟩ := exists_eq_mul_sq_of_isSquare_mul k2 n2
    P.kSecond_mul_discriminant_jSecond_isSquare
  have hk3 : P.kReordered 3 = n3 := by
    apply Units.ext
    simp [kReordered, jReordered, n3]
  have hkArray :
      P.kReordered = Fin.snoc (Fin.snoc base k2) n3 := by
    funext i
    fin_cases i
    · simp [kReordered, base]
    · simp [kReordered, base]
    · simp [kReordered, base, k2]
    · change P.kReordered (Fin.last 3) =
        (Fin.snoc (Fin.snoc base k2) n3 : Fin 4 → Kˣ) (Fin.last 3)
      rw [Fin.snoc_last]
      simpa using hk3
  have hnArray :
      P.kNormalized = Fin.snoc (Fin.snoc base n2) n3 := by
    funext i
    fin_cases i <;> simp [kNormalized, base, n2, n3]
  have hswapK : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc (Fin.snoc base k2) n3))
      (diagonalUnitCoefficients (Fin.snoc (Fin.snoc base n3) k2)) := by
    simpa only [diagonalUnitCoefficients_snoc] using
      (diagonalRepresents_swap_last_two
        (diagonalUnitCoefficients base) (k2 : K) (n3 : K))
  let head : Fin 3 → Kˣ := Fin.snoc base n3
  have hscale : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc head k2))
      (diagonalUnitCoefficients (Fin.snoc head n2)) := by
    have h := diagonalRepresents_snoc_mul_square head n2 u
    rw [← hu] at h
    exact h
  have hswapN : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc (Fin.snoc base n2) n3))
      (diagonalUnitCoefficients (Fin.snoc (Fin.snoc base n3) n2)) := by
    simpa only [diagonalUnitCoefficients_snoc] using
      (diagonalRepresents_swap_last_two
        (diagonalUnitCoefficients base) (n2 : K) (n3 : K))
  rw [hkArray, hnArray]
  exact hswapK.trans (hscale.trans hswapN.symm_of_sameRank)

theorem kReordered_hasse_eq_kNormalized :
    diagonalHasseSymbol K P.kReordered =
      diagonalHasseSymbol K P.kNormalized :=
  DiagonalIsometryInvariantLaws.hasse_eq
    P.kReordered P.kNormalized P.kReordered_represents_kNormalized

/-- Hasse-symbol effect of the simultaneous `Delta` scaling. -/
theorem kNormalized_hasse_eq_discriminant_factor :
    diagonalHasseSymbol K P.kNormalized =
      hilbertSymbol K laws.discriminantUnit
          (-(P.jReordered 2 * P.jReordered 3)) *
        diagonalHasseSymbol K P.jReordered := by
  simpa [kNormalized, jReordered] using
    (DiagonalHassePairScaling.hasse_fin_four_scale_last_pair
      P.jReordered laws.discriminantUnit)

/-- The signed determinant of the final binary pair has odd valuation. -/
theorem jSignedTail_order :
    ordUnit K (-(P.jReordered 2 * P.jReordered 3)) =
      -(ordUnit K P.a + ordUnit K P.b) := by
  have hd : ordUnit K P.d = 0 := by
    apply (isValuationUnit_iff_ordUnit_eq_zero K P.d).1
    simpa [d, coe_omeara9318DiscriminantUnit] using
      P.discriminant_unit
  rw [ordUnit_neg, ordUnit_mul]
  change
    ordUnit K (-(P.d * P.a⁻¹)) + ordUnit K (-(P.b⁻¹)) = _
  rw [ordUnit_neg, ordUnit_mul, hd, ordUnit_inv,
    ordUnit_neg, ordUnit_inv]
  omega

theorem jSignedTail_odd :
    Odd (ordUnit K (-(P.jReordered 2 * P.jReordered 3))) := by
  rw [P.jSignedTail_order]
  rcases P.odd_orders with ⟨t, ht⟩
  refine ⟨-t - 1, ?_⟩
  omega

theorem discriminant_hilbert_jSignedTail_eq_neg_one :
    hilbertSymbol K laws.discriminantUnit
      (-(P.jReordered 2 * P.jReordered 3)) = -1 := by
  have hne := hilbertSymbol_discriminant_ne_one_of_odd_order
    (-(P.jReordered 2 * P.jReordered 3)) P.jSignedTail_odd
  exact (Int.units_eq_one_or
    (hilbertSymbol K laws.discriminantUnit
      (-(P.jReordered 2 * P.jReordered 3)))).resolve_left hne

/-- O'Meara's two odd quaternary models have opposite Hasse invariants. -/
theorem k_hasse_eq_neg_j_hasse :
    diagonalHasseSymbol K P.kData.diagonalUnits =
      -diagonalHasseSymbol K P.jData.diagonalUnits := by
  rw [P.kData_diagonalUnits_eq, P.jData_diagonalUnits_eq]
  calc
    diagonalHasseSymbol K P.kDiagonalUnits =
        diagonalHasseSymbol K P.kReordered :=
      P.kDiagonalUnits_hasse_eq_reordered
    _ = diagonalHasseSymbol K P.kNormalized :=
      P.kReordered_hasse_eq_kNormalized
    _ = hilbertSymbol K laws.discriminantUnit
          (-(P.jReordered 2 * P.jReordered 3)) *
        diagonalHasseSymbol K P.jReordered :=
      P.kNormalized_hasse_eq_discriminant_factor
    _ = -diagonalHasseSymbol K P.jReordered := by
      rw [P.discriminant_hilbert_jSignedTail_eq_neg_one]
      simp
    _ = -diagonalHasseSymbol K P.jDiagonalUnits := by
      rw [P.jDiagonalUnits_hasse_eq_reordered]

end Omeara9318RankFourModelParameters

end Lattice

end Bong
