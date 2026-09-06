/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicSectionSeven

/-!
# He (2024), Lemma 7.11

This file formalizes the odd-rank deletion witnesses used in the minimality
part of Theorem 1.3.  The auxiliary first-column lattice is the literal
`bar C_1` introduced immediately before Lemma 7.11, rather than the ordinary
odd `C_1` row.  Ambient exactness is first proved from He--Hu Proposition
3.5(iii), and Lemma 3.15(ii) then upgrades every permitted ambient
representation to an integral representation.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG AlternatingEndpointTower

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-! ## The auxiliary lattice `bar C_1` -/

/-- The ternary tail `⟨c,-c*omega,c*omega⟩` in the definition immediately
before He, Lemma 7.11. -/
def heClassicOddC1BarTail (c omega : Kˣ) : Fin 3 → Kˣ :=
  ![c, -(c * omega), c * omega]

/-- The literal auxiliary lattice
`bar C_1^(2*pairs+3)(c) = H_0^pairs perp ⟨c,-c*omega,c*omega⟩`. -/
noncomputable def heClassicOddC1Bar (pairs : Nat) (c omega : Kˣ) :
    Fin (2 * pairs + 3) → Kˣ :=
  Fin.append (heClassicScaledHyperbolicTower (K := K) 0 pairs)
    (heClassicOddC1BarTail c omega)

@[simp]
theorem heClassicOddC1Bar_head (pairs : Nat) (c omega : Kˣ)
    (i : Fin (2 * pairs)) :
    heClassicOddC1Bar (K := K) pairs c omega (Fin.castAdd 3 i) =
      heClassicScaledHyperbolicTower (K := K) 0 pairs i := by
  rw [heClassicOddC1Bar, Fin.append_left]

@[simp]
theorem heClassicOddC1Bar_tail (pairs : Nat) (c omega : Kˣ)
    (i : Fin 3) :
    heClassicOddC1Bar (K := K) pairs c omega
        (Fin.natAdd (2 * pairs) i) =
      heClassicOddC1BarTail c omega i := by
  rw [heClassicOddC1Bar, Fin.append_right]

/-- Every displayed order of `bar C_1` is zero for unit parameters. -/
theorem heClassicOddC1Bar_order_zero (pairs : Nat) (c omega : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0)
    (i : Fin (2 * pairs + 3)) :
    ordUnit K (heClassicOddC1Bar (K := K) pairs c omega i) = 0 := by
  by_cases hhead : i.val < 2 * pairs
  · let j : Fin (2 * pairs) := ⟨i.val, hhead⟩
    have hi : i = Fin.castAdd 3 j := Fin.ext rfl
    rw [hi, heClassicOddC1Bar_head,
      heClassicScaledHyperbolicTower_zero_order]
  · have htail : i.val = 2 * pairs ∨
        i.val = 2 * pairs + 1 ∨ i.val = 2 * pairs + 2 := by
      omega
    rcases htail with hzero | hone | htwo
    · have hi : i = Fin.natAdd (2 * pairs) (0 : Fin 3) := by
        apply Fin.ext
        simpa using hzero
      rw [hi, heClassicOddC1Bar_tail]
      simp [heClassicOddC1BarTail, hc]
    · have hi : i = Fin.natAdd (2 * pairs) (1 : Fin 3) := by
        apply Fin.ext
        simpa using hone
      rw [hi, heClassicOddC1Bar_tail]
      simp [heClassicOddC1BarTail, ordUnit_neg, ordUnit_mul, hc, homega]
    · have hi : i = Fin.natAdd (2 * pairs) (2 : Fin 3) := by
        apply Fin.ext
        simpa using htwo
      rw [hi, heClassicOddC1Bar_tail]
      simp [heClassicOddC1BarTail, ordUnit_mul, hc, homega]

/-- The zero order profile makes every adjacent quotient of `bar C_1`
binary-admissible. -/
theorem heClassicOddC1Bar_adjacentAdmissible
    (pairs : Nat) (c omega : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0) :
    BONG.CoefficientAdjacentAdmissible
      (heClassicOddC1Bar (K := K) pairs c omega) := by
  intro i hi
  apply BONG.isBinaryParameterAdmissible_of_ordUnit_nonneg
  rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
    heClassicOddC1Bar_order_zero pairs c omega hc homega,
    heClassicOddC1Bar_order_zero pairs c omega hc homega]
  omega

/-- The two parity chains of `bar C_1` are constant. -/
theorem heClassicOddC1Bar_weakTwoStep
    (pairs : Nat) (c omega : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0) :
    BONG.CoefficientWeakTwoStep (K := K)
      (heClassicOddC1Bar (K := K) pairs c omega) := by
  intro i hi
  rw [heClassicOddC1Bar_order_zero pairs c omega hc homega,
    heClassicOddC1Bar_order_zero pairs c omega hc homega]

/-- The exact good BONG carried by the displayed auxiliary row. -/
noncomputable def heClassicOddC1BarGoodBONG
    (pairs : Nat) (c omega : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0) :=
  heHuExactGoodBONG (heClassicOddC1Bar (K := K) pairs c omega)
    (heClassicOddC1Bar_adjacentAdmissible pairs c omega hc homega)
    (heClassicOddC1Bar_weakTwoStep pairs c omega hc homega)

/-- Bundle the exact good-BONG realization of `bar C_1`. -/
noncomputable def heClassicOddC1BarModel
    (pairs : Nat) (c omega : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heHuExactModel (heClassicOddC1Bar (K := K) pairs c omega)
    (heClassicOddC1Bar_adjacentAdmissible pairs c omega hc homega)
    (heClassicOddC1Bar_weakTwoStep pairs c omega hc homega)

@[simp]
theorem heClassicOddC1BarModel_rank
    (pairs : Nat) (c omega : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0) :
    (heClassicOddC1BarModel (K := K) pairs c omega hc homega).rank =
      2 * pairs + 3 :=
  heHuExactModel_rank _ _ _

/-- The auxiliary row is classic integral. -/
theorem heClassicOddC1Bar_isClassicIntegral
    (pairs : Nat) (c omega : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0) :
    Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace
        (heClassicOddC1Bar (K := K) pairs c omega))
      (heHuExactRealization
        (heClassicOddC1Bar (K := K) pairs c omega)
        (heClassicOddC1Bar_adjacentAdmissible pairs c omega hc homega)
        (heClassicOddC1Bar_weakTwoStep pairs c omega hc homega)).lattice := by
  let b := heClassicOddC1BarGoodBONG (K := K) pairs c omega hc homega
  rw [b.isClassicIntegral_iff_firstOrders]
  simp only [b, heClassicOddC1BarGoodBONG, heHuExactGoodBONG_order]
  rw [heClassicOddC1Bar_order_zero pairs c omega hc homega,
    heClassicOddC1Bar_order_zero pairs c omega hc homega]
  omega

theorem heClassicOddC1BarModel_isClassicIntegral
    (pairs : Nat) (c omega : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0) :
    (heClassicOddC1BarModel (K := K) pairs c omega hc homega).IsClassicIntegral :=
  heClassicOddC1Bar_isClassicIntegral pairs c omega hc homega

/-- The first adjacent product in the auxiliary ternary tail is `omega`
times a square. -/
theorem heClassicOddC1Bar_anchorAdjacentDefect
    (pairs : Nat) (c omega : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0) :
    let b := heClassicOddC1BarGoodBONG (K := K) pairs c omega hc homega
    b.adjacentDefect (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 2)) =
      BONG.GoodBONG.defectOrder (K := K) omega := by
  dsimp only
  unfold heClassicOddC1BarGoodBONG
  rw [BONG.GoodBONG.heHuExactGoodBONG_adjacentDefect]
  have hleft : heClassicOddC1Bar (K := K) pairs c omega
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 3)) = c := by
    rw [show (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 3)) =
      Fin.natAdd (2 * pairs) (0 : Fin 3) by exact Fin.ext rfl,
      heClassicOddC1Bar_tail]
    rfl
  have hright : heClassicOddC1Bar (K := K) pairs c omega
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 3)) =
        -(c * omega) := by
    rw [show (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 3)) =
      Fin.natAdd (2 * pairs) (1 : Fin 3) by exact Fin.ext rfl,
      heClassicOddC1Bar_tail]
    rfl
  have hcast : (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 2)).castSucc =
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 3)) := Fin.ext rfl
  have hsucc : (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 2)).succ =
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 3)) := Fin.ext rfl
  rw [hcast, hsucc, hleft, hright]
  have hfactor : -(c * (-(c * omega))) = omega * c ^ 2 := by
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hfactor, BONG.GoodBONG.defectOrder_mul_square]

/-- Proposition 2.3(vi) gives the alpha-one profile needed by Lemma
3.15(ii). -/
theorem heClassicOddC1Bar_alpha_eq_one
    (pairs : Nat) (c omega : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0)
    (homegaDefect : BONG.GoodBONG.defectOrder (K := K) omega =
      ((1 : ℚ) : WithTop ℚ)) :
    let b := heClassicOddC1BarGoodBONG (K := K) pairs c omega hc homega
    ∀ i : Fin (2 * pairs + 2), b.alphaValue i = 1 := by
  dsimp only
  let b := heClassicOddC1BarGoodBONG (K := K) pairs c omega hc homega
  apply b.he2022ClassicLemma29iii_alpha_of_zero_orders
    (heClassicOddC1Bar_isClassicIntegral pairs c omega hc homega)
  · intro i
    simp only [b, heClassicOddC1BarGoodBONG, heHuExactGoodBONG_order]
    exact heClassicOddC1Bar_order_zero pairs c omega hc homega i
  · refine ⟨⟨2 * pairs, by omega⟩, ?_⟩
    rw [heClassicOddC1Bar_anchorAdjacentDefect pairs c omega hc homega,
      homegaDefect]

/-! ## Ambient exactness in codimension two -/

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
theorem heClassicOddC1BarTail_isotropic (c omega : Kˣ) :
    DiagonalIsotropic
      (diagonalUnitCoefficients (heClassicOddC1BarTail (K := K) c omega)) := by
  let x : Fin 3 → K := ![0, 1, 1]
  refine ⟨x, ?_, ?_⟩
  · intro hx
    have hzero := congrFun hx (1 : Fin 3)
    norm_num [x] at hzero
  · simp [heClassicOddC1BarTail, diagonalUnitCoefficients,
      diagonalQuadratic, Fin.sum_univ_three, x]

/-- The auxiliary isotropic tail and the ordinary even-order `C_2` tail
are the two classes with their common determinant. -/
theorem heClassicOddC1Bar_C2EvenTail_pairProperties
    [HilbertSymbolLaws K] (c omega omegaSharp : Kˣ)
    (hnegative : hilbertSymbol K omegaSharp omega = -1) :
    HeHuSpacePairProperties
      (heClassicOddC1BarTail (K := K) c omega)
      (heClassicOddC2EvenTail (K := K) c omega omegaSharp) := by
  apply HeHuSpacePairProperties.of_det_not
  · refine ⟨c * c * c * omegaSharp * omega * omega, ?_⟩
    simp [heClassicOddC1BarTail, heClassicOddC2EvenTail,
      diagonalUnitDeterminant, Fin.prod_univ_three]
    ac_rfl
  · intro hrep
    have hbarAnisotropic : DiagonalAnisotropic
        (diagonalUnitCoefficients
          (heClassicOddC1BarTail (K := K) c omega)) :=
      hrep.symm_of_sameRank.anisotropic_of
        (heClassicOddC2EvenTail_anisotropic
          c omega omegaSharp hnegative)
    exact ((not_diagonalIsotropic_iff_diagonalAnisotropic
      (diagonalUnitCoefficients
        (heClassicOddC1BarTail (K := K) c omega))).2
          hbarAnisotropic) (heClassicOddC1BarTail_isotropic c omega)

/-- The full auxiliary first row and ordinary second row form the two
ambient classes in their determinant class. -/
theorem heClassicOddC1Bar_C2Even_pairProperties
    [HilbertSymbolLaws K] (pairs : Nat) (c omega omegaSharp : Kˣ)
    (hnegative : hilbertSymbol K omegaSharp omega = -1) :
    HeHuSpacePairProperties
      (heClassicOddC1Bar (K := K) pairs c omega)
      (heClassicOddC2Even (K := K) pairs c omega omegaSharp) := by
  have P := (heClassicOddC1Bar_C2EvenTail_pairProperties
    (K := K) c omega omegaSharp hnegative).append
      (standardHyperbolicEndpointTower (K := K) pairs)
  simpa only [heClassicOddC1Bar, heClassicOddC2Even,
    heClassicOddC2EvenTail, heClassicScaledHyperbolicTower_zero] using P

/-- The standard isotropic He--Hu ternary and the auxiliary ternary are
isometric. -/
theorem heHuOddFirstTail_represents_heClassicOddC1BarTail
    (c omega : Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heHuOddFirstTail (K := K) c))
      (diagonalUnitCoefficients
        (heClassicOddC1BarTail (K := K) c omega)) := by
  have hbinary : DiagonalRepresents
      (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
      (diagonalUnitCoefficients ![-(c * omega), c * omega]) := by
    apply QuadraticSpace.finiteDiagonal_fin_two_diagonalRepresents_of_signedRatioSquares
    · refine ⟨1, ?_⟩
      simp [heHuHyperbolicPair]
    · refine ⟨1, ?_⟩
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
        Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, mul_one]
      rw [neg_div, neg_neg]
      exact div_self' _
  have hline : DiagonalRepresents
      (diagonalUnitCoefficients (![c] : Fin 1 → Kˣ))
      (diagonalUnitCoefficients (![c] : Fin 1 → Kˣ)) :=
    diagonalRepresents_refl _
  have hcomm : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append (heHuHyperbolicPair (K := K)) (![c] : Fin 1 → Kˣ)))
      (diagonalUnitCoefficients
        (Fin.append (![c] : Fin 1 → Kˣ) (heHuHyperbolicPair (K := K)))) := by
    rw [diagonalUnitCoefficients_append, diagonalUnitCoefficients_append]
    exact diagonalRepresents_append_comm _ _
  have happ := DiagonalRepresents.appendBoth hline hbinary
  have htail : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append (![c] : Fin 1 → Kˣ) (heHuHyperbolicPair (K := K))))
      (diagonalUnitCoefficients
        (heClassicOddC1BarTail (K := K) c omega)) := by
    convert happ using 1 <;> funext i <;> fin_cases i <;> rfl
  have h := hcomm.trans htail
  convert h using 1
  funext i
  fin_cases i <;> rfl

/-- Adding a hyperbolic plane to the small `C_1` gives the large auxiliary
first space. -/
theorem heClassicOddC1_to_bar_hyperbolicLift
    (pairs : Nat) (c omega : Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append (heClassicOddC1 (K := K) pairs c)
          (heHuHyperbolicPair (K := K))))
      (diagonalUnitCoefficients
        (heClassicOddC1Bar (K := K) (pairs + 1) c omega)) := by
  have hstandard := heHuOddFirst_hyperbolicLift (K := K) pairs c
  have htail := heHuOddFirstTail_represents_heClassicOddC1BarTail
    (K := K) c omega
  have hhead := diagonalRepresents_refl
    (diagonalUnitCoefficients
      (standardHyperbolicEndpointTower (K := K) (pairs + 1)))
  have hlarge := DiagonalRepresents.appendBoth hhead htail
  have hlarge' : DiagonalRepresents
      (diagonalUnitCoefficients (heHuOddFirst (pairs + 1) c))
      (diagonalUnitCoefficients
        (heClassicOddC1Bar (K := K) (pairs + 1) c omega)) := by
    simpa only [heHuOddFirst, heClassicOddC1Bar,
      heClassicScaledHyperbolicTower_zero,
      diagonalUnitCoefficients_append] using hlarge
  rw [heClassicOddC1_eq_heHuOddFirst]
  exact hstandard.trans hlarge'

/-- The ordinary even-order second column also gains one hyperbolic plane. -/
theorem heClassicOddC2Even_hyperbolicLift
    (pairs : Nat) (c omega omegaSharp : Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append
          (heClassicOddC2Even (K := K) pairs c omega omegaSharp)
          (heHuHyperbolicPair (K := K))))
      (diagonalUnitCoefficients
        (heClassicOddC2Even (K := K) (pairs + 1) c omega omegaSharp)) := by
  simpa only [heClassicOddC2Even, heClassicOddC2EvenTail,
    heClassicScaledHyperbolicTower_zero] using
      (heHuTowerModel_succ_hyperbolicLift
        (K := K) pairs (heClassicOddC2EvenTail (K := K) c omega omegaSharp))

/-- Lemma 7.11(i), ambient exactness for the auxiliary first source. -/
theorem he2022ClassicLemma711i_barC1_missesExactly_C2
    [HilbertSymbolLaws K] (pairs : Nat) (c omega omegaSharp : Kˣ)
    (hnegative : hilbertSymbol K omegaSharp omega = -1) :
    HeHuMissesExactly
      (heClassicOddC2Even (K := K) pairs c omega omegaSharp)
      (heClassicOddC1Bar (K := K) (pairs + 1) c omega) := by
  exact (heHuUniqueExcludingSecond_of_hyperbolicPairs
    (heClassicOddC1 (K := K) pairs c)
    (heClassicOddC2Even (K := K) pairs c omega omegaSharp)
    (heClassicOddC1Bar (K := K) (pairs + 1) c omega)
    (heClassicOddC2Even (K := K) (pairs + 1) c omega omegaSharp)
    (heClassicOddC_evenOrder_pairProperties
      (K := K) pairs c omega omegaSharp hnegative)
    (heClassicOddC1Bar_C2Even_pairProperties
      (K := K) (pairs + 1) c omega omegaSharp hnegative)
    (heClassicOddC1_to_bar_hyperbolicLift (K := K) pairs c omega)
    (heClassicOddC2Even_hyperbolicLift
      (K := K) pairs c omega omegaSharp)).exactness

/-- Lemma 7.11(i), ambient exactness for the ordinary second source. -/
theorem he2022ClassicLemma711i_C2_missesExactly_C1
    [HilbertSymbolLaws K] (pairs : Nat) (c omega omegaSharp : Kˣ)
    (hnegative : hilbertSymbol K omegaSharp omega = -1) :
    HeHuMissesExactly
      (heClassicOddC1 (K := K) pairs c)
      (heClassicOddC2Even (K := K) (pairs + 1) c omega omegaSharp) := by
  exact (heHuUniqueExcludingFirst_of_hyperbolicPairs
    (heClassicOddC1 (K := K) pairs c)
    (heClassicOddC2Even (K := K) pairs c omega omegaSharp)
    (heClassicOddC1Bar (K := K) (pairs + 1) c omega)
    (heClassicOddC2Even (K := K) (pairs + 1) c omega omegaSharp)
    (heClassicOddC_evenOrder_pairProperties
      (K := K) pairs c omega omegaSharp hnegative)
    (heClassicOddC1Bar_C2Even_pairProperties
      (K := K) (pairs + 1) c omega omegaSharp hnegative)
    (heClassicOddC1_to_bar_hyperbolicLift (K := K) pairs c omega)
     (heClassicOddC2Even_hyperbolicLift
       (K := K) pairs c omega omegaSharp)).exactness

/-- Lemma 7.11(ii), ambient exactness for the odd-order second source. -/
theorem he2022ClassicLemma711ii_C2Odd_missesExactly_C1
    (pairs : Nat) (c : Kˣ) (hodd : Odd (ordUnit K c)) :
    HeHuMissesExactly
      (heClassicOddC1 (K := K) pairs c)
      (heClassicOddC2Odd (K := K) (pairs + 1) c) := by
  simpa only [heClassicOddC1_eq_heHuOddFirst,
    heClassicOddC2Odd_eq_heHuOddSecond_of_odd _ c hodd,
    heHuFinFamilyCast_self] using
      (heHu2022Proposition35iiiOddFirst (K := K) pairs c).exactness

/-- Lemma 7.11(ii), ambient exactness for the odd-order first source. -/
theorem he2022ClassicLemma711ii_C1_missesExactly_C2Odd
    (pairs : Nat) (c : Kˣ) (hodd : Odd (ordUnit K c)) :
    HeHuMissesExactly
      (heClassicOddC2Odd (K := K) pairs c)
      (heClassicOddC1 (K := K) (pairs + 1) c) := by
  simpa only [heClassicOddC1_eq_heHuOddFirst,
    heClassicOddC2Odd_eq_heHuOddSecond_of_odd _ c hodd,
    heHuFinFamilyCast_self] using
      (heHu2022Proposition35iiiOddSecond (K := K) pairs c).exactness

/-- Any admissible record for the two printed units carries the Hilbert-symbol
relation used in Lemma 7.11(i). -/
theorem HeClassicOmegaData.hilbert_omegaSharp_omega
    [HilbertSymbolLaws K] (omegaData : HeClassicOmegaData (K := K)) :
    hilbertSymbol K omegaData.omegaSharp omegaData.omega = -1 := by
  rw [omegaData.omega_eq, omegaData.omegaSharp_eq]
  exact BONG.GoodBONG.heClassicOmegaSharp_hilbert_neg (K := K)

/-- Ambient nonrepresentation supplied by Proposition 3.5(iii) already
precludes an integral lattice representation, independently of the lattices
chosen on the two diagonal spaces. -/
theorem HeHuMissesExactly.not_latticeRepresents
    {n : Nat} {excluded : Fin n → Kˣ} {source : Fin (n + 2) → Kˣ}
    (hexact : HeHuMissesExactly excluded source)
    {LS : Lattice K (Fin (n + 2) → K)}
    {LE : Lattice K (Fin n → K)} :
    ¬ Lattice.Represents
      (BONG.coefficientDiagonalSpace source)
      (BONG.coefficientDiagonalSpace excluded) LS LE := by
  intro hrep
  apply hexact.misses
  exact (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
    excluded source).mp hrep.ambient

namespace BONG.GoodBONG

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}
  {W : Type w} [AddCommGroup W] [Module K W]
  {r : QuadraticSpace K W} {M : Lattice K W}

/-- Common Lemma 3.15(ii) upgrade used by all four odd deletion witnesses. -/
theorem he2022ClassicLemma711_represents_other
    (pairs : Nat) (a : GoodBONG q L (2 * pairs + 5))
    (b : GoodBONG r M (2 * pairs + 3))
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hRn : a.order ⟨2 * pairs + 2, by omega⟩ = 0)
    (hRnOne : a.order ⟨2 * pairs + 3, by omega⟩ = 0)
    (hterminal :
      (a.order ⟨2 * pairs + 4, by omega⟩ = 0 ∧
        a.alphaValue ⟨2 * pairs + 2, by omega⟩ = 1) ∨
      a.order ⟨2 * pairs + 4, by omega⟩ = 1)
    {excluded : Fin (2 * pairs + 3) → Kˣ}
    (hexact : HeHuMissesExactly excluded a.valueUnit)
    (hother : ¬ DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients excluded)) :
    Lattice.Represents q r L M := by
  have hdiag := hexact.represents_other b.valueUnit hother
  have hSource : q.Represents
      (BONG.coefficientDiagonalSpace a.valueUnit) :=
    ⟨a.toBONG.exactDiagonalizationIsometry.symm.toRepresentation⟩
  have hDiagonal :
      (BONG.coefficientDiagonalSpace a.valueUnit).Represents
        (BONG.coefficientDiagonalSpace b.valueUnit) :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      b.valueUnit a.valueUnit).2 hdiag
  have hTarget : (BONG.coefficientDiagonalSpace b.valueUnit).Represents r :=
    ⟨b.toBONG.exactDiagonalizationIsometry.toRepresentation⟩
  have hambient : q.Represents r := (hSource.trans hDiagonal).trans hTarget
  exact he2022ClassicLemma315ii pairs a b hAClassic hBClassic
    hRn hRnOne hterminal hambient

end BONG.GoodBONG

/-- The auxiliary large first row integrally represents every classic target
outside the excluded small even-order second ambient class. -/
theorem he2022ClassicLemma711i_barC1_represents_other
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (pairs : Nat) (c omega omegaSharp : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0)
    (homegaDefect : defectOrder (K := K) omega = (1 : WithTop ℚ))
    (hnegative : hilbertSymbol K omegaSharp omega = -1)
    (b : BONG.GoodBONG q L (2 * pairs + 3))
    (hBClassic : Lattice.IsClassicIntegral q L)
    (hother : ¬ DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients
        (heClassicOddC2Even (K := K) pairs c omega omegaSharp))) :
    Lattice.Represents
      (BONG.coefficientDiagonalSpace
        (heClassicOddC1Bar (K := K) (pairs + 1) c omega)) q
      (heHuExactRealization
        (heClassicOddC1Bar (K := K) (pairs + 1) c omega)
        (heClassicOddC1Bar_adjacentAdmissible (pairs + 1) c omega hc homega)
        (heClassicOddC1Bar_weakTwoStep (pairs + 1) c omega hc homega)).lattice
      L := by
  let a := heClassicOddC1BarGoodBONG (K := K) (pairs + 1) c omega hc homega
  apply BONG.GoodBONG.he2022ClassicLemma711_represents_other
    (excluded := heClassicOddC2Even (K := K) pairs c omega omegaSharp)
    pairs a b
  · exact heClassicOddC1Bar_isClassicIntegral (pairs + 1) c omega hc homega
  · exact hBClassic
  · simp only [a, heClassicOddC1BarGoodBONG, heHuExactGoodBONG_order]
    exact heClassicOddC1Bar_order_zero (pairs + 1) c omega hc homega _
  · simp only [a, heClassicOddC1BarGoodBONG, heHuExactGoodBONG_order]
    exact heClassicOddC1Bar_order_zero (pairs + 1) c omega hc homega _
  · left
    constructor
    · simp only [a, heClassicOddC1BarGoodBONG, heHuExactGoodBONG_order]
      exact heClassicOddC1Bar_order_zero (pairs + 1) c omega hc homega _
    · exact heClassicOddC1Bar_alpha_eq_one (pairs + 1) c omega hc homega
        homegaDefect _
  · have haValues : a.valueUnit =
        heClassicOddC1Bar (K := K) (pairs + 1) c omega := by
      funext i
      simp only [a, heClassicOddC1BarGoodBONG, heHuExactGoodBONG_valueUnit]
    rw [haValues]
    exact he2022ClassicLemma711i_barC1_missesExactly_C2
      (K := K) pairs c omega omegaSharp hnegative
  · exact hother

/-- The large even-order second row integrally represents every classic
target outside the excluded small first ambient class. -/
theorem he2022ClassicLemma711i_C2_represents_other
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (pairs : Nat) (c omega omegaSharp : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0)
    (homegaSharp : ordUnit K omegaSharp = 0)
    (homegaDefect : defectOrder (K := K) omega = (1 : WithTop ℚ))
    (hnegative : hilbertSymbol K omegaSharp omega = -1)
    (b : BONG.GoodBONG q L (2 * pairs + 3))
    (hBClassic : Lattice.IsClassicIntegral q L)
    (hother : ¬ DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heClassicOddC1 (K := K) pairs c))) :
    Lattice.Represents
      (BONG.coefficientDiagonalSpace
        (heClassicOddC2Even (K := K) (pairs + 1) c omega omegaSharp)) q
      (heHuExactRealization
        (heClassicOddC2Even (K := K) (pairs + 1) c omega omegaSharp)
        (heClassicOddC2Even_adjacentAdmissible (pairs + 1) c omega omegaSharp
          hc homega homegaSharp)
        (heClassicOddC2Even_weakTwoStep (pairs + 1) c omega omegaSharp
          hc homega homegaSharp)).lattice L := by
  let a := heClassicOddC2EvenGoodBONG (K := K) (pairs + 1)
    c omega omegaSharp hc homega homegaSharp
  apply BONG.GoodBONG.he2022ClassicLemma711_represents_other
    (excluded := heClassicOddC1 (K := K) pairs c) pairs a b
  · exact heClassicOddC2Even_isClassicIntegral (K := K) (pairs + 1)
      c omega omegaSharp hc homega homegaSharp
  · exact hBClassic
  · simp only [a, heClassicOddC2EvenGoodBONG, heHuExactGoodBONG_order]
    exact heClassicOddC2Even_order_zero (pairs + 1) c omega omegaSharp
      hc homega homegaSharp _
  · simp only [a, heClassicOddC2EvenGoodBONG, heHuExactGoodBONG_order]
    exact heClassicOddC2Even_order_zero (pairs + 1) c omega omegaSharp
      hc homega homegaSharp _
  · left
    constructor
    · simp only [a, heClassicOddC2EvenGoodBONG, heHuExactGoodBONG_order]
      exact heClassicOddC2Even_order_zero (pairs + 1) c omega omegaSharp
        hc homega homegaSharp _
    · exact heClassicOddC2Even_alpha_eq_one (pairs + 1) c omega omegaSharp
        hc homega homegaSharp homegaDefect _
  · have haValues : a.valueUnit =
        heClassicOddC2Even (K := K) (pairs + 1) c omega omegaSharp := by
      funext i
      simp only [a, heClassicOddC2EvenGoodBONG, heHuExactGoodBONG_valueUnit]
    rw [haValues]
    exact he2022ClassicLemma711i_C2_missesExactly_C1
      (K := K) pairs c omega omegaSharp hnegative
  · exact hother

/-- The large odd-order second row integrally represents every classic target
outside the excluded small first ambient class. -/
theorem he2022ClassicLemma711ii_C2Odd_represents_other
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (pairs : Nat) (c : Kˣ) (hcOrder : ordUnit K c = 1)
    (b : BONG.GoodBONG q L (2 * pairs + 3))
    (hBClassic : Lattice.IsClassicIntegral q L)
    (hother : ¬ DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heClassicOddC1 (K := K) pairs c))) :
    Lattice.Represents
      (BONG.coefficientDiagonalSpace
        (heClassicOddC2Odd (K := K) (pairs + 1) c)) q
      (heHuExactRealization
        (heClassicOddC2Odd (K := K) (pairs + 1) c)
        (heClassicOddC2Odd_adjacentAdmissible (pairs + 1) c (by omega))
        (heClassicOddC2Odd_weakTwoStep (pairs + 1) c (by omega))).lattice L := by
  have hodd : Odd (ordUnit K c) := by rw [hcOrder]; exact odd_one
  let a := heClassicOddC2OddGoodBONG (K := K) (pairs + 1) c (by omega)
  apply BONG.GoodBONG.he2022ClassicLemma711_represents_other
    (excluded := heClassicOddC1 (K := K) pairs c) pairs a b
  · exact heClassicOddC2Odd_isClassicIntegral (K := K) (pairs + 1) c
      (by omega)
  · exact hBClassic
  · simp only [a, heClassicOddC2OddGoodBONG, heHuExactGoodBONG_order]
    rw [heClassicOddC2Odd_order]
    rw [if_neg (by norm_num [Nat.mul_add])]
  · simp only [a, heClassicOddC2OddGoodBONG, heHuExactGoodBONG_order]
    rw [heClassicOddC2Odd_order]
    rw [if_neg (by norm_num [Nat.mul_add])]
  · right
    simp only [a, heClassicOddC2OddGoodBONG, heHuExactGoodBONG_order]
    rw [heClassicOddC2Odd_order]
    rw [if_pos (by norm_num [Nat.mul_add]), hcOrder]
  · have haValues : a.valueUnit =
        heClassicOddC2Odd (K := K) (pairs + 1) c := by
      funext i
      simp only [a, heClassicOddC2OddGoodBONG, heHuExactGoodBONG_valueUnit]
    rw [haValues]
    exact he2022ClassicLemma711ii_C2Odd_missesExactly_C1
      (K := K) pairs c hodd
  · exact hother

/-- The large odd-order first row integrally represents every classic target
outside the excluded small second ambient class. -/
theorem he2022ClassicLemma711ii_C1_represents_other
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (pairs : Nat) (c : Kˣ) (hcOrder : ordUnit K c = 1)
    (b : BONG.GoodBONG q L (2 * pairs + 3))
    (hBClassic : Lattice.IsClassicIntegral q L)
    (hother : ¬ DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heClassicOddC2Odd (K := K) pairs c))) :
    Lattice.Represents
      (BONG.coefficientDiagonalSpace
        (heClassicOddC1 (K := K) (pairs + 1) c)) q
      (heHuExactRealization
        (heClassicOddC1 (K := K) (pairs + 1) c)
        (heClassicOddC1_adjacentAdmissible (pairs + 1) c (by omega))
        (heClassicOddC1_weakTwoStep (pairs + 1) c (by omega))).lattice L := by
  have hodd : Odd (ordUnit K c) := by rw [hcOrder]; exact odd_one
  let a := heClassicOddC1GoodBONG (K := K) (pairs + 1) c (by omega)
  apply BONG.GoodBONG.he2022ClassicLemma711_represents_other
    (excluded := heClassicOddC2Odd (K := K) pairs c) pairs a b
  · exact heClassicOddC1_isClassicIntegral (K := K) (pairs + 1) c (by omega)
  · exact hBClassic
  · simp only [a, heClassicOddC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicOddC1_order]
    rw [if_neg (by norm_num [Nat.mul_add])]
  · simp only [a, heClassicOddC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicOddC1_order]
    rw [if_neg (by norm_num [Nat.mul_add])]
  · right
    simp only [a, heClassicOddC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicOddC1_order]
    rw [if_pos (by norm_num [Nat.mul_add]), hcOrder]
  · have haValues : a.valueUnit =
        heClassicOddC1 (K := K) (pairs + 1) c := by
      funext i
      simp only [a, heClassicOddC1GoodBONG, heHuExactGoodBONG_valueUnit]
    rw [haValues]
    exact he2022ClassicLemma711ii_C1_missesExactly_C2Odd
      (K := K) pairs c hodd
  · exact hother

/-! ## Uniform access to the published odd table -/

/-- Inverse layout map from the parity/column classic table to the two-column
He--Hu table. -/
def heHuOddIndexOfClassic {I : Type u} :
    HeClassicPublishedOddTestingIndex I → HeHuPublishedOddTestingIndex I
  | (p, false) => .inl p
  | (p, true) => .inr p

@[simp]
theorem classicOddIndexOfHeHu_heHuOddIndexOfClassic {I : Type u}
    (i : HeClassicPublishedOddTestingIndex I) :
    Lattice.QuadraticLatticeModel.classicOddIndexOfHeHu
      (heHuOddIndexOfClassic i) = i := by
  rcases i with ⟨p, column⟩
  cases column <;> rfl

@[simp]
theorem heHuOddIndexOfClassic_classicOddIndexOfHeHu {I : Type u}
    (i : HeHuPublishedOddTestingIndex I) :
    heHuOddIndexOfClassic
      (Lattice.QuadraticLatticeModel.classicOddIndexOfHeHu i) = i := by
  rcases i with p | p <;> rfl

namespace HeClassicPublishedOddTestingIndex

/-- The displayed coefficient family attached to an odd table index. -/
noncomputable def coefficients
    {I : Type u} (U : I → Kˣ) (omegaData : HeClassicOmegaData (K := K))
    (pairs : Nat) : HeClassicPublishedOddTestingIndex I →
      Fin (2 * pairs + 3) → Kˣ
  | ((i, false), false) => heClassicOddC1 (K := K) pairs (U i)
  | ((i, false), true) => heClassicOddC2Even (K := K) pairs (U i)
      omegaData.omega omegaData.omegaSharp
  | ((i, true), false) => heClassicOddC1 (K := K) pairs
      (U i * uniformizerPowerUnit K (1 : Int))
  | ((i, true), true) => heClassicOddC2Odd (K := K) pairs
      (U i * uniformizerPowerUnit K (1 : Int))

/-- Every displayed odd coefficient row satisfies adjacent admissibility. -/
theorem coefficients_adjacentAdmissible
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) (pairs : Nat)
    (i : HeClassicPublishedOddTestingIndex I) :
    BONG.CoefficientAdjacentAdmissible
      (coefficients (K := K) U omegaData pairs i) := by
  rcases i with ⟨⟨i, parity⟩, column⟩
  have hunit : ordUnit K (U i) = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i)
  cases parity <;> cases column
  · exact heClassicOddC1_adjacentAdmissible pairs (U i) (by omega)
  · exact heClassicOddC2Even_adjacentAdmissible pairs (U i)
      omegaData.omega omegaData.omegaSharp hunit
      omegaData.omega_order omegaData.omegaSharp_order
  · exact heClassicOddC1_adjacentAdmissible pairs
      (U i * uniformizerPowerUnit K (1 : Int)) (by
        rw [ordUnit_mul, hunit, ordUnit_uniformizerPowerUnit]
        norm_num)
  · exact heClassicOddC2Odd_adjacentAdmissible pairs
      (U i * uniformizerPowerUnit K (1 : Int)) (by
        rw [ordUnit_mul, hunit, ordUnit_uniformizerPowerUnit]
        norm_num)

/-- Every displayed odd coefficient row satisfies the weak two-step rule. -/
theorem coefficients_weakTwoStep
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) (pairs : Nat)
    (i : HeClassicPublishedOddTestingIndex I) :
    BONG.CoefficientWeakTwoStep (K := K)
      (coefficients (K := K) U omegaData pairs i) := by
  rcases i with ⟨⟨i, parity⟩, column⟩
  have hunit : ordUnit K (U i) = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i)
  cases parity <;> cases column
  · exact heClassicOddC1_weakTwoStep pairs (U i) (by omega)
  · exact heClassicOddC2Even_weakTwoStep pairs (U i)
      omegaData.omega omegaData.omegaSharp hunit
      omegaData.omega_order omegaData.omegaSharp_order
  · exact heClassicOddC1_weakTwoStep pairs
      (U i * uniformizerPowerUnit K (1 : Int)) (by
        rw [ordUnit_mul, hunit, ordUnit_uniformizerPowerUnit]
        norm_num)
  · exact heClassicOddC2Odd_weakTwoStep pairs
      (U i * uniformizerPowerUnit K (1 : Int)) (by
        rw [ordUnit_mul, hunit, ordUnit_uniformizerPowerUnit]
        norm_num)

/-- Exact model reconstructed uniformly from an odd displayed row. -/
noncomputable def exactModel
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) (pairs : Nat)
    (i : HeClassicPublishedOddTestingIndex I) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heHuExactModel (coefficients (K := K) U omegaData pairs i)
    (coefficients_adjacentAdmissible U hU omegaData pairs i)
    (coefficients_weakTwoStep U hU omegaData pairs i)

/-- The uniform reconstruction agrees with the model attached to the table. -/
theorem exactModel_eq_model
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) (pairs : Nat)
    (i : HeClassicPublishedOddTestingIndex I) :
    exactModel (K := K) U hU omegaData pairs i =
      model (K := K) U hU omegaData pairs i := by
  rcases i with ⟨⟨i, parity⟩, column⟩
  cases parity <;> cases column <;> rfl

/-- The canonical good BONG reconstructed from an odd displayed row. -/
noncomputable def exactModelGoodBONG
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) (pairs : Nat)
    (i : HeClassicPublishedOddTestingIndex I) :=
  heHuExactGoodBONG (coefficients (K := K) U omegaData pairs i)
    (coefficients_adjacentAdmissible U hU omegaData pairs i)
    (coefficients_weakTwoStep U hU omegaData pairs i)

/-- Ambient isometry of two literal classic odd rows forces equality of their
published indices. -/
theorem model_eq_of_ambientlyIsometric
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) {pairs : Nat}
    {i j : HeClassicPublishedOddTestingIndex I}
    (hiso : (model (K := K) U hU omegaData pairs i).IsAmbientlyIsometric
      (model (K := K) U hU omegaData pairs j)) :
    i = j := by
  let hi := heHuOddIndexOfClassic i
  let hj := heHuOddIndexOfClassic j
  have hbridgeI : (model (K := K) U hU omegaData pairs i).IsAmbientlyIsometric
      (HeHuPublishedOddTestingIndex.model
        (K := K) (U := U) (pairs := pairs) hi) := by
    simpa only [hi, classicOddIndexOfHeHu_heHuOddIndexOfClassic] using
      (Lattice.QuadraticLatticeModel.classicOddModel_isAmbientlyIsometric_heHuModel
          (K := K) U hU omegaData pairs hi)
  have hbridgeJ : (model (K := K) U hU omegaData pairs j).IsAmbientlyIsometric
      (HeHuPublishedOddTestingIndex.model
        (K := K) (U := U) (pairs := pairs) hj) := by
    simpa only [hj, classicOddIndexOfHeHu_heHuOddIndexOfClassic] using
      (Lattice.QuadraticLatticeModel.classicOddModel_isAmbientlyIsometric_heHuModel
          (K := K) U hU omegaData pairs hj)
  have hHeHu : hi = hj :=
    Lattice.QuadraticLatticeModel.heHuPublishedOdd_model_eq_of_ambientlyIsometric
      U hU
      (hbridgeI.symm.trans (hiso.trans hbridgeJ))
  have hclassic := congrArg
    Lattice.QuadraticLatticeModel.classicOddIndexOfHeHu hHeHu
  simpa only [hi, hj, classicOddIndexOfHeHu_heHuOddIndexOfClassic] using hclassic

/-- A same-rank diagonal representation between displayed classic odd rows
forces equality of their indices. -/
theorem eq_of_diagonalRepresents_coefficients
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) {pairs : Nat}
    {i j : HeClassicPublishedOddTestingIndex I}
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients (coefficients (K := K) U omegaData pairs i))
      (diagonalUnitCoefficients
        (coefficients (K := K) U omegaData pairs j))) :
    i = j := by
  have hexact : Lattice.QuadraticLatticeModel.IsAmbientlyIsometric
      (exactModel (K := K) U hU omegaData pairs i)
      (exactModel (K := K) U hU omegaData pairs j) := by
    change (BONG.coefficientDiagonalSpace
      (coefficients (K := K) U omegaData pairs i)).IsIsometric
        (BONG.coefficientDiagonalSpace
          (coefficients (K := K) U omegaData pairs j))
    have hspace :=
      (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
        (coefficients (K := K) U omegaData pairs i)
        (coefficients (K := K) U omegaData pairs j)).2 hrep
    rcases hspace with ⟨f⟩
    exact ⟨f.toIsometryOfFinrankEq (by simp)⟩
  apply model_eq_of_ambientlyIsometric U hU omegaData
  rw [← exactModel_eq_model U hU omegaData pairs i,
    ← exactModel_eq_model U hU omegaData pairs j]
  exact hexact

/-- Contrapositive form used by odd literal deletion witnesses. -/
theorem not_diagonalRepresents_coefficients_of_ne
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) {pairs : Nat}
    {i j : HeClassicPublishedOddTestingIndex I} (hne : i ≠ j) :
    ¬ DiagonalRepresents
      (diagonalUnitCoefficients (coefficients (K := K) U omegaData pairs i))
      (diagonalUnitCoefficients
        (coefficients (K := K) U omegaData pairs j)) := by
  intro hrep
  exact hne (eq_of_diagonalRepresents_coefficients U hU omegaData hrep)

end HeClassicPublishedOddTestingIndex

/-! ## Literal published-row deletion witnesses -/

/-- The auxiliary large first row represents every published row except the
unit-parameter second row that it is designed to exclude. -/
theorem he2022ClassicLemma711i_barC1_represents_published_other
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) (pairs : Nat) (i : I)
    (j : HeClassicPublishedOddTestingIndex I)
    (hne : j ≠ ((i, false), true)) :
    (heClassicOddC1BarModel (K := K) (pairs + 1) (U i) omegaData.omega
      ((isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i))
      omegaData.omega_order).Represents
        (HeClassicPublishedOddTestingIndex.model
          (K := K) U hU omegaData pairs j) := by
  let deleted : HeClassicPublishedOddTestingIndex I := ((i, false), true)
  let X := HeClassicPublishedOddTestingIndex.exactModel
    (K := K) U hU omegaData pairs j
  let b := HeClassicPublishedOddTestingIndex.exactModelGoodBONG
    (K := K) U hU omegaData pairs j
  have hb : b.valueUnit = HeClassicPublishedOddTestingIndex.coefficients
      (K := K) U omegaData pairs j := by
    funext k
    simp only [b, HeClassicPublishedOddTestingIndex.exactModelGoodBONG,
      heHuExactGoodBONG_valueUnit]
  have hClassic : X.IsClassicIntegral := by
    have h := HeClassicPublishedOddTestingIndex.model_isClassicIntegral
      (K := K) U hU omegaData pairs j
    rw [← HeClassicPublishedOddTestingIndex.exactModel_eq_model] at h
    exact h
  have hother : ¬ DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients
        (heClassicOddC2Even (K := K) pairs (U i)
          omegaData.omega omegaData.omegaSharp)) := by
    have hcoeff :=
      HeClassicPublishedOddTestingIndex.not_diagonalRepresents_coefficients_of_ne
          (K := K) U hU omegaData (pairs := pairs) (i := j) (j := deleted)
          (by simpa only [deleted] using hne)
    rw [hb]
    simpa only [deleted, HeClassicPublishedOddTestingIndex.coefficients] using hcoeff
  have hlow := he2022ClassicLemma711i_barC1_represents_other
    (K := K) pairs (U i) omegaData.omega omegaData.omegaSharp
    ((isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i))
    omegaData.omega_order omegaData.omega_defect
    omegaData.hilbert_omegaSharp_omega b hClassic hother
  rw [← HeClassicPublishedOddTestingIndex.exactModel_eq_model]
  unfold Lattice.QuadraticLatticeModel.Represents
  exact hlow

/-- The large even-order second row represents every published row except the
unit-parameter first row that it is designed to exclude. -/
theorem he2022ClassicLemma711i_C2_represents_published_other
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) (pairs : Nat) (i : I)
    (j : HeClassicPublishedOddTestingIndex I)
    (hne : j ≠ ((i, false), false)) :
    (heClassicOddC2EvenModel (K := K) (pairs + 1) (U i)
      omegaData.omega omegaData.omegaSharp
      ((isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i))
      omegaData.omega_order omegaData.omegaSharp_order).Represents
        (HeClassicPublishedOddTestingIndex.model
          (K := K) U hU omegaData pairs j) := by
  let deleted : HeClassicPublishedOddTestingIndex I := ((i, false), false)
  let X := HeClassicPublishedOddTestingIndex.exactModel
    (K := K) U hU omegaData pairs j
  let b := HeClassicPublishedOddTestingIndex.exactModelGoodBONG
    (K := K) U hU omegaData pairs j
  have hb : b.valueUnit = HeClassicPublishedOddTestingIndex.coefficients
      (K := K) U omegaData pairs j := by
    funext k
    simp only [b, HeClassicPublishedOddTestingIndex.exactModelGoodBONG,
      heHuExactGoodBONG_valueUnit]
  have hClassic : X.IsClassicIntegral := by
    have h := HeClassicPublishedOddTestingIndex.model_isClassicIntegral
      (K := K) U hU omegaData pairs j
    rw [← HeClassicPublishedOddTestingIndex.exactModel_eq_model] at h
    exact h
  have hother : ¬ DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heClassicOddC1 (K := K) pairs (U i))) := by
    have hcoeff :=
      HeClassicPublishedOddTestingIndex.not_diagonalRepresents_coefficients_of_ne
        (K := K) U hU omegaData (pairs := pairs) (i := j) (j := deleted)
        (by simpa only [deleted] using hne)
    rw [hb]
    simpa only [deleted, HeClassicPublishedOddTestingIndex.coefficients] using hcoeff
  have hlow := he2022ClassicLemma711i_C2_represents_other
    (K := K) pairs (U i) omegaData.omega omegaData.omegaSharp
    ((isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i))
    omegaData.omega_order omegaData.omegaSharp_order omegaData.omega_defect
    omegaData.hilbert_omegaSharp_omega b hClassic hother
  rw [← HeClassicPublishedOddTestingIndex.exactModel_eq_model]
  unfold Lattice.QuadraticLatticeModel.Represents
  exact hlow

/-- The large odd-order second row represents every published row except the
odd-parameter first row that it is designed to exclude. -/
theorem he2022ClassicLemma711ii_C2Odd_represents_published_other
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) (pairs : Nat) (i : I)
    (j : HeClassicPublishedOddTestingIndex I)
    (hne : j ≠ ((i, true), false)) :
    (heClassicOddC2OddModel (K := K) (pairs + 1)
      (U i * uniformizerPowerUnit K (1 : Int)) (by
        rw [ordUnit_mul,
          (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i),
          ordUnit_uniformizerPowerUnit]
        norm_num)).Represents
      (HeClassicPublishedOddTestingIndex.model
        (K := K) U hU omegaData pairs j) := by
  let c := U i * uniformizerPowerUnit K (1 : Int)
  have hcOrder : ordUnit K c = 1 := by
    dsimp only [c]
    rw [ordUnit_mul,
      (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i),
      ordUnit_uniformizerPowerUnit]
    norm_num
  let deleted : HeClassicPublishedOddTestingIndex I := ((i, true), false)
  let X := HeClassicPublishedOddTestingIndex.exactModel
    (K := K) U hU omegaData pairs j
  let b := HeClassicPublishedOddTestingIndex.exactModelGoodBONG
    (K := K) U hU omegaData pairs j
  have hb : b.valueUnit = HeClassicPublishedOddTestingIndex.coefficients
      (K := K) U omegaData pairs j := by
    funext k
    simp only [b, HeClassicPublishedOddTestingIndex.exactModelGoodBONG,
      heHuExactGoodBONG_valueUnit]
  have hClassic : X.IsClassicIntegral := by
    have h := HeClassicPublishedOddTestingIndex.model_isClassicIntegral
      (K := K) U hU omegaData pairs j
    rw [← HeClassicPublishedOddTestingIndex.exactModel_eq_model] at h
    exact h
  have hother : ¬ DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heClassicOddC1 (K := K) pairs c)) := by
    have hcoeff :=
      HeClassicPublishedOddTestingIndex.not_diagonalRepresents_coefficients_of_ne
        (K := K) U hU omegaData (pairs := pairs) (i := j) (j := deleted)
        (by simpa only [deleted] using hne)
    rw [hb]
    simpa only [deleted, HeClassicPublishedOddTestingIndex.coefficients, c]
      using hcoeff
  have hlow := he2022ClassicLemma711ii_C2Odd_represents_other
    (K := K) pairs c hcOrder b hClassic hother
  rw [← HeClassicPublishedOddTestingIndex.exactModel_eq_model]
  unfold Lattice.QuadraticLatticeModel.Represents
  exact hlow

/-- The large odd-order first row represents every published row except the
odd-parameter second row that it is designed to exclude. -/
theorem he2022ClassicLemma711ii_C1_represents_published_other
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) (pairs : Nat) (i : I)
    (j : HeClassicPublishedOddTestingIndex I)
    (hne : j ≠ ((i, true), true)) :
    (heClassicOddC1Model (K := K) (pairs + 1)
      (U i * uniformizerPowerUnit K (1 : Int)) (by
        rw [ordUnit_mul,
          (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i),
          ordUnit_uniformizerPowerUnit]
        norm_num)).Represents
      (HeClassicPublishedOddTestingIndex.model
        (K := K) U hU omegaData pairs j) := by
  let c := U i * uniformizerPowerUnit K (1 : Int)
  have hcOrder : ordUnit K c = 1 := by
    dsimp only [c]
    rw [ordUnit_mul,
      (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i),
      ordUnit_uniformizerPowerUnit]
    norm_num
  let deleted : HeClassicPublishedOddTestingIndex I := ((i, true), true)
  let X := HeClassicPublishedOddTestingIndex.exactModel
    (K := K) U hU omegaData pairs j
  let b := HeClassicPublishedOddTestingIndex.exactModelGoodBONG
    (K := K) U hU omegaData pairs j
  have hb : b.valueUnit = HeClassicPublishedOddTestingIndex.coefficients
      (K := K) U omegaData pairs j := by
    funext k
    simp only [b, HeClassicPublishedOddTestingIndex.exactModelGoodBONG,
      heHuExactGoodBONG_valueUnit]
  have hClassic : X.IsClassicIntegral := by
    have h := HeClassicPublishedOddTestingIndex.model_isClassicIntegral
      (K := K) U hU omegaData pairs j
    rw [← HeClassicPublishedOddTestingIndex.exactModel_eq_model] at h
    exact h
  have hother : ¬ DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heClassicOddC2Odd (K := K) pairs c)) := by
    have hcoeff :=
      HeClassicPublishedOddTestingIndex.not_diagonalRepresents_coefficients_of_ne
        (K := K) U hU omegaData (pairs := pairs) (i := j) (j := deleted)
        (by simpa only [deleted] using hne)
    rw [hb]
    simpa only [deleted, HeClassicPublishedOddTestingIndex.coefficients, c]
      using hcoeff
  have hlow := he2022ClassicLemma711ii_C1_represents_other
    (K := K) pairs c hcOrder b hClassic hother
  rw [← HeClassicPublishedOddTestingIndex.exactModel_eq_model]
  unfold Lattice.QuadraticLatticeModel.Represents
  exact hlow

/-- Lemma 7.11 in literal finite-table form: deleting any odd published row
leaves a family represented by a classic integral rank-`n+2` witness which
still misses the deleted row. -/
theorem he2022ClassicLemma711_publishedOdd_deletionWitness
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) (pairs : Nat)
    (deleted : HeClassicPublishedOddTestingIndex I) :
    exists X : Lattice.QuadraticLatticeModel (K := K),
      X.IsClassicIntegral ∧
        ¬ X.Represents
          (HeClassicPublishedOddTestingIndex.model
            (K := K) U hU omegaData pairs deleted) ∧
        forall j : HeClassicPublishedOddTestingIndex I,
          j ≠ deleted →
            X.Represents
              (HeClassicPublishedOddTestingIndex.model
                (K := K) U hU omegaData pairs j) := by
  rcases deleted with ⟨⟨i, parity⟩, column⟩
  have hunit : ordUnit K (U i) = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i)
  have hnegative := omegaData.hilbert_omegaSharp_omega
  cases parity <;> cases column
  · let X := heClassicOddC2EvenModel (K := K) (pairs + 1) (U i)
      omegaData.omega omegaData.omegaSharp hunit omegaData.omega_order
      omegaData.omegaSharp_order
    refine ⟨X, ?_, ?_, ?_⟩
    · exact heClassicOddC2EvenModel_isClassicIntegral
        (K := K) (pairs + 1) (U i) omegaData.omega omegaData.omegaSharp
        hunit omegaData.omega_order omegaData.omegaSharp_order
    · change ¬ Lattice.Represents
        (BONG.coefficientDiagonalSpace
          (heClassicOddC2Even (K := K) (pairs + 1) (U i)
            omegaData.omega omegaData.omegaSharp))
        (BONG.coefficientDiagonalSpace
          (heClassicOddC1 (K := K) pairs (U i))) _ _
      exact (he2022ClassicLemma711i_C2_missesExactly_C1
        (K := K) pairs (U i) omegaData.omega omegaData.omegaSharp
          hnegative).not_latticeRepresents
    · intro j hne
      exact he2022ClassicLemma711i_C2_represents_published_other
        (K := K) U hU omegaData pairs i j (by simpa using hne)
  · let X := heClassicOddC1BarModel (K := K) (pairs + 1)
      (U i) omegaData.omega hunit omegaData.omega_order
    refine ⟨X, ?_, ?_, ?_⟩
    · exact heClassicOddC1BarModel_isClassicIntegral
        (K := K) (pairs + 1) (U i) omegaData.omega hunit
          omegaData.omega_order
    · change ¬ Lattice.Represents
        (BONG.coefficientDiagonalSpace
          (heClassicOddC1Bar (K := K) (pairs + 1) (U i) omegaData.omega))
        (BONG.coefficientDiagonalSpace
          (heClassicOddC2Even (K := K) pairs (U i)
            omegaData.omega omegaData.omegaSharp)) _ _
      exact (he2022ClassicLemma711i_barC1_missesExactly_C2
        (K := K) pairs (U i) omegaData.omega omegaData.omegaSharp
          hnegative).not_latticeRepresents
    · intro j hne
      exact he2022ClassicLemma711i_barC1_represents_published_other
        (K := K) U hU omegaData pairs i j (by simpa using hne)
  · let c := U i * uniformizerPowerUnit K (1 : Int)
    have hcOrder : ordUnit K c = 1 := by
      dsimp only [c]
      rw [ordUnit_mul, hunit, ordUnit_uniformizerPowerUnit]
      norm_num
    have hodd : Odd (ordUnit K c) := by rw [hcOrder]; exact odd_one
    let X := heClassicOddC2OddModel (K := K) (pairs + 1) c (by omega)
    refine ⟨X, ?_, ?_, ?_⟩
    · exact heClassicOddC2OddModel_isClassicIntegral
        (K := K) (pairs + 1) c (by omega)
    · change ¬ Lattice.Represents
        (BONG.coefficientDiagonalSpace
          (heClassicOddC2Odd (K := K) (pairs + 1) c))
        (BONG.coefficientDiagonalSpace
          (heClassicOddC1 (K := K) pairs c)) _ _
      exact (he2022ClassicLemma711ii_C2Odd_missesExactly_C1
        (K := K) pairs c hodd).not_latticeRepresents
    · intro j hne
      exact he2022ClassicLemma711ii_C2Odd_represents_published_other
        (K := K) U hU omegaData pairs i j (by simpa using hne)
  · let c := U i * uniformizerPowerUnit K (1 : Int)
    have hcOrder : ordUnit K c = 1 := by
      dsimp only [c]
      rw [ordUnit_mul, hunit, ordUnit_uniformizerPowerUnit]
      norm_num
    have hodd : Odd (ordUnit K c) := by rw [hcOrder]; exact odd_one
    let X := heClassicOddC1Model (K := K) (pairs + 1) c (by omega)
    refine ⟨X, ?_, ?_, ?_⟩
    · exact heClassicOddC1Model_isClassicIntegral
        (K := K) (pairs + 1) c (by omega)
    · change ¬ Lattice.Represents
        (BONG.coefficientDiagonalSpace
          (heClassicOddC1 (K := K) (pairs + 1) c))
        (BONG.coefficientDiagonalSpace
          (heClassicOddC2Odd (K := K) pairs c)) _ _
      exact (he2022ClassicLemma711ii_C1_missesExactly_C2Odd
        (K := K) pairs c hodd).not_latticeRepresents
    · intro j hne
      exact he2022ClassicLemma711ii_C1_represents_published_other
        (K := K) U hU omegaData pairs i j (by simpa using hne)

end Bong
