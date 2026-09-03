/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Lemma58
import Bong.Bong.Beli2019CappedDefectSharp
import Bong.Bong.DiagonalRepresentationParityProof

/-!
# He--Hu 2022, Lemma 5.9

This file formalizes the two-test obstruction used at the final central
index in odd rank.  For paper rank `N = 2*k+3`, the two tests are the
published first-column maximal lattices `N_1^N(c)` and
`N_1^N(c*cTilde#)`.  Both activate condition (iii'), while the source
prefix cannot represent both underlying quadratic spaces.
-/

namespace Bong

open Dyadic AlternatingEndpointTower

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The order (`0` or `1`) of the maximal unary representative of a square
class. -/
noncomputable def heHuLemma59Parity (x : Kˣ) : Int :=
  if Even (ordUnit K x) then 0 else 1

theorem heHuLemma59Parity_eq_zero_of_even (x : Kˣ)
    (h : Even (ordUnit K x)) :
    heHuLemma59Parity (K := K) x = 0 := by
  simp [heHuLemma59Parity, h]

theorem heHuLemma59Parity_eq_one_of_not_even (x : Kˣ)
    (h : ¬Even (ordUnit K x)) :
    heHuLemma59Parity (K := K) x = 1 := by
  simp [heHuLemma59Parity, h]

theorem heHuLemma59Parity_nonneg (x : Kˣ) :
    0 ≤ heHuLemma59Parity (K := K) x := by
  unfold heHuLemma59Parity
  split <;> omega

theorem heHuLemma59Parity_le_one (x : Kˣ) :
    heHuLemma59Parity (K := K) x ≤ 1 := by
  unfold heHuLemma59Parity
  split <;> omega

/-- The chosen order has the same parity as the original square class. -/
theorem heHuLemma59_order_sub_parity_even (x : Kˣ) :
    Even (ordUnit K x - heHuLemma59Parity (K := K) x) := by
  rcases Int.even_or_odd (ordUnit K x) with heven | hodd
  · rw [heHuLemma59Parity_eq_zero_of_even x heven]
    simpa only [sub_zero] using heven
  · have hnot : ¬Even (ordUnit K x) := by
      exact Int.not_even_iff_odd.mpr hodd
    rw [heHuLemma59Parity_eq_one_of_not_even x hnot]
    rcases hodd with ⟨t, ht⟩
    exact ⟨t, by omega⟩

/-- The normalized unary coefficient used in the canonical maximal test. -/
noncomputable def heHuLemma59NormalizedParameter (x : Kˣ) : Kˣ :=
  normalizedUnitPart K x *
    uniformizerPowerUnit K (heHuLemma59Parity (K := K) x)

@[simp]
theorem heHuLemma59NormalizedParameter_order (x : Kˣ) :
    ordUnit K (heHuLemma59NormalizedParameter (K := K) x) =
      heHuLemma59Parity (K := K) x := by
  rw [heHuLemma59NormalizedParameter, ordUnit_mul,
    ordUnit_uniformizerPowerUnit,
    (isValuationUnit_iff_ordUnit_eq_zero K _).mp
      (normalizedUnitPart_isValuationUnit K x)]
  omega

/-- Normalization preserves the field square class. -/
theorem heHuLemma59_normalized_sameSquareClass (x : Kˣ) :
    IsSquare (x * heHuLemma59NormalizedParameter (K := K) x) := by
  simpa only [heHuLemma59NormalizedParameter] using
    heHuLemma45_normalizedUniformizer_sameSquareClass x
      (heHuLemma59Parity (K := K) x)
      (heHuLemma59_order_sub_parity_even x)

/-- The unary tail of the first-column maximal lattice is integral. -/
theorem heHuLemma59UnaryIntegral (x : Kˣ) :
    Lattice.IsIntegral
      (QuadraticSpace.rescaleUnit
        (heHuLemma59NormalizedParameter (K := K) x)
        (QuadraticSpace.line K))
      (BONG.unaryModelLattice (K := K)) := by
  apply heHuIntegral_of_firstOrder_nonneg
    (BONG.unaryModelGoodBONG
      (heHuLemma59NormalizedParameter (K := K) x))
  rw [BONG.unaryModelGoodBONG_order,
    heHuLemma59NormalizedParameter_order]
  exact heHuLemma59Parity_nonneg x

/-- The literal good BONG of the first-column maximal test `N_1^(2k+3)(x)`.
It is obtained by prepending `k+1` copies of the integral half-hyperbolic
plane to the normalized unary representative of `x`. -/
noncomputable def heHuLemma59Target (x : Kˣ) (k : Nat) :
    GoodBONG
      (Lattice.halfHyperbolicExtensionForm
        (QuadraticSpace.rescaleUnit
          (heHuLemma59NormalizedParameter (K := K) x)
          (QuadraticSpace.line K)) (k + 1))
      (Lattice.halfHyperbolicExtensionLattice
        (BONG.unaryModelLattice (K := K)) (k + 1))
      (2 * k + 3) :=
  (Bong.heHu2022Lemma310BONG
    (BONG.unaryModelGoodBONG
      (heHuLemma59NormalizedParameter (K := K) x))
    (heHuLemma59UnaryIntegral x) (k + 1)).castLength (by omega)

/-- The literal values in every prepended half-hyperbolic pair. -/
theorem heHuLemma59Target_pairValues (x : Kˣ) (k : Nat)
    (t : Fin (k + 1)) :
    (heHuLemma59Target (K := K) x k).valueUnit
        ⟨2 * t.val, by omega⟩ = 1 ∧
      (heHuLemma59Target (K := K) x k).valueUnit
        ⟨2 * t.val + 1, by omega⟩ =
          -(uniformizerPowerUnit K
            (-(2 * (ramificationIndex K : Int)))) := by
  let tail := BONG.unaryModelGoodBONG
    (heHuLemma59NormalizedParameter (K := K) x)
  let htail := heHuLemma59UnaryIntegral x
  have hvalues := Bong.heHu2022Lemma310HyperbolicValues tail htail (k + 1) t
  constructor
  · rw [heHuLemma59Target, BONG.GoodBONG.valueUnit_castLength_heHu]
    exact hvalues.1
  · rw [heHuLemma59Target, BONG.GoodBONG.valueUnit_castLength_heHu]
    exact hvalues.2

/-- The hyperbolic prefix of the constructed test is literally the
half-hyperbolic value family used in Lemma 3.10. -/
theorem heHuLemma59Target_hyperbolicValueUnits_eq (x : Kˣ) (k : Nat) :
    (heHuLemma59Target (K := K) x k).prefixValueUnits (2 * k + 2)
        (by omega) =
      heHuLemma45HyperbolicBONGValues (K := K) (k + 1) := by
  funext i
  unfold prefixValueUnits
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · rcases hiEven with ⟨t, ht⟩
    have htSmall : t < k + 1 := by omega
    let j : Fin (k + 1) := ⟨t, htSmall⟩
    have hiEq : i = ⟨2 * j.val, by omega⟩ := by
      apply Fin.ext
      simpa only [j, two_mul] using ht
    rw [hiEq, (heHuLemma59Target_pairValues (K := K) x k j).1]
    simp [heHuLemma45HyperbolicBONGValues]
  · rcases hiOdd with ⟨t, ht⟩
    have htSmall : t < k + 1 := by omega
    let j : Fin (k + 1) := ⟨t, htSmall⟩
    have hiEq : i = ⟨2 * j.val + 1, by omega⟩ := by
      apply Fin.ext
      simpa only [j] using ht
    rw [hiEq, (heHuLemma59Target_pairValues (K := K) x k j).2]
    have hnotEven : ¬Even (2 * j.val + 1) :=
      Nat.not_even_two_mul_add_one j.val
    simp [heHuLemma45HyperbolicBONGValues, hnotEven]

/-- The determinant of the literal half-hyperbolic prefix has square class
`(-1)^(k+1)`. -/
theorem heHuLemma59Target_hyperbolicPrefix_signedSquare (x : Kˣ)
    (k : Nat) :
    IsSquare ((heHuLemma59Target (K := K) x k).prefixProduct (2 * k + 2) *
      (-1 : Kˣ) ^ (k + 1)) := by
  let literal := heHuLemma45HyperbolicBONGValues (K := K) (k + 1)
  let standard := standardHyperbolicEndpointTower (K := K) (k + 1)
  have hrep : DiagonalRepresents
      (diagonalUnitCoefficients literal)
      (diagonalUnitCoefficients standard) := by
    simpa only [literal, standard] using
      heHuLemma45HyperbolicBONGValues_represents_standard (K := K) (k + 1)
  rcases DiagonalRepresents.exists_prod_eq_mul_square_of_sameRank hrep with
    ⟨p, hp⟩
  have hpUnits : diagonalUnitDeterminant literal =
      diagonalUnitDeterminant standard * p ^ 2 := by
    apply Units.ext
    simp only [diagonalUnitDeterminant, Units.val_mul, Units.val_pow_eq_pow_val]
    change (Units.coeHom K (∏ i, literal i)) =
      Units.coeHom K (∏ i, standard i) * (p : K) ^ 2
    rw [map_prod (Units.coeHom K) literal Finset.univ,
      map_prod (Units.coeHom K) standard Finset.univ]
    exact hp
  have hprefix :
      (heHuLemma59Target (K := K) x k).prefixProduct (2 * k + 2) =
        (-1 : Kˣ) ^ (k + 1) * p ^ 2 := by
    calc
      (heHuLemma59Target (K := K) x k).prefixProduct (2 * k + 2) =
          diagonalUnitDeterminant
            ((heHuLemma59Target (K := K) x k).prefixValueUnits
              (2 * k + 2) (by omega)) :=
        ((heHuLemma59Target (K := K) x k)
          |>.diagonalUnitDeterminant_prefixValueUnits (2 * k + 2)
            (by omega)).symm
      _ = diagonalUnitDeterminant literal := by
        rw [heHuLemma59Target_hyperbolicValueUnits_eq]
      _ = diagonalUnitDeterminant standard * p ^ 2 := hpUnits
      _ = (-1 : Kˣ) ^ (k + 1) * p ^ 2 := by
        rw [diagonalUnitDeterminant_standardHyperbolicEndpointTower]
  refine ⟨(-1 : Kˣ) ^ (k + 1) * p, ?_⟩
  rw [hprefix]
  simp only [pow_two]
  have hsignSquare :
      ((-1 : Kˣ) ^ (k + 1)) * ((-1 : Kˣ) ^ (k + 1)) = 1 := by
    rw [← pow_add]
    have heq : k + 1 + (k + 1) = 2 * (k + 1) := by omega
    rw [heq, pow_mul]
    norm_num
  calc
    ((-1 : Kˣ) ^ (k + 1) * (p * p)) * (-1 : Kˣ) ^ (k + 1) =
        (((-1 : Kˣ) ^ (k + 1)) * ((-1 : Kˣ) ^ (k + 1))) *
          (p * p) := by ac_rfl
    _ = (((-1 : Kˣ) ^ (k + 1)) * p) *
          (((-1 : Kˣ) ^ (k + 1)) * p) := by
      rw [hsignSquare]
      simp only [one_mul]
      rw [show (((-1 : Kˣ) ^ (k + 1)) * p) *
          (((-1 : Kˣ) ^ (k + 1)) * p) =
          (((-1 : Kˣ) ^ (k + 1)) * ((-1 : Kˣ) ^ (k + 1))) *
            (p * p) by ac_rfl, hsignSquare, one_mul]

/-- Every hyperbolic pair in `N_1^(2k+3)(x)` has the published alternating
orders `0,-2e`. -/
theorem heHuLemma59Target_pairOrders (x : Kˣ) (k : Nat)
    (t : Fin (k + 1)) :
    (heHuLemma59Target (K := K) x k).order
        ⟨2 * t.val, by omega⟩ = 0 ∧
      (heHuLemma59Target (K := K) x k).order
        ⟨2 * t.val + 1, by omega⟩ =
          -(2 * (ramificationIndex K : Int)) := by
  let tail := BONG.unaryModelGoodBONG
    (heHuLemma59NormalizedParameter (K := K) x)
  let htail := heHuLemma59UnaryIntegral x
  have hvalues := Bong.heHu2022Lemma310HyperbolicValues tail htail (k + 1) t
  constructor
  · rw [heHuLemma59Target, GoodBONG.order_castLength]
    change ordUnit K
      ((Bong.heHu2022Lemma310BONG tail htail (k + 1)).valueUnit
        ⟨2 * t.val, by omega⟩) = 0
    rw [hvalues.1]
    have hone := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at hone
    omega
  · rw [heHuLemma59Target, GoodBONG.order_castLength]
    change ordUnit K
      ((Bong.heHu2022Lemma310BONG tail htail (k + 1)).valueUnit
        ⟨2 * t.val + 1, by omega⟩) = _
    rw [hvalues.2, ordUnit_neg, ordUnit_uniformizerPowerUnit]

/-- The last order of the first-column test is the chosen parity (`0` or
`1`). -/
theorem heHuLemma59Target_lastOrder (x : Kˣ) (k : Nat) :
    (heHuLemma59Target (K := K) x k).order
        ⟨2 * k + 2, by omega⟩ = heHuLemma59Parity (K := K) x := by
  let tail := BONG.unaryModelGoodBONG
    (heHuLemma59NormalizedParameter (K := K) x)
  let htail := heHuLemma59UnaryIntegral x
  rw [heHuLemma59Target, GoodBONG.order_castLength]
  change ordUnit K
    ((Bong.heHu2022Lemma310BONG tail htail (k + 1)).valueUnit
      ⟨2 * (k + 1), by omega⟩) = _
  rw [show (⟨2 * (k + 1), by omega⟩ : Fin (1 + 2 * (k + 1))) =
      ⟨2 * (k + 1) + (0 : Fin 1).val, by omega⟩ by apply Fin.ext; simp]
  rw [Bong.heHu2022Lemma310TailValues]
  dsimp only [tail]
  change ordUnit K
    ((BONG.unaryModelBONG
      (heHuLemma59NormalizedParameter (K := K) x)).valueUnit 0) = _
  rw [BONG.unaryModelBONG_valueUnit]
  exact heHuLemma59NormalizedParameter_order x

/-- The final BONG value is the normalized representative of the requested
square class. -/
theorem heHuLemma59Target_lastValue (x : Kˣ) (k : Nat) :
    (heHuLemma59Target (K := K) x k).valueUnit
        ⟨2 * k + 2, by omega⟩ =
      heHuLemma59NormalizedParameter (K := K) x := by
  let tail := BONG.unaryModelGoodBONG
    (heHuLemma59NormalizedParameter (K := K) x)
  let htail := heHuLemma59UnaryIntegral x
  rw [heHuLemma59Target, BONG.GoodBONG.valueUnit_castLength_heHu]
  rw [show (⟨2 * k + 2, by omega⟩ : Fin (1 + 2 * (k + 1))) =
      ⟨2 * (k + 1) + (0 : Fin 1).val, by omega⟩ by
        apply Fin.ext
        simp
        omega]
  rw [Bong.heHu2022Lemma310TailValues]
  change (BONG.unaryModelBONG
    (heHuLemma59NormalizedParameter (K := K) x)).valueUnit 0 = _
  rw [BONG.unaryModelBONG_valueUnit]

/-- The complete determinant of `N_1^(2k+3)(x)` has square class
`(-1)^(k+1)x`, exactly as in Definition 3.4. -/
theorem heHuLemma59Target_fullPrefix_signedParameterSquare (x : Kˣ)
    (k : Nat) :
    IsSquare ((heHuLemma59Target (K := K) x k).prefixProduct (2 * k + 3) *
      (((-1 : Kˣ) ^ (k + 1)) * x)) := by
  let b := heHuLemma59Target (K := K) x k
  have hfull : b.prefixProduct (2 * k + 3) =
      b.prefixProduct (2 * k + 2) *
        heHuLemma59NormalizedParameter (K := K) x := by
    have hstep := b.toBONG.prefixProduct_succ (2 * k + 2) (by omega)
    unfold GoodBONG.prefixProduct
    have hstep' : b.toBONG.prefixProduct (2 * k + 3) =
        b.toBONG.prefixProduct (2 * k + 2) *
          b.toBONG.valueUnit ⟨2 * k + 2, by omega⟩ := by
      simpa only [show 2 * k + 2 + 1 = 2 * k + 3 by omega] using hstep
    rw [hstep']
    change _ = _ * heHuLemma59NormalizedParameter (K := K) x
    rw [show b.toBONG.valueUnit ⟨2 * k + 2, by omega⟩ =
      b.valueUnit ⟨2 * k + 2, by omega⟩ by rfl]
    congr 1
    simpa only [b] using heHuLemma59Target_lastValue (K := K) x k
  have hhead := heHuLemma59Target_hyperbolicPrefix_signedSquare
    (K := K) x k
  have htail := heHuLemma59_normalized_sameSquareClass (K := K) x
  have hproduct := hhead.mul htail
  dsimp only [b] at hfull
  rw [hfull]
  have hreorder :
      (heHuLemma59Target (K := K) x k).prefixProduct (2 * k + 2) *
          heHuLemma59NormalizedParameter (K := K) x *
            (((-1 : Kˣ) ^ (k + 1)) * x) =
        (heHuLemma59Target (K := K) x k).prefixProduct (2 * k + 2) *
          (-1 : Kˣ) ^ (k + 1) *
            (x * heHuLemma59NormalizedParameter (K := K) x) := by
    ac_rfl
  rw [hreorder]
  exact hproduct

/-- The first-column maximal test is integral. -/
theorem heHuLemma59Target_integral (x : Kˣ) (k : Nat) :
    Lattice.IsIntegral
      (Lattice.halfHyperbolicExtensionForm
        (QuadraticSpace.rescaleUnit
          (heHuLemma59NormalizedParameter (K := K) x)
          (QuadraticSpace.line K)) (k + 1))
      (Lattice.halfHyperbolicExtensionLattice
        (BONG.unaryModelLattice (K := K)) (k + 1)) := by
  apply heHuIntegral_of_firstOrder_nonneg (heHuLemma59Target (K := K) x k)
  have h := (heHuLemma59Target_pairOrders (K := K) x k (0 : Fin (k + 1))).1
  have hzero : (heHuLemma59Target (K := K) x k).order 0 = 0 := by
    have hindex : (0 : Fin (2 * k + 3)) =
        ⟨2 * (0 : Fin (k + 1)).val, by omega⟩ := by
      apply Fin.ext
      simp
    rw [hindex]
    exact h
  rw [hzero]

/-- The even hyperbolic prefix of the first-column test has capped defect
at least `2e`. -/
theorem heHuLemma59Target_prefixDefect_ge (x : Kˣ) (k : Nat) :
    ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      (heHuLemma59Target (K := K) x k).truncatedPrefixDefect
        (heHuLemma59Target (K := K) x k) ((-1) ^ (k + 1)) 0
          (2 * k + 2) := by
  let b := heHuLemma59Target (K := K) x k
  let last : Fin (2 * k + 3) := ⟨2 * k + 1, by omega⟩
  have hlastOdd : Odd last.val := ⟨k, by simp [last]⟩
  have hlastOrder : b.order last =
      -(2 * (ramificationIndex K : Int)) := by
    have h := (heHuLemma59Target_pairOrders (K := K) x k
      (⟨k, by omega⟩ : Fin (k + 1))).2
    simpa only [b, last] using h
  have h := (b.heHu2022Proposition27iiiiv
    (heHuLemma59Target_integral x k) last hlastOdd hlastOrder)
      |>.alternatingPrefixDefect
  have hlength : 2 * k + 1 - 1 + 2 = 2 * k + 2 := by omega
  have hexponent : (2 * k + 2) / 2 = k + 1 := by omega
  simpa only [b, last, hlength, hexponent] using h

/-! ## Source and target parity at the final central index -/

/-- The paper's `cTilde=(-1)^((N+1)/2)a_(1,N+1)` for `N=2k+3`. -/
noncomputable def heHuLemma59CTilde {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) : Kˣ :=
  (-1) ^ (k + 2) * a.prefixProduct (2 * k + 4)

/-- The paper's `c=(-1)^((N+1)/2)a_(1,N+2)` for `N=2k+3`. -/
noncomputable def heHuLemma59C {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) : Kˣ :=
  (-1) ^ (k + 2) * a.prefixProduct (2 * k + 5)

/-- The `cTilde` notation in Lemma 5.9 is exactly the signed prefix to
which Lemma 5.8 applies. -/
theorem heHuLemma59CTilde_eq_lemma58Prefix {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) :
    heHuLemma59CTilde a k = a.heHuLemma58Prefix (n := 2 * k + 1) := by
  unfold heHuLemma59CTilde heHuLemma58Prefix
  congr 2
  omega

/-- Under `I1^E(N-1)`, the valuation of the first `N=2k+3` source
coefficients is even.  This is the parity observation `ord(a_{1,N}) even`
used at the start of the published proof. -/
theorem heHuLemma59_sourceInitialPrefixOrder_even {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (hm : 2 * k + 3 ≤ m)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega)) :
    Even (ordUnit K (a.prefixProduct (2 * k + 3))) := by
  have hentries (j : Nat) (hj : j < 2 * k + 3) :
      Even (a.orderSequence.entryOrZero j) := by
    let jf : Fin (m + 3) := ⟨j, by omega⟩
    rw [a.orderSequence_entryOrZero_eq_order jf]
    rcases Nat.even_or_odd j with hjeven | hjodd
    · have hoddPaper : Odd (j + 1) := hjeven.add_one
      have hzero := hI1.oddOrder ⟨j, by omega⟩ hoddPaper
      simpa only [jf, hzero] using (Even.zero : Even (0 : Int))
    · have hevenPaper : Even (j + 1) := by
        rcases hjodd with ⟨t, ht⟩
        refine ⟨t + 1, ?_⟩
        omega
      have hjlt : j < 2 * k + 2 := by
        rcases hjodd with ⟨t, ht⟩
        omega
      have horder := hI1.evenOrder ⟨j, hjlt⟩ hevenPaper
      rw [horder]
      refine ⟨-(ramificationIndex K : Int), ?_⟩
      ring
  rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
    (2 * k + 3) (by omega)]
  exact a.orderSequence.prefixSum_even_of_entries_even (2 * k + 3) hentries

/-- The signed determinant `c=(-1)^(k+2)a_(1,N+2)` has the parity of the
published gap `R_(N+2)-R_(N+1)`. -/
theorem heHuLemma59_c_order_sub_gap_even {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (hm : 2 * k + 3 ≤ m)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega)) :
    Even (ordUnit K (heHuLemma59C a k) -
      (a.order ⟨2 * k + 4, by omega⟩ -
        a.order ⟨2 * k + 3, by omega⟩)) := by
  have hprefix := a.heHuLemma59_sourceInitialPrefixOrder_even k hm hI1
  rcases hprefix with ⟨t, ht⟩
  have hproduct :
      ordUnit K (a.prefixProduct (2 * k + 5)) =
        ordUnit K (a.prefixProduct (2 * k + 3)) +
          a.order ⟨2 * k + 3, by omega⟩ +
          a.order ⟨2 * k + 4, by omega⟩ := by
    calc
      ordUnit K (a.prefixProduct (2 * k + 5)) =
          ordUnit K (a.prefixProduct (2 * k + 4)) +
            a.order ⟨2 * k + 4, by omega⟩ := by
        unfold GoodBONG.prefixProduct
        rw [show 2 * k + 5 = (2 * k + 4) + 1 by omega,
          a.toBONG.prefixProduct_succ (2 * k + 4) (by omega),
          ordUnit_mul]
        rfl
      _ = ordUnit K (a.prefixProduct (2 * k + 3)) +
            a.order ⟨2 * k + 3, by omega⟩ +
            a.order ⟨2 * k + 4, by omega⟩ := by
        have hstep :
            ordUnit K (a.prefixProduct (2 * k + 4)) =
              ordUnit K (a.prefixProduct (2 * k + 3)) +
                a.order ⟨2 * k + 3, by omega⟩ := by
          unfold GoodBONG.prefixProduct
          rw [show 2 * k + 4 = (2 * k + 3) + 1 by omega,
            a.toBONG.prefixProduct_succ (2 * k + 3) (by omega),
            ordUnit_mul]
          rfl
        rw [hstep]
  have hminusOne : ordUnit K (-1 : Kˣ) = 0 :=
    ordUnit_neg_one_eq_zero (K := K)
  have hcOrder :
      ordUnit K (heHuLemma59C a k) =
        ordUnit K (a.prefixProduct (2 * k + 5)) := by
    unfold heHuLemma59C
    rw [ordUnit_mul, ordUnit_pow, hminusOne]
    simp only [mul_zero, zero_add]
  refine ⟨t + a.order ⟨2 * k + 3, by omega⟩, ?_⟩
  rw [hcOrder, hproduct, ht]
  ring

/-- Adding an even difference does not change integer parity. -/
theorem heHuLemma59_even_iff_of_sub_even {x y : Int}
    (h : Even (x - y)) : Even x ↔ Even y := by
  rcases h with ⟨d, hd⟩
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t - d, ?_⟩
    omega
  · rintro ⟨t, ht⟩
    refine ⟨d + t, ?_⟩
    omega

/-- If the valuation of `x` differs from `gap` by an even integer, the
normalized maximal representative of `x` has order zero or one according
to the parity split in equation (5.2). -/
theorem heHuLemma59Parity_eq_gapParity (x : Kˣ) (gap : Int)
    (h : Even (ordUnit K x - gap)) :
    heHuLemma59Parity (K := K) x = if Even gap then 0 else 1 := by
  have hparity : Even (ordUnit K x) ↔ Even gap :=
    heHuLemma59_even_iff_of_sub_even h
  by_cases hgap : Even gap
  · have hx : Even (ordUnit K x) := hparity.mpr hgap
    simp [heHuLemma59Parity, hx, hgap]
  · have hx : ¬Even (ordUnit K x) := fun hx ↦ hgap (hparity.mp hx)
    simp [heHuLemma59Parity, hx, hgap]

/-- Multiplication by a valuation unit preserves the final-test parity. -/
theorem heHuLemma59_mul_unit_order_sub_gap_even (x u : Kˣ) (gap : Int)
    (hx : Even (ordUnit K x - gap))
    (hu : IsValuationUnit K (u : K)) :
    Even (ordUnit K (x * u) - gap) := by
  have huOrder : ordUnit K u = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K u).mp hu
  rcases hx with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [ordUnit_mul, huOrder]
  omega

/-- Equation (5.2) together with Remark 5.2 gives the strict order part of
the final central trigger: `R_(N+2)>S_N`. -/
theorem heHuLemma59_boundaryOrder_gt_gapParity {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (hm : 2 * k + 3 ≤ m)
    (hIntegral : Lattice.IsIntegral q L)
    (hTrigger : a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
      1 < a.order ⟨2 * k + 4, by omega⟩) :
    (if Even (a.order ⟨2 * k + 4, by omega⟩ -
        a.order ⟨2 * k + 3, by omega⟩) then 0 else 1) <
      a.order ⟨2 * k + 4, by omega⟩ := by
  have hodd : Odd (2 * k + 3) := ⟨k + 1, by omega⟩
  have hcasesRaw := (a.heHu2022Remark52 (n := 2 * k + 3)
    (by omega) hodd (by omega) hIntegral).mp hTrigger
  have hcases :
      (a.order ⟨2 * k + 3, by omega⟩ = 1 ∧
          a.order ⟨2 * k + 4, by omega⟩ = 1) ∨
        1 < a.order ⟨2 * k + 4, by omega⟩ := by
    simpa only using hcasesRaw
  by_cases heven : Even (a.order ⟨2 * k + 4, by omega⟩ -
      a.order ⟨2 * k + 3, by omega⟩)
  · rw [if_pos heven]
    rcases hcases with hboth | hlarge
    · omega
    · omega
  · rw [if_neg heven]
    rcases hcases with hboth | hlarge
    · exfalso
      apply heven
      rw [hboth.1, hboth.2, sub_self]
      exact Even.zero
    · exact hlarge

/-- Paper index `i=N+1` in the final central test of odd rank
`N=2k+3`. -/
def heHuLemma59CentralIndex {m : Nat} (k : Nat) (hm : 2 * k + 3 ≤ m) :
    CentralRepresentationIndex (m + 3) (2 * k + 3) where
  val := 2 * k + 4
  one_lt := by omega
  lt_large := by omega
  le_small_succ := by omega

/-! ## The two capped defects in the trigger -/

/-- Removing the alpha cap from the Lemma 5.8 source prefix. -/
theorem heHuLemma59_sourceCTildeCapped_eq {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (hm : 2 * k + 3 ≤ m)
    (hraw : defectOrder (K := K) (heHuLemma59CTilde a k) =
      ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
        WithTop ℚ))
    (hcap : (1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) <
      a.alphaValue ⟨2 * k + 3, by omega⟩) :
    a.truncatedPrefixDefect a ((-1) ^ (k + 2)) (2 * k + 4) 0 =
      ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
        WithTop ℚ) := by
  rw [truncatedPrefixDefect]
  have hcapEq : a.prefixAlphaCap (2 * k + 4) =
      (a.alphaValue ⟨2 * k + 3, by omega⟩ : WithTop ℚ) := by
    have h := a.prefixAlphaCap_of_internal (i := 2 * k + 4)
      (by omega) (by omega)
    convert h using 1
    congr 2
  rw [hcapEq, a.prefixAlphaCap_zero]
  have hproduct :
      (-1 : Kˣ) ^ (k + 2) * a.prefixProduct (2 * k + 4) *
          a.prefixProduct 0 = heHuLemma59CTilde a k := by
    simp only [GoodBONG.prefixProduct, BONG.prefixProduct_zero, mul_one,
      heHuLemma59CTilde]
  rw [hproduct, hraw]
  simp only [min_top_right]
  apply min_eq_left
  exact_mod_cast hcap.le

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
/-- The two signed hyperbolic factors used in the domination calculation
multiply to `-1`. -/
theorem heHuLemma59_signedPowers_mul (k : Nat) :
    ((-1 : Kˣ) ^ (k + 2)) * ((-1 : Kˣ) ^ (k + 1)) = -1 := by
  rw [← pow_add]
  have hexponent : k + 2 + (k + 1) = 2 * (k + 1) + 1 := by omega
  rw [hexponent, pow_add, pow_mul]
  norm_num

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
/-- Consecutive powers of `-1` differ by a sign. -/
theorem heHuLemma59_neg_signedPower_eq (k : Nat) :
    -((-1 : Kˣ) ^ (k + 2)) = (-1 : Kˣ) ^ (k + 1) := by
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  simp

/-- The raw second mixed product has the square class `c*x`.  This is the
determinant calculation immediately preceding equation (5.4). -/
theorem heHuLemma59_currentMixed_sameSquareClass {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (x : Kˣ) :
    IsSquare
      (((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
          (heHuLemma59Target (K := K) x k).prefixProduct (2 * k + 3)) *
        (heHuLemma59C a k * x)) := by
  let A := a.prefixProduct (2 * k + 5)
  let B := (heHuLemma59Target (K := K) x k).prefixProduct (2 * k + 3)
  have hA : IsSquare (A * A) := ⟨A, rfl⟩
  have hB := heHuLemma59Target_fullPrefix_signedParameterSquare
    (K := K) x k
  have hproduct := hA.mul hB
  have heq :
      (((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
          (heHuLemma59Target (K := K) x k).prefixProduct (2 * k + 3)) *
          (heHuLemma59C a k * x)) =
        (A * A) * (B * (((-1 : Kˣ) ^ (k + 1)) * x)) := by
    simp only [heHuLemma59C]
    have hsign : (-1 : Kˣ) * ((-1 : Kˣ) ^ (k + 2)) =
        (-1 : Kˣ) ^ (k + 1) := by
      calc
        (-1 : Kˣ) * ((-1 : Kˣ) ^ (k + 2)) =
            -((-1 : Kˣ) ^ (k + 2)) := by simp
        _ = (-1 : Kˣ) ^ (k + 1) :=
          heHuLemma59_neg_signedPower_eq (K := K) k
    rw [show (-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
          (heHuLemma59Target (K := K) x k).prefixProduct (2 * k + 3) *
            (((-1 : Kˣ) ^ (k + 2) * a.prefixProduct (2 * k + 5)) * x) =
        ((-1 : Kˣ) * ((-1 : Kˣ) ^ (k + 2))) *
          (A * A) * (B * x) by dsimp only [A, B]; ac_rfl]
    rw [hsign]
    ac_rfl
  rw [heq]
  exact hproduct

/-- Defect-order form of the preceding determinant square-class
calculation. -/
theorem heHuLemma59_currentMixed_defectOrder_eq {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (x : Kˣ) :
    defectOrder (K := K)
        ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
          (heHuLemma59Target (K := K) x k).prefixProduct (2 * k + 3)) =
      defectOrder (K := K) (heHuLemma59C a k * x) :=
  heHuLemma45_defectOrder_eq_of_mul_isSquare _ _
    (heHuLemma59_currentMixed_sameSquareClass a k x)

/-- For the first test `N_1^N(c)`, the raw second mixed defect is infinite. -/
theorem heHuLemma59_currentMixed_defectOrder_C {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) :
    defectOrder (K := K)
        ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
          (heHuLemma59Target (K := K) (heHuLemma59C a k) k).prefixProduct
            (2 * k + 3)) = ⊤ := by
  rw [heHuLemma59_currentMixed_defectOrder_eq]
  apply defectOrder_eq_top_of_isSquare
  exact ⟨heHuLemma59C a k, rfl⟩

/-- For the second test `N_1^N(c*u)`, the raw second mixed defect equals
the defect of the unit `u`; later `u=cTilde#`. -/
theorem heHuLemma59_currentMixed_defectOrder_C_mul {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (u : Kˣ) :
    defectOrder (K := K)
        ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
          (heHuLemma59Target (K := K) (heHuLemma59C a k * u) k).prefixProduct
            (2 * k + 3)) =
      defectOrder (K := K) u := by
  rw [heHuLemma59_currentMixed_defectOrder_eq]
  apply heHuLemma45_defectOrder_eq_of_mul_isSquare
  refine ⟨heHuLemma59C a k * u, ?_⟩
  ac_rfl

/-- At the final index the second bracketed defect is the minimum of its
raw field defect and the single source alpha cap `alpha_(N+2)`. -/
theorem heHuLemma59_centralCurrentDefect_eq_min {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (hm : 2 * k + 3 ≤ m)
    (x : Kˣ) :
    a.centralCurrentDefect (heHuLemma59Target (K := K) x k)
        (heHuLemma59CentralIndex k hm) =
      min
        (defectOrder (K := K)
          ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
            (heHuLemma59Target (K := K) x k).prefixProduct (2 * k + 3)))
        (a.alphaValue ⟨2 * k + 4, by omega⟩ : WithTop ℚ) := by
  let b := heHuLemma59Target (K := K) x k
  have hadd : 2 * k + 4 + 1 = 2 * k + 5 := by omega
  have hsub : 2 * k + 4 - 1 = 2 * k + 3 := by omega
  have hsourceCap : a.prefixAlphaCap (2 * k + 5) =
      (a.alphaValue ⟨2 * k + 4, by omega⟩ : WithTop ℚ) := by
    have h := a.prefixAlphaCap_of_internal (i := 2 * k + 5)
      (by omega) (by omega)
    convert h using 1
    congr 2
  have htargetCap : b.prefixAlphaCap (2 * k + 3) = ⊤ := by
    simpa only [b] using b.prefixAlphaCap_last
  unfold centralCurrentDefect
  simp only [heHuLemma59CentralIndex, hadd, hsub]
  rw [truncatedPrefixDefect, hsourceCap]
  change min
      (defectOrder (K := K)
        ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
          b.prefixProduct (2 * k + 3)))
      (min (a.alphaValue ⟨2 * k + 4, by omega⟩ : WithTop ℚ)
        (b.prefixAlphaCap (2 * k + 3))) = _
  rw [htargetCap, min_top_right]

/-- A raw-defect and alpha-cap lower bound gives equation (5.4) for either
test lattice. -/
theorem heHuLemma59_centralCurrentDefect_gt {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (hm : 2 * k + 3 ≤ m)
    (x : Kˣ) (G : Int)
    (hraw : ((G : ℚ) : WithTop ℚ) <
      defectOrder (K := K)
        ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
          (heHuLemma59Target (K := K) x k).prefixProduct (2 * k + 3)))
    (hcap : (G : ℚ) < a.alphaValue ⟨2 * k + 4, by omega⟩) :
    ((G : ℚ) : WithTop ℚ) <
      a.centralCurrentDefect (heHuLemma59Target (K := K) x k)
        (heHuLemma59CentralIndex k hm) := by
  rw [a.heHuLemma59_centralCurrentDefect_eq_min k hm x]
  apply lt_min hraw
  exact_mod_cast hcap

/-- The complementary sharp defect is strictly larger than the odd-rank
threshold.  This packages the two parity branches in the proof of (5.4). -/
theorem heHuLemma59_sharpDefect_gt_threshold {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (hm : 2 * k + 3 ≤ m)
    (u : Kˣ)
    (hboundary :
      (if Even (a.order ⟨2 * k + 4, by omega⟩ -
          a.order ⟨2 * k + 3, by omega⟩) then 0 else 1) <
        a.order ⟨2 * k + 4, by omega⟩)
    (hsharp : defectOrder (K := K) u =
      (((2 * (ramificationIndex K : Int) +
          a.order ⟨2 * k + 3, by omega⟩ - 1 : Int) : ℚ) :
        WithTop ℚ)) :
    ((a.heHuOddThreshold (2 * k + 3) (by omega) : ℚ) : WithTop ℚ) <
      defectOrder (K := K) u := by
  let gap := a.order ⟨2 * k + 4, by omega⟩ -
    a.order ⟨2 * k + 3, by omega⟩
  by_cases heven : Even gap
  · have hRPositive : 0 < a.order ⟨2 * k + 4, by omega⟩ := by
      simpa only [gap, if_pos heven] using hboundary
    have hInt :
        a.heHuOddThreshold (2 * k + 3) (by omega) <
          2 * (ramificationIndex K : Int) +
            a.order ⟨2 * k + 3, by omega⟩ - 1 := by
      rw [heHuOddThreshold]
      change (if Even (a.order ⟨2 * k + 4, by omega⟩ -
          a.order ⟨2 * k + 3, by omega⟩) then
          2 * (ramificationIndex K : Int) -
            a.order ⟨2 * k + 4, by omega⟩ +
              a.order ⟨2 * k + 3, by omega⟩ - 1
        else
          2 * (ramificationIndex K : Int) -
            a.order ⟨2 * k + 4, by omega⟩ +
              a.order ⟨2 * k + 3, by omega⟩) < _
      simp only [gap] at heven
      rw [if_pos heven]
      omega
    rw [hsharp]
    exact_mod_cast hInt
  · have hROne : 1 < a.order ⟨2 * k + 4, by omega⟩ := by
      simpa only [gap, if_neg heven] using hboundary
    have hInt :
        a.heHuOddThreshold (2 * k + 3) (by omega) <
          2 * (ramificationIndex K : Int) +
            a.order ⟨2 * k + 3, by omega⟩ - 1 := by
      rw [heHuOddThreshold]
      change (if Even (a.order ⟨2 * k + 4, by omega⟩ -
          a.order ⟨2 * k + 3, by omega⟩) then
          2 * (ramificationIndex K : Int) -
            a.order ⟨2 * k + 4, by omega⟩ +
              a.order ⟨2 * k + 3, by omega⟩ - 1
        else
          2 * (ramificationIndex K : Int) -
            a.order ⟨2 * k + 4, by omega⟩ +
              a.order ⟨2 * k + 3, by omega⟩) < _
      simp only [gap] at heven
      rw [if_neg heven]
      omega
    rw [hsharp]
    exact_mod_cast hInt

/-- Rearrangement of equation (5.1) used in (5.3). -/
theorem heHuLemma59_threshold_identity {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (hm : 2 * k + 3 ≤ m) :
    2 * (ramificationIndex K : Int) +
        (if Even (a.order ⟨2 * k + 4, by omega⟩ -
            a.order ⟨2 * k + 3, by omega⟩) then 0 else 1) -
          a.order ⟨2 * k + 4, by omega⟩ =
      (1 - a.order ⟨2 * k + 3, by omega⟩) +
        a.heHuOddThreshold (2 * k + 3) (by omega) := by
  let gap := a.order ⟨2 * k + 4, by omega⟩ -
    a.order ⟨2 * k + 3, by omega⟩
  by_cases heven : Even gap
  · rw [heHuOddThreshold]
    change 2 * (ramificationIndex K : Int) +
        (if Even gap then 0 else 1) -
          a.order ⟨2 * k + 4, by omega⟩ =
      (1 - a.order ⟨2 * k + 3, by omega⟩) +
        (if Even gap then
          2 * (ramificationIndex K : Int) -
            a.order ⟨2 * k + 4, by omega⟩ +
              a.order ⟨2 * k + 3, by omega⟩ - 1
        else
          2 * (ramificationIndex K : Int) -
            a.order ⟨2 * k + 4, by omega⟩ +
              a.order ⟨2 * k + 3, by omega⟩)
    simp only [if_pos heven]
    ring
  · rw [heHuOddThreshold]
    change 2 * (ramificationIndex K : Int) +
        (if Even gap then 0 else 1) -
          a.order ⟨2 * k + 4, by omega⟩ =
      (1 - a.order ⟨2 * k + 3, by omega⟩) +
        (if Even gap then
          2 * (ramificationIndex K : Int) -
            a.order ⟨2 * k + 4, by omega⟩ +
              a.order ⟨2 * k + 3, by omega⟩ - 1
        else
          2 * (ramificationIndex K : Int) -
            a.order ⟨2 * k + 4, by omega⟩ +
              a.order ⟨2 * k + 3, by omega⟩)
    simp only [if_neg heven]
    ring

/-- The first bracketed defect in (5.3) is exactly `1-R_(N+1)` for every
first-column test. -/
theorem heHuLemma59_centralPreviousDefect_eq {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (hm : 2 * k + 3 ≤ m)
    (hraw : defectOrder (K := K) (heHuLemma59CTilde a k) =
      ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
        WithTop ℚ))
    (hcap : (1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) <
      a.alphaValue ⟨2 * k + 3, by omega⟩)
    (hlt :
      ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ) <
        ((2 * ramificationIndex K : ℚ) : WithTop ℚ))
    (x : Kˣ) :
    a.centralPreviousDefect (heHuLemma59Target (K := K) x k)
        (heHuLemma59CentralIndex k hm) =
      ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
        WithTop ℚ) := by
  let b := heHuLemma59Target (K := K) x k
  let sign : Kˣ := (-1) ^ (k + 2)
  let targetSign : Kˣ := (-1) ^ (k + 1)
  have hsource : a.truncatedPrefixDefect a sign (2 * k + 4) 0 =
      ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
        WithTop ℚ) := by
    simpa only [sign] using
      a.heHuLemma59_sourceCTildeCapped_eq k hm hraw hcap
  have htarget : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      b.truncatedPrefixDefect b targetSign 0 (2 * k + 2) := by
    simpa only [b, targetSign] using
      heHuLemma59Target_prefixDefect_ge (K := K) x k
  have htargetCross : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect b targetSign 0 (2 * k + 2) := by
    simpa only [truncatedPrefixDefect, a.prefixAlphaCap_zero,
      b.prefixAlphaCap_zero, GoodBONG.prefixProduct,
      BONG.prefixProduct_zero, mul_one] using htarget
  have hsep : a.truncatedPrefixDefect a sign (2 * k + 4) 0 <
      a.truncatedPrefixDefect b targetSign 0 (2 * k + 2) := by
    rw [hsource]
    exact hlt.trans_le htargetCross
  have hmul := a.truncatedPrefixDefect_mul_eq_left_of_lt_right
    a b sign targetSign (2 * k + 4) 0 (2 * k + 2) hsep
  have hsign : sign * targetSign = (-1 : Kˣ) := by
    simpa only [sign, targetSign] using
      heHuLemma59_signedPowers_mul (K := K) k
  rw [hsign, hsource] at hmul
  have hsub : 2 * k + 4 - 2 = 2 * k + 2 := by omega
  simpa only [centralPreviousDefect, heHuLemma59CentralIndex, b, hsub] using hmul

/-- The two numerical assertions of Lemma 5.9(i), expressed as the revised
condition-(iii') trigger at `i=N+1`. -/
theorem heHuLemma59_defectTrigger_of_bounds {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (hm : 2 * k + 3 ≤ m)
    (x : Kˣ)
    (hlast : (heHuLemma59Target (K := K) x k).order
        ⟨2 * k + 2, by omega⟩ =
      (if Even (a.order ⟨2 * k + 4, by omega⟩ -
          a.order ⟨2 * k + 3, by omega⟩) then 0 else 1))
    (hboundary :
      (if Even (a.order ⟨2 * k + 4, by omega⟩ -
          a.order ⟨2 * k + 3, by omega⟩) then 0 else 1) <
        a.order ⟨2 * k + 4, by omega⟩)
    (hprevious :
      a.centralPreviousDefect (heHuLemma59Target (K := K) x k)
          (heHuLemma59CentralIndex k hm) =
        ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ))
    (hcurrent :
      ((a.heHuOddThreshold (2 * k + 3) (by omega) : ℚ) : WithTop ℚ) <
        a.centralCurrentDefect (heHuLemma59Target (K := K) x k)
          (heHuLemma59CentralIndex k hm)) :
    a.centralDefectTrigger (heHuLemma59Target (K := K) x k)
      (heHuLemma59CentralIndex k hm) := by
  let b := heHuLemma59Target (K := K) x k
  let i := heHuLemma59CentralIndex k hm
  have hshape :
      b.order ⟨2 * k + 2, by omega⟩ <
          a.order ⟨2 * k + 4, by omega⟩ ∧
        ((2 * (ramificationIndex K : ℚ) +
            (b.order ⟨2 * k + 2, by omega⟩ : ℚ) -
            (a.order ⟨2 * k + 4, by omega⟩ : ℚ) : ℚ) :
              WithTop ℚ) <
          a.centralPreviousDefect b i + a.centralCurrentDefect b i := by
    constructor
    · rw [show b.order ⟨2 * k + 2, by omega⟩ =
          (if Even (a.order ⟨2 * k + 4, by omega⟩ -
              a.order ⟨2 * k + 3, by omega⟩) then 0 else 1) by
        simpa only [b] using hlast]
      exact hboundary
    · have hsumLt :
          (((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
              WithTop ℚ)) +
              ((a.heHuOddThreshold (2 * k + 3) (by omega) : ℚ) :
                WithTop ℚ) <
            (((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
              WithTop ℚ)) +
              a.centralCurrentDefect (heHuLemma59Target (K := K) x k)
                (heHuLemma59CentralIndex k hm) :=
        WithTop.add_lt_add_left WithTop.coe_ne_top hcurrent
      have hidentity := a.heHuLemma59_threshold_identity k hm
      have hidentityQ :
          2 * (ramificationIndex K : ℚ) +
              ((if Even (a.order ⟨2 * k + 4, by omega⟩ -
                  a.order ⟨2 * k + 3, by omega⟩) then
                    (0 : Int) else 1 : Int) : ℚ) -
              (a.order ⟨2 * k + 4, by omega⟩ : ℚ) =
            (((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) +
              (a.heHuOddThreshold (2 * k + 3) (by omega) : ℚ) := by
        exact_mod_cast hidentity
      have hleft :
          ((2 * (ramificationIndex K : ℚ) +
              ((if Even (a.order ⟨2 * k + 4, by omega⟩ -
                  a.order ⟨2 * k + 3, by omega⟩) then
                    (0 : Int) else 1 : Int) : ℚ) -
              (a.order ⟨2 * k + 4, by omega⟩ : ℚ) : ℚ) :
                WithTop ℚ) =
            (((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
                WithTop ℚ)) +
              ((a.heHuOddThreshold (2 * k + 3) (by omega) : ℚ) :
                WithTop ℚ) := by
        rw [← WithTop.coe_add]
        exact congrArg (fun z : ℚ ↦ (z : WithTop ℚ)) hidentityQ
      rw [show b.order ⟨2 * k + 2, by omega⟩ =
          (if Even (a.order ⟨2 * k + 4, by omega⟩ -
              a.order ⟨2 * k + 3, by omega⟩) then 0 else 1) by
        simpa only [b] using hlast]
      rw [hleft]
      have hprevious' : a.centralPreviousDefect b i =
          ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
            WithTop ℚ) := by
        simpa only [b, i] using hprevious
      rw [hprevious']
      exact hsumLt
  unfold centralDefectTrigger
  have hsub : 2 * k + 4 - 2 = 2 * k + 2 := by omega
  simpa only [b, i, heHuLemma59CentralIndex, hsub] using hshape

/-! ## Lemma 5.9(i): both numerical tests are active -/

/-- He--Hu, Lemma 5.9(i).  Both published first-column maximal tests
activate the revised condition-(iii') trigger at `i=N+1`.  The hypothesis
`I3^E(N-1)` is retained exactly as printed although this numerical part of
the proof does not consume it. -/
theorem heHu2022Lemma59i {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (hm : 2 * k + 3 ≤ m)
    (hIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (_hI3 : a.HeHuI3E (2 * k + 2) (by omega))
    (hAlphaNext :
      (a.heHuOddThreshold (2 * k + 3) (by omega) : ℚ) <
        a.alphaValue ⟨2 * k + 4, by omega⟩)
    (hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1)
    (hTrigger : a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
      1 < a.order ⟨2 * k + 4, by omega⟩) :
    let cTilde := heHuLemma59CTilde a k
    ∃ hc : HeHuSharpDomain cTilde,
      let u := heHuSharp cTilde hc
      a.centralDefectTrigger
          (heHuLemma59Target (K := K) (heHuLemma59C a k) k)
          (heHuLemma59CentralIndex k hm) ∧
        a.centralDefectTrigger
          (heHuLemma59Target (K := K) (heHuLemma59C a k * u) k)
          (heHuLemma59CentralIndex k hm) := by
  dsimp only
  have hodd : Odd (2 * k + 3) := ⟨k + 1, by omega⟩
  have h58Raw := a.heHu2022Lemma58 (n := 2 * k + 1) (by omega)
    hodd hm hIntegral hI1 hI2 hAlpha hTrigger
  have h58 :
      ∃ hc : HeHuSharpDomain (heHuLemma59CTilde a k),
        defectOrder (K := K) (heHuLemma59CTilde a k) =
            ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
              WithTop ℚ) ∧
          IsValuationUnit K (heHuSharp (heHuLemma59CTilde a k) hc : K) ∧
          defectOrder (K := K) (heHuSharp (heHuLemma59CTilde a k) hc) =
            (((2 * (ramificationIndex K : Int) +
                a.order ⟨2 * k + 3, by omega⟩ - 1 : Int) : ℚ) :
              WithTop ℚ) := by
    simpa only [heHuLemma59CTilde_eq_lemma58Prefix] using h58Raw
  rcases h58 with ⟨hc, hraw, hunit, hsharp⟩
  refine ⟨hc, ?_⟩
  let c := heHuLemma59C a k
  let cTilde := heHuLemma59CTilde a k
  let u := heHuSharp cTilde hc
  have hcapRaw := a.heHuLemma58_nextAlpha_gt (n := 2 * k + 1)
    (by omega) hodd hm hIntegral hI1 hAlpha hTrigger
  have hcap :
      (1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) <
        a.alphaValue ⟨2 * k + 3, by omega⟩ := by
    simpa only using hcapRaw
  have hsourceDefect : (heHuSharpData cTilde hc).sourceDefect =
      ((1 - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) := by
    have hs := (heHuSharpData cTilde hc).source_defectOrder
    rw [hraw] at hs
    exact WithTop.coe_eq_coe.mp hs.symm
  have hlt :
      ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ) <
        ((2 * ramificationIndex K : ℚ) : WithTop ℚ) := by
    have hs := (heHuSharpData cTilde hc).sourceDefect_lt_twoE
    rw [hsourceDefect] at hs
    exact_mod_cast hs
  have hboundary := a.heHuLemma59_boundaryOrder_gt_gapParity k hm
    hIntegral hTrigger
  let gap := a.order ⟨2 * k + 4, by omega⟩ -
    a.order ⟨2 * k + 3, by omega⟩
  have hcDiff : Even (ordUnit K c - gap) := by
    simpa only [c, gap] using a.heHuLemma59_c_order_sub_gap_even k hm hI1
  have hcParity : heHuLemma59Parity (K := K) c =
      if Even gap then 0 else 1 :=
    heHuLemma59Parity_eq_gapParity c gap hcDiff
  have hcuDiff : Even (ordUnit K (c * u) - gap) := by
    apply heHuLemma59_mul_unit_order_sub_gap_even c u gap hcDiff
    simpa only [u, cTilde] using hunit
  have hcuParity : heHuLemma59Parity (K := K) (c * u) =
      if Even gap then 0 else 1 :=
    heHuLemma59Parity_eq_gapParity (c * u) gap hcuDiff
  have hlastC : (heHuLemma59Target (K := K) c k).order
      ⟨2 * k + 2, by omega⟩ = if Even gap then 0 else 1 :=
    (heHuLemma59Target_lastOrder (K := K) c k).trans hcParity
  have hlastCU : (heHuLemma59Target (K := K) (c * u) k).order
      ⟨2 * k + 2, by omega⟩ = if Even gap then 0 else 1 :=
    (heHuLemma59Target_lastOrder (K := K) (c * u) k).trans hcuParity
  have hpreviousC := a.heHuLemma59_centralPreviousDefect_eq k hm
    hraw hcap hlt c
  have hpreviousCU := a.heHuLemma59_centralPreviousDefect_eq k hm
    hraw hcap hlt (c * u)
  have hrawC :
      ((a.heHuOddThreshold (2 * k + 3) (by omega) : ℚ) : WithTop ℚ) <
        defectOrder (K := K)
          ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
            (heHuLemma59Target (K := K) c k).prefixProduct (2 * k + 3)) := by
    dsimp only [c]
    rw [heHuLemma59_currentMixed_defectOrder_C]
    exact WithTop.coe_lt_top _
  have hcurrentC := a.heHuLemma59_centralCurrentDefect_gt k hm c
    (a.heHuOddThreshold (2 * k + 3) (by omega)) hrawC hAlphaNext
  have hsharpGt := a.heHuLemma59_sharpDefect_gt_threshold k hm u
    (by simpa only [gap] using hboundary) (by
      simpa only [u, cTilde] using hsharp)
  have hrawCU :
      ((a.heHuOddThreshold (2 * k + 3) (by omega) : ℚ) : WithTop ℚ) <
        defectOrder (K := K)
          ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
            (heHuLemma59Target (K := K) (c * u) k).prefixProduct
              (2 * k + 3)) := by
    dsimp only [c]
    rw [heHuLemma59_currentMixed_defectOrder_C_mul]
    exact hsharpGt
  have hcurrentCU := a.heHuLemma59_centralCurrentDefect_gt k hm (c * u)
    (a.heHuOddThreshold (2 * k + 3) (by omega)) hrawCU hAlphaNext
  constructor
  · apply a.heHuLemma59_defectTrigger_of_bounds k hm c
    · simpa only [gap] using hlastC
    · exact hboundary
    · simpa only [c] using hpreviousC
    · simpa only [c] using hcurrentC
  · apply a.heHuLemma59_defectTrigger_of_bounds k hm (c * u)
    · simpa only [gap] using hlastCU
    · exact hboundary
    · simpa only [c, u] using hpreviousCU
    · simpa only [c, u] using hcurrentCU

/-! ## Lemma 5.9(ii): the two representations cannot coexist -/

/-- The product of the two target determinants has the square class of the
sharp unit `u`. -/
theorem heHuLemma59_twoTargetProduct_sameSquareClass {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (u : Kˣ) :
    IsSquare
      (((heHuLemma59Target (K := K) (heHuLemma59C a k) k).prefixProduct
          (2 * k + 3) *
        (heHuLemma59Target (K := K) (heHuLemma59C a k * u) k).prefixProduct
          (2 * k + 3)) * u) := by
  let c := heHuLemma59C a k
  let sign : Kˣ := (-1) ^ (k + 1)
  let B₁ := (heHuLemma59Target (K := K) c k).prefixProduct (2 * k + 3)
  let B₂ := (heHuLemma59Target (K := K) (c * u) k).prefixProduct
    (2 * k + 3)
  have h₁ : IsSquare (B₁ * (sign * c)) := by
    simpa only [B₁, sign, c] using
      heHuLemma59Target_fullPrefix_signedParameterSquare (K := K) c k
  have h₂ : IsSquare (B₂ * (sign * (c * u))) := by
    simpa only [B₂, sign, c] using
      heHuLemma59Target_fullPrefix_signedParameterSquare (K := K) (c * u) k
  let middle := (sign * c) * (sign * (c * u))
  have hleft : IsSquare ((B₁ * B₂) * middle) := by
    dsimp only [middle]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h₁.mul h₂
  have hright : IsSquare (middle * u) := by
    refine ⟨sign * c * u, ?_⟩
    dsimp only [middle]
    ac_rfl
  have hresult := isSquare_mul_trans (B₁ * B₂) middle u hleft hright
  simpa only [B₁, B₂, c] using hresult

/-- The second Hilbert-symbol factor in the parity cycle has the square
class of `cTilde`. -/
theorem heHuLemma59_sourceTargetHead_sameSquareClass {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (u : Kˣ) :
    IsSquare
      (((-a.prefixProduct (2 * k + 4)) *
        (heHuLemma59Target (K := K) (heHuLemma59C a k * u) k).prefixProduct
          (2 * k + 2)) * heHuLemma59CTilde a k) := by
  let A := a.prefixProduct (2 * k + 4)
  let H := (heHuLemma59Target (K := K) (heHuLemma59C a k * u) k).prefixProduct
    (2 * k + 2)
  let sourceSign : Kˣ := (-1) ^ (k + 2)
  let targetSign : Kˣ := (-1) ^ (k + 1)
  have hsource : IsSquare (A * (sourceSign * heHuLemma59CTilde a k)) := by
    refine ⟨sourceSign * A, ?_⟩
    simp only [heHuLemma59CTilde]
    dsimp only [sourceSign, A]
    ac_rfl
  have htarget : IsSquare (H * targetSign) := by
    simpa only [H, targetSign] using
      heHuLemma59Target_hyperbolicPrefix_signedSquare (K := K)
        (heHuLemma59C a k * u) k
  have hproduct := hsource.mul htarget
  have hsign : sourceSign * targetSign = (-1 : Kˣ) := by
    simpa only [sourceSign, targetSign] using
      heHuLemma59_signedPowers_mul (K := K) k
  have heq :
      (A * (sourceSign * heHuLemma59CTilde a k)) * (H * targetSign) =
        ((-A) * H) * heHuLemma59CTilde a k := by
    rw [show (A * (sourceSign * heHuLemma59CTilde a k)) *
          (H * targetSign) =
        (sourceSign * targetSign) * (A * H) *
          heHuLemma59CTilde a k by ac_rfl, hsign]
    simp only [neg_mul, one_mul]
  rw [heq] at hproduct
  simpa only [A, H] using hproduct

/-- He--Hu, Lemma 5.9(ii).  For the sharp unit attached to `cTilde`, the
source prefix cannot represent both published first-column tests.  This is
the paper's simultaneous nonrepresentation assertion: it does not claim
that each test separately fails. -/
theorem heHu2022Lemma59ii {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (hm : 2 * k + 3 ≤ m)
    (hc : HeHuSharpDomain (heHuLemma59CTilde a k)) :
    ¬(
      DiagonalRepresents
          ((heHuLemma59Target (K := K) (heHuLemma59C a k) k).prefixValues
            (2 * k + 3) (by omega))
          (a.prefixValues (2 * k + 4) (by omega)) ∧
        DiagonalRepresents
          ((heHuLemma59Target (K := K)
              (heHuLemma59C a k *
                heHuSharp (heHuLemma59CTilde a k) hc) k).prefixValues
            (2 * k + 3) (by omega))
          (a.prefixValues (2 * k + 4) (by omega))) := by
  rintro ⟨hrepFirst, hrepSecond⟩
  let u := heHuSharp (heHuLemma59CTilde a k) hc
  let first := heHuLemma59Target (K := K) (heHuLemma59C a k) k
  let second := heHuLemma59Target (K := K) (heHuLemma59C a k * u) k
  let au := a.prefixValueUnits (2 * k + 4) (by omega)
  let bu := first.prefixValueUnits (2 * k + 3) (by omega)
  let cu := second.prefixValueUnits (2 * k + 3) (by omega)
  have hp : DiagonalRepresents
      (diagonalUnitCoefficients bu) (diagonalUnitCoefficients au) := by
    simpa only [bu, au, first, diagonalUnitCoefficients_prefixValueUnits]
      using hrepFirst
  have hr : DiagonalRepresents
      (diagonalUnitCoefficients cu) (diagonalUnitCoefficients au) := by
    simpa only [cu, au, second, u,
      diagonalUnitCoefficients_prefixValueUnits] using hrepSecond
  have hheads :
      second.prefixValueUnits (2 * k + 2) (by omega) =
        first.prefixValueUnits (2 * k + 2) (by omega) := by
    rw [show second.prefixValueUnits (2 * k + 2) (by omega) =
          heHuLemma45HyperbolicBONGValues (K := K) (k + 1) by
        simpa only [second] using
          heHuLemma59Target_hyperbolicValueUnits_eq (K := K)
            (heHuLemma59C a k * u) k]
    symm
    simpa only [first] using
      heHuLemma59Target_hyperbolicValueUnits_eq (K := K)
        (heHuLemma59C a k) k
  have htake :
      diagonalUnitTake cu (2 * k + 2) (by omega) =
        first.prefixValueUnits (2 * k + 2) (by omega) := by
    rw [show diagonalUnitTake cu (2 * k + 2) (by omega) =
          second.prefixValueUnits (2 * k + 2) (by omega) by
        simp only [cu, diagonalUnitTake_prefixValueUnits]]
    exact hheads
  have hprefix : DiagonalRepresents
      (first.prefixValues (2 * k + 2) (by omega))
      (first.prefixValues (2 * k + 3) (by omega)) := by
    have h := DiagonalRepresents.prefixOfLE
      (k := 2 * k + 2)
      (first.prefixValues (2 * k + 3) (by omega)) (by omega)
    convert h using 1
    · funext i
      rfl
  have hq : DiagonalRepresents
      (diagonalUnitCoefficients
        (diagonalUnitTake cu (2 * k + 2) (by omega)))
      (diagonalUnitCoefficients bu) := by
    rw [htake]
    simpa only [bu, diagonalUnitCoefficients_prefixValueUnits] using hprefix
  have hcycle := DiagonalRepresentationParityLaws.caseIII
    (i := 2 * k + 4) (j := 2 * k + 3) (k := 2 * k + 3)
    (l := 2 * k + 2) au bu cu (by omega) rfl (by omega)
  have hs := hcycle.all_triple_consequences.1 hp hq hr
  have hfirstClass : IsSquare
      ((diagonalUnitDeterminant bu * diagonalUnitDeterminant cu) * u) := by
    simpa only [bu, cu, first, second, u,
      diagonalUnitDeterminant_prefixValueUnits] using
        heHuLemma59_twoTargetProduct_sameSquareClass a k u
  have hsecondClass : IsSquare
      ((-diagonalUnitDeterminant au *
          diagonalUnitDeterminant
            (diagonalUnitTake cu (2 * k + 2) (by omega))) *
        heHuLemma59CTilde a k) := by
    simpa only [au, cu, second, diagonalUnitTake_prefixValueUnits,
      diagonalUnitDeterminant_prefixValueUnits] using
        heHuLemma59_sourceTargetHead_sameSquareClass a k u
  have htransport :
      hilbertSymbol K
          (diagonalUnitDeterminant bu * diagonalUnitDeterminant cu)
          (-diagonalUnitDeterminant au *
            diagonalUnitDeterminant
              (diagonalUnitTake cu (2 * k + 2) (by omega))) =
        hilbertSymbol K u (heHuLemma59CTilde a k) := by
    calc
      _ = hilbertSymbol K u
          (-diagonalUnitDeterminant au *
            diagonalUnitDeterminant
              (diagonalUnitTake cu (2 * k + 2) (by omega))) :=
        hilbertSymbol_eq_of_isSquare_mul_left hfirstClass
      _ = hilbertSymbol K u (heHuLemma59CTilde a k) :=
        hilbertSymbol_eq_of_isSquare_mul_right hsecondClass
  have hone : hilbertSymbol K u (heHuLemma59CTilde a k) = 1 := by
    rw [← htransport]
    exact hs
  have hminus : hilbertSymbol K u (heHuLemma59CTilde a k) = -1 := by
    simpa only [u] using (heHu2022Proposition32
      (heHuLemma59CTilde a k) hc).2.2
  rw [hminus] at hone
  norm_num at hone

/-- He--Hu, Lemma 5.9 in its complete published quantifier structure.
Both tests activate condition (iii'), but their representations cannot hold
simultaneously; consequently the revised central representation condition
fails for at least one of the two tests. -/
theorem heHu2022Lemma59 {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (hm : 2 * k + 3 ≤ m)
    (hIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (hI3 : a.HeHuI3E (2 * k + 2) (by omega))
    (hAlphaNext :
      (a.heHuOddThreshold (2 * k + 3) (by omega) : ℚ) <
        a.alphaValue ⟨2 * k + 4, by omega⟩)
    (hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1)
    (hTrigger : a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
      1 < a.order ⟨2 * k + 4, by omega⟩) :
    ∃ hc : HeHuSharpDomain (heHuLemma59CTilde a k),
      let u := heHuSharp (heHuLemma59CTilde a k) hc
      a.centralDefectTrigger
          (heHuLemma59Target (K := K) (heHuLemma59C a k) k)
          (heHuLemma59CentralIndex k hm) ∧
        a.centralDefectTrigger
          (heHuLemma59Target (K := K) (heHuLemma59C a k * u) k)
          (heHuLemma59CentralIndex k hm) ∧
        ¬(
          DiagonalRepresents
              ((heHuLemma59Target (K := K)
                  (heHuLemma59C a k) k).prefixValues
                (2 * k + 3) (by omega))
              (a.prefixValues (2 * k + 4) (by omega)) ∧
            DiagonalRepresents
              ((heHuLemma59Target (K := K)
                  (heHuLemma59C a k * u) k).prefixValues
                (2 * k + 3) (by omega))
              (a.prefixValues (2 * k + 4) (by omega))) ∧
        (¬a.CentralRepresentationConditionsPrime
            (heHuLemma59Target (K := K) (heHuLemma59C a k) k) ∨
          ¬a.CentralRepresentationConditionsPrime
            (heHuLemma59Target (K := K) (heHuLemma59C a k * u) k)) := by
  rcases a.heHu2022Lemma59i k hm hIntegral hI1 hI2 hI3 hAlphaNext
      hAlpha hTrigger with ⟨hc, hfirstTrigger, hsecondTrigger⟩
  let u := heHuSharp (heHuLemma59CTilde a k) hc
  have hnot := a.heHu2022Lemma59ii k hm hc
  refine ⟨hc, hfirstTrigger, hsecondTrigger, hnot, ?_⟩
  by_cases hPrimeFirst : a.CentralRepresentationConditionsPrime
      (heHuLemma59Target (K := K) (heHuLemma59C a k) k)
  · right
    intro hPrimeSecond
    apply hnot
    constructor
    · apply a.centralRepresentationConditionsPrime_represents_castLengths
        (heHuLemma59Target (K := K) (heHuLemma59C a k) k)
        hPrimeFirst (heHuLemma59CentralIndex k hm) hfirstTrigger
      · simp only [heHuLemma59CentralIndex]
        omega
      · rfl
    · apply a.centralRepresentationConditionsPrime_represents_castLengths
        (heHuLemma59Target (K := K) (heHuLemma59C a k * u) k)
        hPrimeSecond (heHuLemma59CentralIndex k hm) hsecondTrigger
      · simp only [heHuLemma59CentralIndex]
        omega
      · rfl
  · exact Or.inl hPrimeFirst

end BONG.GoodBONG

end Bong
