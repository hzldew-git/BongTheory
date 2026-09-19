/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma55

/-!
# He (2024), Lemma 5.6

The targets below are literal exact good-BONG realizations of the publisher's
classic row `C₁ⁿ(c)=H₀^((n-1)/2) perp <c>`.  The parameter is first replaced by
the order-`0/1` representative of its square class.  This replacement is an
isometry of the displayed diagonal space, but unlike the He--Hu maximal model
it leaves every hyperbolic coefficient at order zero.  Keeping those two
models separate is essential for the first capped defect in part (i).
-/

namespace Bong

open Dyadic AlternatingEndpointTower

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-! ## The literal classic first-column tests -/

/-- The exact classic test `C₁^(2k+3)(x)`, with the last coefficient chosen
in the square class of `x` and of order `0` or `1`. -/
noncomputable def he2022ClassicLemma56Target (x : Kˣ) (k : Nat) :=
  heClassicOddC1GoodBONG (K := K) k
    (heHuLemma59NormalizedParameter (K := K) x)
    (by
      rw [heHuLemma59NormalizedParameter_order]
      exact heHuLemma59Parity_nonneg x)

/-- The order profile in Lemma 2.9(ii): all hyperbolic entries have order
zero, and the last entry has the parity-normalized order of `x`. -/
theorem he2022ClassicLemma56Target_order (x : Kˣ) (k : Nat)
    (i : Fin (2 * k + 3)) :
    (he2022ClassicLemma56Target (K := K) x k).order i =
      if i.val = 2 * k + 2 then heHuLemma59Parity (K := K) x else 0 := by
  simp only [he2022ClassicLemma56Target, heClassicOddC1GoodBONG,
    heHuExactGoodBONG_order]
  rw [heClassicOddC1_order, heHuLemma59NormalizedParameter_order]

/-- At full rank the exact good BONG has precisely the displayed classic
coefficient row. -/
theorem he2022ClassicLemma56Target_fullPrefixValueUnits
    (x : Kˣ) (k : Nat) :
    let b := he2022ClassicLemma56Target (K := K) x k
    b.prefixValueUnits (2 * k + 3) le_rfl =
      heClassicOddC1 (K := K) k
        (heHuLemma59NormalizedParameter (K := K) x) := by
  dsimp only
  funext i
  change (he2022ClassicLemma56Target (K := K) x k).valueUnit i = _
  rw [he2022ClassicLemma56Target, heClassicOddC1GoodBONG,
    heHuExactGoodBONG_valueUnit]

/-- The first `2k+2` values are literally the standard hyperbolic tower. -/
theorem he2022ClassicLemma56Target_hyperbolicValueUnits
    (x : Kˣ) (k : Nat) :
    (he2022ClassicLemma56Target (K := K) x k).prefixValueUnits
        (2 * k + 2) (by omega) =
      standardHyperbolicEndpointTower (K := K) (k + 1) := by
  funext i
  change (he2022ClassicLemma56Target (K := K) x k).valueUnit
      ⟨i.val, by omega⟩ = _
  rw [he2022ClassicLemma56Target, heClassicOddC1GoodBONG,
    heHuExactGoodBONG_valueUnit]
  have hi :
      (⟨i.val, by omega⟩ : Fin (2 * k + 3)) = i.castSucc := Fin.ext rfl
  rw [hi, heClassicOddC1_head, heClassicScaledHyperbolicTower_zero]

/-- The hyperbolic prefix has exact signed determinant `(-1)^(k+1)`. -/
theorem he2022ClassicLemma56Target_prefixProduct_hyperbolic
    (x : Kˣ) (k : Nat) :
    (he2022ClassicLemma56Target (K := K) x k).prefixProduct
        (2 * k + 2) = (-1 : Kˣ) ^ (k + 1) := by
  rw [← (he2022ClassicLemma56Target (K := K) x k)
      |>.diagonalUnitDeterminant_prefixValueUnits (2 * k + 2) (by omega),
    he2022ClassicLemma56Target_hyperbolicValueUnits,
    diagonalUnitDeterminant_standardHyperbolicEndpointTower]

/-- The complete determinant is the normalized parameter times the standard
odd-rank sign. -/
theorem he2022ClassicLemma56Target_prefixProduct_full
    (x : Kˣ) (k : Nat) :
    (he2022ClassicLemma56Target (K := K) x k).prefixProduct
        (2 * k + 3) =
      (-1 : Kˣ) ^ (k + 1) *
        heHuLemma59NormalizedParameter (K := K) x := by
  rw [← (he2022ClassicLemma56Target (K := K) x k)
      |>.diagonalUnitDeterminant_prefixValueUnits (2 * k + 3) le_rfl,
    he2022ClassicLemma56Target_fullPrefixValueUnits,
    heClassicOddC1_eq_heHuOddFirst,
    diagonalUnitDeterminant_heHuOddFirst]

/-- The full determinant has the square class of the parameter with the
standard odd-rank sign. -/
theorem he2022ClassicLemma56Target_fullPrefix_signedParameterSquare
    (x : Kˣ) (k : Nat) :
    IsSquare
      ((he2022ClassicLemma56Target (K := K) x k).prefixProduct
          (2 * k + 3) * (((-1 : Kˣ) ^ (k + 1)) * x)) := by
  rw [he2022ClassicLemma56Target_prefixProduct_full]
  have hnormalized := heHuLemma59_normalized_sameSquareClass (K := K) x
  have heq :
      (((-1 : Kˣ) ^ (k + 1) *
          heHuLemma59NormalizedParameter (K := K) x) *
        (((-1 : Kˣ) ^ (k + 1)) * x)) =
      x * heHuLemma59NormalizedParameter (K := K) x := by
    have hsign :
        ((-1 : Kˣ) ^ (k + 1)) * ((-1 : Kˣ) ^ (k + 1)) = 1 := by
      rw [← pow_add]
      rw [show k + 1 + (k + 1) = 2 * (k + 1) by omega, pow_mul]
      norm_num
    calc
      (((-1 : Kˣ) ^ (k + 1) *
          heHuLemma59NormalizedParameter (K := K) x) *
        (((-1 : Kˣ) ^ (k + 1)) * x)) =
          (((-1 : Kˣ) ^ (k + 1)) * ((-1 : Kˣ) ^ (k + 1))) *
            (x * heHuLemma59NormalizedParameter (K := K) x) := by ac_rfl
      _ = x * heHuLemma59NormalizedParameter (K := K) x := by
        rw [hsign, one_mul]
  rw [heq]
  exact hnormalized

/-- The last order is the parity-normalized order of the requested square
class. -/
theorem he2022ClassicLemma56Target_lastOrder (x : Kˣ) (k : Nat) :
    (he2022ClassicLemma56Target (K := K) x k).order
        ⟨2 * k + 2, by omega⟩ = heHuLemma59Parity (K := K) x := by
  rw [he2022ClassicLemma56Target_order, if_pos rfl]

/-- The alpha cap immediately before the unary tail is at least one.  This
is exactly the use of Lemma 2.9(ii) in the publisher's proof. -/
theorem he2022ClassicLemma56Target_lastInternalAlpha_one_le
    (x : Kˣ) (k : Nat) :
    (1 : ℚ) ≤
      (he2022ClassicLemma56Target (K := K) x k).alphaValue
        ⟨2 * k + 1, by omega⟩ := by
  let b := he2022ClassicLemma56Target (K := K) x k
  apply b.one_le_alphaValue_of_ne_zero
  intro hzero
  let p : Fin (2 * k + 2) := ⟨2 * k + 1, by omega⟩
  have hgap := (b.he2022ClassicProposition23 p).alphaZero.mp (by
    simpa only [p] using hzero)
  unfold orderGap at hgap
  have hpcast : p.castSucc =
      (⟨2 * k + 1, by omega⟩ : Fin (2 * k + 3)) := Fin.ext rfl
  have hpsucc : p.succ =
      (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 3)) := Fin.ext rfl
  have hleft : b.order p.castSucc = 0 := by
    rw [hpcast]
    change (he2022ClassicLemma56Target (K := K) x k).order
      ⟨2 * k + 1, by omega⟩ = 0
    rw [he2022ClassicLemma56Target_order]
    have hne : 2 * k + 1 ≠ 2 * k + 2 := by omega
    exact if_neg hne
  have hright : b.order p.succ =
        heHuLemma59Parity (K := K) x := by
    rw [hpsucc]
    change (he2022ClassicLemma56Target (K := K) x k).order
      ⟨2 * k + 2, by omega⟩ = _
    rw [he2022ClassicLemma56Target_order]
    rw [if_pos (by rfl)]
  rw [hleft, hright] at hgap
  have hnonneg := heHuLemma59Parity_nonneg (K := K) x
  have hepos := ramificationIndex_pos (K := K)
  omega

/-- The self capped defect of the hyperbolic prefix is at least one. -/
theorem he2022ClassicLemma56Target_prefixDefect_one_le
    (x : Kˣ) (k : Nat) :
    (1 : WithTop ℚ) ≤
      (he2022ClassicLemma56Target (K := K) x k).truncatedPrefixDefect
        (he2022ClassicLemma56Target (K := K) x k)
        ((-1) ^ (k + 1)) 0 (2 * k + 2) := by
  let b := he2022ClassicLemma56Target (K := K) x k
  unfold truncatedPrefixDefect
  rw [b.prefixAlphaCap_zero,
    b.prefixAlphaCap_of_internal (by omega) (by omega)]
  have hindex :
      (⟨2 * k + 2 - 1, by omega⟩ : Fin (2 * k + 2)) =
        ⟨2 * k + 1, by omega⟩ := by
    apply Fin.ext
    change 2 * k + 2 - 1 = 2 * k + 1
    omega
  rw [hindex, he2022ClassicLemma56Target_prefixProduct_hyperbolic]
  have hraw : defectOrder (K := K)
      (((-1 : Kˣ) ^ (k + 1)) *
        ((-1 : Kˣ) ^ (k + 1))) = ⊤ := by
    apply defectOrder_eq_top_of_isSquare
    exact ⟨(-1 : Kˣ) ^ (k + 1), rfl⟩
  rw [GoodBONG.prefixProduct, BONG.prefixProduct_zero, mul_one, hraw]
  simp only [min_top_left]
  exact_mod_cast he2022ClassicLemma56Target_lastInternalAlpha_one_le
    (K := K) x k

/-- Under `J1'_E(N-1)`, the valuation of the first `N=2*k+3`
coefficients is even (indeed, it is zero). -/
theorem he2022ClassicLemma56_sourceInitialPrefixOrder_even
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 <= m)
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega)) :
    Even (ordUnit K (a.prefixProduct (2 * k + 3))) := by
  have hEntries (j : Nat) (hj : j < 2 * k + 3) :
      Even (a.orderSequence.entryOrZero j) := by
    let jf : Fin (m + 3) := ⟨j, by omega⟩
    rw [a.orderSequence_entryOrZero_eq_order jf]
    have hZero := hJ1.1 ⟨j, by omega⟩
    have hIndex : (⟨j, by omega⟩ : Fin (m + 3)) = jf := Fin.ext rfl
    rw [hIndex] at hZero
    rw [hZero]
    exact Even.zero
  rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
    (2 * k + 3) (by omega)]
  exact a.orderSequence.prefixSum_even_of_entries_even (2 * k + 3) hEntries

/-- In the classic case, the signed determinant
`c=(-1)^((N+1)/2)a_(1,N+2)` has the parity of
`R_(N+2)-R_(N+1)`. -/
theorem he2022ClassicLemma56_c_order_sub_gap_even
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 <= m)
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega)) :
    Even (ordUnit K (heHuLemma59C a k) -
      (a.order ⟨2 * k + 4, by omega⟩ -
        a.order ⟨2 * k + 3, by omega⟩)) := by
  have hPrefix :=
    a.he2022ClassicLemma56_sourceInitialPrefixOrder_even (k := k) hm hJ1
  rcases hPrefix with ⟨t, ht⟩
  have hProduct :
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
          a.toBONG.prefixProduct_succ (2 * k + 4) (by omega), ordUnit_mul]
        rfl
      _ = ordUnit K (a.prefixProduct (2 * k + 3)) +
            a.order ⟨2 * k + 3, by omega⟩ +
            a.order ⟨2 * k + 4, by omega⟩ := by
        have hStep :
            ordUnit K (a.prefixProduct (2 * k + 4)) =
              ordUnit K (a.prefixProduct (2 * k + 3)) +
                a.order ⟨2 * k + 3, by omega⟩ := by
          unfold GoodBONG.prefixProduct
          rw [show 2 * k + 4 = (2 * k + 3) + 1 by omega,
            a.toBONG.prefixProduct_succ (2 * k + 3) (by omega), ordUnit_mul]
          rfl
        rw [hStep]
  have hCOrder :
      ordUnit K (heHuLemma59C a k) =
        ordUnit K (a.prefixProduct (2 * k + 5)) := by
    unfold heHuLemma59C
    rw [ordUnit_mul, ordUnit_pow, ordUnit_neg_one_eq_zero (K := K)]
    simp only [mul_zero, zero_add]
  refine ⟨t + a.order ⟨2 * k + 3, by omega⟩, ?_⟩
  rw [hCOrder, hProduct, ht]
  ring

/-! ## The two capped defects at the terminal central index -/

/-- For a classic `C₁` target, the first capped defect is exactly the
source value `1-R_(n+1)`.  The proof uses the literal order-zero
hyperbolic prefix; this is the step that distinguishes Lemma 5.6 from the
He--Hu Lemma 5.9 model. -/
theorem he2022ClassicLemma56_centralPreviousDefect_eq
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m) (x : Kˣ)
    (hraw : defectOrder (K := K) (heHuLemma59CTilde a k) =
      ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
        WithTop ℚ))
    (hcap : (1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) <
      a.alphaValue ⟨2 * k + 3, by omega⟩)
    (hR : a.order ⟨2 * k + 3, by omega⟩ = 0 ∨
      a.order ⟨2 * k + 3, by omega⟩ = 1) :
    a.centralPreviousDefect (he2022ClassicLemma56Target (K := K) x k)
        (heHuLemma59CentralIndex k hm) =
      ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
        WithTop ℚ) := by
  let b := he2022ClassicLemma56Target (K := K) x k
  let D : WithTop ℚ :=
    ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
      WithTop ℚ)
  have hDleOne : D ≤ (1 : WithTop ℚ) := by
    rcases hR with hzero | hone
    · simp only [D, hzero]
      norm_num
    · simp only [D, hone]
      norm_num
  have hsourceCap : D ≤ a.prefixAlphaCap (2 * k + 4) := by
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
    have hindex :
        (⟨2 * k + 4 - 1, by omega⟩ : Fin (m + 2)) =
          ⟨2 * k + 3, by omega⟩ := by
      apply Fin.ext
      change 2 * k + 4 - 1 = 2 * k + 3
      omega
    rw [hindex]
    change ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
      WithTop ℚ) ≤
        (a.alphaValue ⟨2 * k + 3, by omega⟩ : WithTop ℚ)
    exact_mod_cast hcap.le
  have htargetCap : D ≤ b.prefixAlphaCap (2 * k + 2) := by
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
    have hindex :
        (⟨2 * k + 2 - 1, by omega⟩ : Fin (2 * k + 2)) =
          ⟨2 * k + 1, by omega⟩ := by
      apply Fin.ext
      change 2 * k + 2 - 1 = 2 * k + 1
      omega
    rw [hindex]
    exact hDleOne.trans (by
      exact_mod_cast he2022ClassicLemma56Target_lastInternalAlpha_one_le
        (K := K) x k)
  have hproduct :
      (-1 : Kˣ) * a.prefixProduct (2 * k + 4) *
          b.prefixProduct (2 * k + 2) = heHuLemma59CTilde a k := by
    rw [show b.prefixProduct (2 * k + 2) = (-1 : Kˣ) ^ (k + 1) by
      simpa only [b] using
        he2022ClassicLemma56Target_prefixProduct_hyperbolic
          (K := K) x k]
    unfold heHuLemma59CTilde
    rw [show (-1 : Kˣ) ^ (k + 2) =
        (-1 : Kˣ) * (-1 : Kˣ) ^ (k + 1) by
      rw [show k + 2 = 1 + (k + 1) by omega, pow_add]
      simp]
    ac_rfl
  unfold centralPreviousDefect truncatedPrefixDefect
  simp only [heHuLemma59CentralIndex]
  have hsub : 2 * k + 4 - 2 = 2 * k + 2 := by omega
  rw [hsub, hproduct, hraw]
  change min D (min (a.prefixAlphaCap (2 * k + 4))
    (b.prefixAlphaCap (2 * k + 2))) = D
  rw [min_eq_left (le_min hsourceCap htargetCap)]

/-- The raw second mixed product has square class `c*x`, where `c` is the
signed source determinant through `n+2`. -/
theorem he2022ClassicLemma56_currentMixed_sameSquareClass
    {m : Nat} (a : GoodBONG q L (m + 3)) (k : Nat) (x : Kˣ) :
    IsSquare
      (((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
          (he2022ClassicLemma56Target (K := K) x k).prefixProduct
            (2 * k + 3)) * (heHuLemma59C a k * x)) := by
  let A := a.prefixProduct (2 * k + 5)
  let normalized := heHuLemma59NormalizedParameter (K := K) x
  let sourceSign : Kˣ := (-1) ^ (k + 2)
  let targetSign : Kˣ := (-1) ^ (k + 1)
  have hA : IsSquare (A * A) := ⟨A, rfl⟩
  have hnormalized : IsSquare (x * normalized) := by
    simpa only [normalized] using
      heHuLemma59_normalized_sameSquareClass (K := K) x
  have hsign : sourceSign * targetSign = (-1 : Kˣ) := by
    simpa only [sourceSign, targetSign] using
      heHuLemma59_signedPowers_mul (K := K) k
  have heq :
      (((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
          (he2022ClassicLemma56Target (K := K) x k).prefixProduct
            (2 * k + 3)) * (heHuLemma59C a k * x)) =
        (A * A) * (x * normalized) := by
    rw [he2022ClassicLemma56Target_prefixProduct_full]
    simp only [heHuLemma59C]
    change ((-1 : Kˣ) * A * (targetSign * normalized)) *
      ((sourceSign * A) * x) = (A * A) * (x * normalized)
    have hsign' : (-1 : Kˣ) * targetSign * sourceSign = 1 := by
      rw [mul_assoc, mul_comm targetSign sourceSign, hsign]
      norm_num
    calc
      ((-1 : Kˣ) * A * (targetSign * normalized)) *
          ((sourceSign * A) * x) =
        ((-1 : Kˣ) * targetSign * sourceSign) *
          (A * A) * (x * normalized) := by ac_rfl
      _ = (A * A) * (x * normalized) := by rw [hsign']; simp
  rw [heq]
  exact hA.mul hnormalized

/-- Defect-order form of the preceding square-class calculation. -/
theorem he2022ClassicLemma56_currentMixed_defectOrder_eq
    {m : Nat} (a : GoodBONG q L (m + 3)) (k : Nat) (x : Kˣ) :
    defectOrder (K := K)
        ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
          (he2022ClassicLemma56Target (K := K) x k).prefixProduct
            (2 * k + 3)) =
      defectOrder (K := K) (heHuLemma59C a k * x) :=
  heHuLemma45_defectOrder_eq_of_mul_isSquare _ _
    (he2022ClassicLemma56_currentMixed_sameSquareClass a k x)

/-- At the terminal index, the second capped defect is the minimum of the
raw field defect and the source alpha cap `alpha_(n+2)`. -/
theorem he2022ClassicLemma56_centralCurrentDefect_eq_min
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m) (x : Kˣ) :
    a.centralCurrentDefect (he2022ClassicLemma56Target (K := K) x k)
        (heHuLemma59CentralIndex k hm) =
      min
        (defectOrder (K := K)
          ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
            (he2022ClassicLemma56Target (K := K) x k).prefixProduct
              (2 * k + 3)))
        (a.alphaValue ⟨2 * k + 4, by omega⟩ : WithTop ℚ) := by
  let b := he2022ClassicLemma56Target (K := K) x k
  have hsourceCap : a.prefixAlphaCap (2 * k + 5) =
      (a.alphaValue ⟨2 * k + 4, by omega⟩ : WithTop ℚ) := by
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
    congr 2
  have htargetCap : b.prefixAlphaCap (2 * k + 3) = ⊤ := by
    simpa only [b] using b.prefixAlphaCap_last
  unfold centralCurrentDefect truncatedPrefixDefect
  simp only [heHuLemma59CentralIndex]
  have hadd : 2 * k + 4 + 1 = 2 * k + 5 := by omega
  have hsub : 2 * k + 4 - 1 = 2 * k + 3 := by omega
  rw [hadd, hsub, hsourceCap, htargetCap, min_top_right]

/-- Raw-defect and alpha-cap lower bounds give equation (5.4) for either
classic test lattice. -/
theorem he2022ClassicLemma56_centralCurrentDefect_gt
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m) (x : Kˣ) (G : Int)
    (hraw : ((G : ℚ) : WithTop ℚ) <
      defectOrder (K := K)
        ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
          (he2022ClassicLemma56Target (K := K) x k).prefixProduct
            (2 * k + 3)))
    (hcap : (G : ℚ) < a.alphaValue ⟨2 * k + 4, by omega⟩) :
    ((G : ℚ) : WithTop ℚ) <
      a.centralCurrentDefect (he2022ClassicLemma56Target (K := K) x k)
        (heHuLemma59CentralIndex k hm) := by
  rw [a.he2022ClassicLemma56_centralCurrentDefect_eq_min hm x]
  apply lt_min hraw
  exact_mod_cast hcap

/-- The two numerical inequalities of Lemma 5.6(i), packaged as the exact
publisher trigger in Theorem 2.5(iii). -/
theorem he2022ClassicLemma56_defectTrigger_of_bounds
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m) (x : Kˣ)
    (hlast : (he2022ClassicLemma56Target (K := K) x k).order
        ⟨2 * k + 2, by omega⟩ =
      (if Even (a.order ⟨2 * k + 4, by omega⟩ -
          a.order ⟨2 * k + 3, by omega⟩) then 0 else 1))
    (hboundary :
      (if Even (a.order ⟨2 * k + 4, by omega⟩ -
          a.order ⟨2 * k + 3, by omega⟩) then 0 else 1) <
        a.order ⟨2 * k + 4, by omega⟩)
    (hprevious :
      a.centralPreviousDefect (he2022ClassicLemma56Target (K := K) x k)
          (heHuLemma59CentralIndex k hm) =
        ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ))
    (hcurrent :
      ((a.heHuOddThreshold (2 * k + 3) (by omega) : ℚ) : WithTop ℚ) <
        a.centralCurrentDefect (he2022ClassicLemma56Target (K := K) x k)
          (heHuLemma59CentralIndex k hm)) :
    a.centralDefectTrigger (he2022ClassicLemma56Target (K := K) x k)
      (heHuLemma59CentralIndex k hm) := by
  let b := he2022ClassicLemma56Target (K := K) x k
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
              a.centralCurrentDefect
                (he2022ClassicLemma56Target (K := K) x k)
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

/-- Lemma 5.6(i): both first-column tests activate the numerical trigger in
Theorem 2.5(iii). -/
theorem he2022ClassicLemma56i
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 <= m)
    (hClassic : Lattice.IsClassicIntegral q L)
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * k + 2) (by omega))
    (hAlphaNext :
      (a.heClassicOddThreshold (2 * k + 3) (by omega) : ℚ) <
        a.alphaValue ⟨2 * k + 4, by omega⟩)
    (hTrigger : a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
      1 < a.order ⟨2 * k + 4, by omega⟩) :
    let cTilde := heHuLemma59CTilde a k
    ∃ hc : HeHuSharpDomain cTilde,
      let u := heHuSharp cTilde hc
      a.centralDefectTrigger
          (he2022ClassicLemma56Target (K := K) (heHuLemma59C a k) k)
          (heHuLemma59CentralIndex k hm) ∧
        a.centralDefectTrigger
          (he2022ClassicLemma56Target
            (K := K) (heHuLemma59C a k * u) k)
          (heHuLemma59CentralIndex k hm) := by
  dsimp only
  have h55 := a.he2022ClassicLemma55 (k := k) hm hClassic hJ1 hJ2 hTrigger
  rcases h55 with ⟨hc, hRaw, hUnit, hSharp⟩
  refine ⟨hc, ?_⟩
  let c := heHuLemma59C a k
  let cTilde := heHuLemma59CTilde a k
  let u := heHuSharp cTilde hc
  have hCap := a.he2022ClassicLemma55_nextAlpha_gt (k := k) hm hClassic
    hJ1 hJ2 hTrigger
  have hRNonnegative : 0 ≤ a.order ⟨2 * k + 3, by omega⟩ := by
    have htwo := a.orderSequence.twoStep (2 * k + 1) (by omega)
    change a.order ⟨2 * k + 1, by omega⟩ ≤
      a.order ⟨2 * k + 3, by omega⟩ at htwo
    rw [hJ1.1 ⟨2 * k + 1, by omega⟩] at htwo
    exact htwo
  have hRAtMostOne : a.order ⟨2 * k + 3, by omega⟩ ≤ 1 := by
    have hnonnegative := defectOrder_nonneg (K := K) cTilde
    rw [show defectOrder (K := K) cTilde =
        ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ) by simpa only [cTilde] using hRaw] at hnonnegative
    norm_cast at hnonnegative
    omega
  have hRCases : a.order ⟨2 * k + 3, by omega⟩ = 0 ∨
      a.order ⟨2 * k + 3, by omega⟩ = 1 := by omega
  have hBoundary := a.heHuLemma59_boundaryOrder_gt_gapParity k hm
    hClassic.isIntegral hTrigger
  let gap := a.order ⟨2 * k + 4, by omega⟩ -
    a.order ⟨2 * k + 3, by omega⟩
  have hCDiff : Even (ordUnit K c - gap) := by
    simpa only [c, gap] using
      a.he2022ClassicLemma56_c_order_sub_gap_even (k := k) hm hJ1
  have hCParity : heHuLemma59Parity (K := K) c =
      if Even gap then 0 else 1 :=
    heHuLemma59Parity_eq_gapParity c gap hCDiff
  have hCUDiff : Even (ordUnit K (c * u) - gap) := by
    apply heHuLemma59_mul_unit_order_sub_gap_even c u gap hCDiff
    simpa only [u, cTilde] using hUnit
  have hCUParity : heHuLemma59Parity (K := K) (c * u) =
      if Even gap then 0 else 1 :=
    heHuLemma59Parity_eq_gapParity (c * u) gap hCUDiff
  have hLastC : (he2022ClassicLemma56Target (K := K) c k).order
      ⟨2 * k + 2, by omega⟩ = if Even gap then 0 else 1 :=
    (he2022ClassicLemma56Target_lastOrder (K := K) c k).trans hCParity
  have hLastCU : (he2022ClassicLemma56Target (K := K) (c * u) k).order
      ⟨2 * k + 2, by omega⟩ = if Even gap then 0 else 1 :=
    (he2022ClassicLemma56Target_lastOrder (K := K) (c * u) k).trans
      hCUParity
  have hPreviousC := a.he2022ClassicLemma56_centralPreviousDefect_eq
    hm c hRaw hCap hRCases
  have hPreviousCU := a.he2022ClassicLemma56_centralPreviousDefect_eq
    hm (c * u) hRaw hCap hRCases
  have hRawC :
      ((a.heHuOddThreshold (2 * k + 3) (by omega) : ℚ) : WithTop ℚ) <
        defectOrder (K := K)
          ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
            (he2022ClassicLemma56Target (K := K) c k).prefixProduct
              (2 * k + 3)) := by
    rw [he2022ClassicLemma56_currentMixed_defectOrder_eq]
    dsimp only [c]
    rw [show defectOrder (K := K)
        (heHuLemma59C a k * heHuLemma59C a k) = ⊤ by
      apply defectOrder_eq_top_of_isSquare
      exact ⟨heHuLemma59C a k, rfl⟩]
    exact WithTop.coe_lt_top _
  have hCurrentC := a.he2022ClassicLemma56_centralCurrentDefect_gt hm c
    (a.heHuOddThreshold (2 * k + 3) (by omega)) hRawC (by
      simpa only [heClassicOddThreshold] using hAlphaNext)
  have hSharpGt := a.heHuLemma59_sharpDefect_gt_threshold k hm u
    (by simpa only [gap] using hBoundary) (by
      simpa only [u, cTilde] using hSharp)
  have hRawCU :
      ((a.heHuOddThreshold (2 * k + 3) (by omega) : ℚ) : WithTop ℚ) <
        defectOrder (K := K)
          ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
            (he2022ClassicLemma56Target (K := K) (c * u) k).prefixProduct
              (2 * k + 3)) := by
    rw [he2022ClassicLemma56_currentMixed_defectOrder_eq]
    have heq : defectOrder (K := K) (heHuLemma59C a k * (c * u)) =
        defectOrder (K := K) u := by
      apply heHuLemma45_defectOrder_eq_of_mul_isSquare
      refine ⟨heHuLemma59C a k * u, ?_⟩
      dsimp only [c]
      ac_rfl
    rw [heq]
    exact hSharpGt
  have hCurrentCU := a.he2022ClassicLemma56_centralCurrentDefect_gt hm (c * u)
    (a.heHuOddThreshold (2 * k + 3) (by omega)) hRawCU (by
      simpa only [heClassicOddThreshold] using hAlphaNext)
  constructor
  · apply a.he2022ClassicLemma56_defectTrigger_of_bounds hm c
    · simpa only [gap] using hLastC
    · exact hBoundary
    · simpa only [c] using hPreviousC
    · simpa only [c] using hCurrentC
  · apply a.he2022ClassicLemma56_defectTrigger_of_bounds hm (c * u)
    · simpa only [gap] using hLastCU
    · exact hBoundary
    · simpa only [c, u] using hPreviousCU
    · simpa only [c, u] using hCurrentCU

/-- The product of the two classic target determinants has square class
equal to the sharp unit `u`. -/
theorem he2022ClassicLemma56_twoTargetProduct_sameSquareClass
    {m : Nat} (a : GoodBONG q L (m + 3)) (k : Nat) (u : Kˣ) :
    IsSquare
      (((he2022ClassicLemma56Target (K := K) (heHuLemma59C a k) k).prefixProduct
          (2 * k + 3) *
        (he2022ClassicLemma56Target (K := K)
          (heHuLemma59C a k * u) k).prefixProduct (2 * k + 3)) * u) := by
  let c := heHuLemma59C a k
  let sign : Kˣ := (-1) ^ (k + 1)
  let B₁ := (he2022ClassicLemma56Target (K := K) c k).prefixProduct
    (2 * k + 3)
  let B₂ := (he2022ClassicLemma56Target (K := K) (c * u) k).prefixProduct
    (2 * k + 3)
  have h₁ : IsSquare (B₁ * (sign * c)) := by
    simpa only [B₁, sign, c] using
      he2022ClassicLemma56Target_fullPrefix_signedParameterSquare
        (K := K) c k
  have h₂ : IsSquare (B₂ * (sign * (c * u))) := by
    simpa only [B₂, sign, c] using
      he2022ClassicLemma56Target_fullPrefix_signedParameterSquare
        (K := K) (c * u) k
  let middle := (sign * c) * (sign * (c * u))
  have hleft : IsSquare ((B₁ * B₂) * middle) := by
    let X : Kˣ := sign * c
    let Y : Kˣ := sign * (c * u)
    have hmul : IsSquare ((B₁ * X) * (B₂ * Y)) := by
      simpa only [X, Y] using h₁.mul h₂
    change IsSquare ((B₁ * B₂) * (X * Y))
    have hreorder :
        (B₁ * B₂) * (X * Y) = (B₁ * X) * (B₂ * Y) := by
      calc
        (B₁ * B₂) * (X * Y) = B₁ * (B₂ * (X * Y)) :=
          mul_assoc B₁ B₂ (X * Y)
        _ = B₁ * (X * (B₂ * Y)) := by
          congr 1
          rw [← mul_assoc B₂ X Y, mul_comm B₂ X,
            mul_assoc X B₂ Y]
        _ = (B₁ * X) * (B₂ * Y) :=
          (mul_assoc B₁ X (B₂ * Y)).symm
    rw [hreorder]
    exact hmul
  have hright : IsSquare (middle * u) := by
    refine ⟨sign * c * u, ?_⟩
    dsimp only [middle]
    ac_rfl
  have hresult := isSquare_mul_trans (B₁ * B₂) middle u hleft hright
  simpa only [B₁, B₂, c] using hresult

/-- The source determinant and the common classic hyperbolic head have
square product.  This is the second Hilbert-symbol transport in part (ii). -/
theorem he2022ClassicLemma56_sourceTargetHead_sameSquareClass
    {m : Nat} (a : GoodBONG q L (m + 3)) (k : Nat) (u : Kˣ) :
    IsSquare
      (((-a.prefixProduct (2 * k + 4)) *
        (he2022ClassicLemma56Target (K := K)
          (heHuLemma59C a k * u) k).prefixProduct (2 * k + 2)) *
        heHuLemma59CTilde a k) := by
  let A := a.prefixProduct (2 * k + 4)
  let sourceSign : Kˣ := (-1) ^ (k + 2)
  let targetSign : Kˣ := (-1) ^ (k + 1)
  have hhead :
      (he2022ClassicLemma56Target (K := K)
          (heHuLemma59C a k * u) k).prefixProduct (2 * k + 2) =
        targetSign := by
    simpa only [targetSign] using
      he2022ClassicLemma56Target_prefixProduct_hyperbolic
        (K := K) (heHuLemma59C a k * u) k
  have hsign : sourceSign * targetSign = (-1 : Kˣ) := by
    simpa only [sourceSign, targetSign] using
      heHuLemma59_signedPowers_mul (K := K) k
  have heq : ((-A) * targetSign) * (sourceSign * A) = A * A := by
    have hneg : -A = (-1 : Kˣ) * A := by simp
    rw [hneg]
    calc
      (((-1 : Kˣ) * A) * targetSign) * (sourceSign * A) =
          ((-1 : Kˣ) * (targetSign * sourceSign)) * (A * A) := by ac_rfl
      _ = A * A := by
        rw [mul_comm targetSign sourceSign, hsign]
        norm_num
  rw [hhead]
  unfold heHuLemma59CTilde
  change IsSquare (((-A) * targetSign) * (sourceSign * A))
  rw [heq]
  exact ⟨A, rfl⟩

/-- Lemma 5.6(ii): the common source prefix cannot represent both literal
classic first-column tests. -/
theorem he2022ClassicLemma56ii
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 <= m)
    (hc : HeHuSharpDomain (heHuLemma59CTilde a k)) :
    ¬(
      DiagonalRepresents
          ((he2022ClassicLemma56Target
              (K := K) (heHuLemma59C a k) k).prefixValues
            (2 * k + 3) (by omega))
          (a.prefixValues (2 * k + 4) (by omega)) ∧
        DiagonalRepresents
          ((he2022ClassicLemma56Target (K := K)
              (heHuLemma59C a k *
                heHuSharp (heHuLemma59CTilde a k) hc) k).prefixValues
            (2 * k + 3) (by omega))
          (a.prefixValues (2 * k + 4) (by omega))) := by
  rintro ⟨hrepFirst, hrepSecond⟩
  let u := heHuSharp (heHuLemma59CTilde a k) hc
  let first := he2022ClassicLemma56Target (K := K)
    (heHuLemma59C a k) k
  let second := he2022ClassicLemma56Target (K := K)
    (heHuLemma59C a k * u) k
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
          standardHyperbolicEndpointTower (K := K) (k + 1) by
      simpa only [second] using
        he2022ClassicLemma56Target_hyperbolicValueUnits
          (K := K) (heHuLemma59C a k * u) k]
    symm
    simpa only [first] using
      he2022ClassicLemma56Target_hyperbolicValueUnits
        (K := K) (heHuLemma59C a k) k
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
    funext i
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
        he2022ClassicLemma56_twoTargetProduct_sameSquareClass a k u
  have hsecondClass : IsSquare
      ((-diagonalUnitDeterminant au *
          diagonalUnitDeterminant
            (diagonalUnitTake cu (2 * k + 2) (by omega))) *
        heHuLemma59CTilde a k) := by
    simpa only [au, cu, second, diagonalUnitTake_prefixValueUnits,
      diagonalUnitDeterminant_prefixValueUnits] using
        he2022ClassicLemma56_sourceTargetHead_sameSquareClass a k u
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

/-- He (2024), Lemma 5.6 in the publisher's full logical form: both tests
activate condition (iii), they cannot both be represented, and therefore
condition (iii) fails for at least one of them. -/
theorem he2022ClassicLemma56
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 <= m)
    (hClassic : Lattice.IsClassicIntegral q L)
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * k + 2) (by omega))
    (hAlphaNext :
      (a.heClassicOddThreshold (2 * k + 3) (by omega) : ℚ) <
        a.alphaValue ⟨2 * k + 4, by omega⟩)
    (hTrigger : a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
      1 < a.order ⟨2 * k + 4, by omega⟩) :
    ∃ hc : HeHuSharpDomain (heHuLemma59CTilde a k),
      let u := heHuSharp (heHuLemma59CTilde a k) hc
      a.centralDefectTrigger
          (he2022ClassicLemma56Target (K := K) (heHuLemma59C a k) k)
          (heHuLemma59CentralIndex k hm) ∧
        a.centralDefectTrigger
          (he2022ClassicLemma56Target
            (K := K) (heHuLemma59C a k * u) k)
          (heHuLemma59CentralIndex k hm) ∧
        ¬(
          DiagonalRepresents
              ((he2022ClassicLemma56Target
                  (K := K) (heHuLemma59C a k) k).prefixValues
                (2 * k + 3) (by omega))
              (a.prefixValues (2 * k + 4) (by omega)) ∧
            DiagonalRepresents
              ((he2022ClassicLemma56Target (K := K)
                  (heHuLemma59C a k * u) k).prefixValues
                (2 * k + 3) (by omega))
              (a.prefixValues (2 * k + 4) (by omega))) ∧
        (¬a.HeClassicPublishedCentralConditionAt
            (he2022ClassicLemma56Target
              (K := K) (heHuLemma59C a k) k)
            (heHuLemma59CentralIndex k hm) ∨
          ¬a.HeClassicPublishedCentralConditionAt
            (he2022ClassicLemma56Target
              (K := K) (heHuLemma59C a k * u) k)
            (heHuLemma59CentralIndex k hm)) := by
  rcases a.he2022ClassicLemma56i (k := k) hm hClassic hJ1 hJ2
    hAlphaNext hTrigger with
    ⟨hc, hFirstTrigger, hSecondTrigger⟩
  let u := heHuSharp (heHuLemma59CTilde a k) hc
  have hNot := a.he2022ClassicLemma56ii (k := k) hm hc
  refine ⟨hc, hFirstTrigger, hSecondTrigger, hNot, ?_⟩
  exact not_both_heClassicPublishedCentralConditionAt_of_triggers
    (m := m + 1) (n₁ := 2 * k + 1) (n₂ := 2 * k + 1)
    a
    (he2022ClassicLemma56Target (K := K) (heHuLemma59C a k) k)
    (he2022ClassicLemma56Target (K := K) (heHuLemma59C a k * u) k)
    (heHuLemma59CentralIndex k hm) (heHuLemma59CentralIndex k hm)
    hFirstTrigger hSecondTrigger hNot

end BONG.GoodBONG

end Bong
