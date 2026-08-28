/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeICaseOnePrefixClass
import Bong.Bong.Beli2009AlphaArithmetic

/-!
# Beli (2019), Lemma 7.9(ii), case 1: the comparison-prefix defect

The two endpoint models make the product of the two comparison-prefix
determinants either a square or the dyadic discriminant times a square.
Its raw quadratic-defect order is consequently at least `2e`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- A discriminant-twisted square has embedded quadratic-defect order
exactly `2e`. -/
theorem defectOrder_eq_twoE_of_mul_discriminant_isSquare
    [laws : DyadicDiscriminantClassLaws K]
    (x : Kˣ) (hsquare : IsSquare (x * laws.discriminantUnit)) :
    defectOrder (K := K) x =
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
  rcases hsquare with ⟨s, hs⟩
  have hx : x = laws.discriminantUnit *
      (s * laws.discriminantUnit⁻¹) ^ 2 := by
    calc
      x = (x * laws.discriminantUnit) * laws.discriminantUnit⁻¹ := by group
      _ = (s * s) * laws.discriminantUnit⁻¹ := by rw [hs]
      _ = laws.discriminantUnit *
          (s * laws.discriminantUnit⁻¹) ^ 2 := by
        simp only [pow_two]
        calc
          s * s * laws.discriminantUnit⁻¹ =
              (laws.discriminantUnit * laws.discriminantUnit⁻¹) *
                (s * s) * laws.discriminantUnit⁻¹ := by simp
          _ = laws.discriminantUnit * s * laws.discriminantUnit⁻¹ * s *
                laws.discriminantUnit⁻¹ := by ac_rfl
          _ = laws.discriminantUnit *
              (s * laws.discriminantUnit⁻¹ *
                (s * laws.discriminantUnit⁻¹)) := by group
  rw [hx, defectOrder_mul_square]
  unfold defectOrder
  rw [laws.discriminant_defect]
  rfl

/-- The comparison-prefix determinant product in case 1 has raw defect at
least `2e`, before the square-class alternative is eliminated. -/
theorem beli2019Lemma79_typeI_caseOne_prefixProduct_defect_ge_twoE
    [Beli2006AlphaLaws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch)
    (hgap : b.orderGap ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = 2 * (ramificationIndex K : Int) + 1)
    (hprevious : c.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = b.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩) :
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) (b.prefixProduct i.val * c.prefixProduct i.val) := by
  rcases beli2019Lemma79_typeI_caseOne_prefixProduct_cases
      a b c D C hnorm i hleft hgap hprevious with hsquare | htwisted
  · rw [defectOrder_eq_top_of_isSquare hsquare]
    exact le_top
  · rw [defectOrder_eq_twoE_of_mul_discriminant_isSquare _ htwisted]

/-- After the two endpoint alpha caps are included, the capped comparison
defect is still at least `2e`. -/
theorem beli2019Lemma79_typeI_caseOne_comparisonDefect_ge_twoE
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch)
    (hgap : b.orderGap ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = 2 * (ramificationIndex K : Int) + 1)
    (hprevious : c.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = b.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩) :
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let p : Fin (n + 1) := ⟨i.val - 1, by
    have hiBound := i.lt_large
    omega⟩
  have hiPos := i.pos
  have hiPreviousBound : i.val - 1 < n + 2 :=
    (Nat.sub_le i.val 1).trans_lt i.lt_large
  have hpSucc : p.succ = ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have hpCast : p.castSucc =
      (⟨i.val - 1, hiPreviousBound⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hgapB : b.orderGap p =
      2 * (ramificationIndex K : Int) + 1 := by
    simpa only [p] using hgap
  have hlargeB : 2 * (ramificationIndex K : Int) ≤ b.orderGap p := by
    rw [hgapB]
    omega
  have hcurrentLe : b.order ⟨i.val, i.lt_large⟩ ≤
      c.order ⟨i.val, i.lt_large⟩ := by
    rcases horderBC ⟨i.val, i.lt_large⟩ with
      hcurrent | ⟨_, hiNext, hpair⟩
    · exact hcurrent
    · change i.val + 1 < n + 2 at hiNext
      have htwoStep := b.good ⟨i.val - 1, hiPreviousBound⟩ (by
          change (i.val - 1) + 2 < n + 2
          omega)
      have htwoStep' : b.order ⟨i.val - 1, hiPreviousBound⟩ ≤
          b.order ⟨i.val + 1, hiNext⟩ := by
        have hindex :
            (⟨(i.val - 1) + 2, by omega⟩ : Fin (n + 2)) =
              ⟨i.val + 1, hiNext⟩ := by
          apply Fin.ext
          change (i.val - 1) + 2 = i.val + 1
          omega
        rw [hindex] at htwoStep
        exact htwoStep
      have hpair' : b.order ⟨i.val, i.lt_large⟩ +
            b.order ⟨i.val + 1, hiNext⟩ ≤
          c.order ⟨i.val - 1, hiPreviousBound⟩ +
            c.order ⟨i.val, i.lt_large⟩ := by
        simpa only using hpair
      rw [hprevious] at hpair'
      omega
  have hgapLe : b.orderGap p ≤ c.orderGap p := by
    unfold orderGap
    rw [hpSucc, hpCast, hprevious]
    omega
  have hlargeC : 2 * (ramificationIndex K : Int) ≤ c.orderGap p :=
    hlargeB.trans hgapLe
  have hbAlpha := b.beli2009Lemma27_ii p hlargeB
  have hcAlpha := c.beli2009Lemma27_ii p hlargeC
  have htwoEGap : (2 * (ramificationIndex K : ℚ)) ≤
      b.halfGapValue p := by
    unfold halfGapValue
    have hgapBQ : (b.orderGap p : ℚ) =
        2 * (ramificationIndex K : ℚ) + 1 := by
      exact_mod_cast hgapB
    rw [hgapBQ]
    linarith
  have hhalfLe : b.halfGapValue p ≤ c.halfGapValue p := by
    unfold halfGapValue
    have hgapLeQ : (b.orderGap p : ℚ) ≤ (c.orderGap p : ℚ) := by
      exact_mod_cast hgapLe
    linarith
  have hbCap : (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) ≤
      b.prefixAlphaCap i.val := by
    rw [b.prefixAlphaCap_of_internal i.pos i.lt_large]
    have hpIndex : (⟨i.val - 1, p.isLt⟩ : Fin (n + 1)) = p := by
      apply Fin.ext
      rfl
    rw [hpIndex, hbAlpha]
    exact_mod_cast htwoEGap
  have hcCap : (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) ≤
      c.prefixAlphaCap i.val := by
    rw [c.prefixAlphaCap_of_internal i.pos i.lt_large]
    have hpIndex : (⟨i.val - 1, p.isLt⟩ : Fin (n + 1)) = p := by
      apply Fin.ext
      rfl
    rw [hpIndex, hcAlpha]
    exact_mod_cast htwoEGap.trans hhalfLe
  have hraw :=
    beli2019Lemma79_typeI_caseOne_prefixProduct_defect_ge_twoE
      a b c D C hnorm i hleft hgap hprevious
  unfold truncatedPrefixDefect
  simpa only [one_mul] using le_min hraw (le_min hbCap hcCap)

end BONG.GoodBONG

end Bong
