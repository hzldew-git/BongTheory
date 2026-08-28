/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma63
import Bong.Bong.BeliLemma62Proof
import Bong.Bong.BinaryNormGeneratorLocalProof

/-!
# Proof of Beli (2003), Lemma 6.3

The value-set congruences of Lemma 6.2 give the upper group `g'(a)`.
When the original BONG has property B, the only extra low-defect factor is
the quadratic norm group.  It is obtained by splitting off the initial binary
segment and applying the Hilbert defect criterion to the deep tail.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace Dyadic

/-- Above depth `2e`, every principal unit is a square, so its unit
square-class subgroup is trivial. -/
theorem principalUnitValuationClassSubgroup_eq_bot_of_two_mul_e_lt
    (r : Nat) (hr : 2 * ramificationIndex K < r) :
    principalUnitValuationClassSubgroup K r = ⊥ := by
  apply le_antisymm
  · intro c hc
    rw [Subgroup.mem_bot]
    rcases hc with ⟨a, ha, rfl⟩
    change (a : Kˣ) ∈ principalUnitSubgroup K r at ha
    have herror : (r : WithTop Int) ≤
        ord K (((a : Kˣ) : K) - 1) :=
      (Lattice.mem_powerIdeal_iff (K := K) (r : Int)
        (((a : Kˣ) : K) - 1)).1 ha.2
    have hdeep :
        (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) <
          ord K (((a : Kˣ) : K) - 1) := by
      exact (show
        (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) <
          (r : WithTop Int) by exact_mod_cast hr).trans_le herror
    have hsquare : IsSquare (a : Kˣ) :=
      isSquare_of_ord_sub_one_gt_two_mul_e K (a : Kˣ) hdeep
    apply valuationUnitClassToSquareClass_injective K
    rw [valuationUnitClassToSquareClass_apply, map_one]
    apply (QuotientGroup.eq_one_iff (a : Kˣ)).2
    change IsSquare (a : Kˣ)
    exact hsquare
  · exact bot_le

end Dyadic

namespace BONG

/-- For an even adjacent order gap, the doubled cutoff in Definition 11 is
twice the cutoff used in Lemma 6.2. -/
theorem beliDefectCutoff_adjacentParameter_zero_eq_two_mul_lemma62Cutoff
    (b : BONG V q L (n + 2)) (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int)) :
    beliDefectCutoff K (b.adjacentParameter 0 (by simp)) =
      2 * b.lemma62DefectCutoff := by
  have hR : ¬2 * (ramificationIndex K : Int) <
      ordUnit K (b.adjacentParameter 0 (by simp)) := by
    rw [b.ordUnit_adjacentParameter_zero]
    omega
  have hleft := scratch_beliDefectCutoff_cast
    (K := K) (b.adjacentParameter 0 (by simp)) hR
  have hright := b.lemma62DefectCutoff_cast heven hupper
  rw [b.ordUnit_adjacentParameter_zero] at hleft
  rcases heven with ⟨g, hg⟩
  have hcalc :
      (beliDefectCutoff K
        (b.adjacentParameter 0 (by simp)) : Int) =
        2 * (b.lemma62DefectCutoff : Int) := by
    calc
      (beliDefectCutoff K
          (b.adjacentParameter 0 (by simp)) : Int) =
          2 * (ramificationIndex K : Int) - b.lemma62Gap := hleft
      _ = 2 * ((ramificationIndex K : Int) - b.lemma62Gap / 2) := by
        omega
      _ = 2 * (b.lemma62DefectCutoff : Int) := by rw [hright]
  exact_mod_cast hcalc

/-- The low branch of Definition 11 implies the Lemma 6.2(b) defect bound. -/
theorem lemma62_parameterDefect_le_cutoff_of_low
    (b : BONG V q L (n + 2)) (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hlow : 2 * beliParameterDefect K
        (b.adjacentParameter 0 (by simp)) ≤
      (beliDefectCutoff K
        (b.adjacentParameter 0 (by simp)) : ℕ∞)) :
    beliParameterDefect K (b.adjacentParameter 0 (by simp)) ≤
      (b.lemma62DefectCutoff : ℕ∞) := by
  let d := beliParameterDefect K (b.adjacentParameter 0 (by simp))
  have hfinite : d ≠ ⊤ := by
    intro htop
    rw [show beliParameterDefect K
        (b.adjacentParameter 0 (by simp)) = ⊤ by exact htop] at hlow
    simp at hlow
  have hcut :=
    b.beliDefectCutoff_adjacentParameter_zero_eq_two_mul_lemma62Cutoff
      heven hupper
  rw [hcut] at hlow
  change d ≤ (b.lemma62DefectCutoff : ℕ∞)
  change 2 * d ≤ ((2 * b.lemma62DefectCutoff : Nat) : ℕ∞) at hlow
  have hdcoe : ((d.toNat : Nat) : ℕ∞) = d := ENat.coe_toNat hfinite
  rw [← hdcoe] at hlow ⊢
  norm_cast at hlow ⊢
  omega

/-- The complementary high branch implies the Lemma 6.2(c) defect bound. -/
theorem lemma62_cutoff_le_parameterDefect_of_high
    (b : BONG V q L (n + 2)) (heven : Even b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int))
    (hhigh : ¬2 * beliParameterDefect K
        (b.adjacentParameter 0 (by simp)) ≤
      (beliDefectCutoff K
        (b.adjacentParameter 0 (by simp)) : ℕ∞)) :
    (b.lemma62DefectCutoff : ℕ∞) ≤
      beliParameterDefect K (b.adjacentParameter 0 (by simp)) := by
  let d := beliParameterDefect K (b.adjacentParameter 0 (by simp))
  by_cases htop : d = ⊤
  · simpa only [d, htop, le_top]
  · have hcut :=
      b.beliDefectCutoff_adjacentParameter_zero_eq_two_mul_lemma62Cutoff
        heven hupper
    rw [hcut] at hhigh
    change (b.lemma62DefectCutoff : ℕ∞) ≤ d
    change ¬2 * d ≤ ((2 * b.lemma62DefectCutoff : Nat) : ℕ∞) at hhigh
    have hdcoe : ((d.toNat : Nat) : ℕ∞) = d := ENat.coe_toNat htop
    rw [← hdcoe] at hhigh ⊢
    norm_cast at hhigh ⊢
    omega

/-- The relative low exponent becomes the absolute exponent in Lemma 6.2(b)
after adding the first order. -/
theorem order_zero_add_beliLowDefectExponent_eq_lemma62LowExponent
    (b : BONG V q L (n + 2))
    (hfinite : beliParameterDefect K
      (b.adjacentParameter 0 (by simp)) ≠ ⊤) :
    b.order 0 +
        (beliLowDefectExponent K
          (b.adjacentParameter 0 (by simp)) : Int) =
      b.lemma62LowExponent := by
  let a := b.adjacentParameter 0 (by simp)
  have hadmissible : IsBinaryParameterAdmissible a :=
    b.adjacentParameter_isBinaryParameterAdmissible 0 (by simp)
  have hexponent := scratch_beliLowDefectExponent_cast
    (K := K) a hadmissible (by simpa only [a] using hfinite)
  rw [hexponent]
  unfold lemma62LowExponent lemma62DefectNat
  rw [show ordUnit K a = b.lemma62Gap by
    simpa only [a] using b.ordUnit_adjacentParameter_zero]
  change b.order 0 +
      (b.lemma62Gap + (beliParameterDefectNat K
        (b.adjacentParameter 0 (by simp)) : Int)) =
    b.order 1 + (beliParameterDefectNat K
      (b.adjacentParameter 0 (by simp)) : Int)
  unfold lemma62Gap
  omega

/-- The relative high exponent becomes the absolute exponent in Lemma 6.2(c)
after adding the first order. -/
theorem order_zero_add_beliHighDefectExponent_eq_lemma62HighExponent
    (b : BONG V q L (n + 2)) (heven : Even b.lemma62Gap) :
    b.order 0 +
        (beliHighDefectExponent K
          (b.adjacentParameter 0 (by simp)) : Int) =
      b.lemma62HighExponent := by
  let a := b.adjacentParameter 0 (by simp)
  have hadmissible : IsBinaryParameterAdmissible a :=
    b.adjacentParameter_isBinaryParameterAdmissible 0 (by simp)
  have hlower := hadmissible.ordUnit_ge_neg_two_mul_e
  have hgap : ordUnit K a = b.lemma62Gap := by
    simpa only [a] using b.ordUnit_adjacentParameter_zero
  have hnonneg :
      0 ≤ (ramificationIndex K : Int) + ordUnit K a / 2 := by
    rw [hgap] at hlower ⊢
    rcases heven with ⟨g, hg⟩
    omega
  have hexponent : (beliHighDefectExponent K a : Int) =
      (ramificationIndex K : Int) + ordUnit K a / 2 := by
    unfold beliHighDefectExponent
    rw [Int.toNat_of_nonneg hnonneg]
  rw [hexponent, hgap]
  unfold lemma62HighExponent lemma62Gap
  rcases heven with ⟨g, hg⟩
  omega

/-- A norm generator has the same finite quadratic-value order as the
zeroth vector of any nonempty BONG of its lattice. -/
theorem ord_quadratic_isNormGenerator_eq_order_zero
    (b : BONG V q L (n + 1)) (y : V)
    (hy : Lattice.IsNormGenerator q L y) :
    ord K (q.quadratic y) = (b.order 0 : WithTop Int) := by
  have hyAnisotropic := b.isAnisotropic_of_isNormGenerator_binary hy
  have hratioOrder :
      ordUnit K (b.normGeneratorValueRatioUnit y hy) = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K
      (b.normGeneratorValueRatioUnit y hy)).1
        (b.normGeneratorValueRatioUnit_isValuationUnit y hy)
  have hvalueOrderUnit :
      ordUnit K (Units.mk0 (q.quadratic y) hyAnisotropic) =
        ordUnit K (b.valueUnit 0) := by
    simp only [normGeneratorValueRatioUnit, div_eq_mul_inv,
      ordUnit_mul, ordUnit_inv] at hratioOrder
    omega
  calc
    ord K (q.quadratic y) =
        (ordUnit K (Units.mk0 (q.quadratic y) hyAnisotropic) :
          WithTop Int) := by
      simpa only [Units.val_mk0] using
        (coe_ordUnit K
          (Units.mk0 (q.quadratic y) hyAnisotropic)).symm
    _ = (ordUnit K (b.valueUnit 0) : WithTop Int) := by
      rw [hvalueOrderUnit]
    _ = (b.order 0 : WithTop Int) := by
      rw [b.order_eq_ordUnit]

/-- The norm ideal of a nonempty BONG, with its zeroth index supplied
explicitly.  This avoids an `OfNat (Fin m) 0` side condition when `m` is an
unreduced arithmetic expression. -/
theorem normIdeal_eq_powerIdeal_order_mk_zero
    {m : Nat} (b : BONG V q L m) (hm : 0 < m) :
    Lattice.normIdeal q L =
      Lattice.powerIdeal (K := K) (b.order ⟨0, hm⟩) := by
  cases m with
  | zero => omega
  | succ m =>
      have hindex : (⟨0, hm⟩ : Fin (m + 1)) = 0 := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact b.normIdeal_eq_powerIdeal_order_zero

/-- A congruence `Q(L) ⊆ Q(x₁)·ᵊ² + 𝐭ᵐ`, with
`R₁ + r ≤ m`, puts every norm-generator value ratio in the principal-unit
square-class subgroup of depth `r`. -/
theorem normGeneratorValueRatioClass_mem_principal_of_quadraticValues
    (b : BONG V q L (n + 2)) (m : Int) (r : Nat)
    (hexponent : b.order 0 + (r : Int) ≤ m)
    (hvalues : Lattice.quadraticValueSet q L ⊆
      Lattice.scaledIntegralSquareResidueSet (b.value 0)
        (Lattice.powerIdeal (K := K) m))
    (y : V) (hy : Lattice.IsNormGenerator q L y) :
    b.normGeneratorValueRatioClass y hy ∈
      principalUnitValuationClassSubgroup K r := by
  apply
    valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
  apply (isQuadraticApproximation_iff_le_defect K).1
  have hyValue : q.quadratic y ∈ Lattice.quadraticValueSet q L := by
    rw [Lattice.mem_quadraticValueSet_iff]
    exact ⟨y, hy.mem, rfl⟩
  rcases hvalues hyValue with ⟨x, hx⟩
  refine ⟨(x : K), ?_⟩
  have hyAnisotropic := b.isAnisotropic_of_isNormGenerator_binary hy
  have hnormalized :
      1 - (x : K) ^ 2 /
          (b.normGeneratorValueRatioUnit y hy : K) =
        (q.quadratic y - b.value 0 * (x : K) ^ 2) /
          q.quadratic y := by
    have hqyNe : q.quadratic y ≠ 0 := hyAnisotropic
    simp only [normGeneratorValueRatioUnit, Units.val_div_eq_div_val,
      Units.val_mk0, coe_valueUnit]
    field_simp [hqyNe, b.value_ne_zero 0]
  have hratioOrder :
      ordUnit K (b.normGeneratorValueRatioUnit y hy) = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K
      (b.normGeneratorValueRatioUnit y hy)).1
        (b.normGeneratorValueRatioUnit_isValuationUnit y hy)
  have hvalueOrderUnit :
      ordUnit K (Units.mk0 (q.quadratic y) hyAnisotropic) =
        ordUnit K (b.valueUnit 0) := by
    simp only [normGeneratorValueRatioUnit, div_eq_mul_inv,
      ordUnit_mul, ordUnit_inv] at hratioOrder
    omega
  have hvalueOrder :
      ord K (q.quadratic y) = (b.order 0 : WithTop Int) := by
    calc
      ord K (q.quadratic y) =
          (ordUnit K (Units.mk0 (q.quadratic y) hyAnisotropic) :
            WithTop Int) := by
        simpa only [Units.val_mk0] using
          (coe_ordUnit K
            (Units.mk0 (q.quadratic y) hyAnisotropic)).symm
      _ = (ordUnit K (b.valueUnit 0) : WithTop Int) := by
        rw [hvalueOrderUnit]
      _ = (b.order 0 : WithTop Int) := by
        rw [b.order_eq_ordUnit]
  have herror : (m : WithTop Int) ≤
      ord K (q.quadratic y - b.value 0 * (x : K) ^ 2) :=
    (Lattice.mem_powerIdeal_iff (K := K) m _).1 hx
  change (r : WithTop Int) ≤ ord K
    (1 - (x : K) ^ 2 / (b.normGeneratorValueRatioUnit y hy : K))
  rw [hnormalized, div_eq_mul_inv, ord_mul, AddValuation.map_inv,
    hvalueOrder]
  have hbase :
      ((b.order 0 + (r : Int) : Int) : WithTop Int) ≤
        ord K (q.quadratic y - b.value 0 * (x : K) ^ 2) := by
    exact (show
      ((b.order 0 + (r : Int) : Int) : WithTop Int) ≤
        (m : WithTop Int) by exact_mod_cast hexponent).trans herror
  calc
    (r : WithTop Int) =
        ((b.order 0 + (r : Int) : Int) : WithTop Int) +
          (-((b.order 0 : Int) : WithTop Int)) := by
      norm_cast
      omega
    _ ≤ ord K (q.quadratic y - b.value 0 * (x : K) ^ 2) +
          (-((b.order 0 : Int) : WithTop Int)) := by
      simpa only [add_comm] using
        add_le_add_right hbase
          (-((b.order 0 : Int) : WithTop Int))

/-- The three congruence estimates of Lemma 6.2 give the upper group `g'(a)`
in Beli (2003), Lemma 6.3(i). -/
theorem beliLemma63_valueRatioClassSet_subset_upper_proved
    (b : BONG V q L (n + 2)) (w : b.HeadInverseRescaleWitness)
    (hB : b.HasPropertyBOrInverse w) :
    b.normGeneratorValueRatioClassSet ⊆
      (beliNormGeneratorUpperGroup K
        (b.adjacentParameter 0 (by simp)) :
          Set (ValuationUnitClass K)) := by
  intro c hc
  rcases hc with ⟨y, hy, rfl⟩
  let a := b.adjacentParameter 0 (by simp)
  have hparameterOrder : ordUnit K a = b.lemma62Gap := by
    simpa only [a] using b.ordUnit_adjacentParameter_zero
  by_cases hR : 2 * (ramificationIndex K : Int) < ordUnit K a
  · rw [beliNormGeneratorUpperGroup_of_two_e_lt K a hR]
    let r : Nat := Int.toNat b.lemma62Gap
    have hgapPos : 0 < b.lemma62Gap := by
      rw [hparameterOrder] at hR
      omega
    have hrCast : (r : Int) = b.lemma62Gap := by
      unfold r
      rw [Int.toNat_of_nonneg (le_of_lt hgapPos)]
    have hrDeep : 2 * ramificationIndex K < r := by
      exact_mod_cast (show
        2 * (ramificationIndex K : Int) < (r : Int) by
          rw [hrCast, ← hparameterOrder]
          exact hR)
    rw [← principalUnitValuationClassSubgroup_eq_bot_of_two_mul_e_lt
      (K := K) r hrDeep]
    apply b.normGeneratorValueRatioClass_mem_principal_of_quadraticValues
      (b.order 1) r
    · rw [hrCast]
      unfold lemma62Gap
      omega
    · apply b.beliLemma62_ii_a w hB
      unfold lemma62Gap at hgapPos
      omega
  · by_cases hlow : 2 * beliParameterDefect K a ≤
        (beliDefectCutoff K a : ℕ∞)
    · rw [beliNormGeneratorUpperGroup_of_low_defect K a hR hlow]
      rcases Int.even_or_odd b.lemma62Gap with heven | hodd
      · have hupper :
            b.lemma62Gap ≤ 2 * (ramificationIndex K : Int) := by
          rw [← hparameterOrder]
          omega
        have hdefect : beliParameterDefect K
            (b.adjacentParameter 0 (by simp)) ≤
              (b.lemma62DefectCutoff : ℕ∞) := by
          apply b.lemma62_parameterDefect_le_cutoff_of_low heven hupper
          simpa only [a] using hlow
        have hfinite : beliParameterDefect K
            (b.adjacentParameter 0 (by simp)) ≠ ⊤ := by
          intro htop
          rw [htop] at hdefect
          simp at hdefect
        have hvalues := b.beliLemma62_ii_b w hB heven hupper hdefect
        apply b.normGeneratorValueRatioClass_mem_principal_of_quadraticValues
          b.lemma62LowExponent (beliLowDefectExponent K a)
        · have hexponent :=
            b.order_zero_add_beliLowDefectExponent_eq_lemma62LowExponent
              hfinite
          simpa only [a] using le_of_eq hexponent
        · exact hvalues
      · have hiZero : (0 : Fin (n + 2)).1 + 1 < n + 2 := by
          simp
        have hoddGap : Odd
            (b.order ⟨(0 : Fin (n + 2)).1 + 1, hiZero⟩ -
              b.order (0 : Fin (n + 2))) := by
          change Odd b.lemma62Gap
          exact hodd
        have hgapPosRaw :=
          b.adjacentOrderGap_pos_of_odd (0 : Fin (n + 2))
            hiZero hoddGap
        have hgapPos : 0 < b.lemma62Gap := by
          simpa [lemma62Gap] using hgapPosRaw
        have horder : b.order 0 ≤ b.order 1 := by
          unfold lemma62Gap at hgapPos
          omega
        have hvalues := b.beliLemma62_ii_a w hB horder
        have hoddNeg : Odd (ordUnit K (-a)) := by
          rw [ordUnit_neg, hparameterOrder]
          exact hodd
        have hzero : beliParameterDefect K a = 0 := by
          unfold beliParameterDefect
          exact quadraticDefect_eq_zero_of_odd_ordUnit
            (K := K) (-a) hoddNeg
        have hfinite : beliParameterDefect K
            (b.adjacentParameter 0 (by simp)) ≠ ⊤ := by
          simpa only [a, hzero] using (show (0 : ℕ∞) ≠ ⊤ by simp)
        have hdefectNat : b.lemma62DefectNat = 0 := by
          unfold lemma62DefectNat beliParameterDefectNat
          simpa only [a, hzero] using ENat.toNat_zero
        have hlemmaExponent : b.lemma62LowExponent = b.order 1 := by
          unfold lemma62LowExponent
          rw [hdefectNat]
          simp
        apply b.normGeneratorValueRatioClass_mem_principal_of_quadraticValues
          (b.order 1) (beliLowDefectExponent K a)
        · have hexponent :=
            b.order_zero_add_beliLowDefectExponent_eq_lemma62LowExponent
              hfinite
          rw [hlemmaExponent] at hexponent
          simpa only [a] using le_of_eq hexponent
        · exact hvalues
    · rw [beliNormGeneratorUpperGroup_of_high_defect K a hR hlow]
      have hevenParameter :=
        beli2009BinaryHighDefect_even_order (K := K) a hlow
      have heven : Even b.lemma62Gap := by
        rwa [hparameterOrder] at hevenParameter
      have hupper :
          b.lemma62Gap ≤ 2 * (ramificationIndex K : Int) := by
        rw [← hparameterOrder]
        omega
      have hdefect : (b.lemma62DefectCutoff : ℕ∞) ≤
          beliParameterDefect K
            (b.adjacentParameter 0 (by simp)) := by
        apply b.lemma62_cutoff_le_parameterDefect_of_high heven hupper
        simpa only [a] using hlow
      have hvalues := b.beliLemma62_ii_c w hB heven hupper hdefect
      apply b.normGeneratorValueRatioClass_mem_principal_of_quadraticValues
        b.lemma62HighExponent (beliHighDefectExponent K a)
      · have hexponent :=
          b.order_zero_add_beliHighDefectExponent_eq_lemma62HighExponent
            heven
        simpa only [a] using le_of_eq hexponent
      · exact hvalues

/-- A norm generator differs from the norm represented by the initial binary
block by a principal unit whose depth is the order of the third vector minus
the first order.  If that depth is complementary to `d(-a)`, the full value
ratio is again a norm from `K(√(-a))`. -/
theorem normGeneratorValueRatioClass_mem_quadraticNorm_of_deep_third
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (horder12 : b.order 1 ≤ b.order 2)
    (hdepthPos : 0 < b.order 2 - b.order 0)
    (hsum : ((2 * ramificationIndex K : Nat) : ℕ∞) <
      beliParameterDefect K (b.adjacentParameter 0 (by simp)) +
        (Int.toNat (b.order 2 - b.order 0) : ℕ∞))
    (y : V) (hy : Lattice.IsNormGenerator q L y) :
    b.normGeneratorValueRatioClass y hy ∈
      quadraticNormValuationClassSubgroup K
        (-(b.adjacentParameter 0 (by simp))) := by
  have hsplitRaw := b.beliCorollary44_i_unconditional hB.isGood
    (1 : Fin (n + 3)) (by simp) horder12
  have hsplit : b.HasTwoBlockSplit 2 (by omega) := by
    simpa using hsplitRaw
  rcases hsplit with ⟨S⟩
  let F := S.toProductLatticeIsometry
  let xy := F.toLinearEquiv.symm y
  have hxy : xy ∈ Lattice.product S.left.lattice S.right.lattice := by
    apply (F.map_mem xy).mpr
    simpa [xy, F] using hy.mem
  have hxyParts := Lattice.mem_product_iff.mp hxy
  let leftValue : K :=
    (q.restrict S.left.carrier S.left.nondegenerate).quadratic xy.1
  let rightValue : K :=
    (q.restrict S.right.carrier S.right.nondegenerate).quadratic xy.2
  have htotal : q.quadratic y = leftValue + rightValue := by
    have hmap := F.map_quadratic xy
    have hFxy : F.toLinearEquiv xy = y := by simp [xy, F]
    rw [← hFxy, hmap, QuadraticSpace.orthogonalSum_quadratic_apply]
  let j0 : Fin (n + 3 - 2) := ⟨0, by omega⟩
  have hrightOrder : S.right.bong.order j0 = b.order 2 := by
    calc
      S.right.bong.order j0 = b.order (S.right.sourceIndex j0) :=
        S.right.order_eq j0
      _ = b.order 2 := by
        apply congrArg b.order
        apply Fin.ext
        simp [SegmentWitness.sourceIndex, j0,
          Nat.mod_eq_of_lt (by omega : 2 < n + 3)]
  have hrightIdeal : rightValue ∈
      Lattice.powerIdeal (K := K) (b.order 2) := by
    have hmem := Lattice.quadratic_mem_normIdeal_of_mem
      (q.restrict S.right.carrier S.right.nondegenerate)
      S.right.lattice hxyParts.2
    have hnorm := normIdeal_eq_powerIdeal_order_mk_zero
      S.right.bong (by omega)
    change Lattice.normIdeal
      (q.restrict S.right.carrier S.right.nondegenerate)
        S.right.lattice =
      Lattice.powerIdeal (K := K) (S.right.bong.order j0) at hnorm
    rw [hnorm, hrightOrder] at hmem
    exact hmem
  have hrightOrderLower : (b.order 2 : WithTop Int) ≤
      ord K rightValue :=
    (Lattice.mem_powerIdeal_iff (K := K) (b.order 2) rightValue).1
      hrightIdeal
  have htotalOrder : ord K (q.quadratic y) =
      (b.order 0 : WithTop Int) :=
    b.ord_quadratic_isNormGenerator_eq_order_zero y hy
  have htotalLtRight : ord K (q.quadratic y) < ord K rightValue := by
    rw [htotalOrder]
    exact (show (b.order 0 : WithTop Int) <
      (b.order 2 : WithTop Int) by
        exact_mod_cast (show b.order 0 < b.order 2 by omega)).trans_le
          hrightOrderLower
  have hleftEq : leftValue = q.quadratic y - rightValue := by
    rw [htotal]
    ring
  have hleftOrder : ord K leftValue =
      (b.order 0 : WithTop Int) := by
    rw [hleftEq, (ord K).map_sub_eq_of_lt_left htotalLtRight,
      htotalOrder]
  have hleftNe : leftValue ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero] at hleftOrder
    exact WithTop.coe_ne_top hleftOrder.symm
  have hleftOrderUnit :
      ordUnit K (Units.mk0 leftValue hleftNe) = b.order 0 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit K]
    simpa only [Units.val_mk0] using hleftOrder
  have hleftBongOrder : S.left.bong.order 0 = b.order 0 := by
    simpa [SegmentWitness.sourceIndex] using
      S.left.order_eq (0 : Fin 2)
  have hleftValueZero : S.left.bong.value 0 = b.value 0 := by
    simpa [SegmentWitness.sourceIndex] using
      S.left.value_eq (0 : Fin 2)
  have hleftNorm : Lattice.IsNormGenerator
      (q.restrict S.left.carrier S.left.nondegenerate)
      S.left.lattice xy.1 := by
    refine ⟨hxyParts.1, ?_⟩
    calc
      Lattice.normIdeal
          (q.restrict S.left.carrier S.left.nondegenerate)
          S.left.lattice =
          Lattice.principalIdeal (K := K) (S.left.bong.value 0) := by
        simpa [S.left.bong.value_zero_eq_quadratic_head] using
          S.left.bong.head_isNormGenerator.normIdeal_eq
      _ = Lattice.principalIdeal (K := K) leftValue := by
        apply (Lattice.principalIdeal_eq_iff_ordUnit_eq
          (S.left.bong.valueUnit 0) (Units.mk0 leftValue hleftNe)).2
        rw [← S.left.bong.order_eq_ordUnit, hleftBongOrder,
          hleftOrderUnit]
  have hparameter : S.left.bong.binaryParameter =
      b.adjacentParameter 0 (by simp) := by
    unfold binaryParameter adjacentParameter
    rw [S.left.valueUnit_eq, S.left.valueUnit_eq]
    congr 2
  let zUnit := S.left.bong.normGeneratorValueRatioUnit xy.1 hleftNorm
  let uUnit := b.normGeneratorValueRatioUnit y hy
  let correction : Kˣ := uUnit / zUnit
  have hzValuationUnit : IsValuationUnit K (zUnit : K) := by
    exact S.left.bong.normGeneratorValueRatioUnit_isValuationUnit
      xy.1 hleftNorm
  have huValuationUnit : IsValuationUnit K (uUnit : K) := by
    exact b.normGeneratorValueRatioUnit_isValuationUnit y hy
  have hcorrectionValuationUnit : IsValuationUnit K (correction : K) := by
    apply (isValuationUnit_iff_ordUnit_eq_zero K correction).2
    have hzOrder :=
      (isValuationUnit_iff_ordUnit_eq_zero K zUnit).1 hzValuationUnit
    have huOrder :=
      (isValuationUnit_iff_ordUnit_eq_zero K uUnit).1 huValuationUnit
    dsimp only [correction]
    simp only [div_eq_mul_inv, ordUnit_mul, ordUnit_inv]
    omega
  have hcorrectionError : (correction : K) - 1 =
      rightValue / leftValue := by
    dsimp only [correction, uUnit, zUnit]
    simp only [normGeneratorValueRatioUnit, Units.val_div_eq_div_val,
      Units.val_mk0, coe_valueUnit]
    rw [hleftValueZero]
    field_simp [b.value_ne_zero 0, hleftNe,
      b.isAnisotropic_of_isNormGenerator_binary hy]
    rw [htotal]
    change ((leftValue + rightValue) / leftValue - 1) * leftValue =
      rightValue
    field_simp [hleftNe]
    ring
  let depth : Nat := Int.toNat (b.order 2 - b.order 0)
  have hdepthCast : (depth : Int) = b.order 2 - b.order 0 := by
    unfold depth
    rw [Int.toNat_of_nonneg (le_of_lt hdepthPos)]
  have hcorrectionErrorOrder : (depth : WithTop Int) ≤
      ord K ((correction : K) - 1) := by
    rw [hcorrectionError, div_eq_mul_inv, ord_mul,
      AddValuation.map_inv, hleftOrder]
    have hbase :
        ((b.order 2 - b.order 0 : Int) : WithTop Int) ≤
          ord K rightValue + (-((b.order 0 : Int) : WithTop Int)) := by
      calc
        ((b.order 2 - b.order 0 : Int) : WithTop Int) =
            (b.order 2 : WithTop Int) +
              (-((b.order 0 : Int) : WithTop Int)) := by
          norm_cast
        _ ≤ ord K rightValue +
              (-((b.order 0 : Int) : WithTop Int)) := by
          simpa only [add_comm] using
            add_le_add_right hrightOrderLower
              (-((b.order 0 : Int) : WithTop Int))
    have hdepthCastTop : (depth : WithTop Int) =
        ((b.order 2 - b.order 0 : Int) : WithTop Int) := by
      exact_mod_cast hdepthCast
    rw [hdepthCastTop]
    exact hbase
  let correctionUnit : valuationUnitSubgroup K :=
    ⟨correction, hcorrectionValuationUnit⟩
  have hcorrectionPrincipal : valuationUnitClassHom K correctionUnit ∈
      principalUnitValuationClassSubgroup K depth := by
    refine ⟨correctionUnit, ?_, rfl⟩
    change correction ∈ principalUnitSubgroup K depth
    refine ⟨hcorrectionValuationUnit, ?_⟩
    exact (Lattice.mem_powerIdeal_iff (K := K) (depth : Int)
      ((correction : K) - 1)).2 hcorrectionErrorOrder
  have hcorrectionNorm : valuationUnitClassHom K correctionUnit ∈
      quadraticNormValuationClassSubgroup K
        (-(b.adjacentParameter 0 (by simp))) := by
    apply principalUnitValuationClassSubgroup_le_quadraticNorm_of_defect_sum_gt
      (K := K) (-(b.adjacentParameter 0 (by simp))) depth
    · simpa only [beliParameterDefect, depth] using hsum
    · exact hcorrectionPrincipal
  have hzNorm : S.left.bong.normGeneratorValueRatioClass xy.1 hleftNorm ∈
      quadraticNormValuationClassSubgroup K
        (-(b.adjacentParameter 0 (by simp))) := by
    let zValuationUnit :=
      S.left.bong.normGeneratorValueRatioValuationUnit xy.1 hleftNorm
    refine ⟨zValuationUnit, ?_, rfl⟩
    change IsQuadraticNorm K
      (-(b.adjacentParameter 0 (by simp))) zUnit
    rw [← hparameter]
    exact S.left.bong.normGeneratorValueRatioUnit_isQuadraticNorm_binary
      xy.1 hleftNorm
  have hclassFactor : b.normGeneratorValueRatioClass y hy =
      S.left.bong.normGeneratorValueRatioClass xy.1 hleftNorm *
        valuationUnitClassHom K correctionUnit := by
    unfold normGeneratorValueRatioClass
    rw [← map_mul]
    apply congrArg (valuationUnitClassHom K)
    apply Subtype.ext
    change uUnit = zUnit * correction
    dsimp only [correction]
    simp
  rw [hclassFactor]
  exact (quadraticNormValuationClassSubgroup K
    (-(b.adjacentParameter 0 (by simp)))).mul_mem hzNorm hcorrectionNorm

/-- In the odd first-gap branch, Property B forces the next gap to have
depth at least `2e + 1`. -/
theorem thirdGap_ge_of_propertyB_lemma63_odd
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (hodd : Odd b.lemma62Gap)
    (hupper : b.lemma62Gap ≤ 2 * (ramificationIndex K : Int)) :
    2 * (ramificationIndex K : Int) + 1 ≤
      b.order 2 - b.order 1 := by
  have htrigger : b.propertyBTrigger (0 : Fin (n + 2)) := by
    unfold propertyBTrigger
    left
    constructor
    · simpa [lemma62Gap] using
        (show b.lemma62Gap ≤
          2 * (ramificationIndex K : Int) + 1 by omega)
    · simpa [lemma62Gap] using hodd
  have hright := (hB.2 (0 : Fin (n + 2)) htrigger).2
  exact hright ⟨2, by omega⟩ rfl

/-- Beli (2003), Lemma 6.3(ii): Property B supplies the quadratic-norm
factor missing from the upper congruence group. -/
theorem beliLemma63_valueRatioClassSet_subset_group_of_propertyB_proved
    (b : BONG V q L (n + 2)) (hB : b.HasPropertyB) :
    b.normGeneratorValueRatioClassSet ⊆
      (beliNormGeneratorGroup K
        (b.adjacentParameter 0 (by simp)) :
          Set (ValuationUnitClass K)) := by
  intro c hc
  rcases hc with ⟨y, hy, rfl⟩
  let a := b.adjacentParameter 0 (by simp)
  have hparameterOrder : ordUnit K a = b.lemma62Gap := by
    simpa only [a] using b.ordUnit_adjacentParameter_zero
  let w := b.headInverseRescaleWitness
  have hupperMem := b.beliLemma63_valueRatioClassSet_subset_upper_proved
    w (Or.inl hB)
      (show b.normGeneratorValueRatioClass y hy ∈
        b.normGeneratorValueRatioClassSet from ⟨y, hy, rfl⟩)
  by_cases hR : 2 * (ramificationIndex K : Int) < ordUnit K a
  · rw [beliNormGeneratorGroup_of_two_e_lt K a hR]
    rw [beliNormGeneratorUpperGroup_of_two_e_lt K a hR] at hupperMem
    exact hupperMem
  · by_cases hlow : 2 * beliParameterDefect K a ≤
        (beliDefectCutoff K a : ℕ∞)
    · rw [beliNormGeneratorGroup_of_low_defect K a hR hlow]
      have hprincipal : b.normGeneratorValueRatioClass y hy ∈
          principalUnitValuationClassSubgroup K
            (beliLowDefectExponent K a) := by
        rw [beliNormGeneratorUpperGroup_of_low_defect K a hR hlow]
          at hupperMem
        exact hupperMem
      refine ⟨hprincipal, ?_⟩
      cases n with
      | zero =>
          let vu := b.normGeneratorValueRatioValuationUnit y hy
          refine ⟨vu, ?_, rfl⟩
          change IsQuadraticNorm K (-a)
            (b.normGeneratorValueRatioUnit y hy)
          have hnorm :=
            b.normGeneratorValueRatioUnit_isQuadraticNorm_binary y hy
          simpa [a, binaryParameter, adjacentParameter] using hnorm
      | succ m =>
          have hupper : b.lemma62Gap ≤
              2 * (ramificationIndex K : Int) := by
            rw [← hparameterOrder]
            omega
          rcases Int.even_or_odd b.lemma62Gap with heven | hodd
          · have hdefect : beliParameterDefect K
                (b.adjacentParameter 0 (by simp)) ≤
                  (b.lemma62DefectCutoff : ℕ∞) := by
              apply b.lemma62_parameterDefect_le_cutoff_of_low
                heven hupper
              simpa only [a] using hlow
            have hfinite : beliParameterDefect K
                (b.adjacentParameter 0 (by simp)) ≠ ⊤ := by
              intro htop
              rw [htop] at hdefect
              simp at hdefect
            have hthird := b.thirdGap_ge_of_propertyB_lemma62_low
              hB heven hupper hdefect
            have horder12 : b.order 1 ≤ b.order 2 := by
              have he : 0 ≤ (ramificationIndex K : Int) := by positivity
              omega
            have hadmissible :=
              b.adjacentParameter_isBinaryParameterAdmissible 0 (by simp)
            have hgapLower := hadmissible.ordUnit_ge_neg_two_mul_e
            rw [b.ordUnit_adjacentParameter_zero] at hgapLower
            have hdepthPos : 0 < b.order 2 - b.order 0 := by
              unfold lemma62Gap at hgapLower
              omega
            have hdefectEq : beliParameterDefect K
                (b.adjacentParameter 0 (by simp)) =
                  ((beliParameterDefect K
                    (b.adjacentParameter 0 (by simp))).toNat : ℕ∞) :=
              (ENat.coe_toNat hfinite).symm
            have hparameterNonneg :=
              beli2009_order_add_parameterDefect_nonneg
                (K := K) hadmissible hfinite
            have hdepthCast :
                (Int.toNat (b.order 2 - b.order 0) : Int) =
                  b.order 2 - b.order 0 := by
              rw [Int.toNat_of_nonneg (le_of_lt hdepthPos)]
            have hsumInt : 2 * (ramificationIndex K : Int) <
                ((beliParameterDefect K
                  (b.adjacentParameter 0 (by simp))).toNat : Int) +
                  Int.toNat (b.order 2 - b.order 0) := by
              rw [hdepthCast]
              rw [b.ordUnit_adjacentParameter_zero] at hparameterNonneg
              unfold lemma62Gap at hparameterNonneg
              omega
            have hsumNat : 2 * ramificationIndex K <
                (beliParameterDefect K
                  (b.adjacentParameter 0 (by simp))).toNat +
                  Int.toNat (b.order 2 - b.order 0) := by
              exact_mod_cast hsumInt
            have hsum : ((2 * ramificationIndex K : Nat) : ℕ∞) <
                beliParameterDefect K
                    (b.adjacentParameter 0 (by simp)) +
                  (Int.toNat (b.order 2 - b.order 0) : ℕ∞) := by
              rw [hdefectEq, ← ENat.coe_add]
              exact_mod_cast hsumNat
            exact b.normGeneratorValueRatioClass_mem_quadraticNorm_of_deep_third
              hB horder12 hdepthPos hsum y hy
          · have hgapPosRaw :=
              b.adjacentOrderGap_pos_of_odd (0 : Fin (m + 1 + 2))
                (by simp) (by simpa [lemma62Gap] using hodd)
            have hgapPos : 0 < b.lemma62Gap := by
              simpa [lemma62Gap] using hgapPosRaw
            have hthird := b.thirdGap_ge_of_propertyB_lemma63_odd
              hB hodd hupper
            have horder12 : b.order 1 ≤ b.order 2 := by
              have he : 0 ≤ (ramificationIndex K : Int) := by positivity
              omega
            have hdepthPos : 0 < b.order 2 - b.order 0 := by
              unfold lemma62Gap at hgapPos
              omega
            have hoddNeg : Odd (ordUnit K (-a)) := by
              rw [ordUnit_neg, hparameterOrder]
              exact hodd
            have hzero : beliParameterDefect K
                (b.adjacentParameter 0 (by simp)) = 0 := by
              unfold beliParameterDefect
              simpa only [a] using
                (quadraticDefect_eq_zero_of_odd_ordUnit
                  (K := K) (-a) hoddNeg)
            have hdepthCast :
                (Int.toNat (b.order 2 - b.order 0) : Int) =
                  b.order 2 - b.order 0 := by
              rw [Int.toNat_of_nonneg (le_of_lt hdepthPos)]
            have hdepthDeepInt : 2 * (ramificationIndex K : Int) <
                (Int.toNat (b.order 2 - b.order 0) : Int) := by
              rw [hdepthCast]
              unfold lemma62Gap at hgapPos
              omega
            have hdepthDeepNat : 2 * ramificationIndex K <
                Int.toNat (b.order 2 - b.order 0) := by
              exact_mod_cast hdepthDeepInt
            have hsum : ((2 * ramificationIndex K : Nat) : ℕ∞) <
                beliParameterDefect K
                    (b.adjacentParameter 0 (by simp)) +
                  (Int.toNat (b.order 2 - b.order 0) : ℕ∞) := by
              rw [hzero, zero_add]
              exact_mod_cast hdepthDeepNat
            exact b.normGeneratorValueRatioClass_mem_quadraticNorm_of_deep_third
              hB horder12 hdepthPos hsum y hy
    · rw [beliNormGeneratorGroup_of_high_defect K a hR hlow]
      rw [beliNormGeneratorUpperGroup_of_high_defect K a hR hlow]
        at hupperMem
      exact hupperMem

/-- Unconditional realization of Beli (2003), Lemma 6.3. -/
noncomputable instance binaryNormGeneratorLocalLawsInstance :
    BinaryNormGeneratorLocalLaws.{u, v} K :=
  binaryNormGeneratorLocalLawsProved

noncomputable instance beliLemma63LawsProved :
    BeliLemma63Laws.{u, v} K where
  valueRatioClassSet_subset_upper b w hB :=
    b.beliLemma63_valueRatioClassSet_subset_upper_proved w hB
  valueRatioClassSet_subset_group_of_propertyB b hB :=
    b.beliLemma63_valueRatioClassSet_subset_group_of_propertyB_proved hB

end BONG

end Bong
