/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.ResidueDefectProductProof
import Bong.Bong.Classification
import Bong.Bong.DiscriminantClassProof
import Bong.Bong.MaximalDefectClassProof
import Bong.Bong.DiagonalCodimensionOneCancellation
import Bong.Bong.DiagonalHeadCancellation
import Bong.Dyadic.HilbertDefectCriterionProof
import Bong.Dyadic.HilbertMultiplicativityReduction
import Bong.Dyadic.HilbertNondegeneracyProof
import Bong.Dyadic.UnramifiedNormDirectProof

/-!
# Direct dyadic proof of the Hilbert-symbol laws

This file follows O'Meara 63:11--13.  It first proves the exact binary
prime-discriminant dichotomy, then classifies every nonsplit quaternion norm
form by explicit changes of variables.  Two Witt cancellations show that the
product of two nonnorm cosets is a norm, which supplies bimultiplicativity.
-/

namespace Bong.Dyadic

open Bong

universe u

variable {K : Type u} [Field K]

noncomputable def binaryChangeLinearMap
    (a b : Kˣ) (x y : K) (d : Kˣ) :
    (Fin 2 → K) →ₗ[K] (Fin 2 → K) where
  toFun z := ![
    x * z 0 + (b : K) * y / (d : K) * z 1,
    y * z 0 - (a : K) * x / (d : K) * z 1]
  map_add' z w := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c z := by
    funext i
    fin_cases i <;> simp <;> ring

theorem binaryChangeLinearMap_injective
    (a b : Kˣ) (x y : K) (d : Kˣ)
    (hvalue : (a : K) * x ^ 2 + (b : K) * y ^ 2 = (d : K)) :
    Function.Injective (binaryChangeLinearMap a b x y d) := by
  intro z w hzw
  have hzero := congrFun hzw (0 : Fin 2)
  have hone := congrFun hzw (1 : Fin 2)
  change x * z 0 + (b : K) * y / (d : K) * z 1 =
    x * w 0 + (b : K) * y / (d : K) * w 1 at hzero
  change y * z 0 - (a : K) * x / (d : K) * z 1 =
    y * w 0 - (a : K) * x / (d : K) * w 1 at hone
  funext i
  fin_cases i
  · field_simp [Units.ne_zero d] at hzero hone
    have hscaled : (d : K) ^ 2 * (z 0 - w 0) = 0 := by
      linear_combination
        (a : K) * x * hzero + (b : K) * y * hone -
          (d : K) * (z 0 - w 0) * hvalue
    rcases mul_eq_zero.mp hscaled with hd | hzw
    · exact ((pow_ne_zero 2 (Units.ne_zero d)) hd).elim
    · exact sub_eq_zero.mp hzw
  · field_simp [Units.ne_zero d] at hzero hone
    have hscaled : (d : K) * (z 1 - w 1) = 0 := by
      linear_combination
        y * hzero - x * hone - (z 1 - w 1) * hvalue
    rcases mul_eq_zero.mp hscaled with hd | hzw
    · exact (Units.ne_zero d hd).elim
    · exact sub_eq_zero.mp hzw

theorem binaryChange_diagonalRepresents
    (a b d : Kˣ) (x y : K)
    (hvalue : (a : K) * x ^ 2 + (b : K) * y ^ 2 = (d : K)) :
    DiagonalRepresents
      (fun i => ((![d, a * b / d] : Fin 2 → Kˣ) i : K))
      (fun i => ((![a, b] : Fin 2 → Kˣ) i : K)) := by
  refine ⟨binaryChangeLinearMap a b x y d,
    binaryChangeLinearMap_injective a b x y d hvalue, ?_⟩
  intro z
  simp only [diagonalQuadratic, Fin.sum_univ_two]
  change
    (a : K) * (x * z 0 + (b : K) * y / (d : K) * z 1) ^ 2 +
      (b : K) * (y * z 0 - (a : K) * x / (d : K) * z 1) ^ 2 =
    (d : K) * z 0 ^ 2 + ((a * b / d : Kˣ) : K) * z 1 ^ 2
  rw [Units.val_div_eq_div_val, Units.val_mul]
  have hvalue' : (b : K) * y ^ 2 + (a : K) * x ^ 2 = (d : K) := by
    linear_combination hvalue
  calc
    (a : K) * (x * z 0 + (b : K) * y / (d : K) * z 1) ^ 2 +
          (b : K) * (y * z 0 - (a : K) * x / (d : K) * z 1) ^ 2 =
        ((a : K) * x ^ 2 + (b : K) * y ^ 2) * z 0 ^ 2 +
          ((a : K) * (b : K) / (d : K) ^ 2) *
            ((b : K) * y ^ 2 + (a : K) * x ^ 2) * z 1 ^ 2 := by ring
    _ = (d : K) * z 0 ^ 2 +
          ((a : K) * (b : K) / (d : K)) * z 1 ^ 2 := by
      rw [hvalue, hvalue']
      field_simp [Units.ne_zero d]

section DefectImprovement

variable [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K]

local instance defect : QuadraticDefectLaws K :=
  quadraticDefectLawsOfHensel K

private theorem one_le_ord_of_pos_local {x : K} (h : 0 < ord K x) :
    (1 : WithTop Int) ≤ ord K x := by
  by_cases htop : ord K x = ⊤
  · rw [htop]
    exact le_top
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hn] at h ⊢
    have hnPos : (0 : Int) < n := by exact_mod_cast h
    exact_mod_cast (show (1 : Int) ≤ n by omega)

/-- The defect-improvement step in O'Meara 63:11.  If the first coefficient
of a binary diagonal form is a nonsquare valuation unit of nonmaximal defect
and the second coefficient has odd order, an explicit change of basis makes
the first defect strictly larger while preserving those two order conditions. -/
theorem exists_binary_defect_improvement
    (a b : Kˣ)
    (haUnit : IsValuationUnit K (a : K))
    (hbOdd : Odd (ordUnit K b))
    (haFinite : quadraticDefect K a ≠ ⊤)
    (haNonzero : quadraticDefect K a ≠ 0)
    (haLt : quadraticDefect K a <
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    ∃ d : Kˣ,
      IsValuationUnit K (d : K) ∧
        quadraticDefect K a < quadraticDefect K d ∧
        Odd (ordUnit K (a * b / d)) ∧
        DiagonalRepresents
          (fun i => ((![d, a * b / d] : Fin 2 → Kˣ) i : K))
          (fun i => ((![a, b] : Fin 2 → Kˣ) i : K)) := by
  obtain ⟨v, r, t, hvUnit, hvDefect, hfactor, hvField, htOrder⟩ :=
    Bong.BONG.exists_exact_principal_representation a haFinite haNonzero
  let n : Nat := (quadraticDefect K a).toNat
  have hdefectCoe : quadraticDefect K a = (n : ℕ∞) := by
    simpa only [n] using (ENat.coe_toNat haFinite).symm
  have hvLt : quadraticDefect K v <
      ((2 * ramificationIndex K : Nat) : ℕ∞) := by
    rwa [hvDefect]
  have hnOdd : Odd n := by
    have h := quadraticDefect_toNat_odd_of_unit_of_lt_two_mul_e
      (K := K) v hvUnit hvLt
    simpa only [hvDefect, n] using h
  rcases hnOdd with ⟨j, hj⟩
  rcases hbOdd with ⟨l, hl⟩
  let k : Int := (j : Int) - l
  have horderMatch : ordUnit K b + 2 * k = (n : Int) := by
    dsimp only [k]
    omega
  let p : Kˣ := uniformizerPowerUnit K k
  have hpOrder : ordUnit K p = k :=
    ordUnit_uniformizerPowerUnit (K := K) k
  have htOrderN : ord K t = ((n : Int) : WithTop Int) := by
    simpa only [n] using htOrder
  have htNe : t ≠ 0 := by
    apply (ord_eq_top_iff K).not.mp
    rw [htOrderN]
    exact WithTop.coe_ne_top
  let tu : Kˣ := Units.mk0 t htNe
  have htuOrder : ordUnit K tu = (n : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    exact htOrderN
  let epsilon : Kˣ := -tu / (b * p ^ 2)
  have hepsilonOrder : ordUnit K epsilon = 0 := by
    dsimp only [epsilon]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_neg,
      ordUnit_mul, ordUnit_pow, htuOrder, hpOrder]
    omega
  have hepsilonUnit : IsValuationUnit K (epsilon : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K epsilon).2 hepsilonOrder
  obtain ⟨z, _hzUnit, hzApprox⟩ :=
    exists_unit_squareRoot_mod_maximal K epsilon hepsilonUnit
  let q : K := t + (b : K) * (p : K) ^ 2 * z ^ 2
  have hqFactor : q =
      (b : K) * (p : K) ^ 2 * (z ^ 2 - (epsilon : K)) := by
    dsimp only [q, epsilon, tu]
    simp only [Units.val_neg, Units.val_div_eq_div_val, Units.val_mul,
      Units.val_pow_eq_pow_val, Units.val_mk0]
    field_simp [Units.ne_zero b, Units.ne_zero p]
    ring
  have hbpOrder : ord K ((b : K) * (p : K) ^ 2) =
      ((n : Int) : WithTop Int) := by
    rw [ord_mul, ord_pow, ← coe_ordUnit, ← coe_ordUnit, hpOrder]
    exact_mod_cast horderMatch
  have hzDepth : (1 : WithTop Int) ≤
      ord K (z ^ 2 - (epsilon : K)) :=
    one_le_ord_of_pos_local hzApprox
  have hqDepth : (((n + 1 : Nat) : Int) : WithTop Int) ≤ ord K q := by
    rw [hqFactor, ord_mul, hbpOrder]
    calc
      (((n + 1 : Nat) : Int) : WithTop Int) =
          ((n : Int) : WithTop Int) + 1 := by norm_num
      _ ≤ ((n : Int) : WithTop Int) +
          ord K (z ^ 2 - (epsilon : K)) :=
        by
          simpa only [add_comm] using
            add_le_add_left hzDepth ((n : Int) : WithTop Int)
  have hqPos : (0 : WithTop Int) < ord K q := by
    have honePos : (0 : WithTop Int) < 1 := by norm_num
    exact honePos.trans_le (show (1 : WithTop Int) ≤ ord K q by
      exact (show (1 : WithTop Int) ≤
        (((n + 1 : Nat) : Int) : WithTop Int) by
          exact_mod_cast (show 1 ≤ n + 1 by omega)).trans hqDepth)
  have hdFieldOrder : ord K (1 + q) = 0 := by
    have hlt : ord K (1 : K) < ord K q := by
      simpa only [ord_one] using hqPos
    simpa only [ord_one] using (ord K).map_add_eq_of_lt_left hlt
  have hdNe : 1 + q ≠ 0 := by
    apply (ord_eq_top_iff K).not.mp
    rw [hdFieldOrder]
    exact WithTop.coe_ne_top
  let d : Kˣ := Units.mk0 (1 + q) hdNe
  have hdUnit : IsValuationUnit K (d : K) := by
    simpa only [d, Units.val_mk0, IsValuationUnit] using hdFieldOrder
  have hdDefectDepth : ((n + 1 : Nat) : ℕ∞) ≤ quadraticDefect K d := by
    apply natCast_le_quadraticDefect K
    refine ⟨1, ?_⟩
    have hfield : 1 - (1 : K) ^ 2 / (d : K) = q / (d : K) := by
      change 1 - (1 : K) ^ 2 / (1 + q) = q / (1 + q)
      field_simp [hdNe]
      ring
    rw [hfield, div_eq_mul_inv, ord_mul, AddValuation.map_inv, hdUnit]
    convert hqDepth using 1 <;> norm_num
  have haStrict : quadraticDefect K a < quadraticDefect K d := by
    rw [hdefectCoe]
    have hstep : (n : ℕ∞) < ((n + 1 : Nat) : ℕ∞) := by
      exact_mod_cast Nat.lt_succ_self n
    exact hstep.trans_le hdDefectDepth
  have haOrder : ordUnit K a = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K a).1 haUnit
  have hdOrder : ordUnit K d = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K d).1 hdUnit
  have hcOdd : Odd (ordUnit K (a * b / d)) := by
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_mul, ordUnit_inv,
      haOrder, hdOrder]
    simpa using (show Odd (ordUnit K b) from ⟨l, hl⟩)
  have haScaled : (a : K) * ((r : K)⁻¹) ^ 2 = (v : K) := by
    have hf := congrArg Units.val hfactor
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hf
    rw [hf]
    field_simp [Units.ne_zero r]
  have hvalue :
      (a : K) * ((r : K)⁻¹) ^ 2 +
          (b : K) * ((p : K) * z) ^ 2 = (d : K) := by
    rw [haScaled]
    change (v : K) + (b : K) * ((p : K) * z) ^ 2 = 1 + q
    rw [hvField]
    dsimp only [q]
    ring
  refine ⟨d, hdUnit, haStrict, hcOdd, ?_⟩
  exact binaryChange_diagonalRepresents a b d ((r : K)⁻¹)
    ((p : K) * z) hvalue

end DefectImprovement

section PrimeBinaryRepresentation

variable [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K]

local instance primeBinaryDefect : QuadraticDefectLaws K :=
  quadraticDefectLawsOfHensel K

noncomputable local instance primeBinaryDiscriminant :
    DyadicDiscriminantClassLaws K :=
  dyadicDiscriminantClassLawsProved

noncomputable local instance primeBinaryMaximalDefect :
    DyadicMaximalDefectClassLaws K :=
  dyadicMaximalDefectClassLawsProved

noncomputable local instance primeBinaryUnramifiedNorm :
    DyadicUnramifiedNormLaws K :=
  dyadicUnramifiedNormLawsProvedDirect

/-- A scalar is represented by a binary diagonal form. -/
def BinaryRepresentsValue (a b target : Kˣ) : Prop :=
  ∃ x y : K,
    (a : K) * x ^ 2 + (b : K) * y ^ 2 = (target : K)

private theorem binaryRepresentsValue_of_first_eq_mul_square
    (a b target s : Kˣ) (h : a = target * s ^ 2) :
    BinaryRepresentsValue a b target := by
  refine ⟨(s : K)⁻¹, 0, ?_⟩
  simp only [zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero]
  have hfield := congrArg Units.val h
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hfield
  rw [hfield]
  field_simp [Units.ne_zero s]

private theorem binaryRepresentsValue_transport
    (a b d c target : Kˣ)
    (hsource : BinaryRepresentsValue d c target)
    (hchange : DiagonalRepresents
      (fun i => ((![d, c] : Fin 2 → Kˣ) i : K))
      (fun i => ((![a, b] : Fin 2 → Kˣ) i : K))) :
    BinaryRepresentsValue a b target := by
  rcases hsource with ⟨x, y, hxy⟩
  rcases hchange with ⟨f, _hfInjective, hf⟩
  let z : Fin 2 → K := ![x, y]
  refine ⟨f z 0, f z 1, ?_⟩
  have hform := hf z
  simp only [diagonalQuadratic, Fin.sum_univ_two] at hform
  have h := hform.trans hxy
  simpa only [z, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons] using h

private theorem binaryRepresentsValue_reflect
    (a b d c target : Kˣ)
    (htarget : BinaryRepresentsValue a b target)
    (hchange : DiagonalRepresents
      (fun i => ((![d, c] : Fin 2 → Kˣ) i : K))
      (fun i => ((![a, b] : Fin 2 → Kˣ) i : K))) :
    BinaryRepresentsValue d c target := by
  rcases htarget with ⟨x, y, hxy⟩
  rcases hchange with ⟨f, hfInjective, hf⟩
  let w : Fin 2 → K := ![x, y]
  obtain ⟨z, hz⟩ := f.surjective_of_injective hfInjective w
  refine ⟨z 0, z 1, ?_⟩
  have hform := hf z
  simp only [diagonalQuadratic, Fin.sum_univ_two] at hform
  have htargetW :
      ((![a, b] : Fin 2 → Kˣ) 0 : K) * (f z 0) ^ 2 +
          ((![a, b] : Fin 2 → Kˣ) 1 : K) * (f z 1) ^ 2 =
        (target : K) := by
    rw [hz]
    simpa only [w, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons] using hxy
  have hform' := hform.symm.trans htargetW
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons] using hform'

/-- Remaining distance to the maximal finite unit defect.  Square classes are
assigned distance zero, so every use of `exists_binary_defect_improvement`
strictly decreases this natural measure. -/
noncomputable def binaryDefectMeasure (x : Kˣ) : Nat :=
  if quadraticDefect K x = ⊤ then 0
  else 2 * ramificationIndex K - (quadraticDefect K x).toNat

/-- O'Meara 63:11 (existence half), in the precise scalar form needed for
the Hilbert-symbol proof: a binary form whose determinant has odd valuation
represents either `1` or the distinguished discriminant unit. -/
theorem primeBinary_represents_one_or_discriminant
    (a b : Kˣ)
    (haUnit : IsValuationUnit K (a : K))
    (hbOdd : Odd (ordUnit K b)) :
    BinaryRepresentsValue a b (1 : Kˣ) ∨
      BinaryRepresentsValue a b
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit := by
  let delta : Kˣ :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  have aux : ∀ m : Nat, ∀ a b : Kˣ,
      binaryDefectMeasure (K := K) a = m →
      IsValuationUnit K (a : K) →
      Odd (ordUnit K b) →
      BinaryRepresentsValue a b (1 : Kˣ) ∨
        BinaryRepresentsValue a b delta := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro a b hmeasure haUnit hbOdd
        by_cases haSquare : IsSquare a
        · left
          rcases haSquare with ⟨s, hs⟩
          apply binaryRepresentsValue_of_first_eq_mul_square a b 1 s
          simpa only [one_mul, pow_two] using hs
        · have haFinite : quadraticDefect K a ≠ ⊤ := by
            intro htop
            exact haSquare
              ((quadraticDefect_eq_top_iff_isSquare (K := K) a).mp htop)
          have haUpper : quadraticDefect K a ≤
              ((2 * ramificationIndex K : Nat) : ℕ∞) :=
            quadraticDefect_le_two_mul_e_of_not_isSquare
              (K := K) haSquare
          by_cases haEndpoint :
              ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
                quadraticDefect K a
          · rcases isSquare_or_isSquare_div_discriminant_of_defect_ge_twoE
                a haEndpoint with haSq | haDiscSq
            · exact (haSquare haSq).elim
            · right
              rcases haDiscSq with ⟨s, hs⟩
              apply binaryRepresentsValue_of_first_eq_mul_square
                a b delta s
              calc
                a = (a / delta) * delta := by simp
                _ = (s * s) * delta := by rw [hs]
                _ = delta * s ^ 2 := by simp [pow_two, mul_comm]
          · have haLt : quadraticDefect K a <
                ((2 * ramificationIndex K : Nat) : ℕ∞) :=
              lt_of_not_ge haEndpoint
            have haNonzero : quadraticDefect K a ≠ 0 := by
              have haDefectOdd :=
                quadraticDefect_toNat_odd_of_unit_of_lt_two_mul_e
                  (K := K) a haUnit haLt
              intro hzero
              rw [hzero] at haDefectOdd
              norm_num at haDefectOdd
            obtain ⟨d, hdUnit, hadStrict, hcOdd, hchange⟩ :=
              exists_binary_defect_improvement a b haUnit hbOdd
                haFinite haNonzero haLt
            have hmeasureLt :
                binaryDefectMeasure (K := K) d <
                  binaryDefectMeasure (K := K) a := by
              by_cases hdTop : quadraticDefect K d = ⊤
              · have haNatLt :
                    (quadraticDefect K a).toNat <
                      2 * ramificationIndex K := by
                  have haCoe : quadraticDefect K a =
                      ((quadraticDefect K a).toNat : ℕ∞) :=
                    (ENat.coe_toNat haFinite).symm
                  rw [haCoe] at haLt
                  exact_mod_cast haLt
                simp only [binaryDefectMeasure, hdTop, if_pos,
                  haFinite, if_false]
                omega
              · have hdNotSquare : ¬ IsSquare d := by
                  intro hdSquare
                  exact hdTop
                    ((quadraticDefect_eq_top_iff_isSquare (K := K) d).2
                      hdSquare)
                have hdUpper : quadraticDefect K d ≤
                    ((2 * ramificationIndex K : Nat) : ℕ∞) :=
                  quadraticDefect_le_two_mul_e_of_not_isSquare
                    (K := K) hdNotSquare
                have haCoe : quadraticDefect K a =
                    ((quadraticDefect K a).toNat : ℕ∞) :=
                  (ENat.coe_toNat haFinite).symm
                have hdCoe : quadraticDefect K d =
                    ((quadraticDefect K d).toNat : ℕ∞) :=
                  (ENat.coe_toNat hdTop).symm
                have hnatStrict :
                    (quadraticDefect K a).toNat <
                      (quadraticDefect K d).toNat := by
                  rw [haCoe, hdCoe] at hadStrict
                  exact_mod_cast hadStrict
                have hdNatUpper : (quadraticDefect K d).toNat ≤
                    2 * ramificationIndex K := by
                  rw [hdCoe] at hdUpper
                  exact_mod_cast hdUpper
                have haNatLt : (quadraticDefect K a).toNat <
                    2 * ramificationIndex K := by
                  rw [haCoe] at haLt
                  exact_mod_cast haLt
                simp only [binaryDefectMeasure, hdTop, if_false,
                  haFinite]
                omega
            have hdm : binaryDefectMeasure (K := K) d < m := by
              rw [← hmeasure]
              exact hmeasureLt
            rcases ih (binaryDefectMeasure (K := K) d) hdm d (a * b / d)
                rfl hdUnit hcOdd with hone | hdelta
            · left
              exact binaryRepresentsValue_transport a b d (a * b / d)
                1 hone hchange
            · right
              exact binaryRepresentsValue_transport a b d (a * b / d)
                delta hdelta hchange
  simpa only [delta] using
    aux (binaryDefectMeasure (K := K) a) a b rfl haUnit hbOdd

/-- O'Meara 63:11 (exclusion half): a prime-discriminant binary form cannot
represent both `1` and the distinguished unramified discriminant unit. -/
theorem primeBinary_not_represents_one_and_discriminant
    (a b : Kˣ)
    (haUnit : IsValuationUnit K (a : K))
    (hbOdd : Odd (ordUnit K b)) :
    ¬(BinaryRepresentsValue a b (1 : Kˣ) ∧
      BinaryRepresentsValue a b
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit) := by
  let delta : Kˣ :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  rintro ⟨hone, hdelta⟩
  rcases hone with ⟨x, y, hxy⟩
  let c : Kˣ := a * b / (1 : Kˣ)
  have hchange : DiagonalRepresents
      (fun i => ((![(1 : Kˣ), c] : Fin 2 → Kˣ) i : K))
      (fun i => ((![a, b] : Fin 2 → Kˣ) i : K)) := by
    simpa only [c] using
      binaryChange_diagonalRepresents a b (1 : Kˣ) x y hxy
  have hdeltaNormalized : BinaryRepresentsValue (1 : Kˣ) c delta :=
    binaryRepresentsValue_reflect a b 1 c delta hdelta hchange
  rcases hdeltaNormalized with ⟨ξ, η, hξη⟩
  have hdeltaNotSquare : ¬ IsSquare delta := by
    intro hsquare
    have htop := quadraticDefect_eq_top_of_isSquare K hsquare
    have hfiniteValue : quadraticDefect K delta =
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
      simpa only [delta] using
        (inferInstance : DyadicDiscriminantClassLaws K).discriminant_defect
    rw [hfiniteValue] at htop
    exact ENat.coe_ne_top _ htop
  have hξη' : ξ ^ 2 + (c : K) * η ^ 2 = (delta : K) := by
    simpa using hξη
  have hηNe : η ≠ 0 := by
    intro hη
    have hξSq : ξ ^ 2 = (delta : K) := by
      simpa only [hη, zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero,
        one_mul] using hξη'
    have hξNe : ξ ≠ 0 := by
      intro hξ
      rw [hξ] at hξSq
      exact Units.ne_zero delta (by simpa using hξSq.symm)
    apply hdeltaNotSquare
    refine ⟨Units.mk0 ξ hξNe, ?_⟩
    apply Units.ext
    change (delta : K) = ξ * ξ
    simpa only [pow_two] using hξSq.symm
  have hnorm : IsQuadraticNorm K delta (-c) := by
    refine ⟨ξ / η, 1 / η, ?_⟩
    simp only [Units.val_neg]
    change (ξ / η) ^ 2 - (delta : K) * (1 / η) ^ 2 = -(c : K)
    field_simp [hηNe]
    linear_combination hξη'
  have hcOdd : Odd (ordUnit K c) := by
    have haOrder : ordUnit K a = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K a).1 haUnit
    dsimp only [c]
    rw [div_one, ordUnit_mul, haOrder, zero_add]
    exact hbOdd
  have hnegOdd : Odd (ordUnit K (-c)) := by
    rw [ordUnit_neg]
    exact hcOdd
  have hnegEven : Even (ordUnit K (-c)) :=
    (isQuadraticNorm_discriminant_iff_even_order (-c)).mp hnorm
  exact Int.not_even_iff_odd.mpr hnegOdd hnegEven

/-- Exact O'Meara 63:11 dichotomy for a prime-discriminant binary form. -/
theorem primeBinary_represents_exactly_one
    (a b : Kˣ)
    (haUnit : IsValuationUnit K (a : K))
    (hbOdd : Odd (ordUnit K b)) :
    (BinaryRepresentsValue a b (1 : Kˣ) ∨
      BinaryRepresentsValue a b
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit) ∧
    ¬(BinaryRepresentsValue a b (1 : Kˣ) ∧
      BinaryRepresentsValue a b
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit) :=
  ⟨primeBinary_represents_one_or_discriminant a b haUnit hbOdd,
    primeBinary_not_represents_one_and_discriminant a b haUnit hbOdd⟩

end PrimeBinaryRepresentation

section QuaternionNormForms

variable [CharZero K]

/-- Coefficients of the reduced norm form of the quaternion symbol `(a,b)`.
The ordering is `1, -a, -b, a*b`. -/
def quaternionNormCoefficients (a b : Kˣ) : Fin 4 → K :=
  fun i => ((![(1 : Kˣ), -a, -b, a * b] : Fin 4 → Kˣ) i : K)

/-- Equal-rank diagonal representations compose. -/
private theorem diagonalRepresents_trans
    {n : Nat} {a b c : Fin n → K}
    (hab : DiagonalRepresents a b) (hbc : DiagonalRepresents b c) :
    DiagonalRepresents a c := by
  rcases hab with ⟨f, hf, hqf⟩
  rcases hbc with ⟨g, hg, hqg⟩
  refine ⟨g.comp f, hg.comp hf, ?_⟩
  intro x
  rw [LinearMap.comp_apply, hqg, hqf]

/-- A diagonal form is isometric to itself. -/
private theorem diagonalRepresents_refl_local {n : Nat} (a : Fin n → K) :
    DiagonalRepresents a a :=
  diagonalRepresents_refl a

/-- Multiplying the first quaternion parameter by a square does not change
its norm form. -/
theorem quaternionNorm_mul_square_left
    (a b s : Kˣ) :
    DiagonalRepresents
      (quaternionNormCoefficients (a * s ^ 2) b)
      (quaternionNormCoefficients a b) := by
  let f : (Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
    { toFun := fun z => ![z 0, (s : K) * z 1, z 2, (s : K) * z 3]
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp <;> ring
      map_smul' := by
        intro c x
        funext i
        fin_cases i <;> simp <;> ring }
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    funext i
    fin_cases i
    · exact congrFun hxy 0
    · have h := congrFun hxy 1
      change (s : K) * x 1 = (s : K) * y 1 at h
      exact mul_left_cancel₀ (Units.ne_zero s) h
    · exact congrFun hxy 2
    · have h := congrFun hxy 3
      change (s : K) * x 3 = (s : K) * y 3 at h
      exact mul_left_cancel₀ (Units.ne_zero s) h
  · intro z
    simp only [quaternionNormCoefficients, diagonalQuadratic,
      Fin.sum_univ_four]
    dsimp [f]
    simp only [one_mul]
    change
      z 0 ^ 2 + (-(a : K)) * ((s : K) * z 1) ^ 2 +
          (-(b : K)) * z 2 ^ 2 + ((a : K) * (b : K)) *
            ((s : K) * z 3) ^ 2 =
        z 0 ^ 2 + (-((a : K) * (s : K) ^ 2)) * z 1 ^ 2 +
          (-(b : K)) * z 2 ^ 2 +
            (((a : K) * (s : K) ^ 2) * (b : K)) * z 3 ^ 2
    ring

/-- Multiplying the second quaternion parameter by a square does not change
its norm form. -/
theorem quaternionNorm_mul_square_right
    (a b s : Kˣ) :
    DiagonalRepresents
      (quaternionNormCoefficients a (b * s ^ 2))
      (quaternionNormCoefficients a b) := by
  let f : (Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
    { toFun := fun z => ![z 0, z 1, (s : K) * z 2, (s : K) * z 3]
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp <;> ring
      map_smul' := by
        intro c x
        funext i
        fin_cases i <;> simp <;> ring }
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    funext i
    fin_cases i
    · exact congrFun hxy 0
    · exact congrFun hxy 1
    · have h := congrFun hxy 2
      change (s : K) * x 2 = (s : K) * y 2 at h
      exact mul_left_cancel₀ (Units.ne_zero s) h
    · have h := congrFun hxy 3
      change (s : K) * x 3 = (s : K) * y 3 at h
      exact mul_left_cancel₀ (Units.ne_zero s) h
  · intro z
    simp only [quaternionNormCoefficients, diagonalQuadratic,
      Fin.sum_univ_four]
    dsimp [f]
    simp only [one_mul]
    change
      z 0 ^ 2 + (-(a : K)) * z 1 ^ 2 +
          (-(b : K)) * ((s : K) * z 2) ^ 2 + ((a : K) * (b : K)) *
            ((s : K) * z 3) ^ 2 =
        z 0 ^ 2 + (-(a : K)) * z 1 ^ 2 +
          (-((b : K) * (s : K) ^ 2)) * z 2 ^ 2 +
            ((a : K) * ((b : K) * (s : K) ^ 2)) * z 3 ^ 2
    ring

/-- The quaternion parameters may be interchanged. -/
theorem quaternionNorm_swap (a b : Kˣ) :
    DiagonalRepresents (quaternionNormCoefficients a b)
      (quaternionNormCoefficients b a) := by
  let f : (Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
    { toFun := fun z => ![z 0, z 2, z 1, z 3]
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp
      map_smul' := by
        intro c x
        funext i
        fin_cases i <;> simp }
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    funext i
    fin_cases i
    · exact congrFun hxy 0
    · exact congrFun hxy 2
    · exact congrFun hxy 1
    · exact congrFun hxy 3
  · intro z
    simp only [quaternionNormCoefficients, diagonalQuadratic,
      Fin.sum_univ_four]
    dsimp [f]
    simp only [one_mul]
    change
      z 0 ^ 2 + (-(b : K)) * z 2 ^ 2 + (-(a : K)) * z 1 ^ 2 +
          ((b : K) * (a : K)) * z 3 ^ 2 =
        z 0 ^ 2 + (-(a : K)) * z 1 ^ 2 + (-(b : K)) * z 2 ^ 2 +
          ((a : K) * (b : K)) * z 3 ^ 2
    ring

/-- The standard quaternion-symbol identity `(a,b) ≃ (-ab,a)`, written as
an explicit diagonal coordinate change. -/
theorem quaternionNorm_rotate (a b : Kˣ) :
    DiagonalRepresents (quaternionNormCoefficients (-a * b) a)
      (quaternionNormCoefficients a b) := by
  let f : (Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
    { toFun := fun z => ![z 0, z 2, (a : K) * z 3, z 1]
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp <;> ring
      map_smul' := by
        intro c x
        funext i
        fin_cases i <;> simp <;> ring }
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    funext i
    fin_cases i
    · exact congrFun hxy 0
    · exact congrFun hxy 3
    · exact congrFun hxy 1
    · have h := congrFun hxy 2
      change (a : K) * x 3 = (a : K) * y 3 at h
      exact mul_left_cancel₀ (Units.ne_zero a) h
  · intro z
    simp only [quaternionNormCoefficients, diagonalQuadratic,
      Fin.sum_univ_four]
    dsimp [f]
    simp only [one_mul]
    change
      z 0 ^ 2 + (-(a : K)) * z 2 ^ 2 + (-(b : K)) *
          ((a : K) * z 3) ^ 2 + ((a : K) * (b : K)) * z 1 ^ 2 =
        z 0 ^ 2 + (-((-((a : K)) * (b : K)))) * z 1 ^ 2 +
          (-(a : K)) * z 2 ^ 2 +
            (((-((a : K)) * (b : K)) * (a : K))) * z 3 ^ 2
    ring

/-- A determinant-preserving isometry of the binary parameter form lifts to
an isometry of the associated quaternion norm forms. -/
theorem quaternionNorm_of_binary_change
    (a b c d : Kˣ)
    (hdet : c * d = a * b)
    (hbinary : DiagonalRepresents
      (fun i => ((![c, d] : Fin 2 → Kˣ) i : K))
      (fun i => ((![a, b] : Fin 2 → Kˣ) i : K))) :
    DiagonalRepresents (quaternionNormCoefficients c d)
      (quaternionNormCoefficients a b) := by
  rcases hbinary with ⟨g, hg, hqg⟩
  let pair : (Fin 4 → K) →ₗ[K] (Fin 2 → K) :=
    { toFun := fun z => ![z 1, z 2]
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp
      map_smul' := by
        intro s x
        funext i
        fin_cases i <;> simp }
  let f : (Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
    { toFun := fun z => ![z 0, g (pair z) 0, g (pair z) 1, z 3]
      map_add' := by
        intro x y
        funext i
        fin_cases i
        · simp
        · change g (pair (x + y)) 0 = g (pair x) 0 + g (pair y) 0
          simp only [map_add, Pi.add_apply]
        · change g (pair (x + y)) 1 = g (pair x) 1 + g (pair y) 1
          simp only [map_add, Pi.add_apply]
        · simp
      map_smul' := by
        intro s x
        funext i
        fin_cases i
        · simp
        · change g (pair (s • x)) 0 = s * g (pair x) 0
          simp only [map_smul, Pi.smul_apply, smul_eq_mul]
        · change g (pair (s • x)) 1 = s * g (pair x) 1
          simp only [map_smul, Pi.smul_apply, smul_eq_mul]
        · simp }
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    have hzero : x 0 = y 0 := congrFun hxy 0
    have hthree : x 3 = y 3 := congrFun hxy 3
    have hpairImage : g (pair x) = g (pair y) := by
      funext i
      fin_cases i
      · exact congrFun hxy 1
      · exact congrFun hxy 2
    have hp := hg hpairImage
    funext i
    fin_cases i
    · exact hzero
    · exact congrFun hp 0
    · exact congrFun hp 1
    · exact hthree
  · intro z
    have hq := hqg (pair z)
    simp only [diagonalQuadratic, Fin.sum_univ_two] at hq
    dsimp [pair] at hq
    simp only [quaternionNormCoefficients, diagonalQuadratic,
      Fin.sum_univ_four]
    dsimp [f]
    simp only [one_mul]
    have hdetField := congrArg Units.val hdet
    simp only [Units.val_mul] at hdetField
    linear_combination -hq - z 3 ^ 2 * hdetField

/-- A norm witness for `t/s` gives the standard similitude between the two
quaternion norm forms with common first parameter. -/
theorem quaternionNorm_fixed_left_of_norm_ratio
    (a t s : Kˣ) (hnorm : IsQuadraticNorm K a (t / s)) :
    DiagonalRepresents (quaternionNormCoefficients a t)
      (quaternionNormCoefficients a s) := by
  rcases hnorm with ⟨x, y, hxy⟩
  let f : (Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
    { toFun := fun z => ![z 0, z 1,
          x * z 2 + (a : K) * y * z 3,
          y * z 2 + x * z 3]
      map_add' := by
        intro z w
        funext i
        fin_cases i <;> simp <;> ring
      map_smul' := by
        intro c z
        funext i
        fin_cases i <;> simp <;> ring }
  have hratioNe : (t : K) / (s : K) ≠ 0 :=
    div_ne_zero (Units.ne_zero t) (Units.ne_zero s)
  have hxy' : x ^ 2 - (a : K) * y ^ 2 = (t : K) / (s : K) := by
    simpa only [Units.val_div_eq_div_val] using hxy
  refine ⟨f, ?_, ?_⟩
  · intro z w hzw
    have hzero : z 0 = w 0 := congrFun hzw 0
    have hone : z 1 = w 1 := congrFun hzw 1
    have htwo := congrFun hzw 2
    have hthree := congrFun hzw 3
    change x * z 2 + (a : K) * y * z 3 =
      x * w 2 + (a : K) * y * w 3 at htwo
    change y * z 2 + x * z 3 = y * w 2 + x * w 3 at hthree
    have hcoordTwo : z 2 = w 2 := by
      have hmul : ((t : K) / (s : K)) * (z 2 - w 2) = 0 := by
        linear_combination x * htwo - (a : K) * y * hthree -
          (z 2 - w 2) * hxy'
      exact sub_eq_zero.mp
        ((mul_eq_zero.mp hmul).resolve_left hratioNe)
    have hcoordThree : z 3 = w 3 := by
      have hmul : ((t : K) / (s : K)) * (z 3 - w 3) = 0 := by
        linear_combination x * hthree - y * htwo -
          (z 3 - w 3) * hxy'
      exact sub_eq_zero.mp
        ((mul_eq_zero.mp hmul).resolve_left hratioNe)
    funext i
    fin_cases i
    · exact hzero
    · exact hone
    · exact hcoordTwo
    · exact hcoordThree
  · intro z
    simp only [quaternionNormCoefficients, diagonalQuadratic,
      Fin.sum_univ_four]
    dsimp [f]
    simp only [one_mul]
    have hscale : (s : K) * ((t : K) / (s : K)) = (t : K) := by
      field_simp [Units.ne_zero s]
    have hnormMul :
        (x * z 2 + (a : K) * y * z 3) ^ 2 -
            (a : K) * (y * z 2 + x * z 3) ^ 2 =
          ((t : K) / (s : K)) *
            (z 2 ^ 2 - (a : K) * z 3 ^ 2) := by
      calc
        _ = (x ^ 2 - (a : K) * y ^ 2) *
              (z 2 ^ 2 - (a : K) * z 3 ^ 2) := by ring
        _ = ((t : K) / (s : K)) *
              (z 2 ^ 2 - (a : K) * z 3 ^ 2) := by rw [hxy']
    calc
      z 0 ^ 2 + (-(a : K)) * z 1 ^ 2 +
            (-(s : K)) *
              (x * z 2 + (a : K) * y * z 3) ^ 2 +
            ((a : K) * (s : K)) *
              (y * z 2 + x * z 3) ^ 2 =
          z 0 ^ 2 - (a : K) * z 1 ^ 2 -
            (s : K) *
              ((x * z 2 + (a : K) * y * z 3) ^ 2 -
                (a : K) * (y * z 2 + x * z 3) ^ 2) := by ring
      _ = z 0 ^ 2 - (a : K) * z 1 ^ 2 -
            (s : K) * (((t : K) / (s : K)) *
              (z 2 ^ 2 - (a : K) * z 3 ^ 2)) := by rw [hnormMul]
      _ = z 0 ^ 2 - (a : K) * z 1 ^ 2 -
            (t : K) * (z 2 ^ 2 - (a : K) * z 3 ^ 2) := by
              rw [← mul_assoc, hscale]
      _ = z 0 ^ 2 + (-(a : K)) * z 1 ^ 2 +
            (-(t : K)) * z 2 ^ 2 +
              ((a : K) * (t : K)) * z 3 ^ 2 := by ring

end QuaternionNormForms

section QuaternionLocalClassification

variable [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K]

local instance localDefect : QuadraticDefectLaws K :=
  quadraticDefectLawsOfHensel K

noncomputable local instance localDiscriminant :
    DyadicDiscriminantClassLaws K :=
  dyadicDiscriminantClassLawsProved

noncomputable local instance localMaximalDefect :
    DyadicMaximalDefectClassLaws K :=
  dyadicMaximalDefectClassLawsProved

noncomputable local instance localUnramifiedNorm :
    DyadicUnramifiedNormLaws K :=
  dyadicUnramifiedNormLawsProvedDirect

/-- Representing `1` by `<a,b>` forces `b` to be a norm from `K(√a)`.
This is the elementary bridge between O'Meara 63:11 and quaternion symbols. -/
theorem isQuadraticNorm_of_binaryRepresents_one
    (a b : Kˣ) (h : BinaryRepresentsValue a b (1 : Kˣ)) :
    IsQuadraticNorm K a b := by
  rcases h with ⟨x, y, hxy⟩
  by_cases hy : y = 0
  · have hax : (a : K) * x ^ 2 = 1 := by
      simpa [hy] using hxy
    have hx : x ≠ 0 := by
      intro hx
      rw [hx] at hax
      norm_num at hax
    let s : Kˣ := Units.mk0 (1 / x) (one_div_ne_zero hx)
    have haSquare : IsSquare a := by
      refine ⟨s, ?_⟩
      apply Units.ext
      change (a : K) = (1 / x) * (1 / x)
      field_simp [hx]
      simpa [pow_two] using hax
    exact isQuadraticNorm_of_isSquare_left K haSquare
  · refine ⟨1 / y, x / y, ?_⟩
    change (1 / y) ^ 2 - (a : K) * (x / y) ^ 2 = (b : K)
    have hxy' : (a : K) * x ^ 2 + (b : K) * y ^ 2 = (1 : K) := by
      simpa using hxy
    have hrest : 1 - (a : K) * x ^ 2 = (b : K) * y ^ 2 := by
      linear_combination -hxy'
    calc
      (1 / y) ^ 2 - (a : K) * (x / y) ^ 2 =
          (1 - (a : K) * x ^ 2) / y ^ 2 := by ring
      _ = ((b : K) * y ^ 2) / y ^ 2 := by rw [hrest]
      _ = (b : K) := by field_simp [hy]

/-- Conversely, every quadratic norm gives a representation of `1` by the
associated binary form. -/
theorem binaryRepresents_one_of_isQuadraticNorm
    (a b : Kˣ) (h : IsQuadraticNorm K a b) :
    BinaryRepresentsValue a b (1 : Kˣ) := by
  rcases h with ⟨x, y, hxy⟩
  by_cases hx : x = 0
  · subst x
    have hy : y ≠ 0 := by
      intro hy
      subst y
      norm_num at hxy
      exact Units.ne_zero b hxy.symm
    refine ⟨((a : K) + 1) / (2 * (a : K)),
      ((a : K) - 1) / (2 * (a : K) * y), ?_⟩
    change (a : K) * (((a : K) + 1) / (2 * (a : K))) ^ 2 +
      (b : K) * (((a : K) - 1) / (2 * (a : K) * y)) ^ 2 = (1 : K)
    have hb : (b : K) = -(a : K) * y ^ 2 := by
      simpa using hxy.symm
    rw [hb]
    field_simp [Units.ne_zero a, hy]
    ring
  · refine ⟨y / x, 1 / x, ?_⟩
    change (a : K) * (y / x) ^ 2 + (b : K) * (1 / x) ^ 2 = (1 : K)
    field_simp [hx]
    rw [← hxy]
    ring

/-- A norm of the inverse second coefficient from the signed coefficient
ratio gives a representation of `1` by the original binary form. -/
private theorem binaryRepresents_one_of_norm_neg_div
    (a b : Kˣ)
    (h : IsQuadraticNorm K (-a / b) b⁻¹) :
    BinaryRepresentsValue a b (1 : Kˣ) := by
  rcases h with ⟨x, y, hxy⟩
  refine ⟨y, x, ?_⟩
  have hxy' : x ^ 2 - ((-a / b : Kˣ) : K) * y ^ 2 = ((b⁻¹ : Kˣ) : K) := hxy
  simp only [Units.val_div_eq_div_val, Units.val_neg,
    Units.val_inv_eq_inv_val] at hxy'
  have hbNe : (b : K) ≠ 0 := Units.ne_zero b
  field_simp [hbNe] at hxy'
  change (a : K) * y ^ 2 + (b : K) * x ^ 2 = (1 : K)
  linear_combination hxy'

/-- Elementary quaternion rotation on the norm relation.  It is the only
direction needed to transport a nonnorm hypothesis through `(a,b) ↦ (-ab,a)`. -/
private theorem isQuadraticNorm_of_rotated
    (a b : Kˣ)
    (h : IsQuadraticNorm K (-a * b) a) :
    IsQuadraticNorm K a b := by
  rcases h with ⟨x, y, hxy⟩
  by_cases hy : y = 0
  · have hxa : x ^ 2 = (a : K) := by
      simpa [hy] using hxy
    have hx : x ≠ 0 := by
      intro hx
      rw [hx] at hxa
      exact Units.ne_zero a (by simpa using hxa.symm)
    have haSquare : IsSquare a := by
      refine ⟨Units.mk0 x hx, ?_⟩
      apply Units.ext
      change (a : K) = x * x
      simpa [pow_two] using hxa.symm
    exact isQuadraticNorm_of_isSquare_left K haSquare
  · refine ⟨1 / y, x / ((a : K) * y), ?_⟩
    simp only [Units.val_mul, Units.val_neg] at hxy
    have haNe : (a : K) ≠ 0 := Units.ne_zero a
    change (1 / y) ^ 2 - (a : K) * (x / ((a : K) * y)) ^ 2 = (b : K)
    field_simp [haNe, hy]
    linear_combination -hxy

/-- The difficult even/even reduction: a binary unit form that does not
represent `1` must represent a nonzero scalar of odd valuation. -/
theorem exists_odd_value_of_unit_unit_nonnorm
    (a b : Kˣ)
    (haUnit : IsValuationUnit K (a : K))
    (hbUnit : IsValuationUnit K (b : K))
    (hnorm : ¬ IsQuadraticNorm K a b) :
    ∃ d : Kˣ, Odd (ordUnit K d) ∧ BinaryRepresentsValue a b d := by
  let q : Kˣ := -a / b
  have hqOrder : ordUnit K q = 0 := by
    have haOrder := (isValuationUnit_iff_ordUnit_eq_zero K a).1 haUnit
    have hbOrder := (isValuationUnit_iff_ordUnit_eq_zero K b).1 hbUnit
    dsimp only [q]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_neg, ordUnit_inv,
      haOrder, hbOrder]
    omega
  have hqUnit : IsValuationUnit K (q : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K q).2 hqOrder
  have hqNotSquare : ¬ IsSquare q := by
    intro hqSquare
    have hratioNorm : IsQuadraticNorm K q b⁻¹ :=
      isQuadraticNorm_of_isSquare_left K hqSquare
    exact hnorm (isQuadraticNorm_of_binaryRepresents_one a b
      (binaryRepresents_one_of_norm_neg_div a b hratioNorm))
  have hqFinite : quadraticDefect K q ≠ ⊤ := by
    intro htop
    exact hqNotSquare
      ((quadraticDefect_eq_top_iff_isSquare (K := K) q).mp htop)
  have hqBelowEndpoint : quadraticDefect K q <
      ((2 * ramificationIndex K : Nat) : ℕ∞) := by
    have hqUpper : quadraticDefect K q ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) :=
      quadraticDefect_le_two_mul_e_of_not_isSquare (K := K) hqNotSquare
    apply lt_of_le_of_ne hqUpper
    intro heq
    have hlarge : ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
        quadraticDefect K q := heq.ge
    rcases isSquare_or_isSquare_div_discriminant_of_defect_ge_twoE
        q hlarge with hsq | hdisc
    · exact hqNotSquare hsq
    · rcases hdisc with ⟨s, hs⟩
      let delta : Kˣ :=
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
      have hqFactor : q = delta * s ^ 2 := by
        calc
          q = (q / delta) * delta := by simp
          _ = (s * s) * delta := by rw [hs]
          _ = delta * s ^ 2 := by simp [pow_two, mul_comm]
      have hbInvEven : Even (ordUnit K b⁻¹) := by
        refine ⟨0, ?_⟩
        rw [ordUnit_inv,
          (isValuationUnit_iff_ordUnit_eq_zero K b).1 hbUnit]
        norm_num
      have hdeltaNorm : IsQuadraticNorm K delta b⁻¹ :=
        (isQuadraticNorm_discriminant_iff_even_order b⁻¹).2 hbInvEven
      have hqNorm : IsQuadraticNorm K q b⁻¹ := by
        rw [hqFactor]
        exact (isQuadraticNorm_mul_square_left_iff K delta b⁻¹ s).2
          hdeltaNorm
      exact hnorm (isQuadraticNorm_of_binaryRepresents_one a b
        (binaryRepresents_one_of_norm_neg_div a b hqNorm))
  have hqNonzeroDefect : quadraticDefect K q ≠ 0 := by
    intro hzero
    have hodd := odd_ordUnit_of_quadraticDefect_eq_zero q hzero
    rw [hqOrder] at hodd
    norm_num at hodd
  obtain ⟨v, r, t, hvUnit, hvDefect, hfactor, hvField, htOrder⟩ :=
    Bong.BONG.exists_exact_principal_representation q hqFinite hqNonzeroDefect
  let n : Nat := (quadraticDefect K q).toNat
  have hnOdd : Odd n := by
    have hvLt : quadraticDefect K v <
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
      rwa [hvDefect]
    have hvOdd := quadraticDefect_toNat_odd_of_unit_of_lt_two_mul_e
      (K := K) v hvUnit hvLt
    simpa only [hvDefect, n] using hvOdd
  have htOrderN : ord K t = ((n : Int) : WithTop Int) := by
    simpa only [n] using htOrder
  have htNe : t ≠ 0 := by
    apply (ord_eq_top_iff K).not.mp
    rw [htOrderN]
    exact WithTop.coe_ne_top
  let tu : Kˣ := Units.mk0 t htNe
  let d : Kˣ := -(b * tu)
  have hdOdd : Odd (ordUnit K d) := by
    have hbOrder := (isValuationUnit_iff_ordUnit_eq_zero K b).1 hbUnit
    have htuOrder : ordUnit K tu = (n : Int) := by
      apply WithTop.coe_injective
      rw [coe_ordUnit]
      exact htOrderN
    dsimp only [d]
    rw [ordUnit_neg, ordUnit_mul, hbOrder, htuOrder, zero_add]
    exact_mod_cast hnOdd
  have hqField : (q : K) = (v : K) * (r : K) ^ 2 := by
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using
      congrArg Units.val hfactor
  have hqDefinition : (a : K) = -(b : K) * (q : K) := by
    dsimp only [q]
    simp only [Units.val_div_eq_div_val, Units.val_neg]
    field_simp [Units.ne_zero b]
  have hvalue :
      (a : K) * ((r : K)⁻¹) ^ 2 + (b : K) * 1 ^ 2 = (d : K) := by
    dsimp only [d, tu]
    simp only [Units.val_neg, Units.val_mul, Units.val_mk0,
      one_pow, mul_one]
    change (a : K) * ((r : K)⁻¹) ^ 2 + (b : K) = -((b : K) * t)
    rw [hqDefinition, hqField, hvField]
    field_simp [Units.ne_zero r]
    ring
  refine ⟨d, hdOdd, ((r : K)⁻¹), 1, hvalue⟩

/-- A nonnorm prime binary pair has quaternion norm form isometric to one
with first parameter the distinguished unramified discriminant and second
parameter of odd valuation. -/
theorem quaternionNorm_to_discriminant_of_unit_odd_nonnorm
    (a b : Kˣ)
    (haUnit : IsValuationUnit K (a : K))
    (hbOdd : Odd (ordUnit K b))
    (hnorm : ¬ IsQuadraticNorm K a b) :
    ∃ t : Kˣ,
      Odd (ordUnit K t) ∧
        DiagonalRepresents (quaternionNormCoefficients a b)
          (quaternionNormCoefficients
            (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit t) := by
  let delta : Kˣ :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  have hchoice := primeBinary_represents_one_or_discriminant a b haUnit hbOdd
  have hdelta : BinaryRepresentsValue a b delta := by
    rcases hchoice with hone | hdelta
    · exact (hnorm (isQuadraticNorm_of_binaryRepresents_one a b hone)).elim
    · exact hdelta
  rcases hdelta with ⟨x, y, hxy⟩
  let t : Kˣ := a * b / delta
  have htOdd : Odd (ordUnit K t) := by
    have haOrder : ordUnit K a = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K a).1 haUnit
    have hdeltaOrder : ordUnit K delta = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K delta).1
        (inferInstance : DyadicDiscriminantClassLaws K).discriminant_isValuationUnit
    dsimp only [t]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_mul, ordUnit_inv,
      haOrder, hdeltaOrder]
    simpa using hbOdd
  have hdet : delta * t = a * b := by
    dsimp only [t]
    simp [mul_comm]
  have hbinary : DiagonalRepresents
      (fun i => ((![delta, t] : Fin 2 → Kˣ) i : K))
      (fun i => ((![a, b] : Fin 2 → Kˣ) i : K)) := by
    exact binaryChange_diagonalRepresents a b delta x y hxy
  have hforward : DiagonalRepresents
      (quaternionNormCoefficients delta t)
      (quaternionNormCoefficients a b) :=
    quaternionNorm_of_binary_change a b delta t hdet hbinary
  refine ⟨t, htOdd, ?_⟩
  exact DiagonalRepresents.symm_of_sameRank hforward

/-- All odd second parameters define the same quaternion norm form once the
first parameter is the unramified discriminant. -/
theorem quaternionNorm_discriminant_odd_isometric
    (t s : Kˣ)
    (htOdd : Odd (ordUnit K t))
    (hsOdd : Odd (ordUnit K s)) :
    DiagonalRepresents
      (quaternionNormCoefficients
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit t)
      (quaternionNormCoefficients
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit s) := by
  have hratioEven : Even (ordUnit K (t / s)) := by
    rcases htOdd with ⟨m, hm⟩
    rcases hsOdd with ⟨n, hn⟩
    refine ⟨m - n, ?_⟩
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv]
    omega
  have hnorm : IsQuadraticNorm K
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
      (t / s) :=
    (isQuadraticNorm_discriminant_iff_even_order (t / s)).2 hratioEven
  exact quaternionNorm_fixed_left_of_norm_ratio
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit t s hnorm

/-- The prime unit/odd nonnorm case is isometric to the fixed ramified
quaternion model `(Δ,π)`. -/
theorem quaternionNorm_to_standard_of_unit_odd_nonnorm
    (a b : Kˣ)
    (haUnit : IsValuationUnit K (a : K))
    (hbOdd : Odd (ordUnit K b))
    (hnorm : ¬ IsQuadraticNorm K a b) :
    DiagonalRepresents (quaternionNormCoefficients a b)
      (quaternionNormCoefficients
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
        (uniformizerPowerUnit K (1 : Int))) := by
  obtain ⟨t, htOdd, htoDelta⟩ :=
    quaternionNorm_to_discriminant_of_unit_odd_nonnorm
      a b haUnit hbOdd hnorm
  have hpiOdd : Odd (ordUnit K (uniformizerPowerUnit K (1 : Int))) := by
    rw [ordUnit_uniformizerPowerUnit]
    exact odd_one
  exact diagonalRepresents_trans htoDelta
    (quaternionNorm_discriminant_odd_isometric t
      (uniformizerPowerUnit K (1 : Int)) htOdd hpiOdd)

/-- Remove the even valuation of the first parameter by an explicit square
factor, preserving both the nonnorm condition and the quaternion norm form. -/
private theorem exists_even_left_normalization
    (a b : Kˣ)
    (haEven : Even (ordUnit K a))
    (hnorm : ¬ IsQuadraticNorm K a b) :
    ∃ u s : Kˣ,
      IsValuationUnit K (u : K) ∧
        a = u * s ^ 2 ∧
        ¬ IsQuadraticNorm K u b ∧
        DiagonalRepresents (quaternionNormCoefficients a b)
          (quaternionNormCoefficients u b) := by
  rcases haEven with ⟨k, hk⟩
  let s : Kˣ := uniformizerPowerUnit K k
  let u : Kˣ := a / s ^ 2
  have hsOrder : ordUnit K s = k :=
    ordUnit_uniformizerPowerUnit (K := K) k
  have huOrder : ordUnit K u = 0 := by
    dsimp only [u]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_pow,
      hsOrder]
    omega
  have huUnit : IsValuationUnit K (u : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K u).2 huOrder
  have hfactor : a = u * s ^ 2 := by
    dsimp only [u]
    simp
  have hnormU : ¬ IsQuadraticNorm K u b := by
    intro huNorm
    apply hnorm
    rw [hfactor]
    exact (isQuadraticNorm_mul_square_left_iff K u b s).2 huNorm
  have hrep : DiagonalRepresents (quaternionNormCoefficients a b)
      (quaternionNormCoefficients u b) := by
    rw [hfactor]
    exact quaternionNorm_mul_square_left u b s
  exact ⟨u, s, huUnit, hfactor, hnormU, hrep⟩

/-- Two odd parameters rotate to the unit/odd case after removal of one
even square factor. -/
private theorem quaternionNorm_to_standard_of_odd_odd_nonnorm
    (a b : Kˣ)
    (haOdd : Odd (ordUnit K a))
    (hbOdd : Odd (ordUnit K b))
    (hnorm : ¬ IsQuadraticNorm K a b) :
    DiagonalRepresents (quaternionNormCoefficients a b)
      (quaternionNormCoefficients
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
        (uniformizerPowerUnit K (1 : Int))) := by
  let c : Kˣ := -a * b
  have hcEven : Even (ordUnit K c) := by
    rcases haOdd with ⟨m, hm⟩
    rcases hbOdd with ⟨n, hn⟩
    refine ⟨m + n + 1, ?_⟩
    dsimp only [c]
    rw [ordUnit_mul, ordUnit_neg]
    omega
  have hnormC : ¬ IsQuadraticNorm K c a := by
    intro hcNorm
    exact hnorm (isQuadraticNorm_of_rotated a b (by simpa only [c] using hcNorm))
  obtain ⟨u, s, huUnit, hfactor, hnormU, hnormalize⟩ :=
    exists_even_left_normalization c a hcEven hnormC
  have hrotate : DiagonalRepresents (quaternionNormCoefficients a b)
      (quaternionNormCoefficients c a) := by
    exact DiagonalRepresents.symm_of_sameRank
      (by simpa only [c] using quaternionNorm_rotate a b)
  exact diagonalRepresents_trans (diagonalRepresents_trans hrotate hnormalize)
    (quaternionNorm_to_standard_of_unit_odd_nonnorm
      u a huUnit haOdd hnormU)

/-- O'Meara 63:11b in diagonal form: every nonsplit quaternion norm form
over the dyadic local field is isometric to the fixed model `(Δ,π)`. -/
theorem quaternionNorm_to_standard_of_nonnorm
    (a b : Kˣ) (hnorm : ¬ IsQuadraticNorm K a b) :
    DiagonalRepresents (quaternionNormCoefficients a b)
      (quaternionNormCoefficients
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
        (uniformizerPowerUnit K (1 : Int))) := by
  rcases Int.even_or_odd (ordUnit K a) with haEven | haOdd
  · rcases Int.even_or_odd (ordUnit K b) with hbEven | hbOdd
    · obtain ⟨u, su, huUnit, haFactor, hnormU, hnormalizeA⟩ :=
        exists_even_left_normalization a b haEven hnorm
      have hnormBU : ¬ IsQuadraticNorm K b u := by
        intro hbu
        exact hnormU (IsQuadraticNorm.symm K hbu)
      obtain ⟨v, sv, hvUnit, hbFactor, hnormV, hnormalizeB⟩ :=
        exists_even_left_normalization b u hbEven hnormBU
      have hswap : DiagonalRepresents (quaternionNormCoefficients u b)
          (quaternionNormCoefficients b u) :=
        quaternionNorm_swap u b
      have htoVU : DiagonalRepresents (quaternionNormCoefficients a b)
          (quaternionNormCoefficients v u) :=
        diagonalRepresents_trans
          (diagonalRepresents_trans hnormalizeA hswap) hnormalizeB
      obtain ⟨d, hdOdd, x, y, hvalue⟩ :=
        exists_odd_value_of_unit_unit_nonnorm
          v u hvUnit huUnit hnormV
      let e : Kˣ := v * u / d
      have heOdd : Odd (ordUnit K e) := by
        have hvOrder := (isValuationUnit_iff_ordUnit_eq_zero K v).1 hvUnit
        have huOrder := (isValuationUnit_iff_ordUnit_eq_zero K u).1 huUnit
        rcases hdOdd with ⟨k, hk⟩
        refine ⟨-k - 1, ?_⟩
        dsimp only [e]
        rw [div_eq_mul_inv, ordUnit_mul, ordUnit_mul, ordUnit_inv,
          hvOrder, huOrder]
        omega
      have hdet : d * e = v * u := by
        dsimp only [e]
        simp [mul_comm]
      have hbinary : DiagonalRepresents
          (fun i => ((![d, e] : Fin 2 → Kˣ) i : K))
          (fun i => ((![v, u] : Fin 2 → Kˣ) i : K)) := by
        exact binaryChange_diagonalRepresents v u d x y hvalue
      have hnormDE : ¬ IsQuadraticNorm K d e := by
        intro hde
        have honeDE := binaryRepresents_one_of_isQuadraticNorm d e hde
        have honeVU := binaryRepresentsValue_transport
          v u d e 1 honeDE hbinary
        exact hnormV (isQuadraticNorm_of_binaryRepresents_one v u honeVU)
      have htoDE : DiagonalRepresents
          (quaternionNormCoefficients v u)
          (quaternionNormCoefficients d e) := by
        exact DiagonalRepresents.symm_of_sameRank
          (quaternionNorm_of_binary_change v u d e hdet hbinary)
      exact diagonalRepresents_trans
        (diagonalRepresents_trans htoVU htoDE)
        (quaternionNorm_to_standard_of_odd_odd_nonnorm
          d e hdOdd heOdd hnormDE)
    · obtain ⟨u, s, huUnit, haFactor, hnormU, hnormalize⟩ :=
        exists_even_left_normalization a b haEven hnorm
      exact diagonalRepresents_trans hnormalize
        (quaternionNorm_to_standard_of_unit_odd_nonnorm
          u b huUnit hbOdd hnormU)
  · rcases Int.even_or_odd (ordUnit K b) with hbEven | hbOdd
    · have hnormBA : ¬ IsQuadraticNorm K b a := by
        intro hba
        exact hnorm (IsQuadraticNorm.symm K hba)
      obtain ⟨u, s, huUnit, hbFactor, hnormU, hnormalize⟩ :=
        exists_even_left_normalization b a hbEven hnormBA
      have hswap : DiagonalRepresents (quaternionNormCoefficients a b)
          (quaternionNormCoefficients b a) :=
        quaternionNorm_swap a b
      exact diagonalRepresents_trans
        (diagonalRepresents_trans hswap hnormalize)
        (quaternionNorm_to_standard_of_unit_odd_nonnorm
          u a huUnit haOdd hnormU)
    · exact quaternionNorm_to_standard_of_odd_odd_nonnorm
        a b haOdd hbOdd hnorm

/-- The nonzero values outside a quadratic norm subgroup form its single
nontrivial coset: the product of two nonnorms is a norm.  This is obtained
from uniqueness of the nonsplit quaternion norm form and two explicit Witt
cancellations. -/
theorem isQuadraticNorm_mul_of_not_isQuadraticNorm
    (a b c : Kˣ)
    (hb : ¬ IsQuadraticNorm K a b)
    (hc : ¬ IsQuadraticNorm K a c) :
    IsQuadraticNorm K a (b * c) := by
  have hstandardB := quaternionNorm_to_standard_of_nonnorm a b hb
  have hstandardC := quaternionNorm_to_standard_of_nonnorm a c hc
  have hiso : DiagonalRepresents (quaternionNormCoefficients a b)
      (quaternionNormCoefficients a c) :=
    diagonalRepresents_trans hstandardB
      (DiagonalRepresents.symm_of_sameRank hstandardC)
  let tailB : Fin 3 → K := ![-(a : K), -(b : K), (a : K) * (b : K)]
  let tailC : Fin 3 → K := ![-(a : K), -(c : K), (a : K) * (c : K)]
  have hsourceEq : quaternionNormCoefficients a b =
      Fin.cons (1 : K) tailB := by
    funext i
    fin_cases i <;> simp [quaternionNormCoefficients, tailB]
  have htargetEq : quaternionNormCoefficients a c =
      Fin.cons (1 : K) tailC := by
    funext i
    fin_cases i <;> simp [quaternionNormCoefficients, tailC]
  have hfull : DiagonalRepresents (Fin.cons (1 : K) tailB)
      (Fin.cons (1 : K) tailC) := by
    rw [← hsourceEq, ← htargetEq]
    exact hiso
  have htail3 : DiagonalRepresents tailB tailC := by
    apply DiagonalRepresents.cancel_common_head
      (1 : K) tailB tailC one_ne_zero
    · intro i
      fin_cases i <;> simp [tailB, Units.ne_zero]
    · intro i
      fin_cases i <;> simp [tailC, Units.ne_zero]
    · exact hfull
  let restB : Fin 2 → K := ![-(b : K), (a : K) * (b : K)]
  let restC : Fin 2 → K := ![-(c : K), (a : K) * (c : K)]
  have htail3' : DiagonalRepresents (Fin.cons (-(a : K)) restB)
      (Fin.cons (-(a : K)) restC) := by
    simpa [tailB, tailC, restB, restC] using htail3
  have htail2 : DiagonalRepresents restB restC := by
    apply DiagonalRepresents.cancel_common_head
      (-(a : K)) restB restC (neg_ne_zero.mpr (Units.ne_zero a))
    · intro i
      fin_cases i <;> simp [restB, Units.ne_zero]
    · intro i
      fin_cases i <;> simp [restC, Units.ne_zero]
    · exact htail3'
  rcases htail2 with ⟨f, hf, hqf⟩
  let e₀ : Fin 2 → K := ![1, 0]
  have hvalue := hqf e₀
  simp only [restB, restC, diagonalQuadratic, Fin.sum_univ_two] at hvalue
  dsimp [e₀] at hvalue
  simp only [one_pow, mul_one, zero_pow (by omega : 2 ≠ 0), mul_zero,
    add_zero] at hvalue
  have hratio : IsQuadraticNorm K a (b / c) := by
    refine ⟨f e₀ 0, f e₀ 1, ?_⟩
    change (f e₀ 0) ^ 2 - (a : K) * (f e₀ 1) ^ 2 =
      ((b / c : Kˣ) : K)
    simp only [Units.val_div_eq_div_val]
    have hcNe : (c : K) ≠ 0 := Units.ne_zero c
    field_simp [hcNe]
    linear_combination -hvalue
  have hscaled : IsQuadraticNorm K a ((b / c) * c ^ 2) :=
    (isQuadraticNorm_mul_square_right_iff K a (b / c) c).2 hratio
  simpa [div_eq_mul_inv, pow_two, mul_assoc, mul_comm, mul_left_comm]
    using hscaled

/-- Concrete right multiplicativity of the norm-equation Hilbert symbol. -/
theorem hilbertSymbol_map_mul_right_proved (a b c : Kˣ) :
    hilbertSymbol K a (b * c) =
      hilbertSymbol K a b * hilbertSymbol K a c :=
  hilbertSymbol_map_mul_right_of_nonnorm_mul_closed
    (fun a b c hb hc =>
      isQuadraticNorm_mul_of_not_isQuadraticNorm a b c hb hc)
    a b c

/-- All three local Hilbert-symbol laws, derived from explicit dyadic
quadratic-defect and quaternion calculations. -/
noncomputable instance hilbertSymbolLawsProved : HilbertSymbolLaws K where
  map_mul_right := hilbertSymbol_map_mul_right_proved
  nondegenerate := hilbertSymbol_nondegenerate_proved
  eq_one_of_defect_add_gt_two_mul_e :=
    hilbertSymbol_eq_one_of_defect_add_gt_two_mul_e_proved

end QuaternionLocalClassification

end Bong.Dyadic
