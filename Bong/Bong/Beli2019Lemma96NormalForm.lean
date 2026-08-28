/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma96
import Bong.Bong.Beli2019Lemma814HigherRankSegments
import Bong.Bong.Prefix
import Bong.Lattice.NormGeneratorValues

/-!
# Beli (2019), Lemma 9.6: the initial ternary normal form

For rank at least four, Lemma 9.6 isolates the first three BONG vectors and
applies the anisotropic branch of Lemma 9.5.  This file realizes that initial
block as the literal restriction of the parent lattice, transports both
alpha values to it, and obtains the integral unary--binary normal form.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {T : Nat}

/-- The canonical first-three prefix, including the proof that its integral
lattice is exactly the restriction of the parent lattice. -/
noncomputable def lemma96InitialThreePrefix
    (a : GoodBONG q L (T + 3)) :
    BONG.PrefixWitness a.toBONG 3 (by omega) :=
  a.toBONG.prefixWitness 3 (by omega)

/-- The first-three prefix as a good BONG. -/
noncomputable def lemma96InitialThree
    (a : GoodBONG q L (T + 3)) :
    GoodBONG
      (q.restrict a.lemma96InitialThreePrefix.carrier
        a.lemma96InitialThreePrefix.nondegenerate)
      a.lemma96InitialThreePrefix.lattice 3 :=
  a.lemma96InitialThreePrefix.toSegmentWitness.toGoodBONG a.good

/-- The local ternary values are the first three values of the parent. -/
@[simp]
theorem lemma96InitialThree_valueUnit_eq
    (a : GoodBONG q L (T + 3)) (i : Fin 3) :
    a.lemma96InitialThree.valueUnit i =
      a.valueUnit ⟨i.1, by omega⟩ := by
  let w := a.lemma96InitialThreePrefix
  change w.bong.valueUnit i = a.toBONG.valueUnit ⟨i.1, by omega⟩
  calc
    w.bong.valueUnit i =
        a.toBONG.valueUnit (w.toSegmentWitness.sourceIndex i) :=
      w.toSegmentWitness.valueUnit_eq i
    _ = a.toBONG.valueUnit ⟨i.1, by omega⟩ := by
      congr 1
      apply Fin.ext
      simp only [BONG.SegmentWitness.sourceIndex_val]
      omega

/-- The local ternary orders are the first three orders of the parent. -/
@[simp]
theorem lemma96InitialThree_order_eq
    (a : GoodBONG q L (T + 3)) (i : Fin 3) :
    a.lemma96InitialThree.order i = a.order ⟨i.1, by omega⟩ := by
  let w := a.lemma96InitialThreePrefix
  change w.bong.order i = a.toBONG.order ⟨i.1, by omega⟩
  calc
    w.bong.order i =
        a.toBONG.order (w.toSegmentWitness.sourceIndex i) :=
      w.toSegmentWitness.order_eq i
    _ = a.toBONG.order ⟨i.1, by omega⟩ := by
      congr 1
      apply Fin.ext
      simp only [BONG.SegmentWitness.sourceIndex_val]
      omega

/-- Prefix products of the literal initial ternary restriction agree with
the corresponding products in the parent BONG. -/
theorem lemma96InitialThree_prefixProduct_eq
    (a : GoodBONG q L (T + 3)) (k : Nat) (hk : k ≤ 3) :
    a.lemma96InitialThree.prefixProduct k = a.prefixProduct k := by
  induction k with
  | zero =>
      simp only [GoodBONG.prefixProduct, BONG.prefixProduct_zero]
  | succ k ih =>
      have hkThree : k < 3 := by omega
      have hkAmbient : k < T + 3 := by omega
      unfold GoodBONG.prefixProduct
      rw [a.lemma96InitialThree.toBONG.prefixProduct_succ k hkThree,
        a.toBONG.prefixProduct_succ k hkAmbient]
      have ih' := ih (by omega)
      change a.lemma96InitialThree.toBONG.prefixProduct k =
        a.toBONG.prefixProduct k at ih'
      rw [ih']
      congr 1
      exact a.lemma96InitialThree_valueUnit_eq ⟨k, hkThree⟩

/-- The diagonal coefficient function of the local ternary lattice is
literally the parent's first-three coefficient function. -/
theorem lemma96InitialThree_firstThreeValues_eq
    (a : GoodBONG q L (T + 3)) :
    a.lemma96InitialThree.lemma814FirstThreeValues =
      a.lemma814FirstThreeValues := by
  funext i
  unfold lemma814FirstThreeValues prefixValues
  rw [← a.lemma96InitialThree.coe_valueUnit, ← a.coe_valueUnit,
    a.lemma96InitialThree_valueUnit_eq]

/-- Isotropy of the first three entries is unchanged by passing to the
literal prefix lattice. -/
theorem lemma96InitialThree_isotropic_iff
    (a : GoodBONG q L (T + 3)) :
    a.lemma96InitialThree.Lemma814FirstThreeIsotropic ↔
      a.Lemma814FirstThreeIsotropic := by
  unfold Lemma814FirstThreeIsotropic
  rw [a.lemma96InitialThree_firstThreeValues_eq]

/-- Anisotropy of the first three entries is unchanged by passage to the
literal prefix lattice. -/
theorem lemma96InitialThree_anisotropic_iff
    (a : GoodBONG q L (T + 3)) :
    a.lemma96InitialThree.Lemma814FirstThreeAnisotropic ↔
      a.Lemma814FirstThreeAnisotropic := by
  unfold Lemma814FirstThreeAnisotropic
  rw [a.lemma96InitialThree_firstThreeValues_eq]

/-- The first global alpha localized to the first ternary prefix. -/
def lemma96InitialThreeFirstLocalization :
    AlphaLocalizationIndex (T + 2) where
  start := 0
  pivot := 0
  stop := 2
  start_le_pivot := by omega
  pivot_lt_stop := by omega
  stop_lt := by omega

/-- The second global alpha localized to the same ternary prefix. -/
def lemma96InitialThreeSecondLocalization :
    AlphaLocalizationIndex (T + 2) where
  start := 0
  pivot := 1
  stop := 2
  start_le_pivot := by omega
  pivot_lt_stop := by omega
  stop_lt := by omega

/-- A half-gap first alpha has the same value on the initial ternary
restriction. -/
theorem lemma96InitialThree_firstAlpha_eq
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (T + 3))
    (hhalf : a.AttainsHalfGap (0 : Fin (T + 2))) :
    a.lemma96InitialThree.alphaValue (0 : Fin 2) =
      a.alphaValue (0 : Fin (T + 2)) := by
  let p := lemma96InitialThreeFirstLocalization (T := T)
  let w := a.lemma96InitialThreePrefix
  have h := a.segmentAlpha_eq_global_of_attainsHalfGap
    p w.toSegmentWitness hhalf
  convert h using 1 <;> congr 1

/-- A half-gap second alpha has the same value on the initial ternary
restriction. -/
theorem lemma96InitialThree_secondAlpha_eq
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (T + 3))
    (hhalf : a.AttainsHalfGap (1 : Fin (T + 2))) :
    a.lemma96InitialThree.alphaValue (1 : Fin 2) =
      a.alphaValue (1 : Fin (T + 2)) := by
  let p := lemma96InitialThreeSecondLocalization (T := T)
  let w := a.lemma96InitialThreePrefix
  have h := a.segmentAlpha_eq_global_of_attainsHalfGap
    p w.toSegmentWitness hhalf
  convert h using 1 <;> congr 1

/-- The two exact alpha computations in Lemma 9.6 also provide the
half-gap hypotheses needed to localize them. -/
theorem lemma96_firstTwoAttainHalfGap
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (T + 3))
    (houter : a.order (0 : Fin (T + 3)) =
      a.order (2 : Fin (T + 3)))
    (hfirstGap :
      a.order (1 : Fin (T + 3)) - a.order (0 : Fin (T + 3)) =
        2 * (ramificationIndex K : Int) - 2) :
    a.AttainsHalfGap (0 : Fin (T + 2)) ∧
      a.AttainsHalfGap (1 : Fin (T + 2)) := by
  have hvalues := a.lemma96_firstTwoAlphaValues (by omega) houter (by
    convert hfirstGap using 1 <;> congr)
  have hfirstValue : a.alphaValue (0 : Fin (T + 2)) =
      ((2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) := by
    convert hvalues.1 using 1 <;> congr
  have hsecondValue : a.alphaValue (1 : Fin (T + 2)) = 1 := by
    convert hvalues.2 using 1 <;> congr
  constructor
  · unfold AttainsHalfGap
    have hgap : a.orderGap (0 : Fin (T + 2)) =
        2 * (ramificationIndex K : Int) - 2 := by
      change a.order (1 : Fin (T + 3)) - a.order (0 : Fin (T + 3)) = _
      exact hfirstGap
    rw [hfirstValue]
    unfold halfGapValue
    rw [hgap]
    push_cast
    ring
  · unfold AttainsHalfGap
    have hgap : a.orderGap (1 : Fin (T + 2)) =
        2 - 2 * (ramificationIndex K : Int) := by
      change a.order (2 : Fin (T + 3)) - a.order (1 : Fin (T + 3)) = _
      rw [← houter]
      omega
    rw [hsecondValue]
    unfold halfGapValue
    rw [hgap]
    push_cast
    ring

/-- Under the Lemma 9.6 order pattern, the first-three determinant is its
normalized unit part times the displayed uniformizer power. -/
theorem lemma96InitialThree_determinant_factor
    (a : GoodBONG q L (T + 3))
    (houter : a.order (0 : Fin (T + 3)) =
      a.order (2 : Fin (T + 3)))
    (hfirstGap :
      a.order (1 : Fin (T + 3)) - a.order (0 : Fin (T + 3)) =
        2 * (ramificationIndex K : Int) - 2) :
    uniformizerPowerUnit K
        (3 * a.order 0 + 2 * (ramificationIndex K : Int) - 2) *
      a.lemma96InitialThree.ternaryDeterminantUnitPart =
        a.prefixProduct 3 := by
  let s := a.lemma96InitialThree
  have horder : ordUnit K s.toBONG.valueProduct =
      3 * a.order 0 + 2 * (ramificationIndex K : Int) - 2 := by
    rw [s.toBONG.ordUnit_valueProduct_eq_sum_order,
      Fin.sum_univ_three]
    change s.order 0 + s.order 1 + s.order 2 = _
    rw [a.lemma96InitialThree_order_eq,
      a.lemma96InitialThree_order_eq,
      a.lemma96InitialThree_order_eq]
    change a.order 0 + a.order 1 + a.order 2 = _
    rw [houter]
    omega
  have hfactor :=
    uniformizerPower_mul_normalizedUnitPart K s.toBONG.valueProduct
  change uniformizerPowerUnit K (ordUnit K s.toBONG.valueProduct) *
      s.ternaryDeterminantUnitPart = s.toBONG.valueProduct at hfactor
  rw [horder] at hfactor
  rw [← s.prefixProduct_eq_valueProduct_of_rank_le 3 le_rfl,
    a.lemma96InitialThree_prefixProduct_eq 3 le_rfl] at hfactor
  exact hfactor

/-! ## Integral application of Lemma 9.5 -/

/-- The integral unary--binary normal form of the first ternary block.  The
three coefficient equalities are the displayed formulas in Lemma 9.6; the
last field is a genuine lattice isometry, not merely an ambient-space
classification. -/
structure Beli2019Lemma96InitialNormalFormData
    [laws : DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (T + 3)) where
  head : Kˣ
  first : Kˣ
  second : Kˣ
  admissible : IsBinaryParameterAdmissible (second / first)
  head_eq : head =
    -(uniformizerPowerUnit K (a.order 0) *
      a.lemma96InitialThree.ternaryDeterminantUnitPart *
        laws.discriminantUnit)
  first_eq : first = uniformizerPowerUnit K
    (a.order 0 + (2 * (ramificationIndex K : Int) - 1))
  second_eq : second =
    -(uniformizerPowerUnit K (a.order 0 - 1) * laws.discriminantUnit)
  latticeIsometry :
    Lattice.IsIsometric
      (q.restrict a.lemma96InitialThreePrefix.carrier
        a.lemma96InitialThreePrefix.nondegenerate)
      (unaryBinaryModelSpace head first second admissible)
      a.lemma96InitialThreePrefix.lattice
      (unaryBinaryModelLattice (K := K))

/-- Lemma 9.5(ii), anisotropic branch, applied to the literal first-three
restriction in Lemma 9.6. -/
theorem beli2019Lemma96_initialNormalForm
    [QuadraticDefectLaws K]
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [alphaSource : Beli2006AlphaLaws.{u, v} K]
    [alphaModel : Beli2006AlphaLaws.{u, u} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [GoodBONGClassificationLaws.{u, v, u} K]
    (a : GoodBONG q L (T + 3))
    (houter : a.order (0 : Fin (T + 3)) =
      a.order (2 : Fin (T + 3)))
    (hfirstGap :
      a.order (1 : Fin (T + 3)) - a.order (0 : Fin (T + 3)) =
        2 * (ramificationIndex K : Int) - 2)
    (hanisotropic : a.Lemma814FirstThreeAnisotropic) :
    Nonempty (Beli2019Lemma96InitialNormalFormData a) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaSource
  let s := a.lemma96InitialThree
  let A₁ : Int := 2 * (ramificationIndex K : Int) - 1
  let A₂ : Int := 1
  have hvalues := a.lemma96_firstTwoAlphaValues (by omega) houter (by
    convert hfirstGap using 1 <;> congr)
  have hhalf := a.lemma96_firstTwoAttainHalfGap houter hfirstGap
  have hlocalFirst := a.lemma96InitialThree_firstAlpha_eq hhalf.1
  have hlocalSecond := a.lemma96InitialThree_secondAlpha_eq hhalf.2
  have hA₁ : s.alphaValue (0 : Fin 2) = (A₁ : ℚ) := by
    change a.lemma96InitialThree.alphaValue (0 : Fin 2) = _
    rw [hlocalFirst]
    change a.alphaValue (0 : Fin (T + 2)) =
      ((2 * (ramificationIndex K : Int) - 1 : Int) : ℚ)
    convert hvalues.1 using 1 <;> congr
  have hA₂ : s.alphaValue (1 : Fin 2) = (A₂ : ℚ) := by
    change a.lemma96InitialThree.alphaValue (1 : Fin 2) = _
    rw [hlocalSecond]
    change a.alphaValue (1 : Fin (T + 2)) = (1 : ℚ)
    convert hvalues.2 using 1 <;> congr
  have hlocalOuter : s.order (0 : Fin 3) = s.order (2 : Fin 3) := by
    change a.lemma96InitialThree.order 0 =
      a.lemma96InitialThree.order 2
    rw [a.lemma96InitialThree_order_eq,
      a.lemma96InitialThree_order_eq]
    convert houter using 1 <;> congr
  have hlocalAnisotropic : s.Lemma814FirstThreeAnisotropic := by
    change a.lemma96InitialThree.Lemma814FirstThreeAnisotropic
    exact a.lemma96InitialThree_anisotropic_iff.mpr hanisotropic
  let values := s.beli2019Lemma95NormalFormValues
    A₁ A₂ laws.discriminantUnit
  let admissible :=
    s.beli2019Lemma95NormalForm_binaryAdmissible_discriminant
      hlocalOuter A₁ A₂ hA₁ hA₂
  have hisometry := s.beli2019Lemma95_ii_anisotropic
    (alphaSource := alphaSource) (alphaModel := alphaModel)
    hlocalOuter A₁ A₂ hA₁ hA₂ hlocalAnisotropic
  refine ⟨{
    head := values 0
    first := values 1
    second := values 2
    admissible := admissible
    head_eq := ?_
    first_eq := ?_
    second_eq := ?_
    latticeIsometry := hisometry }⟩
  · change values 0 = _
    dsimp only [values]
    rw [s.beli2019Lemma95NormalFormValues_zero,
      show s.order 0 = a.order 0 by
      change a.lemma96InitialThree.order 0 = a.order 0
      rw [a.lemma96InitialThree_order_eq]
      congr]
  · change values 1 = _
    dsimp only [values]
    rw [s.beli2019Lemma95NormalFormValues_one,
      show s.order 0 = a.order 0 by
      change a.lemma96InitialThree.order 0 = a.order 0
      rw [a.lemma96InitialThree_order_eq]
      congr]
  · change values 2 = _
    dsimp only [values]
    rw [s.beli2019Lemma95NormalFormValues_two,
      show s.order 0 = a.order 0 by
      change a.lemma96InitialThree.order 0 = a.order 0
      rw [a.lemma96InitialThree_order_eq]
      congr]

namespace Beli2019Lemma96InitialNormalFormData

variable [laws : DyadicDiscriminantClassLaws K]
  {a : GoodBONG q L (T + 3)}

/-- A chosen integral isometry realizing the normal form. -/
noncomputable def toIsometry
    (D : Beli2019Lemma96InitialNormalFormData a) :
    Lattice.Isometry
      (q.restrict a.lemma96InitialThreePrefix.carrier
        a.lemma96InitialThreePrefix.nondegenerate)
      (unaryBinaryModelSpace D.head D.first D.second D.admissible)
      a.lemma96InitialThreePrefix.lattice
      (unaryBinaryModelLattice (K := K)) :=
  Classical.choice D.latticeIsometry

/-- The distinguished unary vector, pulled back to the first-three
restriction. -/
noncomputable def localHead
    (D : Beli2019Lemma96InitialNormalFormData a) :
    a.lemma96InitialThreePrefix.carrier :=
  D.toIsometry.symm.toLinearEquiv ((1 : K), (0 : Fin 2 → K))

/-- The same vector in the ambient target space. -/
noncomputable def ambientHead
    (D : Beli2019Lemma96InitialNormalFormData a) : V :=
  D.localHead

/-- The pulled-back unary vector belongs to the literal prefix lattice. -/
theorem localHead_mem
    (D : Beli2019Lemma96InitialNormalFormData a) :
    D.localHead ∈ a.lemma96InitialThreePrefix.lattice := by
  apply (D.toIsometry.symm.map_mem
    ((1 : K), (0 : Fin 2 → K))).mp
  exact unaryBinaryModel_head_mem (K := K)

/-- Hence the selected vector belongs to the original target lattice. -/
theorem ambientHead_mem
    (D : Beli2019Lemma96InitialNormalFormData a) :
    D.ambientHead ∈ L := by
  exact a.lemma96InitialThreePrefix.contained D.localHead D.localHead_mem

/-- The selected vector has the displayed unary coefficient as its
quadratic value. -/
theorem localHead_quadratic
    (D : Beli2019Lemma96InitialNormalFormData a) :
    (q.restrict a.lemma96InitialThreePrefix.carrier
      a.lemma96InitialThreePrefix.nondegenerate).quadratic D.localHead =
        (D.head : K) := by
  have h := D.toIsometry.symm.map_quadratic
    ((1 : K), (0 : Fin 2 → K))
  simpa only [localHead, unaryBinaryModelSpace_quadratic_head] using h

/-- Ambient form of the preceding value identity. -/
theorem ambientHead_quadratic
    (D : Beli2019Lemma96InitialNormalFormData a) :
    q.quadratic D.ambientHead = (D.head : K) := by
  exact D.localHead_quadratic

/-- The new head has the same valuation order `R_1` as the original norm
generator. -/
theorem head_order
    (D : Beli2019Lemma96InitialNormalFormData a) :
    ordUnit K D.head = a.order 0 := by
  have hdet : ordUnit K
      a.lemma96InitialThree.ternaryDeterminantUnitPart = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K
      a.lemma96InitialThree.ternaryDeterminantUnitPart).1
      a.lemma96InitialThree.ternaryDeterminantUnitPart_isValuationUnit
  have hdelta : ordUnit K laws.discriminantUnit = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K laws.discriminantUnit).1
      laws.discriminant_isValuationUnit
  rw [D.head_eq, ordUnit_neg, ordUnit_mul, ordUnit_mul,
    ordUnit_uniformizerPowerUnit, hdet, hdelta]
  omega

/-- The distinguished unary vector is already a norm generator of the
literal first-three prefix lattice. -/
theorem localHead_isNormGenerator
    (D : Beli2019Lemma96InitialNormalFormData a) :
    Lattice.IsNormGenerator
      (q.restrict a.lemma96InitialThreePrefix.carrier
        a.lemma96InitialThreePrefix.nondegenerate)
      a.lemma96InitialThreePrefix.lattice D.localHead := by
  let s := a.lemma96InitialThree
  let old : Kˣ := s.valueUnit (0 : Fin 3)
  have hold : ordUnit K old = a.order 0 := by
    calc
      ordUnit K old = s.order (0 : Fin 3) :=
        (s.toBONG.order_eq_ordUnit 0).symm
      _ = a.order ⟨(0 : Fin 3).val, by omega⟩ :=
        a.lemma96InitialThree_order_eq 0
      _ = a.order 0 := by rfl
  have hratio : IsValuationUnit K ((old / D.head : Kˣ) : K) := by
    rw [isValuationUnit_iff_ordUnit_eq_zero, div_eq_mul_inv,
      ordUnit_mul, ordUnit_inv, hold, D.head_order]
    ring
  have hideal :
      Lattice.principalIdeal (K := K) (old : K) =
        Lattice.principalIdeal (K := K) (D.head : K) :=
    (Lattice.principalIdeal_eq_iff_isValuationUnit_div old D.head).2 hratio
  refine ⟨D.localHead_mem, ?_⟩
  calc
    Lattice.normIdeal
        (q.restrict a.lemma96InitialThreePrefix.carrier
          a.lemma96InitialThreePrefix.nondegenerate)
        a.lemma96InitialThreePrefix.lattice =
      Lattice.principalIdeal (K := K)
        ((q.restrict a.lemma96InitialThreePrefix.carrier
          a.lemma96InitialThreePrefix.nondegenerate).quadratic
            s.toBONG.head) :=
      s.toBONG.head_isNormGenerator.normIdeal_eq
    _ = Lattice.principalIdeal (K := K) (s.toBONG.value 0) :=
      congrArg (Lattice.principalIdeal (K := K))
        s.toBONG.value_zero_eq_quadratic_head.symm
    _ = Lattice.principalIdeal (K := K)
        (s.toBONG.valueUnit 0 : K) :=
      congrArg (Lattice.principalIdeal (K := K))
        (s.toBONG.coe_valueUnit 0).symm
    _ = Lattice.principalIdeal (K := K) (old : K) := rfl
    _ = Lattice.principalIdeal (K := K) (D.head : K) := hideal
    _ = Lattice.principalIdeal (K := K)
        ((q.restrict a.lemma96InitialThreePrefix.carrier
          a.lemma96InitialThreePrefix.nondegenerate).quadratic
            D.localHead) := by
      rw [D.localHead_quadratic]

/-- The first coefficient of the projected binary block has order
`R₁ + 2e - 1 = R₂ + 1`. -/
theorem first_order
    (D : Beli2019Lemma96InitialNormalFormData a) :
    ordUnit K D.first =
      a.order 0 + (2 * (ramificationIndex K : Int) - 1) := by
  rw [D.first_eq, ordUnit_uniformizerPowerUnit]

/-- The second coefficient of the projected binary block has order
`R₁ - 1 = R₃ - 1`. -/
theorem second_order
    (D : Beli2019Lemma96InitialNormalFormData a) :
    ordUnit K D.second = a.order 0 - 1 := by
  have hdelta : ordUnit K laws.discriminantUnit = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K
      laws.discriminantUnit).1 laws.discriminant_isValuationUnit
  rw [D.second_eq, ordUnit_neg, ordUnit_mul,
    ordUnit_uniformizerPowerUnit, hdelta]
  omega

/-- The pulled-back unary vector is anisotropic. -/
theorem ambientHead_anisotropic
    (D : Beli2019Lemma96InitialNormalFormData a) :
    q.IsAnisotropic D.ambientHead := by
  rw [QuadraticSpace.IsAnisotropic, D.ambientHead_quadratic]
  exact Units.ne_zero D.head

/-- The pulled-back unary vector is a norm generator of the full parent
lattice, because it lies in that lattice and has the same value order as the
original BONG head. -/
theorem ambientHead_isNormGenerator
    (D : Beli2019Lemma96InitialNormalFormData a) :
    Lattice.IsNormGenerator q L D.ambientHead := by
  let old : Kˣ := a.valueUnit (0 : Fin (T + 3))
  have hratio : IsValuationUnit K ((old / D.head : Kˣ) : K) := by
    rw [isValuationUnit_iff_ordUnit_eq_zero, div_eq_mul_inv,
      ordUnit_mul, ordUnit_inv]
    have hold : ordUnit K old = a.order 0 := by
      exact (a.toBONG.order_eq_ordUnit 0).symm
    rw [hold, D.head_order]
    omega
  have hideal :
      Lattice.principalIdeal (K := K) (old : K) =
        Lattice.principalIdeal (K := K) (D.head : K) :=
    (Lattice.principalIdeal_eq_iff_isValuationUnit_div old D.head).2 hratio
  refine ⟨D.ambientHead_mem, ?_⟩
  calc
    Lattice.normIdeal q L =
        Lattice.principalIdeal (K := K) (q.quadratic a.toBONG.head) :=
      a.toBONG.head_isNormGenerator.normIdeal_eq
    _ = Lattice.principalIdeal (K := K) (old : K) := by
      rw [← a.toBONG.value_zero_eq_quadratic_head,
        ← a.toBONG.coe_valueUnit]
      rfl
    _ = Lattice.principalIdeal (K := K) (D.head : K) := hideal
    _ = Lattice.principalIdeal (K := K) (q.quadratic D.ambientHead) := by
      rw [D.ambientHead_quadratic]

variable {W : Type w} [AddCommGroup W] [Module K W]
  {r : QuadraticSpace K W} {M : Lattice K W} {m : Nat}

/-- In the discriminant branch of the raw defect dichotomy, the unary
coefficient supplied by Lemma 9.5 has the same square class as the source
BONG head.  The even power appearing here is exactly
`4R₁ + 2e - 2`, as in the paper's unit-square normalization. -/
theorem valueRatio_isSquare_of_twistedRawSquare
    (D : Beli2019Lemma96InitialNormalFormData a)
    (b : GoodBONG r M (m + 1))
    (houter : a.order (0 : Fin (T + 3)) =
      a.order (2 : Fin (T + 3)))
    (hfirstGap :
      a.order (1 : Fin (T + 3)) - a.order (0 : Fin (T + 3)) =
        2 * (ramificationIndex K : Int) - 2)
    (htwisted : IsSquare
      (((-1) * a.prefixProduct 3 * b.prefixProduct 1) /
        laws.discriminantUnit)) :
    IsSquare (b.valueUnit (0 : Fin (m + 1)) / D.head) := by
  let unitPart :=
    a.lemma96InitialThree.ternaryDeterminantUnitPart
  let factor := a.prefixProduct 3 *
    uniformizerPowerUnit K (a.order 0) * unitPart
  have hfactorSquare : IsSquare factor := by
    have hdet := a.lemma96InitialThree_determinant_factor
      houter hfirstGap
    have hpower :
        uniformizerPowerUnit K
              (3 * a.order 0 + 2 * (ramificationIndex K : Int) - 2) *
            uniformizerPowerUnit K (a.order 0) =
          uniformizerPowerUnit K
            (4 * a.order 0 + 2 * (ramificationIndex K : Int) - 2) := by
      unfold uniformizerPowerUnit
      rw [← zpow_add]
      congr 1
      omega
    have hpowerSquare : IsSquare
        (uniformizerPowerUnit K
          (4 * a.order 0 + 2 * (ramificationIndex K : Int) - 2)) :=
      isSquare_uniformizerPowerUnit_of_even
        (K := K)
        (4 * a.order 0 + 2 * (ramificationIndex K : Int) - 2)
        ⟨2 * a.order 0 + (ramificationIndex K : Int) - 1, by omega⟩
    have hunitPartSquare : IsSquare (unitPart ^ 2) :=
      ⟨unitPart, by simp only [pow_two]⟩
    change IsSquare
      (a.prefixProduct 3 * uniformizerPowerUnit K (a.order 0) *
        unitPart)
    rw [← hdet]
    rw [show
        (uniformizerPowerUnit K
              (3 * a.order 0 + 2 * (ramificationIndex K : Int) - 2) *
            unitPart) * uniformizerPowerUnit K (a.order 0) * unitPart =
          (uniformizerPowerUnit K
              (3 * a.order 0 + 2 * (ramificationIndex K : Int) - 2) *
            uniformizerPowerUnit K (a.order 0)) * unitPart ^ 2 by
        simp only [pow_two]
        ac_rfl,
      hpower]
    exact hpowerSquare.mul hunitPartSquare
  have hbPrefix : b.prefixProduct 1 =
      b.valueUnit (0 : Fin (m + 1)) := by
    change b.toBONG.prefixProduct 1 = b.toBONG.valueUnit 0
    rw [b.toBONG.prefixProduct_succ 0 (by omega),
      BONG.prefixProduct_zero]
    simp
  have hreorder :
      (((-1 : Kˣ) * a.prefixProduct 3 * b.prefixProduct 1) /
          laws.discriminantUnit) / factor =
        b.valueUnit (0 : Fin (m + 1)) / D.head := by
    dsimp only [factor, unitPart]
    rw [hbPrefix, D.head_eq]
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_neg,
      Units.val_one]
    field_simp [Units.ne_zero laws.discriminantUnit,
      Units.ne_zero (a.prefixProduct 3),
      Units.ne_zero (uniformizerPowerUnit K (a.order 0)),
      Units.ne_zero
        a.lemma96InitialThree.ternaryDeterminantUnitPart]
  have hquotient := htwisted.div hfactorSquare
  rw [hreorder] at hquotient
  exact hquotient

/-- The exact matched-head datum needed by the projected rank reduction in
Lemma 9.6.  The target vector is a norm generator and represents the source
BONG head value, not merely its valuation ideal. -/
structure MatchedHeadData
    (D : Beli2019Lemma96InitialNormalFormData a)
    (b : GoodBONG r M (m + 1)) where
  /-- The valuation-unit square root used in the final normalization. -/
  scalar : Kˣ
  /-- The scalar preserves the integral unary summand. -/
  scalar_isValuationUnit : IsValuationUnit K (scalar : K)
  vector : V
  /-- The matched vector is the displayed scalar multiple of the unary
  normal-form vector.  Retaining this equality is essential for computing
  its orthogonal projection geometrically. -/
  vector_eq : vector = (scalar : K) • D.ambientHead
  isNormGenerator : Lattice.IsNormGenerator q L vector
  quadratic_eq : q.quadratic vector =
    (b.valueUnit (0 : Fin (m + 1)) : K)

namespace MatchedHeadData

/-- A matched head is automatically anisotropic, since its value is the
nonzero first diagonal coefficient of the source BONG. -/
theorem anisotropic
    {D : Beli2019Lemma96InitialNormalFormData a}
    {b : GoodBONG r M (m + 1)}
    (E : MatchedHeadData D b) :
    q.IsAnisotropic E.vector := by
  rw [QuadraticSpace.IsAnisotropic, E.quadratic_eq]
  exact Units.ne_zero (b.valueUnit (0 : Fin (m + 1)))

end MatchedHeadData

/-- Once the displayed normal-form head and the source BONG head have the
same square class and order, scaling by the square root of their ratio gives
a target norm generator whose quadratic value is exactly the source value.
This is the final unit-square normalization in the proof of Lemma 9.6. -/
theorem exists_matchedHead
    (D : Beli2019Lemma96InitialNormalFormData a)
    (b : GoodBONG r M (m + 1))
    (horder : b.order (0 : Fin (m + 1)) = a.order 0)
    (hsquare : IsSquare
      (b.valueUnit (0 : Fin (m + 1)) / D.head)) :
    Nonempty (MatchedHeadData D b) := by
  rcases hsquare with ⟨s, hs⟩
  have hbOrder :
      ordUnit K (b.valueUnit (0 : Fin (m + 1))) = b.order 0 := by
    exact (b.toBONG.order_eq_ordUnit 0).symm
  have hratioOrder :
      ordUnit K (b.valueUnit (0 : Fin (m + 1)) / D.head) = 0 := by
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
      hbOrder, D.head_order, horder]
    omega
  have hsOrder : ordUnit K s = 0 := by
    have h := congrArg (ordUnit K) hs
    rw [ordUnit_mul, hratioOrder] at h
    omega
  have hsUnit : IsValuationUnit K (s : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K s).2 hsOrder
  have hvalueUnit :
      s ^ 2 * D.head = b.valueUnit (0 : Fin (m + 1)) := by
    rw [pow_two, ← hs]
    simp
  refine ⟨
    { scalar := s
      scalar_isValuationUnit := hsUnit
      vector := (s : K) • D.ambientHead
      vector_eq := rfl
      isNormGenerator := D.ambientHead_isNormGenerator.smul_valuationUnit s hsUnit
      quadratic_eq := ?_ }⟩
  rw [q.quadratic_smul, D.ambientHead_quadratic]
  exact congrArg (fun z : Units K => (z : K)) hvalueUnit

end Beli2019Lemma96InitialNormalFormData

variable {W : Type w} [AddCommGroup W] [Module K W]
  {r : QuadraticSpace K W} {M : Lattice K W}

/-- The complete normal-form head package in the discriminant square-class
branch: it retains the integral ternary normal form together with the actual
full-lattice vector whose value is the source BONG head. -/
structure Beli2019Lemma96MatchedNormalFormData
    [DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (T + 3))
    (b : GoodBONG r M (T + 3)) where
  normalForm : Beli2019Lemma96InitialNormalFormData a
  matchedHead : normalForm.MatchedHeadData b
  /-- The discriminant-twisted raw prefix square class selecting this
  branch.  Retaining the certificate is needed for the exceptional
  `d[-a'_{2,3}] = 2e` calculation later in Lemma 9.6. -/
  twistedRawSquare : IsSquare
    (((-1) * a.prefixProduct 3 * b.prefixProduct 1) /
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)

/-- The discriminant branch of Lemma 9.6 now constructs the exact target
head used for the subsequent orthogonal-projection reduction. -/
theorem beli2019Lemma96_matchedNormalForm_of_twistedRawSquare
    [QuadraticDefectLaws K]
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [targetAlpha : Beli2006AlphaLaws.{u, v} K]
    [modelAlpha : Beli2006AlphaLaws.{u, u} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [GoodBONGClassificationLaws.{u, v, u} K]
    (a : GoodBONG q L (T + 3))
    (b : GoodBONG r M (T + 3))
    (houter : a.order (0 : Fin (T + 3)) =
      a.order (2 : Fin (T + 3)))
    (hfirstGap :
      a.order (1 : Fin (T + 3)) - a.order (0 : Fin (T + 3)) =
        2 * (ramificationIndex K : Int) - 2)
    (hanisotropic : a.Lemma814FirstThreeAnisotropic)
    (hsourceOrder : b.order (0 : Fin (T + 3)) = a.order 0)
    (htwisted : IsSquare
      (((-1) * a.prefixProduct 3 * b.prefixProduct 1) /
        laws.discriminantUnit)) :
    Nonempty (Beli2019Lemma96MatchedNormalFormData a b) := by
  rcases a.beli2019Lemma96_initialNormalForm
      (alphaSource := targetAlpha) (alphaModel := modelAlpha)
      houter hfirstGap hanisotropic with ⟨D⟩
  have hsquare := D.valueRatio_isSquare_of_twistedRawSquare
    b houter hfirstGap htwisted
  rcases D.exists_matchedHead b hsourceOrder hsquare with ⟨E⟩
  exact ⟨⟨D, E, htwisted⟩⟩

/-- Combining the maximal-defect square-class dichotomy with the preceding
construction leaves exactly the one branch treated by the paper's
Lemma 2.19 / rank-four `Δ`-scaling argument. -/
theorem beli2019Lemma96_squareRaw_or_matchedNormalForm
    [QuadraticDefectLaws K]
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicMaximalDefectClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [targetAlpha : Beli2006AlphaLaws.{u, v} K]
    [modelAlpha : Beli2006AlphaLaws.{u, u} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [GoodBONGClassificationLaws.{u, v, u} K]
    (a : GoodBONG q L (T + 3))
    (b : GoodBONG r M (T + 3))
    (houter : a.order (0 : Fin (T + 3)) =
      a.order (2 : Fin (T + 3)))
    (hfirstGap :
      a.order (1 : Fin (T + 3)) - a.order (0 : Fin (T + 3)) =
        2 * (ramificationIndex K : Int) - 2)
    (hanisotropic : a.Lemma814FirstThreeAnisotropic)
    (hsourceOrder : b.order (0 : Fin (T + 3)) = a.order 0)
    (hdefect : a.Beli2019Lemma96DefectBound b) :
    IsSquare ((-1) * a.prefixProduct 3 * b.prefixProduct 1) ∨
      Nonempty (Beli2019Lemma96MatchedNormalFormData a b) := by
  rcases a.lemma96_rawSquareClassCases b hdefect with
    hsquare | htwisted
  · exact Or.inl hsquare
  · exact Or.inr
      (a.beli2019Lemma96_matchedNormalForm_of_twistedRawSquare b
        (targetAlpha := targetAlpha) (modelAlpha := modelAlpha)
        houter hfirstGap hanisotropic hsourceOrder htwisted)

end BONG.GoodBONG

end Bong
