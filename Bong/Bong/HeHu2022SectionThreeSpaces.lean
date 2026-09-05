/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.HeHu2022SectionThreeBinary
import Bong.Bong.AlternatingEndpointOddNormalForm
import Bong.Bong.BeliUniversalAnisotropicQuaternary
import Bong.Bong.DiagonalTernaryRepresentationObstructionProof
import Bong.Bong.DiagonalTailCancellation
import Bong.Bong.DiagonalHyperbolicBlocks
import Bong.Dyadic.UnramifiedNormProof

/-!
# He--Hu (2024), Definition 3.4 and the space classification in Proposition 3.5

The coefficient families in this file are the rows of Table 1, organized by
the actual square-class tests used in the published proof.  An even dimension
is written `2*pairs+2` and an odd dimension at least three is written
`2*pairs+3`.  Equal-rank diagonal representation is the repository's concrete
isometry relation.
-/

namespace Bong

open Dyadic BONG.GoodBONG
open AlternatingEndpointTower

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Transport a finite coefficient family across an arithmetic equality of
its dimension. -/
def heHuFinFamilyCast {α : Type*} {m n : Nat} (h : m = n)
    (a : Fin m → α) : Fin n → α :=
  fun i => a (Fin.cast h.symm i)

/-- The residual `H perp [c]` in the odd-dimensional first column. -/
def heHuOddFirstTail (c : Kˣ) : Fin 3 → Kˣ := ![1, -1, c]

/-- The standard diagonal hyperbolic pair `[1,-1]`. -/
def heHuHyperbolicPair : Fin 2 → Kˣ := ![1, -1]

/-- The four-dimensional residual block `H perp [1,-c]`. -/
def heHuEvenFirstTail (c : Kˣ) : Fin 4 → Kˣ :=
  Fin.append (heHuHyperbolicPair (K := K)) (heHuBinaryFirst c)

/-- Definition 3.4(i): `W_1^{2*pairs+2}(c)`.  The successor clause groups
the last hyperbolic plane with the binary endpoint so that Table 1
nonisometry is a literal common-head cancellation. -/
def heHuEvenFirst : (pairs : Nat) → (c : Kˣ) →
    Fin (2 * pairs + 2) → Kˣ
  | 0, c => heHuBinaryFirst c
  | pairs + 1, c => heHuFinFamilyCast (by omega)
      (Fin.append (standardHyperbolicEndpointTower (K := K) pairs)
        (heHuEvenFirstTail c))

/-- Definition 3.4(ii): `W_1^{2*pairs+3}(c)`. -/
def heHuOddFirst (pairs : Nat) (c : Kˣ) :
    Fin (2 * pairs + 3) → Kˣ :=
  Fin.append (standardHyperbolicEndpointTower (K := K) pairs)
    (heHuOddFirstTail c)

/-- The only undefined `W_2` case is dimension two with square `c`. -/
def HeHuEvenSecondDefined (pairs : Nat) (c : Kˣ) : Prop :=
  0 < pairs ∨ ¬ IsSquare c

/-- The binary row `[pi,-Delta*pi]`. -/
noncomputable def heHuDiscriminantBinary (c : Kˣ) : Fin 2 → Kˣ :=
  heHuBinaryTwist c (uniformizerPowerUnit K (1 : Int))

/-- The even-valuation anisotropic ternary row
`[pi,-Delta*pi,Delta*c]`. -/
noncomputable def heHuOddSecondTailEven (c : Kˣ) : Fin 3 → Kˣ :=
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let pi := uniformizerPowerUnit K (1 : Int)
  ![pi, -(delta * pi), delta * c]

/-- The odd-valuation anisotropic ternary row `[1,-Delta,Delta*c]`. -/
noncomputable def heHuOddSecondTailOdd (c : Kˣ) : Fin 3 → Kˣ :=
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  ![1, -delta, delta * c]

/-- The four-dimensional residual block `H perp [pi,-pi*c]`. -/
noncomputable def heHuEvenDiscriminantTail (c : Kˣ) : Fin 4 → Kˣ :=
  Fin.append (heHuHyperbolicPair (K := K))
    (heHuDiscriminantBinary c)

/-- The four-dimensional residual block `H perp [c#,-c#*c]`. -/
noncomputable def heHuEvenSharpTail (c : Kˣ)
    (hc : HeHuSharpDomain c) : Fin 4 → Kˣ :=
  Fin.append (heHuHyperbolicPair (K := K))
    (heHuBinarySecond c hc)

/-- Definition 3.4(i) and Table 1, even-dimensional second column. -/
noncomputable def heHuEvenSecond (pairs : Nat) (c : Kˣ)
    (hdefined : HeHuEvenSecondDefined pairs c) :
    Fin (2 * pairs + 2) → Kˣ := by
  classical
  cases pairs with
  | zero =>
      have hnonsquare : ¬ IsSquare c := by
        rcases hdefined with hp | hn
        · omega
        · exact hn
      let delta :=
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
      by_cases hdelta : IsSquare (c / delta)
      · exact heHuDiscriminantBinary c
      · exact heHuBinarySecond c
          { notSquare := hnonsquare
            notDiscriminantSquare := hdelta }
  | succ pairs =>
      by_cases hsquare : IsSquare c
      · exact heHuFinFamilyCast (by omega)
          (Fin.append
            (standardHyperbolicEndpointTower (K := K) pairs)
            (beliAnisotropicQuaternaryUnits (K := K)))
      · let delta :=
          (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
        by_cases hdelta : IsSquare (c / delta)
        · exact heHuFinFamilyCast (by omega)
            (Fin.append
              (standardHyperbolicEndpointTower (K := K) pairs)
              (heHuEvenDiscriminantTail c))
        · exact heHuFinFamilyCast (by omega)
            (Fin.append
              (standardHyperbolicEndpointTower (K := K) pairs)
              (heHuEvenSharpTail c
                { notSquare := hsquare
                  notDiscriminantSquare := hdelta }))

/-- Definition 3.4(ii) and Table 1, odd-dimensional second column. -/
noncomputable def heHuOddSecond (pairs : Nat) (c : Kˣ) :
    Fin (2 * pairs + 3) → Kˣ := by
  classical
  by_cases heven : Even (ordUnit K c)
  · exact Fin.append
      (standardHyperbolicEndpointTower (K := K) pairs)
      (heHuOddSecondTailEven c)
  · exact Fin.append
      (standardHyperbolicEndpointTower (K := K) pairs)
      (heHuOddSecondTailOdd c)

theorem heHuOddSecond_of_even (pairs : Nat) (c : Kˣ)
    (heven : Even (ordUnit K c)) :
    heHuOddSecond pairs c =
      Fin.append (standardHyperbolicEndpointTower (K := K) pairs)
        (heHuOddSecondTailEven c) := by
  simp [heHuOddSecond, heven]

theorem heHuOddSecond_of_not_even (pairs : Nat) (c : Kˣ)
    (heven : ¬ Even (ordUnit K c)) :
    heHuOddSecond pairs c =
      Fin.append (standardHyperbolicEndpointTower (K := K) pairs)
        (heHuOddSecondTailOdd c) := by
  simp [heHuOddSecond, heven]

theorem heHuEvenSecond_zero_of_discriminant
    (c : Kˣ) (hdefined : HeHuEvenSecondDefined 0 c)
    (hdelta : IsSquare (c /
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)) :
    heHuEvenSecond 0 c hdefined = heHuDiscriminantBinary c := by
  simp [heHuEvenSecond, hdelta]

theorem heHuEvenSecond_zero_of_sharp
    (c : Kˣ) (hdefined : HeHuEvenSecondDefined 0 c)
    (hnonsquare : ¬ IsSquare c)
    (hdelta : ¬ IsSquare (c /
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)) :
    heHuEvenSecond 0 c hdefined =
      heHuBinarySecond c
        { notSquare := hnonsquare
          notDiscriminantSquare := hdelta } := by
  simp [heHuEvenSecond, hdelta]

theorem heHuEvenSecond_succ_of_square
    (pairs : Nat) (c : Kˣ)
    (hdefined : HeHuEvenSecondDefined (pairs + 1) c)
    (hsquare : IsSquare c) :
    heHuEvenSecond (pairs + 1) c hdefined =
      heHuFinFamilyCast (by omega)
        (Fin.append (standardHyperbolicEndpointTower (K := K) pairs)
          (beliAnisotropicQuaternaryUnits (K := K))) := by
  simp [heHuEvenSecond, hsquare]

theorem heHuEvenSecond_succ_of_discriminant
    (pairs : Nat) (c : Kˣ)
    (hdefined : HeHuEvenSecondDefined (pairs + 1) c)
    (hnonsquare : ¬ IsSquare c)
    (hdelta : IsSquare (c /
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)) :
    heHuEvenSecond (pairs + 1) c hdefined =
      heHuFinFamilyCast (by omega)
        (Fin.append (standardHyperbolicEndpointTower (K := K) pairs)
          (heHuEvenDiscriminantTail c)) := by
  simp [heHuEvenSecond, hnonsquare, hdelta]

theorem heHuEvenSecond_succ_of_sharp
    (pairs : Nat) (c : Kˣ)
    (hdefined : HeHuEvenSecondDefined (pairs + 1) c)
    (hnonsquare : ¬ IsSquare c)
    (hdelta : ¬ IsSquare (c /
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)) :
    heHuEvenSecond (pairs + 1) c hdefined =
      heHuFinFamilyCast (by omega)
        (Fin.append (standardHyperbolicEndpointTower (K := K) pairs)
          (heHuEvenSharpTail c
            { notSquare := hnonsquare
              notDiscriminantSquare := hdelta })) := by
  simp [heHuEvenSecond, hnonsquare, hdelta]

/-- Cancel a common diagonal head when proving that two displayed Table 1
rows are nonisometric. -/
theorem not_represents_append_of_not_tail {head tail : Nat}
    (common : Fin head → Kˣ) (source target : Fin tail → Kˣ)
    (hnot : ¬ DiagonalRepresents
      (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients target)) :
    ¬ DiagonalRepresents
      (diagonalUnitCoefficients (Fin.append common source))
      (diagonalUnitCoefficients (Fin.append common target)) := by
  intro hfull
  apply hnot
  apply DiagonalRepresents.cancel_common_prefix
    (diagonalUnitCoefficients common)
    (diagonalUnitCoefficients source)
    (diagonalUnitCoefficients target)
  · exact fun i => Units.ne_zero (common i)
  · exact fun i => Units.ne_zero (source i)
  · exact fun i => Units.ne_zero (target i)
  · simpa only [diagonalUnitCoefficients_append] using hfull

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
@[simp] theorem diagonalUnitDeterminant_heHuFinFamilyCast
    {m n : Nat} (h : m = n) (a : Fin m → Kˣ) :
    diagonalUnitDeterminant (heHuFinFamilyCast h a) =
      diagonalUnitDeterminant a := by
  subst n
  rfl

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
@[simp] theorem diagonalUnitCoefficients_heHuFinFamilyCast
    {m n : Nat} (h : m = n) (a : Fin m → Kˣ) :
    diagonalUnitCoefficients (heHuFinFamilyCast h a) =
      heHuFinFamilyCast h (diagonalUnitCoefficients a) := by
  subst n
  rfl

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
/-- Reindexing both equal-rank diagonal forms across the same arithmetic
dimension equality preserves the isometry relation. -/
theorem diagonalRepresents_heHuFinFamilyCast_iff
    {m n : Nat} (h : m = n) (source target : Fin m → Kˣ) :
    DiagonalRepresents
        (diagonalUnitCoefficients (heHuFinFamilyCast h source))
        (diagonalUnitCoefficients (heHuFinFamilyCast h target)) ↔
      DiagonalRepresents
        (diagonalUnitCoefficients source)
        (diagonalUnitCoefficients target) := by
  subst n
  rfl

/-- Appending a common nondegenerate head preserves equality of determinant
square classes. -/
theorem determinantSquare_append_of_tail {head tail : Nat}
    (common : Fin head → Kˣ) (source target : Fin tail → Kˣ)
    (htail : IsSquare
      (diagonalUnitDeterminant source *
        diagonalUnitDeterminant target)) :
    IsSquare
      (diagonalUnitDeterminant (Fin.append common source) *
        diagonalUnitDeterminant (Fin.append common target)) := by
  have hcommon : IsSquare (diagonalUnitDeterminant common ^ 2) :=
    ⟨diagonalUnitDeterminant common, pow_two _⟩
  have h := hcommon.mul htail
  rw [diagonalUnitDeterminant_append,
    diagonalUnitDeterminant_append]
  simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using h

/-- A two-class exhaustion from determinant equality and one verified
nonisometric partner. -/
theorem heHuTwoClass_exhaustive {n : Nat}
    (first second : Fin n → Kˣ)
    (hdet : IsSquare
      (diagonalUnitDeterminant second *
        diagonalUnitDeterminant first))
    (hnot : ¬ DiagonalRepresents
      (diagonalUnitCoefficients second)
      (diagonalUnitCoefficients first))
    (w : Fin n → Kˣ)
    (hwdet : IsSquare
      (diagonalUnitDeterminant w *
        diagonalUnitDeterminant first)) :
    DiagonalRepresents
        (diagonalUnitCoefficients w)
        (diagonalUnitCoefficients first) ∨
      DiagonalRepresents
        (diagonalUnitCoefficients w)
        (diagonalUnitCoefficients second) := by
  by_cases hwHasse :
      diagonalHasseSymbol K w = diagonalHasseSymbol K first
  · exact Or.inl (dyadicDiagonalClassification_represents
      n w first hwdet hwHasse)
  · right
    have hsecondHasseNe :
        diagonalHasseSymbol K second ≠
          diagonalHasseSymbol K first := by
      intro hhasse
      exact hnot (dyadicDiagonalClassification_represents
        n second first hdet hhasse)
    have hwSecondHasse : diagonalHasseSymbol K w =
        diagonalHasseSymbol K second := by
      rcases Int.units_eq_one_or (diagonalHasseSymbol K first) with
          hfirst | hfirst <;>
        rcases Int.units_eq_one_or (diagonalHasseSymbol K second) with
          hsecond | hsecond <;>
        rcases Int.units_eq_one_or (diagonalHasseSymbol K w) with
          hw | hw <;>
        simp [hfirst, hsecond, hw] at hwHasse hsecondHasseNe ⊢
    have hfirstSecond : IsSquare
        (diagonalUnitDeterminant first *
          diagonalUnitDeterminant second) := by
      simpa only [mul_comm] using hdet
    have hwSecondDet : IsSquare
        (diagonalUnitDeterminant w *
          diagonalUnitDeterminant second) :=
      isSquare_mul_trans
        (diagonalUnitDeterminant w)
        (diagonalUnitDeterminant first)
        (diagonalUnitDeterminant second) hwdet hfirstSecond
    exact dyadicDiagonalClassification_represents
      n w second hwSecondDet hwSecondHasse

/-- The exact determinant, nonisometry, and two-class exhaustiveness package
attached to each defined pair in Definition 3.4. -/
structure HeHuSpacePairProperties {n : Nat}
    (first second : Fin n → Kˣ) : Prop where
  determinantSquare : IsSquare
    (diagonalUnitDeterminant second *
      diagonalUnitDeterminant first)
  nonisometric : ¬ DiagonalRepresents
    (diagonalUnitCoefficients second)
    (diagonalUnitCoefficients first)
  exhaustive (w : Fin n → Kˣ) :
    IsSquare
        (diagonalUnitDeterminant w *
          diagonalUnitDeterminant first) →
      DiagonalRepresents
          (diagonalUnitCoefficients w)
          (diagonalUnitCoefficients first) ∨
        DiagonalRepresents
          (diagonalUnitCoefficients w)
          (diagonalUnitCoefficients second)

/-- Determinant equality and nonisometry generate the complete two-class
package by the local determinant--Hasse classification. -/
theorem HeHuSpacePairProperties.of_det_not {n : Nat}
    (first second : Fin n → Kˣ)
    (hdet : IsSquare
      (diagonalUnitDeterminant second *
        diagonalUnitDeterminant first))
    (hnot : ¬ DiagonalRepresents
      (diagonalUnitCoefficients second)
      (diagonalUnitCoefficients first)) :
    HeHuSpacePairProperties first second where
  determinantSquare := hdet
  nonisometric := hnot
  exhaustive := fun w hw =>
    heHuTwoClass_exhaustive first second hdet hnot w hw

/-- A common hyperbolic head preserves the Table 1 pair package. -/
theorem HeHuSpacePairProperties.append {head tail : Nat}
    {first second : Fin tail → Kˣ}
    (P : HeHuSpacePairProperties first second)
    (common : Fin head → Kˣ) :
    HeHuSpacePairProperties
      (Fin.append common first) (Fin.append common second) :=
  HeHuSpacePairProperties.of_det_not _ _
    (determinantSquare_append_of_tail common second first
      P.determinantSquare)
    (not_represents_append_of_not_tail common second first
      P.nonisometric)

/-- Arithmetic reindexing of a finite family preserves the Table 1 pair
package. -/
theorem HeHuSpacePairProperties.cast {m n : Nat}
    {first second : Fin m → Kˣ}
    (P : HeHuSpacePairProperties first second) (h : m = n) :
    HeHuSpacePairProperties
      (heHuFinFamilyCast h first) (heHuFinFamilyCast h second) := by
  apply HeHuSpacePairProperties.of_det_not
  · simpa using P.determinantSquare
  · intro hrep
    exact P.nonisometric
      ((diagonalRepresents_heHuFinFamilyCast_iff
        h second first).mp hrep)

/-- Convert the paper's test `c/Delta` square into equality of the ordinary
square classes of `c` and `Delta`. -/
theorem isSquare_mul_discriminant_of_div_discriminant_square
    (c : Kˣ)
    (h : IsSquare (c /
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)) :
    IsSquare (c *
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit) := by
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  rcases h with ⟨s, hs⟩
  change c / delta = s * s at hs
  refine ⟨s * delta, ?_⟩
  calc
    c * delta = (c / delta) * delta ^ 2 := by
      simp [div_eq_mul_inv, pow_two, mul_assoc]
    _ = (s * s) * delta ^ 2 := by rw [hs]
    _ = (s * delta) * (s * delta) := by
      simp only [pow_two]
      ac_rfl

/-- In the discriminant square-class row, the uniformizer is the negative
Hilbert partner required by Proposition 3.3. -/
theorem heHuDiscriminantBinary_hilbert_neg (c : Kˣ)
    (hdelta : IsSquare (c /
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)) :
    hilbertSymbol K (uniformizerPowerUnit K (1 : Int)) c = -1 := by
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let pi := uniformizerPowerUnit K (1 : Int)
  have hclass : IsSquare (c * delta) := by
    simpa only [delta] using
      isSquare_mul_discriminant_of_div_discriminant_square c hdelta
  have heq : hilbertSymbol K pi c = hilbertSymbol K pi delta :=
    hilbertSymbol_eq_of_isSquare_mul_right hclass
  have hpiOdd : Odd (ordUnit K pi) := by
    dsimp only [pi]
    rw [ordUnit_uniformizerPowerUnit]
    exact odd_one
  have hne : hilbertSymbol K delta pi ≠ 1 :=
    hilbertSymbol_discriminant_ne_one_of_odd_order pi hpiOdd
  have hneg : hilbertSymbol K delta pi = -1 :=
    (Int.units_eq_one_or (hilbertSymbol K delta pi)).resolve_left hne
  calc
    hilbertSymbol K (uniformizerPowerUnit K (1 : Int)) c =
        hilbertSymbol K pi c := rfl
    _ = hilbertSymbol K pi delta := heq
    _ = hilbertSymbol K delta pi := hilbertSymbol_comm K pi delta
    _ = -1 := hneg

/-- The general nonsquare-unit row of the even-dimensional table. -/
theorem heHuEvenSharpTail_properties (c : Kˣ)
    (hc : HeHuSharpDomain c) :
    HeHuSpacePairProperties
      (heHuEvenFirstTail c) (heHuEvenSharpTail c hc) := by
  have Pbinary : HeHuSpacePairProperties
      (heHuBinaryFirst c) (heHuBinarySecond c hc) := by
    apply HeHuSpacePairProperties.of_det_not
    · exact heHuBinarySecond_determinantSquare_first c hc
    · exact heHuBinarySecond_not_represents_first c hc
  simpa only [heHuEvenFirstTail, heHuEvenSharpTail] using
    Pbinary.append (heHuHyperbolicPair (K := K))

/-- The discriminant square-class row of the even-dimensional table. -/
theorem heHuEvenDiscriminantTail_properties (c : Kˣ)
    (hdelta : IsSquare (c /
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)) :
    HeHuSpacePairProperties
      (heHuEvenFirstTail c) (heHuEvenDiscriminantTail c) := by
  have hnegative := heHuDiscriminantBinary_hilbert_neg c hdelta
  have hclassification :=
    heHuBinaryTwist_classification c
      (uniformizerPowerUnit K (1 : Int)) hnegative
  have Pbinary : HeHuSpacePairProperties
      (heHuBinaryFirst c) (heHuDiscriminantBinary c) := by
    apply HeHuSpacePairProperties.of_det_not
    · simpa only [heHuDiscriminantBinary] using hclassification.1
    · simpa only [heHuDiscriminantBinary] using hclassification.2.1
  simpa only [heHuEvenFirstTail, heHuEvenDiscriminantTail] using
    Pbinary.append (heHuHyperbolicPair (K := K))

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
theorem heHuEvenFirstTail_eq_vector (c : Kˣ) :
    heHuEvenFirstTail c = ![1, -1, 1, -c] := by
  funext i
  fin_cases i <;> rfl

omit [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
/-- The residual `H perp [1,-c]` is visibly isotropic. -/
theorem heHuEvenFirstTail_isotropic (c : Kˣ) :
    DiagonalIsotropic
      (diagonalUnitCoefficients (heHuEvenFirstTail c)) := by
  let x : Fin 4 → K := ![1, 1, 0, 0]
  refine ⟨x, ?_, ?_⟩
  · intro hx
    have hzero := congrFun hx (0 : Fin 4)
    norm_num [x] at hzero
  · rw [heHuEvenFirstTail_eq_vector]
    simp [diagonalUnitCoefficients,
      diagonalQuadratic, Fin.sum_univ_four, x]

/-- The quaternary Table 1 block is anisotropic. -/
theorem heHuAnisotropicQuaternary_units_anisotropic :
    DiagonalAnisotropic
      (diagonalUnitCoefficients
        (beliAnisotropicQuaternaryUnits (K := K))) := by
  intro z hz
  apply beliAnisotropicQuaternaryForm_isAnisotropic (K := K) z
  simpa only [beliAnisotropicQuaternaryForm,
    QuadraticSpace.finiteDiagonal_quadratic_apply] using hz

/-- In the square row, the anisotropic quaternary block and
`H perp [1,-c]` have the same determinant square class. -/
theorem heHuAnisotropicQuaternary_determinantSquare_firstTail
    (c : Kˣ) (hsquare : IsSquare c) :
    IsSquare
      (diagonalUnitDeterminant
          (beliAnisotropicQuaternaryUnits (K := K)) *
        diagonalUnitDeterminant (heHuEvenFirstTail c)) := by
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let pi := uniformizerPowerUnit K (1 : Int)
  rcases hsquare with ⟨s, hs⟩
  refine ⟨delta * pi * s, ?_⟩
  rw [hs]
  rw [heHuEvenFirstTail_eq_vector]
  simp [beliAnisotropicQuaternaryUnits,
    diagonalUnitDeterminant,
    Fin.prod_univ_four, delta, pi]
  ac_rfl

/-- The square row is the hyperbolic quaternary class paired with the
unique anisotropic quaternary class. -/
theorem heHuEvenSquareTail_properties (c : Kˣ)
    (hsquare : IsSquare c) :
    HeHuSpacePairProperties
      (heHuEvenFirstTail c)
      (beliAnisotropicQuaternaryUnits (K := K)) := by
  apply HeHuSpacePairProperties.of_det_not
  · exact heHuAnisotropicQuaternary_determinantSquare_firstTail c hsquare
  · intro hrep
    have hfirstAnisotropic : DiagonalAnisotropic
        (diagonalUnitCoefficients (heHuEvenFirstTail c)) :=
      hrep.symm_of_sameRank.anisotropic_of
        (heHuAnisotropicQuaternary_units_anisotropic (K := K))
    exact ((not_diagonalIsotropic_iff_diagonalAnisotropic
      (diagonalUnitCoefficients (heHuEvenFirstTail c))).2
        hfirstAnisotropic) (heHuEvenFirstTail_isotropic c)

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
theorem heHuOddFirstTail_isotropic (c : Kˣ) :
    DiagonalIsotropic
      (diagonalUnitCoefficients (heHuOddFirstTail c)) := by
  let x : Fin 3 → K := ![1, 1, 0]
  refine ⟨x, ?_, ?_⟩
  · intro hx
    have hzero := congrFun hx (0 : Fin 3)
    norm_num [x] at hzero
  · simp [heHuOddFirstTail, diagonalUnitCoefficients,
      diagonalQuadratic, Fin.sum_univ_three, x]

/-- The unramified discriminant pairs negatively with every odd-order
square class. -/
theorem hilbertSymbol_discriminant_eq_neg_one_of_odd_order
    (c : Kˣ) (hodd : Odd (ordUnit K c)) :
    hilbertSymbol K
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit c =
        -1 := by
  have hne := hilbertSymbol_discriminant_ne_one_of_odd_order c hodd
  exact (Int.units_eq_one_or
    (hilbertSymbol K
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit c)).resolve_left
        hne

theorem heHuOddSecondTailEven_eq_vector (c : Kˣ) :
    heHuOddSecondTailEven c =
      ![uniformizerPowerUnit K (1 : Int),
        -((inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit *
          uniformizerPowerUnit K (1 : Int)),
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit * c] := by
  rfl

theorem heHuOddSecondTailOdd_eq_vector (c : Kˣ) :
    heHuOddSecondTailOdd c =
      ![1,
        -(inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit,
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit * c] := by
  rfl

@[simp] theorem heHuOddSecondTailEven_zero (c : Kˣ) :
    heHuOddSecondTailEven c 0 = uniformizerPowerUnit K (1 : Int) := rfl

@[simp] theorem heHuOddSecondTailEven_one (c : Kˣ) :
    heHuOddSecondTailEven c 1 =
      -((inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit *
        uniformizerPowerUnit K (1 : Int)) := rfl

@[simp] theorem heHuOddSecondTailEven_two (c : Kˣ) :
    heHuOddSecondTailEven c 2 =
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit * c := rfl

@[simp] theorem heHuOddSecondTailOdd_zero (c : Kˣ) :
    heHuOddSecondTailOdd c 0 = 1 := rfl

@[simp] theorem heHuOddSecondTailOdd_one (c : Kˣ) :
    heHuOddSecondTailOdd c 1 =
      -(inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit := rfl

@[simp] theorem heHuOddSecondTailOdd_two (c : Kˣ) :
    heHuOddSecondTailOdd c 2 =
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit * c := rfl

/-- The even-valuation ternary row has negative adjacent Hilbert symbol. -/
theorem heHuOddSecondTailEven_adjacentHilbert
    (c : Kˣ) (heven : Even (ordUnit K c)) :
    hilbertSymbol K
        (-(heHuOddSecondTailEven c 0 *
          heHuOddSecondTailEven c 1))
        (-(heHuOddSecondTailEven c 1 *
          heHuOddSecondTailEven c 2)) = -1 := by
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let pi := uniformizerPowerUnit K (1 : Int)
  have hfirst :
      -(heHuOddSecondTailEven c 0 *
          heHuOddSecondTailEven c 1) = delta * pi ^ 2 := by
    rw [heHuOddSecondTailEven_zero, heHuOddSecondTailEven_one]
    simp only [mul_neg, neg_neg, pow_two]
    dsimp only [delta, pi]
    ac_rfl
  have hsecond :
      -(heHuOddSecondTailEven c 1 *
          heHuOddSecondTailEven c 2) = (pi * c) * delta ^ 2 := by
    rw [heHuOddSecondTailEven_one, heHuOddSecondTailEven_two]
    simp only [neg_mul, neg_neg, pow_two]
    dsimp only [delta, pi]
    ac_rfl
  have hpiOrder : ordUnit K pi = 1 := by
    dsimp only [pi]
    rw [ordUnit_uniformizerPowerUnit]
  have hproductOdd : Odd (ordUnit K (pi * c)) := by
    rcases heven with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [ordUnit_mul, hpiOrder, hk]
    omega
  rw [hfirst, hsecond, hilbertSymbol_mul_square_left,
    hilbertSymbol_mul_square_right]
  exact hilbertSymbol_discriminant_eq_neg_one_of_odd_order
    (pi * c) hproductOdd

/-- The odd-valuation ternary row has negative adjacent Hilbert symbol. -/
theorem heHuOddSecondTailOdd_adjacentHilbert
    (c : Kˣ) (hodd : Odd (ordUnit K c)) :
    hilbertSymbol K
        (-(heHuOddSecondTailOdd c 0 *
          heHuOddSecondTailOdd c 1))
        (-(heHuOddSecondTailOdd c 1 *
          heHuOddSecondTailOdd c 2)) = -1 := by
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  have hfirst :
      -(heHuOddSecondTailOdd c 0 *
          heHuOddSecondTailOdd c 1) = delta := by
    rw [heHuOddSecondTailOdd_zero, heHuOddSecondTailOdd_one]
    simp only [one_mul, neg_neg]
    rfl
  have hsecond :
      -(heHuOddSecondTailOdd c 1 *
          heHuOddSecondTailOdd c 2) = c * delta ^ 2 := by
    rw [heHuOddSecondTailOdd_one, heHuOddSecondTailOdd_two]
    simp only [neg_mul, neg_neg, pow_two]
    dsimp only [delta]
    ac_rfl
  rw [hfirst, hsecond, hilbertSymbol_mul_square_right]
  exact hilbertSymbol_discriminant_eq_neg_one_of_odd_order c hodd

/-- Both displayed odd-dimensional residual ternaries are anisotropic. -/
theorem heHuOddSecondTailEven_anisotropic
    (c : Kˣ) (heven : Even (ordUnit K c)) :
    DiagonalAnisotropic
      (diagonalUnitCoefficients (heHuOddSecondTailEven c)) := by
  rw [← not_diagonalIsotropic_iff_diagonalAnisotropic,
    diagonalUnitTernary_isotropic_iff_adjacentHilbertOne,
    heHuOddSecondTailEven_adjacentHilbert c heven]
  norm_num

theorem heHuOddSecondTailOdd_anisotropic
    (c : Kˣ) (hodd : Odd (ordUnit K c)) :
    DiagonalAnisotropic
      (diagonalUnitCoefficients (heHuOddSecondTailOdd c)) := by
  rw [← not_diagonalIsotropic_iff_diagonalAnisotropic,
    diagonalUnitTernary_isotropic_iff_adjacentHilbertOne,
    heHuOddSecondTailOdd_adjacentHilbert c hodd]
  norm_num

/-- Determinant equality for the even-valuation odd-dimensional row. -/
theorem heHuOddSecondTailEven_determinantSquare_first
    (c : Kˣ) :
    IsSquare
      (diagonalUnitDeterminant (heHuOddSecondTailEven c) *
        diagonalUnitDeterminant (heHuOddFirstTail c)) := by
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let pi := uniformizerPowerUnit K (1 : Int)
  refine ⟨delta * pi * c, ?_⟩
  rw [heHuOddSecondTailEven_eq_vector]
  simp [heHuOddFirstTail, diagonalUnitDeterminant,
    Fin.prod_univ_three, delta, pi]
  ac_rfl

/-- Determinant equality for the odd-valuation odd-dimensional row. -/
theorem heHuOddSecondTailOdd_determinantSquare_first
    (c : Kˣ) :
    IsSquare
      (diagonalUnitDeterminant (heHuOddSecondTailOdd c) *
        diagonalUnitDeterminant (heHuOddFirstTail c)) := by
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  refine ⟨delta * c, ?_⟩
  rw [heHuOddSecondTailOdd_eq_vector]
  simp [heHuOddFirstTail, diagonalUnitDeterminant,
    Fin.prod_univ_three, delta]
  ac_rfl

theorem heHuOddEvenTail_properties (c : Kˣ)
    (heven : Even (ordUnit K c)) :
    HeHuSpacePairProperties
      (heHuOddFirstTail c) (heHuOddSecondTailEven c) := by
  apply HeHuSpacePairProperties.of_det_not
  · exact heHuOddSecondTailEven_determinantSquare_first c
  · intro hrep
    have hfirstAnisotropic : DiagonalAnisotropic
        (diagonalUnitCoefficients (heHuOddFirstTail c)) :=
      hrep.symm_of_sameRank.anisotropic_of
        (heHuOddSecondTailEven_anisotropic c heven)
    exact ((not_diagonalIsotropic_iff_diagonalAnisotropic
      (diagonalUnitCoefficients (heHuOddFirstTail c))).2
        hfirstAnisotropic) (heHuOddFirstTail_isotropic c)

theorem heHuOddOddTail_properties (c : Kˣ)
    (hodd : Odd (ordUnit K c)) :
    HeHuSpacePairProperties
      (heHuOddFirstTail c) (heHuOddSecondTailOdd c) := by
  apply HeHuSpacePairProperties.of_det_not
  · exact heHuOddSecondTailOdd_determinantSquare_first c
  · intro hrep
    have hfirstAnisotropic : DiagonalAnisotropic
        (diagonalUnitCoefficients (heHuOddFirstTail c)) :=
      hrep.symm_of_sameRank.anisotropic_of
        (heHuOddSecondTailOdd_anisotropic c hodd)
    exact ((not_diagonalIsotropic_iff_diagonalAnisotropic
      (diagonalUnitCoefficients (heHuOddFirstTail c))).2
        hfirstAnisotropic) (heHuOddFirstTail_isotropic c)

/-- He--Hu, Definition 3.4(ii) and Proposition 3.5(i)--(ii), odd-dimensional
form.  The two displayed spaces have the prescribed common determinant, are
nonisometric, and exhaust every diagonal space in that determinant class. -/
theorem heHu2022Definition34Proposition35Odd
    (pairs : Nat) (c : Kˣ) :
    HeHuSpacePairProperties
      (heHuOddFirst pairs c) (heHuOddSecond pairs c) := by
  classical
  by_cases heven : Even (ordUnit K c)
  · have P := (heHuOddEvenTail_properties c heven).append
      (standardHyperbolicEndpointTower (K := K) pairs)
    rw [heHuOddSecond_of_even pairs c heven]
    simpa only [heHuOddFirst] using P
  · have hodd : Odd (ordUnit K c) := Int.not_even_iff_odd.mp heven
    have P := (heHuOddOddTail_properties c hodd).append
      (standardHyperbolicEndpointTower (K := K) pairs)
    rw [heHuOddSecond_of_not_even pairs c heven]
    simpa only [heHuOddFirst] using P

/-- He--Hu, Definition 3.4(i) and Proposition 3.5(i)--(ii), even-dimensional
form, including the unique undefined case `n=2`, `c=1` in square-class
notation. -/
theorem heHu2022Definition34Proposition35Even
    (pairs : Nat) (c : Kˣ)
    (hdefined : HeHuEvenSecondDefined pairs c) :
    HeHuSpacePairProperties
      (heHuEvenFirst pairs c) (heHuEvenSecond pairs c hdefined) := by
  classical
  cases pairs with
  | zero =>
      have hnonsquare : ¬ IsSquare c := by
        rcases hdefined with hp | hn
        · omega
        · exact hn
      let delta :=
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
      by_cases hdelta : IsSquare (c / delta)
      · have hnegative := heHuDiscriminantBinary_hilbert_neg c (by
          simpa only [delta] using hdelta)
        have hclassification := heHuBinaryTwist_classification c
          (uniformizerPowerUnit K (1 : Int)) hnegative
        have P : HeHuSpacePairProperties
            (heHuBinaryFirst c) (heHuDiscriminantBinary c) :=
          HeHuSpacePairProperties.of_det_not _ _
            (by simpa only [heHuDiscriminantBinary] using hclassification.1)
            (by simpa only [heHuDiscriminantBinary] using
              hclassification.2.1)
        rw [heHuEvenSecond_zero_of_discriminant c hdefined (by
          simpa only [delta] using hdelta)]
        simpa only [heHuEvenFirst] using P
      · have hc : HeHuSharpDomain c :=
          { notSquare := hnonsquare
            notDiscriminantSquare := by simpa only [delta] using hdelta }
        have P : HeHuSpacePairProperties
            (heHuBinaryFirst c) (heHuBinarySecond c hc) :=
          HeHuSpacePairProperties.of_det_not _ _
            (heHuBinarySecond_determinantSquare_first c hc)
            (heHuBinarySecond_not_represents_first c hc)
        rw [heHuEvenSecond_zero_of_sharp c hdefined hnonsquare (by
          simpa only [delta] using hdelta)]
        simpa only [heHuEvenFirst] using P
  | succ pairs =>
      by_cases hsquare : IsSquare c
      · have Ptail := heHuEvenSquareTail_properties c hsquare
        have Pappend := Ptail.append
          (standardHyperbolicEndpointTower (K := K) pairs)
        have hdim : 2 * pairs + 4 = 2 * (pairs + 1) + 2 := by omega
        have Pcast := Pappend.cast hdim
        rw [heHuEvenSecond_succ_of_square pairs c hdefined hsquare]
        simpa only [heHuEvenFirst] using Pcast
      · let delta :=
          (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
        by_cases hdelta : IsSquare (c / delta)
        · have Ptail := heHuEvenDiscriminantTail_properties c (by
            simpa only [delta] using hdelta)
          have Pappend := Ptail.append
            (standardHyperbolicEndpointTower (K := K) pairs)
          have hdim : 2 * pairs + 4 = 2 * (pairs + 1) + 2 := by omega
          have Pcast := Pappend.cast hdim
          rw [heHuEvenSecond_succ_of_discriminant pairs c hdefined
            hsquare (by simpa only [delta] using hdelta)]
          simpa only [heHuEvenFirst] using Pcast
        · have hc : HeHuSharpDomain c :=
            { notSquare := hsquare
              notDiscriminantSquare := by simpa only [delta] using hdelta }
          have Ptail := heHuEvenSharpTail_properties c hc
          have Pappend := Ptail.append
            (standardHyperbolicEndpointTower (K := K) pairs)
          have hdim : 2 * pairs + 4 = 2 * (pairs + 1) + 2 := by omega
          have Pcast := Pappend.cast hdim
          rw [heHuEvenSecond_succ_of_sharp pairs c hdefined hsquare (by
            simpa only [delta] using hdelta)]
          simpa only [heHuEvenFirst] using Pcast

/-- Determinant of the diagonal hyperbolic tower. -/
theorem diagonalUnitDeterminant_standardHyperbolicEndpointTower
    (pairs : Nat) :
    diagonalUnitDeterminant
        (standardHyperbolicEndpointTower (K := K) pairs) =
      (-1 : Kˣ) ^ pairs := by
  have h := signedDeterminant_standardHyperbolicEndpointTower
    (K := K) pairs
  unfold signedDeterminant at h
  have hinv := inv_eq_of_mul_eq_one_right h
  calc
    diagonalUnitDeterminant
        (standardHyperbolicEndpointTower (K := K) pairs) =
        ((-1 : Kˣ) ^ pairs)⁻¹ := hinv.symm
    _ = (-1 : Kˣ) ^ pairs := by
      have hneg : ((-1 : Kˣ)⁻¹) = -1 := by
        apply inv_eq_of_mul_eq_one_left
        norm_num
      rw [← inv_pow, hneg]

/-- The determinant formula printed in Definition 3.4(i). -/
theorem diagonalUnitDeterminant_heHuEvenFirst
    (pairs : Nat) (c : Kˣ) :
    diagonalUnitDeterminant (heHuEvenFirst pairs c) =
      (-1 : Kˣ) ^ (pairs + 1) * c := by
  cases pairs with
  | zero =>
      simp [heHuEvenFirst, heHuBinaryFirst,
        diagonalUnitDeterminant, Fin.prod_univ_two]
  | succ pairs =>
      rw [heHuEvenFirst,
        diagonalUnitDeterminant_heHuFinFamilyCast,
        diagonalUnitDeterminant_append,
        diagonalUnitDeterminant_standardHyperbolicEndpointTower,
        heHuEvenFirstTail_eq_vector]
      simp [diagonalUnitDeterminant, Fin.prod_univ_four, pow_succ]

/-- The determinant formula printed in Definition 3.4(ii). -/
theorem diagonalUnitDeterminant_heHuOddFirst
    (pairs : Nat) (c : Kˣ) :
    diagonalUnitDeterminant (heHuOddFirst pairs c) =
      (-1 : Kˣ) ^ (pairs + 1) * c := by
  rw [heHuOddFirst, diagonalUnitDeterminant_append,
    diagonalUnitDeterminant_standardHyperbolicEndpointTower]
  simp [heHuOddFirstTail, diagonalUnitDeterminant,
    Fin.prod_univ_three, pow_succ]

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
/-- Signed-product square implies the equivalent signed-ratio square used
by the explicit hyperbolic-plane coordinate map. -/
theorem isSquare_neg_div_of_neg_mul_square (a b : Kˣ)
    (h : IsSquare (-(a * b))) : IsSquare (-(a / b)) := by
  rcases h with ⟨s, hs⟩
  refine ⟨s / b, ?_⟩
  calc
    -(a / b) = (-(a * b)) / b ^ 2 := by
      simp [div_eq_mul_inv, pow_two, mul_assoc]
    _ = (s * s) / b ^ 2 := by rw [hs]
    _ = (s / b) * (s / b) := by
      simp only [div_eq_mul_inv, pow_two]
      ac_rfl

omit [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
/-- The exceptional binary determinant class has only the hyperbolic
space, exactly as stated after Definition 3.4. -/
theorem heHuBinarySquareClass_represents_first
    (w : Fin 2 → Kˣ) (c : Kˣ)
    (hc : IsSquare c)
    (hdet : IsSquare
      (diagonalUnitDeterminant w *
        diagonalUnitDeterminant (heHuBinaryFirst c))) :
    DiagonalRepresents
      (diagonalUnitCoefficients w)
      (diagonalUnitCoefficients (heHuBinaryFirst c)) := by
  have hwSigned : IsSquare (-diagonalUnitDeterminant w) := by
    have hfirst : diagonalUnitDeterminant (heHuBinaryFirst c) = -c :=
      diagonalUnitDeterminant_heHuBinaryFirst c
    rw [hfirst] at hdet
    have hquotient := hdet.div hc
    have heq :
        (diagonalUnitDeterminant w * -c) / c =
          -diagonalUnitDeterminant w := by
      rw [show -c = (-1 : Kˣ) * c by simp,
        show -diagonalUnitDeterminant w =
          (-1 : Kˣ) * diagonalUnitDeterminant w by simp]
      simp [div_eq_mul_inv, mul_comm, mul_left_comm]
    rw [heq] at hquotient
    exact hquotient
  have hwRatio : IsSquare (-(w 0 / w 1)) := by
    apply isSquare_neg_div_of_neg_mul_square
    simpa [diagonalUnitDeterminant, Fin.prod_univ_two] using hwSigned
  have hfirstSigned : IsSquare
      (-((1 : Kˣ) * (-c))) := by simpa using hc
  have hfirstRatio : IsSquare (-((1 : Kˣ) / (-c))) :=
    isSquare_neg_div_of_neg_mul_square 1 (-c) hfirstSigned
  have hrep :=
    QuadraticSpace.finiteDiagonal_fin_two_diagonalRepresents_of_signedRatioSquares
      (w 0) (w 1) 1 (-c) hwRatio hfirstRatio
  convert hrep using 1 <;> funext i <;> fin_cases i <;> rfl

/-- He--Hu, Proposition 3.5(ii), even-dimensional diagonal form.  The
existential proof also records whether the second class is defined. -/
theorem heHu2022Proposition35iiEven (pairs : Nat)
    (w : Fin (2 * pairs + 2) → Kˣ) :
    ∃ c : Kˣ,
      DiagonalRepresents
          (diagonalUnitCoefficients w)
          (diagonalUnitCoefficients (heHuEvenFirst pairs c)) ∨
        ∃ hdefined : HeHuEvenSecondDefined pairs c,
          DiagonalRepresents
            (diagonalUnitCoefficients w)
            (diagonalUnitCoefficients
              (heHuEvenSecond pairs c hdefined)) := by
  classical
  let c : Kˣ :=
    (-1 : Kˣ) ^ (pairs + 1) * diagonalUnitDeterminant w
  have hwdet : IsSquare
      (diagonalUnitDeterminant w *
        diagonalUnitDeterminant (heHuEvenFirst pairs c)) := by
    refine ⟨c, ?_⟩
    rw [diagonalUnitDeterminant_heHuEvenFirst]
    simp only [c]
    ac_rfl
  refine ⟨c, ?_⟩
  by_cases hdefined : HeHuEvenSecondDefined pairs c
  · rcases (heHu2022Definition34Proposition35Even pairs c hdefined).exhaustive
        w hwdet with hfirst | hsecond
    · exact Or.inl hfirst
    · exact Or.inr ⟨hdefined, hsecond⟩
  · have hpairs : pairs = 0 := by
      by_contra hp
      exact hdefined (Or.inl (Nat.pos_of_ne_zero hp))
    have hc : IsSquare c := by
      by_contra hc
      exact hdefined (Or.inr hc)
    subst pairs
    left
    simpa only [heHuEvenFirst] using
      heHuBinarySquareClass_represents_first w c hc hwdet

/-- He--Hu, Proposition 3.5(ii), odd-dimensional diagonal form. -/
theorem heHu2022Proposition35iiOdd (pairs : Nat)
    (w : Fin (2 * pairs + 3) → Kˣ) :
    ∃ c : Kˣ,
      DiagonalRepresents
          (diagonalUnitCoefficients w)
          (diagonalUnitCoefficients (heHuOddFirst pairs c)) ∨
        DiagonalRepresents
          (diagonalUnitCoefficients w)
          (diagonalUnitCoefficients (heHuOddSecond pairs c)) := by
  classical
  let c : Kˣ :=
    (-1 : Kˣ) ^ (pairs + 1) * diagonalUnitDeterminant w
  have hwdet : IsSquare
      (diagonalUnitDeterminant w *
        diagonalUnitDeterminant (heHuOddFirst pairs c)) := by
    refine ⟨c, ?_⟩
    rw [diagonalUnitDeterminant_heHuOddFirst]
    simp only [c]
    ac_rfl
  refine ⟨c, ?_⟩
  exact (heHu2022Definition34Proposition35Odd pairs c).exhaustive w hwdet

end Bong
