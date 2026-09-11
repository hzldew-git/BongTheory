/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.HeHu2022SectionThreeSpaces
import Bong.Bong.DiagonalCodimensionTwoRepresentationProof
import Bong.Bong.DiagonalIsometryInvariantProof

/-!
# He--Hu (2024), Proposition 3.5(iii)

This file isolates the local Witt-theoretic argument behind the unique
`(n+2)`-dimensional space which represents every `n`-dimensional space except
one prescribed isometry class.  The proof uses the unconditional
codimension-two theorem in `DiagonalCodimensionTwoRepresentationProof` and a
binary-complement calculation in the exceptional determinant class.
-/

namespace Bong

open Dyadic BONG.GoodBONG
open AlternatingEndpointTower

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A target of rank `n+2` represents precisely the rank-`n` isometry
classes other than `excluded`.  Equal-rank diagonal representation is the
repository's concrete isometry relation. -/
structure HeHuMissesExactly {n : Nat} (excluded : Fin n → Kˣ)
    (target : Fin (n + 2) → Kˣ) : Prop where
  misses : ¬ DiagonalRepresents
    (diagonalUnitCoefficients excluded)
    (diagonalUnitCoefficients target)
  represents_other (w : Fin n → Kˣ) :
    ¬ DiagonalRepresents
        (diagonalUnitCoefficients w)
        (diagonalUnitCoefficients excluded) →
      DiagonalRepresents
        (diagonalUnitCoefficients w)
        (diagonalUnitCoefficients target)

/-- The existence-and-uniqueness package in Proposition 3.5(iii). -/
structure HeHuUniqueExcludingTarget {n : Nat} (excluded : Fin n → Kˣ)
    (target : Fin (n + 2) → Kˣ) : Prop where
  exactness : HeHuMissesExactly excluded target
  unique (other : Fin (n + 2) → Kˣ) :
    HeHuMissesExactly excluded other →
      DiagonalRepresents
        (diagonalUnitCoefficients other)
        (diagonalUnitCoefficients target)

/-- A square relation for an isometric codimension-two completion forces
the binary complement to have square signed determinant. -/
theorem binaryComplement_signedDeterminantSquare {n : Nat}
    (source : Fin n → Kˣ) (target : Fin (n + 2) → Kˣ)
    (complement : Fin 2 → Kˣ)
    (hcompletion : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.append source complement))
      (diagonalUnitCoefficients target))
    (hnegative : IsSquare
      (-diagonalUnitDeterminant target *
        diagonalUnitDeterminant source)) :
    IsSquare (-diagonalUnitDeterminant complement) := by
  let DS := diagonalUnitDeterminant source
  let DT := diagonalUnitDeterminant target
  let DC := diagonalUnitDeterminant complement
  have hfull : IsSquare ((DS * DC) * DT) := by
    have h := DiagonalIsometryInvariantLaws.determinant_square
      (Fin.append source complement) target hcompletion
    rw [diagonalUnitDeterminant_append] at h
    simpa only [DS, DT, DC] using h
  have hproduct : IsSquare (((DS * DC) * DT) * ((-DT) * DS)) := by
    exact hfull.mul (by simpa only [DS, DT] using hnegative)
  have hdenominator : IsSquare ((DS * DT) ^ 2) :=
    ⟨DS * DT, pow_two (DS * DT)⟩
  have hquotient : IsSquare
      ((((DS * DC) * DT) * ((-DT) * DS)) / ((DS * DT) ^ 2)) :=
    hproduct.div hdenominator
  have heq :
      (((DS * DC) * DT) * ((-DT) * DS)) / ((DS * DT) ^ 2) =
        -DC := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_neg,
      Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero DS, Units.ne_zero DT]
  rw [heq] at hquotient
  exact hquotient

/-- In the exceptional determinant square class, a codimension-two
representation identifies the target with the source plus a hyperbolic
plane. -/
theorem diagonalRepresents_target_to_appendHyperbolic_of_negativeDetSquare
    {n : Nat} (source : Fin n → Kˣ) (target : Fin (n + 2) → Kˣ)
    (hnegative : IsSquare
      (-diagonalUnitDeterminant target *
        diagonalUnitDeterminant source))
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients target)) :
    DiagonalRepresents
      (diagonalUnitCoefficients target)
      (diagonalUnitCoefficients
        (Fin.append source (heHuHyperbolicPair (K := K)))) := by
  obtain ⟨complement, hcompletion⟩ :=
    exists_diagonalBinaryComplement source target hrep
  have hcomplementSigned : IsSquare
      (-diagonalUnitDeterminant complement) :=
    binaryComplement_signedDeterminantSquare
      source target complement hcompletion hnegative
  have hcomplementRatio : IsSquare (-(complement 0 / complement 1)) := by
    apply isSquare_neg_div_of_neg_mul_square
    simpa [diagonalUnitDeterminant, Fin.prod_univ_two] using
      hcomplementSigned
  have hhyperbolicRatio : IsSquare (-((1 : Kˣ) / (-1 : Kˣ))) := by
    simp
  have hbinary : DiagonalRepresents
      (diagonalUnitCoefficients complement)
      (diagonalUnitCoefficients (heHuHyperbolicPair (K := K))) := by
    have h :=
      QuadraticSpace.finiteDiagonal_fin_two_diagonalRepresents_of_signedRatioSquares
        (complement 0) (complement 1) 1 (-1)
        hcomplementRatio hhyperbolicRatio
    convert h using 1 <;> funext i <;> fin_cases i <;> rfl
  have happend : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.append source complement))
      (diagonalUnitCoefficients
        (Fin.append source (heHuHyperbolicPair (K := K)))) := by
    simpa only [diagonalUnitCoefficients_append] using
      DiagonalRepresents.appendBoth
        (diagonalRepresents_refl (diagonalUnitCoefficients source)) hbinary
  exact hcompletion.symm_of_sameRank.trans happend

omit [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
/-- The evident copy of `source` inside an isometric hyperbolic extension. -/
theorem diagonalRepresents_of_appendHyperbolic_lift {n : Nat}
    (source : Fin n → Kˣ) (target : Fin (n + 2) → Kˣ)
    (hlift : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append source (heHuHyperbolicPair (K := K))))
      (diagonalUnitCoefficients target)) :
    DiagonalRepresents
      (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients target) := by
  have hprefix := DiagonalRepresents.prefixOfLE
    (diagonalUnitCoefficients
      (Fin.append source (heHuHyperbolicPair (K := K))))
    (by omega : n ≤ n + 2)
  have hsource : DiagonalRepresents
      (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients
        (Fin.append source (heHuHyperbolicPair (K := K)))) := by
    convert hprefix using 1
    funext i
    change (source i : K) =
      (Fin.append source (heHuHyperbolicPair (K := K))
        ⟨i.val, by omega⟩ : Kˣ)
    have hi : (⟨i.val, by omega⟩ : Fin (n + 2)) =
        Fin.castAdd 2 i := Fin.ext rfl
    rw [hi, Fin.append_left]
  exact hsource.trans hlift

/-- An isometric hyperbolic lift has the exceptional signed determinant
class required by the codimension-two theorem. -/
theorem negativeDeterminantSquare_of_appendHyperbolic_lift {n : Nat}
    (source : Fin n → Kˣ) (target : Fin (n + 2) → Kˣ)
    (hlift : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append source (heHuHyperbolicPair (K := K))))
      (diagonalUnitCoefficients target)) :
    IsSquare
      (-diagonalUnitDeterminant target *
        diagonalUnitDeterminant source) := by
  have h := DiagonalIsometryInvariantLaws.determinant_square
    (Fin.append source (heHuHyperbolicPair (K := K))) target hlift
  rw [diagonalUnitDeterminant_append] at h
  have hhyperbolic : diagonalUnitDeterminant
      (heHuHyperbolicPair (K := K)) = -1 := by
    simp [heHuHyperbolicPair, diagonalUnitDeterminant,
      Fin.prod_univ_two]
  rw [hhyperbolic] at h
  simpa only [mul_neg, mul_one, one_mul, neg_mul, mul_comm, mul_left_comm,
    mul_assoc] using h

/-- Outside the exceptional determinant class, codimension-two
representation is automatic.  This form makes the square-class
contrapositive used in Proposition 3.5(iii) explicit. -/
theorem diagonalRepresents_of_determinantClass_ne_excluded {n : Nat}
    (excluded w : Fin n → Kˣ) (target : Fin (n + 2) → Kˣ)
    (htarget : IsSquare
      (-diagonalUnitDeterminant target *
        diagonalUnitDeterminant excluded))
    (hw : ¬ IsSquare
      (diagonalUnitDeterminant w *
        diagonalUnitDeterminant excluded)) :
    DiagonalRepresents
      (diagonalUnitCoefficients w)
      (diagonalUnitCoefficients target) := by
  apply diagonalRepresents_of_not_negative_determinant_square
    w target rfl
  intro hautomatic
  apply hw
  apply isSquare_mul_trans
      (diagonalUnitDeterminant w)
      (-diagonalUnitDeterminant target)
      (diagonalUnitDeterminant excluded)
  · simpa only [mul_comm] using hautomatic
  · simpa only [mul_comm] using htarget

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
/-- Transport the source and target coordinate families of a diagonal
representation across independent arithmetic equalities of their ranks. -/
theorem diagonalRepresents_heHuFinFamilyCast_both
    {m m' n n' : Nat} (hm : m = m') (hn : n = n')
    (source : Fin m → Kˣ) (target : Fin n → Kˣ)
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients target)) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heHuFinFamilyCast hm source))
      (diagonalUnitCoefficients (heHuFinFamilyCast hn target)) := by
  subst m'
  subst n'
  exact hrep

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
@[simp] theorem heHuFinFamilyCast_trans {m n r : Nat}
    (hmn : m = n) (hnr : n = r) (a : Fin m → Kˣ) :
    heHuFinFamilyCast hnr (heHuFinFamilyCast hmn a) =
      heHuFinFamilyCast (hmn.trans hnr) a := by
  funext i
  unfold heHuFinFamilyCast
  congr 1

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
@[simp] theorem heHuFinFamilyCast_self {m : Nat} (h : m = m)
    (a : Fin m → Kˣ) :
    heHuFinFamilyCast h a = a := by
  have hp : h = rfl := Subsingleton.elim _ _
  subst hp
  rfl

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
/-- Associativity of finite-family append, oriented as the rank cast used
by the He--Hu tables. -/
theorem heHuFinFamilyCast_append_assoc {m n r : Nat}
    (h : m + (n + r) = (m + n) + r)
    (a : Fin m → Kˣ) (b : Fin n → Kˣ) (c : Fin r → Kˣ) :
    heHuFinFamilyCast h (Fin.append a (Fin.append b c)) =
      Fin.append (Fin.append a b) c := by
  funext i
  unfold heHuFinFamilyCast
  have hp : h.symm = Nat.add_assoc m n r := Subsingleton.elim _ _
  rw [hp]
  exact congrFun (Fin.append_assoc a b c) i |>.symm

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
/-- Casting the left block of an appended family is the same as casting
the whole family by the induced rank equality. -/
theorem heHuFinFamilyCast_append_left {m n r : Nat}
    (h : m = n) (a : Fin m → Kˣ) (c : Fin r → Kˣ) :
    heHuFinFamilyCast (congrArg (fun q => q + r) h) (Fin.append a c) =
      Fin.append (heHuFinFamilyCast h a) c := by
  have happend := Fin.append_cast_left a c n h.symm
  unfold heHuFinFamilyCast
  convert happend.symm using 1
  · funext i
    congr 1
  · rfl

/-- The standard tower in the next rank is the preceding standard tower
with one hyperbolic pair appended, after the arithmetic rank cast. -/
theorem heHuStandardHyperbolicTower_succ
    (pairs : Nat) :
    heHuFinFamilyCast (by omega :
        2 * pairs + 2 = 2 * (pairs + 1))
      (Fin.append
        (standardHyperbolicEndpointTower (K := K) pairs)
        (heHuHyperbolicPair (K := K))) =
      standardHyperbolicEndpointTower (K := K) (pairs + 1) := by
  funext i
  unfold heHuFinFamilyCast
  by_cases hi : i.val < 2 * pairs
  · have hindex :
        Fin.cast (by omega : 2 * (pairs + 1) = 2 * pairs + 2) i =
          Fin.castAdd 2 ⟨i.val, hi⟩ := Fin.ext rfl
    rw [hindex, Fin.append_left]
    rfl
  · have hlast : i.val = 2 * pairs ∨ i.val = 2 * pairs + 1 := by
      omega
    rcases hlast with hzero | hone
    · have hiEq : i = ⟨2 * pairs, by omega⟩ := Fin.ext hzero
      rw [hiEq]
      have hindex :
          Fin.cast (by omega : 2 * (pairs + 1) = 2 * pairs + 2)
              ⟨2 * pairs, by omega⟩ =
            Fin.natAdd (2 * pairs) (0 : Fin 2) := Fin.ext rfl
      rw [hindex, Fin.append_right]
      simp [heHuHyperbolicPair, standardHyperbolicEndpointTower]
    · have hiEq : i = ⟨2 * pairs + 1, by omega⟩ := Fin.ext hone
      rw [hiEq]
      have hindex :
          Fin.cast (by omega : 2 * (pairs + 1) = 2 * pairs + 2)
              ⟨2 * pairs + 1, by omega⟩ =
            Fin.natAdd (2 * pairs) (1 : Fin 2) := Fin.ext rfl
      rw [hindex, Fin.append_right]
      have hnotEven : ¬ Even (2 * pairs + 1) :=
        Nat.not_even_two_mul_add_one pairs
      simp [heHuHyperbolicPair, standardHyperbolicEndpointTower,
        hnotEven]

/-- Reassociate a leading hyperbolic pair into the standard tower. -/
theorem heHuFinFamilyCast_tower_hyperbolic_tail {tailRank : Nat}
    (pairs : Nat) (tail : Fin tailRank → Kˣ) :
    heHuFinFamilyCast (by omega :
        2 * pairs + (2 + tailRank) = 2 * (pairs + 1) + tailRank)
      (Fin.append
        (standardHyperbolicEndpointTower (K := K) pairs)
        (Fin.append (heHuHyperbolicPair (K := K)) tail)) =
      Fin.append
        (standardHyperbolicEndpointTower (K := K) (pairs + 1)) tail := by
  let hAssoc : 2 * pairs + (2 + tailRank) =
      (2 * pairs + 2) + tailRank := by omega
  let hTower : 2 * pairs + 2 = 2 * (pairs + 1) := by omega
  let hDim : (2 * pairs + 2) + tailRank =
      2 * (pairs + 1) + tailRank := by omega
  calc
    heHuFinFamilyCast (by omega :
        2 * pairs + (2 + tailRank) = 2 * (pairs + 1) + tailRank)
        (Fin.append
          (standardHyperbolicEndpointTower (K := K) pairs)
          (Fin.append (heHuHyperbolicPair (K := K)) tail)) =
      heHuFinFamilyCast hDim
        (heHuFinFamilyCast hAssoc
          (Fin.append
            (standardHyperbolicEndpointTower (K := K) pairs)
            (Fin.append (heHuHyperbolicPair (K := K)) tail))) := by
          rw [heHuFinFamilyCast_trans]
    _ = heHuFinFamilyCast hDim
        (Fin.append
          (Fin.append
            (standardHyperbolicEndpointTower (K := K) pairs)
            (heHuHyperbolicPair (K := K))) tail) := by
          congr 1
          exact heHuFinFamilyCast_append_assoc hAssoc
            (standardHyperbolicEndpointTower (K := K) pairs)
            (heHuHyperbolicPair (K := K)) tail
    _ = Fin.append
        (standardHyperbolicEndpointTower (K := K) (pairs + 1)) tail := by
          have htower := heHuStandardHyperbolicTower_succ
            (K := K) pairs
          have happend := heHuFinFamilyCast_append_left hTower
            (Fin.append
              (standardHyperbolicEndpointTower (K := K) pairs)
              (heHuHyperbolicPair (K := K))) tail
          simpa only [htower] using happend

/-- Adding one more standard hyperbolic pair to a tower is isometric to
adjoining that pair at the end of the preceding tower model. -/
theorem heHuTowerModel_succ_hyperbolicLift {tailRank : Nat}
    (pairs : Nat) (tail : Fin tailRank → Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append
          (Fin.append
            (standardHyperbolicEndpointTower (K := K) pairs) tail)
          (heHuHyperbolicPair (K := K))))
      (diagonalUnitCoefficients
        (Fin.append
          (standardHyperbolicEndpointTower (K := K) (pairs + 1)) tail)) := by
  have hcomm := diagonalRepresents_append_comm
    (diagonalUnitCoefficients tail)
    (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
  have hhead := diagonalRepresents_refl
    (diagonalUnitCoefficients
      (standardHyperbolicEndpointTower (K := K) pairs))
  have h := DiagonalRepresents.appendBoth hhead hcomm
  have h' : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append
          (standardHyperbolicEndpointTower (K := K) pairs)
          (Fin.append tail (heHuHyperbolicPair (K := K)))))
      (diagonalUnitCoefficients
        (Fin.append
          (standardHyperbolicEndpointTower (K := K) pairs)
          (Fin.append (heHuHyperbolicPair (K := K)) tail))) := by
    simpa only [diagonalUnitCoefficients_append] using h
  have hcast := diagonalRepresents_heHuFinFamilyCast_both
    (K := K) (by omega :
      2 * pairs + (tailRank + 2) = (2 * pairs + tailRank) + 2)
    (by omega :
      2 * pairs + (2 + tailRank) = 2 * (pairs + 1) + tailRank)
    _ _ h'
  have hsourceFamily :
      heHuFinFamilyCast (by omega :
          2 * pairs + (tailRank + 2) = (2 * pairs + tailRank) + 2)
        (Fin.append
          (standardHyperbolicEndpointTower (K := K) pairs)
          (Fin.append tail (heHuHyperbolicPair (K := K)))) =
        Fin.append
          (Fin.append
            (standardHyperbolicEndpointTower (K := K) pairs) tail)
          (heHuHyperbolicPair (K := K)) := by
    exact heHuFinFamilyCast_append_assoc _
      (standardHyperbolicEndpointTower (K := K) pairs) tail
      (heHuHyperbolicPair (K := K))
  have htargetFamily :
      heHuFinFamilyCast (by omega :
          2 * pairs + (2 + tailRank) = 2 * (pairs + 1) + tailRank)
        (Fin.append
          (standardHyperbolicEndpointTower (K := K) pairs)
          (Fin.append (heHuHyperbolicPair (K := K)) tail)) =
        Fin.append
          (standardHyperbolicEndpointTower (K := K) (pairs + 1)) tail := by
    exact heHuFinFamilyCast_tower_hyperbolic_tail pairs tail
  rw [hsourceFamily, htargetFamily] at hcast
  exact hcast

/-- Casted tower models inherit the hyperbolic-extension isometry. -/
theorem heHuTowerModel_succ_hyperbolicLift_cast
    {tailRank smallRank largeRank : Nat}
    (pairs : Nat) (tail : Fin tailRank → Kˣ)
    (hsmall : 2 * pairs + tailRank = smallRank)
    (hlarge : 2 * (pairs + 1) + tailRank = largeRank) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append
          (heHuFinFamilyCast hsmall
            (Fin.append
              (standardHyperbolicEndpointTower (K := K) pairs) tail))
          (heHuHyperbolicPair (K := K))))
      (diagonalUnitCoefficients
        (heHuFinFamilyCast hlarge
          (Fin.append
            (standardHyperbolicEndpointTower (K := K) (pairs + 1))
            tail))) := by
  have hbase := heHuTowerModel_succ_hyperbolicLift
    (K := K) pairs tail
  have hcast := diagonalRepresents_heHuFinFamilyCast_both
    (K := K) (congrArg (fun q => q + 2) hsmall) hlarge _ _ hbase
  have hsource := heHuFinFamilyCast_append_left hsmall
    (Fin.append
      (standardHyperbolicEndpointTower (K := K) pairs) tail)
    (heHuHyperbolicPair (K := K))
  rw [hsource] at hcast
  exact hcast

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
@[simp] theorem heHuStandardTower_zero_append {tailRank : Nat}
    (tail : Fin tailRank → Kˣ) :
    heHuFinFamilyCast (by omega : 2 * 0 + tailRank = tailRank)
      (Fin.append (standardHyperbolicEndpointTower (K := K) 0) tail) =
        tail := by
  funext i
  unfold heHuFinFamilyCast
  have hi : Fin.cast (by omega : tailRank = 2 * 0 + tailRank) i =
      Fin.natAdd 0 i := by
    apply Fin.ext
    simp
  rw [hi, Fin.append_right]

/-- Closed tower normal form for `W_1` in even dimension. -/
theorem heHuEvenFirst_eq_towerModel (pairs : Nat) (c : Kˣ) :
    heHuEvenFirst pairs c =
      Fin.append (standardHyperbolicEndpointTower (K := K) pairs)
        (heHuBinaryFirst c) := by
  cases pairs with
  | zero =>
      funext i
      fin_cases i <;> rfl
  | succ pairs =>
      simpa only [heHuEvenFirst, heHuEvenFirstTail] using
        heHuFinFamilyCast_tower_hyperbolic_tail
          (K := K) pairs (heHuBinaryFirst c)

/-- The first-column even model gains one hyperbolic plane when the
dimension increases by two. -/
theorem heHuEvenFirst_hyperbolicLift (pairs : Nat) (c : Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append (heHuEvenFirst pairs c)
          (heHuHyperbolicPair (K := K))))
      (diagonalUnitCoefficients (heHuEvenFirst (pairs + 1) c)) := by
  rw [heHuEvenFirst_eq_towerModel,
    heHuEvenFirst_eq_towerModel]
  exact heHuTowerModel_succ_hyperbolicLift pairs (heHuBinaryFirst c)

/-- The first-column odd model gains one hyperbolic plane when the
dimension increases by two. -/
theorem heHuOddFirst_hyperbolicLift (pairs : Nat) (c : Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append (heHuOddFirst pairs c)
          (heHuHyperbolicPair (K := K))))
      (diagonalUnitCoefficients (heHuOddFirst (pairs + 1) c)) := by
  simpa only [heHuOddFirst] using
    heHuTowerModel_succ_hyperbolicLift
      (K := K) pairs (heHuOddFirstTail c)

/-- The second-column odd model gains one hyperbolic plane when the
dimension increases by two. -/
theorem heHuOddSecond_hyperbolicLift (pairs : Nat) (c : Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append (heHuOddSecond pairs c)
          (heHuHyperbolicPair (K := K))))
      (diagonalUnitCoefficients (heHuOddSecond (pairs + 1) c)) := by
  by_cases heven : Even (ordUnit K c)
  · rw [heHuOddSecond_of_even pairs c heven,
      heHuOddSecond_of_even (pairs + 1) c heven]
    exact heHuTowerModel_succ_hyperbolicLift
      pairs (heHuOddSecondTailEven c)
  · rw [heHuOddSecond_of_not_even pairs c heven,
      heHuOddSecond_of_not_even (pairs + 1) c heven]
    exact heHuTowerModel_succ_hyperbolicLift
      pairs (heHuOddSecondTailOdd c)

/-- Every defined second-column even model gains one hyperbolic plane when
the dimension increases by two. -/
theorem heHuEvenSecond_hyperbolicLift (pairs : Nat) (c : Kˣ)
    (hsmall : HeHuEvenSecondDefined pairs c)
    (hlarge : HeHuEvenSecondDefined (pairs + 1) c) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append (heHuEvenSecond pairs c hsmall)
          (heHuHyperbolicPair (K := K))))
      (diagonalUnitCoefficients
        (heHuEvenSecond (pairs + 1) c hlarge)) := by
  classical
  cases pairs with
  | zero =>
      have hnonsquare : ¬ IsSquare c := by
        rcases hsmall with hp | hn
        · omega
        · exact hn
      let delta :=
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
      by_cases hdelta : IsSquare (c / delta)
      · rw [heHuEvenSecond_zero_of_discriminant c hsmall (by
            simpa only [delta] using hdelta),
          heHuEvenSecond_succ_of_discriminant 0 c hlarge hnonsquare (by
            simpa only [delta] using hdelta)]
        unfold heHuEvenDiscriminantTail
        rw [heHuFinFamilyCast_tower_hyperbolic_tail
          (K := K) 0 (heHuDiscriminantBinary c)]
        have hbase := heHuTowerModel_succ_hyperbolicLift_cast
          (K := K) 0 (heHuDiscriminantBinary c)
          (by omega : 2 * 0 + 2 = 2)
          (by omega : 2 * (0 + 1) + 2 = 4)
        rw [heHuStandardTower_zero_append] at hbase
        simpa only [heHuFinFamilyCast_self] using hbase
      · have hc : HeHuSharpDomain c :=
          { notSquare := hnonsquare
            notDiscriminantSquare := by
              simpa only [delta] using hdelta }
        rw [heHuEvenSecond_zero_of_sharp c hsmall hnonsquare (by
              simpa only [delta] using hdelta),
          heHuEvenSecond_succ_of_sharp 0 c hlarge hnonsquare (by
              simpa only [delta] using hdelta)]
        unfold heHuEvenSharpTail
        rw [heHuFinFamilyCast_tower_hyperbolic_tail
          (K := K) 0 (heHuBinarySecond c hc)]
        have hbase := heHuTowerModel_succ_hyperbolicLift_cast
          (K := K) 0 (heHuBinarySecond c hc)
          (by omega : 2 * 0 + 2 = 2)
          (by omega : 2 * (0 + 1) + 2 = 4)
        rw [heHuStandardTower_zero_append] at hbase
        simpa only [heHuFinFamilyCast_self] using hbase
  | succ pairs =>
      by_cases hsquare : IsSquare c
      · rw [heHuEvenSecond_succ_of_square pairs c hsmall hsquare,
          heHuEvenSecond_succ_of_square (pairs + 1) c hlarge hsquare]
        exact heHuTowerModel_succ_hyperbolicLift_cast
          pairs (beliAnisotropicQuaternaryUnits (K := K))
          (by omega) (by omega)
      · let delta :=
          (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
        by_cases hdelta : IsSquare (c / delta)
        · rw [heHuEvenSecond_succ_of_discriminant pairs c hsmall
              hsquare (by simpa only [delta] using hdelta),
            heHuEvenSecond_succ_of_discriminant (pairs + 1) c hlarge
              hsquare (by simpa only [delta] using hdelta)]
          exact heHuTowerModel_succ_hyperbolicLift_cast
            pairs (heHuEvenDiscriminantTail c) (by omega) (by omega)
        · have hc : HeHuSharpDomain c :=
            { notSquare := hsquare
              notDiscriminantSquare := by
                simpa only [delta] using hdelta }
          rw [heHuEvenSecond_succ_of_sharp pairs c hsmall hsquare (by
                simpa only [delta] using hdelta),
            heHuEvenSecond_succ_of_sharp (pairs + 1) c hlarge hsquare (by
                simpa only [delta] using hdelta)]
          exact heHuTowerModel_succ_hyperbolicLift_cast
            pairs (heHuEvenSharpTail c hc) (by omega) (by omega)

/-- Generic form of Proposition 3.5(iii) for the first member of a
two-class determinant pair.  The second large space is the unique target
which misses the first small space. -/
theorem heHuUniqueExcludingFirst_of_hyperbolicPairs {n : Nat}
    (first second : Fin n → Kˣ)
    (largeFirst largeSecond : Fin (n + 2) → Kˣ)
    (smallPair : HeHuSpacePairProperties first second)
    (largePair : HeHuSpacePairProperties largeFirst largeSecond)
    (hfirstLift : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append first (heHuHyperbolicPair (K := K))))
      (diagonalUnitCoefficients largeFirst))
    (hsecondLift : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append second (heHuHyperbolicPair (K := K))))
      (diagonalUnitCoefficients largeSecond)) :
    HeHuUniqueExcludingTarget first largeSecond := by
  classical
  let DF := diagonalUnitDeterminant first
  let DL1 := diagonalUnitDeterminant largeFirst
  let DL2 := diagonalUnitDeterminant largeSecond
  have hnegativeFirst : IsSquare (-DL1 * DF) := by
    simpa only [DL1, DF] using
      negativeDeterminantSquare_of_appendHyperbolic_lift
        first largeFirst hfirstLift
  have hnegativeCandidate : IsSquare (-DL2 * DF) := by
    have hbridge : IsSquare (DL1 * (-DF)) := by
      simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc]
        using hnegativeFirst
    have h := isSquare_mul_trans DL2 DL1 (-DF)
      largePair.determinantSquare hbridge
    simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc]
      using h
  have hfirstIntoLargeFirst :=
    diagonalRepresents_of_appendHyperbolic_lift
      first largeFirst hfirstLift
  have hsecondIntoCandidate :=
    diagonalRepresents_of_appendHyperbolic_lift
      second largeSecond hsecondLift
  refine
    { exactness :=
        { misses := ?_
          represents_other := ?_ }
      unique := ?_ }
  · intro hrep
    have hcollapse :=
      diagonalRepresents_target_to_appendHyperbolic_of_negativeDetSquare
        first largeSecond (by
          simpa only [DL2, DF] using hnegativeCandidate) hrep
    exact largePair.nonisometric (hcollapse.trans hfirstLift)
  · intro w hwNotFirst
    by_cases hwDet : IsSquare
        (diagonalUnitDeterminant w * DF)
    · rcases smallPair.exhaustive w (by
          simpa only [DF] using hwDet) with hwFirst | hwSecond
      · exact (hwNotFirst hwFirst).elim
      · exact hwSecond.trans hsecondIntoCandidate
    · exact diagonalRepresents_of_determinantClass_ne_excluded
        first w largeSecond
          (by simpa only [DL2, DF] using hnegativeCandidate)
          (by simpa only [DF] using hwDet)
  · intro other hother
    have hnegativeOther : IsSquare
        (-diagonalUnitDeterminant other * DF) := by
      by_contra hnot
      exact hother.misses
        (diagonalRepresents_of_not_negative_determinant_square
          first other rfl (by simpa only [DF] using hnot))
    have hotherDet : IsSquare
        (diagonalUnitDeterminant other * DL1) := by
      apply isSquare_mul_trans
          (diagonalUnitDeterminant other) (-DF) DL1
      · simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc]
          using hnegativeOther
      · simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc]
          using hnegativeFirst
    rcases largePair.exhaustive other (by
        simpa only [DL1] using hotherDet) with hotherFirst | hotherSecond
    · have hfirstToOther :=
        hfirstIntoLargeFirst.trans hotherFirst.symm_of_sameRank
      exact (hother.misses hfirstToOther).elim
    · exact hotherSecond

/-- Generic form of Proposition 3.5(iii) for the second member of a
two-class determinant pair.  The first large space is the unique target
which misses the second small space. -/
theorem heHuUniqueExcludingSecond_of_hyperbolicPairs {n : Nat}
    (first second : Fin n → Kˣ)
    (largeFirst largeSecond : Fin (n + 2) → Kˣ)
    (smallPair : HeHuSpacePairProperties first second)
    (largePair : HeHuSpacePairProperties largeFirst largeSecond)
    (hfirstLift : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append first (heHuHyperbolicPair (K := K))))
      (diagonalUnitCoefficients largeFirst))
    (hsecondLift : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append second (heHuHyperbolicPair (K := K))))
      (diagonalUnitCoefficients largeSecond)) :
    HeHuUniqueExcludingTarget second largeFirst := by
  classical
  let DS := diagonalUnitDeterminant second
  let DL1 := diagonalUnitDeterminant largeFirst
  let DL2 := diagonalUnitDeterminant largeSecond
  have hnegativeSecond : IsSquare (-DL2 * DS) := by
    simpa only [DL2, DS] using
      negativeDeterminantSquare_of_appendHyperbolic_lift
        second largeSecond hsecondLift
  have hnegativeCandidate : IsSquare (-DL1 * DS) := by
    have hpair : IsSquare (DL1 * DL2) := by
      simpa only [mul_comm] using largePair.determinantSquare
    have hbridge : IsSquare (DL2 * (-DS)) := by
      simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc]
        using hnegativeSecond
    have h := isSquare_mul_trans DL1 DL2 (-DS) hpair hbridge
    simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc]
      using h
  have hfirstIntoCandidate :=
    diagonalRepresents_of_appendHyperbolic_lift
      first largeFirst hfirstLift
  have hsecondIntoLargeSecond :=
    diagonalRepresents_of_appendHyperbolic_lift
      second largeSecond hsecondLift
  refine
    { exactness :=
        { misses := ?_
          represents_other := ?_ }
      unique := ?_ }
  · intro hrep
    have hcollapse :=
      diagonalRepresents_target_to_appendHyperbolic_of_negativeDetSquare
        second largeFirst (by
          simpa only [DL1, DS] using hnegativeCandidate) hrep
    have hwrong : DiagonalRepresents
        (diagonalUnitCoefficients largeFirst)
        (diagonalUnitCoefficients largeSecond) :=
      hcollapse.trans hsecondLift
    exact largePair.nonisometric hwrong.symm_of_sameRank
  · intro w hwNotSecond
    by_cases hwDet : IsSquare
        (diagonalUnitDeterminant w * DS)
    · have hwFirstDet : IsSquare
          (diagonalUnitDeterminant w *
            diagonalUnitDeterminant first) :=
        isSquare_mul_trans
          (diagonalUnitDeterminant w) DS
          (diagonalUnitDeterminant first) hwDet
          (by simpa only [DS] using smallPair.determinantSquare)
      rcases smallPair.exhaustive w hwFirstDet with hwFirst | hwSecond
      · exact hwFirst.trans hfirstIntoCandidate
      · exact (hwNotSecond hwSecond).elim
    · exact diagonalRepresents_of_determinantClass_ne_excluded
        second w largeFirst
          (by simpa only [DL1, DS] using hnegativeCandidate)
          (by simpa only [DS] using hwDet)
  · intro other hother
    have hnegativeOther : IsSquare
        (-diagonalUnitDeterminant other * DS) := by
      by_contra hnot
      exact hother.misses
        (diagonalRepresents_of_not_negative_determinant_square
          second other rfl (by simpa only [DS] using hnot))
    have hotherDet : IsSquare
        (diagonalUnitDeterminant other * DL1) := by
      apply isSquare_mul_trans
          (diagonalUnitDeterminant other) (-DS) DL1
      · simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc]
          using hnegativeOther
      · simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc]
          using hnegativeCandidate
    rcases largePair.exhaustive other (by
        simpa only [DL1] using hotherDet) with hotherFirst | hotherSecond
    · exact hotherFirst
    · have hsecondToOther :=
        hsecondIntoLargeSecond.trans hotherSecond.symm_of_sameRank
      exact (hother.misses hsecondToOther).elim

/-- Variant of Proposition 3.5(iii) for the exceptional binary determinant
class, where the first model is the sole rank-two isometry class. -/
theorem heHuUniqueExcludingOnlyClass_of_hyperbolicPair {n : Nat}
    (first : Fin n → Kˣ)
    (largeFirst largeSecond : Fin (n + 2) → Kˣ)
    (largePair : HeHuSpacePairProperties largeFirst largeSecond)
    (hfirstLift : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append first (heHuHyperbolicPair (K := K))))
      (diagonalUnitCoefficients largeFirst))
    (hsole : ∀ w : Fin n → Kˣ,
      IsSquare
          (diagonalUnitDeterminant w *
            diagonalUnitDeterminant first) →
        DiagonalRepresents
          (diagonalUnitCoefficients w)
          (diagonalUnitCoefficients first)) :
    HeHuUniqueExcludingTarget first largeSecond := by
  classical
  let DF := diagonalUnitDeterminant first
  let DL1 := diagonalUnitDeterminant largeFirst
  let DL2 := diagonalUnitDeterminant largeSecond
  have hnegativeFirst : IsSquare (-DL1 * DF) := by
    simpa only [DL1, DF] using
      negativeDeterminantSquare_of_appendHyperbolic_lift
        first largeFirst hfirstLift
  have hnegativeCandidate : IsSquare (-DL2 * DF) := by
    have hbridge : IsSquare (DL1 * (-DF)) := by
      simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc]
        using hnegativeFirst
    have h := isSquare_mul_trans DL2 DL1 (-DF)
      largePair.determinantSquare hbridge
    simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc]
      using h
  have hfirstIntoLargeFirst :=
    diagonalRepresents_of_appendHyperbolic_lift
      first largeFirst hfirstLift
  refine
    { exactness :=
        { misses := ?_
          represents_other := ?_ }
      unique := ?_ }
  · intro hrep
    have hcollapse :=
      diagonalRepresents_target_to_appendHyperbolic_of_negativeDetSquare
        first largeSecond (by
          simpa only [DL2, DF] using hnegativeCandidate) hrep
    exact largePair.nonisometric (hcollapse.trans hfirstLift)
  · intro w hwNotFirst
    by_cases hwDet : IsSquare
        (diagonalUnitDeterminant w * DF)
    · exact (hwNotFirst (hsole w (by simpa only [DF] using hwDet))).elim
    · exact diagonalRepresents_of_determinantClass_ne_excluded
        first w largeSecond
          (by simpa only [DL2, DF] using hnegativeCandidate)
          (by simpa only [DF] using hwDet)
  · intro other hother
    have hnegativeOther : IsSquare
        (-diagonalUnitDeterminant other * DF) := by
      by_contra hnot
      exact hother.misses
        (diagonalRepresents_of_not_negative_determinant_square
          first other rfl (by simpa only [DF] using hnot))
    have hotherDet : IsSquare
        (diagonalUnitDeterminant other * DL1) := by
      apply isSquare_mul_trans
          (diagonalUnitDeterminant other) (-DF) DL1
      · simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc]
          using hnegativeOther
      · simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc]
          using hnegativeFirst
    rcases largePair.exhaustive other (by
        simpa only [DL1] using hotherDet) with hotherFirst | hotherSecond
    · have hfirstToOther :=
        hfirstIntoLargeFirst.trans hotherFirst.symm_of_sameRank
      exact (hother.misses hfirstToOther).elim
    · exact hotherSecond

/-- Canonical proof-independent name for the always-defined second model
in the next even dimension. -/
noncomputable def heHuEvenSecondNext (pairs : Nat) (c : Kˣ) :
    Fin (2 * (pairs + 1) + 2) → Kˣ :=
  heHuEvenSecond (pairs + 1) c
    (Or.inl (Nat.succ_pos pairs))

/-- Proposition 3.5(iii), odd dimension, excluding `W_1^n(c)`: the unique
target is `W_2^(n+2)(c)`. -/
theorem heHu2022Proposition35iiiOddFirst (pairs : Nat) (c : Kˣ) :
    HeHuUniqueExcludingTarget
      (heHuOddFirst pairs c)
      (heHuFinFamilyCast (by omega :
          2 * (pairs + 1) + 3 = (2 * pairs + 3) + 2)
        (heHuOddSecond (pairs + 1) c)) := by
  let hdim : 2 * (pairs + 1) + 3 = (2 * pairs + 3) + 2 := by omega
  have smallPair := heHu2022Definition34Proposition35Odd
    (K := K) pairs c
  have largePairRaw := heHu2022Definition34Proposition35Odd
    (K := K) (pairs + 1) c
  have largePair := largePairRaw.cast hdim
  have hfirstRaw := heHuOddFirst_hyperbolicLift
    (K := K) pairs c
  have hsecondRaw := heHuOddSecond_hyperbolicLift
    (K := K) pairs c
  have hfirst := diagonalRepresents_heHuFinFamilyCast_both
    (K := K) (rfl : (2 * pairs + 3) + 2 = (2 * pairs + 3) + 2)
    hdim _ _ hfirstRaw
  have hsecond := diagonalRepresents_heHuFinFamilyCast_both
    (K := K) (rfl : (2 * pairs + 3) + 2 = (2 * pairs + 3) + 2)
    hdim _ _ hsecondRaw
  simpa only [heHuFinFamilyCast_self] using
    heHuUniqueExcludingFirst_of_hyperbolicPairs
      (heHuOddFirst pairs c) (heHuOddSecond pairs c)
      (heHuFinFamilyCast hdim (heHuOddFirst (pairs + 1) c))
      (heHuFinFamilyCast hdim (heHuOddSecond (pairs + 1) c))
      smallPair largePair
      (by simpa only [heHuFinFamilyCast_self] using hfirst)
      (by simpa only [heHuFinFamilyCast_self] using hsecond)

/-- Proposition 3.5(iii), odd dimension, excluding `W_2^n(c)`: the unique
target is `W_1^(n+2)(c)`. -/
theorem heHu2022Proposition35iiiOddSecond (pairs : Nat) (c : Kˣ) :
    HeHuUniqueExcludingTarget
      (heHuOddSecond pairs c)
      (heHuFinFamilyCast (by omega :
          2 * (pairs + 1) + 3 = (2 * pairs + 3) + 2)
        (heHuOddFirst (pairs + 1) c)) := by
  let hdim : 2 * (pairs + 1) + 3 = (2 * pairs + 3) + 2 := by omega
  have smallPair := heHu2022Definition34Proposition35Odd
    (K := K) pairs c
  have largePairRaw := heHu2022Definition34Proposition35Odd
    (K := K) (pairs + 1) c
  have largePair := largePairRaw.cast hdim
  have hfirstRaw := heHuOddFirst_hyperbolicLift
    (K := K) pairs c
  have hsecondRaw := heHuOddSecond_hyperbolicLift
    (K := K) pairs c
  have hfirst := diagonalRepresents_heHuFinFamilyCast_both
    (K := K) (rfl : (2 * pairs + 3) + 2 = (2 * pairs + 3) + 2)
    hdim _ _ hfirstRaw
  have hsecond := diagonalRepresents_heHuFinFamilyCast_both
    (K := K) (rfl : (2 * pairs + 3) + 2 = (2 * pairs + 3) + 2)
    hdim _ _ hsecondRaw
  simpa only [heHuFinFamilyCast_self] using
    heHuUniqueExcludingSecond_of_hyperbolicPairs
      (heHuOddFirst pairs c) (heHuOddSecond pairs c)
      (heHuFinFamilyCast hdim (heHuOddFirst (pairs + 1) c))
      (heHuFinFamilyCast hdim (heHuOddSecond (pairs + 1) c))
      smallPair largePair
      (by simpa only [heHuFinFamilyCast_self] using hfirst)
      (by simpa only [heHuFinFamilyCast_self] using hsecond)

/-- Proposition 3.5(iii), even dimension, excluding `W_1^n(c)`.  This
includes the exceptional binary square determinant class, where `W_2^2(c)`
is undefined but `W_2^4(c)` is still the unique excluding target. -/
theorem heHu2022Proposition35iiiEvenFirst (pairs : Nat) (c : Kˣ) :
    HeHuUniqueExcludingTarget
      (heHuEvenFirst pairs c)
      (heHuFinFamilyCast (by omega :
          2 * (pairs + 1) + 2 = (2 * pairs + 2) + 2)
        (heHuEvenSecondNext pairs c)) := by
  classical
  let hdim : 2 * (pairs + 1) + 2 = (2 * pairs + 2) + 2 := by omega
  have hlarge : HeHuEvenSecondDefined (pairs + 1) c :=
    Or.inl (Nat.succ_pos pairs)
  have largePairRaw := heHu2022Definition34Proposition35Even
    (K := K) (pairs + 1) c hlarge
  have largePair := largePairRaw.cast hdim
  have hfirstRaw := heHuEvenFirst_hyperbolicLift
    (K := K) pairs c
  have hfirst := diagonalRepresents_heHuFinFamilyCast_both
    (K := K) (rfl : (2 * pairs + 2) + 2 = (2 * pairs + 2) + 2)
    hdim _ _ hfirstRaw
  by_cases hsmall : HeHuEvenSecondDefined pairs c
  · have smallPair := heHu2022Definition34Proposition35Even
      (K := K) pairs c hsmall
    have hsecondRaw := heHuEvenSecond_hyperbolicLift
      (K := K) pairs c hsmall hlarge
    have hsecond := diagonalRepresents_heHuFinFamilyCast_both
      (K := K) (rfl : (2 * pairs + 2) + 2 = (2 * pairs + 2) + 2)
      hdim _ _ hsecondRaw
    simpa only [heHuEvenSecondNext, heHuFinFamilyCast_self] using
      heHuUniqueExcludingFirst_of_hyperbolicPairs
        (heHuEvenFirst pairs c) (heHuEvenSecond pairs c hsmall)
        (heHuFinFamilyCast hdim (heHuEvenFirst (pairs + 1) c))
        (heHuFinFamilyCast hdim
          (heHuEvenSecond (pairs + 1) c hlarge))
        smallPair largePair
        (by simpa only [heHuFinFamilyCast_self] using hfirst)
        (by simpa only [heHuFinFamilyCast_self] using hsecond)
  · have hpairs : pairs = 0 := by
      by_contra hp
      exact hsmall (Or.inl (Nat.pos_of_ne_zero hp))
    subst pairs
    have hc : IsSquare c := by
      by_contra hc
      exact hsmall (Or.inr hc)
    have hsole : ∀ w : Fin 2 → Kˣ,
        IsSquare
            (diagonalUnitDeterminant w *
              diagonalUnitDeterminant (heHuEvenFirst 0 c)) →
          DiagonalRepresents
            (diagonalUnitCoefficients w)
            (diagonalUnitCoefficients (heHuEvenFirst 0 c)) := by
      intro w hw
      simpa only [heHuEvenFirst] using
        heHuBinarySquareClass_represents_first w c hc
          (by simpa only [heHuEvenFirst] using hw)
    simpa only [heHuEvenSecondNext, heHuFinFamilyCast_self] using
      heHuUniqueExcludingOnlyClass_of_hyperbolicPair
        (heHuEvenFirst 0 c)
        (heHuFinFamilyCast hdim (heHuEvenFirst 1 c))
        (heHuFinFamilyCast hdim (heHuEvenSecond 1 c hlarge))
        largePair
        (by simpa only [heHuFinFamilyCast_self] using hfirst)
        hsole

/-- Proposition 3.5(iii), even dimension, excluding a defined
`W_2^n(c)`: the unique target is `W_1^(n+2)(c)`. -/
theorem heHu2022Proposition35iiiEvenSecond (pairs : Nat) (c : Kˣ)
    (hsmall : HeHuEvenSecondDefined pairs c) :
    HeHuUniqueExcludingTarget
      (heHuEvenSecond pairs c hsmall)
      (heHuFinFamilyCast (by omega :
          2 * (pairs + 1) + 2 = (2 * pairs + 2) + 2)
        (heHuEvenFirst (pairs + 1) c)) := by
  let hdim : 2 * (pairs + 1) + 2 = (2 * pairs + 2) + 2 := by omega
  have hlarge : HeHuEvenSecondDefined (pairs + 1) c :=
    Or.inl (Nat.succ_pos pairs)
  have smallPair := heHu2022Definition34Proposition35Even
    (K := K) pairs c hsmall
  have largePairRaw := heHu2022Definition34Proposition35Even
    (K := K) (pairs + 1) c hlarge
  have largePair := largePairRaw.cast hdim
  have hfirstRaw := heHuEvenFirst_hyperbolicLift
    (K := K) pairs c
  have hsecondRaw := heHuEvenSecond_hyperbolicLift
    (K := K) pairs c hsmall hlarge
  have hfirst := diagonalRepresents_heHuFinFamilyCast_both
    (K := K) (rfl : (2 * pairs + 2) + 2 = (2 * pairs + 2) + 2)
    hdim _ _ hfirstRaw
  have hsecond := diagonalRepresents_heHuFinFamilyCast_both
    (K := K) (rfl : (2 * pairs + 2) + 2 = (2 * pairs + 2) + 2)
    hdim _ _ hsecondRaw
  simpa only [heHuFinFamilyCast_self] using
    heHuUniqueExcludingSecond_of_hyperbolicPairs
      (heHuEvenFirst pairs c) (heHuEvenSecond pairs c hsmall)
      (heHuFinFamilyCast hdim (heHuEvenFirst (pairs + 1) c))
      (heHuFinFamilyCast hdim
        (heHuEvenSecond (pairs + 1) c hlarge))
      smallPair largePair
      (by simpa only [heHuFinFamilyCast_self] using hfirst)
      (by simpa only [heHuFinFamilyCast_self] using hsecond)

end Bong
