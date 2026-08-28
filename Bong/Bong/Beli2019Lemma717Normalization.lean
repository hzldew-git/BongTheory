/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.AlternatingEndpointTowerNormalizationProof
import Bong.Bong.AdjacentNormGeneratorChange
import Bong.Bong.BeliDiscriminantNormGenerator
import Bong.Bong.Beli2019Lemma717Boundary
import Bong.Bong.Beli2019Lemma718OrderProfiles
import Bong.Bong.Beli2019Lemma75EndpointClass
import Bong.Bong.BeliCorollary44ThreeBlockProof

/-!
# Beli (2019), Lemma 7.17: integral normalization

This file implements the change of BONG used between Lemmas 7.17 and 7.18.
It first develops the exact canonical coefficient towers and their determinant
classes.  The source prefix is then normalized through the separately named
integral endpoint-tower classification interface.  In type III, paragraph
3.12 of Beli (2003) first toggles the discriminant class at the last boundary
pair when necessary.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The repeated canonical hyperbolic source tower in Lemma 7.18(i),(iii). -/
noncomputable def lemma717CanonicalTowerValues
    (R : Int) (pairs : Nat) : Fin (2 * pairs) → Kˣ := fun i ↦
  if Even i.val then lemma718CanonicalHigh (K := K) R
  else lemma718CanonicalLow (K := K) R

theorem lemma717CanonicalTowerValues_even
    (R : Int) (pairs : Nat) (i : Fin (2 * pairs)) (hi : Even i.val) :
    lemma717CanonicalTowerValues (K := K) R pairs i =
      lemma718CanonicalHigh (K := K) R := by
  simp [lemma717CanonicalTowerValues, hi]

theorem lemma717CanonicalTowerValues_odd
    (R : Int) (pairs : Nat) (i : Fin (2 * pairs)) (hi : Odd i.val) :
    lemma717CanonicalTowerValues (K := K) R pairs i =
      lemma718CanonicalLow (K := K) R := by
  simp [lemma717CanonicalTowerValues, Nat.not_even_iff_odd.mpr hi]

/-- The determinant of the repeated canonical tower is the expected power
of the binary determinant. -/
theorem diagonalUnitDeterminant_lemma717CanonicalTowerValues
    (R : Int) (pairs : Nat) :
    diagonalUnitDeterminant
        (lemma717CanonicalTowerValues (K := K) R pairs) =
      (lemma718CanonicalHigh (K := K) R *
        lemma718CanonicalLow (K := K) R) ^ pairs := by
  unfold diagonalUnitDeterminant
  let e : Fin pairs × Fin 2 ≃ Fin (2 * pairs) :=
    finProdFinEquiv.trans (finCongr (by omega))
  have hprod := Fintype.prod_equiv e
    (fun ij : Fin pairs × Fin 2 ↦
      lemma717CanonicalTowerValues (K := K) R pairs (e ij))
    (lemma717CanonicalTowerValues (K := K) R pairs)
    (fun _ ↦ by rfl)
  rw [Fintype.prod_prod_type] at hprod
  simp only [Fin.prod_univ_two] at hprod
  have hezero (t : Fin pairs) :
      (e (t, 0)).val = 2 * t.val := by
    simp [e, finProdFinEquiv]
  have heone (t : Fin pairs) :
      (e (t, 1)).val = 2 * t.val + 1 := by
    simp [e, finProdFinEquiv]
    omega
  have heval (t : Fin pairs) :
      lemma717CanonicalTowerValues (K := K) R pairs (e (t, 0)) *
        lemma717CanonicalTowerValues (K := K) R pairs (e (t, 1)) =
      lemma718CanonicalHigh (K := K) R *
        lemma718CanonicalLow (K := K) R := by
    have hEven : Even (e (t, 0)).val :=
      ⟨t.val, by rw [hezero]; omega⟩
    have hOdd : Odd (e (t, 1)).val := ⟨t.val, by rw [heone]⟩
    rw [lemma717CanonicalTowerValues_even R pairs (e (t, 0)) hEven,
      lemma717CanonicalTowerValues_odd R pairs (e (t, 1)) hOdd]
  calc
    (∏ i, lemma717CanonicalTowerValues (K := K) R pairs i) =
        ∏ _ : Fin pairs,
          (lemma718CanonicalHigh (K := K) R *
            lemma718CanonicalLow (K := K) R) := by
      simpa only [heval] using hprod.symm
    _ = _ := by simp

/-- One canonical binary block has square signed determinant. -/
theorem lemma718CanonicalPair_signedProduct_isSquare (R : Int) :
    IsSquare (-(lemma718CanonicalHigh (K := K) R *
      lemma718CanonicalLow (K := K) R)) := by
  let high := lemma718CanonicalHigh (K := K) R
  let low := lemma718CanonicalLow (K := K) R
  have hratio : IsSquare (-(high / low)) :=
    lemma718CanonicalPair_signedRatio_isSquare R
  have heq : -(high * low) = -(high / low) * low ^ 2 := by
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_div_eq_div_val,
      Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero low]
  rw [heq]
  exact hratio.mul ⟨low, by simp [pow_two]⟩

/-- Every pair of the canonical tower is in the hyperbolic endpoint class. -/
theorem lemma717CanonicalTowerValues_pairClasses
    [DyadicDiscriminantClassLaws K]
    (R : Int) (pairs : Nat) :
    AlternatingEndpointPairClasses
      (lemma717CanonicalTowerValues (K := K) R pairs) := by
  intro t
  left
  have hEven : Even (2 * t.val) := ⟨t.val, by omega⟩
  have hOdd : Odd (2 * t.val + 1) := ⟨t.val, by omega⟩
  rw [lemma717CanonicalTowerValues_even R pairs ⟨2 * t.val, by omega⟩ hEven,
    lemma717CanonicalTowerValues_odd R pairs
      ⟨2 * t.val + 1, by omega⟩ hOdd]
  exact lemma718CanonicalPair_signedProduct_isSquare R

/-- The complete signed determinant of the canonical tower is a square. -/
theorem signedDeterminant_lemma717CanonicalTowerValues_isSquare
    (R : Int) (pairs : Nat) :
    IsSquare (((-1 : Kˣ) ^ pairs) *
      diagonalUnitDeterminant
        (lemma717CanonicalTowerValues (K := K) R pairs)) := by
  rw [diagonalUnitDeterminant_lemma717CanonicalTowerValues]
  have heq : ((-1 : Kˣ) ^ pairs) *
        (lemma718CanonicalHigh (K := K) R *
          lemma718CanonicalLow (K := K) R) ^ pairs =
      (-(lemma718CanonicalHigh (K := K) R *
          lemma718CanonicalLow (K := K) R)) ^ pairs := by
    rw [← mul_pow]
    congr 1
    apply Units.ext
    simp
  rw [heq]
  exact (lemma718CanonicalPair_signedProduct_isSquare R).pow pairs

/-- The type-II source tower: only its second coefficient carries the
distinguished discriminant factor. -/
noncomputable def lemma717TypeIICanonicalTowerValues
    [laws : DyadicDiscriminantClassLaws K]
    (R : Int) (pairs : Nat) (hpairs : 0 < pairs) :
    Fin (2 * pairs) → Kˣ :=
  Function.update (lemma717CanonicalTowerValues (K := K) R pairs)
    ⟨1, by omega⟩
    (laws.discriminantUnit * lemma718CanonicalLow (K := K) R)

theorem lemma717TypeIICanonicalTowerValues_zero
    [DyadicDiscriminantClassLaws K]
    (R : Int) (pairs : Nat) (hpairs : 0 < pairs) :
    lemma717TypeIICanonicalTowerValues (K := K) R pairs hpairs
        ⟨0, by omega⟩ = lemma718CanonicalHigh (K := K) R := by
  simp [lemma717TypeIICanonicalTowerValues, lemma717CanonicalTowerValues]

theorem lemma717TypeIICanonicalTowerValues_one
    [laws : DyadicDiscriminantClassLaws K]
    (R : Int) (pairs : Nat) (hpairs : 0 < pairs) :
    lemma717TypeIICanonicalTowerValues (K := K) R pairs hpairs
        ⟨1, by omega⟩ =
      -(laws.discriminantUnit * uniformizerPowerUnit K
        (R - 2 * (ramificationIndex K : Int))) := by
  rw [show lemma717TypeIICanonicalTowerValues (K := K) R pairs hpairs
      ⟨1, by omega⟩ = laws.discriminantUnit *
        lemma718CanonicalLow (K := K) R by
    simp [lemma717TypeIICanonicalTowerValues]]
  unfold lemma718CanonicalLow
  apply Units.ext
  simp

theorem lemma717TypeIICanonicalTowerValues_of_two_le
    [DyadicDiscriminantClassLaws K]
    (R : Int) (pairs : Nat) (hpairs : 0 < pairs)
    (i : Fin (2 * pairs)) (hi : 2 ≤ i.val) :
    lemma717TypeIICanonicalTowerValues (K := K) R pairs hpairs i =
      lemma717CanonicalTowerValues (K := K) R pairs i := by
  have hne : i ≠ (⟨1, by omega⟩ : Fin (2 * pairs)) := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = 1 at hv
    omega
  simp [lemma717TypeIICanonicalTowerValues, Function.update, hne]

/-- The type-II determinant is the canonical determinant times `Delta`. -/
theorem diagonalUnitDeterminant_lemma717TypeIICanonicalTowerValues
    [laws : DyadicDiscriminantClassLaws K]
    (R : Int) (pairs : Nat) (hpairs : 0 < pairs) :
    diagonalUnitDeterminant
        (lemma717TypeIICanonicalTowerValues (K := K) R pairs hpairs) =
      diagonalUnitDeterminant
          (lemma717CanonicalTowerValues (K := K) R pairs) *
        laws.discriminantUnit := by
  classical
  let one : Fin (2 * pairs) := ⟨1, by omega⟩
  let canonical := lemma717CanonicalTowerValues (K := K) R pairs
  have hcanonicalOne : canonical one =
      lemma718CanonicalLow (K := K) R := by
    apply lemma717CanonicalTowerValues_odd
    exact ⟨0, by simp [one]⟩
  have hcanonical := Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
    (Finset.mem_univ one) canonical
  unfold diagonalUnitDeterminant
  rw [show lemma717TypeIICanonicalTowerValues (K := K) R pairs hpairs =
      Function.update canonical one
        (laws.discriminantUnit * lemma718CanonicalLow (K := K) R) by rfl]
  rw [Finset.prod_update_of_mem (Finset.mem_univ one)]
  rw [hcanonicalOne] at hcanonical
  rw [hcanonical]
  ac_rfl

/-- The first type-II pair is discriminant-twisted; all later pairs are
canonical hyperbolic endpoint blocks. -/
theorem lemma717TypeIICanonicalTowerValues_pairClasses
    [laws : DyadicDiscriminantClassLaws K]
    (R : Int) (pairs : Nat) (hpairs : 0 < pairs) :
    AlternatingEndpointPairClasses
      (lemma717TypeIICanonicalTowerValues (K := K) R pairs hpairs) := by
  intro t
  by_cases ht : t.val = 0
  · right
    have hzero : (⟨2 * t.val, by omega⟩ : Fin (2 * pairs)) =
        ⟨0, by omega⟩ := by
      apply Fin.ext
      change 2 * t.val = 0
      omega
    have hone : (⟨2 * t.val + 1, by omega⟩ : Fin (2 * pairs)) =
        ⟨1, by omega⟩ := by
      apply Fin.ext
      change 2 * t.val + 1 = 1
      omega
    rw [hzero, hone, lemma717TypeIICanonicalTowerValues_zero,
      lemma717TypeIICanonicalTowerValues_one]
    have hbase := lemma718CanonicalPair_signedProduct_isSquare (K := K) R
    have heq :
        (-(lemma718CanonicalHigh (K := K) R *
            (-(laws.discriminantUnit * uniformizerPowerUnit K
              (R - 2 * (ramificationIndex K : Int))))) *
          laws.discriminantUnit) =
        (-(lemma718CanonicalHigh (K := K) R *
            lemma718CanonicalLow (K := K) R)) *
          laws.discriminantUnit ^ 2 := by
      unfold lemma718CanonicalLow
      apply Units.ext
      simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    rw [heq]
    exact hbase.mul ⟨laws.discriminantUnit, by simp [pow_two]⟩
  · left
    have htwo : 2 ≤ 2 * t.val := by omega
    have htwoOne : 2 ≤ 2 * t.val + 1 := by omega
    rw [lemma717TypeIICanonicalTowerValues_of_two_le R pairs hpairs _ htwo,
      lemma717TypeIICanonicalTowerValues_of_two_le R pairs hpairs _ htwoOne]
    have hEven : Even (2 * t.val) := ⟨t.val, by omega⟩
    have hOdd : Odd (2 * t.val + 1) := ⟨t.val, by omega⟩
    rw [lemma717CanonicalTowerValues_even R pairs _ hEven,
      lemma717CanonicalTowerValues_odd R pairs _ hOdd]
    exact lemma718CanonicalPair_signedProduct_isSquare R

/-- The signed type-II determinant becomes a square after multiplying by
the discriminant unit. -/
theorem
    signedDeterminant_lemma717TypeIICanonicalTowerValues_twisted_isSquare
    [laws : DyadicDiscriminantClassLaws K]
    (R : Int) (pairs : Nat) (hpairs : 0 < pairs) :
    IsSquare (((-1 : Kˣ) ^ pairs *
      diagonalUnitDeterminant
        (lemma717TypeIICanonicalTowerValues (K := K) R pairs hpairs)) *
      laws.discriminantUnit) := by
  rw [diagonalUnitDeterminant_lemma717TypeIICanonicalTowerValues]
  have hbase := signedDeterminant_lemma717CanonicalTowerValues_isSquare
    (K := K) R pairs
  have heq :
      (((-1 : Kˣ) ^ pairs *
          (diagonalUnitDeterminant
            (lemma717CanonicalTowerValues (K := K) R pairs) *
              laws.discriminantUnit)) * laws.discriminantUnit) =
        (((-1 : Kˣ) ^ pairs *
          diagonalUnitDeterminant
            (lemma717CanonicalTowerValues (K := K) R pairs)) *
          laws.discriminantUnit ^ 2) := by
    simp only [pow_two]
    ac_rfl
  rw [heq]
  exact hbase.mul ⟨laws.discriminantUnit, by simp [pow_two]⟩

/-- The canonical tower has the alternating order profile `R, R - 2e`. -/
theorem ordUnit_lemma717CanonicalTowerValues
    (R : Int) (pairs : Nat) (i : Fin (2 * pairs)) :
    ordUnit K (lemma717CanonicalTowerValues (K := K) R pairs i) =
      if Even i.val then R
      else R - 2 * (ramificationIndex K : Int) := by
  by_cases hi : Even i.val
  · rw [if_pos hi, lemma717CanonicalTowerValues_even R pairs i hi,
      ordUnit_lemma718CanonicalHigh]
  · have hiOdd : Odd i.val := Nat.not_even_iff_odd.mp hi
    rw [if_neg hi, lemma717CanonicalTowerValues_odd R pairs i hiOdd,
      ordUnit_lemma718CanonicalLow]

/-- Multiplying the second canonical coefficient by the discriminant unit
does not change the alternating order profile. -/
theorem ordUnit_lemma717TypeIICanonicalTowerValues
    [laws : DyadicDiscriminantClassLaws K]
    (R : Int) (pairs : Nat) (hpairs : 0 < pairs)
    (i : Fin (2 * pairs)) :
    ordUnit K
        (lemma717TypeIICanonicalTowerValues (K := K) R pairs hpairs i) =
      if Even i.val then R
      else R - 2 * (ramificationIndex K : Int) := by
  by_cases hiZero : i.val = 0
  · have hi : i = ⟨0, by omega⟩ := Fin.ext hiZero
    rw [hi, lemma717TypeIICanonicalTowerValues_zero,
      ordUnit_lemma718CanonicalHigh]
    simp
  · by_cases hiOne : i.val = 1
    · have hi : i = ⟨1, by omega⟩ := Fin.ext hiOne
      rw [hi, lemma717TypeIICanonicalTowerValues_one,
        ordUnit_neg, ordUnit_mul,
        (isValuationUnit_iff_ordUnit_eq_zero K laws.discriminantUnit).1
          laws.discriminant_isValuationUnit,
        ordUnit_uniformizerPowerUnit]
      simp
    · have hiTwo : 2 ≤ i.val := by omega
      rw [lemma717TypeIICanonicalTowerValues_of_two_le R pairs hpairs i hiTwo,
        ordUnit_lemma717CanonicalTowerValues]

/-- The canonical type-I/III tower has the rigid order profile required by
the integral normalization theorem. -/
theorem lemma717CanonicalTowerValues_orderProfile
    (R : Int) (pairs : Nat) :
    AlternatingEndpointOrderProfile
      (lemma717CanonicalTowerValues (K := K) R pairs) R := by
  intro t
  constructor
  · rw [ordUnit_lemma717CanonicalTowerValues]
    have heven : Even (2 * t.val) := ⟨t.val, by omega⟩
    rw [if_pos heven]
  · rw [ordUnit_lemma717CanonicalTowerValues]
    have hodd : ¬Even (2 * t.val + 1) := by
      rintro ⟨k, hk⟩
      omega
    rw [if_neg hodd]

/-- The type-II canonical tower has the same rigid order profile. -/
theorem lemma717TypeIICanonicalTowerValues_orderProfile
    [DyadicDiscriminantClassLaws K]
    (R : Int) (pairs : Nat) (hpairs : 0 < pairs) :
    AlternatingEndpointOrderProfile
      (lemma717TypeIICanonicalTowerValues (K := K) R pairs hpairs) R := by
  intro t
  constructor
  · rw [ordUnit_lemma717TypeIICanonicalTowerValues]
    have heven : Even (2 * t.val) := ⟨t.val, by omega⟩
    rw [if_pos heven]
  · rw [ordUnit_lemma717TypeIICanonicalTowerValues]
    have hodd : ¬Even (2 * t.val + 1) := by
      rintro ⟨k, hk⟩
      omega
    rw [if_neg hodd]

/-- Cancelling the common square of a sign from two signed square classes. -/
theorem isSquare_product_of_same_signed
    (sign x y : Kˣ)
    (hx : IsSquare (sign * x))
    (hy : IsSquare (sign * y)) :
    IsSquare (x * y) := by
  have hquotient := (hx.mul hy).div
    (show IsSquare (sign ^ 2) from ⟨sign, by simp [pow_two]⟩)
  have hcancel : ((sign * x) * (sign * y)) / sign ^ 2 = x * y := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul,
      Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero sign]
  rwa [hcancel] at hquotient

/-- Cancelling the common square of `sign * Delta` from two identically
discriminant-twisted square classes. -/
theorem isSquare_product_of_same_signed_discriminant
    [laws : DyadicDiscriminantClassLaws K]
    (sign x y : Kˣ)
    (hx : IsSquare (sign * x * laws.discriminantUnit))
    (hy : IsSquare (sign * y * laws.discriminantUnit)) :
    IsSquare (x * y) := by
  let common := sign * laws.discriminantUnit
  have hquotient := (hx.mul hy).div
    (show IsSquare (common ^ 2) from ⟨common, by simp [pow_two]⟩)
  have hcancel : ((sign * x * laws.discriminantUnit) *
        (sign * y * laws.discriminantUnit)) / common ^ 2 = x * y := by
    apply Units.ext
    simp only [common, Units.val_div_eq_div_val, Units.val_mul,
      Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero sign, Units.ne_zero laws.discriminantUnit]
  rwa [hcancel] at hquotient

private theorem even_le_sub_two_of_lt {i s : Nat}
    (his : i < s) (hi : Even i) (hs : Even s) : i ≤ s - 2 := by
  rcases hi with ⟨t, ht⟩
  rcases hs with ⟨d, hd⟩
  omega

private theorem even_sub_one_of_odd {i : Nat} (hi : Odd i) :
    Even (i - 1) := by
  rcases hi with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  omega

private theorem one_le_of_odd {i : Nat} (hi : Odd i) : 1 ≤ i := by
  exact hi.pos

private theorem succ_sub_two_eq_sub_one {s : Nat} (hs : 2 ≤ s) :
    (s - 2) + 1 = s - 1 := by
  omega

/-- The stopping index is exactly twice the number of binary blocks in its
prefix. -/
theorem Lemma717StoppingData.two_mul_half
    {a : GoodBONG q L (n + 3)} {R : Int} {s : Nat}
    (D : Lemma717StoppingData a R s) : 2 * (s / 2) = s := by
  rcases D.even with ⟨d, hd⟩
  omega

/-- A Lemma 7.17 stopping prefix contains at least one binary block. -/
theorem Lemma717StoppingData.half_pos
    {a : GoodBONG q L (n + 3)} {R : Int} {s : Nat}
    (D : Lemma717StoppingData a R s) : 0 < s / 2 := by
  have hEq := D.two_mul_half
  have hTwo := D.two_le
  by_contra hnot
  have hzero : s / 2 = 0 := Nat.eq_zero_of_not_pos hnot
  omega

/-- On the stopped prefix, all even-numbered coefficients have order `R`. -/
theorem lemma717_prefixOrder_even
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData a R s)
    (hfirst : a.order (0 : Fin (n + 3)) = R)
    (i : Fin (n + 3)) (his : i.val < s) (hiEven : Even i.val) :
    a.order i = R := by
  let first : Fin (n + 2) := ⟨0, by omega⟩
  have hlast : s - 2 < n + 2 := by
    have hsBound := D.le_rank
    omega
  let last : Fin (n + 2) := ⟨s - 2, hlast⟩
  have hfirstLe : first ≤ last := by
    change 0 ≤ s - 2
    omega
  have hevenSegment : Even (last.val - first.val) := by
    rcases D.even with ⟨d, hd⟩
    refine ⟨d - 1, ?_⟩
    simp only [last, first, Nat.sub_zero]
    omega
  have hfirstOrder : a.order first.castSucc = R := by
    have hindex : first.castSucc = (0 : Fin (n + 3)) := Fin.ext rfl
    rw [hindex]
    exact hfirst
  have hterminal : a.order last.succ =
      R - 2 * (ramificationIndex K : Int) := by
    have hindex : last.succ = ⟨s - 1, by omega⟩ := by
      apply Fin.ext
      change (s - 2) + 1 = s - 1
      exact succ_sub_two_eq_sub_one D.two_le
    rw [hindex]
    exact D.terminal
  let C := a.beli2019Lemma75_arithmetic first last R hfirstLe
    hevenSegment hfirstOrder hterminal
  have hiLast : i.val ≤ s - 2 :=
    even_le_sub_two_of_lt his hiEven D.even
  have hkBound : i.val < n + 2 := lt_of_le_of_lt hiLast hlast
  let k : Fin (n + 2) := ⟨i.val, hkBound⟩
  have hik : first ≤ k := by
    change 0 ≤ i.val
    exact Nat.zero_le i.val
  have hkj : k ≤ last := by
    exact Fin.mk_le_mk.mpr hiLast
  have hkEven : Even (k.val - first.val) := by
    change Even (i.val - 0)
    simpa only [Nat.sub_zero] using hiEven
  have hk := C.even_order k hik hkj hkEven
  have hindex : k.castSucc = i := Fin.ext rfl
  rwa [hindex] at hk

/-- On the stopped prefix, all odd-numbered coefficients have order
`R - 2e`. -/
theorem lemma717_prefixOrder_odd
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData a R s)
    (hfirst : a.order (0 : Fin (n + 3)) = R)
    (i : Fin (n + 3)) (his : i.val < s) (hiOdd : Odd i.val) :
    a.order i = R - 2 * (ramificationIndex K : Int) := by
  let first : Fin (n + 2) := ⟨0, by omega⟩
  have hlast : s - 2 < n + 2 := by
    have hsBound := D.le_rank
    omega
  let last : Fin (n + 2) := ⟨s - 2, hlast⟩
  have hfirstLe : first ≤ last := by
    change 0 ≤ s - 2
    omega
  have hevenSegment : Even (last.val - first.val) := by
    rcases D.even with ⟨d, hd⟩
    refine ⟨d - 1, ?_⟩
    simp only [last, first, Nat.sub_zero]
    omega
  have hfirstOrder : a.order first.castSucc = R := by
    have hindex : first.castSucc = (0 : Fin (n + 3)) := Fin.ext rfl
    rw [hindex]
    exact hfirst
  have hterminal : a.order last.succ =
      R - 2 * (ramificationIndex K : Int) := by
    have hindex : last.succ = ⟨s - 1, by omega⟩ := by
      apply Fin.ext
      change (s - 2) + 1 = s - 1
      exact succ_sub_two_eq_sub_one D.two_le
    rw [hindex]
    exact D.terminal
  let C := a.beli2019Lemma75_arithmetic first last R hfirstLe
    hevenSegment hfirstOrder hterminal
  have hik : first.val + 1 ≤ i.val := by
    change 1 ≤ i.val
    exact one_le_of_odd hiOdd
  have hkj : i.val ≤ last.val + 1 := by
    change i.val ≤ (s - 2) + 1
    omega
  have hEvenOffset : Even (i.val - (first.val + 1)) := by
    change Even (i.val - 1)
    exact even_sub_one_of_odd hiOdd
  apply C.odd_order i
  · exact hik
  · exact hkj
  · exact hEvenOffset

/-- The stopped source prefix itself has the alternating order profile. -/
theorem ordUnit_lemma717_sourcePrefix
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData a R s)
    (hfirst : a.order (0 : Fin (n + 3)) = R)
    (i : Fin (2 * (s / 2))) :
    ordUnit K ((a.prefixValueUnits (2 * (s / 2)) (by
      rw [D.two_mul_half]
      exact D.le_rank)) i) =
      if Even i.val then R
      else R - 2 * (ramificationIndex K : Int) := by
  let hbound : 2 * (s / 2) ≤ n + 3 := by
    rw [D.two_mul_half]
    exact D.le_rank
  let j : Fin (n + 3) := ⟨i.val, i.isLt.trans_le hbound⟩
  have hjs : j.val < s := by
    have hi := i.isLt
    have hsEq := D.two_mul_half
    simpa only [j] using (show i.val < s by omega)
  by_cases hiEven : Even i.val
  · rw [if_pos hiEven]
    have hjOrder := lemma717_prefixOrder_even a R s D hfirst j hjs (by
      simpa only [j] using hiEven)
    calc
      ordUnit K ((a.prefixValueUnits (2 * (s / 2)) (by
          rw [D.two_mul_half]
          exact D.le_rank)) i) = a.order j := by
            simpa only [prefixValueUnits, GoodBONG.valueUnit,
              GoodBONG.order, j] using
              (a.toBONG.order_eq_ordUnit j).symm
      _ = R := hjOrder
  · rw [if_neg hiEven]
    have hiOdd : Odd i.val := Nat.not_even_iff_odd.mp hiEven
    have hjOrder := lemma717_prefixOrder_odd a R s D hfirst j hjs (by
      simpa only [j] using hiOdd)
    calc
      ordUnit K ((a.prefixValueUnits (2 * (s / 2)) (by
          rw [D.two_mul_half]
          exact D.le_rank)) i) = a.order j := by
            simpa only [prefixValueUnits, GoodBONG.valueUnit,
              GoodBONG.order, j] using
              (a.toBONG.order_eq_ordUnit j).symm
      _ = R - 2 * (ramificationIndex K : Int) := hjOrder

/-- The type-I/III canonical source tower has exactly the source-prefix
orders required by integral normalization. -/
theorem lemma717CanonicalTowerValues_orders_match_source
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData a R s)
    (hfirst : a.order (0 : Fin (n + 3)) = R)
    (i : Fin (2 * (s / 2))) :
    ordUnit K (lemma717CanonicalTowerValues (K := K) R (s / 2) i) =
      ordUnit K ((a.prefixValueUnits (2 * (s / 2)) (by
        rw [D.two_mul_half]
        exact D.le_rank)) i) := by
  rw [ordUnit_lemma717CanonicalTowerValues,
    ordUnit_lemma717_sourcePrefix a R s D hfirst]

/-- The discriminant-twisted type-II canonical source tower also preserves
every stopped-prefix order. -/
theorem lemma717TypeIICanonicalTowerValues_orders_match_source
    [Beli2006AlphaLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData a R s)
    (hfirst : a.order (0 : Fin (n + 3)) = R)
    (i : Fin (2 * (s / 2))) :
    ordUnit K
        (lemma717TypeIICanonicalTowerValues (K := K) R (s / 2)
          D.half_pos i) =
      ordUnit K ((a.prefixValueUnits (2 * (s / 2)) (by
        rw [D.two_mul_half]
        exact D.le_rank)) i) := by
  rw [ordUnit_lemma717TypeIICanonicalTowerValues,
    ordUnit_lemma717_sourcePrefix a R s D hfirst]

/-- The endpoint classes of every adjacent pair in the stopped source prefix
are exactly the two classes allowed by the dyadic binary classification. -/
theorem lemma717_sourcePrefix_pairClasses
    [Beli2006AlphaLaws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData a R s)
    (hfirst : a.order (0 : Fin (n + 3)) = R) :
    AlternatingEndpointPairClasses
      (a.prefixValueUnits (2 * (s / 2)) (by
        rw [D.two_mul_half]
        exact D.le_rank)) := by
  intro t
  let first : Fin (n + 2) := ⟨0, by omega⟩
  have hlast : s - 2 < n + 2 := by
    have hsBound := D.le_rank
    omega
  let last : Fin (n + 2) := ⟨s - 2, hlast⟩
  have hkLast : 2 * t.val ≤ s - 2 := by
    have hsEq := D.two_mul_half
    have ht := t.isLt
    omega
  have hkBound : 2 * t.val < n + 2 := lt_of_le_of_lt hkLast hlast
  let k : Fin (n + 2) := ⟨2 * t.val, hkBound⟩
  have hfirstLe : first ≤ last := by
    change 0 ≤ s - 2
    omega
  have hevenSegment : Even (last.val - first.val) := by
    rcases D.even with ⟨d, hd⟩
    refine ⟨d - 1, ?_⟩
    simp only [last, first, Nat.sub_zero]
    omega
  have hfirstOrder : a.order first.castSucc = R := by
    have hindex : first.castSucc = (0 : Fin (n + 3)) := Fin.ext rfl
    rw [hindex]
    exact hfirst
  have hterminal : a.order last.succ =
      R - 2 * (ramificationIndex K : Int) := by
    have hindex : last.succ = ⟨s - 1, by omega⟩ := by
      apply Fin.ext
      change (s - 2) + 1 = s - 1
      exact succ_sub_two_eq_sub_one D.two_le
    rw [hindex]
    exact D.terminal
  have hik : first ≤ k := Fin.zero_le k
  have hkj : k ≤ last := by
    change 2 * t.val ≤ s - 2
    exact hkLast
  have hkEven : Even (k.val - first.val) := by
    exact ⟨t.val, by simp [k, first]; omega⟩
  have hclasses := a.beli2019Lemma75_pairBlock_endpointClass
    first last k R hfirstLe hevenSegment hfirstOrder hterminal
      hik hkj hkEven
  have hpair := a.toBONG.adjacentSignedProduct_endpoint_cases
    k.castSucc (Nat.succ_lt_succ k.isLt) hclasses
  simpa only [prefixValueUnits, GoodBONG.valueUnit, k,
    Fin.castSucc_mk] using hpair

/-- In the square (type-I) branch, the source prefix and canonical tower have
matching determinant square class. -/
theorem lemma717_typeI_determinants_match
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData a R s)
    (hsquare : IsSquare
      (a.toBONG.signedEvenPrefixProduct (s / 2))) :
    IsSquare
      (diagonalUnitDeterminant
          (a.prefixValueUnits (2 * (s / 2)) (by
            rw [D.two_mul_half]
            exact D.le_rank)) *
        diagonalUnitDeterminant
          (lemma717CanonicalTowerValues (K := K) R (s / 2))) := by
  let sign : Kˣ := (-1 : Kˣ) ^ (s / 2)
  let source := diagonalUnitDeterminant
    (a.prefixValueUnits (2 * (s / 2)) (by
      rw [D.two_mul_half]
      exact D.le_rank))
  let target := diagonalUnitDeterminant
    (lemma717CanonicalTowerValues (K := K) R (s / 2))
  have hsource : IsSquare (sign * source) := by
    simpa only [sign, source, BONG.signedEvenPrefixProduct,
      diagonalUnitDeterminant_prefixValueUnits,
      GoodBONG.prefixProduct] using hsquare
  have htarget : IsSquare (sign * target) := by
    simpa only [sign, target] using
      signedDeterminant_lemma717CanonicalTowerValues_isSquare
        (K := K) R (s / 2)
  exact isSquare_product_of_same_signed sign source target hsource htarget

/-- In the discriminant branch, the two identical `Delta` twists cancel,
again giving the determinant square-class match needed for normalization. -/
theorem lemma717_typeII_determinants_match
    [laws : DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData a R s)
    (htwisted : IsSquare
      (a.toBONG.signedEvenPrefixProduct (s / 2) *
        laws.discriminantUnit)) :
    IsSquare
      (diagonalUnitDeterminant
          (a.prefixValueUnits (2 * (s / 2)) (by
            rw [D.two_mul_half]
            exact D.le_rank)) *
        diagonalUnitDeterminant
          (lemma717TypeIICanonicalTowerValues (K := K) R (s / 2)
            D.half_pos)) := by
  let sign : Kˣ := (-1 : Kˣ) ^ (s / 2)
  let source := diagonalUnitDeterminant
    (a.prefixValueUnits (2 * (s / 2)) (by
      rw [D.two_mul_half]
      exact D.le_rank))
  let target := diagonalUnitDeterminant
    (lemma717TypeIICanonicalTowerValues (K := K) R (s / 2)
      D.half_pos)
  have hsource : IsSquare (sign * source * laws.discriminantUnit) := by
    simpa only [sign, source, BONG.signedEvenPrefixProduct,
      diagonalUnitDeterminant_prefixValueUnits,
      GoodBONG.prefixProduct] using htwisted
  have htarget : IsSquare (sign * target * laws.discriminantUnit) := by
    simpa only [sign, target] using
      signedDeterminant_lemma717TypeIICanonicalTowerValues_twisted_isSquare
        (K := K) R (s / 2) D.half_pos
  exact isSquare_product_of_same_signed_discriminant
    sign source target hsource htarget

/-- The stopped prefix is either the whole lattice or an orthogonal summand.
This is Corollary 4.4(i) at the boundary `s - 1, s`, uniformly for the
endpoint-above and type-III alternatives of Lemma 7.17. -/
theorem lemma717_hasSplitAtStopping
    [BeliCorollary44Laws.{u, v} K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData a R s)
    (hcase : Lemma717EndpointAbove a R s ∨
      Lemma717IsTypeIII a R s) :
    s = n + 3 ∨
      a.toBONG.HasTwoBlockSplit s D.le_rank := by
  rcases hcase with hend | hIII
  · rcases hend with hwhole | ⟨hs, hnext⟩
    · exact Or.inl hwhole
    · right
      let boundary : Fin (n + 3) := ⟨s - 1, by omega⟩
      have hboundaryOrder : a.toBONG.order boundary ≤
          a.toBONG.order ⟨s, hs⟩ := by
        calc
          a.toBONG.order boundary =
              R - 2 * (ramificationIndex K : Int) := D.terminal
          _ ≤ R := by
            have hepos := ramificationIndex_pos (K := K)
            omega
          _ ≤ a.toBONG.order ⟨s, hs⟩ := le_of_lt hnext
      have hnextBound : boundary.val + 1 < n + 3 := by
        simp only [boundary]
        omega
      have hboundaryOrder' : a.toBONG.order boundary ≤
          a.toBONG.order ⟨boundary.val + 1, hnextBound⟩ := by
        calc
          _ ≤ a.toBONG.order ⟨s, hs⟩ := hboundaryOrder
          _ = _ := by
            congr 1
            apply Fin.ext
            change s = (s - 1) + 1
            have hsTwo := D.two_le
            omega
      have hsplit := a.toBONG.beliCorollary44_i_unconditional a.good boundary
        hnextBound hboundaryOrder'
      have hcut : boundary.val + 1 = s := by
        change (s - 1) + 1 = s
        have hsTwo := D.two_le
        omega
      simpa only [hcut] using hsplit
  · rcases hIII with ⟨hs, hnext⟩
    right
    let boundary : Fin (n + 3) := ⟨s - 1, by omega⟩
    have hboundaryOrder : a.toBONG.order boundary ≤
        a.toBONG.order ⟨s, hs⟩ := by
      calc
        a.toBONG.order boundary =
            R - 2 * (ramificationIndex K : Int) := D.terminal
        _ ≤ R := by
          have hepos := ramificationIndex_pos (K := K)
          omega
        _ = a.toBONG.order ⟨s, hs⟩ := hnext.symm
    have hnextBound : boundary.val + 1 < n + 3 := by
      simp only [boundary]
      omega
    have hboundaryOrder' : a.toBONG.order boundary ≤
        a.toBONG.order ⟨boundary.val + 1, hnextBound⟩ := by
      calc
        _ ≤ a.toBONG.order ⟨s, hs⟩ := hboundaryOrder
        _ = _ := by
          congr 1
          apply Fin.ext
          change s = (s - 1) + 1
          have hsTwo := D.two_le
          omega
    have hsplit := a.toBONG.beliCorollary44_i_unconditional a.good boundary
      hnextBound hboundaryOrder'
    have hcut : boundary.val + 1 = s := by
      change (s - 1) + 1 = s
      have hsTwo := D.two_le
      omega
    simpa only [hcut] using hsplit

/-- Type I can be normalized on the same lattice to the exact canonical
source tower, with the entire suffix unchanged. -/
theorem exists_lemma717TypeINormalizedSource
    [Beli2006AlphaLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData a R s)
    (hfirst : a.order (0 : Fin (n + 3)) = R)
    (htype : Lemma717IsTypeI a R s) :
    ∃ c : GoodBONG q L (n + 3),
      (∀ i : Fin (2 * (s / 2)),
        c.valueUnit ⟨i.val, i.isLt.trans_le (by
          rw [D.two_mul_half]
          exact D.le_rank)⟩ =
          lemma717CanonicalTowerValues (K := K) R (s / 2) i) ∧
      (∀ j : Fin (n + 3), 2 * (s / 2) ≤ j.val →
        c.valueUnit j = a.valueUnit j) := by
  rcases htype with ⟨_, hsquare⟩
  let hbound : 2 * (s / 2) ≤ n + 3 := by
    rw [D.two_mul_half]
    exact D.le_rank
  have hsource := lemma717_sourcePrefix_pairClasses a R s D hfirst
  have htarget := lemma717CanonicalTowerValues_pairClasses
    (K := K) R (s / 2)
  have horders := lemma717CanonicalTowerValues_orders_match_source
    a R s D hfirst
  have hdet := lemma717_typeI_determinants_match a R s D hsquare
  exact a.exists_normalizedSplitPrefix hbound
    (lemma717CanonicalTowerValues (K := K) R (s / 2))
    hsource htarget R
    (lemma717CanonicalTowerValues_orderProfile (K := K) R (s / 2))
    horders hdet

/-- Type II can likewise be normalized to the tower whose second coefficient
carries `Delta`, again without changing the suffix. -/
theorem exists_lemma717TypeIINormalizedSource
    [Beli2006AlphaLaws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData a R s)
    (hfirst : a.order (0 : Fin (n + 3)) = R)
    (htype : Lemma717IsTypeII a R s) :
    ∃ c : GoodBONG q L (n + 3),
      (∀ i : Fin (2 * (s / 2)),
        c.valueUnit ⟨i.val, i.isLt.trans_le (by
          rw [D.two_mul_half]
          exact D.le_rank)⟩ =
          lemma717TypeIICanonicalTowerValues (K := K) R (s / 2)
            D.half_pos i) ∧
      (∀ j : Fin (n + 3), 2 * (s / 2) ≤ j.val →
        c.valueUnit j = a.valueUnit j) := by
  rcases htype with ⟨_, htwisted⟩
  let hbound : 2 * (s / 2) ≤ n + 3 := by
    rw [D.two_mul_half]
    exact D.le_rank
  have hsource := lemma717_sourcePrefix_pairClasses a R s D hfirst
  have htarget := lemma717TypeIICanonicalTowerValues_pairClasses
    (K := K) R (s / 2) D.half_pos
  have horders := lemma717TypeIICanonicalTowerValues_orders_match_source
    a R s D hfirst
  have hdet := lemma717_typeII_determinants_match a R s D htwisted
  exact a.exists_normalizedSplitPrefix hbound
    (lemma717TypeIICanonicalTowerValues (K := K) R (s / 2) D.half_pos)
    hsource htarget R
    (lemma717TypeIICanonicalTowerValues_orderProfile
      (K := K) R (s / 2) D.half_pos)
    horders hdet

/-- A type-III source whose stopped signed determinant is already square can
be normalized directly to the canonical tower.  The complete order sequence
is preserved. -/
theorem exists_lemma717TypeIIINormalizedSource_of_square
    [Beli2006AlphaLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData a R s)
    (hfirst : a.order (0 : Fin (n + 3)) = R)
    (htype : Lemma717IsTypeIII a R s)
    (hsquare : IsSquare
      (a.toBONG.signedEvenPrefixProduct (s / 2))) :
    ∃ c : GoodBONG q L (n + 3),
      (∀ i : Fin (2 * (s / 2)),
        c.valueUnit ⟨i.val, i.isLt.trans_le (by
          rw [D.two_mul_half]
          exact D.le_rank)⟩ =
          lemma717CanonicalTowerValues (K := K) R (s / 2) i) ∧
      (∀ j : Fin (n + 3), c.order j = a.order j) := by
  let hbound : 2 * (s / 2) ≤ n + 3 := by
    rw [D.two_mul_half]
    exact D.le_rank
  have hsource := lemma717_sourcePrefix_pairClasses a R s D hfirst
  have htarget := lemma717CanonicalTowerValues_pairClasses
    (K := K) R (s / 2)
  have horders := lemma717CanonicalTowerValues_orders_match_source
    a R s D hfirst
  have hdet := lemma717_typeI_determinants_match a R s D hsquare
  rcases a.exists_normalizedSplitPrefix hbound
      (lemma717CanonicalTowerValues (K := K) R (s / 2))
      hsource htarget R
      (lemma717CanonicalTowerValues_orderProfile (K := K) R (s / 2))
      horders hdet with ⟨c, hprefix, hsuffix⟩
  refine ⟨c, hprefix, ?_⟩
  intro j
  exact normalizedSplitPrefix_order_eq a c hbound
    (lemma717CanonicalTowerValues (K := K) R (s / 2))
    hprefix hsuffix horders j

/-- Full type-III normalization.  If the source lies in the discriminant
class, paragraph 3.12 of Beli (2003) multiplies the boundary pair by `Delta`.
The boundary parameter has order exactly `2e`, so the multiplier belongs to
its norm-generator group.  The resulting source is then normalized by the
preceding square branch. -/
theorem exists_lemma717TypeIIINormalizedSource
    [Beli2006AlphaLaws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [BeliCorollary44Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData a R s)
    (hfirst : a.order (0 : Fin (n + 3)) = R)
    (htype : Lemma717IsTypeIII a R s) :
    ∃ c : GoodBONG q L (n + 3),
      (∀ k : Fin (2 * (s / 2)),
        c.valueUnit ⟨k.val, k.isLt.trans_le (by
          rw [D.two_mul_half]
          exact D.le_rank)⟩ =
          lemma717CanonicalTowerValues (K := K) R (s / 2) k) ∧
      (∀ j : Fin (n + 3), c.order j = a.order j) := by
  have hclasses := lemma717_signedPrefixProduct_cases a R s D hfirst
  rcases hclasses with hsquare | htwisted
  · exact exists_lemma717TypeIIINormalizedSource_of_square
      a R s D hfirst htype hsquare
  · rcases htype with ⟨hs, hnext⟩
    let i : Fin (n + 3) := ⟨s - 1, by omega⟩
    have hi : i.val + 1 < n + 3 := by
      simp only [i]
      have hsTwo := D.two_le
      omega
    let parameter := a.toBONG.adjacentParameter i hi
    have hparameterOrder :
        ordUnit K parameter = 2 * (ramificationIndex K : Int) := by
      have hleft : a.order i =
          R - 2 * (ramificationIndex K : Int) := by
        simpa only [i] using D.terminal
      have hright : a.order ⟨i.val + 1, hi⟩ = R := by
        have hindex : (⟨i.val + 1, hi⟩ : Fin (n + 3)) = ⟨s, hs⟩ := by
          apply Fin.ext
          change (s - 1) + 1 = s
          have hsTwo := D.two_le
          omega
        rw [hindex, hnext]
      rw [show parameter = a.toBONG.adjacentParameter i hi by rfl,
        a.toBONG.ordUnit_adjacentParameter i hi]
      change a.order ⟨i.val + 1, hi⟩ - a.order i = _
      rw [hleft, hright]
      ring
    have hu :=
      discriminantUnitClass_mem_beliNormGeneratorGroup_of_order_eq_twoE
        parameter hparameterOrder
    rcases Bong.BONG.exists_adjacentMultiplierData a i hi
        (discriminantValuationUnit (K := K)) hu with ⟨C⟩
    let D' : Lemma717StoppingData C.bong R s :=
      { even := D.even
        two_le := D.two_le
        le_rank := D.le_rank
        terminal := by
          rw [C.order_eq]
          exact D.terminal
        maximal := by
          intro hsBound
          rw [C.order_eq]
          exact D.maximal hsBound }
    have hfirstC : C.bong.order (0 : Fin (n + 3)) = R := by
      rw [C.order_eq]
      exact hfirst
    have htypeC : Lemma717IsTypeIII C.bong R s := ⟨hs, by
      rw [C.order_eq]
      exact hnext⟩
    have hcut : 2 * (s / 2) = i.val + 1 := by
      rw [D.two_mul_half]
      simp only [i]
      have hsTwo := D.two_le
      omega
    have hchanged := C.signedEvenPrefixProduct_leftBoundary (s / 2) hcut
    have hchanged' :
        C.bong.toBONG.signedEvenPrefixProduct (s / 2) =
          laws.discriminantUnit *
            a.toBONG.signedEvenPrefixProduct (s / 2) := by
      simpa only [discriminantValuationUnit] using hchanged
    have hsquareC : IsSquare
        (C.bong.toBONG.signedEvenPrefixProduct (s / 2)) := by
      rw [hchanged', mul_comm]
      exact htwisted
    rcases exists_lemma717TypeIIINormalizedSource_of_square
        C.bong R s D' hfirstC htypeC hsquareC with
      ⟨c, hprefix, horder⟩
    refine ⟨c, ?_, ?_⟩
    · intro k
      simpa only [] using hprefix k
    · intro j
      exact (horder j).trans (C.order_eq j)

end BONG.GoodBONG

end Bong
