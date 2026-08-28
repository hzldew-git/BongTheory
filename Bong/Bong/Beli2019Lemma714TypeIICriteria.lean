/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714TypeIICoefficients

/-!
# Beli (2019), Lemma 7.14(ii): global numerical BONG criteria

This file checks the two numerical conditions of Beli (2006), Definition
2.2, for the complete type-II replacement list: every adjacent parameter is
admissible and the order sequence is weakly increasing at distance two.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The left external pair written directly in the complete target list. -/
theorem lemma714TypeIITargetValues_leftBoundaryAdmissible
    [laws : DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s) (hsFour : 4 ≤ s)
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hsCurrent : s < n + 3)
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (ε η : Kˣ) (hεUnit : IsValuationUnit K (ε : K)) :
    IsBinaryParameterAdmissible
      (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η
          ⟨s - 2, by omega⟩ /
        lemma714TypeIITargetValues b s D.two_le hsCurrent ε η
          ⟨s - 3, by omega⟩) := by
  have hprefix : (⟨s - 3, by omega⟩ : Fin (n + 3)).val < s - 2 := by
    change s - 3 < s - 2
    omega
  rw [lemma714TypeIITargetValues_zero,
    lemma714TypeIITargetValues_prefix b s D.two_le hsCurrent ε η
      ⟨s - 3, by omega⟩ hprefix]
  have hprevious : (⟨s - 3 + 2, by omega⟩ : Fin (n + 3)) =
      ⟨s - 1, by omega⟩ := by
    apply Fin.ext
    change s - 3 + 2 = s - 1
    omega
  rw [hprevious]
  exact b.lemma714_typeII_leftBoundaryAdmissible R s D hsFour
    hthird hsCurrent hcurrent ε η hεUnit

/-- The first internal pair of the inserted ternary block. -/
theorem lemma714TypeIITargetValues_firstInternalAdmissible
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K]
    (b : GoodBONG q L (n + 3)) (s : Nat)
    (hsTwo : 2 ≤ s) (hsCurrent : s < n + 3)
    (ε η : Kˣ) (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    IsBinaryParameterAdmissible
      (lemma714TypeIITargetValues b s hsTwo hsCurrent ε η
          ⟨s - 1, by omega⟩ /
        lemma714TypeIITargetValues b s hsTwo hsCurrent ε η
          ⟨s - 2, by omega⟩) := by
  rw [lemma714TypeIITargetValues_one,
    lemma714TypeIITargetValues_zero]
  exact lemma712TargetValues_firstBinaryAdmissible
    (b.valueUnit ⟨s, hsCurrent⟩) ε η hεUnit hηUnit hηDefect

/-- The second internal pair of the inserted ternary block. -/
theorem lemma714TypeIITargetValues_secondInternalAdmissible
    [laws : DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (s : Nat)
    (hsTwo : 2 ≤ s) (hsCurrent : s < n + 3)
    (ε η : Kˣ) (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K)) :
    IsBinaryParameterAdmissible
      (lemma714TypeIITargetValues b s hsTwo hsCurrent ε η
          ⟨s, hsCurrent⟩ /
        lemma714TypeIITargetValues b s hsTwo hsCurrent ε η
          ⟨s - 1, by omega⟩) := by
  rw [lemma714TypeIITargetValues_two,
    lemma714TypeIITargetValues_one]
  exact lemma712TargetValues_secondBinaryAdmissible
    (b.valueUnit ⟨s, hsCurrent⟩) ε η hεUnit hηUnit

/-- The right external pair written directly in the complete target list. -/
theorem lemma714TypeIITargetValues_rightBoundaryAdmissible
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hsCurrent : s < n + 3)
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (hsSuffix : s + 2 ≤ n + 3)
    (ε η : Kˣ) (hηUnit : IsValuationUnit K (η : K))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    IsBinaryParameterAdmissible
      (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η
          ⟨s + 1, by omega⟩ /
        lemma714TypeIITargetValues b s D.two_le hsCurrent ε η
          ⟨s, hsCurrent⟩) := by
  have hslt : s < (⟨s + 1, by omega⟩ : Fin (n + 3)).val := by
    change s < s + 1
    omega
  rw [lemma714TypeIITargetValues_suffix b s D.two_le hsCurrent ε η
      ⟨s + 1, by omega⟩ hslt,
    lemma714TypeIITargetValues_two]
  exact b.lemma714_typeII_rightBoundaryAdmissible R s D hsCurrent
    hcurrent hsSuffix ε η hηUnit hηDefect

/-- Every adjacent parameter of the complete type-II coefficient list is
admissible. -/
theorem lemma714TypeIITargetValues_adjacentAdmissible
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hsCurrent : s < n + 3)
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (ε η : Kˣ) (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    ∀ (i : Fin (n + 3)) (hi : i.val + 1 < n + 3),
      IsBinaryParameterAdmissible
        (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η
            ⟨i.val + 1, hi⟩ /
          lemma714TypeIITargetValues b s D.two_le hsCurrent ε η i) := by
  intro i hi
  by_cases hprefix : i.val + 1 < s - 2
  · rw [lemma714TypeIITargetValues_prefix,
      lemma714TypeIITargetValues_prefix]
    · let j : Fin (n + 3) := ⟨i.val + 2, by omega⟩
      have hj : j.val + 1 < n + 3 := by
        dsimp only [j]
        omega
      have hadmissible :=
        b.toBONG.adjacentParameter_isBinaryParameterAdmissible j hj
      unfold BONG.adjacentParameter at hadmissible
      convert hadmissible using 1 <;> congr 1
    · omega
    · omega
  by_cases hleft : i.val + 1 = s - 2
  · have hsFour : 4 ≤ s := by
      rcases D.even with ⟨d, hd⟩
      omega
    have hiLeft : i = (⟨s - 3, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      change i.val = s - 3
      omega
    have hiRight : (⟨i.val + 1, hi⟩ : Fin (n + 3)) =
        ⟨s - 2, by omega⟩ := by
      apply Fin.ext
      change i.val + 1 = s - 2
      omega
    have hresult :=
      b.lemma714TypeIITargetValues_leftBoundaryAdmissible R s D
        hsFour hthird hsCurrent hcurrent ε η hεUnit
    have hleftValue := congrArg
      (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η) hiLeft
    have hrightValue := congrArg
      (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η) hiRight
    rw [hleftValue, hrightValue]
    exact hresult
  by_cases hfirst : i.val + 2 = s
  · have hiLeft : i = (⟨s - 2, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      change i.val = s - 2
      omega
    have hiRight : (⟨i.val + 1, hi⟩ : Fin (n + 3)) =
        ⟨s - 1, by omega⟩ := by
      apply Fin.ext
      change i.val + 1 = s - 1
      omega
    have hresult := b.lemma714TypeIITargetValues_firstInternalAdmissible s
      D.two_le hsCurrent ε η hεUnit hηUnit hηDefect
    have hleftValue := congrArg
      (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η) hiLeft
    have hrightValue := congrArg
      (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η) hiRight
    rw [hleftValue, hrightValue]
    exact hresult
  by_cases hsecond : i.val + 1 = s
  · have hiLeft : i = (⟨s - 1, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      change i.val = s - 1
      omega
    have hiRight : (⟨i.val + 1, hi⟩ : Fin (n + 3)) =
        ⟨s, hsCurrent⟩ := by
      apply Fin.ext
      change i.val + 1 = s
      omega
    have hresult := b.lemma714TypeIITargetValues_secondInternalAdmissible s
      D.two_le hsCurrent ε η hεUnit hηUnit
    have hleftValue := congrArg
      (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η) hiLeft
    have hrightValue := congrArg
      (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η) hiRight
    rw [hleftValue, hrightValue]
    exact hresult
  by_cases hright : i.val = s
  · have hsSuffix : s + 2 ≤ n + 3 := by omega
    have hiLeft : i = (⟨s, hsCurrent⟩ : Fin (n + 3)) := by
      apply Fin.ext
      exact hright
    have hiRight : (⟨i.val + 1, hi⟩ : Fin (n + 3)) =
        ⟨s + 1, by omega⟩ := by
      apply Fin.ext
      change i.val + 1 = s + 1
      omega
    have hresult :=
      b.lemma714TypeIITargetValues_rightBoundaryAdmissible R s D
        hsCurrent hcurrent hsSuffix ε η hηUnit hηDefect
    simpa only [hiLeft, hiRight] using hresult
  · have hslt : s < i.val := by omega
    have hnextlt : s < (⟨i.val + 1, hi⟩ : Fin (n + 3)).val := by
      change s < i.val + 1
      omega
    rw [lemma714TypeIITargetValues_suffix b s D.two_le hsCurrent ε η
        ⟨i.val + 1, hi⟩ hnextlt,
      lemma714TypeIITargetValues_suffix b s D.two_le hsCurrent ε η i hslt]
    change IsBinaryParameterAdmissible
      (b.toBONG.valueUnit ⟨i.val + 1, hi⟩ /
        b.toBONG.valueUnit i)
    exact b.toBONG.adjacentParameter_isBinaryParameterAdmissible i hi

/-- The complete target order sequence is weakly increasing at distance
two.  The six cases around the inserted block are precisely the order
comparisons displayed in the proof of Lemma 7.14(ii). -/
theorem lemma714TypeIITargetValues_weakTwoStep
    [laws : DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hsCurrent : s < n + 3)
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (ε η : Kˣ) (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K)) :
    ∀ (i : Fin (n + 3)) (hi : i.val + 2 < n + 3),
      ordUnit K
          (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η i) ≤
        ordUnit K
          (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η
            ⟨i.val + 2, hi⟩) := by
  intro i hi
  let next : Fin (n + 3) := ⟨i.val + 2, hi⟩
  by_cases hprefix : next.val < s - 2
  · have hleftPrefix : i.val < s - 2 := by
      dsimp only [next] at hprefix
      omega
    rw [ordUnit_lemma714TypeIITargetValues_prefix b s D.two_le
        hsCurrent ε η i hleftPrefix,
      ordUnit_lemma714TypeIITargetValues_prefix b s D.two_le
        hsCurrent ε η next hprefix]
    let j : Fin (n + 3) := ⟨i.val + 2, by
      dsimp only [next] at hprefix
      omega⟩
    have hj : j.val + 2 < n + 3 := by
      dsimp only [j, next] at hprefix ⊢
      omega
    have hgood := b.good j hj
    convert hgood using 1 <;> congr 1
  by_cases hminusFour : i.val + 4 = s
  · have hsFour : 4 ≤ s := by omega
    have P := b.beli2019Lemma714_i R s D.toLemma714MinimalityData
      hsFour hthird
    have heven : Even (s - 2) := by
      rcases D.even with ⟨d, hd⟩
      exact ⟨d - 1, by omega⟩
    have hplateau := P.high_positions (s - 2) (by omega) le_rfl heven
    have hiLeft : i = (⟨s - 4, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      change i.val = s - 4
      omega
    have hiRight : next = (⟨s - 2, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      dsimp only [next]
      change i.val + 2 = s - 2
      omega
    have hleftValue := congrArg
      (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η) hiLeft
    have hrightValue := congrArg
      (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η) hiRight
    have hleftPrefix :
        (⟨s - 4, by omega⟩ : Fin (n + 3)).val < s - 2 := by
      change s - 4 < s - 2
      omega
    rw [hleftValue, hrightValue,
      ordUnit_lemma714TypeIITargetValues_prefix b s D.two_le
        hsCurrent ε η ⟨s - 4, by omega⟩ hleftPrefix,
      ordUnit_lemma714TypeIITargetValues_zero b R s D.two_le
        hsCurrent hcurrent ε η hεUnit hηUnit]
    have hindex : (⟨s - 4 + 2, by omega⟩ : Fin (n + 3)) =
        ⟨s - 2, by omega⟩ := by
      apply Fin.ext
      change s - 4 + 2 = s - 2
      omega
    rw [hindex, hplateau]
  by_cases hminusThree : i.val + 3 = s
  · have hsFour : 4 ≤ s := by
      rcases D.even with ⟨d, hd⟩
      omega
    have P := b.beli2019Lemma714_i R s D.toLemma714MinimalityData
      hsFour hthird
    have hodd : Odd (s - 1) := by
      rcases D.even with ⟨d, hd⟩
      exact ⟨d - 1, by omega⟩
    have hplateau := P.low_positions (s - 1) (by omega) le_rfl hodd
    have hiLeft : i = (⟨s - 3, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      change i.val = s - 3
      omega
    have hiRight : next = (⟨s - 1, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      dsimp only [next]
      change i.val + 2 = s - 1
      omega
    have hleftValue := congrArg
      (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η) hiLeft
    have hrightValue := congrArg
      (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η) hiRight
    have hleftPrefix :
        (⟨s - 3, by omega⟩ : Fin (n + 3)).val < s - 2 := by
      change s - 3 < s - 2
      omega
    rw [hleftValue, hrightValue,
      ordUnit_lemma714TypeIITargetValues_prefix b s D.two_le
        hsCurrent ε η ⟨s - 3, by omega⟩ hleftPrefix,
      ordUnit_lemma714TypeIITargetValues_one b R s D.two_le
        hsCurrent hcurrent ε η hεUnit hηUnit]
    have hindex : (⟨s - 3 + 2, by omega⟩ : Fin (n + 3)) =
        ⟨s - 1, by omega⟩ := by
      apply Fin.ext
      change s - 3 + 2 = s - 1
      omega
    rw [hindex, hplateau]
    omega
  by_cases hminusTwo : i.val + 2 = s
  · have hiLeft : i = (⟨s - 2, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      change i.val = s - 2
      omega
    have hiRight : next = (⟨s, hsCurrent⟩ : Fin (n + 3)) := by
      apply Fin.ext
      dsimp only [next]
      exact hminusTwo
    have hleftValue := congrArg
      (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η) hiLeft
    have hrightValue := congrArg
      (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η) hiRight
    rw [hleftValue, hrightValue,
      ordUnit_lemma714TypeIITargetValues_zero b R s D.two_le
        hsCurrent hcurrent ε η hεUnit hηUnit,
      ordUnit_lemma714TypeIITargetValues_two b R s D.two_le
        hsCurrent hcurrent ε η hεUnit hηUnit]
  by_cases hminusOne : i.val + 1 = s
  · have hsSuffix : s + 2 ≤ n + 3 := by omega
    have hstop := b.lemma714_typeII_stopOrder_ge R s D
      ⟨hsCurrent, hcurrent⟩ hsSuffix
    have hiLeft : i = (⟨s - 1, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      change i.val = s - 1
      omega
    have hiRight : next = (⟨s + 1, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      dsimp only [next]
      change i.val + 2 = s + 1
      omega
    have hleftValue := congrArg
      (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η) hiLeft
    have hrightValue := congrArg
      (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η) hiRight
    have hslt : s < (⟨s + 1, by omega⟩ : Fin (n + 3)).val := by
      change s < s + 1
      omega
    rw [hleftValue, hrightValue,
      ordUnit_lemma714TypeIITargetValues_one b R s D.two_le
        hsCurrent hcurrent ε η hεUnit hηUnit,
      ordUnit_lemma714TypeIITargetValues_suffix b s D.two_le
        hsCurrent ε η ⟨s + 1, by omega⟩ hslt]
    exact hstop
  by_cases hcenter : i.val = s
  · have hiRightBound : s + 2 < n + 3 := by omega
    have hiLeft : i = (⟨s, hsCurrent⟩ : Fin (n + 3)) := by
      apply Fin.ext
      exact hcenter
    have hiRight : next = (⟨s + 2, hiRightBound⟩ : Fin (n + 3)) := by
      apply Fin.ext
      dsimp only [next]
      omega
    have hleftValue := congrArg
      (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η) hiLeft
    have hrightValue := congrArg
      (lemma714TypeIITargetValues b s D.two_le hsCurrent ε η) hiRight
    have hslt : s < (⟨s + 2, hiRightBound⟩ : Fin (n + 3)).val := by
      change s < s + 2
      omega
    rw [hleftValue, hrightValue,
      ordUnit_lemma714TypeIITargetValues_two b R s D.two_le
        hsCurrent hcurrent ε η hεUnit hηUnit,
      ordUnit_lemma714TypeIITargetValues_suffix b s D.two_le
        hsCurrent ε η ⟨s + 2, hiRightBound⟩ hslt]
    calc
      R + 1 = b.order ⟨s, hsCurrent⟩ := hcurrent.symm
      _ ≤ b.order ⟨s + 2, hiRightBound⟩ :=
        b.good ⟨s, hsCurrent⟩ hiRightBound
  · have hslt : s < i.val := by
      dsimp only [next] at hprefix
      omega
    have hnextlt : s < next.val := by
      dsimp only [next]
      omega
    rw [ordUnit_lemma714TypeIITargetValues_suffix b s D.two_le
        hsCurrent ε η i hslt,
      ordUnit_lemma714TypeIITargetValues_suffix b s D.two_le
        hsCurrent ε η next hnextlt]
    have hgood := b.good i hi
    exact hgood

end BONG.GoodBONG

end Bong
