/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalHyperbolicBlocks
import Bong.Bong.Beli2019Lemma718Values

/-!
# Beli (2019), Lemma 7.18: normal forms and even prefixes

This file records the displayed standard BONGs in parts (i)--(iii) of
Lemma 7.18.  It then proves the local even-prefix isometry used in Lemma
7.19.  Type I consists entirely of canonical hyperbolic binary blocks.  In
type II the initial discriminant block is unchanged, while every subsequent
binary block is hyperbolic before and after the replacement.  Type III has
the same source blocks as type I; Corollary 7.13 realizes the target by
multiplying precisely the low entries by the square `π²`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The high coefficient `π^R` in the canonical hyperbolic pair. -/
noncomputable def lemma718CanonicalHigh (R : Int) : Kˣ :=
  uniformizerPowerUnit K R

/-- The low coefficient `-π^(R-2e)` in the canonical hyperbolic pair. -/
noncomputable def lemma718CanonicalLow (R : Int) : Kˣ :=
  -(uniformizerPowerUnit K
    (R - 2 * (ramificationIndex K : Int)))

/-- The signed ratio of the canonical pair is the even uniformizer power
`π^(2e)`. -/
theorem lemma718CanonicalPair_signedRatio_eq (R : Int) :
    -(lemma718CanonicalHigh (K := K) R /
      lemma718CanonicalLow (K := K) R) =
      uniformizerPowerUnit K (2 * (ramificationIndex K : Int)) := by
  unfold lemma718CanonicalHigh lemma718CanonicalLow
  calc
    -(uniformizerPowerUnit K R /
        (-(uniformizerPowerUnit K
          (R - 2 * (ramificationIndex K : Int))))) =
        uniformizerPowerUnit K R /
          uniformizerPowerUnit K
            (R - 2 * (ramificationIndex K : Int)) := by
      apply Units.ext
      simp only [Units.val_neg, Units.val_div_eq_div_val]
      rw [← neg_div, neg_div_neg_eq]
    _ = uniformizerPowerUnit K (2 * (ramificationIndex K : Int)) := by
      unfold uniformizerPowerUnit
      rw [div_eq_mul_inv, ← zpow_neg, ← zpow_add]
      congr 1
      omega

/-- The canonical pair is hyperbolic. -/
theorem lemma718CanonicalPair_signedRatio_isSquare (R : Int) :
    IsSquare (-(lemma718CanonicalHigh (K := K) R /
      lemma718CanonicalLow (K := K) R)) := by
  rw [lemma718CanonicalPair_signedRatio_eq]
  refine ⟨uniformizerPowerUnit K (ramificationIndex K : Int), ?_⟩
  unfold uniformizerPowerUnit
  rw [← zpow_add]
  congr 1
  ring

/-- The explicit type-I normal form in Lemma 7.18(i). -/
structure Lemma718TypeINormalForm
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) : Prop where
  stopping : Lemma717StoppingData a R s
  typeI : Lemma717IsTypeI a R s
  sourcePair (j : Nat) (hj : 2 * j + 1 < s) :
    a.valueUnit ⟨2 * j, by
      have hs := stopping.le_rank
      omega⟩ = lemma718CanonicalHigh (K := K) R ∧
    a.valueUnit ⟨2 * j + 1, by
      have hs := stopping.le_rank
      omega⟩ = lemma718CanonicalLow (K := K) R
  targetValues : ∀ i,
    b.valueUnit i = lemma718TypeITargetValues a s i

/-- The explicit type-II normal form in Lemma 7.18(ii). -/
structure Lemma718TypeIINormalForm
    [laws : DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) : Prop where
  stopping : Lemma717StoppingData a R s
  typeII : Lemma717IsTypeII a R s
  initialFirst : a.valueUnit ⟨0, by omega⟩ =
    lemma718CanonicalHigh (K := K) R
  initialSecond : a.valueUnit ⟨1, by omega⟩ =
    -(laws.discriminantUnit *
      uniformizerPowerUnit K
        (R - 2 * (ramificationIndex K : Int)))
  sourcePair (j : Nat) (hjOne : 1 ≤ j) (hj : 2 * j + 1 < s) :
    a.valueUnit ⟨2 * j, by
      have hs := stopping.le_rank
      omega⟩ = lemma718CanonicalHigh (K := K) R ∧
    a.valueUnit ⟨2 * j + 1, by
      have hs := stopping.le_rank
      omega⟩ = lemma718CanonicalLow (K := K) R
  targetValues : ∀ i,
    b.valueUnit i = lemma718TypeIITargetValues a s i

/-- The explicit type-III normal form in Lemma 7.18(iii).  The source
prefix is a sum of canonical hyperbolic blocks, and the target coefficient
family is the one produced by Corollary 7.13. -/
structure Lemma718TypeIIINormalForm
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) : Prop where
  stopping : Lemma717StoppingData a R s
  typeIII : Lemma717IsTypeIII a R s
  sourcePair (j : Nat) (hj : 2 * j + 1 < s) :
    a.valueUnit ⟨2 * j, by
      have hs := stopping.le_rank
      omega⟩ = lemma718CanonicalHigh (K := K) R ∧
    a.valueUnit ⟨2 * j + 1, by
      have hs := stopping.le_rank
      omega⟩ = lemma718CanonicalLow (K := K) R
  targetValues : ∀ i,
    b.valueUnit i = lemma718TypeIIITargetValues a s i

/-- Every even prefix inside the type-I modified block is isometric to its
source prefix. -/
theorem Lemma718TypeINormalForm.evenPrefix
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s)
    (k : Nat) (heven : Even k) (hks : k ≤ s)
    (hk : k ≤ n + 3) :
    (a.prefixDiagonalSpace k hk).IsIsometric
      (b.prefixDiagonalSpace k hk) := by
  generalize hmdef : Classical.choose heven = m
  have hm : k = m + m := by
    have h := Classical.choose_spec heven
    rw [hmdef] at h
    exact h
  clear hmdef heven
  have hkEq : k = 2 * m := by omega
  clear hm
  subst k
  have hk' : 2 * m ≤ n + 3 := by omega
  have hsource : ∀ j : Fin m,
      IsSquare (-(a.valueUnit ⟨2 * j.val, by omega⟩ /
        a.valueUnit ⟨2 * j.val + 1, by omega⟩)) := by
    intro j
    have hj : 2 * j.val + 1 < s := by omega
    rw [(D.sourcePair j.val hj).1, (D.sourcePair j.val hj).2]
    exact lemma718CanonicalPair_signedRatio_isSquare R
  have htarget : ∀ j : Fin m,
      IsSquare (-(b.valueUnit ⟨2 * j.val, by omega⟩ /
        b.valueUnit ⟨2 * j.val + 1, by omega⟩)) := by
    intro j
    have hj : 2 * j.val + 1 < s := by omega
    have hevenIndex : 2 * j.val < s := by omega
    rw [D.targetValues, D.targetValues,
      lemma718TypeITargetValues_prefix a s _ hevenIndex,
      lemma718TypeITargetValues_prefix a s _ hj]
    have hratio :
        -((uniformizerUnit K * a.valueUnit
              ⟨2 * j.val, by omega⟩) /
            (uniformizerUnit K * a.valueUnit
              ⟨2 * j.val + 1, by omega⟩)) =
          -(a.valueUnit ⟨2 * j.val, by omega⟩ /
            a.valueUnit ⟨2 * j.val + 1, by omega⟩) := by
      rw [mul_div_mul_left_eq_div]
    rw [hratio, (D.sourcePair j.val hj).1,
      (D.sourcePair j.val hj).2]
    exact lemma718CanonicalPair_signedRatio_isSquare R
  exact prefixDiagonalSpace_isIsometric_of_two_mul_pair_signedRatioSquares
    a b m hk' hsource htarget

/-- Every even prefix inside the type-II modified block is isometric to its
source prefix.  The first pair is literally unchanged; all remaining pairs
are canonical hyperbolic blocks. -/
theorem Lemma718TypeIINormalForm.evenPrefix
    [laws : DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s)
    (k : Nat) (heven : Even k) (hks : k ≤ s)
    (hk : k ≤ n + 3) :
    (a.prefixDiagonalSpace k hk).IsIsometric
      (b.prefixDiagonalSpace k hk) := by
  generalize hmdef : Classical.choose heven = m
  have hm : k = m + m := by
    have h := Classical.choose_spec heven
    rw [hmdef] at h
    exact h
  clear hmdef heven
  have hkEq : k = 2 * m := by omega
  clear hm
  subst k
  have hk' : 2 * m ≤ n + 3 := by omega
  have hpair : ∀ j : Fin m, DiagonalRepresents
      ![(a.valueUnit ⟨2 * j.val, by omega⟩ : K),
        (a.valueUnit ⟨2 * j.val + 1, by omega⟩ : K)]
      ![(b.valueUnit ⟨2 * j.val, by omega⟩ : K),
        (b.valueUnit ⟨2 * j.val + 1, by omega⟩ : K)] := by
    intro j
    by_cases hjzero : j.val = 0
    · have hevenIndex : 2 * j.val < 2 := by omega
      have hoddIndex : 2 * j.val + 1 < 2 := by omega
      have hbEven := D.targetValues ⟨2 * j.val, by omega⟩
      have hbOdd := D.targetValues ⟨2 * j.val + 1, by omega⟩
      rw [lemma718TypeIITargetValues_initial a s _ hevenIndex] at hbEven
      rw [lemma718TypeIITargetValues_initial a s _ hoddIndex] at hbOdd
      have hcoeff :
          ![(b.valueUnit ⟨2 * j.val, by omega⟩ : K),
            (b.valueUnit ⟨2 * j.val + 1, by omega⟩ : K)] =
          ![(a.valueUnit ⟨2 * j.val, by omega⟩ : K),
            (a.valueUnit ⟨2 * j.val + 1, by omega⟩ : K)] := by
        funext i
        fin_cases i
        · exact congrArg Units.val hbEven
        · exact congrArg Units.val hbOdd
      rw [hcoeff]
      exact diagonalRepresents_refl _
    · have hjOne : 1 ≤ j.val := by omega
      have hj : 2 * j.val + 1 < s := by omega
      have hevenIndex : 2 * j.val < s := by omega
      have htwo : 2 ≤ 2 * j.val := by omega
      have htwoOdd : 2 ≤ 2 * j.val + 1 := by omega
      apply QuadraticSpace.finiteDiagonal_fin_two_diagonalRepresents_of_signedRatioSquares
      · rw [(D.sourcePair j.val hjOne hj).1,
          (D.sourcePair j.val hjOne hj).2]
        exact lemma718CanonicalPair_signedRatio_isSquare R
      · rw [D.targetValues, D.targetValues,
          lemma718TypeIITargetValues_changed a s _ htwo hevenIndex,
          lemma718TypeIITargetValues_changed a s _ htwoOdd hj]
        have hratio :
            -((uniformizerUnit K * a.valueUnit
                  ⟨2 * j.val, by omega⟩) /
                (uniformizerUnit K * a.valueUnit
                  ⟨2 * j.val + 1, by omega⟩)) =
              -(a.valueUnit ⟨2 * j.val, by omega⟩ /
                a.valueUnit ⟨2 * j.val + 1, by omega⟩) := by
          rw [mul_div_mul_left_eq_div]
        rw [hratio, (D.sourcePair j.val hjOne hj).1,
          (D.sourcePair j.val hjOne hj).2]
        exact lemma718CanonicalPair_signedRatio_isSquare R
  exact prefixDiagonalSpace_isIsometric_of_two_mul_pairRepresentations
    a b m hk' hpair

end BONG.GoodBONG

end Bong
