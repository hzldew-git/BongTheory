/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.JordanScaleTruncation

/-!
# Invariants of Jordan decompositions

The volume of the intrinsic truncations `L^r` recovers, by a discrete second
difference, the total rank at every modular scale.  Since strict Jordan
decompositions have at most one component at a given scale, their scale
orders and component ranks are canonically matched.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice.JordanDecomposition

/-- The ranks of the orthogonal Jordan components add up to the rank of the
ambient quadratic space. -/
theorem sum_componentRank_eq_finrank {t : Nat}
    (J : JordanDecomposition q L t) :
    (∑ i, J.componentRank i) = finrank K V := by
  classical
  letI (i : Fin t) : Fintype (J.component i).lattice.BasisIndex :=
    Fintype.ofFinite _
  rw [Module.finrank_eq_card_basis
      J.toOrthogonalDecomposition.componentAmbientBasis,
    Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  change finrank K (J.component i).carrier =
    Fintype.card (J.component i).lattice.BasisIndex
  exact Module.finrank_eq_card_basis (J.component i).lattice.ambientBasis

/-- The weighted positive scale difference appearing in the volume of
`L^r`. -/
noncomputable def scalePositiveRankSum {t : Nat}
    (J : JordanDecomposition q L t) (r : Int) : Int :=
  ∑ i, (J.componentRank i : Int) *
    max 0 (r - ordUnit K (J.scaleGenerator i))

/-- The total Jordan rank having a specified scale order. -/
noncomputable def scaleRankMultiplicity {t : Nat}
    (J : JordanDecomposition q L t) (r : Int) : Int :=
  ∑ i, (J.componentRank i : Int) *
    if ordUnit K (J.scaleGenerator i) = r then 1 else 0

/-- The positive-rank sum is intrinsic because it is half of the volume
jump from `L` to `L^r`. -/
theorem scalePositiveRankSum_eq {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition q L s)
    (r : Int) :
    J.scalePositiveRankSum r = H.scalePositiveRankSum r := by
  have hJ := J.volumeOrder_scaleTruncation r
  have hH := H.volumeOrder_scaleTruncation r
  change volumeOrder q (scaleTruncation q L r) =
      volumeOrder q L + 2 * J.scalePositiveRankSum r at hJ
  change volumeOrder q (scaleTruncation q L r) =
      volumeOrder q L + 2 * H.scalePositiveRankSum r at hH
  omega

private theorem positivePart_secondDifference (r a : Int) :
    max 0 (r + 1 - a) - 2 * max 0 (r - a) +
        max 0 (r - 1 - a) =
      if a = r then 1 else 0 := by
  by_cases heq : a = r
  · subst a
    simp
  · by_cases hlt : a < r
    · have hm : 0 ≤ r - 1 - a := by omega
      have h0 : 0 ≤ r - a := by omega
      have hp : 0 ≤ r + 1 - a := by omega
      rw [if_neg heq, max_eq_right hp, max_eq_right h0,
        max_eq_right hm]
      omega
    · have hgt : r < a := by omega
      have hp : r + 1 - a ≤ 0 := by omega
      have h0 : r - a ≤ 0 := by omega
      have hm : r - 1 - a ≤ 0 := by omega
      rw [if_neg heq, max_eq_left hp, max_eq_left h0,
        max_eq_left hm]
      omega

/-- The rank multiplicity at `r` is the discrete second difference of the
intrinsic positive-rank sum. -/
theorem scaleRankMultiplicity_eq_secondDifference {t : Nat}
    (J : JordanDecomposition q L t) (r : Int) :
    J.scaleRankMultiplicity r =
      J.scalePositiveRankSum (r + 1) -
        2 * J.scalePositiveRankSum r +
          J.scalePositiveRankSum (r - 1) := by
  classical
  unfold scaleRankMultiplicity scalePositiveRankSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (J.componentRank i : Int) *
          (if ordUnit K (J.scaleGenerator i) = r then 1 else 0) =
        (J.componentRank i : Int) *
          (max 0 (r + 1 - ordUnit K (J.scaleGenerator i)) -
            2 * max 0 (r - ordUnit K (J.scaleGenerator i)) +
              max 0 (r - 1 - ordUnit K (J.scaleGenerator i))) := by
      rw [positivePart_secondDifference]
    _ = (J.componentRank i : Int) *
            max 0 (r + 1 - ordUnit K (J.scaleGenerator i)) -
          2 * ((J.componentRank i : Int) *
            max 0 (r - ordUnit K (J.scaleGenerator i))) +
          (J.componentRank i : Int) *
            max 0 (r - 1 - ordUnit K (J.scaleGenerator i)) := by
      ring

/-- Total ranks at every scale agree between arbitrary Jordan
decompositions of the same lattice. -/
theorem scaleRankMultiplicity_eq {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition q L s)
    (r : Int) :
    J.scaleRankMultiplicity r = H.scaleRankMultiplicity r := by
  rw [J.scaleRankMultiplicity_eq_secondDifference,
    H.scaleRankMultiplicity_eq_secondDifference,
    J.scalePositiveRankSum_eq H (r + 1),
    J.scalePositiveRankSum_eq H r,
    J.scalePositiveRankSum_eq H (r - 1)]

/-- At the scale of one component, strictness makes the scale-rank
multiplicity equal exactly that component's rank. -/
theorem scaleRankMultiplicity_at_scale {t : Nat}
    (J : JordanDecomposition q L t) (i : Fin t) :
    J.scaleRankMultiplicity (ordUnit K (J.scaleGenerator i)) =
      J.componentRank i := by
  classical
  unfold scaleRankMultiplicity
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hne : ordUnit K (J.scaleGenerator j) ≠
        ordUnit K (J.scaleGenerator i) := by
      intro heq
      have hstrict : StrictMono
          (fun k : Fin t ↦ ordUnit K (J.scaleGenerator k)) :=
        fun _ _ h ↦ J.scaleOrder_strict h
      exact hji (hstrict.injective heq)
    simp [hne]
  · simp

/-- Every component scale in one Jordan decomposition occurs in every
other Jordan decomposition of the same lattice. -/
theorem exists_scaleOrder_eq {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition q L s)
    (i : Fin t) :
    ∃ j : Fin s,
      ordUnit K (H.scaleGenerator j) =
        ordUnit K (J.scaleGenerator i) := by
  by_contra hexists
  push_neg at hexists
  have hzero :
      H.scaleRankMultiplicity (ordUnit K (J.scaleGenerator i)) = 0 := by
    classical
    unfold scaleRankMultiplicity
    apply Finset.sum_eq_zero
    intro j hj
    simp [hexists j]
  have hinvariant :=
    J.scaleRankMultiplicity_eq H (ordUnit K (J.scaleGenerator i))
  rw [J.scaleRankMultiplicity_at_scale i, hzero] at hinvariant
  have hpos := J.component_finrank_pos i
  change (J.componentRank i : Int) = 0 at hinvariant
  have hne : (J.componentRank i : Int) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  exact hne hinvariant

/-- The canonical matching of two strict Jordan component families by scale
order. -/
noncomputable def scaleIndexEquiv {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition q L s) :
    Fin t ≃ Fin s where
  toFun i := Classical.choose (J.exists_scaleOrder_eq H i)
  invFun j := Classical.choose (H.exists_scaleOrder_eq J j)
  left_inv i := by
    have hstrict : StrictMono
        (fun k : Fin t ↦ ordUnit K (J.scaleGenerator k)) :=
      fun _ _ h ↦ J.scaleOrder_strict h
    apply hstrict.injective
    calc
      ordUnit K (J.scaleGenerator
          (Classical.choose (H.exists_scaleOrder_eq J
            (Classical.choose (J.exists_scaleOrder_eq H i))))) =
          ordUnit K (H.scaleGenerator
            (Classical.choose (J.exists_scaleOrder_eq H i))) :=
        Classical.choose_spec (H.exists_scaleOrder_eq J
          (Classical.choose (J.exists_scaleOrder_eq H i)))
      _ = ordUnit K (J.scaleGenerator i) :=
        Classical.choose_spec (J.exists_scaleOrder_eq H i)
  right_inv j := by
    have hstrict : StrictMono
        (fun k : Fin s ↦ ordUnit K (H.scaleGenerator k)) :=
      fun _ _ h ↦ H.scaleOrder_strict h
    apply hstrict.injective
    calc
      ordUnit K (H.scaleGenerator
          (Classical.choose (J.exists_scaleOrder_eq H
            (Classical.choose (H.exists_scaleOrder_eq J j))))) =
          ordUnit K (J.scaleGenerator
            (Classical.choose (H.exists_scaleOrder_eq J j))) :=
        Classical.choose_spec (J.exists_scaleOrder_eq H
          (Classical.choose (H.exists_scaleOrder_eq J j)))
      _ = ordUnit K (H.scaleGenerator j) :=
        Classical.choose_spec (H.exists_scaleOrder_eq J j)

@[simp]
theorem scaleOrder_scaleIndexEquiv {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition q L s)
    (i : Fin t) :
    ordUnit K (H.scaleGenerator (J.scaleIndexEquiv H i)) =
      ordUnit K (J.scaleGenerator i) :=
  Classical.choose_spec (J.exists_scaleOrder_eq H i)

/-- The scale matching also preserves component ranks. -/
theorem componentRank_scaleIndexEquiv {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition q L s)
    (i : Fin t) :
    H.componentRank (J.scaleIndexEquiv H i) = J.componentRank i := by
  have hinvariant :=
    J.scaleRankMultiplicity_eq H (ordUnit K (J.scaleGenerator i))
  rw [J.scaleRankMultiplicity_at_scale i] at hinvariant
  have hH := H.scaleRankMultiplicity_at_scale (J.scaleIndexEquiv H i)
  rw [J.scaleOrder_scaleIndexEquiv H i] at hH
  rw [hH] at hinvariant
  exact_mod_cast hinvariant.symm

/-- Matching by scale preserves the component order. -/
theorem scaleIndexEquiv_strictMono {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition q L s) :
    StrictMono (J.scaleIndexEquiv H) := by
  intro i j hij
  have hHstrict : StrictMono
      (fun k : Fin s ↦ ordUnit K (H.scaleGenerator k)) :=
    fun _ _ h ↦ H.scaleOrder_strict h
  have hHmono : Monotone
      (fun k : Fin s ↦ ordUnit K (H.scaleGenerator k)) := by
    exact hHstrict.monotone
  apply hHmono.reflect_lt
  rw [J.scaleOrder_scaleIndexEquiv H i,
    J.scaleOrder_scaleIndexEquiv H j]
  exact J.scaleOrder_strict hij

/-- Since the component scales in a Jordan decomposition are strictly
ordered, the canonical scale matching preserves the numerical component
index. -/
@[simp]
theorem scaleIndexEquiv_val {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition q L s)
    (i : Fin t) :
    (J.scaleIndexEquiv H i).val = i.val := by
  let e := J.scaleIndexEquiv H
  let E : Fin t ≃o Fin s := e.toOrderIso
    (J.scaleIndexEquiv_strictMono H).monotone
    (H.scaleIndexEquiv_strictMono J).monotone
  exact Fin.coe_orderIso_apply E i

end Lattice.JordanDecomposition

end Bong
