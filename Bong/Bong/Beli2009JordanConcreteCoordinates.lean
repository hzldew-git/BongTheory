/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanAdaptedAlignment
import Bong.Bong.Beli2009JordanCoordinates

namespace Bong

open Dyadic Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m : Nat}

namespace BONG.StrictJordanAdaptedAlignment

/-!
## Concrete Jordan-block coordinates

The earlier `JordanBlockCoordinates` record is sound only when its interval
is tied to an actual Jordan component.  The two constructions below derive
those intervals and their alternating order profiles from a strict adapted
alignment.  Thus corresponding source and target blocks are no longer
arbitrary records: they are literal slices of the two global good BONGs.
-/

variable {a : GoodBONG q L (m + 1)} {b : GoodBONG r M (m + 1)}

noncomputable def componentStart
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (i : Fin S.componentCount) : Nat :=
  ∑ k ∈ Finset.Iio i, S.sourceJordan.toOrthogonalDecomposition.componentRank k

noncomputable def componentStop
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (i : Fin S.componentCount) : Nat :=
  S.componentStart i + S.sourceJordan.toOrthogonalDecomposition.componentRank i

theorem componentStop_le
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (i : Fin S.componentCount) : S.componentStop i ≤ m + 1 := by
  have hsum := S.sourceProfile.sum_componentRank_eq_length
  rw [← hsum]
  unfold componentStop componentStart
  have hsubset : insert i (Finset.Iio i) ⊆ Finset.univ := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_Iio] at hk ⊢
    rcases hk with rfl | hk
    · simp
    · exact Finset.mem_univ k
  have hle := Finset.sum_le_sum_of_subset hsubset
    (f := fun k ↦ S.sourceJordan.toOrthogonalDecomposition.componentRank k)
  rw [Finset.sum_insert (by simp)] at hle
  simpa only [add_comm] using hle

theorem componentStart_lt_componentStop
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (i : Fin S.componentCount) : S.componentStart i < S.componentStop i := by
  unfold componentStop
  exact Nat.lt_add_of_pos_right (S.sourceJordan.component_finrank_pos i)

theorem source_hasImproperEvenRank
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG) :
    S.weakAlignment.endpoint.sourceWeak.HasImproperEvenRank :=
  S.weakAlignment.endpoint.sourceParity

noncomputable def sourceComponentCoordinates
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (i : Fin S.componentCount) :
    a.JordanBlockCoordinates where
  start := S.componentStart i
  stop := S.componentStop i
  start_lt_stop := S.componentStart_lt_componentStop i
  stop_le := S.componentStop_le i
  scaleOrder := ordUnit K (S.sourceJordan.scaleGenerator i)
  normOrder := jordanEffectiveNormOrder S.sourceJordan i
  order_eq := by
    intro j hstart hstop
    let loc : Fin (S.sourceJordan.toOrthogonalDecomposition.componentRank i) :=
      ⟨j - S.componentStart i, by
        unfold componentStop at hstop
        omega⟩
    have hval : (S.sourceProfile.indexEquiv.symm ⟨i, loc⟩).val = j := by
      rw [S.sourceProfile.inverse_index_val]
      change S.componentStart i + (j - S.componentStart i) = j
      omega
    have hindex : S.sourceProfile.indexEquiv.symm ⟨i, loc⟩ =
        ⟨j, hstop.trans_le (S.componentStop_le i)⟩ := Fin.ext hval
    have hord := S.sourceProfile.order_inverse_indexEquiv i loc
    rw [hindex] at hord
    change a.toBONG.order ⟨j, hstop.trans_le (S.componentStop_le i)⟩ = _
    rw [hord]
    simp only [jordanExpectedOrder, loc]
    by_cases hproper : ordUnit K (S.sourceJordan.scaleGenerator i) =
        jordanEffectiveNormOrder S.sourceJordan i
    · simp [hproper]
      omega
    · simp only [hproper, if_false]
      by_cases heven : (j - S.componentStart i) % 2 = 0
      · have : Even (j - S.componentStart i) := Nat.even_iff.mpr heven
        simp [this, heven]
      · have : ¬ Even (j - S.componentStart i) := by
          simpa [Nat.even_iff] using heven
        simp [this, heven]
  proper_or_even := by
    by_cases hproper : ordUnit K (S.sourceJordan.scaleGenerator i) =
        jordanEffectiveNormOrder S.sourceJordan i
    · exact Or.inl hproper.symm
    · right
      have hscale : ordUnit K
            (S.weakAlignment.endpoint.sourceWeak.scaleGenerator i) <
          S.weakAlignment.endpoint.sourceWeak.effectiveNormOrderAt i
            (ordUnit K
              (S.weakAlignment.endpoint.sourceWeak.scaleGenerator i)) := by
        apply lt_of_le_of_ne
        · exact S.weakAlignment.endpoint.sourceWeak.targetScale_le_effectiveNormOrderAt
            i _
        · intro heq
          apply hproper
          unfold Lattice.WeakJordanDecomposition.effectiveNormOrderAt
            Lattice.WeakJordanDecomposition.scaleOrderFamily
            Lattice.WeakJordanDecomposition.normOrderFamily at heq
          simpa only [sourceJordan, toStrictJordanEndpointAlignment,
            StrictJordanEndpointAlignment.sourceJordan,
            StrictJordanEndpointWitness.jordan,
            Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
            jordanEffectiveNormOrder, jordanEffectiveNormOrderAt,
            Lattice.WeakJordanDecomposition.toJordan_normGenerator]
            using heq
      have heven :=
        S.source_hasImproperEvenRank.componentRank_even_of_lt_effectiveNormOrderAt
          S.weakAlignment.endpoint.sourceWeak i i hscale
      have hdiff : S.componentStop i - S.componentStart i =
          S.sourceJordan.toOrthogonalDecomposition.componentRank i := by
        simp only [componentStop, Nat.add_sub_cancel_left]
      rw [hdiff]
      change Even (finrank K
        (S.weakAlignment.endpoint.sourceWeak.component i).carrier)
      exact heven

noncomputable def targetComponentStart
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (i : Fin S.componentCount) : Nat :=
  ∑ k ∈ Finset.Iio i, S.targetJordan.toOrthogonalDecomposition.componentRank k

noncomputable def targetComponentStop
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (i : Fin S.componentCount) : Nat :=
  S.targetComponentStart i +
    S.targetJordan.toOrthogonalDecomposition.componentRank i

theorem targetComponentStop_le
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (i : Fin S.componentCount) : S.targetComponentStop i ≤ m + 1 := by
  have hsum := S.targetProfile.sum_componentRank_eq_length
  rw [← hsum]
  unfold targetComponentStop targetComponentStart
  have hsubset : insert i (Finset.Iio i) ⊆ Finset.univ := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_Iio] at hk ⊢
    rcases hk with rfl | hk
    · simp
    · exact Finset.mem_univ k
  have hle := Finset.sum_le_sum_of_subset hsubset
    (f := fun k ↦ S.targetJordan.toOrthogonalDecomposition.componentRank k)
  rw [Finset.sum_insert (by simp)] at hle
  simpa only [add_comm] using hle

theorem targetComponentStart_lt_componentStop
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (i : Fin S.componentCount) :
    S.targetComponentStart i < S.targetComponentStop i := by
  unfold targetComponentStop
  exact Nat.lt_add_of_pos_right (S.targetJordan.component_finrank_pos i)

theorem target_hasImproperEvenRank
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG) :
    S.weakAlignment.endpoint.targetWeak.HasImproperEvenRank :=
  S.weakAlignment.endpoint.targetParity

noncomputable def targetComponentCoordinates
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (i : Fin S.componentCount) : b.JordanBlockCoordinates where
  start := S.targetComponentStart i
  stop := S.targetComponentStop i
  start_lt_stop := S.targetComponentStart_lt_componentStop i
  stop_le := S.targetComponentStop_le i
  scaleOrder := ordUnit K (S.targetJordan.scaleGenerator i)
  normOrder := jordanEffectiveNormOrder S.targetJordan i
  order_eq := by
    intro j hstart hstop
    let loc : Fin (S.targetJordan.toOrthogonalDecomposition.componentRank i) :=
      ⟨j - S.targetComponentStart i, by
        unfold targetComponentStop at hstop
        omega⟩
    have hval : (S.targetProfile.indexEquiv.symm ⟨i, loc⟩).val = j := by
      rw [S.targetProfile.inverse_index_val]
      change S.targetComponentStart i + (j - S.targetComponentStart i) = j
      omega
    have hindex : S.targetProfile.indexEquiv.symm ⟨i, loc⟩ =
        ⟨j, hstop.trans_le (S.targetComponentStop_le i)⟩ := Fin.ext hval
    have hord := S.targetProfile.order_inverse_indexEquiv i loc
    rw [hindex] at hord
    change b.toBONG.order ⟨j, hstop.trans_le (S.targetComponentStop_le i)⟩ = _
    rw [hord]
    simp only [jordanExpectedOrder, loc]
    by_cases hproper : ordUnit K (S.targetJordan.scaleGenerator i) =
        jordanEffectiveNormOrder S.targetJordan i
    · simp [hproper]
      omega
    · simp only [hproper, if_false]
      by_cases heven : (j - S.targetComponentStart i) % 2 = 0
      · have : Even (j - S.targetComponentStart i) := Nat.even_iff.mpr heven
        simp [this, heven]
      · have : ¬ Even (j - S.targetComponentStart i) := by
          simpa [Nat.even_iff] using heven
        simp [this, heven]
  proper_or_even := by
    by_cases hproper : ordUnit K (S.targetJordan.scaleGenerator i) =
        jordanEffectiveNormOrder S.targetJordan i
    · exact Or.inl hproper.symm
    · right
      have hscale : ordUnit K
            (S.weakAlignment.endpoint.targetWeak.scaleGenerator i) <
          S.weakAlignment.endpoint.targetWeak.effectiveNormOrderAt i
            (ordUnit K
              (S.weakAlignment.endpoint.targetWeak.scaleGenerator i)) := by
        apply lt_of_le_of_ne
        · exact S.weakAlignment.endpoint.targetWeak.targetScale_le_effectiveNormOrderAt
            i _
        · intro heq
          apply hproper
          unfold Lattice.WeakJordanDecomposition.effectiveNormOrderAt
            Lattice.WeakJordanDecomposition.scaleOrderFamily
            Lattice.WeakJordanDecomposition.normOrderFamily at heq
          simpa only [targetJordan, toStrictJordanEndpointAlignment,
            StrictJordanEndpointAlignment.targetJordan,
            StrictJordanEndpointWitness.jordan,
            Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
            jordanEffectiveNormOrder, jordanEffectiveNormOrderAt,
            Lattice.WeakJordanDecomposition.toJordan_normGenerator]
            using heq
      have heven :=
        S.target_hasImproperEvenRank.componentRank_even_of_lt_effectiveNormOrderAt
          S.weakAlignment.endpoint.targetWeak i i hscale
      have hdiff : S.targetComponentStop i - S.targetComponentStart i =
          S.targetJordan.toOrthogonalDecomposition.componentRank i := by
        simp only [targetComponentStop, Nat.add_sub_cancel_left]
      rw [hdiff]
      change Even (finrank K
        (S.weakAlignment.endpoint.targetWeak.component i).carrier)
      exact heven

end BONG.StrictJordanAdaptedAlignment

end Bong
