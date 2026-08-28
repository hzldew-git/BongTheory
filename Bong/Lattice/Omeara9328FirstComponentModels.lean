/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328NormalizedFirstComponents

/-!
# The common parity split for the first rank-four components

The normalized source and target first components use the same norm
generator and have the same weight order.  Consequently O'Meara 93:18 can
be applied to both in the same branch: 93:18(ii) in even parity and
93:18(iii) in odd parity.  This packages the resulting concrete data and
removes a duplicated branch choice from the proof of 93:28.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- The common integer whose parity selects 93:18(ii) or 93:18(iii). -/
noncomputable def firstNormWeightParity : Int :=
  ordUnit K S.firstNormGenerator +
    weightIdealOrder S.sourceFirstNormalized
      (S.sourceJordan.component 0).lattice

/-- Concrete, synchronized 93:18 output for the two normalized first
components. -/
inductive FirstComponentModels
    (S : Omeara9328RankFourReductionSystem J H) : Type (max u v w)
  | even
      (source : Omeara9318vData S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice (1 : Kˣ))
      (target : Omeara9318vData S.targetFirstNormalized
        (S.targetJordan.component 0).lattice (1 : Kˣ))
  | odd
      (source : Omeara9318RankFourOddData S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice S.firstNormGenerator)
      (target : Omeara9318RankFourOddData S.targetFirstNormalized
        (S.targetJordan.component 0).lattice S.firstNormGenerator)

/-- Apply the appropriate fully formalized 93:18 branch to both first
components using the coherent normalized generator. -/
noncomputable def firstComponentModels : S.FirstComponentModels := by
  by_cases heven : Even S.firstNormWeightParity
  · apply FirstComponentModels.even
    · exact omeara9318iiData S.sourceFirstNormalized_unimodular
        (by rw [S.sourceFirstNormalized_finrank]; omega)
        S.firstNormGenerator S.firstNormGenerator_source heven
    · apply omeara9318iiData S.targetFirstNormalized_unimodular
        (by rw [S.targetFirstNormalized_finrank]; omega)
        S.firstNormGenerator S.firstNormGenerator_target
      unfold firstNormWeightParity at heven
      simpa only [S.firstNormalized_weightIdealOrder_eq] using heven
  · have hodd : Odd S.firstNormWeightParity :=
      Int.not_even_iff_odd.mp heven
    apply FirstComponentModels.odd
    · exact omeara9318iiiData S.sourceFirstNormalized_unimodular
        S.sourceFirstNormalized_finrank S.firstNormGenerator
        S.firstNormGenerator_source hodd
    · apply omeara9318iiiData S.targetFirstNormalized_unimodular
        S.targetFirstNormalized_finrank S.firstNormGenerator
        S.firstNormGenerator_target
      unfold firstNormWeightParity at hodd
      simpa only [S.firstNormalized_weightIdealOrder_eq] using hodd

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
