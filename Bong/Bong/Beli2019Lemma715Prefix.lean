/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma715Orders
import Bong.Bong.Beli2019CanonicalApproximation
import Bong.Bong.DiagonalTailCancellation

/-!
# Beli (2019), Lemma 7.15: isometry of the prefixes

The bracket `[a₁, ..., aᵢ]` in the paper is represented here by the finite
nondegenerate diagonal quadratic space attached to the first `i`
coefficients.  Both full coefficient lists diagonalize the same ambient
quadratic space.  Once their suffixes agree, Witt cancellation of that common
tail gives an actual quadratic-space isometry of the corresponding prefixes.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The finite diagonal quadratic space denoted by
`[a₁, ..., aₖ]` in the paper. -/
noncomputable def prefixDiagonalSpace
    (b : GoodBONG q L n) (k : Nat) (hk : k ≤ n) :
    QuadraticSpace K (Fin k → K) :=
  QuadraticSpace.finiteDiagonal (b.prefixValues k hk) (by
    intro i
    exact b.toBONG.value_ne_zero
      ⟨i.val, i.isLt.trans_le hk⟩)

/-- If two full good BONGs diagonalize the same ambient quadratic space and
their coefficients agree from `k` onward, then their length-`k` diagonal
prefixes are isometric. -/
theorem prefixDiagonalSpace_isIsometric_of_suffix_valueUnit_eq
    (a : GoodBONG q L n) (b : GoodBONG q M n)
    (k : Nat) (hk : k ≤ n)
    (htail : ∀ i, k ≤ i.val → a.valueUnit i = b.valueUnit i) :
    (a.prefixDiagonalSpace k hk).IsIsometric
      (b.prefixDiagonalSpace k hk) := by
  have hsource : ∀ i, a.value i ≠ 0 := a.toBONG.value_ne_zero
  have htarget : ∀ i, b.value i ≠ 0 := b.toBONG.value_ne_zero
  have htailValues : ∀ i, k ≤ i.val → a.value i = b.value i := by
    intro i hi
    change (a.valueUnit i : K) = (b.valueUnit i : K)
    exact congrArg Units.val (htail i hi)
  have hfull : DiagonalRepresents a.value b.value :=
    a.toBONG.diagonalRepresents_values b.toBONG
  have hprefixRaw := DiagonalRepresents.cancel_common_suffix
    a.value b.value hk hsource htarget htailValues hfull
  have hprefix : DiagonalRepresents
      (a.prefixValues k hk) (b.prefixValues k hk) := by
    change DiagonalRepresents
      (fun i : Fin k ↦ a.value ⟨i.val, i.isLt.trans_le hk⟩)
      (fun i : Fin k ↦ b.value ⟨i.val, i.isLt.trans_le hk⟩)
    exact hprefixRaw
  have hsourcePrefix : ∀ i, a.prefixValues k hk i ≠ 0 := by
    intro i
    exact a.toBONG.value_ne_zero ⟨i.val, i.isLt.trans_le hk⟩
  have htargetPrefix : ∀ i, b.prefixValues k hk i ≠ 0 := by
    intro i
    exact b.toBONG.value_ne_zero ⟨i.val, i.isLt.trans_le hk⟩
  rcases DiagonalRepresents.toQuadraticSpaceRepresents
      hsourcePrefix htargetPrefix hprefix with ⟨f⟩
  have hisometry :
      (QuadraticSpace.finiteDiagonal
          (a.prefixValues k hk) hsourcePrefix).IsIsometric
        (QuadraticSpace.finiteDiagonal
          (b.prefixValues k hk) htargetPrefix) :=
    ⟨f.toIsometryOfFinrankEq rfl⟩
  simpa only [prefixDiagonalSpace] using hisometry

variable [DyadicDiscriminantClassLaws K]

/-- Prefix isometry in the type-I branch.  It already starts at prefix
length `s`, as asserted in the last sentence of Lemma 7.15. -/
theorem lemma715_typeI_prefix_isIsometric
    (b : GoodBONG q L (n + 3)) (s : Nat)
    (hsTwo : 2 ≤ s) (hsRank : s ≤ n + 3)
    (result : GoodBONG q M (n + 3))
    (hvalues : ∀ i, result.valueUnit i =
      lemma714TypeITargetValues b s hsTwo hsRank i)
    (k : Nat) (hsk : s ≤ k) (hk : k ≤ n + 3) :
    (b.prefixDiagonalSpace k hk).IsIsometric
      (result.prefixDiagonalSpace k hk) := by
  apply prefixDiagonalSpace_isIsometric_of_suffix_valueUnit_eq
  intro i hki
  have hsi : s ≤ i.val := hsk.trans hki
  calc
    b.valueUnit i = lemma714TypeITargetValues b s hsTwo hsRank i :=
      (lemma714TypeITargetValues_suffix b s hsTwo hsRank i hsi).symm
    _ = result.valueUnit i := (hvalues i).symm

/-- Prefix isometry in the type-II branch.  The common suffix begins after
the modified ternary block, so the first admissible prefix length is
`s + 1`. -/
theorem lemma715_typeII_prefix_isIsometric
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hII : Lemma714IsTypeII b R s)
    (ε η : Kˣ)
    (result : GoodBONG q M (n + 3))
    (hvalues : ∀ i, result.valueUnit i =
      lemma714TypeIITargetValues b s D.two_le
        (Classical.choose hII) ε η i)
    (k : Nat) (hsk : s + 1 ≤ k) (hk : k ≤ n + 3) :
    (b.prefixDiagonalSpace k hk).IsIsometric
      (result.prefixDiagonalSpace k hk) := by
  apply prefixDiagonalSpace_isIsometric_of_suffix_valueUnit_eq
  intro i hki
  have hsi : s < i.val := by omega
  calc
    b.valueUnit i = lemma714TypeIITargetValues b s D.two_le
        (Classical.choose hII) ε η i :=
      (lemma714TypeIITargetValues_suffix b s D.two_le
        (Classical.choose hII) ε η i hsi).symm
    _ = result.valueUnit i := (hvalues i).symm

/-- The order conclusion enriched with the prefix-isometry assertions of
Lemma 7.15. -/
inductive Beli2019Lemma715PrefixConclusion
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hnorm : Lattice.normIdeal q L = Lattice.powerIdeal (K := K) R)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.powerIdeal (K := K)
        (R - ramificationIndex K + 1))
    (ε η : Kˣ) : Prop where
  | typeI
      (hI : Lemma714IsTypeI b R s)
      (result : GoodBONG q
        (Lattice.nonNormGeneratorLattice R hnorm hscale) (n + 3))
      (values : ∀ i, result.valueUnit i =
        lemma714TypeITargetValues b s D.two_le D.le_rank i)
      (order_eq : ∀ i, s ≤ i.val → b.order i = result.order i)
      (prefix_isometric : ∀ (k : Nat), s ≤ k → (hk : k ≤ n + 3) →
        (b.prefixDiagonalSpace k hk).IsIsometric
          (result.prefixDiagonalSpace k hk)) :
      Beli2019Lemma715PrefixConclusion b R s D hnorm hscale ε η
  | typeII
      (hII : Lemma714IsTypeII b R s)
      (result : GoodBONG q
        (Lattice.nonNormGeneratorLattice R hnorm hscale) (n + 3))
      (values : ∀ i, result.valueUnit i =
        lemma714TypeIITargetValues b s D.two_le
          (Classical.choose hII) ε η i)
      (order_eq : ∀ i, s ≤ i.val → b.order i = result.order i)
      (prefix_isometric : ∀ (k : Nat), s + 1 ≤ k →
        (hk : k ≤ n + 3) →
        (b.prefixDiagonalSpace k hk).IsIsometric
          (result.prefixDiagonalSpace k hk)) :
      Beli2019Lemma715PrefixConclusion b R s D hnorm hscale ε η

/-- Extract all prefix-isometry assertions of Lemma 7.15 from the branch
information and exact coefficient lists retained by the order conclusion. -/
theorem Beli2019Lemma715OrderConclusion.toPrefixConclusion
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hnorm : Lattice.normIdeal q L = Lattice.powerIdeal (K := K) R)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.powerIdeal (K := K)
        (R - ramificationIndex K + 1))
    (ε η : Kˣ)
    (C : Beli2019Lemma715OrderConclusion
      b R s D hnorm hscale ε η) :
    Beli2019Lemma715PrefixConclusion b R s D hnorm hscale ε η := by
  cases C with
  | typeI hI result hvalues horders =>
      exact Beli2019Lemma715PrefixConclusion.typeI hI result hvalues
        horders (fun k hsk hk ↦
          lemma715_typeI_prefix_isIsometric b s D.two_le D.le_rank
            result hvalues k hsk hk)
  | typeII hII result hvalues horders =>
      exact Beli2019Lemma715PrefixConclusion.typeII hII result hvalues
        horders (fun k hsk hk ↦
          lemma715_typeII_prefix_isIsometric b R s D hII ε η
            result hvalues k hsk hk)

end BONG.GoodBONG

end Bong
