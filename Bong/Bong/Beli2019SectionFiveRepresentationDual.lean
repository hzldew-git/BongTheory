/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019SectionFiveDual
import Bong.Bong.Beli2019SectionFourCentralDual
import Bong.Bong.DiagonalRepresentationCons
import Bong.Bong.DiagonalSquareIsometry
import Bong.Bong.DiagonalTailCancellation
import Bong.Bong.DiagonalTernaryCore

/-!
# Reverse-dual transport of Section 5 prefix representations

A prefix of a reverse-dual BONG is the reversed reciprocal diagonalization
of the complementary suffix of the original BONG.  Reciprocal diagonal
coefficients are square-equivalent to the original coefficients.  Thus a
representation between complementary reverse-dual prefixes gives a
representation between the original suffixes.  Appending the smaller
original prefix, changing between the two full BONG bases, and cancelling
the common suffix gives the required original prefix representation.

This is the field-valued linear-algebra step used in Section 5.2 for both
conditions (iii) and (iv); it uses no additional local-field law.
-/

namespace Bong

open Dyadic

universe u v

namespace LongRepresentationIndex

/-- The complementary long boundary used after swapping and reversing a
same-rank pair. -/
def reverseComplement {N : Nat} (i : LongRepresentationIndex N N) :
    LongRepresentationIndex N N where
  val := N - i.val
  one_lt := by
    have := i.succ_lt_large
    omega
  succ_lt_large := by
    have := i.one_lt
    have := i.succ_lt_large
    omega
  le_small_succ := by omega

@[simp]
theorem reverseComplement_val {N : Nat} (i : LongRepresentationIndex N N) :
    i.reverseComplement.val = N - i.val :=
  rfl

end LongRepresentationIndex

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V}
  {rank n : Nat}

/-- Reindex a diagonal form along an equivalence between two (possibly
definitionally different) finite coordinate types. -/
theorem DiagonalRepresents.reindexEquiv {m r : Nat}
    (c : Fin r → K) (e : Fin m ≃ Fin r) :
    DiagonalRepresents (c ∘ e) c := by
  let E := LinearEquiv.piCongrLeft K (fun _ : Fin r ↦ K) e
  refine ⟨E.toLinearMap, E.injective, ?_⟩
  intro x
  have hE (i : Fin m) : E x (e i) = x i := by
    change (Equiv.piCongrLeft (fun _ : Fin r ↦ K) e) x (e i) = x i
    exact Equiv.piCongrLeft_apply_apply (fun _ : Fin r ↦ K) e x i
  unfold diagonalQuadratic
  calc
    (∑ i, c i * (E x i) ^ 2) =
        ∑ i, c (e i) * (E x (e i)) ^ 2 := by
      exact (Equiv.sum_comp e (fun j ↦ c j * (E x j) ^ 2)).symm
    _ = ∑ i, (c ∘ e) i * x i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hE]
      rfl

/-- The nonzero coefficients in the suffix beginning at `k`. -/
noncomputable def suffixValueUnits
    (a : GoodBONG q L rank) (k : Nat) (hk : k ≤ rank) :
    Fin (rank - k) → Kˣ :=
  fun j ↦ a.valueUnit ⟨k + j.val, by omega⟩

/-- The field-valued coefficients in the suffix beginning at `k`. -/
noncomputable def suffixValues
    (a : GoodBONG q L rank) (k : Nat) (hk : k ≤ rank) :
    Fin (rank - k) → K :=
  diagonalUnitCoefficients (a.suffixValueUnits k hk)

/-- Canonical reindexing of a prefix followed by its complementary suffix
back to the full coordinate set. -/
noncomputable def prefixSuffixEquiv (k rank : Nat) (hk : k ≤ rank) :
    Fin (k + (rank - k)) ≃ Fin rank :=
  finCongr (Nat.add_sub_of_le hk)

theorem append_prefixValues_suffixValues
    (a : GoodBONG q L rank) (k : Nat) (hk : k ≤ rank) :
    Fin.append (a.prefixValues k hk) (a.suffixValues k hk) =
      a.value ∘ prefixSuffixEquiv k rank hk := by
  funext i
  refine Fin.addCases (m := k) (n := rank - k) (fun j ↦ ?_)
    (fun j ↦ ?_) i
  · rw [Fin.append_left]
    change a.value ⟨j.val, by omega⟩ =
      a.value (prefixSuffixEquiv k rank hk (Fin.castAdd (rank - k) j))
    congr 1
  · rw [Fin.append_right]
    change a.value ⟨k + j.val, by omega⟩ =
      a.value (prefixSuffixEquiv k rank hk (Fin.natAdd k j))
    congr 1

/-- Splitting a full BONG coefficient list into a prefix and suffix is an
isometry (expressed in the representation direction used in this project). -/
theorem appendPrefixSuffix_represents_values
    (a : GoodBONG q L rank) (k : Nat) (hk : k ≤ rank) :
    DiagonalRepresents
      (Fin.append (a.prefixValues k hk) (a.suffixValues k hk)) a.value := by
  rw [a.append_prefixValues_suffixValues k hk]
  exact DiagonalRepresents.reindexEquiv a.value
    (prefixSuffixEquiv k rank hk)

/-- The reverse direction of `appendPrefixSuffix_represents_values`. -/
theorem values_represents_appendPrefixSuffix
    (a : GoodBONG q L rank) (k : Nat) (hk : k ≤ rank) :
    DiagonalRepresents a.value
      (Fin.append (a.prefixValues k hk) (a.suffixValues k hk)) := by
  rw [a.append_prefixValues_suffixValues k hk]
  have h := DiagonalRepresents.reindexEquiv
    (a.value ∘ prefixSuffixEquiv k rank hk)
      (prefixSuffixEquiv k rank hk).symm
  have hcoeff :
      (a.value ∘ prefixSuffixEquiv k rank hk) ∘
          (prefixSuffixEquiv k rank hk).symm = a.value := by
    funext i
    simp
  rw [hcoeff] at h
  exact h

/-- Replace every nonzero diagonal coefficient by its inverse.  The two
diagonal spaces are explicitly isometric because `cᵢ/cᵢ⁻¹ = cᵢ²`. -/
theorem diagonalInverse_represents_self {k : Nat} (c : Fin k → Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients (fun i ↦ (c i)⁻¹))
      (diagonalUnitCoefficients c) := by
  have hisometric := QuadraticSpace.finiteDiagonal_isIsometric_of_eq_square_mul
    (diagonalUnitCoefficients (fun i ↦ (c i)⁻¹))
    (diagonalUnitCoefficients c)
    (fun i ↦ Units.ne_zero ((c i)⁻¹))
    (fun i ↦ Units.ne_zero (c i)) c (by
      intro i
      change (c i : K) = (c i : K) ^ 2 * (((c i)⁻¹ : Kˣ) : K)
      simp [pow_two, Units.ne_zero (c i)])
  apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
    (fun i ↦ (c i)⁻¹) c).mp
  exact ⟨(Classical.choice hisometric).toRepresentation⟩

/-- Reverse and invert a finite nonzero diagonal list. -/
noncomputable def reverseInverseUnits {k : Nat} (c : Fin k → Kˣ) :
    Fin k → Kˣ :=
  fun i ↦ (c (Fin.rev i))⁻¹

/-- A reversed reciprocal list diagonalizes the same quadratic space as the
original list. -/
theorem reverseInverse_represents_self {k : Nat} (c : Fin k → Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients (reverseInverseUnits c))
      (diagonalUnitCoefficients c) := by
  let d : Fin k → Kˣ := fun i ↦ c (Fin.rev i)
  have hinv := diagonalInverse_represents_self (K := K) d
  have hrev := DiagonalRepresents.reindex
    (diagonalUnitCoefficients c) Fin.revPerm
  change DiagonalRepresents
    (diagonalUnitCoefficients (fun i ↦ (c (Fin.rev i))⁻¹))
    (diagonalUnitCoefficients c)
  exact hinv.trans hrev

/-- Pure diagonal cancellation lemma behind reverse-dual prefix transport. -/
theorem prefixRepresentation_of_suffixRepresentation
    (a : GoodBONG q L rank) (b : GoodBONG q M rank)
    (pa pb : Nat) (hpa : pa ≤ rank) (hpb : pb ≤ rank)
    (hsuffix : DiagonalRepresents
      (a.suffixValues pa hpa) (b.suffixValues pb hpb)) :
    DiagonalRepresents (b.prefixValues pb hpb) (a.prefixValues pa hpa) := by
  let aPrefix := a.prefixValues pa hpa
  let bPrefix := b.prefixValues pb hpb
  let aSuffix := a.suffixValues pa hpa
  let bSuffix := b.suffixValues pb hpb
  have hwithPrefix : DiagonalRepresents
      (Fin.append bPrefix aSuffix) (Fin.append bPrefix bSuffix) := by
    exact (DiagonalRepresents.append_comm bPrefix aSuffix).trans <|
      (diagonalRepresents_append hsuffix bPrefix).trans <|
        DiagonalRepresents.append_comm bSuffix bPrefix
  have hfull : DiagonalRepresents
      (Fin.append bPrefix aSuffix) (Fin.append aPrefix aSuffix) := by
    exact hwithPrefix.trans <|
      (b.appendPrefixSuffix_represents_values pb hpb).trans <|
        (b.toBONG.diagonalRepresents_values a.toBONG).trans <|
          a.values_represents_appendPrefixSuffix pa hpa
  apply DiagonalRepresents.cancel_common_append bPrefix aPrefix aSuffix
  · intro i
    exact b.toBONG.value_ne_zero ⟨i.val, i.isLt.trans_le hpb⟩
  · intro i
    exact a.toBONG.value_ne_zero ⟨i.val, i.isLt.trans_le hpa⟩
  · intro i
    exact Units.ne_zero (a.suffixValueUnits pa hpa i)
  · exact hfull

namespace Beli2019SectionFiveReverseDualData

variable {a : GoodBONG q M (n + 1)} {b : GoodBONG q N (n + 1)}
  {inclusion : Beli2019IndexPInclusion q M N}

theorem targetDual_prefixValues_eq_reverseInverse_suffix
    (D : Beli2019SectionFiveReverseDualData a b inclusion)
    (k : Nat) (hk : k ≤ n + 1) :
    D.targetDual.prefixValues (n + 1 - k) (Nat.sub_le _ _) =
      diagonalUnitCoefficients
        (reverseInverseUnits (a.suffixValueUnits k hk)) := by
  funext j
  let jFull : Fin (n + 1) := ⟨j.val, j.isLt.trans_le (Nat.sub_le _ _)⟩
  have hindex : Fin.rev jFull =
      ⟨k + (Fin.rev j).val, by omega⟩ := by
    apply Fin.ext
    simp only [jFull, Fin.rev]
    omega
  have hv := D.targetValues jFull
  change (D.targetDual.valueUnit jFull : K) = _
  rw [hv, hindex]
  rfl

theorem sourceDual_prefixValues_eq_reverseInverse_suffix
    (D : Beli2019SectionFiveReverseDualData a b inclusion)
    (k : Nat) (hk : k ≤ n + 1) :
    D.sourceDual.prefixValues (n + 1 - k) (Nat.sub_le _ _) =
      diagonalUnitCoefficients
        (reverseInverseUnits (b.suffixValueUnits k hk)) := by
  funext j
  let jFull : Fin (n + 1) := ⟨j.val, j.isLt.trans_le (Nat.sub_le _ _)⟩
  have hindex : Fin.rev jFull =
      ⟨k + (Fin.rev j).val, by omega⟩ := by
    apply Fin.ext
    simp only [jFull, Fin.rev]
    omega
  have hv := D.sourceValues jFull
  change (D.sourceDual.valueUnit jFull : K) = _
  rw [hv, hindex]
  rfl

/-- A representation at complementary prefixes of the swapped reverse-dual
pair gives the corresponding original prefix representation. -/
theorem originalPrefixRepresentation_of_reverse
    (D : Beli2019SectionFiveReverseDualData a b inclusion)
    (pa pb : Nat) (hpa : pa ≤ n + 1) (hpb : pb ≤ n + 1)
    (hreverse : DiagonalRepresents
      (D.targetDual.prefixValues (n + 1 - pa) (Nat.sub_le _ _))
      (D.sourceDual.prefixValues (n + 1 - pb) (Nat.sub_le _ _))) :
    DiagonalRepresents (b.prefixValues pb hpb) (a.prefixValues pa hpa) := by
  rw [D.targetDual_prefixValues_eq_reverseInverse_suffix pa hpa,
    D.sourceDual_prefixValues_eq_reverseInverse_suffix pb hpb] at hreverse
  have ha := reverseInverse_represents_self
    (K := K) (a.suffixValueUnits pa hpa)
  have hb := reverseInverse_represents_self
    (K := K) (b.suffixValueUnits pb hpb)
  have hsuffix : DiagonalRepresents
      (a.suffixValues pa hpa) (b.suffixValues pb hpb) := by
    exact ha.symm_of_sameRank.trans (hreverse.trans hb)
  exact prefixRepresentation_of_suffixRepresentation
    a b pa pb hpa hpb hsuffix

/-- Section 5.2, condition (iii): transport the represented conclusion at
the complementary central boundary back to the original inclusion. -/
theorem originalCentralRepresentation_of_reverse
    (D : Beli2019SectionFiveReverseDualData a b inclusion)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hreverse : DiagonalRepresents
      (D.targetDual.prefixValues (i.reversePrevious.val - 1)
        i.reversePrevious.previous_le_sameRank)
      (D.sourceDual.prefixValues i.reversePrevious.val
        i.reversePrevious.current_le_sameRank)) :
    DiagonalRepresents
      (b.prefixValues (i.val - 1) i.previous_le_sameRank)
      (a.prefixValues i.val i.current_le_sameRank) := by
  apply D.originalPrefixRepresentation_of_reverse
    i.val (i.val - 1) i.current_le_sameRank i.previous_le_sameRank
  have htargetLength : n + 1 - i.val =
      i.reversePrevious.val - 1 := by
    simp only [CentralRepresentationIndex.reversePrevious_val]
    have := i.one_lt
    have := i.lt_large
    omega
  have hsourceLength : n + 1 - (i.val - 1) =
      i.reversePrevious.val := by
    simp only [CentralRepresentationIndex.reversePrevious_val]
  exact prefixRepresents_cast D.targetDual D.sourceDual
    htargetLength.symm hsourceLength.symm hreverse

/-- Certificate-level reverse-dual reduction for condition (iii). -/
theorem originalCentralCertificate_of_reverse
    (D : Beli2019SectionFiveReverseDualData a b inclusion)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (C : Beli2019SectionFiveCentralCertificate
      D.sourceDual D.targetDual i.reversePrevious) :
    Beli2019SectionFiveCentralCertificate a b i := by
  have hAlpha : ∀ k : RepresentationIndex (n + 1) (n + 1),
      D.sourceDual.representationAlpha D.targetDual k.reverse =
        a.representationAlpha b k := by
    intro k
    exact a.representationAlpha_reverseDual_swap b
      D.targetDual D.sourceDual D.targetOrder D.sourceOrder
        D.truncatedPrefixDefect k
  cases C with
  | vacuous hnotDual =>
      apply Beli2019SectionFiveCentralCertificate.vacuous
      intro htrigger
      apply hnotDual
      exact a.centralAlphaTrigger_reverseDual_swap b
        D.targetDual D.sourceDual D.targetOrder D.sourceOrder
          hAlpha i htrigger
  | represented hrepresentation =>
      exact Beli2019SectionFiveCentralCertificate.represented
        (D.originalCentralRepresentation_of_reverse i hrepresentation)

/-- The numerical trigger in condition (iv) is invariant under the swapped
reverse-dual operation at the complementary long boundary. -/
theorem sectionFiveLongTrigger_reverseDual_swap
    (D : Beli2019SectionFiveReverseDualData a b inclusion)
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : sectionFiveLongTrigger a b i) :
    sectionFiveLongTrigger D.sourceDual D.targetDual
      i.reverseComplement := by
  let j := i.reverseComplement
  have hSourceNext :
      D.sourceDual.order ⟨j.val + 1, j.succ_lt_large⟩ =
        -b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.succ_lt_large
          omega⟩ := by
    rw [D.sourceOrder]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, j, LongRepresentationIndex.reverseComplement_val]
    have := i.one_lt
    have := i.succ_lt_large
    omega
  have hTargetPrevious :
      D.targetDual.order ⟨j.val - 1, by
        have := j.succ_lt_large
        omega⟩ =
        -a.order ⟨i.val, by have := i.succ_lt_large; omega⟩ := by
    rw [D.targetOrder]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, j, LongRepresentationIndex.reverseComplement_val]
    have := i.one_lt
    have := i.succ_lt_large
    omega
  have hTargetTwoPrevious :
      D.targetDual.order ⟨j.val - 2, by
        have := j.one_lt
        have := j.le_small_succ
        omega⟩ =
        -a.order ⟨i.val + 1, i.succ_lt_large⟩ := by
    rw [D.targetOrder]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, j, LongRepresentationIndex.reverseComplement_val]
    have := i.one_lt
    have := i.succ_lt_large
    omega
  have hSourceCurrent :
      D.sourceDual.order ⟨j.val, by
        have := j.succ_lt_large
        omega⟩ =
        -b.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.succ_lt_large
          omega⟩ := by
    rw [D.sourceOrder]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, j, LongRepresentationIndex.reverseComplement_val]
    have := i.one_lt
    have := i.succ_lt_large
    omega
  unfold sectionFiveLongTrigger at htrigger ⊢
  rcases htrigger with ⟨hfirst, hsecond, hthird⟩
  have hiLe : i.val ≤ n + 1 := by
    have := i.succ_lt_large
    omega
  have hjLe : j.val ≤ n + 1 := by
    simp only [j, LongRepresentationIndex.reverseComplement_val]
    omega
  rw [dif_pos hiLe] at hfirst
  rw [dif_pos hjLe]
  rw [hSourceNext, hTargetPrevious, hTargetTwoPrevious, hSourceCurrent]
  constructor
  · omega
  constructor <;> omega

/-- Section 5.2, condition (iv): transport the represented conclusion at
the complementary long boundary back to the original inclusion. -/
theorem originalLongRepresentation_of_reverse
    (D : Beli2019SectionFiveReverseDualData a b inclusion)
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (hreverse : DiagonalRepresents
      (D.targetDual.prefixValues (i.reverseComplement.val - 1)
        (by have := i.reverseComplement.succ_lt_large; omega))
      (D.sourceDual.prefixValues (i.reverseComplement.val + 1)
        (by have := i.reverseComplement.succ_lt_large; omega))) :
    DiagonalRepresents
      (b.prefixValues (i.val - 1) i.previous_le_sameRank)
      (a.prefixValues (i.val + 1) i.next_le_sameRank) := by
  apply D.originalPrefixRepresentation_of_reverse
    (i.val + 1) (i.val - 1) i.next_le_sameRank i.previous_le_sameRank
  have htargetLength : n + 1 - (i.val + 1) =
      i.reverseComplement.val - 1 := by
    simp only [LongRepresentationIndex.reverseComplement_val]
    have := i.one_lt
    have := i.succ_lt_large
    omega
  have hsourceLength : n + 1 - (i.val - 1) =
      i.reverseComplement.val + 1 := by
    simp only [LongRepresentationIndex.reverseComplement_val]
    have := i.one_lt
    have := i.succ_lt_large
    omega
  exact prefixRepresents_cast D.targetDual D.sourceDual
    htargetLength.symm hsourceLength.symm hreverse

/-- Certificate-level reverse-dual reduction for condition (iv). -/
theorem originalLongCertificate_of_reverse
    (D : Beli2019SectionFiveReverseDualData a b inclusion)
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (C : Beli2019SectionFiveLongCertificate
      D.sourceDual D.targetDual i.reverseComplement) :
    Beli2019SectionFiveLongCertificate a b i := by
  cases C with
  | vacuous hnotDual =>
      apply Beli2019SectionFiveLongCertificate.vacuous
      intro htrigger
      exact hnotDual (D.sectionFiveLongTrigger_reverseDual_swap i htrigger)
  | represented hrepresentation =>
      exact Beli2019SectionFiveLongCertificate.represented
        (D.originalLongRepresentation_of_reverse i hrepresentation)

end Beli2019SectionFiveReverseDualData

end BONG.GoodBONG

end Bong
