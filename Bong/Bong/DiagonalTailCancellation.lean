/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.DiagonalCodimensionOneCancellation
import Bong.Bong.DiagonalHeadCancellation

/-!
# Cancellation of a common diagonal tail

This file supplies the right-handed companion to common-head cancellation.
It proves cancellation of one final coefficient, an appended block, and an
arbitrary common suffix of two equal-rank nondegenerate diagonal forms.
-/

namespace Bong

universe u

namespace DiagonalRepresents

variable {K : Type u} [Field K]

private theorem trans_private
    {l m n : Nat} {a : Fin l → K} {b : Fin m → K} {c : Fin n → K}
    (hab : DiagonalRepresents a b) (hbc : DiagonalRepresents b c) :
    DiagonalRepresents a c := by
  rcases hab with ⟨f, hf, hqf⟩
  rcases hbc with ⟨g, hg, hqg⟩
  refine ⟨g.comp f, hg.comp hf, ?_⟩
  intro x
  rw [LinearMap.comp_apply, hqg, hqf]

/-- Reindexing diagonal coefficients by a permutation preserves their
diagonal quadratic space. -/
theorem reindex {n : Nat} (a : Fin n → K) (e : Equiv.Perm (Fin n)) :
    DiagonalRepresents (a ∘ e) a := by
  let E := LinearEquiv.piCongrLeft K (fun _ : Fin n => K) e
  refine ⟨E.toLinearMap, E.injective, ?_⟩
  intro x
  have hE (i : Fin n) : E x (e i) = x i := by
    change (Equiv.piCongrLeft (fun _ : Fin n => K) e) x (e i) = x i
    exact Equiv.piCongrLeft_apply_apply (fun _ : Fin n => K) e x i
  unfold diagonalQuadratic
  calc
    (∑ i, a i * (E x i) ^ 2) =
        ∑ i, a (e i) * (E x (e i)) ^ 2 := by
      exact (Equiv.sum_comp e (fun j => a j * (E x j) ^ 2)).symm
    _ = ∑ i, (a ∘ e) i * x i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hE]
      rfl

/-- The standard permutation which interchanges two consecutive finite
coordinate blocks. -/
private def finAddCommEquiv (m n : Nat) : Fin (m + n) ≃ Fin (n + m) :=
  finSumFinEquiv.symm |>.trans (Equiv.sumComm (Fin m) (Fin n)) |>.trans
    finSumFinEquiv

/-- Orthogonal sums of diagonal forms commute. -/
theorem append_comm {m n : Nat} (a : Fin m → K) (b : Fin n → K) :
    DiagonalRepresents (Fin.append a b) (Fin.append b a) := by
  let e := finAddCommEquiv m n
  let E := LinearEquiv.piCongrLeft K (fun _ : Fin (n + m) => K) e
  refine ⟨E.toLinearMap, E.injective, ?_⟩
  intro x
  have hE (i : Fin (m + n)) : E x (e i) = x i := by
    change (Equiv.piCongrLeft (fun _ : Fin (n + m) => K) e) x (e i) = x i
    exact Equiv.piCongrLeft_apply_apply (fun _ : Fin (n + m) => K) e x i
  have hcoeff (i : Fin (m + n)) :
      Fin.append b a (e i) = Fin.append a b i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [e, finAddCommEquiv]
    · simp [e, finAddCommEquiv]
  unfold diagonalQuadratic
  calc
    (∑ i, Fin.append b a i * (E x i) ^ 2) =
        ∑ i, Fin.append b a (e i) * (E x (e i)) ^ 2 := by
      exact (Equiv.sum_comp e
        (fun j => Fin.append b a j * (E x j) ^ 2)).symm
    _ = ∑ i, Fin.append a b i * x i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hcoeff, hE]

/-- Cancel a common nonzero final coefficient from a representation of
nondegenerate diagonal forms. -/
theorem cancel_common_last [CharZero K]
    {m n : Nat} (last : K) (source : Fin m → K) (target : Fin n → K)
    (hlast : last ≠ 0) (hsource : ∀ i, source i ≠ 0)
    (htarget : ∀ i, target i ≠ 0)
    (hrep : DiagonalRepresents
      (Fin.snoc source last) (Fin.snoc target last)) :
    DiagonalRepresents source target := by
  let sourceFull : Fin (m + 1) → K := Fin.snoc source last
  let targetFull : Fin (n + 1) → K := Fin.snoc target last
  have hreverseFull :
      DiagonalRepresents (sourceFull ∘ Fin.revPerm)
        (targetFull ∘ Fin.revPerm) := by
    exact trans_private
      (trans_private (reindex sourceFull Fin.revPerm) hrep)
      (reindex targetFull Fin.revPerm).symm_of_sameRank
  have hsourceReverse :
      sourceFull ∘ Fin.revPerm = Fin.cons last (source ∘ Fin.rev) := by
    change Fin.snoc source last ∘ Fin.rev =
      Fin.cons last (source ∘ Fin.rev)
    exact Fin.snoc_comp_rev last source
  have htargetReverse :
      targetFull ∘ Fin.revPerm = Fin.cons last (target ∘ Fin.rev) := by
    change Fin.snoc target last ∘ Fin.rev =
      Fin.cons last (target ∘ Fin.rev)
    exact Fin.snoc_comp_rev last target
  have hreverseHead :
      DiagonalRepresents (Fin.cons last (source ∘ Fin.rev))
        (Fin.cons last (target ∘ Fin.rev)) := by
    rw [hsourceReverse, htargetReverse] at hreverseFull
    exact hreverseFull
  have hcancelled :
      DiagonalRepresents (source ∘ Fin.rev) (target ∘ Fin.rev) := by
    apply cancel_common_head last (source ∘ Fin.rev) (target ∘ Fin.rev)
    · exact hlast
    · intro i
      exact hsource i.rev
    · intro i
      exact htarget i.rev
    · exact hreverseHead
  exact trans_private
    (trans_private (reindex source Fin.revPerm).symm_of_sameRank hcancelled)
    (reindex target Fin.revPerm)

/-- Cancel a common nonzero diagonal block appended to both sides of a
representation. -/
theorem cancel_common_append [CharZero K]
    {m n k : Nat} (source : Fin m → K) (target : Fin n → K)
    (common : Fin k → K) (hsource : ∀ i, source i ≠ 0)
    (htarget : ∀ i, target i ≠ 0) (hcommon : ∀ i, common i ≠ 0)
    (hrep : DiagonalRepresents (Fin.append source common)
      (Fin.append target common)) :
    DiagonalRepresents source target := by
  induction k with
  | zero =>
      have hsourceZero : Fin.append source common = source := by
        funext i
        change Fin.append source common (Fin.castAdd 0 i) = source i
        rw [Fin.append_left]
      have htargetZero : Fin.append target common = target := by
        funext i
        change Fin.append target common (Fin.castAdd 0 i) = target i
        rw [Fin.append_left]
      rw [hsourceZero, htargetZero] at hrep
      exact hrep
  | succ k ih =>
      let commonInit : Fin k → K := Fin.init common
      let commonLast : K := common (Fin.last k)
      have hcommonInit : ∀ i, commonInit i ≠ 0 := by
        intro i
        exact hcommon i.castSucc
      have hsourceAppend : ∀ i, Fin.append source commonInit i ≠ 0 := by
        intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa using hsource j
        · simpa [commonInit] using hcommonInit j
      have htargetAppend : ∀ i, Fin.append target commonInit i ≠ 0 := by
        intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa using htarget j
        · simpa [commonInit] using hcommonInit j
      have hsourceSnoc :
          Fin.snoc (Fin.append source commonInit) commonLast =
            Fin.append source common := by
        calc
          Fin.snoc (Fin.append source commonInit) commonLast =
              Fin.append source (Fin.snoc commonInit commonLast) :=
            (Fin.append_snoc source commonInit commonLast).symm
          _ = Fin.append source common := by
            rw [show Fin.snoc commonInit commonLast = common by
              exact Fin.snoc_init_self common]
      have htargetSnoc :
          Fin.snoc (Fin.append target commonInit) commonLast =
            Fin.append target common := by
        calc
          Fin.snoc (Fin.append target commonInit) commonLast =
              Fin.append target (Fin.snoc commonInit commonLast) :=
            (Fin.append_snoc target commonInit commonLast).symm
          _ = Fin.append target common := by
            rw [show Fin.snoc commonInit commonLast = common by
              exact Fin.snoc_init_self common]
      have hlast : commonLast ≠ 0 := hcommon (Fin.last k)
      have hcancelled :
          DiagonalRepresents (Fin.append source commonInit)
            (Fin.append target commonInit) := by
        apply cancel_common_last commonLast
          (Fin.append source commonInit) (Fin.append target commonInit)
          hlast hsourceAppend htargetAppend
        rw [hsourceSnoc, htargetSnoc]
        exact hrep
      exact ih commonInit hcommonInit hcancelled

/-- Cancel an arbitrary finite common nondegenerate diagonal prefix.  The
blocks are first interchanged, after which `cancel_common_append` applies. -/
theorem cancel_common_prefix [CharZero K]
    {m n r : Nat} (common : Fin m → K)
    (source : Fin n → K) (target : Fin r → K)
    (hcommon : ∀ i, common i ≠ 0)
    (hsource : ∀ i, source i ≠ 0)
    (htarget : ∀ i, target i ≠ 0)
    (hrep : DiagonalRepresents
      (Fin.append common source) (Fin.append common target)) :
    DiagonalRepresents source target := by
  have hswapped : DiagonalRepresents
      (Fin.append source common) (Fin.append target common) :=
    trans_private
      (trans_private (append_comm source common) hrep)
      (append_comm common target)
  exact cancel_common_append source target common
    hsource htarget hcommon hswapped

/-- If two nondegenerate diagonal forms agree from coordinate `k` onward,
then an equal-rank representation restricts to their first `k` entries. -/
theorem cancel_common_suffix [CharZero K]
    {n k : Nat} (source target : Fin n → K) (hk : k ≤ n)
    (hsource : ∀ i, source i ≠ 0) (htarget : ∀ i, target i ≠ 0)
    (htail : ∀ i, k ≤ i.val → source i = target i)
    (hrep : DiagonalRepresents source target) :
    DiagonalRepresents
      (fun i : Fin k => source ⟨i.val, i.isLt.trans_le hk⟩)
      (fun i : Fin k => target ⟨i.val, i.isLt.trans_le hk⟩) := by
  rcases Nat.exists_eq_add_of_le hk with ⟨d, hd⟩
  subst n
  let sourcePrefix : Fin k → K := fun i => source (Fin.castAdd d i)
  let targetPrefix : Fin k → K := fun i => target (Fin.castAdd d i)
  let common : Fin d → K := fun j => source (Fin.natAdd k j)
  have hsourceDecomp : source = Fin.append sourcePrefix common := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [sourcePrefix]
    · simp [common]
  have htargetDecomp : target = Fin.append targetPrefix common := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [targetPrefix]
    · simp only [Fin.append_right, common]
      exact (htail (Fin.natAdd k j) (by simp)).symm
  have hsourcePrefix : ∀ i, sourcePrefix i ≠ 0 := by
    intro i
    exact hsource (Fin.castAdd d i)
  have htargetPrefix : ∀ i, targetPrefix i ≠ 0 := by
    intro i
    exact htarget (Fin.castAdd d i)
  have hcommon : ∀ i, common i ≠ 0 := by
    intro i
    exact hsource (Fin.natAdd k i)
  have happend : DiagonalRepresents
      (Fin.append sourcePrefix common) (Fin.append targetPrefix common) := by
    rw [← hsourceDecomp, ← htargetDecomp]
    exact hrep
  have hcancelled := cancel_common_append sourcePrefix targetPrefix common
    hsourcePrefix htargetPrefix hcommon happend
  convert hcancelled using 1 <;> funext i <;> rfl

end DiagonalRepresents

end Bong
