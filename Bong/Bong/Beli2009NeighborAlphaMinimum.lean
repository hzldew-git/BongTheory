import Bong.Bong.Beli2009AlphaCompression

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {m : Nat}

namespace BONG.GoodBONG

/-- Beli's Corollary 2.5(i), with the two actual neighbouring
`alpha`-terms displayed at an interior index. -/
theorem alphaValue_eq_min_four_neighborCandidates
    (b : GoodBONG q L (m + 2)) (i : Fin (m + 1))
    (hleft : 0 < i.val) (hright : i.val + 1 < m + 1) :
    let p : Fin (m + 1) := ⟨i.val - 1, by omega⟩
    let s : Fin (m + 1) := ⟨i.val + 1, by omega⟩
    (b.alphaValue i : WithTop ℚ) =
      min (b.halfGapCandidate i)
        (min (b.leftDefectCandidate i i)
          (min (b.neighborAlphaCandidate i p)
            (b.neighborAlphaCandidate i s))) := by
  dsimp only
  classical
  let p : Fin (m + 1) := ⟨i.val - 1, by omega⟩
  let s : Fin (m + 1) := ⟨i.val + 1, by omega⟩
  have hneighbors : b.neighborAlphaCandidates i =
      {b.neighborAlphaCandidate i p, b.neighborAlphaCandidate i s} := by
    ext x
    simp only [neighborAlphaCandidates, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨j, hj | hj, rfl⟩
      · left
        congr 1
        apply Fin.ext
        dsimp only [p]
        omega
      · right
        congr 1
        apply Fin.ext
        dsimp only [s]
        omega
    · rintro (rfl | rfl)
      · refine ⟨p, Or.inl ?_, rfl⟩
        dsimp only [p]
        omega
      · refine ⟨s, Or.inr ?_, rfl⟩
        rfl
  have hcor := b.beli2009Corollary25_i i
  simp only [recursiveAlphaCandidates, hneighbors] at hcor
  rw [b.coe_alphaValue, hcor]
  simp [p, s, min_comm]

/-- Beli's Corollary 2.5(i) at the first `alpha`-index. -/
theorem alphaValue_zero_eq_min_neighborSuccessor
    (b : GoodBONG q L (m + 3)) :
    let i : Fin (m + 2) := 0
    let s : Fin (m + 2) := 1
    (b.alphaValue i : WithTop ℚ) =
      min (b.halfGapCandidate i)
        (min (b.leftDefectCandidate i i)
          (b.neighborAlphaCandidate i s)) := by
  dsimp only
  classical
  let i : Fin (m + 2) := 0
  let s : Fin (m + 2) := 1
  have hneighbors : b.neighborAlphaCandidates i =
      {b.neighborAlphaCandidate i s} := by
    ext x
    simp only [neighborAlphaCandidates, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨j, hj | hj, rfl⟩
      · change j.val + 1 = 0 at hj
        omega
      · congr 1
        apply Fin.ext
        change 0 + 1 = j.val at hj
        change j.val = 1
        omega
    · rintro rfl
      exact ⟨s, Or.inr rfl, rfl⟩
  have hcor := b.beli2009Corollary25_i i
  simp only [recursiveAlphaCandidates, hneighbors] at hcor
  rw [b.coe_alphaValue, hcor]
  simp [i, s]

/-- Beli's Corollary 2.5(i) at the final `alpha`-index. -/
theorem alphaValue_last_eq_min_neighborPredecessor
    (b : GoodBONG q L (m + 3)) :
    let i : Fin (m + 2) := Fin.last (m + 1)
    let p : Fin (m + 2) := ⟨m, by omega⟩
    (b.alphaValue i : WithTop ℚ) =
      min (b.halfGapCandidate i)
        (min (b.leftDefectCandidate i i)
          (b.neighborAlphaCandidate i p)) := by
  dsimp only
  classical
  let i : Fin (m + 2) := Fin.last (m + 1)
  let p : Fin (m + 2) := ⟨m, by omega⟩
  have hneighbors : b.neighborAlphaCandidates i =
      {b.neighborAlphaCandidate i p} := by
    ext x
    simp only [neighborAlphaCandidates, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨j, hj | hj, rfl⟩
      · congr 1
        apply Fin.ext
        change j.val + 1 = m + 1 at hj
        dsimp only [p]
        omega
      · change m + 1 + 1 = j.val at hj
        have hjlt := j.isLt
        omega
    · rintro rfl
      refine ⟨p, Or.inl ?_, rfl⟩
      change p.val + 1 = m + 1
      dsimp only [p]
  have hcor := b.beli2009Corollary25_i i
  simp only [recursiveAlphaCandidates, hneighbors] at hcor
  rw [b.coe_alphaValue, hcor]
  simp [i, p]

end BONG.GoodBONG

end Bong
