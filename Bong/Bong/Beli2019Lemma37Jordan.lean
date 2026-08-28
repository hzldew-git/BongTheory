/- Beli 2019, Lemma 3.7: Jordan-prefix approximation cases. -/
import Bong.Bong.Beli2019Lemma34OneBeforeModel

namespace Bong

open Dyadic Module
open BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

omit [DyadicDiscriminantClassLaws K] in
theorem not_rightApproximationTrigger_of_twoStepOrder_eq
    {n : Nat} (a : BONG.GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (hinternal : i.val + 1 < n + 1)
    (houter : a.order i.castSucc =
      a.order (⟨i.val + 1, hinternal⟩ : Fin (n + 1)).succ) :
    ¬a.rightApproximationTrigger i := by
  intro htrigger
  rcases htrigger with hterminal | ⟨hi, hsum⟩
  · omega
  · have hle := a.alpha_p6 i hi houter
    exact (not_lt_of_ge hle) hsum

omit [DyadicDiscriminantClassLaws K] in
theorem not_leftApproximationTrigger_of_twoStepOrder_eq
    {n : Nat} (a : BONG.GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (hpositive : 0 < i.val)
    (houter : a.order ⟨i.val - 1, by omega⟩ =
      a.order ⟨i.val + 1, by omega⟩) :
    ¬a.leftApproximationTrigger i := by
  intro htrigger
  rcases htrigger with hzero | ⟨hi, hsum⟩
  · omega
  · let j : Fin (n + 1) := ⟨i.val - 1, by omega⟩
    have hj : j.val + 1 < n + 1 := by
      dsimp only [j]
      omega
    have horders : a.order j.castSucc =
        a.order (⟨j.val + 1, hj⟩ : Fin (n + 1)).succ := by
      have hleft : j.castSucc =
          (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        rfl
      have hright : (⟨j.val + 1, hj⟩ : Fin (n + 1)).succ =
          (⟨i.val + 1, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        change (i.val - 1) + 1 + 1 = i.val + 1
        omega
      rw [hleft, hright]
      exact houter
    have hle := a.alpha_p6 j hj horders
    have hprevious : j =
        (⟨i.val - 1, by omega⟩ : Fin (n + 1)) := rfl
    have hcurrent : (⟨j.val + 1, hj⟩ : Fin (n + 1)) = i := by
      apply Fin.ext
      change (i.val - 1) + 1 = i.val
      omega
    have hle' : a.alphaValue ⟨i.val - 1, by omega⟩ +
        a.alphaValue i ≤ 2 * (ramificationIndex K : ℚ) := by
      rw [hcurrent] at hle
      rw [hprevious] at hle
      exact hle
    exact (not_lt_of_ge hle') hsum

end BONG.GoodBONG

namespace BONG.JordanOrderProfileWitness.PrescribedJordanComparison

variable {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
  {J : Lattice.JordanDecomposition q L (t + 1)}

set_option maxHeartbeats 0 in
/-- Beli (2019), Lemma 3.7(i). -/
theorem beli2019Lemma37_i
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : BONG.JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (z : Fin t) :
    a.IsSpaceApproximation (P.boundaryIndex z)
      (P.boundaryPrefixDiagonalUnits z) :=
  beli2019Lemma34_i a W hW hstrict P z

set_option maxHeartbeats 0 in
/-- Beli (2019), Lemma 3.7(ii).  The right clause is vacuous by P6 and
the asserted two-step order equality. -/
theorem beli2019Lemma37_ii
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : BONG.JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (z : Fin t) (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice
        (Lattice.JordanDecomposition.boundaryRightIndex z)) A)
    (hrank : 1 < (W.toJordan hstrict).componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex z))
    (hinternal : (P.boundaryOneAfterIndex z hrank).val + 1 < n + 1)
    (houter : a.order (P.boundaryOneAfterIndex z hrank).castSucc =
      a.order (⟨(P.boundaryOneAfterIndex z hrank).val + 1,
        hinternal⟩ : Fin (n + 1)).succ) :
    a.IsSpaceApproximation (P.boundaryOneAfterIndex z hrank)
      (P.boundaryOneAfterDiagonalUnits z A) := by
  have hleft := beli2019Lemma34_ii a W hW hstrict P z A hA hrank
  have hnot := a.not_rightApproximationTrigger_of_twoStepOrder_eq
    (P.boundaryOneAfterIndex z hrank) hinternal houter
  exact ⟨hleft, ⟨hleft.1, fun htrigger ↦ (hnot htrigger).elim⟩⟩

set_option maxHeartbeats 0 in
/-- Beli (2019), Lemma 3.7(iii).  The left clause is vacuous by P6 and
the asserted two-step order equality. -/
theorem beli2019Lemma37_iii
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : BONG.JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (z : Fin t) (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex z)) A)
    (M : BONG.JordanOrderProfileWitness.BoundaryOneBeforeModel P z A)
    (hrank : 1 < (W.toJordan hstrict).componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z))
    (hpositive : 0 < (P.boundaryOneBeforeIndex z hrank).val)
    (houter : a.order
        ⟨(P.boundaryOneBeforeIndex z hrank).val - 1, by omega⟩ =
      a.order
        ⟨(P.boundaryOneBeforeIndex z hrank).val + 1, by omega⟩) :
    a.IsSpaceApproximation (P.boundaryOneBeforeIndex z hrank)
      (M.approximationUnits hrank) := by
  have hright := beli2019Lemma34_iii a W hW hstrict P z A hA M hrank
  have hnot := a.not_leftApproximationTrigger_of_twoStepOrder_eq
    (P.boundaryOneBeforeIndex z hrank) hpositive houter
  exact ⟨⟨hright.1, fun htrigger ↦ (hnot htrigger).elim⟩, hright⟩

end BONG.JordanOrderProfileWitness.PrescribedJordanComparison

end Bong
