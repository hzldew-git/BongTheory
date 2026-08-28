/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma63Right
import Bong.Bong.Beli2019Lemma79RightTailBetaProfile
import Bong.Bong.Beli2019Lemma79RightTailGapTwoTypeIInitial

/-!
# Beli (2019), Lemma 7.9(ii), case 8: the gap-two boundary alpha

The paper begins the gap-two calculation with `A_u = beta_u`.  The last
difference profile gives an unchanged suffix beginning at `u + 1`, so
Lemma 6.3 supplies this equality directly from condition 2.1(ii).  The same
suffix identifies the mixed half-gap candidate at `u` with the target's
self half-gap.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The one-based paper index `u` immediately after the zero-based last
difference coordinate. -/
def caseEightTypeIBoundaryIndex
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    (D : Lemma67TypeI a b) (hlast : D.profile.last < n + 1) :
    RepresentationIndex (n + 2) (n + 2) :=
  ⟨D.profile.last + 1, by omega, by omega, by omega⟩

@[simp]
theorem caseEightTypeIBoundaryIndex_val
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    (D : Lemma67TypeI a b) (hlast : D.profile.last < n + 1) :
    (caseEightTypeIBoundaryIndex D hlast).val = D.profile.last + 1 :=
  rfl

/-- At the gap-two boundary, Lemma 6.3 gives the displayed equality
`A_u = beta_u`. -/
theorem beli2019Lemma79_typeI_caseEight_boundaryAlpha_eq
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b)
    (hdefect : a.RepresentationDefectCondition b)
    (hlast : D.profile.last < n + 1) :
    a.representationAlphaValue b
        (caseEightTypeIBoundaryIndex D hlast) =
      b.alphaValue ⟨D.profile.last, hlast⟩ := by
  let boundary := caseEightTypeIBoundaryIndex D hlast
  have hsuffix : forall k, boundary.val <= k -> k < n + 2 ->
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply D.profile.lastDifference.after k
    · change D.profile.last + 1 <= k at hk
      omega
    · exact hkn
  have hvalue := a.beli2019Lemma63_sameRank_right_value
    b hdefect boundary hsuffix
  simpa only [boundary, caseEightTypeIBoundaryIndex,
    show D.profile.last + 1 - 1 = D.profile.last by omega] using hvalue

/-- The mixed half-gap candidate at `u` is the target self half-gap,
because the source and target orders already agree at `u + 1`. -/
theorem beli2019Lemma79_typeI_caseEight_boundaryHalfGap_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hlast : D.profile.last < n + 1) :
    a.representationHalfGap b
        (caseEightTypeIBoundaryIndex D hlast) =
      b.halfGapCandidate ⟨D.profile.last, hlast⟩ := by
  let next : Fin (n + 2) := ⟨D.profile.last + 1, by omega⟩
  have hnextEntry := D.profile.lastDifference.after
    (D.profile.last + 1) (by omega) (by omega)
  have hnextOrder : a.order next = b.order next := by
    rw [a.orderSequence_entryOrZero_eq_order next,
      b.orderSequence_entryOrZero_eq_order next] at hnextEntry
    exact hnextEntry
  rw [← b.coe_halfGapValue]
  unfold representationHalfGap halfGapValue orderGap
  change
    ((((a.order next - b.order ⟨D.profile.last, by omega⟩ : Int) :
        Rat) / 2 + (ramificationIndex K : Rat) : Rat) : WithTop Rat) =
      ((((b.order next - b.order ⟨D.profile.last, by omega⟩ : Int) :
        Rat) / 2 + (ramificationIndex K : Rat) : Rat) : WithTop Rat)
  rw [hnextOrder]

/-- The strict beta profile makes the boundary value strictly smaller than
the mixed half-gap candidate used in the definition of `A_u`. -/
theorem beli2019Lemma79_typeI_caseEight_boundaryAlpha_lt_halfGap
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hlast : D.profile.last < n + 1)
    {last : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b
      ⟨D.profile.last, hlast⟩ last)
    (hfirstLast : (⟨D.profile.last, hlast⟩ : Fin (n + 1)) <= last) :
    (b.alphaValue ⟨D.profile.last, hlast⟩ : WithTop Rat) <
      a.representationHalfGap b
        (caseEightTypeIBoundaryIndex D hlast) := by
  rw [beli2019Lemma79_typeI_caseEight_boundaryHalfGap_eq
    a b D hlast, ← b.coe_halfGapValue]
  exact_mod_cast H.alpha_lt_halfGap
    ⟨D.profile.last, hlast⟩ le_rfl hfirstLast

end BONG.GoodBONG

end Bong
