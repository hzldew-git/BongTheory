/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716TailDefect
import Bong.Bong.Beli2019Lemma716BoundaryAlpha
import Bong.Bong.Beli2019RepresentationSourceHalfGap

/-!
# Beli (2019), Lemma 7.16(ii): the boundary `i = s`

The representation invariant at `s` is unchanged by Lemma 7.15, although
the diagonal defect at the prefix of length `s` is not part of the unchanged
tail.  Beli bridges this last gap with the capped-defect domination principle,
using the original prefix as the middle term.  In type I the old and new
prefixes are isometric; in type II their determinant product has defect
`2e - 1`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- A pointwise form of the three-lattice domination argument.  If the new
representation invariant agrees with the old one and is also bounded by the
new--old prefix defect, then the old instance of condition 2.1(ii) transports
to the new BONG. -/
theorem representationDefectAt_of_middlePrefix
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (i : RepresentationIndex (n + 3) (n + 3))
    (hAlpha : a.representationAlpha c i = b.representationAlpha c i)
    (hsource : a.RepresentationDefectAt c i)
    (hmiddle : b.representationAlpha c i ≤
      b.truncatedPrefixDefect a 1 i.val i.val) :
    b.RepresentationDefectAt c i := by
  unfold RepresentationDefectAt at hsource ⊢
  have hsource' : b.representationAlpha c i ≤
      a.truncatedPrefixDefect c 1 i.val i.val := by
    rw [← hAlpha]
    exact hsource
  calc
    b.representationAlpha c i ≤
        min (b.truncatedPrefixDefect a 1 i.val i.val)
          (a.truncatedPrefixDefect c 1 i.val i.val) :=
      le_min hmiddle hsource'
    _ ≤ b.truncatedPrefixDefect c 1 i.val i.val := by
      simpa using b.truncatedPrefixDefect_domination a c 1 1
        i.val i.val i.val

variable [DyadicDiscriminantClassLaws K]
variable [Beli2006AlphaLaws.{u, v} K]
variable [Beli2009AlphaParityLaws.{u, v} K]

/-- Condition 2.1(ii) at `i = s` in the type-I branch. -/
theorem lemma716_typeI_s_representationDefectAt
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hI : Lemma714IsTypeI a R s)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (halphas : ∀ j, s ≤ j.val → a.alphaValue j = b.alphaValue j)
    (hprefix : ∀ (k : Nat), s ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk))
    (hsInterior : s < n + 3) :
    b.RepresentationDefectAt c
      { val := s
        pos := by have := D.two_le; omega
        lt_large := hsInterior
        le_small := hsInterior.le } := by
  let i : RepresentationIndex (n + 3) (n + 3) :=
    { val := s
      pos := by have := D.two_le; omega
      lt_large := hsInterior
      le_small := hsInterior.le }
  let boundary : Fin (n + 2) := ⟨s - 1, by omega⟩
  have hAlpha : a.representationAlpha c i = b.representationAlpha c i :=
    a.lemma716_tail_representationAlpha_eq b c s horders halphas
      (fun k hsk hk => hprefix k (by omega) hk) i le_rfl
  have hsource : a.RepresentationDefectAt c i :=
    ((a.representationDefectCondition_iff_forall_at c).mp
      hac.defectCondition) i
  have hprevious := a.lemma716_typeI_rightBoundary_order_eq b R s D
    hsecond hvalues
  have hnextSource := a.lemma714_typeI_nextOrder_ge R s hI hsInterior
  have hnext : R + 2 ≤ b.order ⟨s, hsInterior⟩ := by
    rw [← horders ⟨s, hsInterior⟩ le_rfl]
    exact hnextSource
  have hgap : 2 * (ramificationIndex K : Int) ≤ b.orderGap boundary := by
    unfold orderGap
    have hcast : boundary.castSucc =
        (⟨s - 1, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      rfl
    have hsucc : boundary.succ = (⟨s, hsInterior⟩ : Fin (n + 3)) := by
      apply Fin.ext
      change s - 1 + 1 = s
      have := D.two_le
      omega
    rw [hcast, hsucc, hprevious]
    omega
  have hattains : b.alphaValue boundary = b.halfGapValue boundary :=
    b.beli2009Lemma27_ii boundary hgap
  have hbValue :=
    b.representationAlphaValue_le_sourceAlpha_of_attainsHalfGap
      c horderBC i (by simpa only [i, boundary] using hattains)
  have hbTop : b.representationAlpha c i ≤
      (b.alphaValue boundary : WithTop ℚ) := by
    rw [← b.coe_representationAlphaValue c i]
    exact WithTop.coe_le_coe.mpr hbValue
  have hbCap : b.representationAlpha c i ≤ b.prefixAlphaCap s := by
    rw [b.prefixAlphaCap_of_internal (by have := D.two_le; omega)
      hsInterior]
    simpa only [boundary] using hbTop
  have haCap : b.representationAlpha c i ≤ a.prefixAlphaCap s := by
    unfold RepresentationDefectAt at hsource
    calc
      b.representationAlpha c i = a.representationAlpha c i := hAlpha.symm
      _ ≤ a.truncatedPrefixDefect c 1 i.val i.val := hsource
      _ ≤ a.prefixAlphaCap s := by
        simpa only [i] using
          a.truncatedPrefixDefect_le_leftCap c 1 i.val i.val
  have hraw : b.representationAlpha c i ≤ defectOrder (K := K)
      (1 * b.prefixProduct s * a.prefixProduct s) := by
    have heq := a.defectOrder_mixedPrefix_eq_of_prefix_isometric
      b a 1 s s D.le_rank (hprefix s le_rfl D.le_rank)
    have hsquare : IsSquare
        (1 * a.prefixProduct s * a.prefixProduct s) := by
      refine ⟨a.prefixProduct s, ?_⟩
      simp only [one_mul]
    rw [← heq, defectOrder_eq_top_of_isSquare hsquare]
    exact le_top
  have hmiddle : b.representationAlpha c i ≤
      b.truncatedPrefixDefect a 1 s s := by
    unfold truncatedPrefixDefect
    exact le_min hraw (le_min hbCap haCap)
  simpa only [i] using
    representationDefectAt_of_middlePrefix a b c i hAlpha hsource
      (by simpa only [i] using hmiddle)

/-- Condition 2.1(ii) at `i = s` in the type-II branch. -/
theorem lemma716_typeII_s_representationDefectAt
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hII : Lemma714IsTypeII a R s) (epsilon eta : Kˣ)
    (hepsilonUnit : IsValuationUnit K (epsilon : K))
    (hetaUnit : IsValuationUnit K (eta : K))
    (hetaDefect : defectOrder (K := K) eta =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) epsilon eta j)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (halphas : ∀ j, s ≤ j.val → a.alphaValue j = b.alphaValue j)
    (hprefix : ∀ (k : Nat), s + 1 ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk)) :
    b.RepresentationDefectAt c
      { val := s
        pos := by have := D.two_le; omega
        lt_large := Classical.choose hII
        le_small := (Classical.choose hII).le } := by
  have hsInterior : s < n + 3 := Classical.choose hII
  let i : RepresentationIndex (n + 3) (n + 3) :=
    { val := s
      pos := by have := D.two_le; omega
      lt_large := hsInterior
      le_small := hsInterior.le }
  let boundary : Fin (n + 2) := ⟨s - 1, by omega⟩
  have hAlpha : a.representationAlpha c i = b.representationAlpha c i :=
    a.lemma716_tail_representationAlpha_eq b c s horders halphas hprefix
      i le_rfl
  have hsource : a.RepresentationDefectAt c i :=
    ((a.representationDefectCondition_iff_forall_at c).mp
      hac.defectCondition) i
  have hboundaryAlpha :=
    a.lemma716_typeII_rightBoundary_alphaValue_eq_twoE_sub_one
      b R s D hII epsilon eta hepsilonUnit hetaUnit hvalues
  have hright := a.lemma716_typeII_rightBoundary_order_eq b R s D hII
    epsilon eta hepsilonUnit hetaUnit hvalues
  have htail := a.lemma716_typeII_tailBoundary_order_eq b R s D hII
    epsilon eta hepsilonUnit hetaUnit hvalues
  have hgap : b.orderGap boundary =
      2 * (ramificationIndex K : Int) - 2 := by
    unfold orderGap
    have hcast : boundary.castSucc =
        (⟨s - 1, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      rfl
    have hsucc : boundary.succ =
        (⟨s, hsInterior⟩ : Fin (n + 3)) := by
      apply Fin.ext
      change s - 1 + 1 = s
      have := D.two_le
      omega
    rw [hcast, hsucc, hright, htail]
    ring
  have hhalf : b.halfGapValue boundary =
      2 * (ramificationIndex K : ℚ) - 1 := by
    unfold halfGapValue
    rw [hgap]
    push_cast
    ring
  have hattains : b.alphaValue boundary = b.halfGapValue boundary := by
    rw [hboundaryAlpha, hhalf]
  have hbValue :=
    b.representationAlphaValue_le_sourceAlpha_of_attainsHalfGap
      c horderBC i (by simpa only [i, boundary] using hattains)
  have hbTop : b.representationAlpha c i ≤
      (b.alphaValue boundary : WithTop ℚ) := by
    rw [← b.coe_representationAlphaValue c i]
    exact WithTop.coe_le_coe.mpr hbValue
  have hbCap : b.representationAlpha c i ≤ b.prefixAlphaCap s := by
    rw [b.prefixAlphaCap_of_internal (by have := D.two_le; omega)
      hsInterior]
    simpa only [boundary] using hbTop
  have haCap : b.representationAlpha c i ≤ a.prefixAlphaCap s := by
    unfold RepresentationDefectAt at hsource
    calc
      b.representationAlpha c i = a.representationAlpha c i := hAlpha.symm
      _ ≤ a.truncatedPrefixDefect c 1 i.val i.val := hsource
      _ ≤ a.prefixAlphaCap s := by
        simpa only [i] using
          a.truncatedPrefixDefect_le_leftCap c 1 i.val i.val
  have hvalue : b.valueUnit ⟨s, hsInterior⟩ =
      a.valueUnit ⟨s, hsInterior⟩ * eta := by
    rw [hvalues]
    simpa using lemma714TypeIITargetValues_two a s D.two_le
      hsInterior epsilon eta
  have hsSucc : s + 1 ≤ n + 3 := by omega
  rcases a.exists_prefixProduct_eq_mul_square_of_prefix_isometric b
      (s + 1) hsSucc (hprefix (s + 1) le_rfl hsSucc) with ⟨p, hp⟩
  unfold GoodBONG.prefixProduct at hp
  change b.toBONG.valueUnit ⟨s, hsInterior⟩ =
      a.toBONG.valueUnit ⟨s, hsInterior⟩ * eta at hvalue
  rw [a.toBONG.prefixProduct_succ s hsInterior,
    b.toBONG.prefixProduct_succ s hsInterior, hvalue] at hp
  have hp' : a.prefixProduct s =
      b.prefixProduct s * eta * p ^ 2 := by
    apply mul_left_cancel (a := a.valueUnit ⟨s, hsInterior⟩)
    calc
      a.valueUnit ⟨s, hsInterior⟩ * a.prefixProduct s =
          a.prefixProduct s * a.valueUnit ⟨s, hsInterior⟩ := mul_comm _ _
      _ = b.prefixProduct s *
          (a.valueUnit ⟨s, hsInterior⟩ * eta) * p ^ 2 := hp
      _ = a.valueUnit ⟨s, hsInterior⟩ *
          (b.prefixProduct s * eta * p ^ 2) := by ac_rfl
  have hproduct : 1 * b.prefixProduct s * a.prefixProduct s =
      eta * (b.prefixProduct s * p) ^ 2 := by
    rw [one_mul, hp']
    simp only [pow_two]
    ac_rfl
  have hthreshold : b.representationAlpha c i ≤
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) := by
    calc
      b.representationAlpha c i ≤ b.prefixAlphaCap s := hbCap
      _ = (b.alphaValue boundary : WithTop ℚ) := by
        rw [b.prefixAlphaCap_of_internal (by have := D.two_le; omega)
          hsInterior]
      _ = (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) := by
        rw [hboundaryAlpha]
  have hraw : b.representationAlpha c i ≤ defectOrder (K := K)
      (1 * b.prefixProduct s * a.prefixProduct s) := by
    rw [hproduct, defectOrder_mul_square, hetaDefect]
    exact hthreshold
  have hmiddle : b.representationAlpha c i ≤
      b.truncatedPrefixDefect a 1 s s := by
    unfold truncatedPrefixDefect
    exact le_min hraw (le_min hbCap haCap)
  simpa only [i] using
    representationDefectAt_of_middlePrefix a b c i hAlpha hsource
      (by simpa only [i] using hmiddle)

end BONG.GoodBONG

end Bong
