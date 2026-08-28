/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoOddComplete

/-!
# Beli (2019), Lemma 7.9(ii), case 8: the even comparison prefix

At an even index, the source self-prefix has the central defect.  That
central value is at most the final beta, whereas the strict case-8 branch
puts the source/comparison mixed prefix strictly above the beta.  Sharp
defect multiplication therefore identifies the comparison self-prefix with
the same central defect.  This justifies the "we may assume" reduction at
the start of the even calculation in lines 5902--5906 of the v2 paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- If a source self-prefix lies strictly below a mixed prefix, sharp
defect multiplication transports its value to the comparison self-prefix. -/
theorem truncatedPrefixDefect_comparisonSelf_eq_of_sourceSelf_lt_mixed
    (a : GoodBONG q L (n + 2)) (c : GoodBONG q N (n + 2))
    (epsilon : Kˣ) (length : Nat) (central : WithTop Rat)
    (hsource : a.truncatedPrefixDefect a epsilon 0 length = central)
    (hstrict : central < a.truncatedPrefixDefect c 1 length length) :
    c.truncatedPrefixDefect c epsilon 0 length = central := by
  have hsharp := a.truncatedPrefixDefect_mul_eq_left_of_lt_right
    a c epsilon 1 0 length length (by
      rw [hsource]
      exact hstrict)
  rw [mul_one,
    a.truncatedPrefixDefect_zero_left_eq_self c epsilon length,
    hsource] at hsharp
  exact hsharp

/-- In the strict even type-I gap-two branch, the comparison self-prefix
has the central defect required by the complete even beta estimate. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_even_comparisonPrefixDefect
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last + 1 <= i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.profile.last hlast) (caseEightLastAlphaIndex i))
    (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i))
    (hiEven : Even i.val)
    (hmixedStrict :
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) <
        a.truncatedPrefixDefect c 1 i.val i.val) :
    c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val =
      ((((b.order (Fin.mk D.profile.last hlast).castSucc -
          b.order (Fin.mk D.profile.last hlast).succ : Int) : Rat) +
        b.alphaValue (Fin.mk D.profile.last hlast) : Rat) : WithTop Rat) := by
  let first : Fin (n + 1) := Fin.mk D.profile.last hlast
  let last : Fin (n + 1) := caseEightLastAlphaIndex i
  have hfirstLast : first <= last := by
    change D.profile.last <= i.val - 1
    omega
  have hsource :=
    beli2019Lemma79_typeI_caseEight_gapTwo_sourcePrefixDefect_at_evenIndex
      a b D hfirst hgapTwo hlast horder hdefect i hafter H hstrictLast hiEven
  rcases beli2019Lemma79_typeI_caseEight_gapTwo_initialData
      a b D hfirst hgapTwo with ⟨I⟩
  have hindexParity : Even (i.val - D.profile.last) := by
    rcases hiEven with ⟨r, hr⟩
    rcases I.last_even with ⟨d, hd⟩
    refine ⟨r - d, ?_⟩
    omega
  have horderEntry := b.orderSequence.entryOrZero_le_of_evenGap
    D.profile.last i.val (by omega) i.lt_large hindexParity
  have hfirstEntry :=
    b.orderSequence_entryOrZero_eq_order first.castSucc
  change b.orderSequence.entryOrZero D.profile.last =
    b.order first.castSucc at hfirstEntry
  let current : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  have hlastSucc : last.succ = current := by
    apply Fin.ext
    simp only [last, current, caseEightLastAlphaIndex, Fin.val_succ]
    omega
  have hlastEntry := b.orderSequence_entryOrZero_eq_order current
  change b.orderSequence.entryOrZero i.val = b.order current at hlastEntry
  rw [<- hlastSucc] at hlastEntry
  rw [hfirstEntry, hlastEntry] at horderEntry
  have hcentralLe :
      ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
        b.alphaValue first : Rat) : WithTop Rat) <=
      (b.alphaValue last : WithTop Rat) := by
    rw [<- H.coe_centralCoefficient_eq last hfirstLast le_rfl]
    apply WithTop.coe_le_coe.mpr
    have horderQ : (b.order first.castSucc : Rat) <=
        (b.order last.succ : Rat) := by
      exact_mod_cast horderEntry
    push_cast
    linarith
  have hstrict :
      ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
        b.alphaValue first : Rat) : WithTop Rat) <
      a.truncatedPrefixDefect c 1 i.val i.val :=
    hcentralLe.trans_lt (by simpa only [last] using hmixedStrict)
  exact truncatedPrefixDefect_comparisonSelf_eq_of_sourceSelf_lt_mixed
    a c ((-1) ^ (i.val / 2)) i.val
      (((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
        b.alphaValue first : Rat) : WithTop Rat))
      (by simpa only [first] using hsource) hstrict

end BONG.GoodBONG

end Bong
