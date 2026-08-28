/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourCentralBoth
import Bong.Bong.Beli2019CappedDefectTriangle
import Bong.Bong.Beli2019Lemma216Arithmetic
import Bong.Bong.Beli2019Lemma29ReducedPrimeRight
import Bong.Bong.Beli2019Lemma93TailCentral
import Bong.Bong.Beli2019SectionFourCentralEssential

/-!
# Beli (2019), Section 4: the central comparison alternatives

This file records the three alternatives of Lemma 4.3 and its reverse-dual
Corollary 4.4 in the paper's zero-based Lean indexing.  It also proves the
two strict arithmetic exclusions used in the asymmetric cases of the proof
of Theorem 2.1(iii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  {L M N : Lattice K V} {n : Nat}

/-- The three conclusions of Beli (2019), Lemma 4.3.  In the paper these
are denoted

`S_i + A'_i ≥ T_i + C_i`,
`-R_(i+1) + A'_i ≥ -S_i + B_(i-1)`, and
`R_(i+1) < S_(i-1)`.
-/
def SectionFourForwardComparison
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1)) : Prop :=
  (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
        WithTop ℚ) + a.representationAlpha c (i.current i.lt_large.le) ≤
      (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
        WithTop ℚ) +
        a.representationAlphaPrime b (i.current i.lt_large.le) ∨
    ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) : ℚ) :
          WithTop ℚ) + b.representationAlpha c i.previous ≤
      ((((-a.order ⟨i.val, i.lt_large⟩ : Int) : Int) : ℚ) : WithTop ℚ) +
        a.representationAlphaPrime b (i.current i.lt_large.le) ∨
    a.order ⟨i.val, i.lt_large⟩ <
      b.order ⟨i.val - 2, by have := i.lt_large; omega⟩

/-- The three reverse-dual conclusions of Beli (2019), Corollary 4.4. -/
def SectionFourBackwardComparison
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1)) : Prop :=
  ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) : ℚ) :
          WithTop ℚ) + a.representationAlpha c i.previous ≤
      ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) : ℚ) :
          WithTop ℚ) + b.representationAlphaPrime c i.previous ∨
    (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + a.representationAlpha b (i.current i.lt_large.le) ≤
      (((c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + b.representationAlphaPrime c i.previous ∨
    b.order ⟨i.val, i.lt_large⟩ <
      c.order ⟨i.val - 2, by have := i.lt_large; omega⟩

/-! ## Uniform finite upper bounds at the active central boundary -/

/-- The finite average appearing at the end of Lemmas 4.3 and 4.5. -/
noncomputable def centralLeftAverage
    (a : GoodBONG q L (n + 1)) (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiNext : i.val + 1 < n + 1) : WithTop ℚ :=
  (( ((a.order ⟨i.val, i.lt_large⟩ : ℚ) +
        (a.order ⟨i.val + 1, hiNext⟩ : ℚ)) / 2 -
      (c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : ℚ) +
      (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)

/-- The secondary lower expression in the last branch of Lemma 4.3. -/
noncomputable def centralSecondaryLower
    (a : GoodBONG q L (n + 1)) (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiNext : i.val + 1 < n + 1) : WithTop ℚ :=
  (((a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hiNext⟩ -
        a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ -
        c.order ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : Int) : ℚ) : WithTop ℚ) +
    a.representationAlpha c i.previous

/-- The paper repeatedly uses

`C_i ≤ (R_(i+1) + R_(i+2))/2 - T_i + e`.

It is just `C_i ≤ C'_i`, followed by the primary left half-gap
candidate in Lemma 2.14.  Keeping this equality in a named theorem avoids
re-expanding the half-gap in every branch of Lemmas 4.3 and 4.5. -/
theorem centralCurrentAlpha_le_leftAverage
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiNext : i.val + 1 < n + 1) :
    a.representationAlpha c (i.current i.lt_large.le) ≤
      a.centralLeftAverage c i hiNext := by
  calc
    a.representationAlpha c (i.current i.lt_large.le) ≤
        a.representationAlphaPrime c (i.current i.lt_large.le) :=
      a.representationAlpha_le_prime c (i.current i.lt_large.le)
    _ ≤
        (((a.order ⟨i.val, i.lt_large⟩ -
            c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
          (a.halfGapValue ⟨i.val, by omega⟩ : WithTop ℚ) :=
      a.representationAlphaPrime_le_primaryLeftHalfGap
        c (i.current i.lt_large.le) hiNext
    _ = _ := by
      unfold centralLeftAverage
      norm_cast
      unfold halfGapValue orderGap
      have hsucc : (⟨i.val, by omega⟩ : Fin n).succ =
          (⟨i.val + 1, hiNext⟩ : Fin (n + 1)) := by
        apply Fin.ext
        rfl
      have hcast : (⟨i.val, by omega⟩ : Fin n).castSucc =
          (⟨i.val, i.lt_large⟩ : Fin (n + 1)) := by
        apply Fin.ext
        rfl
      rw [hsucc, hcast]
      simp only [Rat.divInt_eq_div]
      push_cast
      ring

/-- The order-theoretic core of the last contradiction in Lemma 4.3.
The first two hypotheses are the central defect trigger and the secondary
candidate lower bound; the last hypothesis is the universal average upper
bound above. -/
theorem sectionFourForwardSecondaryContradiction
    (a : GoodBONG q L (n + 1)) (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiNext : i.val + 1 < n + 1)
    (htrigger : a.centralAlphaTrigger c i)
    (hlower : a.centralSecondaryLower c i hiNext ≤
      a.representationAlpha c (i.current i.lt_large.le))
    (hupper : a.representationAlpha c (i.current i.lt_large.le) ≤
      a.centralLeftAverage c i hiNext) : False := by
  have hsum := htrigger.2
  unfold centralAdjustedAlpha at hsum
  rw [dif_pos (show i.val ≤ n + 1 from i.lt_large.le)] at hsum
  unfold centralSecondaryLower at hlower
  unfold centralLeftAverage at hupper
  rw [← a.coe_representationAlphaValue c i.previous,
    ← a.coe_representationAlphaValue c (i.current i.lt_large.le)] at hlower
  rw [← a.coe_representationAlphaValue c (i.current i.lt_large.le)] at hupper
  norm_cast at hsum hlower hupper
  simp only [Rat.divInt_eq_div] at hupper
  norm_num [div_eq_mul_inv] at hupper
  push_cast at hsum hlower hupper
  linarith

/-! ## The primary branch of Lemma 4.3 -/

/-- If the first comparison in Lemma 4.3 fails and `A'_i` is its primary
candidate, the strict defect triangle and condition 2.1(ii) for `(b,c)`
give the second comparison.  This is the first branch after the displayed
Lemma 2.7(i) normal form in the paper. -/
theorem sectionFourForwardSecond_of_primary
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hlocal : SectionFourLocalConditions a b c)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hprimary :
      a.representationAlphaPrime b (i.current i.lt_large.le) =
        a.representationPrimaryDefect b (i.current i.lt_large.le))
    (hnotFirst :
      ¬((((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.representationAlpha c (i.current i.lt_large.le) ≤
          (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.representationAlphaPrime b (i.current i.lt_large.le))) :
    ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) : ℚ) :
          WithTop ℚ) + b.representationAlpha c i.previous ≤
      ((((-a.order ⟨i.val, i.lt_large⟩ : Int) : Int) : ℚ) : WithTop ℚ) +
        a.representationAlphaPrime b (i.current i.lt_large.le) := by
  let sourceDefect :=
    a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1)
  let targetDefect :=
    a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1)
  let commonShift : ℚ := (a.order ⟨i.val, i.lt_large⟩ : Int)
  have hstrict := lt_of_not_ge hnotFirst
  have htarget := a.representationAlpha_le_primary
    c (i.current i.lt_large.le)
  have hsourceForm :
      (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlphaPrime b (i.current i.lt_large.le) =
        (commonShift : WithTop ℚ) + sourceDefect := by
    rw [hprimary]
    unfold representationPrimaryDefect
      CentralRepresentationIndex.current
    dsimp only [commonShift, sourceDefect]
    rw [← add_assoc]
    congr 1
    norm_cast
    ring
  have htargetForm :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationPrimaryDefect c (i.current i.lt_large.le) =
        (commonShift : WithTop ℚ) + targetDefect := by
    unfold representationPrimaryDefect
      CentralRepresentationIndex.current
    dsimp only [commonShift, targetDefect]
    rw [← add_assoc]
    congr 1
    norm_cast
    ring
  have hdefect : sourceDefect < targetDefect := by
    apply (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp
    calc
      (commonShift : WithTop ℚ) + sourceDefect =
          (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.representationAlphaPrime b
              (i.current i.lt_large.le) := hsourceForm.symm
      _ < (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.representationAlpha c
              (i.current i.lt_large.le) := hstrict
      _ ≤ (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.representationPrimaryDefect c
              (i.current i.lt_large.le) := add_le_add_right htarget _
      _ = (commonShift : WithTop ℚ) + targetDefect := htargetForm
  have htriangle : sourceDefect =
      b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1) := by
    exact a.truncatedPrefixDefect_neg_eq_pos_of_lt_neg b c
      (i.val + 1) (i.val - 1) (i.val - 1) (by
        simpa only [sourceDefect, targetDefect] using hdefect)
  have hcondition := hlocal.hbcDefect i.previous
  have hmiddle : b.representationAlpha c i.previous ≤ sourceDefect := by
    rw [b.coe_representationAlphaValue c i.previous] at hcondition
    rw [htriangle]
    simpa only [CentralRepresentationIndex.previous] using hcondition
  calc
    ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) : ℚ) :
          WithTop ℚ) + b.representationAlpha c i.previous ≤
        ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) : ℚ) :
          WithTop ℚ) + sourceDefect := add_le_add_right hmiddle _
    _ = ((((-a.order ⟨i.val, i.lt_large⟩ : Int) : Int) : ℚ) : WithTop ℚ) +
          a.representationAlphaPrime b (i.current i.lt_large.le) := by
      rw [hprimary]
      unfold representationPrimaryDefect
        CentralRepresentationIndex.current
      dsimp only [sourceDefect]
      have hcoeff :
          ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) : ℚ) :
              WithTop ℚ) =
            ((((-a.order ⟨i.val, i.lt_large⟩ : Int) : Int) : ℚ) :
                WithTop ℚ) +
              (((a.order ⟨i.val, i.lt_large⟩ -
                b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
                  WithTop ℚ) := by
        norm_cast
        ring
      rw [hcoeff, add_assoc]

/-- In the secondary branch, a previous-bound comparison converts failure
of the first alternative into the lower bound used in the final average
contradiction.  In paper notation this is

`R_(i+1)+R_(i+2)-R_i-T_i+C_(i-1) < C_i`.
-/
theorem centralSecondaryLower_le_current_of_secondary
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiNext : i.val + 1 < n + 1)
    (hprevious : a.representationAlpha c i.previous ≤
      a.representationAlpha b i.previous)
    (hsecondary :
      a.representationAlphaPrime b (i.current i.lt_large.le) =
        a.representationSecondaryPreviousDefect b
          (i.current i.lt_large.le) ⟨i.one_lt, hiNext⟩)
    (hnotFirst :
      ¬((((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.representationAlpha c (i.current i.lt_large.le) ≤
          (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.representationAlphaPrime b (i.current i.lt_large.le))) :
    a.centralSecondaryLower c i hiNext ≤
      a.representationAlpha c (i.current i.lt_large.le) := by
  let base : ℚ :=
    (a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ -
      a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : Int)
  have hstrict := lt_of_not_ge hnotFirst
  have hpreviousPrimary := hprevious.trans
    (a.representationAlpha_le_primary b i.previous)
  have hlowerForm :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + a.centralSecondaryLower c i hiNext =
        (base : WithTop ℚ) + a.representationAlpha c i.previous := by
    unfold centralSecondaryLower
    dsimp only [base]
    rw [← add_assoc]
    congr 1
    norm_cast
    ring
  have hsourceForm :
      (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlphaPrime b (i.current i.lt_large.le) =
        (base : WithTop ℚ) +
          a.representationPrimaryDefect b i.previous := by
    rw [hsecondary, a.representationPrimaryDefect_previous_eq b i]
    unfold representationSecondaryPreviousDefect centralPreviousDefect
      CentralRepresentationIndex.current
    dsimp only [base]
    rw [← add_assoc, ← add_assoc]
    congr 1
    norm_cast
    ring
  have hshifted :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + a.centralSecondaryLower c i hiNext <
        (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) := by
    calc
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + a.centralSecondaryLower c i hiNext =
          (base : WithTop ℚ) +
            a.representationAlpha c i.previous := hlowerForm
      _ ≤ (base : WithTop ℚ) +
            a.representationAlpha b i.previous := add_le_add_right hprevious _
      _ ≤ (base : WithTop ℚ) +
            a.representationPrimaryDefect b i.previous :=
          add_le_add_right (a.representationAlpha_le_primary b i.previous) _
      _ = (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.representationAlphaPrime b
              (i.current i.lt_large.le) := hsourceForm.symm
      _ < (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.representationAlpha c
              (i.current i.lt_large.le) := hstrict
  exact le_of_lt ((WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hshifted)

/-! ## The high-pair branch of Lemma 4.3 -/

/-- Lemma 4.3 in the branch
`R_(i+1)+R_(i+2) > S_(i-1)+S_i`, specialized to the equality
`A_i = A'_i` in which Section 4 actually invokes it.  If neither the first
nor the third alternative holds, Lemma 2.7(i) leaves a primary and a
secondary candidate.  The primary candidate gives the second alternative;
the secondary candidate is either reduced to the primary one by Lemma 2.9,
or contradicts the central trigger via Lemma 4.2(i). -/
theorem sectionFourForwardComparison_of_current_eq_prime_highPair
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hlocal : SectionFourLocalConditions a b c)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiNext : i.val + 1 < n + 1)
    (htrigger : a.centralAlphaTrigger c i)
    (heqAB : a.representationAlpha b (i.current i.lt_large.le) =
      a.representationAlphaPrime b (i.current i.lt_large.le))
    (hpair :
      b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ +
          b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ <
        a.order ⟨i.val, i.lt_large⟩ +
          a.order ⟨i.val + 1, hiNext⟩) :
    SectionFourForwardComparison a b c i := by
  by_cases hfirst :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) ≤
        (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlphaPrime b (i.current i.lt_large.le)
  · exact Or.inl hfirst
  by_cases hthird : a.order ⟨i.val, i.lt_large⟩ <
      b.order ⟨i.val - 2, by have := i.lt_large; omega⟩
  · exact Or.inr (Or.inr hthird)
  apply Or.inr
  apply Or.inl
  let current : RepresentationIndex (n + 1) (n + 1) :=
    i.current i.lt_large.le
  let hinterior : 1 < current.val ∧ current.val + 1 < n + 1 := by
    dsimp only [current, CentralRepresentationIndex.current]
    exact ⟨i.one_lt, hiNext⟩
  have hleft : b.order ⟨current.val - 2, by
        have := current.le_small
        omega⟩ ≤ a.order ⟨current.val, current.lt_large⟩ := by
    simpa only [current, CentralRepresentationIndex.current] using
      le_of_not_gt hthird
  have hnormal := a.representationAlphaPrime_eq_min_primary_previous
    b current hinterior hleft
  rcases min_choice (a.representationPrimaryDefect b current)
      (a.representationSecondaryPreviousDefect b current hinterior) with
    hprimaryChoice | hsecondaryChoice
  · apply a.sectionFourForwardSecond_of_primary b c hlocal i
      (by simpa only [current] using hnormal.trans hprimaryChoice) hfirst
  · have hsecondary :
        a.representationAlphaPrime b (i.current i.lt_large.le) =
          a.representationSecondaryPreviousDefect b
            (i.current i.lt_large.le) ⟨i.one_lt, hiNext⟩ := by
      simpa only [current, hinterior] using hnormal.trans hsecondaryChoice
    by_cases hright :
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ ≤
          a.order ⟨i.val + 1, hiNext⟩
    · have hcondition := hlocal.habDefect (i.current i.lt_large.le)
      rw [a.coe_representationAlphaValue b (i.current i.lt_large.le),
        heqAB] at hcondition
      have hcomparison :
          a.representationAlphaPrime b current ≤
            a.truncatedPrefixDefect b 1 current.val current.val := by
        simpa only [current, CentralRepresentationIndex.current] using hcondition
      have hright' : b.order ⟨current.val - 1, by
            have := current.le_small
            omega⟩ ≤
          a.order ⟨current.val + 1, hinterior.2⟩ := by
        simpa only [current, hinterior, CentralRepresentationIndex.current]
          using hright
      have hshift : 0 <
          a.order ⟨current.val, current.lt_large⟩ +
              a.order ⟨current.val + 1, hinterior.2⟩ -
            b.order ⟨current.val - 2, by
              have := current.le_small
              omega⟩ -
            b.order ⟨current.val - 1, by
              have := current.le_small
              omega⟩ := by
        dsimp only [current, hinterior, CentralRepresentationIndex.current]
        omega
      have hprimeReduced :=
        a.representationAlphaPrime_eq_primeReduced_of_rightCross
          b current hinterior current.lt_large hright' hshift hcomparison
      have hreducedPrimary :=
        a.representationAlphaPrimeReduced_eq_primary_of_crosses
          b current hinterior current.lt_large hleft hright'
      have hprimary :
          a.representationAlphaPrime b (i.current i.lt_large.le) =
            a.representationPrimaryDefect b
              (i.current i.lt_large.le) := by
        simpa only [current] using hprimeReduced.trans hreducedPrimary
      exact a.sectionFourForwardSecond_of_primary b c hlocal i hprimary hfirst
    · have hrightStrict :
          a.order ⟨i.val + 1, hiNext⟩ <
            b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ :=
        lt_of_not_ge hright
      have hessential :=
        a.isEssentialFor_of_centralAlphaTrigger c i htrigger
      have hdirect : a.KeyLemmaLeftDirectTrigger b c
          (nextEssentialIndex i.previous) := by
        unfold KeyLemmaLeftDirectTrigger
        intro hiTwoDirect hiNextDirect
        have hiEssentialTwo :
            1 < (⟨i.val - 1, by omega⟩ : Fin (n + 1)).val := by
          simpa only [nextEssentialIndex,
            CentralRepresentationIndex.previous] using hiTwoDirect
        have hiEssentialNext :
            (⟨i.val - 1, by omega⟩ : Fin (n + 1)).val + 2 < n + 1 := by
          change i.val - 1 + 2 < n + 1
          omega
        have hraw := hessential.2 hiEssentialTwo hiEssentialNext
        have hessentialPair :
            c.order ⟨i.val - 3, by omega⟩ +
                c.order ⟨i.val - 2, by omega⟩ <
              a.order ⟨i.val, i.lt_large⟩ +
                a.order ⟨i.val + 1, hiNext⟩ := by
          simp only [orderSequence_at] at hraw
          have hcLeft :
              (⟨i.val - 1 - 2, by omega⟩ : Fin (n + 1)) =
                ⟨i.val - 3, by omega⟩ := by
            apply Fin.ext
            change i.val - 1 - 2 = i.val - 3
            omega
          have hcRight :
              (⟨i.val - 1 - 1, by omega⟩ : Fin (n + 1)) =
                ⟨i.val - 2, by omega⟩ := by
            apply Fin.ext
            change i.val - 1 - 1 = i.val - 2
            omega
          have haCurrent :
              (⟨i.val - 1 + 1, by omega⟩ : Fin (n + 1)) =
                ⟨i.val, i.lt_large⟩ := by
            exact Fin.ext (Nat.sub_add_cancel i.one_lt.le)
          have haNext :
              (⟨i.val - 1 + 2, hiEssentialNext⟩ : Fin (n + 1)) =
                ⟨i.val + 1, hiNext⟩ := by
            have hval : i.val - 1 + 2 = i.val + 1 :=
              congrArg (fun t : Nat => t + 1)
                (Nat.sub_add_cancel i.one_lt.le)
            exact Fin.ext hval
          simpa only [hcLeft, hcRight, haCurrent, haNext] using hraw
        have hout :
            c.order ⟨i.val - 3, by omega⟩ +
                c.order ⟨i.val - 2, by omega⟩ <
              a.order ⟨i.val, i.lt_large⟩ +
                b.order ⟨i.val - 1, by omega⟩ := by
          omega
        have hcLeft :
            (⟨(nextEssentialIndex i.previous).val - 2, by omega⟩ :
                Fin (n + 1)) = ⟨i.val - 3, by omega⟩ := by
          apply Fin.ext
          change i.val - 1 - 2 = i.val - 3
          omega
        have hcRight :
            (⟨(nextEssentialIndex i.previous).val - 1, by omega⟩ :
                Fin (n + 1)) = ⟨i.val - 2, by omega⟩ := by
          apply Fin.ext
          change i.val - 1 - 1 = i.val - 2
          omega
        have haCurrent :
            (⟨(nextEssentialIndex i.previous).val + 1, hiNextDirect⟩ :
                Fin (n + 1)) = ⟨i.val, i.lt_large⟩ := by
          exact Fin.ext (Nat.sub_add_cancel i.one_lt.le)
        have hbPrevious :
            (⟨(nextEssentialIndex i.previous).val, by omega⟩ :
                Fin (n + 1)) = ⟨i.val - 1, by omega⟩ := by
          apply Fin.ext
          rfl
        simpa only [hcLeft, hcRight, haCurrent, hbPrevious] using hout
      have hprevious :=
        ((a.sectionFourPreviousBounds_of_centralAlphaTrigger
          b c hlocal i htrigger).1 hdirect).1
      have hlower :=
        a.centralSecondaryLower_le_current_of_secondary
          b c i hiNext hprevious hsecondary hfirst
      exact False.elim (a.sectionFourForwardSecondaryContradiction c i
        hiNext htrigger hlower
          (a.centralCurrentAlpha_le_leftAverage c i hiNext))

/-- The endpoint `i = n - 1` part of Lemma 4.3.  Definition 5 has no
secondary candidate there, so failure of the first and third alternatives
immediately enters the primary branch. -/
theorem sectionFourForwardComparison_of_terminal
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hlocal : SectionFourLocalConditions a b c)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hterminal : ¬ i.val + 1 < n + 1) :
    SectionFourForwardComparison a b c i := by
  by_cases hfirst :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) ≤
        (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlphaPrime b (i.current i.lt_large.le)
  · exact Or.inl hfirst
  by_cases hthird : a.order ⟨i.val, i.lt_large⟩ <
      b.order ⟨i.val - 2, by have := i.lt_large; omega⟩
  · exact Or.inr (Or.inr hthird)
  apply Or.inr
  apply Or.inl
  have hnotInterior :
      ¬(1 < (i.current i.lt_large.le).val ∧
        (i.current i.lt_large.le).val + 1 < n + 1) := by
    intro h
    exact hterminal (by
      simpa only [CentralRepresentationIndex.current] using h.2)
  have hprimary := a.representationAlphaPrime_eq_primary_of_not_interior
    b (i.current i.lt_large.le) hnotInterior
  exact a.sectionFourForwardSecond_of_primary b c hlocal i hprimary hfirst

/-- In the asymmetric case `A_i = A'_i` and `B_(i-1) < B'_(i-1)`,
the second alternative of Lemma 4.3 contradicts the outer strict order.
This is the displayed half-gap calculation in case (b) of the paper. -/
theorem sectionFourForwardSecond_impossible
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hcross : c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ <
      a.order ⟨i.val, i.lt_large⟩)
    (heqAB : a.representationAlpha b (i.current i.lt_large.le) =
      a.representationAlphaPrime b (i.current i.lt_large.le))
    (hneBC : b.representationAlpha c i.previous ≠
      b.representationAlphaPrime c i.previous)
    (hsecond :
      ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) : ℚ) :
            WithTop ℚ) + b.representationAlpha c i.previous ≤
        ((((-a.order ⟨i.val, i.lt_large⟩ : Int) : Int) : ℚ) : WithTop ℚ) +
          a.representationAlphaPrime b (i.current i.lt_large.le)) : False := by
  have hABle :=
    a.representationAlpha_le_halfGap b (i.current i.lt_large.le)
  have hBCeq :=
    (b.representationAlpha_eq_halfGap_and_lt_prime_of_ne
      c i.previous hneBC).1
  rw [← heqAB,
    ← a.coe_representationAlphaValue b (i.current i.lt_large.le),
    ← b.coe_representationAlphaValue c i.previous] at hsecond
  rw [← a.coe_representationAlphaValue b (i.current i.lt_large.le)] at hABle
  rw [← b.coe_representationAlphaValue c i.previous] at hBCeq
  unfold representationHalfGap at hABle hBCeq
  norm_cast at hsecond hABle hBCeq
  simp only [Rat.divInt_eq_div] at hABle hBCeq
  simp only [CentralRepresentationIndex.current,
    CentralRepresentationIndex.previous, Nat.sub_sub,
    one_add_one_eq_two] at hsecond hABle hBCeq
  push_cast at hsecond hABle hBCeq
  have hcrossQ :
      (c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : ℚ) <
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
    exact_mod_cast hcross
  linarith

/-- The reverse-dual arithmetic exclusion used in case (c): if
`A_i < A'_i` and `B_(i-1) = B'_(i-1)`, the middle alternative of
Corollary 4.4 is incompatible with `R_(i+1) > T_(i-1)`. -/
theorem sectionFourBackwardSecond_impossible
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hcross : c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ <
      a.order ⟨i.val, i.lt_large⟩)
    (hneAB : a.representationAlpha b (i.current i.lt_large.le) ≠
      a.representationAlphaPrime b (i.current i.lt_large.le))
    (heqBC : b.representationAlpha c i.previous =
      b.representationAlphaPrime c i.previous)
    (hsecond :
      (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + a.representationAlpha b (i.current i.lt_large.le) ≤
        (((c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + b.representationAlphaPrime c i.previous) : False := by
  have hABeq :=
    (a.representationAlpha_eq_halfGap_and_lt_prime_of_ne
      b (i.current i.lt_large.le) hneAB).1
  have hBCle := b.representationAlpha_le_halfGap c i.previous
  rw [← heqBC,
    ← a.coe_representationAlphaValue b (i.current i.lt_large.le),
    ← b.coe_representationAlphaValue c i.previous] at hsecond
  rw [← a.coe_representationAlphaValue b (i.current i.lt_large.le)] at hABeq
  rw [← b.coe_representationAlphaValue c i.previous] at hBCle
  unfold representationHalfGap at hABeq hBCle
  norm_cast at hsecond hABeq hBCle
  simp only [Rat.divInt_eq_div] at hABeq hBCle
  simp only [CentralRepresentationIndex.current,
    CentralRepresentationIndex.previous, Nat.sub_sub,
    one_add_one_eq_two] at hsecond hABeq hBCle
  push_cast at hsecond hABeq hBCle
  have hcrossQ :
      (c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : ℚ) <
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
    exact_mod_cast hcross
  linarith

/-- If `B_(i-1) < B'_(i-1)`, condition 2.1(i) for `(b,c)` forces
`S_(i-1) \le T_(i-1)`.  For `i > 2` this is Lemma 1.6(iii), using the
strict order consequence `S_i > T_(i-2)` of Lemma 2.14; at `i = 2` it
is the first-entry clause of the same order condition. -/
theorem middlePrevious_le_sourcePrevious_of_previous_alpha_ne_prime
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 1)) (c : GoodBONG q N (n + 1))
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hneBC : b.representationAlpha c i.previous ≠
      b.representationAlphaPrime c i.previous) :
    b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ ≤
      c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
  by_cases hi : i.val = 2
  · have hseq :=
      (b.representationOrderCondition_iff c le_rfl).mp hbc.orderCondition
    have hfirst := hseq.first_le (by omega : 0 < n + 1)
    simpa only [orderSequence_at, hi, Nat.reduceSub] using hfirst
  · have hhalf :=
      (b.representationAlpha_eq_halfGap_and_lt_prime_of_ne
        c i.previous hneBC).2
    have hcrossRaw :=
      b.sourceCurrent_gt_targetPrevious_of_halfGap_lt_alphaPrime
        c i.previous (by
          change 1 < i.val - 1
          have := i.one_lt
          omega) hhalf
    let j : CentralRepresentationIndex (n + 1) (n + 1) :=
      { val := i.val - 1
        one_lt := by
          have := i.one_lt
          omega
        lt_large := by
          have := i.lt_large
          omega
        le_small_succ := by
          have := i.le_small_succ
          omega }
    have hjSmall : j.val ≤ n + 1 := by
      dsimp only [j]
      have := i.lt_large
      omega
    have hcross :
        c.order ⟨j.val - 2, by
          have := j.le_small_succ
          omega⟩ ≤
          b.order ⟨j.val, j.lt_large⟩ := by
      apply le_of_lt
      simpa only [j, CentralRepresentationIndex.previous, Nat.sub_sub,
        one_add_one_eq_two] using hcrossRaw
    have horder := b.centralPreviousOrder_le_targetCurrent
      c le_rfl hbc.orderCondition j hjSmall hcross
    simpa only [j, Nat.sub_sub, one_add_one_eq_two] using horder

/-- In case (b) of the paper, the third alternative of Lemma 4.3 is
impossible: `S_(i-1) \le T_(i-1) < R_(i+1)`. -/
theorem sectionFourForwardThird_impossible
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hcross : c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ <
      a.order ⟨i.val, i.lt_large⟩)
    (hneBC : b.representationAlpha c i.previous ≠
      b.representationAlphaPrime c i.previous)
    (hthird : a.order ⟨i.val, i.lt_large⟩ <
      b.order ⟨i.val - 2, by have := i.lt_large; omega⟩) : False := by
  have hmiddle :=
    b.middlePrevious_le_sourcePrevious_of_previous_alpha_ne_prime
      c hbc i hneBC
  exact (not_lt_of_ge (hmiddle.trans hcross.le)) hthird

/-- Once Lemma 4.3 is available, its first alternative is forced in the
asymmetric case `A_i = A'_i`, `B_(i-1) < B'_(i-1)`. -/
theorem sectionFourForwardFirst_of_current_eq_previous_ne
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hcross : c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ <
      a.order ⟨i.val, i.lt_large⟩)
    (heqAB : a.representationAlpha b (i.current i.lt_large.le) =
      a.representationAlphaPrime b (i.current i.lt_large.le))
    (hneBC : b.representationAlpha c i.previous ≠
      b.representationAlphaPrime c i.previous)
    (hcomparison : SectionFourForwardComparison a b c i) :
    (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : ℚ) : WithTop ℚ) +
        a.representationAlphaPrime b (i.current i.lt_large.le) ≥
      ((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : ℚ) : WithTop ℚ) +
        a.representationAlpha c (i.current i.lt_large.le)) := by
  rcases hcomparison with hfirst | hsecond | hthird
  · exact hfirst
  · exact (a.sectionFourForwardSecond_impossible b c i hcross
      heqAB hneBC hsecond).elim
  · exact (a.sectionFourForwardThird_impossible b c hbc i hcross
      hneBC hthird).elim

end BONG.GoodBONG

end Bong
