/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourLemma45

/-!
# Beli (2019), Lemma 4.5(ii)

The paper obtains the second half of Lemma 4.5 from the first half by
reverse-duality at the complementary boundary.  We use that duality only for
the numerical prime-alpha estimate; the resulting original-side trigger is
then discharged by condition 2.1(iii), so no representation-duality axiom is
needed.
-/

namespace Bong

open Dyadic

namespace CentralRepresentationIndex

/-- The ordinary boundary two positions before a central boundary. -/
def previousPrevious {N : Nat} (i : CentralRepresentationIndex N N)
    (hi : 2 < i.val) : RepresentationIndex N N where
  val := i.val - 2
  pos := by omega
  lt_large := by have := i.lt_large; omega
  le_small := by have := i.le_small_succ; omega

@[simp]
theorem previousPrevious_val {N : Nat} (i : CentralRepresentationIndex N N)
    (hi : 2 < i.val) : (i.previousPrevious hi).val = i.val - 2 := by
  rfl

/-- The central boundary immediately preceding `i`. -/
def previousCentral {N : Nat} (i : CentralRepresentationIndex N N)
    (hi : 2 < i.val) : CentralRepresentationIndex N N where
  val := i.val - 1
  one_lt := by omega
  lt_large := by have := i.lt_large; omega
  le_small_succ := by have := i.le_small_succ; omega

@[simp]
theorem previousCentral_val {N : Nat} (i : CentralRepresentationIndex N N)
    (hi : 2 < i.val) : (i.previousCentral hi).val = i.val - 1 := by
  rfl

theorem previousCentral_previous_eq {N : Nat}
    (i : CentralRepresentationIndex N N) (hi : 2 < i.val) :
    (i.previousCentral hi).previous = i.previousPrevious hi := by
  apply RepresentationIndex.ext
  dsimp only [previousCentral, previous, previousPrevious]
  omega

theorem previousCentral_current_eq {N : Nat}
    (i : CentralRepresentationIndex N N) (hi : 2 < i.val) :
    (i.previousCentral hi).current (i.previousCentral hi).lt_large.le =
      i.previous := by
  apply RepresentationIndex.ext
  dsimp only [previousCentral, current, previous]

end CentralRepresentationIndex

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  {L M N : Lattice K V} {n : Nat}

/-- The two conclusions of Lemma 4.5(ii). -/
structure SectionFourLemma45BackwardCertificate
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1)) : Prop where
  sourcePrevious : DiagonalRepresents
    (c.prefixValues (i.val - 2) (by have := i.lt_large; omega))
    (b.prefixValues (i.val - 1) (by have := i.lt_large; omega))
  hilbert : hilbertSymbol K
    (b.prefixProduct (i.val - 1) * c.prefixProduct (i.val - 1))
    (-a.prefixProduct i.val * c.prefixProduct (i.val - 2)) = 1

/-- The prime-alpha estimate used to activate condition (iii) one boundary
to the left in Lemma 4.5(ii).  It is Lemma 4.5(i)'s estimate on the swapped
reverse-dual triple. -/
theorem sectionFourLemma45_previousAlpha_le_shiftedPreviousPreviousAlpha_of_prime
    [Beli2006AlphaLaws.{u, v} K] [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hbcDefectCondition : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiPrev : 2 < i.val)
    (htrigger : a.centralAlphaTrigger c i)
    (hcross : c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ <
      b.order ⟨i.val - 1, by have := i.lt_large; omega⟩)
    (hshift :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) ≤
        (((c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + b.representationAlpha c i.previous)
    (hpreviousPrime :
      b.representationAlpha c (i.previousPrevious hiPrev) =
        b.representationAlphaPrime c (i.previousPrevious hiPrev)) :
    a.representationAlpha c i.previous ≤
      (((a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ -
          b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
        b.representationAlpha c (i.previousPrevious hiPrev) := by
  rcases a.exists_sectionFourReverseDualTriple b c with
    ⟨aDual, bDual, cDual, haOrders, hbOrders, hcOrders,
      habAlpha, hacAlpha, hbcAlpha, habDefect, hbcDefect⟩
  let j := i.reversePrevious
  let k := i.previousPrevious hiPrev
  have hjNext : j.val + 1 < n + 1 := by
    dsimp only [j, CentralRepresentationIndex.reversePrevious_val]
    have := i.lt_large
    omega
  let dualNext := nextRepresentationIndex (j.current j.lt_large.le) hjNext
  have hdualDefect : cDual.RepresentationDefectCondition bDual :=
    b.representationDefectCondition_reverseDual_swap c bDual cDual
      hbOrders hcOrders hbcDefect hbcDefectCondition
  have hdualTrigger : cDual.centralAlphaTrigger aDual j := by
    simpa only [j] using a.centralAlphaTrigger_reverseDual_swap
      c aDual cDual haOrders hcOrders hacAlpha i htrigger
  have hJCurrent : j.current j.lt_large.le = i.previous.reverse := by
    simpa only [j] using i.reversePrevious_current_eq
  have hJPrevious : j.previous = (i.current i.lt_large.le).reverse := by
    simpa only [j] using i.reversePrevious_previous_eq
  have hJNext : dualNext = k.reverse := by
    apply RepresentationIndex.ext
    dsimp only [dualNext, k, j, nextRepresentationIndex,
      CentralRepresentationIndex.current,
      CentralRepresentationIndex.previousPrevious,
      CentralRepresentationIndex.reversePrevious_val,
      CentralRepresentationIndex.previous,
      RepresentationIndex.reverse_val]
    have := i.one_lt
    have := i.lt_large
    omega
  have hcPrevious :
      cDual.order ⟨j.val - 1, by have := j.lt_large; omega⟩ =
        -c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
    rw [hcOrders]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, j, CentralRepresentationIndex.reversePrevious_val]
    have := i.one_lt
    have := i.lt_large
    omega
  have hcCurrent : cDual.order ⟨j.val, j.lt_large⟩ =
      -c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
    rw [hcOrders]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, j, CentralRepresentationIndex.reversePrevious_val]
    have := i.one_lt
    have := i.lt_large
    omega
  have hbCurrent : bDual.order ⟨j.val, j.lt_large⟩ =
      -b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
    rw [hbOrders]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, j, CentralRepresentationIndex.reversePrevious_val]
    have := i.one_lt
    have := i.lt_large
    omega
  have haPrevious :
      aDual.order ⟨j.val - 1, by have := j.lt_large; omega⟩ =
        -a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
    rw [haOrders]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, j, CentralRepresentationIndex.reversePrevious_val]
    have := i.one_lt
    have := i.lt_large
    omega
  have hbPrevious :
      bDual.order ⟨j.val - 1, by have := j.lt_large; omega⟩ =
        -b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
    rw [hbOrders]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, j, CentralRepresentationIndex.reversePrevious_val]
    have := i.one_lt
    have := i.lt_large
    omega
  have hcNext : cDual.order ⟨j.val + 1, hjNext⟩ =
      -c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ := by
    rw [hcOrders]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, j, CentralRepresentationIndex.reversePrevious_val]
    have := i.one_lt
    have := i.lt_large
    omega
  have hdualCross :
      bDual.order ⟨j.val - 1, by have := j.lt_large; omega⟩ <
        cDual.order ⟨j.val + 1, hjNext⟩ := by
    rw [hbPrevious, hcNext]
    omega
  have hdualShift :
      ((((-cDual.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) :
            Int) : ℚ) : WithTop ℚ) +
          cDual.representationAlpha aDual j.previous ≤
        ((((-cDual.order ⟨j.val, j.lt_large⟩ : Int) : Int) : ℚ) :
            WithTop ℚ) +
          cDual.representationAlpha bDual (j.current j.lt_large.le) := by
    rw [hcPrevious, hcCurrent, hJPrevious, hJCurrent,
      hacAlpha (i.current i.lt_large.le), hbcAlpha i.previous]
    simpa only [Int.neg_neg] using hshift
  have hdualPreviousPrime :
      cDual.representationAlpha bDual dualNext =
        cDual.representationAlphaPrime bDual dualNext := by
    rw [hJNext, hbcAlpha k,
      b.representationAlphaPrime_reverseDual_swap c bDual cDual
        hbOrders hcOrders hbcDefect k]
    simpa only [k] using hpreviousPrime
  have hdualBound :=
    cDual.sectionFourLemma45_currentAlpha_le_shiftedNextAlpha_of_prime
      bDual aDual hdualDefect j hjNext hdualTrigger hdualCross hdualShift
        hdualPreviousPrime
  change cDual.representationAlpha aDual (j.current j.lt_large.le) ≤
      (((bDual.order ⟨j.val, j.lt_large⟩ -
          aDual.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + cDual.representationAlpha bDual dualNext at hdualBound
  rw [hJCurrent, hJNext, hbCurrent, haPrevious,
    hacAlpha i.previous, hbcAlpha k] at hdualBound
  have hcoeff :
      (((-b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ -
          -a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)) =
        ((a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ -
          b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : Int) : ℚ) := by
    norm_cast
    ring
  rw [hcoeff] at hdualBound
  simpa only [k] using hdualBound

/-- Under the hypotheses of Lemma 4.5(ii), condition (iii) is activated one
central boundary to the left. -/
theorem sectionFourLemma45_previousAlphaTrigger
    [Beli2006AlphaLaws.{u, v} K] [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiPrev : 2 < i.val)
    (htrigger : a.centralAlphaTrigger c i)
    (hcross : c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ <
      b.order ⟨i.val - 1, by have := i.lt_large; omega⟩)
    (hshift :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) ≤
        (((c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + b.representationAlpha c i.previous) :
    b.centralAlphaTrigger c (i.previousCentral hiPrev) := by
  let j := i.previousCentral hiPrev
  let k := i.previousPrevious hiPrev
  have hjSmall : j.val ≤ n + 1 := by
    dsimp only [j, CentralRepresentationIndex.previousCentral]
    have := i.lt_large
    omega
  by_cases hne : b.representationAlpha c k ≠
      b.representationAlphaPrime c k
  · have hne' : b.representationAlpha c j.previous ≠
        b.representationAlphaPrime c j.previous := by
      rw [i.previousCentral_previous_eq hiPrev]
      simpa only [k] using hne
    exact b.centralAlphaTrigger_of_previous_alpha_ne_prime c le_rfl
      hbc.orderCondition hbc.defectCondition j hjSmall hne'
  · have hpreviousPrime : b.representationAlpha c k =
        b.representationAlphaPrime c k := not_ne_iff.mp hne
    have hbound :=
      a.sectionFourLemma45_previousAlpha_le_shiftedPreviousPreviousAlpha_of_prime
        b c hbc.defectCondition i hiPrev htrigger hcross hshift (by
          simpa only [k] using hpreviousPrime)
    have houter := htrigger.2
    unfold centralAlphaTrigger
    refine ⟨?_, ?_⟩
    · change c.order ⟨i.val - 1 - 2, by
          have := i.lt_large
          omega⟩ <
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩
      convert hcross using 1 <;> congr 1 <;> omega
    · unfold centralAdjustedAlpha at houter ⊢
      rw [dif_pos i.lt_large.le] at houter
      rw [dif_pos hjSmall]
      rw [← a.coe_representationAlphaValue c (i.current i.lt_large.le),
        ← b.coe_representationAlphaValue c i.previous] at hshift
      rw [← a.coe_representationAlphaValue c i.previous,
        ← b.coe_representationAlphaValue c (i.previousPrevious hiPrev)] at hbound
      norm_cast at houter hshift hbound ⊢
      push_cast at houter hshift hbound ⊢
      rw [i.previousCentral_previous_eq hiPrev,
        i.previousCentral_current_eq hiPrev]
      dsimp only [j, k, CentralRepresentationIndex.previousCentral,
        CentralRepresentationIndex.previousPrevious,
        CentralRepresentationIndex.previous,
        CentralRepresentationIndex.current] at houter hshift hbound ⊢
      simp only [Nat.sub_sub, Nat.reduceAdd] at houter hshift hbound ⊢
      linarith

/-- The representation conclusion of Lemma 4.5(ii).  The lower endpoint
`i = 2` has an empty source prefix and is therefore immediate. -/
theorem sectionFourLemma45_sourcePrevious_represents
    [Beli2006AlphaLaws.{u, v} K] [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hboundary :
      (∃ hiPrev : 2 < i.val,
        c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ <
          b.order ⟨i.val - 1, by have := i.lt_large; omega⟩) ∨
        i.val = 2)
    (hshift :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) ≤
        (((c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + b.representationAlpha c i.previous) :
    DiagonalRepresents
      (c.prefixValues (i.val - 2) (by have := i.lt_large; omega))
      (b.prefixValues (i.val - 1) (by have := i.lt_large; omega)) := by
  rcases hboundary with ⟨hiPrev, hcross⟩ | hend
  · let j := i.previousCentral hiPrev
    have hpreviousTrigger := a.sectionFourLemma45_previousAlphaTrigger
      b c hbc i hiPrev htrigger hcross hshift
    change b.centralAlphaTrigger c j at hpreviousTrigger
    have hrep := hbc.centralRepresentations j hpreviousTrigger
    exact prefixRepresents_cast c b (by
      dsimp only [j, CentralRepresentationIndex.previousCentral]
      omega) rfl hrep
  · have hzero : i.val - 2 = 0 := by omega
    have hone : i.val - 1 = 1 := by omega
    have hrep := b.prefixValues_represents_of_le 0 1 (by omega) (by
      have := i.lt_large
      omega)
    have hrep' : DiagonalRepresents
        (b.prefixValues (i.val - 2) (by have := i.lt_large; omega))
        (b.prefixValues (i.val - 1) (by have := i.lt_large; omega)) :=
      prefixRepresents_cast b b hzero.symm hone.symm hrep
    have hsource :
        c.prefixValues (i.val - 2) (by have := i.lt_large; omega) =
          b.prefixValues (i.val - 2) (by have := i.lt_large; omega) := by
      funext x
      have := x.isLt
      omega
    rw [hsource]
    exact hrep'

/-- The primary candidate for `C_(i-1)` gives the lower bound
`T_(i-1)-R_i+C_(i-1) ≤ d[-a_(1,i)c_(1,i-2)]`. -/
theorem sectionFourLemma45_shiftedPreviousAlpha_le_previousDefect
    (a : GoodBONG q L (n + 1)) (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1)) :
    (((c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ -
        a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + a.representationAlpha c i.previous ≤
      a.centralPreviousDefect c i := by
  have hprimary := a.representationAlpha_le_primary c i.previous
  unfold representationPrimaryDefect at hprimary
  have hsubAdd : i.val - 1 + 1 = i.val := by
    have := i.one_lt
    omega
  have hsubSub : i.val - 1 - 1 = i.val - 2 := by omega
  simp only [CentralRepresentationIndex.previous, hsubAdd, hsubSub] at hprimary
  change a.representationAlpha c i.previous ≤
      (((a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ -
          c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
        a.truncatedPrefixDefect c (-1) i.val (i.val - 2) at hprimary
  let shift : ℚ := ((c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ -
    a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  let opposite : ℚ := ((a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ -
    c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : Int) : ℚ)
  unfold centralPreviousDefect
  change (shift : WithTop ℚ) + a.representationAlpha c i.previous ≤
    a.truncatedPrefixDefect c (-1) i.val (i.val - 2)
  have hprimary' : a.representationAlpha c i.previous ≤
      (opposite : WithTop ℚ) +
        a.truncatedPrefixDefect c (-1) i.val (i.val - 2) := by
    simpa only [opposite] using hprimary
  have hcoeff : (shift : WithTop ℚ) + (opposite : WithTop ℚ) = 0 := by
    dsimp only [shift, opposite]
    norm_cast
    ring
  calc
    _ ≤ (shift : WithTop ℚ) +
        ((opposite : WithTop ℚ) +
          a.truncatedPrefixDefect c (-1) i.val (i.val - 2)) :=
      add_le_add_right hprimary' _
    _ = a.truncatedPrefixDefect c (-1) i.val (i.val - 2) := by
      rw [← add_assoc, hcoeff, zero_add]

/-- The two raw defects in Lemma 4.5(ii) have sum strictly larger than
`2e`. -/
theorem sectionFourLemma45_backward_twoE_lt_truncatedDefectSum
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hbcDefect : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hshift :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) ≤
        (((c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + b.representationAlpha c i.previous) :
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
      b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1) +
        a.centralPreviousDefect c i := by
  have hBC := hbcDefect i.previous
  rw [b.coe_representationAlphaValue c i.previous] at hBC
  have hprevious :=
    a.sectionFourLemma45_shiftedPreviousAlpha_le_previousDefect c i
  have hlower :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.representationAlpha c i.previous +
          ((((c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ -
              a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
                WithTop ℚ) + a.representationAlpha c i.previous) := by
    have hsum := htrigger.2
    unfold centralAdjustedAlpha at hsum
    rw [dif_pos i.lt_large.le] at hsum
    rw [← a.coe_representationAlphaValue c (i.current i.lt_large.le),
      ← b.coe_representationAlphaValue c i.previous] at hshift
    rw [← b.coe_representationAlphaValue c i.previous,
      ← a.coe_representationAlphaValue c i.previous]
    norm_cast at hsum hshift ⊢
    push_cast at hsum hshift ⊢
    linarith
  exact hlower.trans_le (add_le_add hBC hprevious)

/-- The Hilbert-symbol conclusion of Lemma 4.5(ii). -/
theorem sectionFourLemma45_backward_hilbert
    [HilbertSymbolLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hbcDefect : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hshift :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) ≤
        (((c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + b.representationAlpha c i.previous) :
    hilbertSymbol K
      (b.prefixProduct (i.val - 1) * c.prefixProduct (i.val - 1))
      (-a.prefixProduct i.val * c.prefixProduct (i.val - 2)) = 1 := by
  apply hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
  have hsum := a.sectionFourLemma45_backward_twoE_lt_truncatedDefectSum
    b c hbcDefect i htrigger hshift
  apply hsum.trans_le
  apply add_le_add
  · simpa only [one_mul] using
      (b.truncatedPrefixDefect_le_defect c 1 (i.val - 1) (i.val - 1))
  · unfold centralPreviousDefect
    simpa only [neg_one_mul] using
      (a.truncatedPrefixDefect_le_defect c (-1) i.val (i.val - 2))

/-- Beli (2019), Lemma 4.5(ii), with its lower-endpoint alternative made
explicit. -/
theorem sectionFourLemma45_backward
    [Beli2006AlphaLaws.{u, v} K] [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hboundary :
      (∃ hiPrev : 2 < i.val,
        c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ <
          b.order ⟨i.val - 1, by have := i.lt_large; omega⟩) ∨
        i.val = 2)
    (hshift :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) ≤
        (((c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + b.representationAlpha c i.previous) :
    SectionFourLemma45BackwardCertificate a b c i where
  sourcePrevious := a.sectionFourLemma45_sourcePrevious_represents
    b c hbc i htrigger hboundary hshift
  hilbert := a.sectionFourLemma45_backward_hilbert
    b c hbc.defectCondition i htrigger hshift

end BONG.GoodBONG

end Bong
