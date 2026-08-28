/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourCentralLowCandidates
import Bong.Bong.Beli2019SectionFourKeyDual

/-!
# Beli (2019), Corollary 4.4 by reverse-duality

This file transports Lemma 4.3 at the complementary boundary of the swapped
reverse-dual triple.  It proves the backward comparison used in the remaining
Section 4 cases without assuming an unproved full duality theorem for the
four-condition representation package.
-/

namespace Bong

open Dyadic

namespace CentralRepresentationIndex

/-- The central boundary whose current ordinary boundary is complementary to
the previous ordinary boundary of `i`. -/
def reversePrevious {N : Nat} (i : CentralRepresentationIndex N N) :
    CentralRepresentationIndex N N where
  val := N - (i.val - 1)
  one_lt := by
    have := i.lt_large
    have := i.one_lt
    omega
  lt_large := by
    have := i.one_lt
    have := i.lt_large
    omega
  le_small_succ := by omega

@[simp]
theorem reversePrevious_val {N : Nat} (i : CentralRepresentationIndex N N) :
    i.reversePrevious.val = N - (i.val - 1) :=
  rfl

/-- The current boundary of `reversePrevious i` is the reverse of
`i.previous`. -/
theorem reversePrevious_current_eq {N : Nat}
    (i : CentralRepresentationIndex N N) :
    i.reversePrevious.current i.reversePrevious.lt_large.le =
      i.previous.reverse := by
  apply RepresentationIndex.ext
  rfl

/-- The preceding boundary of `reversePrevious i` is the reverse of the
current boundary of `i`. -/
theorem reversePrevious_previous_eq {N : Nat}
    (i : CentralRepresentationIndex N N) :
    i.reversePrevious.previous = (i.current i.lt_large.le).reverse := by
  apply RepresentationIndex.ext
  simp only [reversePrevious_val, previous, current,
    RepresentationIndex.reverse_val]
  have := i.one_lt
  have := i.lt_large
  omega

end CentralRepresentationIndex

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  {L N : Lattice K V} {n : Nat}

/-- The central trigger is invariant after reversing both BONGs, swapping
source and target, and moving from `i` to the complementary boundary of
`i.previous`. -/
theorem centralAlphaTrigger_reverseDual_swap
    (a : GoodBONG q L (n + 1)) (c : GoodBONG q N (n + 1))
    (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (cDual : GoodBONG q (Lattice.dualLattice q N) (n + 1))
    (haOrders : ∀ k, aDual.order k = -a.order (Fin.rev k))
    (hcOrders : ∀ k, cDual.order k = -c.order (Fin.rev k))
    (hAlpha : ∀ k : RepresentationIndex (n + 1) (n + 1),
      cDual.representationAlpha aDual k.reverse =
        a.representationAlpha c k)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i) :
    cDual.centralAlphaTrigger aDual i.reversePrevious := by
  let j := i.reversePrevious
  have haTwoPrevious :
      aDual.order ⟨j.val - 2, by have := j.lt_large; omega⟩ =
        -a.order ⟨i.val, i.lt_large⟩ := by
    rw [haOrders]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, j, CentralRepresentationIndex.reversePrevious_val]
    have := i.one_lt
    have := i.lt_large
    omega
  have hcCurrent :
      cDual.order ⟨j.val, j.lt_large⟩ =
        -c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
    rw [hcOrders]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, j, CentralRepresentationIndex.reversePrevious_val]
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
  have hAlphaValue : ∀ k : RepresentationIndex (n + 1) (n + 1),
      cDual.representationAlphaValue aDual k.reverse =
        a.representationAlphaValue c k := by
    intro k
    apply WithTop.coe_injective
    rw [cDual.coe_representationAlphaValue aDual k.reverse,
      a.coe_representationAlphaValue c k, hAlpha k]
  have hCurrentIndex :
      j.current j.lt_large.le = i.previous.reverse := by
    simpa only [j] using i.reversePrevious_current_eq
  have hPreviousIndex :
      j.previous = (i.current i.lt_large.le).reverse := by
    simpa only [j] using i.reversePrevious_previous_eq
  have hValuePrevious :
      cDual.representationAlphaValue aDual j.previous =
        a.representationAlphaValue c (i.current i.lt_large.le) := by
    rw [hPreviousIndex]
    exact hAlphaValue (i.current i.lt_large.le)
  have hValueCurrent :
      cDual.representationAlphaValue aDual (j.current j.lt_large.le) =
        a.representationAlphaValue c i.previous := by
    rw [hCurrentIndex]
    exact hAlphaValue i.previous
  unfold centralAlphaTrigger at htrigger ⊢
  rcases htrigger with ⟨horder, halpha⟩
  constructor
  · rw [haTwoPrevious, hcCurrent]
    omega
  · unfold centralAdjustedAlpha at halpha ⊢
    rw [dif_pos i.lt_large.le] at halpha
    rw [dif_pos j.lt_large.le]
    rw [hcPrevious, haPrevious, hValuePrevious, hValueCurrent]
    norm_cast at halpha ⊢
    push_cast at halpha ⊢
    linarith

/-- Corollary 4.4 in the branch actually used by Section 4:
`B_(i-1)=B'_(i-1)`.  It is Lemma 4.3 for the swapped reverse-dual triple at
the complementary boundary of `i.previous`. -/
theorem sectionFourBackwardComparison_of_previous_eq_prime_of_localConditions
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    {M : Lattice K V}
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hlocal : SectionFourLocalConditions a b c)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (heqBC : b.representationAlpha c i.previous =
      b.representationAlphaPrime c i.previous) :
    SectionFourBackwardComparison a b c i := by
  rcases a.exists_sectionFourReverseDualTriple b c with
    ⟨aDual, bDual, cDual, haOrders, hbOrders, hcOrders,
      habAlpha, hacAlpha, hbcAlpha, habDefect, hbcDefect⟩
  let j := i.reversePrevious
  have hdualLocal : SectionFourLocalConditions cDual bDual aDual := by
    exact {
      habOrder := b.representationOrderCondition_reverseDual_swap
        c bDual cDual hbOrders hcOrders hlocal.hbcOrder
      habDefect := b.representationDefectCondition_reverseDual_swap
        c bDual cDual hbOrders hcOrders hbcDefect hlocal.hbcDefect
      hbcOrder := a.representationOrderCondition_reverseDual_swap
        b aDual bDual haOrders hbOrders hlocal.habOrder
      hbcDefect := a.representationDefectCondition_reverseDual_swap
        b aDual bDual haOrders hbOrders habDefect hlocal.habDefect }
  have hdualTrigger : cDual.centralAlphaTrigger aDual j := by
    simpa only [j] using a.centralAlphaTrigger_reverseDual_swap
      c aDual cDual haOrders hcOrders hacAlpha i htrigger
  have hCurrentIndex :
      j.current j.lt_large.le = i.previous.reverse := by
    simpa only [j] using i.reversePrevious_current_eq
  have hPreviousIndex :
      j.previous = (i.current i.lt_large.le).reverse := by
    simpa only [j] using i.reversePrevious_previous_eq
  have hprimeCurrent :
      cDual.representationAlphaPrime bDual (j.current j.lt_large.le) =
        b.representationAlphaPrime c i.previous := by
    rw [hCurrentIndex]
    exact b.representationAlphaPrime_reverseDual_swap
      c bDual cDual hbOrders hcOrders hbcDefect i.previous
  have hdualEq :
      cDual.representationAlpha bDual (j.current j.lt_large.le) =
        cDual.representationAlphaPrime bDual (j.current j.lt_large.le) := by
    calc
      cDual.representationAlpha bDual (j.current j.lt_large.le) =
          cDual.representationAlpha bDual i.previous.reverse := by
        rw [hCurrentIndex]
      _ = b.representationAlpha c i.previous := hbcAlpha i.previous
      _ = b.representationAlphaPrime c i.previous := heqBC
      _ = cDual.representationAlphaPrime bDual
          (j.current j.lt_large.le) := hprimeCurrent.symm
  have hforward :=
    cDual.sectionFourForwardComparison_of_current_eq_prime_of_localConditions
      bDual aDual hdualLocal j hdualTrigger hdualEq
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
  have hcCurrent :
      cDual.order ⟨j.val, j.lt_large⟩ =
        -c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
    rw [hcOrders]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, j, CentralRepresentationIndex.reversePrevious_val]
    have := i.one_lt
    have := i.lt_large
    omega
  have hbTwoPrevious :
      bDual.order ⟨j.val - 2, by have := j.lt_large; omega⟩ =
        -b.order ⟨i.val, i.lt_large⟩ := by
    rw [hbOrders]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, j, CentralRepresentationIndex.reversePrevious_val]
    have := i.one_lt
    have := i.lt_large
    omega
  have hacCurrent :
      cDual.representationAlpha aDual (j.current j.lt_large.le) =
        a.representationAlpha c i.previous := by
    rw [hCurrentIndex]
    exact hacAlpha i.previous
  have habPrevious :
      bDual.representationAlpha aDual j.previous =
        a.representationAlpha b (i.current i.lt_large.le) := by
    rw [hPreviousIndex]
    exact habAlpha (i.current i.lt_large.le)
  unfold SectionFourForwardComparison at hforward
  unfold SectionFourBackwardComparison
  rcases hforward with hfirst | hsecond | hthird
  · apply Or.inl
    rw [haPrevious, hacCurrent, hbPrevious, hprimeCurrent] at hfirst
    exact hfirst
  · apply Or.inr
    apply Or.inl
    rw [hbPrevious, habPrevious, hcCurrent, hprimeCurrent] at hsecond
    simpa only [Int.neg_neg] using hsecond
  · apply Or.inr
    apply Or.inr
    rw [hcCurrent, hbTwoPrevious] at hthird
    omega

/-- Full representation conditions supply Corollary 4.4's local hypotheses. -/
theorem sectionFourBackwardComparison_of_previous_eq_prime
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    {M : Lattice K V}
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (heqBC : b.representationAlpha c i.previous =
      b.representationAlphaPrime c i.previous) :
    SectionFourBackwardComparison a b c i := by
  exact a.sectionFourBackwardComparison_of_previous_eq_prime_of_localConditions
    b c (SectionFourLocalConditions.ofRepresentationConditions
      a b c hab hbc) i htrigger heqBC

end BONG.GoodBONG

end Bong
