/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814Statement
import Bong.Bong.Beli2019Lemma88Necessity
import Bong.Bong.Beli2006SectionFourInvariants
import Bong.Bong.DiagonalTernaryCore

/-!
# Beli (2019), Lemma 8.14: change-of-BONG invariants

The first part of the proof of Lemma 8.14 shows that its three exceptions do
not depend on the chosen good BONG.  This file separates the formal argument
into two layers:

* all orders, alphas, half gaps, and capped defects are transported by the
  already proved good-BONG invariance theorems;
* the two geometric predicates (isotropy of the ternary prefix and
  anisotropy of the prescribed line's complement in the quaternary prefix)
  are explicit hypotheses of the general transport theorem.

For target ranks three and four the relevant geometric transport follows
directly from full BONG coordinate changes.  Higher ranks require the Hilbert
symbol comparison carried out in the paper after Lemma 8.14.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

/-- The first-third capped defect is independent of the target good BONG. -/
theorem lemma814FirstThirdCappedDefect_invariant
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    (a a' : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) :
    a.lemma814FirstThirdCappedDefect b =
      a'.lemma814FirstThirdCappedDefect b := by
  unfold lemma814FirstThirdCappedDefect
  exact truncatedPrefixDefect_invariant
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW)
    a a' b b (-1) 3 1

/-- The capped defect `d[a_(1,4)]` is independent of the target good BONG. -/
theorem lemma814FirstFourCappedDefect_invariant
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    (a a' : GoodBONG q L (N + 3))
    (hfour hfour' : 4 ≤ N + 3) :
    a.lemma814FirstFourCappedDefect hfour =
      a'.lemma814FirstFourCappedDefect hfour' := by
  unfold lemma814FirstFourCappedDefect
  exact truncatedPrefixDefect_invariant
    (classificationV := classificationV)
    (classificationW := classificationV)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeV)
    a a' a a' 1 4 0

/-- Every adjacent order gap is independent of the chosen good BONG. -/
theorem orderGap_invariant
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    (a a' : GoodBONG q L (N + 3)) (i : Fin (N + 2)) :
    a.orderGap i = a'.orderGap i := by
  have horders : a.SameOrders a' := a.order_invariant a'
  unfold orderGap
  rw [horders i.succ, horders i.castSucc]

/-- Every half-gap value is independent of the chosen good BONG. -/
theorem halfGapValue_invariant
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    (a a' : GoodBONG q L (N + 3)) (i : Fin (N + 2)) :
    a.halfGapValue i = a'.halfGapValue i := by
  unfold halfGapValue
  rw [a.orderGap_invariant (classificationV := classificationV) a' i]

/-- The complementary third-gap quantity in exception (c) is invariant. -/
theorem lemma814ThirdComplementaryDefect_invariant
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    (a a' : GoodBONG q L (N + 3))
    (hfour hfour' : 4 ≤ N + 3) :
    a.lemma814ThirdComplementaryDefect hfour =
      a'.lemma814ThirdComplementaryDefect hfour' := by
  unfold lemma814ThirdComplementaryDefect
  rw [a.orderGap_invariant (classificationV := classificationV) a'
    (⟨2, by omega⟩ : Fin (N + 2))]

/-- All numerical fields of exception (a) transport to another good BONG;
only the ternary anisotropy assertion remains geometric. -/
theorem lemma814ExceptionA_of_changeBONG
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    (a a' : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (A : a.Beli2019Lemma814ExceptionA b)
    (hanisotropic : a'.Lemma814FirstThreeAnisotropic) :
    a'.Beli2019Lemma814ExceptionA b := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  have horders := a.order_invariant a'
  have halphas := a.alpha_invariant a'
  have hdefect := a.lemma814FirstThirdCappedDefect_invariant
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW) a' b
  refine
    { firstThirdOrders_eq :=
        (horders 0).symm.trans (A.firstThirdOrders_eq.trans (horders 2))
      defectSum_strict := ?_
      firstThree_anisotropic := hanisotropic }
  rw [← halphas (1 : Fin (N + 2)), ← hdefect]
  exact A.defectSum_strict

/-- All numerical fields of exception (b) transport to another good BONG;
only ternary isotropy is supplied separately. -/
theorem lemma814ExceptionB_of_changeBONG
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    (a a' : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (B : a.Beli2019Lemma814ExceptionB b)
    (hisotropic : a'.Lemma814FirstThreeIsotropic) :
    a'.Beli2019Lemma814ExceptionB b := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  have horders := a.order_invariant a'
  have halphas := a.alpha_invariant a'
  have hdefect := a.lemma814FirstThirdCappedDefect_invariant
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW) a' b
  refine
    { firstThirdOrders_eq :=
        (horders 0).symm.trans (B.firstThirdOrders_eq.trans (horders 2))
      residueTwo := B.residueTwo
      firstAlpha_strict := ?_
      defectSum_eq := ?_
      firstThree_isotropic := hisotropic
      laterAlphaSum_strict := ?_ }
  · rw [← halphas (0 : Fin (N + 2)),
      ← a.halfGapValue_invariant (classificationV := classificationV)
        a' (0 : Fin (N + 2))]
    exact B.firstAlpha_strict
  · rw [← halphas (1 : Fin (N + 2)), ← hdefect]
    exact B.defectSum_eq
  · intro hfour
    rw [← halphas (1 : Fin (N + 2)),
      ← halphas (⟨2, by omega⟩ : Fin (N + 2))]
    exact B.laterAlphaSum_strict hfour

/-- All numerical fields of exception (c) transport to another good BONG;
only anisotropy of the ternary complement is supplied separately. -/
theorem lemma814ExceptionC_of_changeBONG
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    (a a' : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (C : a.Beli2019Lemma814ExceptionC b)
    (hanisotropic :
      a'.Lemma814FirstFourComplementAnisotropic b C.rank_four) :
    a'.Beli2019Lemma814ExceptionC b := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  have hfour := C.rank_four
  let thirdAlpha : Fin (N + 2) := ⟨2, by omega⟩
  let fourthOrder : Fin (N + 3) := ⟨3, by omega⟩
  have horders := a.order_invariant a'
  have halphas := a.alpha_invariant a'
  have hfirstThird := a.lemma814FirstThirdCappedDefect_invariant
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW) a' b
  have hfirstFour := a.lemma814FirstFourCappedDefect_invariant
    (classificationV := classificationV) (prefixChangeV := prefixChangeV)
    a' C.rank_four C.rank_four
  have hcomplement := a.lemma814ThirdComplementaryDefect_invariant
    (classificationV := classificationV) a' C.rank_four C.rank_four
  refine
    { rank_four := C.rank_four
      firstThirdOrders_eq :=
        (horders 0).symm.trans (C.firstThirdOrders_eq.trans (horders 2))
      residueTwo := C.residueTwo
      secondFourthOrders_lt := ?_
      firstThirdDefect_eq_alpha := ?_
      thirdAlpha_eq_halfGap := ?_
      firstFourDefect_eq_secondAlpha := ?_
      secondAlpha_eq_complement := ?_
      firstFourComplement_anisotropic := hanisotropic
      laterAlpha_strict := ?_ }
  · rw [← horders (1 : Fin (N + 3)),
      ← horders fourthOrder]
    exact C.secondFourthOrders_lt
  · rw [← hfirstThird, ← halphas thirdAlpha]
    exact C.firstThirdDefect_eq_alpha
  · rw [← halphas thirdAlpha,
      ← a.halfGapValue_invariant (classificationV := classificationV)
        a' thirdAlpha]
    exact C.thirdAlpha_eq_halfGap
  · rw [← hfirstFour, ← halphas (1 : Fin (N + 2))]
    exact C.firstFourDefect_eq_secondAlpha
  · rw [← halphas (1 : Fin (N + 2)), ← hcomplement]
    exact C.secondAlpha_eq_complement
  · intro hfive
    let fourthAlpha : Fin (N + 2) := ⟨3, by omega⟩
    rw [← hcomplement, ← halphas fourthAlpha]
    exact C.laterAlpha_strict hfive

/-- Once the two geometric predicates are known to be invariant, the full
exceptional alternative is invariant. -/
theorem lemma814Exceptional_changeBONG_iff
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    (a a' : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hthree :
      a.Lemma814FirstThreeIsotropic ↔
        a'.Lemma814FirstThreeIsotropic)
    (hfour : ∀ h : 4 ≤ N + 3,
      a.Lemma814FirstFourComplementAnisotropic b h ↔
        a'.Lemma814FirstFourComplementAnisotropic b h) :
    a.Beli2019Lemma814Exceptional b ↔
      a'.Beli2019Lemma814Exceptional b := by
  have hthreeAnisotropic :
      a.Lemma814FirstThreeAnisotropic ↔
        a'.Lemma814FirstThreeAnisotropic := by
    rw [← a.not_firstThreeIsotropic_iff_anisotropic,
      ← a'.not_firstThreeIsotropic_iff_anisotropic, not_congr hthree]
  constructor
  · rintro (A | B | C)
    · exact Or.inl (a.lemma814ExceptionA_of_changeBONG
        (classificationV := classificationV) (classificationW := classificationW)
        (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
        a' b A (hthreeAnisotropic.mp A.firstThree_anisotropic))
    · exact Or.inr (Or.inl (a.lemma814ExceptionB_of_changeBONG
        (classificationV := classificationV) (classificationW := classificationW)
        (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
        a' b B (hthree.mp B.firstThree_isotropic)))
    · exact Or.inr (Or.inr (a.lemma814ExceptionC_of_changeBONG
        (classificationV := classificationV) (classificationW := classificationW)
        (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
        a' b C ((hfour C.rank_four).mp C.firstFourComplement_anisotropic)))
  · rintro (A | B | C)
    · exact Or.inl (a'.lemma814ExceptionA_of_changeBONG
        (classificationV := classificationV) (classificationW := classificationW)
        (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
        a b A (hthreeAnisotropic.mpr A.firstThree_anisotropic))
    · exact Or.inr (Or.inl (a'.lemma814ExceptionB_of_changeBONG
        (classificationV := classificationV) (classificationW := classificationW)
        (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
        a b B (hthree.mpr B.firstThree_isotropic)))
    · exact Or.inr (Or.inr (a'.lemma814ExceptionC_of_changeBONG
        (classificationV := classificationV) (classificationW := classificationW)
        (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
        a b C ((hfour C.rank_four).mpr C.firstFourComplement_anisotropic)))

/-- In rank three, ternary isotropy is invariant because the prefix is the
entire ambient quadratic space. -/
theorem lemma814FirstThreeIsotropic_changeBONG_iff_rankThree
    (a a' : GoodBONG q L 3) :
    a.Lemma814FirstThreeIsotropic ↔
      a'.Lemma814FirstThreeIsotropic := by
  constructor
  · intro h
    have hrep := a.fullPrefix_represents a'
    apply hrep.isotropic_of
    simpa [DiagonalIsotropic, Lemma814FirstThreeIsotropic,
      lemma814FirstThreeValues] using h
  · intro h
    have hrep := a'.fullPrefix_represents a
    apply hrep.isotropic_of
    simpa [DiagonalIsotropic, Lemma814FirstThreeIsotropic,
      lemma814FirstThreeValues] using h

/-- In rank three, ternary anisotropy is invariant for the same reason. -/
theorem lemma814FirstThreeAnisotropic_changeBONG_iff_rankThree
    (a a' : GoodBONG q L 3) :
    a.Lemma814FirstThreeAnisotropic ↔
      a'.Lemma814FirstThreeAnisotropic := by
  constructor
  · intro h
    have hrep := a'.fullPrefix_represents a
    apply hrep.anisotropic_of
    simpa [DiagonalAnisotropic, Lemma814FirstThreeAnisotropic,
      lemma814FirstThreeValues] using h
  · intro h
    have hrep := a.fullPrefix_represents a'
    apply hrep.anisotropic_of
    simpa [DiagonalAnisotropic, Lemma814FirstThreeAnisotropic,
      lemma814FirstThreeValues] using h

/-- In rank four, a ternary complement of the prescribed line in one full
BONG presentation is also such a complement in the other full presentation.
Thus its anisotropy is invariant. -/
theorem lemma814FirstFourComplementAnisotropic_changeBONG_iff_rankFour
    (a a' : GoodBONG q L 4) (b : GoodBONG r M 1)
    (hfour : 4 ≤ 4) :
    a.Lemma814FirstFourComplementAnisotropic b hfour ↔
      a'.Lemma814FirstFourComplementAnisotropic b hfour := by
  constructor
  · rintro ⟨complement, hrep, hanisotropic⟩
    refine ⟨complement, hrep.trans (a.fullPrefix_represents a'), hanisotropic⟩
  · rintro ⟨complement, hrep, hanisotropic⟩
    refine ⟨complement, hrep.trans (a'.fullPrefix_represents a), hanisotropic⟩

/-- The complete exceptional alternative is invariant in target rank three.
Here the ternary prefix is the full space and exception (c) is unavailable. -/
theorem lemma814Exceptional_changeBONG_iff_rankThree
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    (a a' : GoodBONG q L 3) (b : GoodBONG r M 1) :
    Beli2019Lemma814Exceptional (N := 0) a b ↔
      Beli2019Lemma814Exceptional (N := 0) a' b := by
  apply a.lemma814Exceptional_changeBONG_iff
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    a' b (a.lemma814FirstThreeIsotropic_changeBONG_iff_rankThree a')
  intro hfour
  omega

/-- Exception (c) itself is invariant in target rank four, where its
quaternary prefix is the whole target space. -/
theorem lemma814ExceptionC_changeBONG_iff_rankFour
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    (a a' : GoodBONG q L 4) (b : GoodBONG r M 1) :
    Beli2019Lemma814ExceptionC (N := 1) a b ↔
      Beli2019Lemma814ExceptionC (N := 1) a' b := by
  constructor
  · intro C
    apply a.lemma814ExceptionC_of_changeBONG
      (classificationV := classificationV) (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      a' b C
    exact (a.lemma814FirstFourComplementAnisotropic_changeBONG_iff_rankFour
      a' b C.rank_four).mp C.firstFourComplement_anisotropic
  · intro C
    apply a'.lemma814ExceptionC_of_changeBONG
      (classificationV := classificationV) (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      a b C
    exact (a.lemma814FirstFourComplementAnisotropic_changeBONG_iff_rankFour
      a' b C.rank_four).mpr C.firstFourComplement_anisotropic

end BONG.GoodBONG

end Bong
