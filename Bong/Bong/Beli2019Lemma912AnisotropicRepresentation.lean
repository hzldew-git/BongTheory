/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912AnisotropicScalar
import Bong.Bong.DiagonalHasseSymbol

/-!
# Beli (2019), Lemma 9.12: anisotropic prefix representations

This file contains the representation-theoretic end of the anisotropic
half-gap branch.  Iterated codimension-one descent reduces the contradiction
to a represented binary prefix.  Determinant completion and the dyadic
defect-sum criterion then make the source ternary prefix isotropic.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {Q : Lattice K U} {N : Nat}

set_option maxHeartbeats 800000 in
-- Determinant completion introduces a dependent last coefficient; the two
-- adjacent Hilbert-symbol arguments are then normalized to prefix products.
/-- A represented binary prefix and the final strict defect sum force the
source ternary prefix to be isotropic.  This is the last geometric step in
the anisotropic branch of Lemma 9.12. -/
theorem firstThreeIsotropic_of_binaryPrefixRepresentation_of_defectSum
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (N + 3))
    (hbinary : DiagonalRepresents
      (c.prefixValues 2 (by omega))
      (a.prefixValues 3 (by omega)))
    (hdefect :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        defectOrder (K := K) (-c.prefixProduct 2) +
          defectOrder (K := K)
            ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1)) :
    a.Lemma814FirstThreeIsotropic := by
  let base := a.prefixValueUnits 3 (by omega)
  let head := c.prefixValueUnits 2 (by omega)
  let d := diagonalUnitDeterminant base * diagonalUnitDeterminant head
  let candidate : Fin 3 → Kˣ := Fin.snoc head d
  have hheadRep : DiagonalRepresents
      (diagonalUnitCoefficients head)
      (diagonalUnitCoefficients base) := by
    simpa only [head, base,
      c.diagonalUnitCoefficients_prefixValueUnits,
      a.diagonalUnitCoefficients_prefixValueUnits] using hbinary
  have hcandidateRep : DiagonalRepresents
      (diagonalUnitCoefficients candidate)
      (diagonalUnitCoefficients base) := by
    simpa only [candidate, d] using
      determinantCompletion_represents_base_general base head hheadRep
  have hcandidateZero : candidate (0 : Fin 3) = head (0 : Fin 2) := by
    simp [candidate]
  have hcandidateOne : candidate (1 : Fin 3) = head (1 : Fin 2) := by
    change (Fin.snoc head d : Fin 3 → Kˣ) 1 = head 1
    rw [show (1 : Fin 3) = (1 : Fin 2).castSucc by rfl,
      Fin.snoc_castSucc]
  have hcandidateTwo : candidate (2 : Fin 3) = d := by
    change (Fin.snoc head d : Fin 3 → Kˣ) 2 = d
    rw [show (2 : Fin 3) = Fin.last 2 by rfl, Fin.snoc_last]
  have hheadOne : head (1 : Fin 2) =
      c.valueUnit (1 : Fin (N + 3)) := by
    rfl
  have hfirstArgument : -(candidate 0 * candidate 1) =
      -c.prefixProduct 2 := by
    rw [hcandidateZero, hcandidateOne]
    have hprefixOne : c.prefixProduct 1 =
        c.valueUnit (0 : Fin (N + 3)) := by
      have h := c.toBONG.prefixProduct_succ 0 (by omega)
      change c.prefixProduct 1 = c.prefixProduct 0 *
        c.valueUnit (0 : Fin (N + 3)) at h
      have hzero : c.prefixProduct 0 = 1 := c.toBONG.prefixProduct_zero
      rw [hzero, one_mul] at h
      exact h
    have hprefix := c.toBONG.prefixProduct_succ 1 (by omega)
    change c.prefixProduct 2 = c.prefixProduct 1 *
      c.valueUnit (1 : Fin (N + 3)) at hprefix
    rw [hprefix, hprefixOne]
    rfl
  have hsecondArgument : -(candidate 1 * candidate 2) =
      ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1) *
        (c.valueUnit (1 : Fin (N + 3))) ^ 2 := by
    rw [hcandidateOne, hcandidateTwo, hheadOne]
    dsimp only [d]
    rw [a.diagonalUnitDeterminant_prefixValueUnits 3 (by omega),
      c.diagonalUnitDeterminant_prefixValueUnits 2 (by omega)]
    have hprefix := c.toBONG.prefixProduct_succ 1 (by omega)
    change c.prefixProduct 2 = c.prefixProduct 1 *
      c.valueUnit (1 : Fin (N + 3)) at hprefix
    rw [hprefix]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_one, pow_two]
    ring
  have hhilbert : hilbertSymbol K (-c.prefixProduct 2)
      ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1) = 1 :=
    hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e hdefect
  have hcandidateHilbert :
      hilbertSymbol K (-(candidate 0 * candidate 1))
          (-(candidate 1 * candidate 2)) = 1 := by
    rw [hfirstArgument, hsecondArgument, hilbertSymbol_mul_square_right]
    exact hhilbert
  have hcandidateIsotropic :
      DiagonalIsotropic (diagonalUnitCoefficients candidate) :=
    (diagonalUnitTernary_isotropic_iff_adjacentHilbertOne candidate).mpr
      hcandidateHilbert
  change DiagonalIsotropic (diagonalUnitCoefficients base)
  exact hcandidateRep.isotropic_of hcandidateIsotropic

namespace Beli2019Lemma910Data

/-- If the shifted scalar inequality fails at an index in the anisotropic
branch, then the following boundary is essential.  The scalar shift formula
shows that condition 2.1(ii) fails there.  Lemma 2.13 therefore makes one of
the two adjacent boundaries essential, while the alternating order profile
rules out the preceding one. -/
theorem nextEssential_of_failure
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [comparisonLaws : Beli2006AlphaLaws.{u, z} K]
    [structural : BONGStructuralLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (hdefectSourceTarget :
      (a.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength))
    (hdefectSource :
      (a.castLength hlength).RepresentationDefectCondition c)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (hfailure :
      (((E.bong.castLength hlength).order ⟨i.val, i.lt_large⟩ -
          (E.bong.castLength hlength).order
            (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
          (A₁ : ℚ) <
        (E.bong.castLength hlength).representationAlphaValue c i)
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i) :
    (E.bong.castLength hlength).IsNextEssential c i := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  letI : Beli2006AlphaLaws.{u, z} K := comparisonLaws
  let target := E.bong.castLength hlength
  have hnotDefect : ¬target.RepresentationDefectAt c i := by
    intro hdefectAt
    have hdefectValue :
        target.representationAlphaValue c i ≤
          target.truncatedPrefixDefect c 1 i.val i.val := by
      simpa only [RepresentationDefectAt,
        ← target.coe_representationAlphaValue c i] using hdefectAt
    have hshiftTop :=
      (@representationDefectAt_iff_shift
        K _ _ _ _ _ V _ _ W _ _ U _ _ q r s L Q N
          sourceLaws structural R₁ R₂ A₁
          a c D E horders hlength hdefectSourceTarget hdefectSource i hiTwo).mp
        hdefectValue
    have hshift : target.representationAlphaValue c i ≤
        (((target.order ⟨i.val, i.lt_large⟩ -
            target.order (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
          (A₁ : ℚ)) := by
      exact_mod_cast hshiftTop
    exact (not_le_of_gt hfailure) hshift
  have hcurrentNot : ¬target.IsCurrentEssential c i := by
    intro hcurrent
    have hiLarge := i.lt_large
    unfold IsCurrentEssential IsEssentialFor
      BeliOrderSequence.IsEssentialFor at hcurrent
    have hcross := hcurrent.1 (by
      simp only [currentEssentialIndex]
      omega) (by
      simpa only [currentEssentialIndex,
        show i.val - 1 + 1 = i.val by omega] using i.lt_large)
    simp only [orderSequence_at, currentEssentialIndex,
      show i.val - 1 - 1 = i.val - 2 by omega,
      show i.val - 1 + 1 = i.val by omega] at hcross
    let previous : Fin (N + 3) := ⟨i.val - 2, by omega⟩
    change c.order previous < target.order ⟨i.val, i.lt_large⟩ at hcross
    have heq : c.order previous =
        target.order ⟨i.val, i.lt_large⟩ := by
      rcases Nat.mod_two_eq_zero_or_one i.val with hmod | hmod
      · have hpreviousMod : (i.val - 2) % 2 = 0 := by omega
        rw [O.comparison_even previous (by simp only [previous]; omega)
            (by simpa only [previous] using hpreviousMod),
          O.target_even ⟨i.val, i.lt_large⟩ le_rfl hmod]
      · have hpreviousMod : (i.val - 2) % 2 = 1 := by omega
        rw [O.comparison_odd previous (by simp only [previous]; omega)
            (by simpa only [previous] using hpreviousMod),
          O.target_odd ⟨i.val, i.lt_large⟩ le_rfl hmod]
    rw [heq] at hcross
    exact (lt_irrefl _ hcross)
  by_contra hnext
  exact hnotDefect
    (target.representationDefectAt_of_not_essential
      (sourceLaws := sourceLaws) (targetLaws := comparisonLaws)
      c i hcurrentNot hnext)

/-- The next essential boundary gives the two strict order crossings used in
the anisotropic descent.  Since the Lemma 9.10 output agrees with the source
from its third coefficient onward, the right-hand orders are stated directly
for the original source BONG. -/
theorem source_orderCrossings_of_nextEssential
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (hnext : (E.bong.castLength hlength).IsNextEssential c i) :
    (∀ hinterior : i.val + 1 < N + 3,
      c.order ⟨i.val - 1, by omega⟩ <
        (a.castLength hlength).order ⟨i.val + 1, hinterior⟩) ∧
    (∀ hsecond : i.val + 2 < N + 3,
      c.order ⟨i.val - 2, by omega⟩ +
          c.order ⟨i.val - 1, by omega⟩ <
        (a.castLength hlength).order ⟨i.val + 1, by omega⟩ +
          (a.castLength hlength).order ⟨i.val + 2, hsecond⟩) := by
  let target := E.bong.castLength hlength
  constructor
  · intro hinterior
    have hcross := order_current_lt_next_of_nextEssential
      target c i (by omega) hinterior hnext
    rw [E.order_castLength_eq_source_of_two_le
      a D horders hlength ⟨i.val + 1, hinterior⟩
        (show 2 ≤ i.val + 1 by omega)] at hcross
    exact hcross
  · intro hsecond
    unfold IsNextEssential IsEssentialFor
      BeliOrderSequence.IsEssentialFor at hnext
    have hcross := hnext.2 (by
      simp only [nextEssentialIndex]
      omega) (by
      simpa only [nextEssentialIndex] using hsecond)
    simp only [orderSequence_at, nextEssentialIndex] at hcross
    rw [E.order_castLength_eq_source_of_two_le
        a D horders hlength ⟨i.val + 1, by omega⟩
          (show 2 ≤ i.val + 1 by omega),
      E.order_castLength_eq_source_of_two_le
        a D horders hlength ⟨i.val + 2, hsecond⟩
          (show 2 ≤ i.val + 2 by omega)] at hcross
    exact hcross

/-- The two mixed-prefix defect bounds at the failure index are precisely the
v2 central trigger at index `i + 1`.  Condition (iii') then yields the paper's
top prefix representation `[c₁,...,cᵢ] rep [a₁,...,aᵢ₊₁]`. -/
theorem prefixRepresentation_of_centralDefectBounds
    (a : GoodBONG q L (N + 3))
    (c : GoodBONG s Q (N + 3))
    (hcentral : a.CentralRepresentationConditionsPrime c)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (hinterior : i.val + 1 < N + 3)
    (hcross : c.order ⟨i.val - 1, by omega⟩ <
      a.order ⟨i.val + 1, hinterior⟩)
    (hsum :
      (((2 * (ramificationIndex K : ℚ) +
          (c.order ⟨i.val - 1, by omega⟩ : ℚ) -
          (a.order ⟨i.val + 1, hinterior⟩ : ℚ) : ℚ) : WithTop ℚ) <
        a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) +
          a.truncatedPrefixDefect c (-1) (i.val + 2) i.val)) :
    DiagonalRepresents
      (c.prefixValues i.val (Nat.le_of_lt i.lt_large))
      (a.prefixValues (i.val + 1) (Nat.le_of_lt hinterior)) := by
  let central : CentralRepresentationIndex (N + 3) (N + 3) :=
    ⟨i.val + 1, by omega, hinterior, by omega⟩
  apply hcentral central
  unfold centralDefectTrigger centralPreviousDefect centralCurrentDefect
  constructor
  · simpa only [central,
      show i.val + 1 - 2 = i.val - 1 by omega] using hcross
  · simpa only [central,
      show i.val + 1 - 2 = i.val - 1 by omega,
      show i.val + 1 + 1 = i.val + 2 by omega,
      show i.val + 1 - 1 = i.val by omega] using hsum

/-- The complete geometric contradiction at the end of the anisotropic
branch.  A top prefix representation and the descending family of strict
defect sums reduce to the represented binary prefix; the final defect sum
then makes the source ternary prefix isotropic, contradicting anisotropy. -/
theorem false_of_anisotropic_of_prefixDescentBounds
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 3))
    (c : GoodBONG s Q (N + 3))
    (hanisotropic : a.Lemma814FirstThreeAnisotropic)
    (j : Nat) (hjTwo : 2 ≤ j) (hjNext : j + 1 ≤ N + 3)
    (htop : DiagonalRepresents
      (c.prefixValues j (by omega))
      (a.prefixValues (j + 1) hjNext))
    (hsteps : ∀ k : Nat, 2 < k → k ≤ j →
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        defectOrder (K := K)
            (a.prefixProduct k * c.prefixProduct k) +
          defectOrder (K := K)
            (-a.prefixProduct (k + 1) * c.prefixProduct (k - 1)))
    (hfinal :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        defectOrder (K := K) (-c.prefixProduct 2) +
          defectOrder (K := K)
            ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1)) :
    False := by
  have hbinary := a.prefixRepresentation_descend_to_two
    c j hjTwo hjNext htop hsteps
  have hisotropic :=
    a.firstThreeIsotropic_of_binaryPrefixRepresentation_of_defectSum
      c hbinary hfinal
  exact a.not_firstThreeIsotropic_of_anisotropic hanisotropic hisotropic

/-- Simultaneously replace both prefix factors in a mixed raw defect.  The
same signed self-defect is used on both sides, so its sign occurs twice and
disappears modulo a square.  This is the domination calculation behind the
descending propagation in Lemma 9.12. -/
theorem defectOrder_replace_both
    (ε δ a a' b b' : Kˣ) (x : WithTop ℚ)
    (htop : x ≤ defectOrder (K := K) (ε * a * b))
    (hleft : x ≤ defectOrder (K := K) (δ * a * a'))
    (hright : x ≤ defectOrder (K := K) (δ * b * b')) :
    x ≤ defectOrder (K := K) (ε * a' * b') := by
  have hleft' : x ≤ defectOrder (K := K) (a * (δ * a')) := by
    convert hleft using 1
    ac_rfl
  have hmid : x ≤ defectOrder (K := K) (ε * (δ * a') * b) :=
    (le_min htop hleft').trans
      (defectOrder_replace_left (K := K) ε a (δ * a') b)
  have hright' : x ≤ defectOrder (K := K) (b * (δ * b')) := by
    convert hright using 1
    ac_rfl
  have hout : x ≤
      defectOrder (K := K) (ε * (δ * a') * (δ * b')) :=
    (le_min hmid hright').trans
      (defectOrder_replace_right (K := K) ε (δ * a') b (δ * b'))
  calc
    x ≤ defectOrder (K := K) (ε * (δ * a') * (δ * b')) := hout
    _ = defectOrder (K := K) ((ε * a' * b') * δ ^ 2) := by
      congr 1
      simp only [pow_two]
      ac_rfl
    _ = defectOrder (K := K) (ε * a' * b') :=
      defectOrder_mul_square (ε * a' * b') δ

/-- A raw defect of an even-order square class cannot equal an even integral
threshold strictly below `2e`.  Thus a weak lower bound at such a threshold
automatically becomes strict. -/
theorem evenThreshold_lt_defectOrder_of_le
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    (x : Kˣ) (A : Int)
    (hAeven : Even A)
    (hAlt : A < 2 * (ramificationIndex K : Int))
    (hxEven : Even (ordUnit K x))
    (hle : ((((A : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) x)) :
    (((A : Int) : ℚ) : WithTop ℚ) < defectOrder (K := K) x := by
  by_contra hnot
  have hupper : defectOrder (K := K) x ≤
      (((A : Int) : ℚ) : WithTop ℚ) := le_of_not_gt hnot
  have heq : defectOrder (K := K) x =
      (((A : Int) : ℚ) : WithTop ℚ) := le_antisymm hupper hle
  have hAltQ : (A : ℚ) < 2 * (ramificationIndex K : ℚ) := by
    exact_mod_cast hAlt
  rcases isOddRationalInteger_of_even_ordUnit_of_defectOrder_eq
      x (A : ℚ) hxEven heq hAltQ with ⟨z, hzOdd, hz⟩
  have hzA : z = A := by
    exact_mod_cast hz.symm
  subst z
  rcases hAeven with ⟨p, hp⟩
  rcases hzOdd with ⟨q, hq⟩
  omega

/-- At the terminal failure index the desired top prefix representation is
the paper's "obvious" ambient case: the source prefix is the entire target
space, while the comparison prefix is realized by its initial segment. -/
theorem prefixRepresentation_of_ambient_when_target_full
    (a : GoodBONG q L (N + 3))
    (c : GoodBONG s Q (N + 3))
    (ambient : q.Represents s)
    (j : Nat) (hj : j ≤ N + 3) (hfull : j + 1 = N + 3) :
    DiagonalRepresents
      (c.prefixValues j hj)
      (a.prefixValues (j + 1) (by omega)) := by
  let w := c.toBONG.segmentWitness 0 j (by omega)
  let inclusion : QuadraticSpace.Representation
      (s.restrict w.carrier w.nondegenerate) s :=
    { toLinearMap := Submodule.subtype w.carrier
      injective := Subtype.val_injective
      map_bilin _ _ := rfl }
  have hsegment : q.Represents (s.restrict w.carrier w.nondegenerate) :=
    ambient.trans ⟨inclusion⟩
  have hdiagonal :=
    a.toBONG.diagonalRepresents_of_ambient w.bong hsegment
  have hcomplete : DiagonalRepresents
      (c.prefixValues j hj)
      (a.prefixValues (N + 3) le_rfl) := by
    convert hdiagonal using 1
    · funext k
      unfold prefixValues
      rw [w.value_eq]
      apply congrArg c.toBONG.value
      apply Fin.ext
      simp [BONG.SegmentWitness.sourceIndex]
    · funext k
      rfl
  exact targetPrefixRepresents_cast
    (c.prefixValues j hj) a hfull.symm hcomplete

end Beli2019Lemma910Data

end BONG.GoodBONG

end Bong
