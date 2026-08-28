/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019RepresentationTransitivity
import Bong.Bong.Beli2019CanonicalApproximation
import Bong.Bong.DiagonalRepresentationParity

/-!
# Beli (2019), Section 4: the three Lemma 1.5 diagrams

The proof of condition 2.1(iii) uses each of the three parity diagrams in
Lemma 1.5.  This file turns their concrete prefix representations and Hilbert
symbols into the central certificate consumed by the Section 4 assembly.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DiagonalRepresentationParityLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K U}
  {n : Nat}

namespace CentralRepresentationCertificate

/-- Lemma 1.5(i): two adjacent middle-prefix representations and the
displayed Hilbert symbol force the missing representation from `c` to `a`. -/
theorem of_caseI
    {a : GoodBONG q L (n + 1)} {b : GoodBONG r M (n + 1)}
    {c : GoodBONG s N (n + 1)}
    {i : CentralRepresentationIndex (n + 1) (n + 1)}
    (middlePrevious : DiagonalRepresents
      (b.prefixValues (i.val - 1) i.previous_le_sameRank)
      (a.prefixValues i.val i.current_le_sameRank))
    (sourceCurrent : DiagonalRepresents
      (c.prefixValues (i.val - 1) i.previous_le_sameRank)
      (b.prefixValues i.val i.current_le_sameRank))
    (hilbert : hilbertSymbol K
      (a.prefixProduct i.val * b.prefixProduct i.val)
      (b.prefixProduct (i.val - 1) * c.prefixProduct (i.val - 1)) = 1) :
    CentralRepresentationCertificate a b c i := by
  apply CentralRepresentationCertificate.direct
  let au := a.prefixValueUnits i.val i.current_le_sameRank
  let bu := b.prefixValueUnits i.val i.current_le_sameRank
  let cu := c.prefixValueUnits (i.val - 1) i.previous_le_sameRank
  have hp : DiagonalRepresents
      (diagonalUnitCoefficients
        (diagonalUnitTake bu (i.val - 1) (by omega)))
      (diagonalUnitCoefficients au) := by
    simpa only [au, bu, diagonalUnitTake_prefixValueUnits,
      diagonalUnitCoefficients_prefixValueUnits] using middlePrevious
  have hq : DiagonalRepresents
      (diagonalUnitCoefficients cu)
      (diagonalUnitCoefficients bu) := by
    simpa only [bu, cu, diagonalUnitCoefficients_prefixValueUnits] using
      sourceCurrent
  have hs : hilbertSymbol K
      (diagonalUnitDeterminant au * diagonalUnitDeterminant bu)
      (diagonalUnitDeterminant
          (diagonalUnitTake bu (i.val - 1) (by omega)) *
        diagonalUnitDeterminant cu) = 1 := by
    simpa only [au, bu, cu, diagonalUnitTake_prefixValueUnits,
      diagonalUnitDeterminant_prefixValueUnits] using hilbert
  have hcycle := DiagonalRepresentationParityLaws.caseI
    au bu cu rfl (by
      have := i.one_lt
      omega)
  have hr := hcycle.all_triple_consequences.2.1 hp hq hs
  simpa only [au, cu, diagonalUnitCoefficients_prefixValueUnits] using hr

/-- Lemma 1.5(ii): a representation through the next `a`-prefix and its
Hilbert symbol force the representation into the current `a`-prefix. -/
theorem of_caseII
    {a : GoodBONG q L (n + 1)} {b : GoodBONG r M (n + 1)}
    {c : GoodBONG s N (n + 1)}
    {i : CentralRepresentationIndex (n + 1) (n + 1)}
    (middleCurrent : DiagonalRepresents
      (b.prefixValues i.val i.current_le_sameRank)
      (a.prefixValues (i.val + 1) (Nat.succ_le_of_lt i.lt_large)))
    (sourceCurrent : DiagonalRepresents
      (c.prefixValues (i.val - 1) i.previous_le_sameRank)
      (b.prefixValues i.val i.current_le_sameRank))
    (hilbert : hilbertSymbol K
      (a.prefixProduct i.val * b.prefixProduct i.val)
      (-a.prefixProduct (i.val + 1) * c.prefixProduct (i.val - 1)) = 1) :
    CentralRepresentationCertificate a b c i := by
  apply CentralRepresentationCertificate.direct
  let au := a.prefixValueUnits (i.val + 1)
    (Nat.succ_le_of_lt i.lt_large)
  let bu := b.prefixValueUnits i.val i.current_le_sameRank
  let cu := c.prefixValueUnits (i.val - 1) i.previous_le_sameRank
  have hp : DiagonalRepresents
      (diagonalUnitCoefficients bu)
      (diagonalUnitCoefficients au) := by
    simpa only [au, bu, diagonalUnitCoefficients_prefixValueUnits] using
      middleCurrent
  have hq : DiagonalRepresents
      (diagonalUnitCoefficients cu)
      (diagonalUnitCoefficients bu) := by
    simpa only [bu, cu, diagonalUnitCoefficients_prefixValueUnits] using
      sourceCurrent
  have hs : hilbertSymbol K
      (diagonalUnitDeterminant
          (diagonalUnitTake au i.val (by omega)) *
        diagonalUnitDeterminant bu)
      (-diagonalUnitDeterminant au * diagonalUnitDeterminant cu) = 1 := by
    simpa only [au, bu, cu, diagonalUnitTake_prefixValueUnits,
      diagonalUnitDeterminant_prefixValueUnits] using hilbert
  have hcycle := DiagonalRepresentationParityLaws.caseII
    au bu cu rfl (by
      have := i.one_lt
      omega)
  have hr := hcycle.all_triple_consequences.2.1 hp hq hs
  simpa only [au, cu, diagonalUnitTake_prefixValueUnits,
    diagonalUnitCoefficients_prefixValueUnits] using hr

/-- Lemma 1.5(iii): the two preceding-prefix representations and their
Hilbert symbol force the missing current-prefix representation. -/
theorem of_caseIII
    {a : GoodBONG q L (n + 1)} {b : GoodBONG r M (n + 1)}
    {c : GoodBONG s N (n + 1)}
    {i : CentralRepresentationIndex (n + 1) (n + 1)}
    (middlePrevious : DiagonalRepresents
      (b.prefixValues (i.val - 1) i.previous_le_sameRank)
      (a.prefixValues i.val i.current_le_sameRank))
    (sourcePrevious : DiagonalRepresents
      (c.prefixValues (i.val - 2) (by
        have := i.lt_large
        omega))
      (b.prefixValues (i.val - 1) i.previous_le_sameRank))
    (hilbert : hilbertSymbol K
      (b.prefixProduct (i.val - 1) * c.prefixProduct (i.val - 1))
      (-a.prefixProduct i.val * c.prefixProduct (i.val - 2)) = 1) :
    CentralRepresentationCertificate a b c i := by
  apply CentralRepresentationCertificate.direct
  let au := a.prefixValueUnits i.val i.current_le_sameRank
  let bu := b.prefixValueUnits (i.val - 1) i.previous_le_sameRank
  let cu := c.prefixValueUnits (i.val - 1) i.previous_le_sameRank
  have hp : DiagonalRepresents
      (diagonalUnitCoefficients bu)
      (diagonalUnitCoefficients au) := by
    simpa only [au, bu, diagonalUnitCoefficients_prefixValueUnits] using
      middlePrevious
  have hq : DiagonalRepresents
      (diagonalUnitCoefficients
        (diagonalUnitTake cu (i.val - 2) (by omega)))
      (diagonalUnitCoefficients bu) := by
    simpa only [bu, cu, diagonalUnitTake_prefixValueUnits,
      diagonalUnitCoefficients_prefixValueUnits] using sourcePrevious
  have hs : hilbertSymbol K
      (diagonalUnitDeterminant bu * diagonalUnitDeterminant cu)
      (-diagonalUnitDeterminant au *
        diagonalUnitDeterminant
          (diagonalUnitTake cu (i.val - 2) (by omega))) = 1 := by
    simpa only [au, bu, cu, diagonalUnitTake_prefixValueUnits,
      diagonalUnitDeterminant_prefixValueUnits] using hilbert
  have hcycle := DiagonalRepresentationParityLaws.caseIII
    (l := i.val - 2) au bu cu (by
      have := i.one_lt
      omega) rfl (by
        have := i.one_lt
        omega)
  have hr := hcycle.all_triple_consequences.2.1 hp hq hs
  simpa only [au, cu, diagonalUnitCoefficients_prefixValueUnits] using hr

/-! ## Defect-sum entry points used in Section 4 -/

/-- Lemma 1.5(i), with its Hilbert symbol discharged by the two capped
equal-prefix defects occurring in the paper. -/
theorem of_caseI_truncatedDefects
    [HilbertSymbolLaws K]
    {a : GoodBONG q L (n + 1)} {b : GoodBONG r M (n + 1)}
    {c : GoodBONG s N (n + 1)}
    {i : CentralRepresentationIndex (n + 1) (n + 1)}
    (middlePrevious : DiagonalRepresents
      (b.prefixValues (i.val - 1) i.previous_le_sameRank)
      (a.prefixValues i.val i.current_le_sameRank))
    (sourceCurrent : DiagonalRepresents
      (c.prefixValues (i.val - 1) i.previous_le_sameRank)
      (b.prefixValues i.val i.current_le_sameRank))
    (hdefects :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        a.truncatedPrefixDefect b 1 i.val i.val +
          b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1)) :
    CentralRepresentationCertificate a b c i := by
  apply of_caseI middlePrevious sourceCurrent
  apply hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
  apply hdefects.trans_le
  apply add_le_add
  · simpa only [one_mul] using
      (a.truncatedPrefixDefect_le_defect b 1 i.val i.val)
  · simpa only [one_mul] using
      (b.truncatedPrefixDefect_le_defect c 1
        (i.val - 1) (i.val - 1))

/-- Lemma 1.5(ii), with the second displayed factor represented by the
current mixed defect for `(a,c)`. -/
theorem of_caseII_truncatedDefects
    [HilbertSymbolLaws K]
    {a : GoodBONG q L (n + 1)} {b : GoodBONG r M (n + 1)}
    {c : GoodBONG s N (n + 1)}
    {i : CentralRepresentationIndex (n + 1) (n + 1)}
    (middleCurrent : DiagonalRepresents
      (b.prefixValues i.val i.current_le_sameRank)
      (a.prefixValues (i.val + 1) (Nat.succ_le_of_lt i.lt_large)))
    (sourceCurrent : DiagonalRepresents
      (c.prefixValues (i.val - 1) i.previous_le_sameRank)
      (b.prefixValues i.val i.current_le_sameRank))
    (hdefects :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        a.truncatedPrefixDefect b 1 i.val i.val +
          a.centralCurrentDefect c i) :
    CentralRepresentationCertificate a b c i := by
  apply of_caseII middleCurrent sourceCurrent
  apply hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
  apply hdefects.trans_le
  apply add_le_add
  · simpa only [one_mul] using
      (a.truncatedPrefixDefect_le_defect b 1 i.val i.val)
  · unfold centralCurrentDefect
    simpa only [neg_one_mul] using
      (a.truncatedPrefixDefect_le_defect c (-1)
        (i.val + 1) (i.val - 1))

/-- Lemma 1.5(iii), with its Hilbert symbol discharged by the equal-prefix
defect of `(b,c)` and the preceding mixed defect of `(a,c)`. -/
theorem of_caseIII_truncatedDefects
    [HilbertSymbolLaws K]
    {a : GoodBONG q L (n + 1)} {b : GoodBONG r M (n + 1)}
    {c : GoodBONG s N (n + 1)}
    {i : CentralRepresentationIndex (n + 1) (n + 1)}
    (middlePrevious : DiagonalRepresents
      (b.prefixValues (i.val - 1) i.previous_le_sameRank)
      (a.prefixValues i.val i.current_le_sameRank))
    (sourcePrevious : DiagonalRepresents
      (c.prefixValues (i.val - 2) (by
        have := i.lt_large
        omega))
      (b.prefixValues (i.val - 1) i.previous_le_sameRank))
    (hdefects :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1) +
          a.centralPreviousDefect c i) :
    CentralRepresentationCertificate a b c i := by
  apply of_caseIII middlePrevious sourcePrevious
  apply hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
  apply hdefects.trans_le
  apply add_le_add
  · simpa only [one_mul] using
      (b.truncatedPrefixDefect_le_defect c 1
        (i.val - 1) (i.val - 1))
  · unfold centralPreviousDefect
    simpa only [neg_one_mul] using
      (a.truncatedPrefixDefect_le_defect c (-1) i.val (i.val - 2))

end CentralRepresentationCertificate

end BONG.GoodBONG

end Bong
