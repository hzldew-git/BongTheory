/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeICaseOnePrefixClass
import Bong.Bong.Beli2019Lemma79TypeICaseOneParity
import Bong.Bong.Beli2019Lemma79TypeICaseOneCommon
import Bong.Bong.DiagonalUnramifiedExclusion
import Bong.Bong.Beli2019CanonicalApproximation

/-!
# Beli (2019), Lemma 7.9(ii), case 1: excluding the mixed endpoint

The determinant and parity calculations are combined with the generic
unramified exclusion theorem.  The only geometric input is the common
codimension-one subform supplied by the two Lemma 7.5 standard models.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Once both exceptional prefixes are represented by the source prefix and
their Lemma 7.5 models have a common codimension-one subform, the two target
prefix determinants must have the same square class. -/
theorem beli2019Lemma79_typeI_caseOne_prefixProduct_isSquare_of_common
    [Beli2006AlphaLaws.{u, v} K]
    [discriminant : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch)
    (hgap : b.orderGap ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = 2 * (ramificationIndex K : Int) + 1)
    (hprevious : c.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = b.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩)
    (hrepB : DiagonalRepresents
      (b.prefixValues i.val i.lt_large.le)
      (a.prefixValues (i.val + 1) (Nat.succ_le_of_lt i.lt_large)))
    (hrepC : DiagonalRepresents
      (c.prefixValues i.val i.lt_large.le)
      (a.prefixValues (i.val + 1) (Nat.succ_le_of_lt i.lt_large)))
    (hcommon : DiagonalRepresents
      (c.prefixValues (i.val - 1)
        ((Nat.sub_le i.val 1).trans i.lt_large.le))
      (b.prefixValues i.val i.lt_large.le)) :
    IsSquare (b.prefixProduct i.val * c.prefixProduct i.val) := by
  rcases beli2019Lemma79_typeI_caseOne_prefixProduct_cases
      a b c D C hnorm i hleft hgap hprevious with hsquare | hmixed
  · exact hsquare
  · have hiTwo : 2 ≤ i.val := by
      have hiEven : Even i.val := by
        simpa only [hleft] using C.left_even
      have hiPos := i.pos
      rcases hiEven with ⟨d, hd⟩
      omega
    let au := a.prefixValueUnits (i.val + 1)
      (Nat.succ_le_of_lt i.lt_large)
    let bu := b.prefixValueUnits i.val i.lt_large.le
    let cu := c.prefixValueUnits i.val i.lt_large.le
    have hcommonUnits : DiagonalRepresents
        (diagonalUnitCoefficients
          (diagonalUnitTake cu (i.val - 1) (Nat.sub_le i.val 1)))
        (diagonalUnitCoefficients bu) := by
      simpa only [cu, bu, diagonalUnitTake_prefixValueUnits,
        diagonalUnitCoefficients_prefixValueUnits] using hcommon
    have hmixedUnits : IsSquare
        ((diagonalUnitDeterminant bu * diagonalUnitDeterminant cu) *
          discriminant.discriminantUnit) := by
      simpa only [bu, cu, diagonalUnitDeterminant_prefixValueUnits]
        using hmixed
    have hodd := beli2019Lemma79_typeI_caseOne_complementaryProduct_odd
      a b c D C hfirst hnorm i hleft hgap hprevious
    have hoddUnits : Odd (ordUnit K
        (-diagonalUnitDeterminant au *
          diagonalUnitDeterminant
            (diagonalUnitTake cu (i.val - 1)
              (Nat.sub_le i.val 1)))) := by
      simp only [au, cu, diagonalUnitTake_prefixValueUnits,
        diagonalUnitDeterminant_prefixValueUnits]
      have hproduct :
          -a.prefixProduct (i.val + 1) * c.prefixProduct (i.val - 1) =
            (-1 : Kˣ) * a.prefixProduct (i.val + 1) *
              c.prefixProduct (i.val - 1) := by
        apply Units.ext
        simp only [Units.val_mul, Units.val_neg, Units.val_one]
        ring
      rw [hproduct]
      exact hodd
    have hnot := not_both_diagonalRepresented_of_unramified_twist
      au bu cu rfl rfl (by
        have hiPos := i.pos
        omega) hcommonUnits hmixedUnits hoddUnits
    apply False.elim
    apply hnot
    constructor
    · simpa only [bu, au, diagonalUnitCoefficients_prefixValueUnits]
        using hrepB
    · simpa only [cu, au, diagonalUnitCoefficients_prefixValueUnits]
        using hrepC

/-- In case 1 the common codimension-one comparison is supplied directly by
the two Lemma 7.5 endpoint towers. -/
theorem beli2019Lemma79_typeI_caseOne_prefixProduct_isSquare
    [Beli2006AlphaLaws.{u, v} K]
    [discriminant : DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch)
    (hgap : b.orderGap ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = 2 * (ramificationIndex K : Int) + 1)
    (hprevious : c.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = b.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩)
    (hrepB : DiagonalRepresents
      (b.prefixValues i.val i.lt_large.le)
      (a.prefixValues (i.val + 1) (Nat.succ_le_of_lt i.lt_large)))
    (hrepC : DiagonalRepresents
      (c.prefixValues i.val i.lt_large.le)
      (a.prefixValues (i.val + 1) (Nat.succ_le_of_lt i.lt_large))) :
    IsSquare (b.prefixProduct i.val * c.prefixProduct i.val) := by
  apply beli2019Lemma79_typeI_caseOne_prefixProduct_isSquare_of_common
    a b c D C hfirst hnorm i hleft hgap hprevious hrepB hrepC
  exact beli2019Lemma79_typeI_caseOne_commonPrefix
    a b c D C hnorm i hleft hgap hprevious

end BONG.GoodBONG

end Bong
