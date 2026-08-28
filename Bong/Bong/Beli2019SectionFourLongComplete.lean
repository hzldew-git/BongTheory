/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourLongDefects
import Bong.Bong.Beli2019SectionFourLongOuter

/-!
# Beli (2019), Section 4(iv): complete long certificates

The determinant square class is split into the two outer order branches and
the remaining middle branch.  The nonsquare class is the direct
codimension-two representation.
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

/-- The complete Section 4(iv) certificate at one long index. -/
theorem sectionFourLongCertificate
    [Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.LongRepresentationTrigger c i) :
    LongRepresentationCertificate a b c i := by
  by_cases hsquare : IsSquare
      (-a.prefixProduct (i.val + 1) * c.prefixProduct (i.val - 1))
  · by_cases hleft : a.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
        b.order ⟨i.val - 1, by
          have := i.succ_lt_large
          omega⟩
    · exact a.sectionFourLongCertificate_throughPrevious b c hab hbc i
        htrigger hleft
    · have hleft' : b.order ⟨i.val - 1, by
          have := i.succ_lt_large
          omega⟩ < a.order ⟨i.val + 1, i.succ_lt_large⟩ :=
        lt_of_not_ge hleft
      by_cases hright : b.order ⟨i.val, by
          have := i.succ_lt_large
          omega⟩ ≤ c.order ⟨i.val - 2, by
          have := i.succ_lt_large
          omega⟩
      · exact a.sectionFourLongCertificate_throughNext b c hab hbc i
          htrigger hright
      · have hright' : c.order ⟨i.val - 2, by
            have := i.succ_lt_large
            omega⟩ < b.order ⟨i.val, by
            have := i.succ_lt_large
            omega⟩ := lt_of_not_ge hright
        exact a.sectionFourLongCertificate_throughCurrent b c hab hbc i
          htrigger hleft' hright' hsquare
  · exact a.sectionFourLongCertificate_of_not_negative_determinant_square
      b c i hsquare

/-- All Section 4(iv) certificates. -/
theorem sectionFourLongCertificates
    [Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl) :
    SectionFourLongCertificates a b c where
  certificate i htrigger :=
    a.sectionFourLongCertificate b c hab hbc i htrigger

end BONG.GoodBONG

end Bong
