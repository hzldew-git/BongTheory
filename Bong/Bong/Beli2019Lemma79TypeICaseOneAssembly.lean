/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeICaseOneCaps

/-!
# Beli (2019), Lemma 7.9(ii), case 1: square-class assembly

Once the two exceptional prefixes have the same square class, their product
has infinite raw defect.  The two cap estimates then give condition 2.1(ii)
at the exceptional boundary.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- The square-class conclusion in case 1, together with the two prefix-cap
bounds, proves condition 2.1(ii) at the exceptional boundary. -/
theorem beli2019Lemma79_ii_typeI_caseOne_of_prefixProduct_isSquare
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hgap : b.orderGap ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = 2 * (ramificationIndex K : Int) + 1)
    (hprevious : c.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = b.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩)
    (hsquare : IsSquare (b.prefixProduct i.val * c.prefixProduct i.val)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  obtain ⟨hbCap, hcCap⟩ :=
    beli2019Lemma79_typeI_caseOne_prefixCaps b c horderBC i hgap hprevious
  have hsquareRaw : IsSquare
      ((1 : Kˣ) * b.prefixProduct i.val * c.prefixProduct i.val) := by
    simpa only [one_mul] using hsquare
  unfold truncatedPrefixDefect
  rw [defectOrder_eq_top_of_isSquare hsquareRaw]
  simpa using le_min hbCap hcCap

end BONG.GoodBONG

end Bong
