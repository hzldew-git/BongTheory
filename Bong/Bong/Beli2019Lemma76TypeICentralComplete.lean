/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma76TypeICentral
import Bong.Bong.Beli2019Lemma79EvenSourcePlateau

/-!
# Beli (2019), Lemma 7.6: complete central source prefix

If the first canonical switch is zero, the entire central target interval
is one constant even plateau.  Otherwise the boundary-and-segment theorem
applies.  These branches give one unconditional central source estimate.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The source self-prefix part of Lemma 7.9(ii), case 3, at every strict
central even type-I coordinate. -/
theorem beli2019Lemma76_typeI_central_sourceCapped_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2) (hiEven : Even i.val)
    (hiLeft : C.leftSwitch < i.val)
    (hiRight : i.val ≤ C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int))
    (hbeta : b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by omega⟩) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect b ((-1) ^ (i.val / 2)) 0 i.val := by
  by_cases hleftZero : C.leftSwitch = 0
  · have hplateau := lemma76_typeI_target_even_order_eq_left
      a b D C hfirst i.val hiLeft.le hiRight hiEven
    have hiTwo : 2 ≤ i.val := by
      rcases hiEven with ⟨d, hd⟩
      omega
    apply b.lemma79_even_sourceCapped_of_plateau
      c i hiTwo hiNext hiEven
    · simpa only [hleftZero] using hplateau
    · exact hbeta
  · exact beli2019Lemma76_typeI_central_sourceCapped_of_beta
      a b c D C hfirst (Nat.pos_of_ne_zero hleftZero) i
        hiNext hiEven hiLeft hiRight hcross hbeta

end BONG.GoodBONG

end Bong
