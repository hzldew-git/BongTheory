/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma76TypeICentral
import Bong.Bong.Beli2019Lemma79NormOrder

/-!
# Beli (2019), Lemma 7.9(ii), case 3: the low witness order

In the central type-I interval the current target order is two above the
source norm floor.  The strict norm-ideal inequality puts every even order
of the third BONG at least one above that floor.  Hence a strict domination
witness below the current target order is exactly one step below it.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- A low even domination witness in the central type-I interval has order
exactly one below the current target order. -/
theorem lemma79_typeI_central_lowWitness_order_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiEven : Even i.val) (hiLeft : C.leftSwitch ≤ i.val)
    (hiRight : i.val ≤ C.rightSwitch)
    (j : Fin (n + 1)) (hjEven : Even j.val)
    (hjLow : c.order j.castSucc < b.order ⟨i.val, i.lt_large⟩) :
    c.order j.castSucc = b.order ⟨i.val, i.lt_large⟩ - 1 := by
  have haZero := C.source_to_anchor 0 (Nat.zero_le _) ⟨0, by omega⟩
  have hbLeft := C.target_from_left C.leftSwitch le_rfl
    C.left_le_anchor C.left_even
  have hbPlateau := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst i.val hiLeft hiRight hiEven
  have hbRaw : b.orderSequence.entryOrZero i.val =
      a.orderSequence.entryOrZero 0 + 2 := by
    omega
  have hbOrder : b.order ⟨i.val, i.lt_large⟩ = a.order 0 + 2 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact hbRaw
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  change a.order 0 + 1 ≤ c.order 0 at hnormOrder
  have hcMonotoneRaw := c.orderSequence.entryOrZero_le_of_evenGap
    0 j.val (Nat.zero_le _) (by omega) hjEven
  have hcMonotone : c.order 0 ≤ c.order j.castSucc := by
    rw [← c.orderSequence_entryOrZero_eq_order,
      ← c.orderSequence_entryOrZero_eq_order]
    exact hcMonotoneRaw
  omega

end BONG.GoodBONG

end Bong
