/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma718NormalForms

/-!
# Beli (2019), Lemma 7.18: order profiles of the three normal forms

The explicit coefficient normal forms determine the source and replacement
BONG orders on the modified prefix. These formulas are the arithmetic input
for the representation-condition comparison following Lemma 7.19.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

@[simp]
theorem ordUnit_lemma718CanonicalHigh (R : Int) :
    ordUnit K (lemma718CanonicalHigh (K := K) R) = R := by
  simp [lemma718CanonicalHigh]

@[simp]
theorem ordUnit_lemma718CanonicalLow (R : Int) :
    ordUnit K (lemma718CanonicalLow (K := K) R) =
      R - 2 * (ramificationIndex K : Int) := by
  unfold lemma718CanonicalLow
  rw [ordUnit_neg, ordUnit_uniformizerPowerUnit]

theorem Lemma718TypeINormalForm.sourceOrder_even
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s)
    (i : Fin (n + 3)) (his : i.val < s) (hiEven : Even i.val) :
    a.order i = R := by
  rcases hiEven with ⟨j, hj⟩
  have hsRank := D.stopping.le_rank
  have hij : i.val = 2 * j := by omega
  rcases D.stopping.even with ⟨d, hd⟩
  have hp := D.sourcePair j (by omega)
  have hindex : i = (⟨2 * j, by omega⟩ : Fin (n + 3)) :=
    Fin.ext hij
  have hvalue : a.valueUnit i = lemma718CanonicalHigh (K := K) R := by
    calc
      a.valueUnit i = a.valueUnit ⟨2 * j, by omega⟩ :=
        congrArg a.valueUnit hindex
      _ = lemma718CanonicalHigh (K := K) R := hp.1
  calc
    a.order i = ordUnit K (a.valueUnit i) := a.toBONG.order_eq_ordUnit i
    _ = ordUnit K (lemma718CanonicalHigh (K := K) R) :=
      congrArg (ordUnit K) hvalue
    _ = R := ordUnit_lemma718CanonicalHigh R

theorem Lemma718TypeINormalForm.sourceOrder_odd
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s)
    (i : Fin (n + 3)) (his : i.val < s) (hiOdd : Odd i.val) :
    a.order i = R - 2 * (ramificationIndex K : Int) := by
  rcases hiOdd with ⟨j, hj⟩
  have hsRank := D.stopping.le_rank
  have hp := D.sourcePair j (by omega)
  have hi : i = ⟨2 * j + 1, by omega⟩ := by
    apply Fin.ext
    omega
  calc
    a.order i = ordUnit K (a.valueUnit i) := a.toBONG.order_eq_ordUnit i
    _ = ordUnit K (lemma718CanonicalLow (K := K) R) := by
      rw [hi, hp.2]
    _ = R - 2 * (ramificationIndex K : Int) :=
      ordUnit_lemma718CanonicalLow R

theorem Lemma718TypeINormalForm.targetOrder_even
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s)
    (i : Fin (n + 3)) (his : i.val < s) (hiEven : Even i.val) :
    b.order i = R + 1 := by
  calc
    b.order i = ordUnit K (b.valueUnit i) := b.toBONG.order_eq_ordUnit i
    _ = ordUnit K (lemma718TypeITargetValues a s i) := by rw [D.targetValues]
    _ = a.order i + 1 :=
      ordUnit_lemma718TypeITargetValues_prefix a s i his
    _ = R + 1 := by rw [D.sourceOrder_even a b R s i his hiEven]

theorem Lemma718TypeINormalForm.targetOrder_odd
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s)
    (i : Fin (n + 3)) (his : i.val < s) (hiOdd : Odd i.val) :
    b.order i = R - 2 * (ramificationIndex K : Int) + 1 := by
  calc
    b.order i = ordUnit K (b.valueUnit i) := b.toBONG.order_eq_ordUnit i
    _ = ordUnit K (lemma718TypeITargetValues a s i) := by rw [D.targetValues]
    _ = a.order i + 1 :=
      ordUnit_lemma718TypeITargetValues_prefix a s i his
    _ = R - 2 * (ramificationIndex K : Int) + 1 := by
      rw [D.sourceOrder_odd a b R s i his hiOdd]

theorem Lemma718TypeIINormalForm.sourceOrder_even
    [laws : DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s)
    (i : Fin (n + 3)) (his : i.val < s) (hiEven : Even i.val) :
    a.order i = R := by
  by_cases hiZero : i.val = 0
  · have hi : i = ⟨0, by omega⟩ := Fin.ext hiZero
    calc
      a.order i = ordUnit K (a.valueUnit i) := a.toBONG.order_eq_ordUnit i
      _ = ordUnit K (lemma718CanonicalHigh (K := K) R) := by
        rw [hi, D.initialFirst]
      _ = R := ordUnit_lemma718CanonicalHigh R
  · rcases hiEven with ⟨j, hj⟩
    have hjOne : 1 ≤ j := by omega
    have hsRank := D.stopping.le_rank
    have hij : i.val = 2 * j := by omega
    rcases D.stopping.even with ⟨d, hd⟩
    have hp := D.sourcePair j hjOne (by omega)
    have hindex : i = (⟨2 * j, by omega⟩ : Fin (n + 3)) :=
      Fin.ext hij
    have hvalue : a.valueUnit i = lemma718CanonicalHigh (K := K) R := by
      calc
        a.valueUnit i = a.valueUnit ⟨2 * j, by omega⟩ :=
          congrArg a.valueUnit hindex
        _ = lemma718CanonicalHigh (K := K) R := hp.1
    calc
      a.order i = ordUnit K (a.valueUnit i) := a.toBONG.order_eq_ordUnit i
      _ = ordUnit K (lemma718CanonicalHigh (K := K) R) :=
        congrArg (ordUnit K) hvalue
      _ = R := ordUnit_lemma718CanonicalHigh R

theorem Lemma718TypeIINormalForm.sourceOrder_odd
    [laws : DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s)
    (i : Fin (n + 3)) (his : i.val < s) (hiOdd : Odd i.val) :
    a.order i = R - 2 * (ramificationIndex K : Int) := by
  by_cases hiOne : i.val = 1
  · have hi : i = ⟨1, by omega⟩ := Fin.ext hiOne
    calc
      a.order i = ordUnit K (a.valueUnit i) := a.toBONG.order_eq_ordUnit i
      _ = ordUnit K (-(laws.discriminantUnit *
          uniformizerPowerUnit K
            (R - 2 * (ramificationIndex K : Int)))) := by
        rw [hi, D.initialSecond]
      _ = R - 2 * (ramificationIndex K : Int) := by
        rw [ordUnit_neg, ordUnit_mul,
          (isValuationUnit_iff_ordUnit_eq_zero K laws.discriminantUnit).1
            laws.discriminant_isValuationUnit,
          ordUnit_uniformizerPowerUnit]
        ring
  · rcases hiOdd with ⟨j, hj⟩
    have hjOne : 1 ≤ j := by omega
    have hsRank := D.stopping.le_rank
    have hp := D.sourcePair j hjOne (by omega)
    have hi : i = ⟨2 * j + 1, by omega⟩ := by
      apply Fin.ext
      omega
    calc
      a.order i = ordUnit K (a.valueUnit i) := a.toBONG.order_eq_ordUnit i
      _ = ordUnit K (lemma718CanonicalLow (K := K) R) := by
        rw [hi, hp.2]
      _ = R - 2 * (ramificationIndex K : Int) :=
        ordUnit_lemma718CanonicalLow R

theorem Lemma718TypeIINormalForm.targetOrder_even
    [laws : DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s)
    (i : Fin (n + 3)) (his : i.val < s) (hiEven : Even i.val) :
    b.order i = if i.val < 2 then R else R + 1 := by
  by_cases hiTwo : i.val < 2
  · have hiZero : i.val = 0 := by
      rcases hiEven with ⟨j, hj⟩
      omega
    have hvalue : b.valueUnit i = a.valueUnit i := by
      rw [D.targetValues, lemma718TypeIITargetValues_initial a s i hiTwo]
    rw [if_pos hiTwo]
    calc
      b.order i = ordUnit K (b.valueUnit i) := b.toBONG.order_eq_ordUnit i
      _ = ordUnit K (a.valueUnit i) := congrArg (ordUnit K) hvalue
      _ = a.order i := (a.toBONG.order_eq_ordUnit i).symm
      _ = R := D.sourceOrder_even a b R s i his ⟨0, by omega⟩
  · have hiTwo' : 2 ≤ i.val := by omega
    rw [if_neg hiTwo]
    calc
      b.order i = ordUnit K (b.valueUnit i) := b.toBONG.order_eq_ordUnit i
      _ = ordUnit K (lemma718TypeIITargetValues a s i) := by
        rw [D.targetValues]
      _ = a.order i + 1 :=
        ordUnit_lemma718TypeIITargetValues_changed a s i hiTwo' his
      _ = R + 1 := by rw [D.sourceOrder_even a b R s i his hiEven]

theorem Lemma718TypeIINormalForm.targetOrder_odd
    [laws : DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s)
    (i : Fin (n + 3)) (his : i.val < s) (hiOdd : Odd i.val) :
    b.order i = if i.val < 2 then
      R - 2 * (ramificationIndex K : Int)
    else R - 2 * (ramificationIndex K : Int) + 1 := by
  by_cases hiTwo : i.val < 2
  · have hvalue : b.valueUnit i = a.valueUnit i := by
      rw [D.targetValues, lemma718TypeIITargetValues_initial a s i hiTwo]
    rw [if_pos hiTwo]
    calc
      b.order i = ordUnit K (b.valueUnit i) := b.toBONG.order_eq_ordUnit i
      _ = ordUnit K (a.valueUnit i) := congrArg (ordUnit K) hvalue
      _ = a.order i := (a.toBONG.order_eq_ordUnit i).symm
      _ = R - 2 * (ramificationIndex K : Int) :=
        D.sourceOrder_odd a b R s i his hiOdd
  · have hiTwo' : 2 ≤ i.val := by omega
    rw [if_neg hiTwo]
    calc
      b.order i = ordUnit K (b.valueUnit i) := b.toBONG.order_eq_ordUnit i
      _ = ordUnit K (lemma718TypeIITargetValues a s i) := by
        rw [D.targetValues]
      _ = a.order i + 1 :=
        ordUnit_lemma718TypeIITargetValues_changed a s i hiTwo' his
      _ = R - 2 * (ramificationIndex K : Int) + 1 := by
        rw [D.sourceOrder_odd a b R s i his hiOdd]

theorem Lemma718TypeIIINormalForm.sourceOrder_even
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIIINormalForm a b R s)
    (i : Fin (n + 3)) (his : i.val < s) (hiEven : Even i.val) :
    a.order i = R := by
  rcases hiEven with ⟨j, hj⟩
  have hsRank := D.stopping.le_rank
  have hij : i.val = 2 * j := by omega
  rcases D.stopping.even with ⟨d, hd⟩
  have hp := D.sourcePair j (by omega)
  have hindex : i = (⟨2 * j, by omega⟩ : Fin (n + 3)) :=
    Fin.ext hij
  have hvalue : a.valueUnit i = lemma718CanonicalHigh (K := K) R := by
    calc
      a.valueUnit i = a.valueUnit ⟨2 * j, by omega⟩ :=
        congrArg a.valueUnit hindex
      _ = lemma718CanonicalHigh (K := K) R := hp.1
  calc
    a.order i = ordUnit K (a.valueUnit i) := a.toBONG.order_eq_ordUnit i
    _ = ordUnit K (lemma718CanonicalHigh (K := K) R) :=
      congrArg (ordUnit K) hvalue
    _ = R := ordUnit_lemma718CanonicalHigh R

theorem Lemma718TypeIIINormalForm.sourceOrder_odd
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIIINormalForm a b R s)
    (i : Fin (n + 3)) (his : i.val < s) (hiOdd : Odd i.val) :
    a.order i = R - 2 * (ramificationIndex K : Int) := by
  rcases hiOdd with ⟨j, hj⟩
  have hsRank := D.stopping.le_rank
  have hp := D.sourcePair j (by omega)
  have hi : i = ⟨2 * j + 1, by omega⟩ := by
    apply Fin.ext
    omega
  calc
    a.order i = ordUnit K (a.valueUnit i) := a.toBONG.order_eq_ordUnit i
    _ = ordUnit K (lemma718CanonicalLow (K := K) R) := by
      rw [hi, hp.2]
    _ = R - 2 * (ramificationIndex K : Int) :=
      ordUnit_lemma718CanonicalLow R

theorem Lemma718TypeIIINormalForm.targetOrder_even
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIIINormalForm a b R s)
    (i : Fin (n + 3)) (his : i.val < s) (hiEven : Even i.val) :
    b.order i = R := by
  have hvalue : b.valueUnit i = a.valueUnit i := by
    rw [D.targetValues, lemma718TypeIIITargetValues_even a s i hiEven]
  calc
    b.order i = ordUnit K (b.valueUnit i) := b.toBONG.order_eq_ordUnit i
    _ = ordUnit K (a.valueUnit i) := congrArg (ordUnit K) hvalue
    _ = a.order i := (a.toBONG.order_eq_ordUnit i).symm
    _ = R := D.sourceOrder_even a b R s i his hiEven

theorem Lemma718TypeIIINormalForm.targetOrder_odd
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIIINormalForm a b R s)
    (i : Fin (n + 3)) (his : i.val < s) (hiOdd : Odd i.val) :
    b.order i = R - 2 * (ramificationIndex K : Int) + 2 := by
  calc
    b.order i = ordUnit K (b.valueUnit i) := b.toBONG.order_eq_ordUnit i
    _ = ordUnit K (lemma718TypeIIITargetValues a s i) := by
      rw [D.targetValues]
    _ = a.order i + 2 :=
      ordUnit_lemma718TypeIIITargetValues_changed a s i his hiOdd
    _ = R - 2 * (ramificationIndex K : Int) + 2 := by
      rw [D.sourceOrder_odd a b R s i his hiOdd]

end BONG.GoodBONG

end Bong
