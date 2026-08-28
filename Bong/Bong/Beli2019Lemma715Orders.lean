/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714

/-!
# Beli (2019), Lemma 7.15: agreement of the orders

This module proves the first assertion of Lemma 7.15.  The paper uses
one-based indices, so its range `i ≥ s + 1` is the range `s ≤ i.val` below.
In the type-I realization that range is literally unchanged.  In the type-II
realization the first entry of the range is the last coefficient of the new
ternary block; its order is unchanged because the auxiliary parameters are
valuation units.  All later entries are again literal suffix coefficients.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

variable [laws : DyadicDiscriminantClassLaws K]

/-- In the type-I realization of Lemma 7.14, every coefficient at or after
the stopping index has the same order as the corresponding source
coefficient. -/
theorem lemma715_typeI_order_eq
    (b : GoodBONG q L (n + 3)) (s : Nat)
    (hsTwo : 2 ≤ s) (hsRank : s ≤ n + 3)
    (result : GoodBONG q M (n + 3))
    (hvalues : ∀ i, result.valueUnit i =
      lemma714TypeITargetValues b s hsTwo hsRank i)
    (i : Fin (n + 3)) (hi : s ≤ i.val) :
    b.order i = result.order i := by
  calc
    b.order i = ordUnit K (b.valueUnit i) :=
      b.toBONG.order_eq_ordUnit i
    _ = ordUnit K (lemma714TypeITargetValues b s hsTwo hsRank i) :=
      congrArg (ordUnit K)
        (lemma714TypeITargetValues_suffix b s hsTwo hsRank i hi).symm
    _ = ordUnit K (result.valueUnit i) :=
      congrArg (ordUnit K) (hvalues i).symm
    _ = result.order i :=
      (result.toBONG.order_eq_ordUnit i).symm

/-- In the type-II realization of Lemma 7.14, every coefficient at or after
the stopping index has the same order as the corresponding source
coefficient.  The equality at the stopping index is the nontrivial boundary
case; strict later indices are the unchanged suffix. -/
theorem lemma715_typeII_order_eq
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hII : Lemma714IsTypeII b R s)
    (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (result : GoodBONG q M (n + 3))
    (hvalues : ∀ i, result.valueUnit i =
      lemma714TypeIITargetValues b s D.two_le
        (Classical.choose hII) ε η i)
    (i : Fin (n + 3)) (hi : s ≤ i.val) :
    b.order i = result.order i := by
  by_cases his : i.val = s
  · let current : Fin (n + 3) := ⟨s, Classical.choose hII⟩
    have hiCurrent : i = current := Fin.ext his
    rw [hiCurrent]
    have hcurrent : b.order current = R + 1 := by
      simpa only [current] using (Classical.choose_spec hII)
    calc
      b.order current = R + 1 := hcurrent
      _ = ordUnit K
          (lemma714TypeIITargetValues b s D.two_le
            (Classical.choose hII) ε η current) := by
        symm
        simpa only [current] using
          (ordUnit_lemma714TypeIITargetValues_two b R s D.two_le
            (Classical.choose hII) (Classical.choose_spec hII)
            ε η hεUnit hηUnit)
      _ = ordUnit K (result.valueUnit current) :=
        congrArg (ordUnit K) (hvalues current).symm
      _ = result.order current :=
        (result.toBONG.order_eq_ordUnit current).symm
  · have hstrict : s < i.val := by omega
    calc
      b.order i = ordUnit K (b.valueUnit i) :=
        b.toBONG.order_eq_ordUnit i
      _ = ordUnit K
          (lemma714TypeIITargetValues b s D.two_le
            (Classical.choose hII) ε η i) :=
        congrArg (ordUnit K)
          (lemma714TypeIITargetValues_suffix b s D.two_le
            (Classical.choose hII) ε η i hstrict).symm
      _ = ordUnit K (result.valueUnit i) :=
        congrArg (ordUnit K) (hvalues i).symm
      _ = result.order i :=
        (result.toBONG.order_eq_ordUnit i).symm

/-- The chosen realization of Lemma 7.14, together with the order agreement
which forms the first assertion of Lemma 7.15. -/
inductive Beli2019Lemma715OrderConclusion
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hnorm : Lattice.normIdeal q L = Lattice.powerIdeal (K := K) R)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.powerIdeal (K := K)
        (R - ramificationIndex K + 1))
    (ε η : Kˣ) : Prop where
  | typeI
      (hI : Lemma714IsTypeI b R s)
      (result : GoodBONG q
        (Lattice.nonNormGeneratorLattice R hnorm hscale) (n + 3))
      (values : ∀ i, result.valueUnit i =
        lemma714TypeITargetValues b s D.two_le D.le_rank i)
      (order_eq : ∀ i, s ≤ i.val → b.order i = result.order i) :
      Beli2019Lemma715OrderConclusion b R s D hnorm hscale ε η
  | typeII
      (hII : Lemma714IsTypeII b R s)
      (result : GoodBONG q
        (Lattice.nonNormGeneratorLattice R hnorm hscale) (n + 3))
      (values : ∀ i, result.valueUnit i =
        lemma714TypeIITargetValues b s D.two_le
          (Classical.choose hII) ε η i)
      (order_eq : ∀ i, s ≤ i.val → b.order i = result.order i) :
      Beli2019Lemma715OrderConclusion b R s D hnorm hscale ε η

/-- Extract the order part of Lemma 7.15 from either realization supplied by
Lemma 7.14. -/
theorem Beli2019Lemma714Realization.toLemma715OrderConclusion
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hnorm : Lattice.normIdeal q L = Lattice.powerIdeal (K := K) R)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.powerIdeal (K := K)
        (R - ramificationIndex K + 1))
    (ε η : Kˣ)
    (H : Beli2019Lemma714Realization b R s D hnorm hscale ε η)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K)) :
    Beli2019Lemma715OrderConclusion b R s D hnorm hscale ε η := by
  cases H with
  | typeI hI result hvalues =>
      exact Beli2019Lemma715OrderConclusion.typeI hI result hvalues
        (fun i hi ↦
          lemma715_typeI_order_eq b s D.two_le D.le_rank result
            hvalues i hi)
  | typeII hII result hvalues =>
      exact Beli2019Lemma715OrderConclusion.typeII hII result hvalues
        (fun i hi ↦
          lemma715_typeII_order_eq b R s D hII ε η hεUnit hηUnit
            result hvalues i hi)

end BONG.GoodBONG

end Bong
