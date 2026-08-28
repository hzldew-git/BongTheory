/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeICentralInduction
import Bong.Bong.Beli2019Lemma69TypeIFromConditions

/-!
# Beli (2019), Lemma 6.9(ii): central type-I values from conditions

For a nonterminal type-I interval, Lemma 6.9(v) supplies every weight
endpoint equality needed by the alternating induction.  The only remaining
inputs are the two left-edge seed values.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The two left-edge values that start the alternating central type-I
induction. -/
structure Lemma69TypeICentralSeedData
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D) : Prop where
  odd (j : RepresentationIndex (n + 2) (n + 2))
      (hj : j.val = C.leftSwitch + 1) :
    a.representationAlpha b j =
      (b.alphaValue ⟨j.val - 1, by
        have hl := j.lt_large
        omega⟩ : WithTop ℚ)
  even (j : RepresentationIndex (n + 2) (n + 2))
      (hj : j.val = C.leftSwitch + 2) :
    a.representationAlpha b j =
      (a.alphaValue ⟨j.val - 1, by
        have hl := j.lt_large
        omega⟩ : WithTop ℚ)

/-- Conditions 2.1(i),(ii) supply the central weight equality, so the two
seed values determine all central type-I values. -/
theorem lemma69_typeI_central_values_of_seeds_from_conditions
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (S : Lemma69TypeICentralSeedData a b D C)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiLeft : C.leftSwitch ≤ i.val - 1)
    (hiRight : i.val - 1 < C.rightSwitch) :
    (Odd i.val → a.representationAlpha b i =
      (b.alphaValue ⟨i.val - 1, by
        have hl := i.lt_large
        omega⟩ : WithTop ℚ)) ∧
    (Even i.val → a.representationAlpha b i =
      (a.alphaValue ⟨i.val - 1, by
        have hl := i.lt_large
        omega⟩ : WithTop ℚ)) := by
  have hweight : ∀ p : Fin (n + 1),
      C.leftSwitch ≤ p.val → p.val < C.rightSwitch →
        a.alphaLeftEndpoint p = b.alphaLeftEndpoint p := by
    intro p hpLeft hpRight
    have h := beli2019Lemma69_v_typeI_of_rightSwitch_lt_last
      a b D C hfirst hrightLast horder hdefect p.val hpLeft hpRight
    simpa only using h
  exact lemma69_typeI_central_values_of_seeds
    a b D C hfirst hdefect hweight S.odd S.even i hiLeft hiRight

/-- The target-beta half of the preceding theorem, stated with the finite
value `A_i` needed by Remark 6.16 and Lemma 7.9(ii). -/
theorem beli2019Lemma69_ii_typeI_targetValue_of_seeds
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (S : Lemma69TypeICentralSeedData a b D C)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val)
    (hiLeft : C.leftSwitch ≤ i.val - 1)
    (hiRight : i.val - 1 < C.rightSwitch) :
    a.representationAlphaValue b i =
      b.alphaValue ⟨i.val - 1, by
        have hl := i.lt_large
        omega⟩ := by
  have hvalue :=
    (lemma69_typeI_central_values_of_seeds_from_conditions
      a b D C hfirst hrightLast horder hdefect S i hiLeft hiRight).1 hodd
  apply WithTop.coe_injective
  rw [a.coe_representationAlphaValue b i]
  exact hvalue

end BONG.GoodBONG

end Bong
