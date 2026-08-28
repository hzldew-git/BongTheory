/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma719Boundary
import Bong.Bong.Beli2019Lemma719

/-!
# Beli (2019), Lemmas 7.18--7.19: closure from normal forms

The coefficient families and standard forms of Lemma 7.18 discharge every
local field of `Beli2019Lemma719Input`.  Thus Lemma 7.19 is available from
concrete normal-form data alone; no boundary-alpha or prefix-isometry
assumption remains in the public entry point below.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

variable [Beli2006AlphaLaws.{u, v} K]
variable [Beli2009AlphaParityLaws.{u, v} K]
variable [laws : DyadicDiscriminantClassLaws K]

/-- The three explicit normal forms in Lemma 7.18. -/
inductive Beli2019Lemma718NormalForm
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) : Prop where
  | typeI (data : Lemma718TypeINormalForm a b R s) :
      Beli2019Lemma718NormalForm a b R s
  | typeII (data : Lemma718TypeIINormalForm a b R s) :
      Beli2019Lemma718NormalForm a b R s
  | typeIII (data : Lemma718TypeIIINormalForm a b R s) :
      Beli2019Lemma718NormalForm a b R s

/-- The stopping index data shared by all three normal forms. -/
theorem Beli2019Lemma718NormalForm.stopping
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Beli2019Lemma718NormalForm a b R s) :
    Lemma717StoppingData a R s := by
  cases D with
  | typeI data => exact data.stopping
  | typeII data => exact data.stopping
  | typeIII data => exact data.stopping

/-- Type-I normal-form data discharge the two local inputs of Lemma 7.19. -/
theorem Lemma718TypeINormalForm.toLemma719Input
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s) :
    Beli2019Lemma719Input a b R s := by
  exact Beli2019Lemma719Input.typeI D.typeI D.targetValues
    (fun k heven hks hk ↦ D.evenPrefix a b R s k heven hks hk)
    (fun hs ↦ D.boundaryAlpha a b R s hs)

/-- Type-II normal-form data discharge the two local inputs of Lemma 7.19. -/
theorem Lemma718TypeIINormalForm.toLemma719Input
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s) :
    Beli2019Lemma719Input a b R s := by
  exact Beli2019Lemma719Input.typeII D.typeII D.targetValues
    (fun k heven hks hk ↦ D.evenPrefix a b R s k heven hks hk)
    (fun hs ↦ D.boundaryAlpha a b R s hs)

/-- Type-III normal-form data discharge the boundary input; all prefix
isometries are already explicit coordinatewise square changes. -/
theorem Lemma718TypeIIINormalForm.toLemma719Input
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIIINormalForm a b R s) :
    Beli2019Lemma719Input a b R s := by
  exact Beli2019Lemma719Input.typeIII D.typeIII D.targetValues
    (fun hs ↦ D.boundaryAlpha a b R s hs)

/-- Every explicit Lemma 7.18 normal form supplies the complete input of
Lemma 7.19. -/
theorem Beli2019Lemma718NormalForm.toLemma719Input
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Beli2019Lemma718NormalForm a b R s) :
    Beli2019Lemma719Input a b R s := by
  cases D with
  | typeI data => exact data.toLemma719Input a b R s
  | typeII data => exact data.toLemma719Input a b R s
  | typeIII data => exact data.toLemma719Input a b R s

/-- Beli (2019), Lemma 7.19, with every local calculation discharged by
the explicit normal form of Lemma 7.18. -/
theorem beli2019Lemma719_of_normalForm
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Beli2019Lemma718NormalForm a b R s) :
    Beli2019Lemma719Conclusion a b R s :=
  a.beli2019Lemma719 b R s (D.toLemma719Input a b R s)

/-- Every Lemma 7.19 conclusion identifies prefixes beginning at the
common-suffix threshold. -/
theorem Beli2019Lemma719Conclusion.prefixIsometric_of_s_le
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Beli2019Lemma719Conclusion a b R s)
    (k : Nat) (hsk : s ≤ k) (hk : k ≤ n + 3) :
    (a.prefixDiagonalSpace k hk).IsIsometric
      (b.prefixDiagonalSpace k hk) := by
  cases D with
  | typeI _ prefix_isometric _ =>
      exact prefix_isometric k (Or.inl hsk) hk
  | typeII _ prefix_isometric _ =>
      exact prefix_isometric k (Or.inl hsk) hk
  | typeIII _ prefix_isometric _ =>
      exact prefix_isometric k hk

/-- Even prefixes are isometric in every Lemma 7.19 branch. -/
theorem Beli2019Lemma719Conclusion.prefixIsometric_of_even
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Beli2019Lemma719Conclusion a b R s)
    (k : Nat) (heven : Even k) (hk : k ≤ n + 3) :
    (a.prefixDiagonalSpace k hk).IsIsometric
      (b.prefixDiagonalSpace k hk) := by
  cases D with
  | typeI _ prefix_isometric _ =>
      exact prefix_isometric k (Or.inr heven) hk
  | typeII _ prefix_isometric _ =>
      exact prefix_isometric k (Or.inr heven) hk
  | typeIII _ prefix_isometric _ =>
      exact prefix_isometric k hk

/-- The alpha values agree throughout the common suffix. -/
theorem Beli2019Lemma719Conclusion.alphaValue_eq_of_s_le
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Beli2019Lemma719Conclusion a b R s)
    (i : Fin (n + 2)) (hsi : s ≤ i.val) :
    a.alphaValue i = b.alphaValue i := by
  cases D with
  | typeI _ _ alpha_eq => exact alpha_eq i hsi
  | typeII _ _ alpha_eq => exact alpha_eq i hsi
  | typeIII _ _ alpha_eq => exact alpha_eq i hsi

end BONG.GoodBONG

end Bong
