/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma718Values
import Bong.Bong.DiagonalSquareIsometry
import Bong.Bong.Beli2019Lemma715AlphaPropagation

/-!
# Beli (2019), Lemma 7.19

This file proves the common-suffix propagation in Lemma 7.19.  For types I
and II, the remaining local input is exactly the isometry of the even
hyperbolic prefixes and the equality of the boundary alpha.  Type III needs
no prefix input: every changed coefficient differs from the old one by the
explicit square `π²`, so all prefixes are isometric by a coordinate map.

The local even-prefix and boundary-alpha calculations are retained as named
fields of `Beli2019Lemma719Input`; they are discharged from the normal forms
of Lemma 7.18 in the subsequent closure modules.  They are not global law
classes and therefore do not enlarge the trust boundary.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Coordinatewise square changes of BONG values give an explicit isometry
of the associated diagonal prefixes. -/
theorem prefixDiagonalSpace_isIsometric_of_valueUnit_eq_square_mul
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (k : Nat) (hk : k ≤ n + 3)
    (hsquare : ∀ i : Fin k, ∃ u : Kˣ,
      b.valueUnit ⟨i.val, i.isLt.trans_le hk⟩ =
        u ^ 2 * a.valueUnit ⟨i.val, i.isLt.trans_le hk⟩) :
    (a.prefixDiagonalSpace k hk).IsIsometric
      (b.prefixDiagonalSpace k hk) := by
  let units : Fin k → Kˣ := fun i ↦ Classical.choose (hsquare i)
  have hcoeff : ∀ i : Fin k,
      b.prefixValues k hk i = (units i : K) ^ 2 *
        a.prefixValues k hk i := by
    intro i
    have hi := Classical.choose_spec (hsquare i)
    exact congrArg Units.val hi
  apply QuadraticSpace.finiteDiagonal_isIsometric_of_eq_square_mul
    (a.prefixValues k hk) (b.prefixValues k hk)
    (fun i ↦ a.toBONG.value_ne_zero
      ⟨i.val, i.isLt.trans_le hk⟩)
    (fun i ↦ b.toBONG.value_ne_zero
      ⟨i.val, i.isLt.trans_le hk⟩)
    units hcoeff

/-- The two local calculations needed before the common-suffix argument of
Lemma 7.19. -/
inductive Beli2019Lemma719Input
    [DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) : Prop where
  | typeI
      (hI : Lemma717IsTypeI a R s)
      (values : ∀ i, b.valueUnit i = lemma718TypeITargetValues a s i)
      (evenPrefix : ∀ (k : Nat), Even k → k ≤ s →
        (hk : k ≤ n + 3) →
        (a.prefixDiagonalSpace k hk).IsIsometric
          (b.prefixDiagonalSpace k hk))
      (boundaryAlpha : ∀ hs : s < n + 2,
        a.alpha ⟨s, hs⟩ = b.alpha ⟨s, hs⟩) :
      Beli2019Lemma719Input a b R s
  | typeII
      (hII : Lemma717IsTypeII a R s)
      (values : ∀ i, b.valueUnit i = lemma718TypeIITargetValues a s i)
      (evenPrefix : ∀ (k : Nat), Even k → k ≤ s →
        (hk : k ≤ n + 3) →
        (a.prefixDiagonalSpace k hk).IsIsometric
          (b.prefixDiagonalSpace k hk))
      (boundaryAlpha : ∀ hs : s < n + 2,
        a.alpha ⟨s, hs⟩ = b.alpha ⟨s, hs⟩) :
      Beli2019Lemma719Input a b R s
  | typeIII
      (hIII : Lemma717IsTypeIII a R s)
      (values : ∀ i, b.valueUnit i = lemma718TypeIIITargetValues a s i)
      (boundaryAlpha : ∀ hs : s < n + 2,
        a.alpha ⟨s, hs⟩ = b.alpha ⟨s, hs⟩) :
      Beli2019Lemma719Input a b R s

/-- The branchwise statement of Lemma 7.19. -/
inductive Beli2019Lemma719Conclusion
    [DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) : Prop where
  | typeI
      (hI : Lemma717IsTypeI a R s)
      (prefix_isometric : ∀ (k : Nat), s ≤ k ∨ Even k →
        (hk : k ≤ n + 3) →
        (a.prefixDiagonalSpace k hk).IsIsometric
          (b.prefixDiagonalSpace k hk))
      (alpha_eq : ∀ i : Fin (n + 2), s ≤ i.val →
        a.alphaValue i = b.alphaValue i) :
      Beli2019Lemma719Conclusion a b R s
  | typeII
      (hII : Lemma717IsTypeII a R s)
      (prefix_isometric : ∀ (k : Nat), s ≤ k ∨ Even k →
        (hk : k ≤ n + 3) →
        (a.prefixDiagonalSpace k hk).IsIsometric
          (b.prefixDiagonalSpace k hk))
      (alpha_eq : ∀ i : Fin (n + 2), s ≤ i.val →
        a.alphaValue i = b.alphaValue i) :
      Beli2019Lemma719Conclusion a b R s
  | typeIII
      (hIII : Lemma717IsTypeIII a R s)
      (prefix_isometric : ∀ (k : Nat), (hk : k ≤ n + 3) →
        (a.prefixDiagonalSpace k hk).IsIsometric
          (b.prefixDiagonalSpace k hk))
      (alpha_eq : ∀ i : Fin (n + 2), s ≤ i.val →
        a.alphaValue i = b.alphaValue i) :
      Beli2019Lemma719Conclusion a b R s

variable [Beli2006AlphaLaws.{u, v} K]

private theorem lemma719_alphaValue_eq_of_boundary_of_suffix
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (s : Nat)
    (hboundary : ∀ hs : s < n + 2,
      a.alpha ⟨s, hs⟩ = b.alpha ⟨s, hs⟩)
    (htail : ∀ j : Fin (n + 3), s < j.val →
      a.valueUnit j = b.valueUnit j)
    (i : Fin (n + 2)) (hsi : s ≤ i.val) :
    a.alphaValue i = b.alphaValue i := by
  have hsBound : s < n + 2 := hsi.trans_lt i.isLt
  have hraw : a.alpha i = b.alpha i := by
    by_cases his : i.val = s
    · have hi : i = (⟨s, hsBound⟩ : Fin (n + 2)) := Fin.ext his
      simpa only [hi] using hboundary hsBound
    · have hstrict : s < i.val := by omega
      exact a.alpha_eq_of_lemma715_boundary_alpha_eq_of_strict_tail
        b s hsBound i hstrict (hboundary hsBound) htail
  apply WithTop.coe_injective
  rw [a.coe_alphaValue, b.coe_alphaValue]
  exact hraw

/-- Beli (2019), Lemma 7.19, once the two local calculations displayed in
its proof have been supplied by Lemma 7.18's normal forms. -/
theorem beli2019Lemma719
    [laws : DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Beli2019Lemma719Input a b R s) :
    Beli2019Lemma719Conclusion a b R s := by
  cases D with
  | typeI hI hvalues heven hboundary =>
      have htail : ∀ j : Fin (n + 3), s ≤ j.val →
          a.valueUnit j = b.valueUnit j := by
        intro j hj
        exact (lemma718_typeI_realized_suffix a b s hvalues j hj).symm
      refine Beli2019Lemma719Conclusion.typeI hI ?_ ?_
      · intro k hkinds hk
        rcases hkinds with hsk | hkeven
        · apply prefixDiagonalSpace_isIsometric_of_suffix_valueUnit_eq
          intro i hki
          exact htail i (hsk.trans hki)
        · by_cases hks : k ≤ s
          · exact heven k hkeven hks hk
          · apply prefixDiagonalSpace_isIsometric_of_suffix_valueUnit_eq
            intro i hki
            exact htail i (by omega)
      · intro i hsi
        exact lemma719_alphaValue_eq_of_boundary_of_suffix a b s
          hboundary (fun j hj ↦ htail j hj.le) i hsi
  | typeII hII hvalues heven hboundary =>
      have htail : ∀ j : Fin (n + 3), s ≤ j.val →
          a.valueUnit j = b.valueUnit j := by
        intro j hj
        exact (lemma718_typeII_realized_suffix a b s hvalues j hj).symm
      refine Beli2019Lemma719Conclusion.typeII hII ?_ ?_
      · intro k hkinds hk
        rcases hkinds with hsk | hkeven
        · apply prefixDiagonalSpace_isIsometric_of_suffix_valueUnit_eq
          intro i hki
          exact htail i (hsk.trans hki)
        · by_cases hks : k ≤ s
          · exact heven k hkeven hks hk
          · apply prefixDiagonalSpace_isIsometric_of_suffix_valueUnit_eq
            intro i hki
            exact htail i (by omega)
      · intro i hsi
        exact lemma719_alphaValue_eq_of_boundary_of_suffix a b s
          hboundary (fun j hj ↦ htail j hj.le) i hsi
  | typeIII hIII hvalues hboundary =>
      have htail : ∀ j : Fin (n + 3), s ≤ j.val →
          a.valueUnit j = b.valueUnit j := by
        intro j hj
        exact (lemma718_typeIII_realized_suffix a b s hvalues j hj).symm
      refine Beli2019Lemma719Conclusion.typeIII hIII ?_ ?_
      · intro k hk
        apply prefixDiagonalSpace_isIsometric_of_valueUnit_eq_square_mul
        intro i
        let j : Fin (n + 3) := ⟨i.val, i.isLt.trans_le hk⟩
        rcases lemma718TypeIIITargetValues_eq_square_mul a s j with
          ⟨u, hu⟩
        refine ⟨u, ?_⟩
        calc
          b.valueUnit j = lemma718TypeIIITargetValues a s j := hvalues j
          _ = u ^ 2 * a.valueUnit j := hu
      · intro i hsi
        exact lemma719_alphaValue_eq_of_boundary_of_suffix a b s
          hboundary (fun j hj ↦ htail j hj.le) i hsi

end BONG.GoodBONG

end Bong
