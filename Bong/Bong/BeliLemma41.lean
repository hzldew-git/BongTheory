/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Structural
import Bong.Lattice.MaximalNormSplitting

/-!
# Beli (2003), Lemma 4.1 and Corollary 4.2

The phrase "putting together BONGs" is represented without flattening away
dependent component spaces.  An order-preserving equivalence identifies the
global indices with the lexicographically ordered dependent sum of component
indices, and every global ambient vector is the corresponding component
vector.

`BeliSectionFourLaws` isolates the remaining integral induction in Lemma 4.1
and the endpoint comparison used in Corollary 4.2(ii).  It has no default
instance.  The coordinate statement of Corollary 4.2(i) follows from the
earlier Jordan-coordinate interface.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}

namespace Lattice.OrthogonalDecomposition

/-- The rank of one component of an orthogonal decomposition. -/
noncomputable def componentRank
    (D : Lattice.OrthogonalDecomposition q L t) (i : Fin t) : Nat :=
  finrank K (D.component i).carrier

/-- A choice of a full BONG for every component of a decomposition. -/
def ComponentBONGFamily (D : Lattice.OrthogonalDecomposition q L t) :=
  ∀ i : Fin t,
    BONG (D.component i).carrier (D.component i).space
      (D.component i).lattice (D.componentRank i)

end Lattice.OrthogonalDecomposition

namespace BONG

open Lattice.OrthogonalDecomposition

/-- Lexicographic order on dependent component indices. -/
def ComponentIndexBefore
    (D : Lattice.OrthogonalDecomposition q L t)
    (a b : Σ i : Fin t, Fin (D.componentRank i)) : Prop :=
  a.1.1 < b.1.1 ∨ (a.1 = b.1 ∧ a.2.1 < b.2.1)

/--
The global BONG `b` is obtained by putting together the selected component
BONGs of `D`, in component order.
-/
structure PutTogetherWitness (b : BONG V q L n)
    (D : Lattice.OrthogonalDecomposition q L t)
    (c : D.ComponentBONGFamily) where
  /-- Global positions are exactly the dependent family of component positions. -/
  indexEquiv : Fin n ≃ Σ i : Fin t, Fin (D.componentRank i)
  /-- The equivalence respects global and lexicographic component order. -/
  order_iff : ∀ i j : Fin n,
    i < j ↔ ComponentIndexBefore D (indexEquiv i) (indexEquiv j)
  /-- Each global vector is the corresponding component BONG vector. -/
  ambientVector_eq : ∀ i : Fin n,
    b.ambientVector i =
      ((c (indexEquiv i).1).ambientVector (indexEquiv i).2 : V)

/-- Existence of an exact, order-preserving component concatenation witness. -/
def IsPutTogether (b : BONG V q L n)
    (D : Lattice.OrthogonalDecomposition q L t)
    (c : D.ComponentBONGFamily) : Prop :=
  Nonempty (PutTogetherWitness b D c)

namespace PutTogetherWitness

open Lattice.OrthogonalDecomposition

variable {b : BONG V q L n}
  {D : Lattice.OrthogonalDecomposition q L t}
  {c : D.ComponentBONGFamily}

/-- The component containing a global BONG index. -/
def componentIndex (h : PutTogetherWitness b D c) (i : Fin n) : Fin t :=
  (h.indexEquiv i).1

/-- The local index inside the component containing a global BONG index. -/
def localIndex (h : PutTogetherWitness b D c) (i : Fin n) :
    Fin (D.componentRank (h.componentIndex i)) :=
  (h.indexEquiv i).2

@[simp]
theorem value_eq (h : PutTogetherWitness b D c) (i : Fin n) :
    b.value i = (c (h.componentIndex i)).value (h.localIndex i) := by
  rw [← b.quadratic_ambientVector i]
  rw [← (c (h.componentIndex i)).quadratic_ambientVector (h.localIndex i)]
  change q.quadratic (b.ambientVector i) =
    q.quadratic
      ((c (h.componentIndex i)).ambientVector (h.localIndex i) : V)
  exact congrArg q.quadratic (h.ambientVector_eq i)

@[simp]
theorem order_eq (h : PutTogetherWitness b D c) (i : Fin n) :
    b.order i = (c (h.componentIndex i)).order (h.localIndex i) := by
  apply WithTop.coe_injective
  simp only [BONG.coe_order, h.value_eq]

end PutTogetherWitness

end BONG

/--
The still-local integral induction of Beli's Lemma 4.1, together with the
endpoint comparison in Corollary 4.2(ii).  There is deliberately no global
or default instance.
-/
class BeliSectionFourLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  /-- Lemma 4.1(i): component BONGs concatenate across a maximal norm splitting. -/
  maximalNorm_putTogether
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}
    (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily) :
    ∃ b : BONG V q L (finrank K V),
      b.IsPutTogether M.toOrthogonalDecomposition c
  /-- Lemma 4.1(ii): every BONG of a property-A lattice has a Jordan blocking. -/
  propertyA_putTogether
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) (hL : Lattice.HasJordanPropertyA q L) :
    ∃ (t : Nat) (J : Lattice.JordanDecomposition q L t),
      J.HasPropertyA ∧
        ∃ c : J.toOrthogonalDecomposition.ComponentBONGFamily,
          b.IsPutTogether J.toOrthogonalDecomposition c
  /-- Corollary 4.2(ii): a concatenated maximal-norm BONG is good. -/
  maximalNorm_putTogether_isGood
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}
    (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily)
    (b : BONG V q L n)
    (hb : b.IsPutTogether M.toOrthogonalDecomposition c) : b.IsGood

namespace BONG

open Lattice.OrthogonalDecomposition

/-- Definition 9 is exactly the existing predicate `BONG.IsGood`. -/
theorem beliDefinition9 (b : BONG V q L n) :
    b.IsGood ↔
      ∀ (i : Fin n) (hi : i.1 + 2 < n),
        b.order i ≤ b.order ⟨i.1 + 2, hi⟩ :=
  Iff.rfl

variable [BeliSectionFourLaws.{u, v} K]

/-- Beli (2003), Lemma 4.1(i). -/
theorem beliLemma41_i (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily) :
    ∃ b : BONG V q L (finrank K V),
      b.IsPutTogether M.toOrthogonalDecomposition c :=
  BeliSectionFourLaws.maximalNorm_putTogether M c

/-- Beli (2003), Lemma 4.1(ii). -/
theorem beliLemma41_ii (b : BONG V q L n)
    (hL : Lattice.HasJordanPropertyA q L) :
    ∃ (t : Nat) (J : Lattice.JordanDecomposition q L t),
      J.HasPropertyA ∧
        ∃ c : J.toOrthogonalDecomposition.ComponentBONGFamily,
          b.IsPutTogether J.toOrthogonalDecomposition c :=
  BeliSectionFourLaws.propertyA_putTogether b hL

/-- Beli (2003), Corollary 4.2(ii). -/
theorem beliCorollary42_ii (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily)
    (b : BONG V q L n)
    (hb : b.IsPutTogether M.toOrthogonalDecomposition c) : b.IsGood :=
  BeliSectionFourLaws.maximalNorm_putTogether_isGood M c b hb

end BONG

variable [BONGStructuralLaws.{u, v} K]

/-- Beli (2003), Corollary 4.2(i), in its strict two-step form. -/
theorem BONG.beliCorollary42_i (b : BONG V q L n)
    (hL : Lattice.HasJordanPropertyA q L) : b.HasPropertyA :=
  (Lattice.hasJordanPropertyA_iff_bongHasPropertyA b).mp hL

end Bong
