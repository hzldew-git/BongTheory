/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrimeIndexChain
import Bong.Bong.Beli2019Lemma310Approximation
import Bong.Bong.GoodExistence
import Bong.Bong.Beli2006SectionThree

/-!
# Beli (2019), decorating a prime-index chain

Smith normal form supplies the finite chain of index-`\mathfrak p`
inclusions required by the necessity argument.  This file separates that
proved lattice-theoretic construction from the remaining mathematical
ingredients: Corollary 3.11 transports the proved identity endpoint, while
Sections 5 and 4 supply one prime step and one composition.
-/

namespace Bong

open Dyadic

universe u v

/-- The order-theoretic part of Section 5, split off from the remaining
three clauses.  This separation is essential: Lemmas 5.7--5.17 use order
necessity for auxiliary nested lattices, while the proof of that necessity
itself only needs the one-step order calculation from Section 5.4. -/
class Beli2019SectionFiveOrderLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  data
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}
    (a : BONG.GoodBONG q M (n + 1))
    (b : BONG.GoodBONG q N (n + 1))
    (inclusion : Beli2019IndexPInclusion q M N) :
    BONG.GoodBONG.Beli2019SectionFiveOrderData a b

/-- A literal index-`\mathfrak p` inclusion carries the Section 5 data used
to prove the four conditions for that one step. -/
class Beli2019SectionFiveLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  data
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}
    (a : BONG.GoodBONG q M (n + 1))
    (b : BONG.GoodBONG q N (n + 1))
    (inclusion : Beli2019IndexPInclusion q M N) :
    BONG.GoodBONG.Beli2019SectionFiveData a b

/-- The complete Section 5 theorem contains, in particular, its independent
order calculation. -/
noncomputable instance sectionFiveOrderLawsOfSectionFiveLaws
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [Beli2019SectionFiveLaws.{u, v} K] :
    Beli2019SectionFiveOrderLaws.{u, v} K where
  data a b inclusion :=
    (Beli2019SectionFiveLaws.data a b inclusion).orderData

/-- The Section 4 certificates needed to compose two already established
same-rank instances of the four representation conditions. -/
class Beli2019SectionFourLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  data
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V}
    {L M N : Lattice K V} {n : Nat}
    (a : BONG.GoodBONG q L (n + 1))
    (b : BONG.GoodBONG q M (n + 1))
    (c : BONG.GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b (Nat.le_refl n))
    (hbc : RepresentationConditions b c (Nat.le_refl n)) :
    BONG.GoodBONG.SectionFourTransitivityData a b c

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Choose a good BONG of the required length on another full lattice in the
same ambient quadratic space. -/
noncomputable def onLattice
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (M : Lattice K V) :
    GoodBONG q M (n + 1) :=
  (GoodBONG.ofLattice q M).castLength
    a.toBONG.length_eq_finrank.symm

end BONG.GoodBONG

namespace Lattice.IndexPChain

open BONG
open BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L N : Lattice K V} {n : Nat}

/-- Decorate a proved lattice-theoretic prime-index chain with the Section 4
and Section 5 arguments, obtaining all four conditions of Theorem 2.1. -/
theorem representationConditions
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [HilbertSymbolLaws K] [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [Beli2019SectionFiveLaws.{u, v} K]
    [Beli2019SectionFourLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q N (n + 1))
    (chain : Lattice.IndexPChain q L N) :
    RepresentationConditions a b (Nat.le_refl n) := by
  induction chain with
  | refl =>
      exact a.representationConditions_sameLattice b
  | step prior next ih =>
      rename_i M N
      let middle : GoodBONG q M (n + 1) := a.onLattice M
      have hab : RepresentationConditions a middle (Nat.le_refl n) :=
        ih middle
      have hbc : RepresentationConditions middle b (Nat.le_refl n) :=
        (Beli2019SectionFiveLaws.data middle b next).representationConditions
          middle b next
      exact representationConditions_trans_sameRank a middle b hab hbc
        (Beli2019SectionFourLaws.data a middle b hab hbc)

/-- The order part of the prime-chain argument needs neither the defect and
representation clauses of Section 5 nor the Section 4 transitivity
certificates.  One-step order certificates compose directly in
`BeliOrderLE`. -/
theorem orderLE
    [BONGStructuralLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [Beli2019SectionFiveOrderLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q N (n + 1))
    (chain : Lattice.IndexPChain q L N) :
    BeliOrderLE a.orderSequence b.orderSequence := by
  induction chain with
  | refl =>
      refine {
        rank := le_rfl
        compare := ?_
      }
      intro i hi
      left
      simpa only [orderSequence_at] using
        (a.order_invariant b ⟨i, hi⟩).le
  | step prior next ih =>
      rename_i M N
      let middle : GoodBONG q M (n + 1) := a.onLattice M
      have ham : BeliOrderLE a.orderSequence middle.orderSequence :=
        ih middle
      have hmb : BeliOrderLE middle.orderSequence b.orderSequence :=
        (Beli2019SectionFiveOrderLaws.data middle b next).certificate.orderLE
      exact BeliOrderLE.trans ham hmb

end Lattice.IndexPChain

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- Once the concrete index-`\mathfrak p` theorem is available, the narrow
order-necessity interface used in Lemmas 5.7--5.17 follows from the proved
Smith prime chain.  This removes it as an independent mathematical law. -/
noncomputable instance derivedBeli2019OrderNecessityLaws
    [BONGStructuralLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [Beli2019SectionFiveOrderLaws.{u, v} K] :
    Beli2019OrderNecessityLaws.{u, v} K where
  nestedOrder a b hLM :=
    (Lattice.indexPChain_of_le _ _ _ hLM).orderLE a b

end BONG.GoodBONG

end Bong
