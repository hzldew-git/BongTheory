/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFive
import Bong.Bong.Beli2019Lemma216Complete
import Bong.Bong.Beli2019PrimeChainDecoration

/-!
# Beli (2019), necessity by prime chains

The proof of necessity in the paper factors a same-rank lattice inclusion
into index-`\mathfrak p` steps.  Section 5 proves the four conditions for
each step, and Section 4 composes them.  The inductive certificate below is
that argument literally: every nontrivial constructor exposes one Section 5
datum and every composite constructor exposes the Section 4 datum used at
that junction.

The underlying chain now comes from Smith normal form.  The certificate is
retained as an inspectable proof object, while the main theorem consumes the
proved `Lattice.IndexPChain` directly.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The rank-preserving identity endpoint of a prime chain.  This local datum
is kept separate because a zero-length chain has no Section 5 step. -/
structure Beli2019ReflexiveConditionsData
    (a b : GoodBONG q L (n + 1)) : Prop where
  orderCondition : a.RepresentationOrderCondition b (Nat.le_refl n)
  defectCondition : a.RepresentationDefectCondition b
  centralRepresentations : a.CentralRepresentationConditions b
  longRepresentations : a.LongRepresentationConditions b

namespace Beli2019ReflexiveConditionsData

/-- Assemble the four fields at the identity endpoint. -/
theorem representationConditions
    {a b : GoodBONG q L (n + 1)}
    (D : Beli2019ReflexiveConditionsData a b) :
    RepresentationConditions a b (Nat.le_refl n) where
  orderCondition := D.orderCondition
  defectCondition := D.defectCondition
  centralRepresentations := D.centralRepresentations
  longRepresentations := D.longRepresentations

end Beli2019ReflexiveConditionsData

/-- A finite derivation from a larger lattice to a smaller one.  `prime`
starts a one-step chain; `trans` appends one prime step and records the exact
Section 4 certificates used to compose it with the accumulated result. -/
inductive Beli2019PrimeChainCertificate
    (a : GoodBONG q L (n + 1)) :
    {N : Lattice K V} → GoodBONG q N (n + 1) → Prop
  | refl (b : GoodBONG q L (n + 1))
      (data : Beli2019ReflexiveConditionsData a b) :
      Beli2019PrimeChainCertificate a b
  | prime {N : Lattice K V} (b : GoodBONG q N (n + 1))
      (inclusion : Beli2019IndexPInclusion q L N)
      (data : Beli2019SectionFiveData a b) :
      Beli2019PrimeChainCertificate a b
  | trans {M N : Lattice K V}
      (c : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
      (prior : Beli2019PrimeChainCertificate a c)
      (inclusion : Beli2019IndexPInclusion q M N)
      (stepData : Beli2019SectionFiveData c b)
      (transitivityData : SectionFourTransitivityData a c b) :
      Beli2019PrimeChainCertificate a b

namespace Beli2019PrimeChainCertificate

/-- A prime-chain certificate proves all four original conditions. -/
theorem representationConditions
    [alpha : Beli2006AlphaLaws.{u, v} K]
    {a : GoodBONG q L (n + 1)} {b : GoodBONG q N (n + 1)}
    (C : Beli2019PrimeChainCertificate a b) :
    RepresentationConditions a b (Nat.le_refl n) := by
  induction C with
  | refl b data => exact data.representationConditions
  | prime b inclusion data =>
      exact data.representationConditions a b inclusion
  | trans c b _ inclusion stepData transitivityData ih =>
      exact representationConditions_trans_sameRank a c b ih
        (stepData.representationConditions c b inclusion)
        transitivityData

end Beli2019PrimeChainCertificate

end BONG.GoodBONG

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L N : Lattice K V} {n : Nat}

/-- Sections 4--6: a literal same-rank inclusion satisfies the four
conditions of Theorem 2.1. -/
theorem representationConditions_of_lattice_le
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [HilbertSymbolLaws K] [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [Beli2019SectionFiveLaws.{u, v} K]
    [Beli2019SectionFourLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q N (n + 1))
    (hNL : N ≤ L) :
    RepresentationConditions a b (Nat.le_refl n) :=
  (Lattice.indexPChain_of_le q N L hNL).representationConditions a b

/-- A narrow adapter for consumers that need only the proved necessity
direction for a literal same-space lattice inclusion.  Unlike
`GoodBONGRepresentationLaws`, this interface contains no sufficiency field
and therefore cannot be circular in the Section 9 descent. -/
class Beli2019InclusionConditionsLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  conditions_of_lattice_le
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L N : Lattice K V} {n : Nat}
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q N (n + 1))
    (hNL : N ≤ L) :
    RepresentationConditions a b (Nat.le_refl n)

/-- Sections 4--6 provide the narrow inclusion adapter; no theorem from
Sections 7--9 is used in this instance. -/
noncomputable instance derivedBeli2019InclusionConditionsLaws
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [HilbertSymbolLaws K] [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [Beli2019SectionFiveLaws.{u, v} K]
    [Beli2019SectionFourLaws.{u, v} K] :
    Beli2019InclusionConditionsLaws.{u, v} K where
  conditions_of_lattice_le a b hNL :=
    a.representationConditions_of_lattice_le b hNL

/-- Use the narrow necessity adapter at a concrete inclusion. -/
theorem representationConditions_of_lattice_le_via_adapter
    [Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q N (n + 1))
    (hNL : N ≤ L) :
    RepresentationConditions a b (Nat.le_refl n) :=
  Beli2019InclusionConditionsLaws.conditions_of_lattice_le a b hNL

end BONG.GoodBONG

namespace RepresentationConditions

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- Convert the original four-condition package to the revised v2 package
using Lemma 2.16, rather than assuming a trigger equivalence separately. -/
theorem toPrime
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    {a : BONG.GoodBONG q L (m + 1)}
    {b : BONG.GoodBONG r M (n + 1)} {hRank : n ≤ m}
    (h : RepresentationConditions a b hRank) :
    RepresentationConditionsPrime a b hRank :=
  (representationConditions_iff_prime a b hRank
    (a.beli2019Lemma216 (sourceLaws := sourceLaws)
      (targetLaws := targetLaws) b hRank h.orderCondition
      h.defectCondition)).mp h

end RepresentationConditions

end Bong
