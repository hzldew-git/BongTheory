/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma83
import Bong.Bong.Beli2009BinaryRemarks
import Bong.Bong.BeliLemmas48To410

/-!
# Beli (2019), Lemma 8.8: the binary branch

This file isolates the rank-two local-space input and proves everything after
it: construction of a good binary BONG, classification back to the original
binary lattice, and replacement of the first binary segment inside a good
BONG of arbitrary rank.

As in Lemma 8.3, the remaining local input returns only an orthogonal basis
certificate.  It is the familiar equivalence between
`(ε, -a₁a₂) = 1` and binary norm representation.
-/

namespace Bong

open Dyadic

universe u v

/-- A purely ambient-space certificate for changing the first value of a
binary good BONG. -/
structure BinaryFirstScalingCertificate
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG.GoodBONG q L 2) (ε : Kˣ) where
  basisData : BONG.OrthogonalBasisData q 2
  firstValue_eq :
    basisData.valueUnit (0 : Fin 2) = ε * b.valueUnit (0 : Fin 2)
  sameOrders : basisData.SameOrders b
  prefixDefectBounds : basisData.PrefixDefectBounds b
  fullComparisonSquare :
    IsSquare (basisData.comparisonPrefixUnit b 2)
  firstAlpha_eq :
    basisData.alphaValue (0 : Fin 1) = b.alphaValue (0 : Fin 1)

/-- The local binary norm-representation step.  The conclusion contains no
lattice: it supplies an orthogonal basis in the same quadratic space with
the comparison data required by Lemma 8.6. -/
class DyadicBinaryFirstScalingLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  exists_basisCertificate
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG.GoodBONG q L 2) (ε : Kˣ)
    (hunit : IsValuationUnit K (ε : K))
    (hdefect : (b.alphaValue (0 : Fin 1) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) ε)
    (hhilbert : hilbertSymbol K ε (b.adjacentProduct 0) = 1) :
    Nonempty (BinaryFirstScalingCertificate b ε)

namespace BinaryFirstScalingCertificate

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- A binary ambient-basis certificate produces a transformed good BONG of
the original binary lattice. -/
theorem exists_transformed
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    {b : BONG.GoodBONG q L 2} {ε : Kˣ}
    (C : BinaryFirstScalingCertificate b ε) :
    ∃ c : BONG.GoodBONG q L 2,
      c.valueUnit (0 : Fin 2) = ε * b.valueUnit (0 : Fin 2) := by
  rcases BONG.OrthogonalBasisData.beli2019Lemma86_i
      b C.basisData C.sameOrders C.prefixDefectBounds
        C.fullComparisonSquare with
    ⟨M, c0, hreal, hgood⟩
  let c : BONG.GoodBONG q M 2 := ⟨c0, hgood⟩
  have horders : b.SameOrders c := by
    intro i
    calc
      b.order i = C.basisData.order i := (C.sameOrders i).symm
      _ = c.order i := C.basisData.order_eq_of_isRealizedBy hreal i
  have halphas : b.SameAlphas c := by
    intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    calc
      b.alphaValue (0 : Fin 1) =
          C.basisData.alphaValue (0 : Fin 1) := C.firstAlpha_eq.symm
      _ = c.alphaValue (0 : Fin 1) :=
        C.basisData.alphaValue_eq_of_isRealizedBy hreal 0
  have hprefix : b.PrefixDefectBounds c :=
    C.basisData.prefixDefectBounds_of_isRealizedBy b hreal
      C.prefixDefectBounds
  have hinternal : b.InternalRepresentationConditions c := by
    intro i hi
    have : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    omega
  have hconditions : ClassificationConditions b c :=
    ⟨horders, halphas, hprefix, hinternal⟩
  have hisometric : Lattice.IsIsometric q q L M :=
    (isometric_iff_classificationConditions
      (QuadraticSpace.isIsometric_refl q) b c).2 hconditions
  rcases hisometric with ⟨f⟩
  let transformed := c.mapLatticeIsometry f.symm
  refine ⟨transformed, ?_⟩
  apply Units.ext
  change (c.toBONG.mapLatticeIsometry f.symm).value 0 =
    ((ε * b.valueUnit 0 : Kˣ) : K)
  rw [BONG.value_mapLatticeIsometry]
  have hvalue := C.basisData.value_eq_of_isRealizedBy hreal (0 : Fin 2)
  have hfirstValue := congrArg Units.val C.firstValue_eq
  change c0.value 0 = ((ε * b.valueUnit 0 : Kˣ) : K)
  rw [← hvalue]
  simpa using hfirstValue

end BinaryFirstScalingCertificate

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- The alpha of the literal first binary coefficient pair. -/
noncomputable def firstBinaryAlpha (b : GoodBONG q L (N + 2)) :
    WithTop ℚ :=
  min (b.halfGapCandidate (0 : Fin (N + 1)))
    (b.leftDefectCandidate (0 : Fin (N + 1)) (0 : Fin (N + 1)))

/-- The rank-two scaling theorem for any multiplier whose defect dominates
the binary alpha.  This is the binary norm-generator statement used in
Lemma 8.14; Lemma 8.8 is its equality-boundary specialization. -/
theorem binary_scaling_of_hilbert_of_alpha_le_defect
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    (b : GoodBONG q L 2) (ε : Kˣ)
    (hunit : IsValuationUnit K (ε : K))
    (hdefect : (b.alphaValue (0 : Fin 1) : WithTop ℚ) ≤
      defectOrder (K := K) ε)
    (hhilbert : hilbertSymbol K ε (b.adjacentProduct 0) = 1) :
    ∃ c : GoodBONG q L 2,
      c.valueUnit (0 : Fin 2) = ε * b.valueUnit (0 : Fin 2) := by
  rcases DyadicBinaryFirstScalingLaws.exists_basisCertificate
      b ε hunit hdefect hhilbert with ⟨C⟩
  exact C.exists_transformed

/-- The equality-boundary rank-two scaling used in Lemma 8.8. -/
theorem beli2019Lemma88_binary_scaling_of_hilbert
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    (b : GoodBONG q L 2) (ε : Kˣ)
    (hunit : IsValuationUnit K (ε : K))
    (hdefect : defectOrder (K := K) ε =
      (b.alphaValue (0 : Fin 1) : WithTop ℚ))
    (hhilbert : hilbertSymbol K ε (b.adjacentProduct 0) = 1) :
    ∃ c : GoodBONG q L 2,
      c.valueUnit (0 : Fin 2) = ε * b.valueUnit (0 : Fin 2) := by
  apply b.binary_scaling_of_hilbert_of_alpha_le_defect ε hunit
    hdefect.symm.le hhilbert

/-- The rank-two conclusion used as the base of Lemma 8.8. -/
theorem beli2019Lemma88_binary_of_hilbert
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    (b : GoodBONG q L 2) (ε : Kˣ)
    (hunit : IsValuationUnit K (ε : K))
    (hdefect : defectOrder (K := K) ε =
      (b.alphaValue (0 : Fin 1) : WithTop ℚ))
    (hhilbert : hilbertSymbol K ε (b.adjacentProduct 0) = 1) :
    Nonempty b.Beli2019FirstValueTransform := by
  rcases b.beli2019Lemma88_binary_scaling_of_hilbert ε hunit hdefect
      hhilbert with ⟨c, hc⟩
  exact ⟨{
    epsilon := ε
    epsilon_isValuationUnit := hunit
    epsilon_defect := hdefect
    transformed := c
    firstValue_eq := hc
  }⟩

/-- The alpha of a binary prefix segment is the explicit first-binary alpha
of the original BONG. -/
theorem firstBinaryAlpha_eq_segmentAlpha
    (b : GoodBONG q L (N + 2))
    (w : BONG.SegmentWitness b.toBONG 0 2 (by omega)) :
    b.firstBinaryAlpha =
      ((w.toGoodBONG b.good).alphaValue (0 : Fin 1) : WithTop ℚ) := by
  let s := w.toGoodBONG b.good
  rw [s.binary_alpha_eq_min_candidates]
  have horder0 : s.order (0 : Fin 2) = b.order (0 : Fin (N + 2)) := by
    change w.bong.order 0 = b.toBONG.order 0
    simpa [BONG.SegmentWitness.sourceIndex] using w.order_eq (0 : Fin 2)
  have horder1 : s.order (1 : Fin 2) = b.order (1 : Fin (N + 2)) := by
    change w.bong.order 1 = b.toBONG.order 1
    simpa [BONG.SegmentWitness.sourceIndex] using w.order_eq (1 : Fin 2)
  have hadjacent : s.adjacentDefect (0 : Fin 1) =
      b.adjacentDefect (0 : Fin (N + 1)) := by
    unfold adjacentDefect adjacentProduct
    have hvalue0 := w.valueUnit_eq (0 : Fin 2)
    have hvalue1 := w.valueUnit_eq (1 : Fin 2)
    change
      defectOrder (K := K) (-(w.bong.valueUnit 0 * w.bong.valueUnit 1)) =
        defectOrder (K := K)
          (-(b.toBONG.valueUnit 0 * b.toBONG.valueUnit 1))
    simpa [BONG.SegmentWitness.sourceIndex] using
      congrArg (defectOrder (K := K))
        (congrArg Neg.neg (congrArg₂ (· * ·) hvalue0 hvalue1))
  have hcastOrder : s.order (0 : Fin 1).castSucc =
      b.order (0 : Fin (N + 1)).castSucc := by
    simpa using horder0
  have hsuccOrder : s.order (0 : Fin 1).succ =
      b.order (0 : Fin (N + 1)).succ := by
    simpa using horder1
  have hhalf :
      b.halfGapCandidate (0 : Fin (N + 1)) =
        s.halfGapCandidate (0 : Fin 1) := by
    unfold halfGapCandidate
    rw [hcastOrder, hsuccOrder]
  have hleft :
      b.leftDefectCandidate (0 : Fin (N + 1)) (0 : Fin (N + 1)) =
        s.leftDefectCandidate (0 : Fin 1) (0 : Fin 1) := by
    unfold leftDefectCandidate
    rw [hcastOrder, hsuccOrder, hadjacent]
  unfold firstBinaryAlpha
  rw [hhalf, hleft]

/-- Replacing the first binary segment lifts the generalized binary scaling
to a good BONG of arbitrary rank. -/
theorem exists_firstValueScaling_of_firstBinaryAlpha
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (b : GoodBONG q L (N + 2)) (ε : Kˣ)
    (hunit : IsValuationUnit K (ε : K))
    (hdefect : (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) ≤
      defectOrder (K := K) ε)
    (hbinary : b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hhilbert : hilbertSymbol K ε (b.adjacentProduct 0) = 1) :
    ∃ transformed : GoodBONG q L (N + 2),
      transformed.valueUnit (0 : Fin (N + 2)) =
        ε * b.valueUnit (0 : Fin (N + 2)) := by
  rcases b.toBONG.exists_segmentWitness 0 2 (by omega) with ⟨w⟩
  let s := w.toGoodBONG b.good
  have hsAlpha :
      (s.alphaValue (0 : Fin 1) : WithTop ℚ) =
        (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
    rw [← b.firstBinaryAlpha_eq_segmentAlpha w, hbinary]
  have hsDefect : (s.alphaValue (0 : Fin 1) : WithTop ℚ) ≤
      defectOrder (K := K) ε := by
    rw [hsAlpha]
    exact hdefect
  have hsHilbert : hilbertSymbol K ε (s.adjacentProduct 0) = 1 := by
    have hvalue0 := w.valueUnit_eq (0 : Fin 2)
    have hvalue1 := w.valueUnit_eq (1 : Fin 2)
    have hadjacent : s.adjacentProduct 0 = b.adjacentProduct 0 := by
      unfold adjacentProduct
      change -(w.bong.valueUnit 0 * w.bong.valueUnit 1) =
        -(b.toBONG.valueUnit 0 * b.toBONG.valueUnit 1)
      simpa [BONG.SegmentWitness.sourceIndex] using
        congrArg Neg.neg (congrArg₂ (· * ·) hvalue0 hvalue1)
    rw [hadjacent]
    exact hhilbert
  rcases s.binary_scaling_of_hilbert_of_alpha_le_defect ε hunit hsDefect
      hsHilbert with ⟨c, hc⟩
  rcases b.toBONG.beliLemma49_ii b.good w c.toBONG c.good with ⟨R⟩
  let transformed : GoodBONG q L (N + 2) := ⟨R.bong, R.good⟩
  have hinside := R.inside_eq (0 : Fin 2)
  have hvalue : transformed.valueUnit (0 : Fin (N + 2)) =
      c.valueUnit (0 : Fin 2) := by
    apply Units.ext
    change R.bong.value 0 = c.toBONG.value 0
    rw [← R.bong.quadratic_ambientVector,
      ← c.toBONG.quadratic_ambientVector]
    change q.quadratic (R.bong.ambientVector 0) =
      q.quadratic (c.toBONG.ambientVector 0 : V)
    have hinside0 : R.bong.ambientVector (0 : Fin (N + 2)) =
        (c.toBONG.ambientVector (0 : Fin 2) : V) := by
      simpa using hinside
    rw [hinside0]
  have hsValue : s.valueUnit (0 : Fin 2) =
      b.valueUnit (0 : Fin (N + 2)) := by
    change w.bong.valueUnit 0 = b.toBONG.valueUnit 0
    simpa [BONG.SegmentWitness.sourceIndex] using
      w.valueUnit_eq (0 : Fin 2)
  refine ⟨transformed, ?_⟩
  calc
    transformed.valueUnit (0 : Fin (N + 2)) =
        c.valueUnit (0 : Fin 2) := hvalue
    _ = ε * s.valueUnit (0 : Fin 2) := hc
    _ = ε * b.valueUnit (0 : Fin (N + 2)) := congrArg (ε * ·) hsValue

/-- Equality-boundary wrapper retaining the multiplier and its exact defect,
as required by the statement of Lemma 8.8. -/
theorem firstValueTransform_of_firstBinaryAlpha
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (b : GoodBONG q L (N + 2)) (ε : Kˣ)
    (hunit : IsValuationUnit K (ε : K))
    (hdefect : defectOrder (K := K) ε =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hbinary : b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hhilbert : hilbertSymbol K ε (b.adjacentProduct 0) = 1) :
    Nonempty b.Beli2019FirstValueTransform := by
  rcases b.exists_firstValueScaling_of_firstBinaryAlpha ε hunit
      hdefect.symm.le hbinary hhilbert with ⟨transformed, hfirst⟩
  exact ⟨{
    epsilon := ε
    epsilon_isValuationUnit := hunit
    epsilon_defect := hdefect
    transformed := transformed
    firstValue_eq := hfirst
  }⟩

end BONG.GoodBONG

end Bong
