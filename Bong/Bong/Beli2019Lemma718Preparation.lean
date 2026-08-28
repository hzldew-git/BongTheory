/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma717Normalization
import Bong.Bong.Beli2019Lemma718Realization

/-!
# Beli (2019), Lemmas 7.17--7.18: preparation of the source BONG

This file closes the normalization step that precedes the three constructive
realizations of Lemma 7.18.  It converts the trichotomy of Lemma 7.17 into an
exact `Lemma718PreparedSource` on the same lattice and records that the full
BONG order sequence is unchanged.

The only external geometric input is the separately named integral
endpoint-tower normalization interface.  In type III, the discriminant
multiplier is supplied constructively by Beli (2003), paragraph 3.12, after
proving that the boundary parameter has order `2e`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Stopping data depend only on the BONG order sequence. -/
theorem Lemma717StoppingData.transport_order
    {a c : GoodBONG q L (n + 3)} {R : Int} {s : Nat}
    (D : Lemma717StoppingData a R s)
    (horder : ∀ j : Fin (n + 3), c.order j = a.order j) :
    Lemma717StoppingData c R s where
  even := D.even
  two_le := D.two_le
  le_rank := D.le_rank
  terminal := by
    rw [horder]
    exact D.terminal
  maximal := by
    intro hs
    rw [horder]
    exact D.maximal hs

/-- The endpoint-above alternative is invariant under pointwise equality of
the order sequence. -/
theorem lemma717EndpointAbove_transport_order
    {a c : GoodBONG q L (n + 3)} {R : Int} {s : Nat}
    (hend : Lemma717EndpointAbove a R s)
    (horder : ∀ j : Fin (n + 3), c.order j = a.order j) :
    Lemma717EndpointAbove c R s := by
  rcases hend with hwhole | ⟨hs, hnext⟩
  · exact Or.inl hwhole
  · exact Or.inr ⟨hs, by rw [horder]; exact hnext⟩

/-- Type III is invariant under pointwise equality of the order sequence. -/
theorem lemma717IsTypeIII_transport_order
    {a c : GoodBONG q L (n + 3)} {R : Int} {s : Nat}
    (htype : Lemma717IsTypeIII a R s)
    (horder : ∀ j : Fin (n + 3), c.order j = a.order j) :
    Lemma717IsTypeIII c R s := by
  rcases htype with ⟨hs, hnext⟩
  exact ⟨hs, by rw [horder]; exact hnext⟩

/-- An exact normalized prefix identifies its signed prefix product with the
signed determinant of the target coefficient tower. -/
theorem signedEvenPrefixProduct_eq_target
    (c : GoodBONG q L (n + 3)) (pairs : Nat)
    (hbound : 2 * pairs ≤ n + 3) (target : Fin (2 * pairs) → Kˣ)
    (hprefix : ∀ i : Fin (2 * pairs),
      c.valueUnit ⟨i.val, i.isLt.trans_le hbound⟩ = target i) :
    c.toBONG.signedEvenPrefixProduct pairs =
      (-1 : Kˣ) ^ pairs * diagonalUnitDeterminant target := by
  have hvalues : c.prefixValueUnits (2 * pairs) hbound = target := by
    funext i
    exact hprefix i
  calc
    c.toBONG.signedEvenPrefixProduct pairs =
        (-1 : Kˣ) ^ pairs * c.prefixProduct (2 * pairs) := rfl
    _ = (-1 : Kˣ) ^ pairs *
        diagonalUnitDeterminant
          (c.prefixValueUnits (2 * pairs) hbound) := by
      rw [diagonalUnitDeterminant_prefixValueUnits]
    _ = _ := by rw [hvalues]

/-- Exact equality with the canonical tower gives all binary source pairs
required by the type-I and type-III prepared-source constructors. -/
theorem lemma717CanonicalTowerValues_sourcePair
    (c : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData c R s)
    (hprefix : ∀ i : Fin (2 * (s / 2)),
      c.valueUnit ⟨i.val, i.isLt.trans_le (by
        rw [D.two_mul_half]
        exact D.le_rank)⟩ =
        lemma717CanonicalTowerValues (K := K) R (s / 2) i) :
    ∀ (j : Nat) (hj : 2 * j + 1 < s),
      c.valueUnit ⟨2 * j, by
        have hs := D.le_rank
        omega⟩ = lemma718CanonicalHigh (K := K) R ∧
      c.valueUnit ⟨2 * j + 1, by
        have hs := D.le_rank
        omega⟩ = lemma718CanonicalLow (K := K) R := by
  intro j hj
  have hbound : 2 * (s / 2) ≤ n + 3 := by
    rw [D.two_mul_half]
    exact D.le_rank
  have hjEvenBound : 2 * j < 2 * (s / 2) := by
    rw [D.two_mul_half]
    omega
  have hjOddBound : 2 * j + 1 < 2 * (s / 2) := by
    rwa [D.two_mul_half]
  let evenIndex : Fin (2 * (s / 2)) := ⟨2 * j, hjEvenBound⟩
  let oddIndex : Fin (2 * (s / 2)) := ⟨2 * j + 1, hjOddBound⟩
  constructor
  · calc
      c.valueUnit ⟨2 * j, by have hs := D.le_rank; omega⟩ =
          c.valueUnit ⟨evenIndex.val,
            evenIndex.isLt.trans_le hbound⟩ := by rfl
      _ = lemma717CanonicalTowerValues (K := K) R (s / 2)
          evenIndex := hprefix evenIndex
      _ = lemma718CanonicalHigh (K := K) R := by
        apply lemma717CanonicalTowerValues_even
        exact ⟨j, by simp only [evenIndex]; omega⟩
  · calc
      c.valueUnit ⟨2 * j + 1, by have hs := D.le_rank; omega⟩ =
          c.valueUnit ⟨oddIndex.val,
            oddIndex.isLt.trans_le hbound⟩ := by rfl
      _ = lemma717CanonicalTowerValues (K := K) R (s / 2)
          oddIndex := hprefix oddIndex
      _ = lemma718CanonicalLow (K := K) R := by
        apply lemma717CanonicalTowerValues_odd
        exact ⟨j, by simp only [oddIndex]⟩

/-- The first coefficient of the exact type-II tower. -/
theorem lemma717TypeIICanonicalTowerValues_initialFirst
    [DyadicDiscriminantClassLaws K]
    (c : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData c R s)
    (hprefix : ∀ i : Fin (2 * (s / 2)),
      c.valueUnit ⟨i.val, i.isLt.trans_le (by
        rw [D.two_mul_half]
        exact D.le_rank)⟩ =
        lemma717TypeIICanonicalTowerValues (K := K) R (s / 2)
          D.half_pos i) :
    c.valueUnit ⟨0, by omega⟩ = lemma718CanonicalHigh (K := K) R := by
  have hzero := hprefix (⟨0, by
    rw [D.two_mul_half]
    have hsTwo := D.two_le
    omega⟩ : Fin (2 * (s / 2)))
  rw [lemma717TypeIICanonicalTowerValues_zero] at hzero
  exact hzero

/-- The discriminant-twisted second coefficient of the exact type-II tower. -/
theorem lemma717TypeIICanonicalTowerValues_initialSecond
    [laws : DyadicDiscriminantClassLaws K]
    (c : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData c R s)
    (hprefix : ∀ i : Fin (2 * (s / 2)),
      c.valueUnit ⟨i.val, i.isLt.trans_le (by
        rw [D.two_mul_half]
        exact D.le_rank)⟩ =
        lemma717TypeIICanonicalTowerValues (K := K) R (s / 2)
          D.half_pos i) :
    c.valueUnit ⟨1, by omega⟩ =
      -(laws.discriminantUnit * uniformizerPowerUnit K
        (R - 2 * (ramificationIndex K : Int))) := by
  have hone := hprefix (⟨1, by
    rw [D.two_mul_half]
    exact D.two_le⟩ : Fin (2 * (s / 2)))
  rw [lemma717TypeIICanonicalTowerValues_one] at hone
  exact hone

/-- Beyond its first pair, the exact type-II tower consists of canonical
hyperbolic source pairs. -/
theorem lemma717TypeIICanonicalTowerValues_sourcePair
    [DyadicDiscriminantClassLaws K]
    (c : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData c R s)
    (hprefix : ∀ i : Fin (2 * (s / 2)),
      c.valueUnit ⟨i.val, i.isLt.trans_le (by
        rw [D.two_mul_half]
        exact D.le_rank)⟩ =
        lemma717TypeIICanonicalTowerValues (K := K) R (s / 2)
          D.half_pos i) :
    ∀ (j : Nat) (_hjOne : 1 ≤ j) (hj : 2 * j + 1 < s),
      c.valueUnit ⟨2 * j, by
        have hs := D.le_rank
        omega⟩ = lemma718CanonicalHigh (K := K) R ∧
      c.valueUnit ⟨2 * j + 1, by
        have hs := D.le_rank
        omega⟩ = lemma718CanonicalLow (K := K) R := by
  intro j hjOne hj
  have hbound : 2 * (s / 2) ≤ n + 3 := by
    rw [D.two_mul_half]
    exact D.le_rank
  have hjEvenBound : 2 * j < 2 * (s / 2) := by
    rw [D.two_mul_half]
    omega
  have hjOddBound : 2 * j + 1 < 2 * (s / 2) := by
    rwa [D.two_mul_half]
  let evenIndex : Fin (2 * (s / 2)) := ⟨2 * j, hjEvenBound⟩
  let oddIndex : Fin (2 * (s / 2)) := ⟨2 * j + 1, hjOddBound⟩
  constructor
  · calc
      c.valueUnit ⟨2 * j, by have hs := D.le_rank; omega⟩ =
          c.valueUnit ⟨evenIndex.val,
            evenIndex.isLt.trans_le hbound⟩ := by rfl
      _ = lemma717TypeIICanonicalTowerValues (K := K) R (s / 2)
          D.half_pos evenIndex := hprefix evenIndex
      _ = lemma717CanonicalTowerValues (K := K) R (s / 2)
          evenIndex := by
        apply lemma717TypeIICanonicalTowerValues_of_two_le
        simp only [evenIndex]
        omega
      _ = lemma718CanonicalHigh (K := K) R := by
        apply lemma717CanonicalTowerValues_even
        exact ⟨j, by simp only [evenIndex]; omega⟩
  · calc
      c.valueUnit ⟨2 * j + 1, by have hs := D.le_rank; omega⟩ =
          c.valueUnit ⟨oddIndex.val,
            oddIndex.isLt.trans_le hbound⟩ := by rfl
      _ = lemma717TypeIICanonicalTowerValues (K := K) R (s / 2)
          D.half_pos oddIndex := hprefix oddIndex
      _ = lemma717CanonicalTowerValues (K := K) R (s / 2)
          oddIndex := by
        apply lemma717TypeIICanonicalTowerValues_of_two_le
        simp only [oddIndex]
        omega
      _ = lemma718CanonicalLow (K := K) R := by
        apply lemma717CanonicalTowerValues_odd
        exact ⟨j, by simp only [oddIndex]⟩

/-- The exact canonical prefix has square signed determinant. -/
theorem lemma717CanonicalTowerValues_signedPrefix_isSquare
    (c : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData c R s)
    (hprefix : ∀ i : Fin (2 * (s / 2)),
      c.valueUnit ⟨i.val, i.isLt.trans_le (by
        rw [D.two_mul_half]
        exact D.le_rank)⟩ =
        lemma717CanonicalTowerValues (K := K) R (s / 2) i) :
    IsSquare (c.toBONG.signedEvenPrefixProduct (s / 2)) := by
  rw [signedEvenPrefixProduct_eq_target c (s / 2) (by
    rw [D.two_mul_half]
    exact D.le_rank) _ hprefix]
  exact signedDeterminant_lemma717CanonicalTowerValues_isSquare
    (K := K) R (s / 2)

/-- The exact type-II prefix has discriminant-twisted square signed
determinant. -/
theorem lemma717TypeIICanonicalTowerValues_signedPrefix_twisted_isSquare
    [laws : DyadicDiscriminantClassLaws K]
    (c : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData c R s)
    (hprefix : ∀ i : Fin (2 * (s / 2)),
      c.valueUnit ⟨i.val, i.isLt.trans_le (by
        rw [D.two_mul_half]
        exact D.le_rank)⟩ =
        lemma717TypeIICanonicalTowerValues (K := K) R (s / 2)
          D.half_pos i) :
    IsSquare (c.toBONG.signedEvenPrefixProduct (s / 2) *
      laws.discriminantUnit) := by
  rw [signedEvenPrefixProduct_eq_target c (s / 2) (by
    rw [D.two_mul_half]
    exact D.le_rank) _ hprefix]
  exact signedDeterminant_lemma717TypeIICanonicalTowerValues_twisted_isSquare
    (K := K) R (s / 2) D.half_pos

/-- Construct the normalized source required by Lemma 7.18 in all three
branches of Lemma 7.17. -/
theorem exists_lemma718PreparedSource
    [Beli2006AlphaLaws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [BeliCorollary44Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData a R s)
    (hfirst : a.order (0 : Fin (n + 3)) = R) :
    ∃ c : GoodBONG q L (n + 3),
      Lemma718PreparedSource c R s ∧
        ∀ j : Fin (n + 3), c.order j = a.order j := by
  rcases beli2019Lemma717_type_trichotomy a R s D hfirst with
    htypeI | htypeII | htypeIII
  · rcases exists_lemma717TypeINormalizedSource
        a R s D hfirst htypeI with ⟨c, hprefix, hsuffix⟩
    let hbound : 2 * (s / 2) ≤ n + 3 := by
      rw [D.two_mul_half]
      exact D.le_rank
    have horders := lemma717CanonicalTowerValues_orders_match_source
      a R s D hfirst
    have horder : ∀ j : Fin (n + 3), c.order j = a.order j := fun j ↦
      normalizedSplitPrefix_order_eq a c hbound
        (lemma717CanonicalTowerValues (K := K) R (s / 2))
        hprefix hsuffix horders j
    let D' := D.transport_order horder
    have hprefix' : ∀ i : Fin (2 * (s / 2)),
        c.valueUnit ⟨i.val, i.isLt.trans_le (by
          rw [D'.two_mul_half]
          exact D'.le_rank)⟩ =
          lemma717CanonicalTowerValues (K := K) R (s / 2) i := by
      intro i
      simpa only [] using hprefix i
    have hend' := lemma717EndpointAbove_transport_order htypeI.1 horder
    have hsquare' :=
      lemma717CanonicalTowerValues_signedPrefix_isSquare c R s D' hprefix'
    have hpairs := lemma717CanonicalTowerValues_sourcePair c R s D' hprefix'
    exact ⟨c, Lemma718PreparedSource.typeI D'
      ⟨hend', hsquare'⟩ hpairs, horder⟩
  · rcases exists_lemma717TypeIINormalizedSource
        a R s D hfirst htypeII with ⟨c, hprefix, hsuffix⟩
    let hbound : 2 * (s / 2) ≤ n + 3 := by
      rw [D.two_mul_half]
      exact D.le_rank
    have horders := lemma717TypeIICanonicalTowerValues_orders_match_source
      a R s D hfirst
    have horder : ∀ j : Fin (n + 3), c.order j = a.order j := fun j ↦
      normalizedSplitPrefix_order_eq a c hbound
        (lemma717TypeIICanonicalTowerValues (K := K) R (s / 2) D.half_pos)
        hprefix hsuffix horders j
    let D' := D.transport_order horder
    have hprefix' : ∀ i : Fin (2 * (s / 2)),
        c.valueUnit ⟨i.val, i.isLt.trans_le (by
          rw [D'.two_mul_half]
          exact D'.le_rank)⟩ =
          lemma717TypeIICanonicalTowerValues (K := K) R (s / 2)
            D'.half_pos i := by
      intro i
      simpa only [] using hprefix i
    have hend' := lemma717EndpointAbove_transport_order htypeII.1 horder
    have htwisted' :=
      lemma717TypeIICanonicalTowerValues_signedPrefix_twisted_isSquare
        c R s D' hprefix'
    have hzero :=
      lemma717TypeIICanonicalTowerValues_initialFirst c R s D' hprefix'
    have hone :=
      lemma717TypeIICanonicalTowerValues_initialSecond c R s D' hprefix'
    have hpairs :=
      lemma717TypeIICanonicalTowerValues_sourcePair c R s D' hprefix'
    exact ⟨c, Lemma718PreparedSource.typeII D'
      ⟨hend', htwisted'⟩ hzero hone hpairs, horder⟩
  · rcases exists_lemma717TypeIIINormalizedSource
        a R s D hfirst htypeIII with ⟨c, hprefix, horder⟩
    let D' := D.transport_order horder
    have hprefix' : ∀ i : Fin (2 * (s / 2)),
        c.valueUnit ⟨i.val, i.isLt.trans_le (by
          rw [D'.two_mul_half]
          exact D'.le_rank)⟩ =
          lemma717CanonicalTowerValues (K := K) R (s / 2) i := by
      intro i
      simpa only [] using hprefix i
    have htypeIII' := lemma717IsTypeIII_transport_order htypeIII horder
    have hpairs := lemma717CanonicalTowerValues_sourcePair c R s D' hprefix'
    exact ⟨c, Lemma718PreparedSource.typeIII D'
      htypeIII' hpairs, horder⟩

/-- Complete assembly of Lemma 7.18 from an arbitrary source satisfying the
Lemma 7.17 stopping conditions.  The source is first normalized on the same
lattice and then passed to the appropriate constructive realization branch. -/
theorem exists_lemma718NormalizedRealization
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    [unramified : DyadicUnramifiedNormLaws K]
    [corollary44V : BeliCorollary44Laws.{u, v} K]
    [binaryLocal : BinaryNormGeneratorLocalLaws.{u, v} K]
    [lemma49 : BeliLemma49Laws.{u, v} K]
    [defect : QuadraticDefectLaws K]
    [hilbert : HilbertSymbolLaws K]
    [diagonal : DyadicDiagonalClassificationLaws K]
    [perfect : PerfectResidueFieldLaws K]
    [structural : BONGStructuralLaws.{u, u} K]
    [weight : Beli2009WeightIdealData.{u, u} K]
    [unaryBinary : Beli2019UnaryBinaryJordanLaws.{u} K]
    [jordanOrder : Beli2009JordanWeightOrderLaws.{u, u} K]
    [alphaBase : Beli2006AlphaLaws.{u, u} K]
    [constructionBase : BeliLemma43ConstructionLaws.{u, u} K]
    [sectionTwoBase : Beli2006SectionTwoLaws.{u, u} K]
    [classification : GoodBONGClassificationLaws.{u, u, u} K]
    [sectionFourV : BONGReverseDualLaws.{u, v} K]
    [constructionV : BeliLemma43ConstructionLaws.{u, v} K]
    [sectionTwoV : Beli2006SectionTwoLaws.{u, v} K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData a R s)
    (hfirst : a.order (0 : Fin (n + 3)) = R) :
    ∃ c : GoodBONG q L (n + 3),
      (∀ j : Fin (n + 3), c.order j = a.order j) ∧
        Nonempty (Lemma718Realization c R s) := by
  rcases (@exists_lemma718PreparedSource.{u, v}
      K _ _ _ _ _ V _ _ q L n alphaV laws unramified corollary44V
      binaryLocal lemma49 a R s D hfirst) with
    ⟨c, prepared, horder⟩
  exact ⟨c, horder,
    @exists_lemma718Realization.{u, v}
      K _ _ _ _ _ V _ _ q L n corollary44V laws
      defect hilbert diagonal perfect structural weight unaryBinary jordanOrder
      alphaBase constructionBase sectionTwoBase classification
      sectionFourV constructionV sectionTwoV c R s prepared⟩

end BONG.GoodBONG

end Bong
