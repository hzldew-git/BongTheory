/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716TypeISMinusTwoRepresentation
import Bong.Bong.Beli2019Lemma716TypeIGeometry

/-!
# Beli (2019), Lemma 7.16(ii): type-I endpoint-tower geometry

At the exceptional boundary both length-`s - 2` prefixes are alternating
endpoint towers at scale `R + 1`.  Lemma 2.19 embeds the comparison tower
in the original prefix, which is the orthogonal sum of the initial
unramified binary block and the constructed tower.  Codimension-two Witt
cancellation therefore forces the two tower determinants into the same
square class.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

variable [Beli2006AlphaLaws.{u, v} K]
variable [laws : DyadicDiscriminantClassLaws K]

/-- Lemma 7.5 arithmetic for a rigid length-`2 * pairs` failure profile. -/
theorem lemma716_typeIIFailureProfile_arithmetic
    (x : GoodBONG q N (n + 3)) (R : Int) (pairs : Nat)
    (hpairs : 0 < pairs) (hInterior : 2 * pairs < n + 3)
    (P : Beli2019Lemma716TypeIIFailureProfile x R (2 * pairs)
      (by omega) hInterior) :
    Lemma75ArithmeticConsequences x
      (⟨0, by omega⟩ : Fin (n + 2))
      (⟨2 * pairs - 2, by omega⟩ : Fin (n + 2)) (R + 1) := by
  let first : Fin (n + 2) := ⟨0, by omega⟩
  let last : Fin (n + 2) := ⟨2 * pairs - 2, by omega⟩
  have hfirstLast : first ≤ last := by
    exact Fin.zero_le last
  have hsegmentEven : Even (last.val - first.val) := by
    exact ⟨pairs - 1, by
      dsimp only [first, last]
      omega⟩
  have hfirstOrder : x.order first.castSucc = R + 1 := by
    have hindex : first.castSucc = (0 : Fin (n + 3)) := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact P.first
  have hterminal : x.order last.succ =
      (R + 1) - 2 * (ramificationIndex K : Int) := by
    have hindex : last.succ =
        (⟨2 * pairs - 1, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      simp only [last, Fin.val_succ, Fin.val_mk]
      omega
    rw [hindex]
    have hlow := P.low
    have hlowIndex :
        (⟨(2 * pairs) - 1, by omega⟩ : Fin (n + 3)) =
          ⟨2 * pairs - 1, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [← hlowIndex, hlow]
    ring
  simpa only [first, last] using
    x.beli2019Lemma75_arithmetic first last (R + 1) hfirstLast
      hsegmentEven hfirstOrder hterminal

/-- Every adjacent pair in a rigid failure prefix has one of the two
unramified endpoint classes. -/
theorem lemma716_typeIIFailureProfile_pairClasses
    (x : GoodBONG q N (n + 3)) (R : Int) (pairs : Nat)
    (hpairs : 0 < pairs) (hInterior : 2 * pairs < n + 3)
    (P : Beli2019Lemma716TypeIIFailureProfile x R (2 * pairs)
      (by omega) hInterior) :
    AlternatingEndpointPairClasses
      (x.prefixValueUnits (2 * pairs) (Nat.le_of_lt hInterior)) := by
  let first : Fin (n + 2) := ⟨0, by omega⟩
  let last : Fin (n + 2) := ⟨2 * pairs - 2, by omega⟩
  have A := x.lemma716_typeIIFailureProfile_arithmetic
    R pairs hpairs hInterior P
  intro t
  let k : Fin (n + 2) := ⟨2 * t.val, by omega⟩
  have hfirstLast : first ≤ last :=
    Fin.zero_le last
  have hsegmentEven : Even (last.val - first.val) := by
    exact ⟨pairs - 1, by dsimp only [first, last]; omega⟩
  have hfirstOrder : x.order first.castSucc = R + 1 := by
    have hindex : first.castSucc = (0 : Fin (n + 3)) := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact P.first
  have hterminal : x.order last.succ =
      (R + 1) - 2 * (ramificationIndex K : Int) := by
    have hindex : last.succ =
        (⟨2 * pairs - 1, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      simp only [last, Fin.val_succ, Fin.val_mk]
      omega
    rw [hindex]
    have hlow : x.order (⟨2 * pairs - 1, by omega⟩ : Fin (n + 3)) =
        R - 2 * (ramificationIndex K : Int) + 1 := by
      simpa only using P.low
    rw [hlow]
    ring
  have hfirstK : first ≤ k := Fin.zero_le k
  have hkLast : k ≤ last :=
    Fin.mk_le_mk.mpr (by
      change 2 * t.val ≤ 2 * pairs - 2
      omega)
  have hkEven : Even (k.val - first.val) := by
    exact ⟨t.val, by dsimp only [k, first]; omega⟩
  have hclasses := x.beli2019Lemma75_pairBlock_endpointClass
    first last k (R + 1) hfirstLast hsegmentEven hfirstOrder hterminal
      hfirstK hkLast hkEven
  have hpair := x.toBONG.adjacentSignedProduct_endpoint_cases
    k.castSucc (Nat.succ_lt_succ k.isLt) hclasses
  simpa only [prefixValueUnits, GoodBONG.valueUnit, k, Fin.castSucc_mk]
    using hpair

/-- All leading entries of a rigid failure tower have order `R + 1`. -/
theorem lemma716_typeIIFailureProfile_leadingOrders
    (x : GoodBONG q N (n + 3)) (R : Int) (pairs : Nat)
    (hpairs : 0 < pairs) (hInterior : 2 * pairs < n + 3)
    (P : Beli2019Lemma716TypeIIFailureProfile x R (2 * pairs)
      (by omega) hInterior) :
    ∀ t : Fin pairs,
      ordUnit K ((x.prefixValueUnits (2 * pairs)
        (Nat.le_of_lt hInterior)) ⟨2 * t.val, by omega⟩) = R + 1 := by
  let first : Fin (n + 2) := ⟨0, by omega⟩
  let last : Fin (n + 2) := ⟨2 * pairs - 2, by omega⟩
  have A := x.lemma716_typeIIFailureProfile_arithmetic
    R pairs hpairs hInterior P
  intro t
  let k : Fin (n + 2) := ⟨2 * t.val, by omega⟩
  have hkOrder := A.even_order k (Fin.zero_le k)
    (Fin.mk_le_mk.mpr (by
      change 2 * t.val ≤ 2 * pairs - 2
      omega))
    ⟨t.val, by dsimp only [k, first]; omega⟩
  calc
    ordUnit K ((x.prefixValueUnits (2 * pairs)
        (Nat.le_of_lt hInterior)) ⟨2 * t.val, by omega⟩) =
        x.order k.castSucc := by
      simpa only [prefixValueUnits, k, GoodBONG.valueUnit,
        Fin.castSucc_mk, GoodBONG.order] using
          (x.toBONG.order_eq_ordUnit k.castSucc).symm
    _ = R + 1 := hkOrder

/-- The constructed type-I prefix of length `s - 2` has the rigid
Lemma 7.5 failure profile used by the endpoint-tower argument. -/
theorem lemma716_typeI_sMinusTwo_sourceProfile
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (hsFour : 4 ≤ s) :
    Beli2019Lemma716TypeIIFailureProfile b R (s - 2)
      (by omega) (by have := D.le_rank; omega) := by
  let zero : Fin (n + 3) := 0
  let high : Fin (n + 3) := ⟨s - 4, by
    have := D.le_rank
    omega⟩
  let low : Fin (n + 3) := ⟨s - 3, by
    have := D.le_rank
    omega⟩
  have hzeroEven : Even zero.val := ⟨0, by simp only [zero, Fin.val_zero]⟩
  have hhighEven : Even high.val := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 2, by dsimp only [high]; omega⟩
  have hlowOdd : Odd low.val := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 2, by dsimp only [low]; omega⟩
  have hzero := a.lemma716_typeI_prefix_order_eq_high b R s D hthird
    hvalues zero (by change 0 < s - 2; omega) hzeroEven
  have hhigh := a.lemma716_typeI_prefix_order_eq_high b R s D hthird
    hvalues high (by change s - 4 < s - 2; omega) hhighEven
  have hlow := a.lemma716_typeI_prefix_order_eq_low b R s D hthird
    hvalues low (by change s - 3 < s - 2; omega) hlowOdd
  refine {
    first := by simpa only [zero] using hzero
    high := ?_
    low := ?_ }
  · have hindex :
        (⟨(s - 2) - 2, by
          have hsRank := D.le_rank
          omega⟩ : Fin (n + 3)) = high := by
      apply Fin.ext
      change (s - 2) - 2 = s - 4
      omega
    simpa only [hindex] using hhigh
  · have hindex :
        (⟨(s - 2) - 1, by
          have hsRank := D.le_rank
          omega⟩ : Fin (n + 3)) = low := by
      apply Fin.ext
      change (s - 2) - 1 = s - 3
      omega
    simpa only [hindex] using hlow

/-- In the exceptional type-I boundary, the two length-`s - 2` prefix
products have the same square class. -/
theorem lemma716_typeI_sMinusTwo_exceptional_prefixProduct_isSquare
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hI : Lemma714IsTypeI a R s)
    (hdiscriminant : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (hsFour : 4 ≤ s)
    (Pcomparison : Beli2019Lemma716TypeIIFailureProfile c R (s - 2)
      (by omega) (by have := D.le_rank; omega)) :
    IsSquare
      (b.prefixProduct (s - 2) * c.prefixProduct (s - 2)) := by
  rcases D.even with ⟨d, hd⟩
  let pairs := d - 1
  have hpairs : 0 < pairs := by dsimp only [pairs]; omega
  have hsEq : s - 2 = 2 * pairs := by dsimp only [pairs]; omega
  have hlengthInterior : 2 * pairs < n + 3 := by
    have := D.le_rank
    omega
  have PsourceRaw := a.lemma716_typeI_sMinusTwo_sourceProfile
    b R s D hthird hvalues hsFour
  have Psource : Beli2019Lemma716TypeIIFailureProfile b R (2 * pairs)
      (by omega) hlengthInterior := by
    simpa only [← hsEq] using PsourceRaw
  have Pcomparison' :
      Beli2019Lemma716TypeIIFailureProfile c R (2 * pairs)
        (by omega) hlengthInterior := by
    simpa only [← hsEq] using Pcomparison
  have hsMinusTwoEven : Even (s - 2) := by
    exact ⟨pairs, by omega⟩
  have hsourceSelf := a.lemma716_typeI_sourcePrefixDefect_ge_twoE
    R s D hfirst hsecond hthird
  have hcomparisonSelf :=
    c.lemma716_typeII_comparisonPrefixDefect_ge_twoE R (s - 2)
      (by omega) (by have := D.le_rank; omega) hsMinusTwoEven Pcomparison
  let theta : Kˣ := (-1) ^ ((s - 2) / 2)
  have htheta : theta * theta = 1 := by
    dsimp only [theta]
    rw [← mul_pow]
    simp
  have hsign : ((-1) * theta) * theta = (-1 : Kˣ) := by
    calc
      ((-1) * theta) * theta = (-1) * (theta * theta) := by ac_rfl
      _ = (-1 : Kˣ) := by rw [htheta]; simp
  have hmixed :
      (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) ≤
        a.truncatedPrefixDefect c (-1) s (s - 2) := by
    exact mixedPrefixDefect_ge_of_selfPrefixDefects a c
      (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ))
      ((-1) * theta) theta (-1) s (s - 2)
      (by simpa only [theta] using hsourceSelf)
      (by simpa only [theta] using hcomparisonSelf) hsign
  have hsourceLast : a.order ⟨s - 1, by
      have := D.le_rank
      omega⟩ = R - 2 * (ramificationIndex K : Int) + 1 := by
    have hplateau := a.beli2019Lemma714_i R s
      D.toLemma714MinimalityData hsFour hthird
    have h := hplateau.low_positions (s - 1) (by omega) (by omega) (by
      rcases D.even with ⟨d', hd'⟩
      exact ⟨d' - 1, by omega⟩)
    simpa only using h
  have hcomparisonLast : c.order ⟨s - 3, by
      have := D.le_rank
      omega⟩ = R - 2 * (ramificationIndex K : Int) + 1 := by
    have hlow := Pcomparison.low
    have hindex :
        (⟨(s - 2) - 1, by omega⟩ : Fin (n + 3)) =
          ⟨s - 3, by omega⟩ := by
      apply Fin.ext
      change (s - 2) - 1 = s - 3
      omega
    rw [hindex] at hlow
    exact hlow
  have hrep := a.lemma716_typeI_sMinusTwo_prefixRepresents c R s D
    hsFour hac hI hsourceLast hcomparisonLast hmixed
  let initial : Fin 2 → Kˣ := a.prefixValueUnits 2 (by
    have := D.le_rank
    omega)
  let source : Fin (2 * pairs) → Kˣ :=
    b.prefixValueUnits (2 * pairs) (Nat.le_of_lt hlengthInterior)
  let comparison : Fin (2 * pairs) → Kˣ :=
    c.prefixValueUnits (2 * pairs) (Nat.le_of_lt hlengthInterior)
  let scale : Kˣ := b.valueUnit (0 : Fin (n + 3))
  have hinitial : IsSquare
      (-(initial 0 * initial 1) * laws.discriminantUnit) := by
    simpa [initial, prefixValueUnits] using
      a.lemma716_initialSignedProduct_mul_discriminant_isSquare
        hdiscriminant
  have hsourceClasses : AlternatingEndpointPairClasses source := by
    simpa only [source] using
      b.lemma716_typeIIFailureProfile_pairClasses R pairs hpairs
        hlengthInterior Psource
  have hcomparisonClasses : AlternatingEndpointPairClasses comparison := by
    simpa only [comparison] using
      c.lemma716_typeIIFailureProfile_pairClasses R pairs hpairs
        hlengthInterior Pcomparison'
  have hscaleOrder : ordUnit K scale = R + 1 := by
    calc
      ordUnit K scale = b.order (0 : Fin (n + 3)) := by
        exact (b.toBONG.order_eq_ordUnit 0).symm
      _ = R + 1 := Psource.first
  have hsourceOrders : ∀ t : Fin pairs,
      ordUnit K (source ⟨2 * t.val, by omega⟩) = ordUnit K scale := by
    intro t
    rw [hscaleOrder]
    simpa only [source] using
      b.lemma716_typeIIFailureProfile_leadingOrders R pairs hpairs
        hlengthInterior Psource t
  have hcomparisonOrders : ∀ t : Fin pairs,
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) = ordUnit K scale := by
    intro t
    rw [hscaleOrder]
    simpa only [comparison] using
      c.lemma716_typeIIFailureProfile_leadingOrders R pairs hpairs
        hlengthInterior Pcomparison' t
  have hinitialOrder : ordUnit K (initial 0) = R := by
    calc
      ordUnit K (initial 0) = a.order (0 : Fin (n + 3)) := by
        exact (a.toBONG.order_eq_ordUnit 0).symm
      _ = R := hfirst
  have hodd : Odd (ordUnit K scale - ordUnit K (initial 0)) := by
    rw [hscaleOrder, hinitialOrder]
    exact ⟨0, by omega⟩
  have hrepUnits : DiagonalRepresents
      (diagonalUnitCoefficients comparison)
      (diagonalUnitCoefficients (Fin.append initial source)) := by
    have hrep' : DiagonalRepresents
        (c.prefixValues (2 * pairs) (Nat.le_of_lt hlengthInterior))
        (a.prefixValues (2 + 2 * pairs) (by
          have := D.le_rank
          omega)) :=
      prefixRepresents_cast c a hsEq (by omega) hrep
    have hcomparisonCoefficients :
        diagonalUnitCoefficients comparison =
          c.prefixValues (2 * pairs) (Nat.le_of_lt hlengthInterior) := by
      simp only [comparison, diagonalUnitCoefficients_prefixValueUnits]
    have hsourceCoefficients :
        diagonalUnitCoefficients (Fin.append initial source) =
          a.prefixValues (2 + 2 * pairs) (by
            have := D.le_rank
            omega) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [initial, diagonalUnitCoefficients, prefixValues,
          prefixValueUnits, GoodBONG.valueUnit, GoodBONG.value]
      · have hj : j.val < s - 2 := by
          rw [hsEq]
          exact j.isLt
        have hvalue := hvalues ⟨j.val, by
          have := D.le_rank
          omega⟩
        rw [lemma714TypeITargetValues_prefix a s D.two_le D.le_rank _ hj]
          at hvalue
        have hindex :
            (⟨j.val + 2, by
              have hjBound := j.isLt
              have hsRank := D.le_rank
              omega⟩ : Fin (n + 3)) =
              ⟨(Fin.natAdd 2 j).val, by
                have hjBound := (Fin.natAdd 2 j).isLt
                have := D.le_rank
                omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_mk, Fin.val_natAdd]
          omega
        have hvalue' := congrArg Units.val hvalue
        rw [hindex] at hvalue'
        simp only [source, diagonalUnitCoefficients, prefixValueUnits,
          prefixValues, GoodBONG.valueUnit, GoodBONG.value,
          Fin.append_right]
        exact hvalue'
    rw [hcomparisonCoefficients, hsourceCoefficients]
    exact hrep'
  have hsquareUnits :=
    alternatingEndpointTower_codimensionTwoDeterminantSquare
      initial source comparison scale hinitial hsourceClasses
        hcomparisonClasses hsourceOrders hcomparisonOrders hodd hrepUnits
  simpa only [source, comparison,
    diagonalUnitDeterminant_prefixValueUnits, ← hsEq] using hsquareUnits

end BONG.GoodBONG

end Bong
