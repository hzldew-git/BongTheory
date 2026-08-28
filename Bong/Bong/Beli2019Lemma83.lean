/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma86
import Bong.Bong.Beli2019Lemma88Statement
import Bong.Bong.GoodMap

/-!
# Beli (2019), Lemma 8.3

The lattice-theoretic part of the quaternary scaling lemma is proved here.
The remaining local-field input is deliberately phrased as the existence of
an orthogonal basis in the *ambient quadratic space*.  It does not assert the
existence of a new lattice or of a good BONG.  Lemma 8.6 constructs that
lattice, and the four explicit conditions of Beli's classification theorem
then identify it with the original lattice.

The basis-construction interface `DyadicQuaternaryFirstScalingLaws` is the
precise place where the Hasse-symbol argument and O'Meara 58:3 used in the
printed proof still have to be supplied.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.OrthogonalBasisData

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-! The alpha invariant can be computed before choosing a lattice: it only
uses the orders and adjacent defects of an orthogonal basis. -/

/-- The half-gap candidate attached to an orthogonal basis. -/
noncomputable def halfGapCandidate (X : OrthogonalBasisData q (n + 1))
    (i : Fin n) : WithTop ℚ :=
  (((((X.order i.succ - X.order i.castSucc : Int) : ℚ) / 2 +
    (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ)

/-- A left defect candidate attached to an orthogonal basis. -/
noncomputable def leftDefectCandidate (X : OrthogonalBasisData q (n + 1))
    (i j : Fin n) : WithTop ℚ :=
  (((X.order i.succ - X.order j.castSucc : Int) : ℚ) : WithTop ℚ) +
    X.adjacentDefect j

/-- A right defect candidate attached to an orthogonal basis. -/
noncomputable def rightDefectCandidate (X : OrthogonalBasisData q (n + 1))
    (i j : Fin n) : WithTop ℚ :=
  (((X.order j.succ - X.order i.castSucc : Int) : ℚ) : WithTop ℚ) +
    X.adjacentDefect j

/-- The finite set whose minimum is the alpha invariant of the basis. -/
noncomputable def alphaCandidates (X : OrthogonalBasisData q (n + 1))
    (i : Fin n) : Finset (WithTop ℚ) :=
  insert (X.halfGapCandidate i)
    (((Finset.univ.filter fun j : Fin n => j ≤ i).image
        (X.leftDefectCandidate i)) ∪
      ((Finset.univ.filter fun j : Fin n => i ≤ j).image
        (X.rightDefectCandidate i)))

theorem alphaCandidates_nonempty (X : OrthogonalBasisData q (n + 1))
    (i : Fin n) : (X.alphaCandidates i).Nonempty := by
  exact ⟨X.halfGapCandidate i, Finset.mem_insert_self _ _⟩

/-- The alpha invariant of an orthogonal basis, before lattice realization. -/
noncomputable def alpha (X : OrthogonalBasisData q (n + 1))
    (i : Fin n) : WithTop ℚ :=
  (X.alphaCandidates i).min' (X.alphaCandidates_nonempty i)

theorem alpha_le_halfGapCandidate (X : OrthogonalBasisData q (n + 1))
    (i : Fin n) : X.alpha i ≤ X.halfGapCandidate i :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem alpha_ne_top (X : OrthogonalBasisData q (n + 1))
    (i : Fin n) : X.alpha i ≠ ⊤ := by
  intro htop
  have hle := X.alpha_le_halfGapCandidate i
  rw [htop] at hle
  simp [halfGapCandidate] at hle

/-- The finite rational alpha value of an orthogonal basis. -/
noncomputable def alphaValue (X : OrthogonalBasisData q (n + 1))
    (i : Fin n) : ℚ :=
  (X.alpha i).untop (X.alpha_ne_top i)

@[simp]
theorem coe_alphaValue (X : OrthogonalBasisData q (n + 1))
    (i : Fin n) : (X.alphaValue i : WithTop ℚ) = X.alpha i :=
  WithTop.coe_untop _ _

variable {M : Lattice K V} {X : OrthogonalBasisData q (n + 1)}
  {b : GoodBONG q M (n + 1)}

/-- Realization identifies the bundled nonzero value sequences. -/
theorem valueUnit_eq_of_isRealizedBy
    (h : X.IsRealizedBy b.toBONG) (i : Fin (n + 1)) :
    X.valueUnit i = b.valueUnit i := by
  apply Units.ext
  simpa [GoodBONG.value] using X.value_eq_of_isRealizedBy h i

/-- Realization identifies every adjacent product. -/
theorem adjacentProduct_eq_of_isRealizedBy
    (h : X.IsRealizedBy b.toBONG) (j : Fin n) :
    X.adjacentProduct j = b.adjacentProduct j := by
  unfold adjacentProduct GoodBONG.adjacentProduct
  rw [X.valueUnit_eq_of_isRealizedBy h,
    X.valueUnit_eq_of_isRealizedBy h]

/-- Realization identifies every adjacent defect. -/
theorem adjacentDefect_eq_of_isRealizedBy
    (h : X.IsRealizedBy b.toBONG) (j : Fin n) :
    X.adjacentDefect j = b.adjacentDefect j := by
  unfold adjacentDefect GoodBONG.adjacentDefect
  rw [X.adjacentProduct_eq_of_isRealizedBy h]

/-- Realization identifies the half-gap candidates. -/
theorem halfGapCandidate_eq_of_isRealizedBy
    (h : X.IsRealizedBy b.toBONG) (i : Fin n) :
    X.halfGapCandidate i = b.halfGapCandidate i := by
  unfold halfGapCandidate GoodBONG.halfGapCandidate
  rw [X.order_eq_of_isRealizedBy h,
    X.order_eq_of_isRealizedBy h]
  rfl

/-- Realization identifies the left defect candidates. -/
theorem leftDefectCandidate_eq_of_isRealizedBy
    (h : X.IsRealizedBy b.toBONG) (i j : Fin n) :
    X.leftDefectCandidate i j = b.leftDefectCandidate i j := by
  unfold leftDefectCandidate GoodBONG.leftDefectCandidate
  rw [X.order_eq_of_isRealizedBy h,
    X.order_eq_of_isRealizedBy h,
    X.adjacentDefect_eq_of_isRealizedBy h]
  rfl

/-- Realization identifies the right defect candidates. -/
theorem rightDefectCandidate_eq_of_isRealizedBy
    (h : X.IsRealizedBy b.toBONG) (i j : Fin n) :
    X.rightDefectCandidate i j = b.rightDefectCandidate i j := by
  unfold rightDefectCandidate GoodBONG.rightDefectCandidate
  rw [X.order_eq_of_isRealizedBy h,
    X.order_eq_of_isRealizedBy h,
    X.adjacentDefect_eq_of_isRealizedBy h]
  rfl

/-- Realization identifies the complete alpha-candidate finsets. -/
theorem alphaCandidates_eq_of_isRealizedBy
    (h : X.IsRealizedBy b.toBONG) (i : Fin n) :
    X.alphaCandidates i = b.alphaCandidates i := by
  have hhalf := X.halfGapCandidate_eq_of_isRealizedBy h i
  have hleft : X.leftDefectCandidate i = b.leftDefectCandidate i := by
    funext j
    exact X.leftDefectCandidate_eq_of_isRealizedBy h i j
  have hright : X.rightDefectCandidate i = b.rightDefectCandidate i := by
    funext j
    exact X.rightDefectCandidate_eq_of_isRealizedBy h i j
  unfold alphaCandidates GoodBONG.alphaCandidates
  rw [hhalf, hleft, hright]

/-- Realization identifies the alpha invariants. -/
theorem alpha_eq_of_isRealizedBy
    (h : X.IsRealizedBy b.toBONG) (i : Fin n) :
    X.alpha i = b.alpha i := by
  have hcandidates := X.alphaCandidates_eq_of_isRealizedBy h i
  unfold alpha GoodBONG.alpha
  simpa only [hcandidates]

/-- Realization identifies the finite alpha values. -/
theorem alphaValue_eq_of_isRealizedBy
    (h : X.IsRealizedBy b.toBONG) (i : Fin n) :
    X.alphaValue i = b.alphaValue i := by
  apply WithTop.coe_injective
  rw [X.coe_alphaValue, b.coe_alphaValue,
    X.alpha_eq_of_isRealizedBy h i]

/-- Realization identifies every prefix product. -/
theorem prefixProduct_eq_of_isRealizedBy
    (h : X.IsRealizedBy b.toBONG) (m : Nat) :
    X.prefixProduct m = b.prefixProduct m := by
  classical
  unfold prefixProduct GoodBONG.prefixProduct BONG.prefixProduct
  apply Finset.prod_congr rfl
  intro j _
  exact X.valueUnit_eq_of_isRealizedBy h j

/-- A realized prescribed-basis prefix bound is condition (iii) for the
resulting good BONG. -/
theorem prefixDefectBounds_of_isRealizedBy
    {L : Lattice K V} (a : GoodBONG q L (n + 1))
    (h : X.IsRealizedBy b.toBONG) (hprefix : X.PrefixDefectBounds a) :
    a.PrefixDefectBounds b := by
  intro i
  have hi := hprefix i
  change (a.alphaValue i : WithTop ℚ) ≤
      GoodBONG.defectOrder (K := K)
        (a.prefixProduct (i.1 + 1) * X.prefixProduct (i.1 + 1)) at hi
  change (a.alphaValue i : WithTop ℚ) ≤
      GoodBONG.defectOrder (K := K)
        (a.prefixProduct (i.1 + 1) * b.prefixProduct (i.1 + 1))
  rw [← X.prefixProduct_eq_of_isRealizedBy h]
  exact hi

end BONG.OrthogonalBasisData

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V}

/-- The alternating-order hypothesis `R₁ = R₃`, `R₂ = R₄` in zero-based
form. -/
def HasQuaternaryAlternatingOrders (b : GoodBONG q L 4) : Prop :=
  b.order (0 : Fin 4) = b.order (2 : Fin 4) ∧
    b.order (1 : Fin 4) = b.order (3 : Fin 4)

/-- Under alternating orders, the three left endpoints are equal. -/
theorem alphaLeftEndpoints_eq_of_quaternaryAlternating
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L 4) (h : b.HasQuaternaryAlternatingOrders) :
    b.alphaLeftEndpoint (0 : Fin 3) =
        b.alphaLeftEndpoint (1 : Fin 3) ∧
      b.alphaLeftEndpoint (1 : Fin 3) =
        b.alphaLeftEndpoint (2 : Fin 3) := by
  have h01 := b.alpha_p1 (0 : Fin 3) (by omega)
  have h12 := b.alpha_p1 (1 : Fin 3) (by omega)
  have hleft01 :
      (b.order (0 : Fin 4) : ℚ) + b.alphaValue (0 : Fin 3) ≤
        (b.order (1 : Fin 4) : ℚ) + b.alphaValue (1 : Fin 3) := by
    simpa [alphaLeftEndpoint] using h01.1
  have hleft12 :
      (b.order (1 : Fin 4) : ℚ) + b.alphaValue (1 : Fin 3) ≤
        (b.order (2 : Fin 4) : ℚ) + b.alphaValue (2 : Fin 3) := by
    simpa [alphaLeftEndpoint] using h12.1
  have hright20 :
      -(b.order (3 : Fin 4) : ℚ) + b.alphaValue (2 : Fin 3) ≤
        -(b.order (1 : Fin 4) : ℚ) + b.alphaValue (0 : Fin 3) := by
    have := h12.2.trans h01.2
    simpa [alphaRightEndpoint] using this
  have halpha20 :
      b.alphaValue (2 : Fin 3) ≤ b.alphaValue (0 : Fin 3) := by
    rw [h.2] at hright20
    linarith
  have hleft20 :
      (b.order (2 : Fin 4) : ℚ) + b.alphaValue (2 : Fin 3) ≤
        (b.order (0 : Fin 4) : ℚ) + b.alphaValue (0 : Fin 3) := by
    rw [← h.1]
    linarith
  have hleft02 := hleft01.trans hleft12
  have h02eq := le_antisymm hleft02 hleft20
  constructor
  · unfold alphaLeftEndpoint
    apply le_antisymm hleft01
    exact hleft12.trans hleft20
  · unfold alphaLeftEndpoint
    apply le_antisymm hleft12
    exact hleft20.trans hleft01

/-- Equality of the first alpha and of all four orders forces equality of all
three alphas in the alternating quaternary case. -/
theorem sameAlphas_of_quaternaryAlternating
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4) (b : GoodBONG q M 4)
    (ha : a.HasQuaternaryAlternatingOrders)
    (horders : a.SameOrders b)
    (hfirst : a.alphaValue (0 : Fin 3) = b.alphaValue (0 : Fin 3)) :
    a.SameAlphas b := by
  have hb : b.HasQuaternaryAlternatingOrders := by
    constructor
    · calc
        b.order (0 : Fin 4) = a.order (0 : Fin 4) :=
          (horders 0).symm
        _ = a.order (2 : Fin 4) := ha.1
        _ = b.order (2 : Fin 4) := horders 2
    · calc
        b.order (1 : Fin 4) = a.order (1 : Fin 4) :=
          (horders 1).symm
        _ = a.order (3 : Fin 4) := ha.2
        _ = b.order (3 : Fin 4) := horders 3
  have haEndpoints := a.alphaLeftEndpoints_eq_of_quaternaryAlternating ha
  have hbEndpoints := b.alphaLeftEndpoints_eq_of_quaternaryAlternating hb
  intro i
  fin_cases i
  · exact hfirst
  · change a.alphaValue (1 : Fin 3) = b.alphaValue (1 : Fin 3)
    have ha01 := haEndpoints.1
    have hb01 := hbEndpoints.1
    unfold alphaLeftEndpoint at ha01 hb01
    rw [horders (0 : Fin 3).castSucc,
      horders (1 : Fin 3).castSucc, hfirst] at ha01
    linarith
  · change a.alphaValue (2 : Fin 3) = b.alphaValue (2 : Fin 3)
    have ha02 := haEndpoints.1.trans haEndpoints.2
    have hb02 := hbEndpoints.1.trans hbEndpoints.2
    unfold alphaLeftEndpoint at ha02 hb02
    rw [horders (0 : Fin 3).castSucc,
      horders (2 : Fin 3).castSucc, hfirst] at ha02
    linarith

/-- In the alternating quaternary case, both possible triggers in
classification condition (iv) are ruled out by property P6. -/
theorem internalRepresentationConditions_of_quaternaryAlternating
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4) (b : GoodBONG q M 4)
    (h : a.HasQuaternaryAlternatingOrders) :
    a.InternalRepresentationConditions b := by
  intro i hi htrigger
  exfalso
  fin_cases i
  · simp at hi
  · have hbound := a.alpha_p6 (0 : Fin 3) (by omega) h.1
    change 2 * (ramificationIndex K : ℚ) <
      a.alphaValue (0 : Fin 3) + a.alphaValue (1 : Fin 3) at htrigger
    exact (not_lt_of_ge hbound) htrigger
  · have hbound := a.alpha_p6 (1 : Fin 3) (by omega) h.2
    change 2 * (ramificationIndex K : ℚ) <
      a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) at htrigger
    exact (not_lt_of_ge hbound) htrigger

end BONG.GoodBONG

/-- A checkable, purely ambient-space certificate for the difficult local
construction in Lemma 8.3.  No target lattice is part of this structure. -/
structure QuaternaryFirstScalingCertificate
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG.GoodBONG q L 4) (ε : Kˣ) where
  basisData : BONG.OrthogonalBasisData q 4
  firstValue_eq :
    basisData.valueUnit (0 : Fin 4) = ε * b.valueUnit (0 : Fin 4)
  sameOrders : basisData.SameOrders b
  prefixDefectBounds : basisData.PrefixDefectBounds b
  fullComparisonSquare :
    IsSquare (basisData.comparisonPrefixUnit b 4)
  firstAlpha_eq :
    basisData.alphaValue (0 : Fin 3) = b.alphaValue (0 : Fin 3)

/-- The local four-dimensional scaling construction used by Beli's proof of
Lemma 8.3.  Its conclusion is only an orthogonal-basis certificate; Lemma 8.6
and lattice classification are applied below rather than assumed here. -/
class DyadicQuaternaryFirstScalingLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  exists_basisCertificate
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG.GoodBONG q L 4)
    (halternating : b.HasQuaternaryAlternatingOrders)
    (ε : Kˣ) (hunit : IsValuationUnit K (ε : K))
    (hdefect : (b.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) ε) :
    Nonempty (QuaternaryFirstScalingCertificate b ε)

namespace QuaternaryFirstScalingCertificate

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The ambient-basis certificate produces the good BONG on the original
lattice.  This is the fully formal lattice-theoretic reduction in Lemma 8.3.
-/
theorem exists_transformed
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    {b : BONG.GoodBONG q L 4} {ε : Kˣ}
    (C : QuaternaryFirstScalingCertificate b ε)
    (halternating : b.HasQuaternaryAlternatingOrders) :
    ∃ c : BONG.GoodBONG q L 4,
      c.valueUnit (0 : Fin 4) = ε * b.valueUnit (0 : Fin 4) := by
  rcases BONG.OrthogonalBasisData.beli2019Lemma86_i
      b C.basisData C.sameOrders C.prefixDefectBounds
        C.fullComparisonSquare with
    ⟨M, c0, hreal, hgood⟩
  let c : BONG.GoodBONG q M 4 := ⟨c0, hgood⟩
  have horders : b.SameOrders c := by
    intro i
    calc
      b.order i = C.basisData.order i := (C.sameOrders i).symm
      _ = c.order i := C.basisData.order_eq_of_isRealizedBy hreal i
  have hfirst :
      b.alphaValue (0 : Fin 3) = c.alphaValue (0 : Fin 3) := by
    calc
      b.alphaValue (0 : Fin 3) =
          C.basisData.alphaValue (0 : Fin 3) := C.firstAlpha_eq.symm
      _ = c.alphaValue (0 : Fin 3) :=
        C.basisData.alphaValue_eq_of_isRealizedBy hreal 0
  have halphas : b.SameAlphas c :=
    b.sameAlphas_of_quaternaryAlternating c halternating horders hfirst
  have hprefix : b.PrefixDefectBounds c :=
    C.basisData.prefixDefectBounds_of_isRealizedBy b hreal
      C.prefixDefectBounds
  have hinternal : b.InternalRepresentationConditions c :=
    b.internalRepresentationConditions_of_quaternaryAlternating c
      halternating
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
  have hvalue := C.basisData.value_eq_of_isRealizedBy hreal (0 : Fin 4)
  have hfirstValue := congrArg Units.val C.firstValue_eq
  change c0.value 0 = ((ε * b.valueUnit 0 : Kˣ) : K)
  rw [← hvalue]
  simpa using hfirstValue

end QuaternaryFirstScalingCertificate

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Beli (2019), Lemma 8.3, reduced to its explicit ambient-space scaling
law. -/
theorem beli2019Lemma83
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    (b : GoodBONG q L 4)
    (halternating : b.HasQuaternaryAlternatingOrders)
    (ε : Kˣ) (hunit : IsValuationUnit K (ε : K))
    (hdefect : (b.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
      defectOrder (K := K) ε) :
    ∃ c : GoodBONG q L 4,
      c.valueUnit (0 : Fin 4) = ε * b.valueUnit (0 : Fin 4) := by
  rcases DyadicQuaternaryFirstScalingLaws.exists_basisCertificate
      b halternating ε hunit hdefect with ⟨C⟩
  exact C.exists_transformed halternating

/-- The exact form of Lemma 8.3 needed in the final exceptional branch of
the sufficiency proof of Lemma 8.8. -/
theorem beli2019Lemma83_firstValueTransform
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    (b : GoodBONG q L 4)
    (halternating : b.HasQuaternaryAlternatingOrders)
    (ε : Kˣ) (hunit : IsValuationUnit K (ε : K))
    (hdefect : defectOrder (K := K) ε =
      (b.alphaValue (0 : Fin 3) : WithTop ℚ)) :
    Nonempty b.Beli2019FirstValueTransform := by
  have hbound : (b.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
      defectOrder (K := K) ε := by rw [hdefect]
  rcases b.beli2019Lemma83 halternating ε hunit hbound with ⟨c, hc⟩
  exact ⟨{
    epsilon := ε
    epsilon_isValuationUnit := hunit
    epsilon_defect := hdefect
    transformed := c
    firstValue_eq := hc
  }⟩

end BONG.GoodBONG

end Bong
