/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalRepresentationParity
import Bong.Bong.Beli2019Lemma814Invariants
import Bong.Dyadic.UnramifiedNorm

/-!
# Representations between alternating endpoint towers

This file isolates the paper-independent Witt-theoretic fact used for the
alternating towers in Beli's Lemma 7.5.  Each adjacent binary pair is either
hyperbolic or the binary norm form of the distinguished unramified quadratic
extension.  Two towers whose leading coefficients have the same orders have
a common codimension-one diagonal subform.

The statement is kept as a local-field interface until the corresponding
binary Witt-reduction argument is developed in the quadratic-space layer.
-/

namespace Bong

open Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [discriminant : DyadicDiscriminantClassLaws K]

/-- Every adjacent pair in an even diagonal tower has one of the two
unramified endpoint determinant classes. -/
def AlternatingEndpointPairClasses {pairs : Nat}
    (a : Fin (2 * pairs) → Kˣ) : Prop :=
  ∀ t : Fin pairs,
    IsSquare (-(a ⟨2 * t.val, by omega⟩ *
      a ⟨2 * t.val + 1, by omega⟩)) ∨
    IsSquare (-(a ⟨2 * t.val, by omega⟩ *
        a ⟨2 * t.val + 1, by omega⟩) *
      discriminant.discriminantUnit)

/-- Corresponding leading entries of two endpoint towers have equal
valuation.  Lemma 7.5 supplies this stronger form of the parity condition
needed by the unramified norm calculation. -/
def AlternatingEndpointLeadingOrdersAgree {pairs : Nat}
    (a b : Fin (2 * pairs) → Kˣ) : Prop :=
  ∀ t : Fin pairs,
    ordUnit K (a ⟨2 * t.val, by omega⟩) =
      ordUnit K (b ⟨2 * t.val, by omega⟩)

/-- All leading entries of an endpoint tower have the valuation of one
fixed scale.  The applications of Lemma 7.5 use this genuinely stronger
hypothesis: merely matching the corresponding orders of two towers does
not control their Witt classes when the orders vary from pair to pair. -/
def AlternatingEndpointLeadingOrdersAt {pairs : Nat}
    (a : Fin (2 * pairs) → Kˣ) (scale : Kˣ) : Prop :=
  ∀ t : Fin pairs,
    ordUnit K (a ⟨2 * t.val, by omega⟩) = ordUnit K scale

/-- The binary Witt-reduction theorem for alternating endpoint towers.

This is the paper-independent local quadratic-space input: pairs with square
signed determinant are hyperbolic, pairs in the discriminant class are
unramified norm planes, two such norm planes cancel in the Witt group, and
the remaining two binary models have a common line when their scales have
the same valuation parity. -/
class DyadicAlternatingEndpointTowerRepresentationLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [discriminant : DyadicDiscriminantClassLaws K] : Prop where
  commonCodimensionOne
    {pairs : Nat} (a b : Fin (2 * pairs) → Kˣ) (scale : Kˣ)
    (ha : AlternatingEndpointPairClasses a)
    (hb : AlternatingEndpointPairClasses b)
    (haOrders : AlternatingEndpointLeadingOrdersAt a scale)
    (hbOrders : AlternatingEndpointLeadingOrdersAt b scale) :
    DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients
        (diagonalUnitTake b (2 * pairs - 1) (by omega)))
      (BONG.GoodBONG.diagonalUnitCoefficients a)
  /-- Equal-scale endpoint towers with the same determinant square class
  are isometric.  Equivalently, either their binary endpoint classes agree
  pairwise after Witt cancellation, or the two simultaneous class switches
  cancel. -/
  equalDeterminantRepresentation
    {pairs : Nat} (a b : Fin (2 * pairs) → Kˣ) (scale : Kˣ)
    (ha : AlternatingEndpointPairClasses a)
    (hb : AlternatingEndpointPairClasses b)
    (haOrders : AlternatingEndpointLeadingOrdersAt a scale)
    (hbOrders : AlternatingEndpointLeadingOrdersAt b scale)
    (hdet : IsSquare
      (BONG.GoodBONG.diagonalUnitDeterminant a *
        BONG.GoodBONG.diagonalUnitDeterminant b)) :
    DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients b)
      (BONG.GoodBONG.diagonalUnitCoefficients a)
  /-- An endpoint tower with one fewer binary pair, extended by a line at
  the common scale, embeds in the tower with the additional pair.  In the
  Witt group the unmatched endpoint plane supplies a line in either of its
  two possible unramified endpoint classes. -/
  onePairExtensionRepresentation
    {pairs : Nat} (large : Fin (2 * (pairs + 1)) → Kˣ)
    (small : Fin (2 * pairs) → Kˣ) (extra : Kˣ)
    (hlarge : AlternatingEndpointPairClasses large)
    (hsmall : AlternatingEndpointPairClasses small)
    (hlargeOrders : ∀ t : Fin (pairs + 1),
      ordUnit K (large ⟨2 * t.val, by omega⟩) = ordUnit K extra)
    (hsmallOrders : ∀ t : Fin pairs,
      ordUnit K (small ⟨2 * t.val, by omega⟩) = ordUnit K extra) :
    DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients (Fin.snoc small extra))
      (BONG.GoodBONG.diagonalUnitCoefficients large)
  /-- Any endpoint tower at a fixed scale embeds in the unary extension of
  another tower of the same length and scale.  The additional line absorbs
  the possible difference between their two endpoint determinant classes. -/
  representationInUnaryExtension
    {pairs : Nat} (target comparison : Fin (2 * pairs) → Kˣ)
    (extra : Kˣ)
    (htarget : AlternatingEndpointPairClasses target)
    (hcomparison : AlternatingEndpointPairClasses comparison)
    (htargetOrders : ∀ t : Fin pairs,
      ordUnit K (target ⟨2 * t.val, by omega⟩) = ordUnit K extra)
    (hcomparisonOrders : ∀ t : Fin pairs,
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) = ordUnit K extra) :
    DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients comparison)
      (BONG.GoodBONG.diagonalUnitCoefficients (Fin.snoc target extra))
  /-- Removing equal-scale endpoint towers cannot make an odd-order line
  representable by an unramified binary plane.  This is the extension form
  of the same binary Witt reduction as `commonCodimensionOne`. -/
  unaryExtensionExclusion
    {pairs : Nat} (initial : Fin 2 → Kˣ)
    (source comparison : Fin (2 * pairs) → Kˣ) (extra : Kˣ)
    (hinitial : IsSquare
      (-(initial 0 * initial 1) *
        (discriminant.discriminantUnit : Kˣ)))
    (hsource : AlternatingEndpointPairClasses source)
    (hcomparison : AlternatingEndpointPairClasses comparison)
    (hsourceOrders : ∀ t : Fin pairs,
      ordUnit K (source ⟨2 * t.val, by omega⟩) = ordUnit K extra)
    (hcomparisonOrders : ∀ t : Fin pairs,
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) = ordUnit K extra)
    (hodd : Odd (ordUnit K (extra * (initial 0)⁻¹))) :
    ¬ DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients
        (Fin.snoc comparison extra))
      (BONG.GoodBONG.diagonalUnitCoefficients
        (Fin.append initial source))
  /-- An equal-length endpoint tower represented in the orthogonal sum of
  an unramified binary head and a second endpoint tower must have the same
  endpoint determinant class as the latter tower when the two scales have
  odd relative valuation.  This is the codimension-two Witt cancellation
  used in Beli's Lemma 7.16(ii). -/
  codimensionTwoDeterminantSquare
    {pairs : Nat} (initial : Fin 2 → Kˣ)
    (source comparison : Fin (2 * pairs) → Kˣ) (scale : Kˣ)
    (hinitial : IsSquare
      (-(initial 0 * initial 1) *
        (discriminant.discriminantUnit : Kˣ)))
    (hsource : AlternatingEndpointPairClasses source)
    (hcomparison : AlternatingEndpointPairClasses comparison)
    (hsourceOrders : ∀ t : Fin pairs,
      ordUnit K (source ⟨2 * t.val, by omega⟩) = ordUnit K scale)
    (hcomparisonOrders : ∀ t : Fin pairs,
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) = ordUnit K scale)
    (hodd : Odd (ordUnit K scale - ordUnit K (initial 0)))
    (hrep : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients comparison)
      (BONG.GoodBONG.diagonalUnitCoefficients
        (Fin.append initial source))) :
    IsSquare
      (BONG.GoodBONG.diagonalUnitDeterminant source *
        BONG.GoodBONG.diagonalUnitDeterminant comparison)
  /-- If an alternating tower with one additional endpoint pair embeds in
  an extension of an equal-scale tower by an initial binary block and one
  line, the residual ternary block is isotropic. -/
  residualTernaryIsotropic
    {pairs : Nat} (initial : Fin 2 → Kˣ)
    (source : Fin (2 * pairs) → Kˣ)
    (comparison : Fin (2 * (pairs + 1)) → Kˣ) (extra : Kˣ)
    (hinitial : IsSquare
      (-(initial 0 * initial 1) *
        (discriminant.discriminantUnit : Kˣ)))
    (hodd : Odd (ordUnit K (extra * (initial 0)⁻¹)))
    (hsource : AlternatingEndpointPairClasses source)
    (hcomparison : AlternatingEndpointPairClasses comparison)
    (hsourceOrders : ∀ t : Fin pairs,
      ordUnit K (source ⟨2 * t.val, by omega⟩) = ordUnit K extra)
    (hcomparisonOrders : ∀ t : Fin (pairs + 1),
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) = ordUnit K extra)
    (hrep : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients comparison)
      (BONG.GoodBONG.diagonalUnitCoefficients
        (Fin.snoc (Fin.append initial source) extra))) :
    DiagonalIsotropic
      (BONG.GoodBONG.diagonalUnitCoefficients
        ![initial 0, initial 1, extra])

/-- Public form of the common-subform theorem. -/
theorem alternatingEndpointTower_commonCodimensionOne
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {pairs : Nat} (a b : Fin (2 * pairs) → Kˣ) (scale : Kˣ)
    (ha : AlternatingEndpointPairClasses a)
    (hb : AlternatingEndpointPairClasses b)
    (haOrders : AlternatingEndpointLeadingOrdersAt a scale)
    (hbOrders : AlternatingEndpointLeadingOrdersAt b scale) :
    DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients
        (diagonalUnitTake b (2 * pairs - 1) (by omega)))
      (BONG.GoodBONG.diagonalUnitCoefficients a) :=
  DyadicAlternatingEndpointTowerRepresentationLaws.commonCodimensionOne
    a b scale ha hb haOrders hbOrders

/-- Public equal-determinant representation theorem for two endpoint
towers. -/
theorem alternatingEndpointTower_equalDeterminantRepresentation
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {pairs : Nat} (a b : Fin (2 * pairs) → Kˣ) (scale : Kˣ)
    (ha : AlternatingEndpointPairClasses a)
    (hb : AlternatingEndpointPairClasses b)
    (haOrders : AlternatingEndpointLeadingOrdersAt a scale)
    (hbOrders : AlternatingEndpointLeadingOrdersAt b scale)
    (hdet : IsSquare
      (BONG.GoodBONG.diagonalUnitDeterminant a *
        BONG.GoodBONG.diagonalUnitDeterminant b)) :
    DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients b)
      (BONG.GoodBONG.diagonalUnitCoefficients a) :=
  DyadicAlternatingEndpointTowerRepresentationLaws.equalDeterminantRepresentation
    a b scale ha hb haOrders hbOrders hdet

/-- Public form of the one-pair extension representation theorem. -/
theorem alternatingEndpointTower_onePairExtensionRepresentation
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {pairs : Nat} (large : Fin (2 * (pairs + 1)) → Kˣ)
    (small : Fin (2 * pairs) → Kˣ) (extra : Kˣ)
    (hlarge : AlternatingEndpointPairClasses large)
    (hsmall : AlternatingEndpointPairClasses small)
    (hlargeOrders : ∀ t : Fin (pairs + 1),
      ordUnit K (large ⟨2 * t.val, by omega⟩) = ordUnit K extra)
    (hsmallOrders : ∀ t : Fin pairs,
      ordUnit K (small ⟨2 * t.val, by omega⟩) = ordUnit K extra) :
    DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients (Fin.snoc small extra))
      (BONG.GoodBONG.diagonalUnitCoefficients large) :=
  DyadicAlternatingEndpointTowerRepresentationLaws.onePairExtensionRepresentation
    large small extra hlarge hsmall hlargeOrders hsmallOrders

/-- Public form of endpoint-tower representation in a unary extension. -/
theorem alternatingEndpointTower_representationInUnaryExtension
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {pairs : Nat} (target comparison : Fin (2 * pairs) → Kˣ)
    (extra : Kˣ)
    (htarget : AlternatingEndpointPairClasses target)
    (hcomparison : AlternatingEndpointPairClasses comparison)
    (htargetOrders : ∀ t : Fin pairs,
      ordUnit K (target ⟨2 * t.val, by omega⟩) = ordUnit K extra)
    (hcomparisonOrders : ∀ t : Fin pairs,
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) = ordUnit K extra) :
    DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients comparison)
      (BONG.GoodBONG.diagonalUnitCoefficients (Fin.snoc target extra)) :=
  DyadicAlternatingEndpointTowerRepresentationLaws.representationInUnaryExtension
    target comparison extra htarget hcomparison htargetOrders
      hcomparisonOrders

/-- Public odd-line exclusion for an unramified binary head followed by an
equal-scale alternating endpoint tower. -/
theorem alternatingEndpointTower_unaryExtensionExclusion
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {pairs : Nat} (initial : Fin 2 → Kˣ)
    (source comparison : Fin (2 * pairs) → Kˣ) (extra : Kˣ)
    (hinitial : IsSquare
      (-(initial 0 * initial 1) *
        (discriminant.discriminantUnit : Kˣ)))
    (hsource : AlternatingEndpointPairClasses source)
    (hcomparison : AlternatingEndpointPairClasses comparison)
    (hsourceOrders : ∀ t : Fin pairs,
      ordUnit K (source ⟨2 * t.val, by omega⟩) = ordUnit K extra)
    (hcomparisonOrders : ∀ t : Fin pairs,
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) = ordUnit K extra)
    (hodd : Odd (ordUnit K (extra * (initial 0)⁻¹))) :
    ¬ DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients
        (Fin.snoc comparison extra))
      (BONG.GoodBONG.diagonalUnitCoefficients
        (Fin.append initial source)) :=
  DyadicAlternatingEndpointTowerRepresentationLaws.unaryExtensionExclusion
    initial source comparison extra hinitial hsource hcomparison
      hsourceOrders hcomparisonOrders hodd

/-- Public codimension-two determinant conclusion for two equal-scale
alternating endpoint towers behind an unramified binary head. -/
theorem alternatingEndpointTower_codimensionTwoDeterminantSquare
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {pairs : Nat} (initial : Fin 2 → Kˣ)
    (source comparison : Fin (2 * pairs) → Kˣ) (scale : Kˣ)
    (hinitial : IsSquare
      (-(initial 0 * initial 1) *
        (discriminant.discriminantUnit : Kˣ)))
    (hsource : AlternatingEndpointPairClasses source)
    (hcomparison : AlternatingEndpointPairClasses comparison)
    (hsourceOrders : ∀ t : Fin pairs,
      ordUnit K (source ⟨2 * t.val, by omega⟩) = ordUnit K scale)
    (hcomparisonOrders : ∀ t : Fin pairs,
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) = ordUnit K scale)
    (hodd : Odd (ordUnit K scale - ordUnit K (initial 0)))
    (hrep : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients comparison)
      (BONG.GoodBONG.diagonalUnitCoefficients
        (Fin.append initial source))) :
    IsSquare
      (BONG.GoodBONG.diagonalUnitDeterminant source *
        BONG.GoodBONG.diagonalUnitDeterminant comparison) :=
  DyadicAlternatingEndpointTowerRepresentationLaws.codimensionTwoDeterminantSquare
    initial source comparison scale hinitial hsource hcomparison
      hsourceOrders hcomparisonOrders hodd hrep

/-- Public residual-ternary form of alternating endpoint cancellation. -/
theorem alternatingEndpointTower_residualTernaryIsotropic
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {pairs : Nat} (initial : Fin 2 → Kˣ)
    (source : Fin (2 * pairs) → Kˣ)
    (comparison : Fin (2 * (pairs + 1)) → Kˣ) (extra : Kˣ)
    (hinitial : IsSquare
      (-(initial 0 * initial 1) *
        (discriminant.discriminantUnit : Kˣ)))
    (hodd : Odd (ordUnit K (extra * (initial 0)⁻¹)))
    (hsource : AlternatingEndpointPairClasses source)
    (hcomparison : AlternatingEndpointPairClasses comparison)
    (hsourceOrders : ∀ t : Fin pairs,
      ordUnit K (source ⟨2 * t.val, by omega⟩) = ordUnit K extra)
    (hcomparisonOrders : ∀ t : Fin (pairs + 1),
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) = ordUnit K extra)
    (hrep : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients comparison)
      (BONG.GoodBONG.diagonalUnitCoefficients
        (Fin.snoc (Fin.append initial source) extra))) :
    DiagonalIsotropic
      (BONG.GoodBONG.diagonalUnitCoefficients
        ![initial 0, initial 1, extra]) :=
  DyadicAlternatingEndpointTowerRepresentationLaws.residualTernaryIsotropic
    initial source comparison extra hinitial hodd hsource hcomparison
      hsourceOrders hcomparisonOrders hrep

end Bong
