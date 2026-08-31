/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalHalfTower
import Bong.Bong.Beli2009ClassificationProof
import Bong.Bong.Beli2019PrefixChange
import Bong.Bong.BinaryNormGeneratorLocalProof
import Bong.Bong.StructuralProof
import Bong.Bong.BeliLemma47Proof
import Bong.Bong.Beli2009AlphaArithmetic
import Bong.Bong.Beli2019Lemma715Prefix
import Bong.Bong.ValueIsometry
import Bong.Bong.TwoBlockProductIsometry
import Bong.Dyadic.QuadraticDefectHensel

/-!
# Beli's splitting criterion for a half-hyperbolic tower

This file formalizes Lemma 4.8 of "Universal integral quadratic forms over
dyadic local fields".  Paper indices are one based; the Lean indices in the
order fields below are zero based.  In particular, the optional tail entry is
the paper's `R_{2k+1}`.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {m k : Nat}

noncomputable local instance universalLemma48Discriminant :
    DyadicDiscriminantClassLaws K :=
  dyadicDiscriminantClassLawsProved

namespace Lattice.QuadraticLatticeModel

/-- The literal meaning of "`M` splits `1/2 A(0,0)^k`" in Beli's paper. -/
def SplitsHalfHyperbolic (M : QuadraticLatticeModel (K := K))
    (k : Nat) : Prop :=
  ∃ R : QuadraticLatticeModel (K := K),
    Nonempty ((R.adjoinHalfHyperbolic k).Isometry M)

end Lattice.QuadraticLatticeModel

namespace BONG.GoodBONG

/-- The coefficient function of the chosen standard good BONG.  Packaging
the carrier instances inside this definition keeps paper-facing statements
independent of implementation-level model instances. -/
noncomputable def standardHalfHyperbolicTowerValues (k : Nat) :
    Fin (2 * k) → Kˣ := by
  let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) k
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  exact fun i ↦
    (standardHalfHyperbolicTowerBONG (K := K) k).valueUnit i

/-- The two explicit clauses in Beli's Lemma 4.8.  The proof `bound` makes
all displayed prefix indices genuine, including the equality-rank boundary
`2k = m`. -/
structure UniversalLemma48Conditions
    (a : GoodBONG q L (m + 1)) (k : Nat) : Prop where
  bound : 2 * k ≤ m + 1
  oddOrders (j : Fin k) :
    a.order ⟨2 * j.val, by have := bound; omega⟩ = 0
  evenOrders (j : Fin k) :
    a.order ⟨2 * j.val + 1, by have := bound; omega⟩ =
      -2 * (ramificationIndex K : Int)
  endpoint :
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        a.truncatedSegmentDefect ((-1 : Kˣ) ^ k) 1 (2 * k) ∨
      ∃ htail : 2 * k < m + 1,
        a.order ⟨2 * k, htail⟩ = 0

/-- The order clause of Lemma 4.8, restricted to the first `2k` values, is
exactly the order profile used by the endpoint-tower normalization theorem. -/
theorem UniversalLemma48Conditions.orderProfile
    {a : GoodBONG q L (m + 1)}
    (h : UniversalLemma48Conditions a k) :
    AlternatingEndpointOrderProfile
      (a.prefixValueUnits (2 * k) h.bound) 0 := by
  intro j
  constructor
  · change a.toBONG.order
      ⟨2 * j.val, by have := h.bound; omega⟩ = 0
    exact h.oddOrders j
  · change a.toBONG.order
      ⟨2 * j.val + 1, by have := h.bound; omega⟩ =
      0 - 2 * (ramificationIndex K : Int)
    have hj := h.evenOrders j
    change a.toBONG.order
      ⟨2 * j.val + 1, by have := h.bound; omega⟩ =
        -2 * (ramificationIndex K : Int) at hj
    simpa using hj

/-- The order clause also gives the endpoint square-class alternative for
every adjacent pair in the prefix. -/
theorem UniversalLemma48Conditions.pairClasses
    {a : GoodBONG q L (m + 1)}
    (h : UniversalLemma48Conditions a k) :
    AlternatingEndpointPairClasses
      (a.prefixValueUnits (2 * k) h.bound) := by
  intro j
  let i : Fin (m + 1) :=
    ⟨2 * j.val, by have := h.bound; omega⟩
  have hi : i.val + 1 < m + 1 := by
    simp only [i]
    have := h.bound
    omega
  have hnext : (⟨i.val + 1, hi⟩ : Fin (m + 1)) =
      ⟨2 * j.val + 1, by have := h.bound; omega⟩ := by
    apply Fin.ext
    simp [i]
  have hgap : a.order ⟨i.val + 1, hi⟩ - a.order i =
      -(2 * (ramificationIndex K : Int)) := by
    rw [hnext, h.oddOrders j, h.evenOrders j]
    ring
  have hp := a.toBONG.adjacentSignedProduct_endpoint_cases i hi
    (a.toBONG.adjacentUnitSquareClass_endpoint_cases i hi hgap)
  simpa [AlternatingEndpointPairClasses,
    BONG.GoodBONG.prefixValueUnits, BONG.GoodBONG.valueUnit,
    BONG.GoodBONG.order, i, hnext] using hp

/-- The endpoint clause in Lemma 4.8 can always be realized by a good BONG
whose first `2k` coefficients have the hyperbolic determinant square class.
In the tail-zero branch this is the paper's boundary `Delta` move. -/
theorem UniversalLemma48Conditions.exists_signedPrefixSquare
    {a : GoodBONG q L (m + 1)} (hk : 1 ≤ k)
    (h : UniversalLemma48Conditions a k) :
    ∃ c : GoodBONG q L (m + 1),
      UniversalLemma48Conditions c k ∧
      (∀ i : Fin (m + 1), c.order i = a.order i) ∧
      IsSquare (c.toBONG.signedEvenPrefixProduct k) ∧
      ∀ (s : Nat), 2 * k + 1 ≤ s → (hs : s ≤ m + 1) →
        (a.prefixDiagonalSpace s hs).IsIsometric
          (c.prefixDiagonalSpace s hs) := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  rcases h.endpoint with hdefect | ⟨htail, htailOrder⟩
  · refine ⟨a, h, fun _ ↦ rfl, ?_, ?_⟩
    · apply BONG.GoodBONG.isSquare_of_two_mul_e_lt_defectOrder
      apply hdefect.trans_le
      have hle := a.truncatedPrefixDefect_le_defect a
        ((-1 : Kˣ) ^ k) (1 - 1) (2 * k)
      simpa [truncatedSegmentDefect, BONG.signedEvenPrefixProduct,
        BONG.GoodBONG.prefixProduct] using hle
    · intro s _ hs
      exact ⟨QuadraticSpace.Isometry.refl (a.prefixDiagonalSpace s hs)⟩
  · have hcases :
        IsSquare (a.toBONG.signedEvenPrefixProduct k) ∨
          IsSquare (a.toBONG.signedEvenPrefixProduct k *
            (universalLemma48Discriminant (K := K)).discriminantUnit) := by
      apply a.toBONG.signedEvenPrefixProduct_endpoint_cases k h.bound
      intro t ht
      have hp := h.pairClasses ⟨t, ht⟩
      simpa [AlternatingEndpointPairClasses,
        BONG.GoodBONG.prefixValueUnits,
        BONG.GoodBONG.valueUnit] using hp
    rcases hcases with hsquare | hdelta
    · refine ⟨a, h, fun _ ↦ rfl, hsquare, ?_⟩
      intro s _ hs
      exact ⟨QuadraticSpace.Isometry.refl (a.prefixDiagonalSpace s hs)⟩
    · let structural : BONGStructuralLaws.{u, v} K :=
        bongStructuralLawsProved K
      let lemma47 : BeliLemma47Laws.{u, v} K :=
        beliLemma47LawsProved K
      let lemma49 : BeliLemma49Laws.{u, v} K :=
        @BONG.beliLemma49LawsOfReverseDual.{u, v} K _ _ _ _ _ lemma47
          (BONGStructuralLaws.toBONGReverseDualLaws (self := structural))
      letI : BinaryNormGeneratorLocalLaws.{u, v} K :=
        binaryNormGeneratorLocalLawsProved
      letI : BeliLemma49Laws.{u, v} K := lemma49
      let boundary : Fin (m + 1) := ⟨2 * k - 1, by omega⟩
      have hboundary : boundary.val + 1 < m + 1 := by
        simp only [boundary]
        omega
      let next : Fin (m + 1) := ⟨boundary.val + 1, hboundary⟩
      let lastPair : Fin k := ⟨k - 1, by omega⟩
      have hboundaryIndex : boundary =
          ⟨2 * lastPair.val + 1, by have := h.bound; omega⟩ := by
        apply Fin.ext
        simp [boundary, lastPair]
        omega
      have hnextIndex : next = ⟨2 * k, htail⟩ := by
        apply Fin.ext
        simp [next, boundary]
        omega
      have hparameterOrder :
          ordUnit K (a.toBONG.adjacentParameter boundary hboundary) =
            2 * (ramificationIndex K : Int) := by
        rw [a.toBONG.ordUnit_adjacentParameter]
        change a.order next - a.order boundary = _
        rw [hnextIndex, htailOrder, hboundaryIndex,
          h.evenOrders lastPair]
        ring
      have hu :=
        discriminantUnitClass_mem_beliNormGeneratorGroup_of_order_eq_twoE
          (a.toBONG.adjacentParameter boundary hboundary) hparameterOrder
      rcases BONG.exists_adjacentMultiplierData a boundary hboundary
          (discriminantValuationUnit (K := K)) hu with ⟨C⟩
      refine ⟨C.bong, ?_, C.order_eq, ?_, ?_⟩
      · refine {
          bound := h.bound
          oddOrders := ?_
          evenOrders := ?_
          endpoint := Or.inr ⟨htail, ?_⟩ }
        · intro j
          rw [C.order_eq]
          exact h.oddOrders j
        · intro j
          rw [C.order_eq]
          exact h.evenOrders j
        · rw [C.order_eq]
          exact htailOrder
      · rw [C.signedEvenPrefixProduct_leftBoundary k (by
          simp only [boundary]
          omega)]
        simpa only [discriminantValuationUnit, mul_comm] using hdelta
      · intro s hs hsRank
        apply prefixDiagonalSpace_isIsometric_of_suffix_valueUnit_eq
        intro i hi
        exact (C.valueUnit_after i (by
          simp only [boundary]
          omega)).symm

/-- Cancelling the common sign in two square representatives. -/
private theorem isSquare_product_of_common_signed_squares
    (sign x y : Kˣ) (hx : IsSquare (sign * x))
    (hy : IsSquare (sign * y)) : IsSquare (x * y) := by
  have h := hx.mul hy
  have hsign : IsSquare (sign ^ 2) := ⟨sign, by simp [pow_two]⟩
  have hquotient := h.div hsign
  have hcancel : ((sign * x) * (sign * y)) / sign ^ 2 = x * y := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul,
      Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero sign]
  rw [hcancel] at hquotient
  exact hquotient

private theorem beliUniversal_valueUnit_castLength
    {W : Type*} [AddCommGroup W] [Module K W]
    {s : QuadraticSpace K W} {N : Lattice K W} {p p' : Nat}
    (d : BONG W s N p) (hp : p = p') (i : Fin p') :
    (d.castLength hp).valueUnit i =
      d.valueUnit ⟨i.val, by simpa [hp] using i.isLt⟩ := by
  subst p'
  rfl

private theorem beliUniversal_goodValueUnit_castLength
    {W : Type*} [AddCommGroup W] [Module K W]
    {s : QuadraticSpace K W} {N : Lattice K W} {p p' : Nat}
    (d : GoodBONG s N p) (hp : p = p') (i : Fin p') :
    (d.castLength hp).valueUnit i =
      d.valueUnit ⟨i.val, by simpa [hp] using i.isLt⟩ := by
  subst p'
  rfl

/-- Under the two numerical clauses of Lemma 4.8, the good BONG can be
chosen so that its first `2k` values are literally those of the standard
half-hyperbolic tower.  Every order is preserved; the tail-zero branch may
multiply its first tail coefficient by `Delta`, exactly as in the paper. -/
theorem UniversalLemma48Conditions.exists_standardTowerPrefix
    {a : GoodBONG q L (m + 1)} (hk : 1 ≤ k)
    (h : UniversalLemma48Conditions a k) :
    ∃ c : GoodBONG q L (m + 1),
      (∀ i : Fin (2 * k),
        c.valueUnit ⟨i.val, i.isLt.trans_le h.bound⟩ =
          standardHalfHyperbolicTowerValues (K := K) k i) ∧
      (∀ j : Fin (m + 1), c.order j = a.order j) ∧
      ∀ (s : Nat), 2 * k + 1 ≤ s → (hs : s ≤ m + 1) →
        (a.prefixDiagonalSpace s hs).IsIsometric
          (c.prefixDiagonalSpace s hs) := by
  letI : DyadicUnramifiedNormLaws K :=
    dyadicUnramifiedNormLawsProvedDirect
  let structural : BONGStructuralLaws.{u, v} K :=
    bongStructuralLawsProved K
  let lemma47 : BeliLemma47Laws.{u, v} K :=
    beliLemma47LawsProved K
  let lemma49 : BeliLemma49Laws.{u, v} K :=
    @BONG.beliLemma49LawsOfReverseDual.{u, v} K _ _ _ _ _ lemma47
      (BONGStructuralLaws.toBONGReverseDualLaws (self := structural))
  letI : BinaryNormGeneratorLocalLaws.{u, v} K :=
    binaryNormGeneratorLocalLawsProved
  letI : BeliLemma49Laws.{u, v} K := lemma49
  rcases h.exists_signedPrefixSquare hk with
    ⟨d, hd, hdOrders, hdSquare, hdPrefixIso⟩
  let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) k
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  let b := standardHalfHyperbolicTowerBONG (K := K) k
  let target : Fin (2 * k) → Kˣ :=
    standardHalfHyperbolicTowerValues (K := K) k
  have htargetValue (i : Fin (2 * k)) : target i = b.valueUnit i := by
    rfl
  have hbPattern : b.HasHalfModularOrderPattern :=
    standardHalfHyperbolicTowerBONG_orderPattern (K := K) hk
  have hbProfile : AlternatingEndpointOrderProfile target 0 := by
    intro j
    constructor
    · rw [htargetValue]
      change b.order ⟨2 * j.val, by omega⟩ = 0
      have hindex : (⟨2 * j.val, by omega⟩ : Fin (2 * k)) =
          halfModularPairIndexEquiv k (j, (0 : Fin 2)) := by
        apply Fin.ext
        simp
      rw [hindex]
      exact (hbPattern j).1
    · rw [htargetValue]
      change b.order ⟨2 * j.val + 1, by omega⟩ =
        0 - 2 * (ramificationIndex K : Int)
      have hindex : (⟨2 * j.val + 1, by omega⟩ : Fin (2 * k)) =
          halfModularPairIndexEquiv k (j, (1 : Fin 2)) := by
        apply Fin.ext
        simp
      rw [hindex]
      simpa using (hbPattern j).2
  have hbPairClasses : AlternatingEndpointPairClasses target := by
    intro j
    let i : Fin (2 * k) := ⟨2 * j.val, by omega⟩
    have hi : i.val + 1 < 2 * k := by
      have hj := j.isLt
      dsimp [i]
      omega
    have hnext : (⟨i.val + 1, hi⟩ : Fin (2 * k)) =
        halfModularPairIndexEquiv k (j, (1 : Fin 2)) := by
      apply Fin.ext
      simp [i]
    have hgap : b.order ⟨i.val + 1, hi⟩ - b.order i =
        -(2 * (ramificationIndex K : Int)) := by
      have hcur : i =
          halfModularPairIndexEquiv k (j, (0 : Fin 2)) := by
        apply Fin.ext
        simp [i]
      rw [hnext, hcur, (hbPattern j).1, (hbPattern j).2]
      ring
    have hp := b.toBONG.adjacentSignedProduct_endpoint_cases i hi
      (b.toBONG.adjacentUnitSquareClass_endpoint_cases i hi hgap)
    simpa [AlternatingEndpointPairClasses, htargetValue,
      BONG.GoodBONG.valueUnit, i, hnext] using hp
  have hbSquare : IsSquare (b.toBONG.signedEvenPrefixProduct k) :=
    BONG.GoodBONG.standardHalfHyperbolicTowerBONG_signedProduct_isSquare
      (K := K) k
  have htargetOrders : ∀ i : Fin (2 * k),
      ordUnit K (target i) =
        ordUnit K ((d.prefixValueUnits (2 * k) hd.bound) i) := by
    intro i
    obtain ⟨js, rfl⟩ := (halfModularPairIndexEquiv k).surjective i
    rcases js with ⟨j, s⟩
    fin_cases s
    · calc
        ordUnit K (target
            (halfModularPairIndexEquiv k (j, (0 : Fin 2)))) = 0 := by
          have hindex : halfModularPairIndexEquiv k (j, (0 : Fin 2)) =
              (⟨2 * j.val, by omega⟩ : Fin (2 * k)) := by
            apply Fin.ext
            simp
          rw [hindex]
          exact (hbProfile j).1
        _ = ordUnit K ((d.prefixValueUnits (2 * k) hd.bound)
            (halfModularPairIndexEquiv k (j, (0 : Fin 2)))) := by
          symm
          have hindex : halfModularPairIndexEquiv k (j, (0 : Fin 2)) =
              (⟨2 * j.val, by omega⟩ : Fin (2 * k)) := by
            apply Fin.ext
            simp
          rw [hindex]
          exact (hd.orderProfile j).1
    · calc
        ordUnit K (target
            (halfModularPairIndexEquiv k (j, (1 : Fin 2)))) =
            0 - 2 * (ramificationIndex K : Int) := by
          have hindex : halfModularPairIndexEquiv k (j, (1 : Fin 2)) =
              (⟨2 * j.val + 1, by omega⟩ : Fin (2 * k)) := by
            apply Fin.ext
            simp
          rw [hindex]
          exact (hbProfile j).2
        _ = ordUnit K ((d.prefixValueUnits (2 * k) hd.bound)
            (halfModularPairIndexEquiv k (j, (1 : Fin 2)))) := by
          symm
          have hindex : halfModularPairIndexEquiv k (j, (1 : Fin 2)) =
              (⟨2 * j.val + 1, by omega⟩ : Fin (2 * k)) := by
            apply Fin.ext
            simp
          rw [hindex]
          exact (hd.orderProfile j).2
  have hdet : IsSquare
      (diagonalUnitDeterminant
          (d.prefixValueUnits (2 * k) hd.bound) *
        diagonalUnitDeterminant target) := by
    rw [d.diagonalUnitDeterminant_prefixValueUnits]
    have hbFull := b.prefixProduct_eq_valueProduct_of_rank_le (2 * k) le_rfl
    have htarget : diagonalUnitDeterminant target = b.prefixProduct (2 * k) := by
      rw [hbFull]
      simp [diagonalUnitDeterminant, target, htargetValue,
        BONG.valueProduct, BONG.GoodBONG.valueUnit,
        BONG.prefixProduct]
    rw [htarget]
    exact isSquare_product_of_common_signed_squares
      ((-1 : Kˣ) ^ k) (d.prefixProduct (2 * k))
        (b.prefixProduct (2 * k)) (by
          simpa [BONG.signedEvenPrefixProduct,
            BONG.GoodBONG.prefixProduct] using hdSquare) (by
          simpa [BONG.signedEvenPrefixProduct,
            BONG.GoodBONG.prefixProduct] using hbSquare)
  rcases AlternatingEndpointNormalization.exists_normalizedRigidEndpointPrefix
      d hd.bound target 0 hd.pairClasses hbPairClasses hd.orderProfile
        hbProfile hdet with ⟨c, hcPrefix, hcSuffix⟩
  refine ⟨c, hcPrefix, ?_, ?_⟩
  · intro j
    exact (normalizedSplitPrefix_order_eq d c hd.bound target hcPrefix
      hcSuffix htargetOrders j).trans (hdOrders j)
  · intro s hs hsRank
    rcases hdPrefixIso s hs hsRank with ⟨f⟩
    have hdc : (d.prefixDiagonalSpace s hsRank).IsIsometric
        (c.prefixDiagonalSpace s hsRank) := by
      apply prefixDiagonalSpace_isIsometric_of_suffix_valueUnit_eq
      intro i hi
      exact (hcSuffix i (by omega)).symm
    rcases hdc with ⟨g⟩
    exact ⟨f.trans g⟩

/-- A literal standard-tower prefix has the paper's hyperbolic signed
determinant square class. -/
theorem isSquare_signedEvenPrefixProduct_of_standardPrefix
    {a : GoodBONG q L (m + 1)} (hbound : 2 * k ≤ m + 1)
    (hvalues : ∀ i : Fin (2 * k),
      a.valueUnit ⟨i.val, i.isLt.trans_le hbound⟩ =
        standardHalfHyperbolicTowerValues (K := K) k i) :
    IsSquare (a.toBONG.signedEvenPrefixProduct k) := by
  let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) k
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  let b := standardHalfHyperbolicTowerBONG (K := K) k
  let target : Fin (2 * k) → Kˣ :=
    standardHalfHyperbolicTowerValues (K := K) k
  have hfunction : a.prefixValueUnits (2 * k) hbound = target := by
    funext i
    exact hvalues i
  have htarget : diagonalUnitDeterminant target = b.prefixProduct (2 * k) := by
    have hbFull := b.prefixProduct_eq_valueProduct_of_rank_le (2 * k) le_rfl
    rw [hbFull]
    change (∏ i, b.toBONG.valueUnit i) = b.toBONG.valueProduct
    simp [BONG.valueProduct, BONG.prefixProduct]
  have hprefix : a.prefixProduct (2 * k) = b.prefixProduct (2 * k) := by
    rw [← a.diagonalUnitDeterminant_prefixValueUnits (2 * k) hbound]
    rw [hfunction, htarget]
  have hbSquare :=
    standardHalfHyperbolicTowerBONG_signedProduct_isSquare (K := K) k
  unfold BONG.signedEvenPrefixProduct at hbSquare ⊢
  change IsSquare (((-1 : Kˣ) ^ k) * a.prefixProduct (2 * k))
  rw [hprefix]
  simpa only [BONG.GoodBONG.prefixProduct] using hbSquare

/-- At full rank the two endpoint alpha caps are absent, so a hyperbolic
signed prefix has infinite truncated defect. -/
theorem truncatedSegmentDefect_eq_top_of_standardFullPrefix
    {a : GoodBONG q L (m + 1)} (hfull : 2 * k = m + 1)
    (hvalues : ∀ i : Fin (2 * k),
      a.valueUnit ⟨i.val, by omega⟩ =
        standardHalfHyperbolicTowerValues (K := K) k i) :
    a.truncatedSegmentDefect ((-1 : Kˣ) ^ k) 1 (2 * k) = ⊤ := by
  have hsquare := isSquare_signedEvenPrefixProduct_of_standardPrefix
    (a := a) (k := k) (by omega) hvalues
  have hcap : a.prefixAlphaCap (2 * k) = ⊤ := by
    have hlast := a.prefixAlphaCap_last
    rw [← hfull] at hlast
    exact hlast
  have hdefect : defectOrder (K := K)
      (a.toBONG.signedEvenPrefixProduct k) = ⊤ :=
    BONG.GoodBONG.defectOrder_eq_top_of_isSquare hsquare
  unfold truncatedSegmentDefect truncatedPrefixDefect
  rw [a.prefixAlphaCap_zero, hcap]
  simpa [BONG.signedEvenPrefixProduct, BONG.GoodBONG.prefixProduct] using hdefect

/-- If the first residual coefficient has positive order, the boundary gap
forces the final prefix alpha to exceed `2e`; the raw signed defect is already
infinite because the prefix is hyperbolic. -/
theorem twoE_lt_truncatedSegmentDefect_of_standardPrefix_of_tail_pos
    {a : GoodBONG q L (m + 1)} (hk : 1 ≤ k)
    (hbound : 2 * k ≤ m + 1) (htail : 2 * k < m + 1)
    (hvalues : ∀ i : Fin (2 * k),
      a.valueUnit ⟨i.val, i.isLt.trans_le hbound⟩ =
        standardHalfHyperbolicTowerValues (K := K) k i)
    (hlast : a.order ⟨2 * k - 1, by omega⟩ =
      -2 * (ramificationIndex K : Int))
    (htailPos : 0 < a.order ⟨2 * k, htail⟩) :
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
      a.truncatedSegmentDefect ((-1 : Kˣ) ^ k) 1 (2 * k) := by
  have hsquare := isSquare_signedEvenPrefixProduct_of_standardPrefix
    (a := a) (k := k) hbound hvalues
  let boundary : Fin m := ⟨2 * k - 1, by omega⟩
  have hcast : boundary.castSucc =
      (⟨2 * k - 1, by omega⟩ : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  have hsucc : boundary.succ = (⟨2 * k, htail⟩ : Fin (m + 1)) := by
    apply Fin.ext
    simp [boundary]
    omega
  have hgap : 2 * (ramificationIndex K : Int) < a.orderGap boundary := by
    unfold orderGap
    rw [hcast, hsucc, hlast]
    omega
  have halpha : 2 * (ramificationIndex K : ℚ) < a.alphaValue boundary :=
    (a.beli2009Corollary28_ii boundary).2.2.mpr hgap
  have hcap : a.prefixAlphaCap (2 * k) =
      (a.alphaValue boundary : WithTop ℚ) := by
    have hraw := a.prefixAlphaCap_of_internal (i := 2 * k) (by omega) htail
    convert hraw using 1
  have hdefect : defectOrder (K := K)
      (a.toBONG.signedEvenPrefixProduct k) = ⊤ :=
    BONG.GoodBONG.defectOrder_eq_top_of_isSquare hsquare
  have hrawDefect : defectOrder (K := K)
      (((-1 : Kˣ) ^ k) * a.toBONG.prefixProduct (2 * k)) = ⊤ := by
    simpa [BONG.signedEvenPrefixProduct] using hdefect
  unfold truncatedSegmentDefect truncatedPrefixDefect
  rw [a.prefixAlphaCap_zero, hcap]
  simp only [Nat.sub_self, BONG.GoodBONG.prefixProduct,
    BONG.prefixProduct_zero, mul_one, min_top_left, lt_min_iff]
  constructor
  · rw [hrawDefect]
    exact WithTop.coe_lt_top _
  · exact_mod_cast halpha

/-- A good BONG adapted to an actual half-hyperbolic splitting.  This is the
constructive content behind the necessity direction of Lemma 4.8 and the
choice assertion in Lemma 4.9. -/
structure HalfHyperbolicSplitGoodBONGData
    {U : Type u} [AddCommGroup U] [Module K U]
    (r : QuadraticSpace K U) (M : Lattice K U)
    (m k : Nat) where
  Residual : Type u
  [residualAddCommGroup : AddCommGroup Residual]
  [residualModule : Module K Residual]
  residualForm : QuadraticSpace K Residual
  residualLattice : Lattice K Residual
  residualIntegral : Lattice.IsIntegral residualForm residualLattice
  presentation : Lattice.Isometry
    (Lattice.halfHyperbolicExtensionForm residualForm k) r
    (Lattice.halfHyperbolicExtensionLattice residualLattice k) M
  rankEq : 2 * k + finrank K Residual = m + 1
  residualBONG : GoodBONG residualForm residualLattice (finrank K Residual)
  bong : GoodBONG r M (m + 1)
  prefixValues (i : Fin (2 * k)) :
    bong.valueUnit ⟨i.val, by have := rankEq; omega⟩ =
      standardHalfHyperbolicTowerValues (K := K) k i
  residualValues (j : Fin (finrank K Residual)) :
    bong.valueUnit ⟨2 * k + j.val, by have := rankEq; omega⟩ =
      residualBONG.valueUnit j

/-- Construct the splitting-adapted good BONG by concatenating the standard
tower BONG with a good BONG of the residual lattice and transporting the
result through the displayed integral isometry. -/
noncomputable def halfHyperbolicSplitGoodBONGData
    {U : Type u} [AddCommGroup U] [Module K U]
    {r : QuadraticSpace K U} {M : Lattice K U} {m k : Nat}
    (hk : 1 ≤ k) (a : GoodBONG r M (m + 1))
    (hM : Lattice.IsIntegral r M)
    (hsplit : (Lattice.quadraticLatticeModel r M).SplitsHalfHyperbolic k) :
    HalfHyperbolicSplitGoodBONGData r M m k := by
  let R := Classical.choose hsplit
  letI : AddCommGroup R.Carrier := R.addCommGroup
  letI : Module K R.Carrier := R.module
  let f : Lattice.Isometry
      (Lattice.halfHyperbolicExtensionForm R.form k) r
      (Lattice.halfHyperbolicExtensionLattice R.lattice k) M := by
    exact Classical.choice (Classical.choose_spec hsplit)
  letI : AddCommGroup (R.adjoinHalfHyperbolic k).Carrier :=
    (R.adjoinHalfHyperbolic k).addCommGroup
  letI : Module K (R.adjoinHalfHyperbolic k).Carrier :=
    (R.adjoinHalfHyperbolic k).module
  have htotal : (R.adjoinHalfHyperbolic k).IsIntegral := by
    change Lattice.IsIntegral (R.adjoinHalfHyperbolic k).form
      (R.adjoinHalfHyperbolic k).lattice
    exact (Lattice.isIntegral_iff_of_latticeIsometry f).2 hM
  have hR : R.IsIntegral :=
    Lattice.QuadraticLatticeModel.IsIntegral.of_adjoinHalfHyperbolic k htotal
  have hrank : 2 * k + R.rank = m + 1 := by
    have hfin := f.toLinearEquiv.finrank_eq
    change (R.adjoinHalfHyperbolic k).rank = finrank K U at hfin
    rw [Lattice.QuadraticLatticeModel.rank_adjoinHalfHyperbolic] at hfin
    have ha := a.toBONG.length_eq_finrank
    change m + 1 = finrank K U at ha
    omega
  let structural : BONGStructuralLaws.{u, u} K := bongStructuralLawsProved K
  letI : BONGGoodExistenceLaws.{u, u} K :=
    BONGStructuralLaws.toBONGGoodExistenceLaws (self := structural)
  let c : GoodBONG R.form R.lattice (finrank K R.Carrier) :=
    GoodBONG.ofLattice R.form R.lattice
  let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) k
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  let b := standardHalfHyperbolicTowerBONG (K := K) k
  have hTower : Lattice.IsHalfModularWithUnitNorm T.form T.lattice :=
    Lattice.halfHyperbolicTower_isHalfModularWithUnitNorm (K := K)
      hk
  let dExists := b.beliUniversalLemma47 hk c hTower hR
  let dProduct := Classical.choose dExists
  have hdLeft := (Classical.choose_spec dExists).1
  have hdRight := (Classical.choose_spec dExists).2
  let zeroLattice := QuadraticSpace.zeroCoordinateBasisLattice (K := K)
  let append : Lattice.Isometry (T.form.orthogonalSum R.form)
      (R.adjoinHalfHyperbolic k).form
      (Lattice.product T.lattice R.lattice)
      (R.adjoinHalfHyperbolic k).lattice := by
    change Lattice.Isometry
      ((Lattice.omearaPlaneExtensionForm
        (Lattice.zeroCoordinateQuadraticSpace (K := K))
        (Lattice.dyadicHalfUnit (K := K)) k (fun _ ↦ 0)).orthogonalSum R.form)
      (Lattice.omearaPlaneExtensionForm R.form
        (Lattice.dyadicHalfUnit (K := K)) k (fun _ ↦ 0))
      (Lattice.product
        (Lattice.hyperbolicExtensionLattice zeroLattice k) R.lattice)
      (Lattice.hyperbolicExtensionLattice R.lattice k)
    exact Lattice.omearaPlaneExtensionAppendIsometry zeroLattice
      R.form R.lattice (Lattice.dyadicHalfUnit (K := K)) k (fun _ ↦ 0)
  let transported := dProduct.mapLatticeIsometry (append.trans f)
  have hrank' : 2 * k + finrank K R.Carrier = m + 1 := by
    exact hrank
  have hlength : finrank K R.Carrier + 2 * k = m + 1 := by omega
  let d : GoodBONG r M (m + 1) := transported.castLength hlength
  refine
    { Residual := R.Carrier
      residualForm := R.form
      residualLattice := R.lattice
      residualIntegral := hR
      presentation := f
      rankEq := hrank
      residualBONG := c
      bong := d
      prefixValues := ?_
      residualValues := ?_ }
  · intro i
    have hcast := beliUniversal_goodValueUnit_castLength transported hlength
      ⟨i.val, by omega⟩
    have hmap := GoodBONG.valueUnit_mapLatticeIsometry (append.trans f)
      dProduct (BONG.orthogonalProductLeftIndex (finrank K R.Carrier) i)
    have hindex :
        (⟨i.val, by omega⟩ : Fin (finrank K R.Carrier + 2 * k)) =
          BONG.orthogonalProductLeftIndex (finrank K R.Carrier) i := by
      apply Fin.ext
      rfl
    change d.valueUnit ⟨i.val, by omega⟩ = _
    rw [show d.valueUnit ⟨i.val, by omega⟩ =
        transported.valueUnit ⟨i.val, by omega⟩ by
      simpa only [d] using hcast]
    rw [hindex, hmap, hdLeft]
    rfl
  · intro j
    have hcast := beliUniversal_goodValueUnit_castLength transported hlength
      ⟨2 * k + j.val, by omega⟩
    have hmap := GoodBONG.valueUnit_mapLatticeIsometry (append.trans f)
      dProduct (BONG.orthogonalProductRightIndex (2 * k) j)
    have hindex :
        (⟨2 * k + j.val, by omega⟩ : Fin (R.rank + 2 * k)) =
          BONG.orthogonalProductRightIndex (2 * k) j := by
      apply Fin.ext
      rfl
    change d.valueUnit ⟨2 * k + j.val, by omega⟩ = _
    rw [show d.valueUnit ⟨2 * k + j.val, by omega⟩ =
        transported.valueUnit ⟨2 * k + j.val, by omega⟩ by
      simpa only [d] using hcast]
    calc
      transported.valueUnit ⟨2 * k + j.val, by omega⟩ =
          transported.valueUnit
            (BONG.orthogonalProductRightIndex (2 * k) j) :=
        congrArg transported.valueUnit hindex
      _ = dProduct.valueUnit
          (BONG.orthogonalProductRightIndex (2 * k) j) := hmap
      _ = c.valueUnit j := hdRight j

/-- The sufficiency direction of Beli's Lemma 4.8.  The normalized prefix is
split integrally by Corollary 4.4; equality with the chosen standard tower is
then upgraded to a literal lattice isometry, after which Lemma 4.3 supplies
the residual integral lattice. -/
theorem UniversalLemma48Conditions.splitsHalfHyperbolic
    {U : Type u} [AddCommGroup U] [Module K U]
    {r : QuadraticSpace K U} {M : Lattice K U}
    {a : GoodBONG r M (m + 1)} (hk : 1 ≤ k)
    (hM : Lattice.IsIntegral r M)
    (h : UniversalLemma48Conditions a k) :
    (Lattice.quadraticLatticeModel r M).SplitsHalfHyperbolic k := by
  rcases h.exists_standardTowerPrefix hk with
    ⟨c, hcValues, hcOrders, _hcPrefixIso⟩
  let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) k
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  let b := standardHalfHyperbolicTowerBONG (K := K) k
  let f : Lattice.Representation T.form r T.lattice M := by
    by_cases hlt : 2 * k < m + 1
    · let lastPair : Fin k := ⟨k - 1, by omega⟩
      let boundary : Fin (m + 1) := ⟨2 * k - 1, by omega⟩
      let next : Fin (m + 1) := ⟨2 * k, hlt⟩
      have hboundaryIndex : boundary =
          ⟨2 * lastPair.val + 1, by have := h.bound; omega⟩ := by
        apply Fin.ext
        simp only [boundary, lastPair]
        omega
      have hboundaryOrder : c.order boundary =
          -2 * (ramificationIndex K : Int) := by
        rw [hcOrders, hboundaryIndex]
        exact h.evenOrders lastPair
      let firstPair : Fin k := ⟨0, by omega⟩
      have hzeroIndex : (⟨0, by omega⟩ : Fin (m + 1)) =
          ⟨2 * firstPair.val, by have := h.bound; omega⟩ := by
        apply Fin.ext
        simp [firstPair]
      have hzeroOrder : c.order (⟨0, by omega⟩ : Fin (m + 1)) = 0 := by
        rw [hcOrders, hzeroIndex]
        exact h.oddOrders firstPair
      have htailMono := c.order_le_add_two_mul 0 k (by omega)
      have htailNonneg : 0 ≤ c.order next := by
        calc
          0 = c.order (⟨0, by omega⟩ : Fin (m + 1)) := hzeroOrder.symm
          _ ≤ c.order ⟨0 + 2 * k, by omega⟩ := htailMono
          _ = c.order next := by
            apply congrArg c.order
            apply Fin.ext
            simp [next]
      have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
      have hboundaryLe : c.order boundary ≤ c.order next := by
        rw [hboundaryOrder]
        omega
      have hnextIndex : next =
          (⟨boundary.val + 1, by simp only [boundary]; omega⟩ : Fin (m + 1)) := by
        apply Fin.ext
        simp [next, boundary]
        omega
      have hboundaryLe' : c.toBONG.order boundary ≤
          c.toBONG.order ⟨boundary.val + 1,
            by simp only [boundary]; omega⟩ := by
        change c.order boundary ≤ c.order _
        rw [← hnextIndex]
        exact hboundaryLe
      let S := Classical.choice
        (c.toBONG.beliCorollary44_i_unconditional c.good boundary
          (by simp only [boundary]; omega) hboundaryLe')
      have hcutEq : boundary.val + 1 = 2 * k := by
        simp only [boundary]
        omega
      let leftBONG := S.left.bong.castLength hcutEq
      have hvalues : ∀ i : Fin (2 * k),
          b.toBONG.value i = leftBONG.value i := by
        intro i
        let j : Fin (boundary.val + 1) := ⟨i.val, by omega⟩
        have hsource : S.left.sourceIndex j =
            (⟨i.val, i.isLt.trans_le h.bound⟩ : Fin (m + 1)) := by
          apply Fin.ext
          simp only [BONG.SegmentWitness.sourceIndex_val, Nat.zero_add]
          rfl
        have hu := hcValues i
        change c.valueUnit ⟨i.val, i.isLt.trans_le h.bound⟩ =
          b.valueUnit i at hu
        have hcast : leftBONG.valueUnit i = S.left.bong.valueUnit j := by
          dsimp only [leftBONG]
          simpa only [j] using
            (beliUniversal_valueUnit_castLength S.left.bong hcutEq i)
        change (b.toBONG.valueUnit i : K) =
          (leftBONG.valueUnit i : K)
        rw [hcast, S.left.valueUnit_eq, hsource]
        exact congrArg Units.val hu.symm
      let e := b.toBONG.latticeIsometryOfValueEq leftBONG hvalues
      let inclusion : Lattice.Representation
          (r.restrict S.left.carrier S.left.nondegenerate) r
          S.left.lattice M :=
        { toLinearMap := S.left.carrier.subtype
          injective := Subtype.val_injective
          map_bilin := by intro x y; rfl
          map_mem := by
            intro x hx
            exact S.left_contained x hx }
      exact inclusion.trans e.toRepresentation
    · have hbound := h.bound
      have heq : 2 * k = m + 1 := by omega
      let cFull : GoodBONG r M (2 * k) := c.castLength heq.symm
      have hvalues : ∀ i : Fin (2 * k),
          b.toBONG.value i = cFull.toBONG.value i := by
        intro i
        have hu := hcValues i
        change c.valueUnit ⟨i.val, i.isLt.trans_le h.bound⟩ =
          b.valueUnit i at hu
        change (b.toBONG.valueUnit i : K) =
          (cFull.toBONG.valueUnit i : K)
        rw [show cFull.toBONG.valueUnit i =
            c.toBONG.valueUnit ⟨i.val, by omega⟩ by
          simpa only [cFull, GoodBONG.valueUnit] using
            (beliUniversal_goodValueUnit_castLength c heq.symm i)]
        exact congrArg Units.val hu.symm
      exact (b.toBONG.latticeIsometryOfValueEq cFull.toBONG hvalues).toRepresentation
  let zeroForm := Lattice.zeroCoordinateQuadraticSpace (K := K)
  let zeroLattice := QuadraticSpace.zeroCoordinateBasisLattice (K := K)
  let f' : Lattice.Representation
      (Lattice.halfHyperbolicExtensionForm zeroForm k) r
      (Lattice.halfHyperbolicExtensionLattice zeroLattice k) M := by
    change Lattice.Representation T.form r T.lattice M
    exact f
  let split := Lattice.halfHyperbolicRepresentationSplitting k hM f'
  letI : AddCommGroup split.Residual := split.residualAddCommGroup
  letI : Module K split.Residual := split.residualModule
  let R : Lattice.QuadraticLatticeModel (K := K) :=
    { Carrier := split.Residual
      form := split.residualForm
      lattice := split.residualLattice }
  refine ⟨R, ⟨?_⟩⟩
  change Lattice.Isometry
    (Lattice.halfHyperbolicExtensionForm split.residualForm k) r
    (Lattice.halfHyperbolicExtensionLattice split.residualLattice k) M
  exact split.presentation

/-- The splitting-adapted good BONG satisfies the two numerical clauses in
Beli's Lemma 4.8.  The endpoint proof separates an empty residual lattice, a
zero-order first residual coefficient, and a positive-order first residual
coefficient. -/
theorem HalfHyperbolicSplitGoodBONGData.conditions
    {U : Type u} [AddCommGroup U] [Module K U]
    {r : QuadraticSpace K U} {M : Lattice K U} {m k : Nat}
    (D : HalfHyperbolicSplitGoodBONGData r M m k) (hk : 1 ≤ k) :
    UniversalLemma48Conditions D.bong k := by
  letI : AddCommGroup D.Residual := D.residualAddCommGroup
  letI : Module K D.Residual := D.residualModule
  let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) k
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  let b := standardHalfHyperbolicTowerBONG (K := K) k
  have hbPattern : b.HasHalfModularOrderPattern :=
    standardHalfHyperbolicTowerBONG_orderPattern (K := K) hk
  have hprefixOrder (i : Fin (2 * k)) :
      D.bong.order ⟨i.val, by have := D.rankEq; omega⟩ = b.order i := by
    have hv := congrArg (ordUnit K) (D.prefixValues i)
    change D.bong.order ⟨i.val, by have := D.rankEq; omega⟩ =
      b.order i at hv
    exact hv
  have hodd (j : Fin k) :
      D.bong.order ⟨2 * j.val, by have := D.rankEq; omega⟩ = 0 := by
    let i : Fin (2 * k) := ⟨2 * j.val, by omega⟩
    rw [show D.bong.order ⟨2 * j.val, by have := D.rankEq; omega⟩ =
        D.bong.order ⟨i.val, by have := D.rankEq; omega⟩ by rfl,
      hprefixOrder i]
    have hi : i = halfModularPairIndexEquiv k (j, (0 : Fin 2)) := by
      apply Fin.ext
      simp [i]
    rw [hi]
    exact (hbPattern j).1
  have heven (j : Fin k) :
      D.bong.order ⟨2 * j.val + 1, by have := D.rankEq; omega⟩ =
        -2 * (ramificationIndex K : Int) := by
    let i : Fin (2 * k) := ⟨2 * j.val + 1, by omega⟩
    rw [show D.bong.order
          ⟨2 * j.val + 1, by have := D.rankEq; omega⟩ =
        D.bong.order ⟨i.val, by have := D.rankEq; omega⟩ by rfl,
      hprefixOrder i]
    have hi : i = halfModularPairIndexEquiv k (j, (1 : Fin 2)) := by
      apply Fin.ext
      simp [i]
    rw [hi]
    exact (hbPattern j).2
  refine
    { bound := by have := D.rankEq; omega
      oddOrders := hodd
      evenOrders := heven
      endpoint := ?_ }
  by_cases hzero : finrank K D.Residual = 0
  · left
    have hfull : 2 * k = m + 1 := by
      have := D.rankEq
      omega
    rw [truncatedSegmentDefect_eq_top_of_standardFullPrefix
      (a := D.bong) hfull D.prefixValues]
    exact WithTop.coe_lt_top _
  · have hresPos : 0 < finrank K D.Residual := Nat.pos_of_ne_zero hzero
    have htail : 2 * k < m + 1 := by
      have := D.rankEq
      omega
    let j0 : Fin (finrank K D.Residual) := ⟨0, hresPos⟩
    have hlength : finrank K D.Residual =
        (finrank K D.Residual).pred + 1 :=
      (Nat.succ_pred_eq_of_pos hresPos).symm
    let c : GoodBONG D.residualForm D.residualLattice
        ((finrank K D.Residual).pred + 1) :=
      D.residualBONG.castLength hlength
    have hcNonneg : 0 ≤ c.order 0 :=
      (beliUniversalLemma22 c.toBONG).mp D.residualIntegral
    have hcastOrder : c.order 0 = D.residualBONG.order j0 := by
      rw [show c = D.residualBONG.castLength hlength by rfl,
        GoodBONG.order_castLength]
      rfl
    have hresNonneg : 0 ≤ D.residualBONG.order j0 := by
      rw [← hcastOrder]
      exact hcNonneg
    have htailOrder : D.bong.order ⟨2 * k, htail⟩ =
        D.residualBONG.order j0 := by
      have hv := congrArg (ordUnit K) (D.residualValues j0)
      change D.bong.order
          ⟨2 * k + j0.val, by have := D.rankEq; omega⟩ =
        D.residualBONG.order j0 at hv
      simpa [j0] using hv
    by_cases hresZero : D.residualBONG.order j0 = 0
    · right
      refine ⟨htail, ?_⟩
      rw [htailOrder, hresZero]
    · left
      have hresPositive : 0 < D.residualBONG.order j0 := by omega
      have htailPositive : 0 < D.bong.order ⟨2 * k, htail⟩ := by
        rw [htailOrder]
        exact hresPositive
      have hlast : D.bong.order ⟨2 * k - 1, by omega⟩ =
          -2 * (ramificationIndex K : Int) := by
        have h := heven (⟨k - 1, by omega⟩ : Fin k)
        convert h using 1
        apply congrArg D.bong.order
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      exact twoE_lt_truncatedSegmentDefect_of_standardPrefix_of_tail_pos
        (a := D.bong) hk (by have := D.rankEq; omega) htail
        D.prefixValues hlast htailPositive

/-- The two clauses of Lemma 4.8 are intrinsic to the lattice: changing the
chosen good BONG preserves every order and the truncated segment defect. -/
theorem UniversalLemma48Conditions.of_changeGoodBONG
    {U : Type u} [AddCommGroup U] [Module K U]
    {r : QuadraticSpace K U} {M : Lattice K U} {m k : Nat}
    {a b : GoodBONG r M (m + 1)}
    (h : UniversalLemma48Conditions b k) :
    UniversalLemma48Conditions a k := by
  letI : GoodBONGClassificationLaws.{u, u, u} K :=
    goodBONGClassificationLawsProved K
  letI : Beli2006PrefixChangeLaws.{u, u} K :=
    prefixChangeLawsOfClassification
  have horders : a.SameOrders b := a.order_invariant b
  refine
    { bound := h.bound
      oddOrders := ?_
      evenOrders := ?_
      endpoint := ?_ }
  · intro j
    rw [horders]
    exact h.oddOrders j
  · intro j
    rw [horders]
    exact h.evenOrders j
  · rcases h.endpoint with hdefect | ⟨htail, htailOrder⟩
    · left
      rw [a.truncatedSegmentDefect_invariant b
        ((-1 : Kˣ) ^ k) 1 (2 * k)]
      exact hdefect
    · right
      refine ⟨htail, ?_⟩
      rw [horders]
      exact htailOrder

/-- Necessity in Beli's Lemma 4.8.  An actual splitting first supplies an
adapted good BONG; the preceding invariance theorem then returns the result to
the arbitrary good BONG appearing in the paper's statement. -/
theorem universalLemma48Conditions_of_splitsHalfHyperbolic
    {U : Type u} [AddCommGroup U] [Module K U]
    {r : QuadraticSpace K U} {M : Lattice K U} {m k : Nat}
    (hk : 1 ≤ k) (a : GoodBONG r M (m + 1))
    (hM : Lattice.IsIntegral r M)
    (hsplit : (Lattice.quadraticLatticeModel r M).SplitsHalfHyperbolic k) :
    UniversalLemma48Conditions a k := by
  let D := halfHyperbolicSplitGoodBONGData hk a hM hsplit
  exact UniversalLemma48Conditions.of_changeGoodBONG
    (a := a) (b := D.bong) (D.conditions hk)

/-- Beli, Lemma 4.8: an integral lattice splits
`1/2 A(0,0)^k` exactly under the displayed alternating-order and endpoint
defect conditions. -/
theorem beliUniversalLemma48
    {U : Type u} [AddCommGroup U] [Module K U]
    {r : QuadraticSpace K U} {M : Lattice K U} {m k : Nat}
    (hk : 1 ≤ k) (hM : Lattice.IsIntegral r M)
    (a : GoodBONG r M (m + 1)) :
    (Lattice.quadraticLatticeModel r M).SplitsHalfHyperbolic k ↔
      UniversalLemma48Conditions a k := by
  constructor
  · exact universalLemma48Conditions_of_splitsHalfHyperbolic hk a hM
  · exact fun h ↦ h.splitsHalfHyperbolic hk hM

end BONG.GoodBONG

end Bong
