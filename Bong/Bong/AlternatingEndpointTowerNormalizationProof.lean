/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.AlternatingEndpointTowerNormalization
import Bong.Bong.AlternatingEndpointTowerRepresentationProof
import Bong.Bong.BeliEndpointNormGenerator
import Bong.Dyadic.UnramifiedNormDirectProof

/-!
# Proof of integral normalization for alternating endpoint towers

The normalization used in Beli (2019), Lemmas 7.17--7.18, has the rigid order
profile `R, R - 2e, R, R - 2e, ...`.  At a binary endpoint every unit class is
an allowed norm-generator multiplier.  Exact coefficients can therefore be
fixed one binary block at a time.  If the last source and target blocks have
opposite endpoint classes, multiplying the boundary pair by `Delta` toggles
the last two endpoint classes simultaneously; equality of the total
determinant class rules out a lone unmatched block.
-/

namespace Bong

open Dyadic

universe u v

namespace AlternatingEndpointNormalization

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [laws : DyadicDiscriminantClassLaws K]

/-- The rigid order profile is inherited by the initial subtower. -/
theorem orderProfile_init
    {pairs : Nat} {a : Fin (2 * (pairs + 1)) → Kˣ} {R : Int}
    (ha : AlternatingEndpointOrderProfile a R) :
    AlternatingEndpointOrderProfile
      (AlternatingEndpointTower.init a) R := by
  intro t
  simpa [AlternatingEndpointOrderProfile,
    AlternatingEndpointTower.init] using ha ⟨t.val, by omega⟩

/-- Two binary endpoint blocks in the square branch have the same determinant
square class. -/
theorem pairProduct_isSquare_of_both_square
    (a₀ a₁ b₀ b₁ : Kˣ)
    (ha : IsSquare (-(a₀ * a₁)))
    (hb : IsSquare (-(b₀ * b₁))) :
    IsSquare ((a₀ * a₁) * (b₀ * b₁)) := by
  have h := ha.mul hb
  have heq : (-(a₀ * a₁)) * (-(b₀ * b₁)) =
      (a₀ * a₁) * (b₀ * b₁) := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg]
    ring
  rw [heq] at h
  exact h

/-- Two binary endpoint blocks in the discriminant branch also have the same
determinant square class; the two `Delta` factors cancel. -/
theorem pairProduct_isSquare_of_both_discriminant
    (a₀ a₁ b₀ b₁ : Kˣ)
    (ha : IsSquare (-(a₀ * a₁) * laws.discriminantUnit))
    (hb : IsSquare (-(b₀ * b₁) * laws.discriminantUnit)) :
    IsSquare ((a₀ * a₁) * (b₀ * b₁)) := by
  have hdelta : IsSquare (laws.discriminantUnit ^ 2) :=
    ⟨laws.discriminantUnit, by simp [pow_two]⟩
  have h := (ha.mul hb).div hdelta
  have heq :
      ((-(a₀ * a₁) * laws.discriminantUnit) *
          (-(b₀ * b₁) * laws.discriminantUnit)) /
          laws.discriminantUnit ^ 2 =
        (a₀ * a₁) * (b₀ * b₁) := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul,
      Units.val_pow_eq_pow_val, Units.val_neg]
    field_simp [Units.ne_zero laws.discriminantUnit]
  rw [heq] at h
  exact h

/-- The distinguished discriminant class is genuinely nonsquare. -/
theorem discriminantUnit_not_isSquare : ¬IsSquare laws.discriminantUnit := by
  intro hsquare
  have htop := quadraticDefect_eq_top_of_isSquare (K := K) hsquare
  rw [laws.discriminant_defect] at htop
  exact ENat.coe_ne_top (2 * ramificationIndex K) htop

/-- Opposite endpoint branches are incompatible with equality of the binary
determinant square classes. -/
theorem false_of_square_discriminant_and_pairProduct_square
    (a₀ a₁ b₀ b₁ : Kˣ)
    (ha : IsSquare (-(a₀ * a₁)))
    (hb : IsSquare (-(b₀ * b₁) * laws.discriminantUnit))
    (hdet : IsSquare ((a₀ * a₁) * (b₀ * b₁))) : False := by
  have htwisted : IsSquare
      (((a₀ * a₁) * (b₀ * b₁)) * laws.discriminantUnit) := by
    have h := ha.mul hb
    have heq :
        (-(a₀ * a₁)) *
            (-(b₀ * b₁) * laws.discriminantUnit) =
          ((a₀ * a₁) * (b₀ * b₁)) * laws.discriminantUnit := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_neg]
      ring
    rw [heq] at h
    exact h
  have hdelta := htwisted.div hdet
  have hcancel :
      (((a₀ * a₁) * (b₀ * b₁)) * laws.discriminantUnit) /
          ((a₀ * a₁) * (b₀ * b₁)) =
        laws.discriminantUnit := by simp
  rw [hcancel] at hdelta
  exact discriminantUnit_not_isSquare (K := K) hdelta

/-- Symmetric form of the preceding incompatibility. -/
theorem false_of_discriminant_square_and_pairProduct_square
    (a₀ a₁ b₀ b₁ : Kˣ)
    (ha : IsSquare (-(a₀ * a₁) * laws.discriminantUnit))
    (hb : IsSquare (-(b₀ * b₁)))
    (hdet : IsSquare ((a₀ * a₁) * (b₀ * b₁))) : False := by
  exact false_of_square_discriminant_and_pairProduct_square
    (laws := laws) b₀ b₁ a₀ a₁ hb ha (by
      simpa only [mul_comm] using hdet)

/-- Multiplying one coefficient of a square endpoint pair by `Delta` moves
the pair to the discriminant endpoint class. -/
theorem endpoint_square_to_discriminant_after_mul_discriminant
    (p : Kˣ) (hp : IsSquare (-p)) :
    IsSquare (-(laws.discriminantUnit * p) *
      laws.discriminantUnit) := by
  have hdeltaSquare : IsSquare (laws.discriminantUnit ^ 2) :=
    ⟨laws.discriminantUnit, by simp [pow_two]⟩
  have h := hp.mul hdeltaSquare
  have heq : (-p) * laws.discriminantUnit ^ 2 =
      -(laws.discriminantUnit * p) * laws.discriminantUnit := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val]
    ring
  rw [heq] at h
  exact h

/-- Multiplying one coefficient of a discriminant endpoint pair by `Delta`
moves the pair to the square endpoint class. -/
theorem endpoint_discriminant_to_square_after_mul_discriminant
    (p : Kˣ)
    (hp : IsSquare (-p * laws.discriminantUnit)) :
    IsSquare (-(laws.discriminantUnit * p)) := by
  have heq : -(laws.discriminantUnit * p) =
      -p * laws.discriminantUnit := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg]
    ring
  rw [heq]
  exact hp

/-- Multiplying one side of a determinant comparison by a square preserves
equality of square classes. -/
theorem squareFactor_preserves_productSquare
    (d x y : Kˣ) (hxy : IsSquare (x * y)) :
    IsSquare ((d ^ 2 * x) * y) := by
  have h := (show IsSquare (d ^ 2) from
    ⟨d, by simp [pow_two]⟩).mul hxy
  have heq : d ^ 2 * (x * y) = (d ^ 2 * x) * y := by
    ac_rfl
  rw [heq] at h
  exact h

/-- The determinant of a nonempty endpoint tower splits into the determinant
of its initial tower and the product of its last two coefficients. -/
theorem diagonalUnitDeterminant_eq_init_mul_lastPair
    {pairs : Nat} (a : Fin (2 * (pairs + 1)) → Kˣ) :
    BONG.GoodBONG.diagonalUnitDeterminant a =
      BONG.GoodBONG.diagonalUnitDeterminant
          (AlternatingEndpointTower.init a) *
        (AlternatingEndpointTower.lastPair a 0 *
          AlternatingEndpointTower.lastPair a 1) := by
  calc
    BONG.GoodBONG.diagonalUnitDeterminant a =
        BONG.GoodBONG.diagonalUnitDeterminant
          (Fin.append (AlternatingEndpointTower.init a)
            (AlternatingEndpointTower.lastPair a)) := by
      rw [AlternatingEndpointTower.append_init_lastPair]
    _ = BONG.GoodBONG.diagonalUnitDeterminant
          (AlternatingEndpointTower.init a) *
        BONG.GoodBONG.diagonalUnitDeterminant
          (AlternatingEndpointTower.lastPair a) :=
      AlternatingEndpointTower.diagonalUnitDeterminant_append _ _
    _ = _ := by
      simp [BONG.GoodBONG.diagonalUnitDeterminant]

/-- If full endpoint towers have equal determinant square class and their
last binary blocks do too, then their initial subtowers have equal determinant
square class. -/
theorem initDeterminant_product_isSquare
    {pairs : Nat} (a b : Fin (2 * (pairs + 1)) → Kˣ)
    (hfull : IsSquare
      (BONG.GoodBONG.diagonalUnitDeterminant a *
        BONG.GoodBONG.diagonalUnitDeterminant b))
    (hlast : IsSquare
      ((AlternatingEndpointTower.lastPair a 0 *
          AlternatingEndpointTower.lastPair a 1) *
        (AlternatingEndpointTower.lastPair b 0 *
          AlternatingEndpointTower.lastPair b 1))) :
    IsSquare
      (BONG.GoodBONG.diagonalUnitDeterminant
          (AlternatingEndpointTower.init a) *
        BONG.GoodBONG.diagonalUnitDeterminant
          (AlternatingEndpointTower.init b)) := by
  rw [diagonalUnitDeterminant_eq_init_mul_lastPair,
    diagonalUnitDeterminant_eq_init_mul_lastPair] at hfull
  have hquotient := hfull.div hlast
  have hcancel :
      ((BONG.GoodBONG.diagonalUnitDeterminant
          (AlternatingEndpointTower.init a) *
          (AlternatingEndpointTower.lastPair a 0 *
            AlternatingEndpointTower.lastPair a 1)) *
        (BONG.GoodBONG.diagonalUnitDeterminant
          (AlternatingEndpointTower.init b) *
          (AlternatingEndpointTower.lastPair b 0 *
            AlternatingEndpointTower.lastPair b 1))) /
        ((AlternatingEndpointTower.lastPair a 0 *
            AlternatingEndpointTower.lastPair a 1) *
          (AlternatingEndpointTower.lastPair b 0 *
            AlternatingEndpointTower.lastPair b 1)) =
      BONG.GoodBONG.diagonalUnitDeterminant
          (AlternatingEndpointTower.init a) *
        BONG.GoodBONG.diagonalUnitDeterminant
          (AlternatingEndpointTower.init b) := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul]
    field_simp [Units.ne_zero
      (AlternatingEndpointTower.lastPair a 0),
      Units.ne_zero (AlternatingEndpointTower.lastPair a 1),
      Units.ne_zero (AlternatingEndpointTower.lastPair b 0),
      Units.ne_zero (AlternatingEndpointTower.lastPair b 1)]
  rw [hcancel] at hquotient
  exact hquotient

/-- Once the source and target endpoint classes agree pair by pair, exact
coefficient normalization is obtained by replacing the binary blocks from
right to left.  Every replacement is supported on its own consecutive
segment, so the already normalized suffix is left fixed. -/
theorem exists_normalizedRigidEndpointPrefix_of_pairwiseDeterminants
    [DyadicUnramifiedNormLaws K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    {n pairs : Nat}
    (b : BONG.GoodBONG q L (n + 1))
    (hbound : 2 * pairs ≤ n + 1)
    (target : Fin (2 * pairs) → Kˣ) (R : Int)
    (hsourceProfile : AlternatingEndpointOrderProfile
      (b.prefixValueUnits (2 * pairs) hbound) R)
    (htargetProfile : AlternatingEndpointOrderProfile target R)
    (hpairDet : ∀ t : Fin pairs, IsSquare
      (((b.prefixValueUnits (2 * pairs) hbound)
          ⟨2 * t.val, by omega⟩ *
        (b.prefixValueUnits (2 * pairs) hbound)
          ⟨2 * t.val + 1, by omega⟩) *
       (target ⟨2 * t.val, by omega⟩ *
        target ⟨2 * t.val + 1, by omega⟩))) :
    ∃ c : BONG.GoodBONG q L (n + 1),
      (∀ i : Fin (2 * pairs),
        c.valueUnit ⟨i.val, i.isLt.trans_le hbound⟩ = target i) ∧
      (∀ j : Fin (n + 1), 2 * pairs ≤ j.val →
        c.valueUnit j = b.valueUnit j) := by
  induction pairs generalizing b with
  | zero =>
      refine ⟨b, ?_, ?_⟩
      · exact fun i ↦ Fin.elim0 i
      · intro j _
        rfl
  | succ pairs ih =>
      let left : Fin (n + 1) := ⟨2 * pairs, by omega⟩
      have hi : left.val + 1 < n + 1 := by
        simp only [left]
        omega
      let right : Fin (n + 1) := ⟨left.val + 1, hi⟩
      let targetLeft : Kˣ := target ⟨2 * pairs, by omega⟩
      let targetRight : Kˣ := target ⟨2 * pairs + 1, by omega⟩
      have hsLast := hsourceProfile ⟨pairs, by omega⟩
      have htLast := htargetProfile ⟨pairs, by omega⟩
      have hsLeft : ordUnit K (b.valueUnit left) = R := by
        simpa [AlternatingEndpointOrderProfile,
          BONG.GoodBONG.prefixValueUnits, left] using hsLast.1
      have hsRight : ordUnit K (b.valueUnit right) =
          R - 2 * (ramificationIndex K : Int) := by
        simpa [AlternatingEndpointOrderProfile,
          BONG.GoodBONG.prefixValueUnits, left, right] using hsLast.2
      have htLeft : ordUnit K targetLeft = R := by
        simpa [AlternatingEndpointOrderProfile, targetLeft] using htLast.1
      have htRight : ordUnit K targetRight =
          R - 2 * (ramificationIndex K : Int) := by
        simpa [AlternatingEndpointOrderProfile, targetRight] using htLast.2
      have hgap : b.order right - b.order left =
          -(2 * (ramificationIndex K : Int)) := by
        change ordUnit K (b.valueUnit right) -
          ordUnit K (b.valueUnit left) = _
        rw [hsLeft, hsRight]
        ring
      have hzeroOrder : ordUnit K targetLeft =
          ordUnit K (b.valueUnit left) := by
        rw [hsLeft, htLeft]
      have honeOrder : ordUnit K targetRight =
          ordUnit K (b.valueUnit right) := by
        rw [hsRight, htRight]
      have hdetLast : IsSquare
          ((b.valueUnit left * b.valueUnit right) *
            (targetLeft * targetRight)) := by
        simpa [BONG.GoodBONG.prefixValueUnits, left, right,
          targetLeft, targetRight] using
          hpairDet ⟨pairs, by omega⟩
      rcases BONG.exists_endpointExactPairReplacementData
          b left hi targetLeft targetRight hgap hzeroOrder honeOrder
            hdetLast with ⟨E⟩
      have hsmall : 2 * pairs ≤ n + 1 := by omega
      have heSourceProfile : AlternatingEndpointOrderProfile
          (E.bong.prefixValueUnits (2 * pairs) hsmall) R := by
        intro t
        have hs := hsourceProfile ⟨t.val, by omega⟩
        let j0 : Fin (n + 1) :=
          ⟨2 * t.val, by omega⟩
        let j1 : Fin (n + 1) :=
          ⟨2 * t.val + 1, by omega⟩
        have hj0 : j0.val < left.val := by
          simp only [j0, left]
          omega
        have hj1 : j1.val < left.val := by
          simp only [j1, left]
          omega
        constructor
        · simpa [AlternatingEndpointOrderProfile,
            BONG.GoodBONG.prefixValueUnits, j0] using
            congrArg (ordUnit K) (E.valueUnit_before j0 hj0) |>.trans
              hs.1
        · simpa [AlternatingEndpointOrderProfile,
            BONG.GoodBONG.prefixValueUnits, j1] using
            congrArg (ordUnit K) (E.valueUnit_before j1 hj1) |>.trans
              hs.2
      have htInitProfile : AlternatingEndpointOrderProfile
          (AlternatingEndpointTower.init target) R :=
        orderProfile_init htargetProfile
      have hpairInit : ∀ t : Fin pairs, IsSquare
          (((E.bong.prefixValueUnits (2 * pairs) hsmall)
              ⟨2 * t.val, by omega⟩ *
            (E.bong.prefixValueUnits (2 * pairs) hsmall)
              ⟨2 * t.val + 1, by omega⟩) *
           ((AlternatingEndpointTower.init target)
              ⟨2 * t.val, by omega⟩ *
            (AlternatingEndpointTower.init target)
              ⟨2 * t.val + 1, by omega⟩)) := by
        intro t
        have hp := hpairDet ⟨t.val, by omega⟩
        let j0 : Fin (n + 1) :=
          ⟨2 * t.val, by omega⟩
        let j1 : Fin (n + 1) :=
          ⟨2 * t.val + 1, by omega⟩
        have hj0 : j0.val < left.val := by
          simp only [j0, left]
          omega
        have hj1 : j1.val < left.val := by
          simp only [j1, left]
          omega
        have he0 := E.valueUnit_before j0 hj0
        have he1 := E.valueUnit_before j1 hj1
        simpa [BONG.GoodBONG.prefixValueUnits,
          AlternatingEndpointTower.init, j0, j1] using
          (show IsSquare
            (((E.bong.valueUnit j0) * (E.bong.valueUnit j1)) *
              (target ⟨2 * t.val, by omega⟩ *
                target ⟨2 * t.val + 1, by omega⟩)) from by
              rw [he0, he1]
              simpa [BONG.GoodBONG.prefixValueUnits, j0, j1] using hp)
      rcases ih E.bong hsmall (AlternatingEndpointTower.init target)
          heSourceProfile htInitProfile hpairInit with
        ⟨c, hprefix, hsuffix⟩
      refine ⟨c, ?_, ?_⟩
      · intro k
        let j : Fin (n + 1) :=
          ⟨k.val, k.isLt.trans_le hbound⟩
        by_cases hk : k.val < 2 * pairs
        · let k' : Fin (2 * pairs) := ⟨k.val, hk⟩
          have hj :
              (⟨k'.val, k'.isLt.trans_le hsmall⟩ : Fin (n + 1)) = j :=
            Fin.ext rfl
          have htarget :
              (AlternatingEndpointTower.init target) k' = target k := by
            rfl
          simpa only [j, hj, htarget] using hprefix k'
        · have hkCases : k.val = 2 * pairs ∨
              k.val = 2 * pairs + 1 := by omega
          rcases hkCases with hkLeft | hkRight
          · have hjLeft : j = left := Fin.ext hkLeft
            calc
              c.valueUnit j = E.bong.valueUnit j :=
                hsuffix j (by simp only [j]; omega)
              _ = targetLeft := by rw [hjLeft, E.valueUnit_left]
              _ = target k := by
                simp only [targetLeft]
                congr 1
                exact Fin.ext hkLeft.symm
          · have hjRight : j = right := by
              apply Fin.ext
              simp only [j, right, left]
              omega
            calc
              c.valueUnit j = E.bong.valueUnit j :=
                hsuffix j (by simp only [j]; omega)
              _ = targetRight := by rw [hjRight, E.valueUnit_right]
              _ = target k := by
                simp only [targetRight]
                congr 1
                exact Fin.ext hkRight.symm
      · intro j hj
        calc
          c.valueUnit j = E.bong.valueUnit j := hsuffix j (by omega)
          _ = b.valueUnit j := E.valueUnit_after j (by
            simp only [left]
            omega)

/-- The global determinant condition aligns the endpoint classes pair by
pair.  A mismatch at the final block is transported one block to the left by
multiplying the intervening boundary pair by `Delta`; the determinant changes
only by the square `Delta^2`.  At the first block a remaining mismatch would
contradict the global determinant square class. -/
theorem exists_pairwiseAlignedRigidEndpointPrefix
    [DyadicUnramifiedNormLaws K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    {n pairs : Nat}
    (b : BONG.GoodBONG q L (n + 1))
    (hbound : 2 * pairs ≤ n + 1)
    (target : Fin (2 * pairs) → Kˣ) (R : Int)
    (hsource : AlternatingEndpointPairClasses
      (b.prefixValueUnits (2 * pairs) hbound))
    (htarget : AlternatingEndpointPairClasses target)
    (hsourceProfile : AlternatingEndpointOrderProfile
      (b.prefixValueUnits (2 * pairs) hbound) R)
    (htargetProfile : AlternatingEndpointOrderProfile target R)
    (hdet : IsSquare
      (BONG.GoodBONG.diagonalUnitDeterminant
          (b.prefixValueUnits (2 * pairs) hbound) *
        BONG.GoodBONG.diagonalUnitDeterminant target)) :
    ∃ c : BONG.GoodBONG q L (n + 1),
      AlternatingEndpointOrderProfile
          (c.prefixValueUnits (2 * pairs) hbound) R ∧
      (∀ t : Fin pairs, IsSquare
        (((c.prefixValueUnits (2 * pairs) hbound)
            ⟨2 * t.val, by omega⟩ *
          (c.prefixValueUnits (2 * pairs) hbound)
            ⟨2 * t.val + 1, by omega⟩) *
         (target ⟨2 * t.val, by omega⟩ *
          target ⟨2 * t.val + 1, by omega⟩))) ∧
      (∀ j : Fin (n + 1), 2 * pairs ≤ j.val →
        c.valueUnit j = b.valueUnit j) := by
  induction pairs generalizing b with
  | zero =>
      refine ⟨b, ?_, ?_, ?_⟩
      · exact fun t ↦ Fin.elim0 t
      · exact fun t ↦ Fin.elim0 t
      · intro j _
        rfl
  | succ pairs ih =>
      have hsmall : 2 * pairs ≤ n + 1 := by omega
      let source := b.prefixValueUnits (2 * (pairs + 1)) hbound
      let sourceInit := AlternatingEndpointTower.init source
      let targetInit := AlternatingEndpointTower.init target
      have hsourceInitEq : sourceInit =
          b.prefixValueUnits (2 * pairs) hsmall := by
        funext k
        rfl
      have htargetInit : AlternatingEndpointPairClasses targetInit :=
        AlternatingEndpointTower.pairClasses_init target htarget
      have htargetInitProfile : AlternatingEndpointOrderProfile targetInit R :=
        orderProfile_init htargetProfile
      have hfinish : ∀
          (d : BONG.GoodBONG q L (n + 1)),
          (hdsource : AlternatingEndpointPairClasses
            (d.prefixValueUnits (2 * (pairs + 1)) hbound)) →
          (hdprofile : AlternatingEndpointOrderProfile
            (d.prefixValueUnits (2 * (pairs + 1)) hbound) R) →
          (hdlast : IsSquare
            ((AlternatingEndpointTower.lastPair
                (d.prefixValueUnits (2 * (pairs + 1)) hbound) 0 *
              AlternatingEndpointTower.lastPair
                (d.prefixValueUnits (2 * (pairs + 1)) hbound) 1) *
             (AlternatingEndpointTower.lastPair target 0 *
              AlternatingEndpointTower.lastPair target 1))) →
          (hdglobal : IsSquare
            (BONG.GoodBONG.diagonalUnitDeterminant
                (d.prefixValueUnits (2 * (pairs + 1)) hbound) *
              BONG.GoodBONG.diagonalUnitDeterminant target)) →
          (hdsuffix : ∀ j : Fin (n + 1),
            2 * (pairs + 1) ≤ j.val →
              d.valueUnit j = b.valueUnit j) →
          ∃ c : BONG.GoodBONG q L (n + 1),
            AlternatingEndpointOrderProfile
                (c.prefixValueUnits (2 * (pairs + 1)) hbound) R ∧
            (∀ t : Fin (pairs + 1), IsSquare
              (((c.prefixValueUnits (2 * (pairs + 1)) hbound)
                  ⟨2 * t.val, by omega⟩ *
                (c.prefixValueUnits (2 * (pairs + 1)) hbound)
                  ⟨2 * t.val + 1, by omega⟩) *
               (target ⟨2 * t.val, by omega⟩ *
                target ⟨2 * t.val + 1, by omega⟩))) ∧
            (∀ j : Fin (n + 1), 2 * (pairs + 1) ≤ j.val →
              c.valueUnit j = b.valueUnit j) := by
        intro d hdsource hdprofile hdlast hdglobal hdsuffix
        let dsource :=
          d.prefixValueUnits (2 * (pairs + 1)) hbound
        let dsourceInit := AlternatingEndpointTower.init dsource
        have hdsourceInitEq : dsourceInit =
            d.prefixValueUnits (2 * pairs) hsmall := by
          funext k
          rfl
        have hdinitClasses : AlternatingEndpointPairClasses
            (d.prefixValueUnits (2 * pairs) hsmall) := by
          rw [← hdsourceInitEq]
          exact AlternatingEndpointTower.pairClasses_init dsource hdsource
        have hdinitProfile : AlternatingEndpointOrderProfile
            (d.prefixValueUnits (2 * pairs) hsmall) R := by
          rw [← hdsourceInitEq]
          exact orderProfile_init hdprofile
        have hdinitDet : IsSquare
            (BONG.GoodBONG.diagonalUnitDeterminant
                (d.prefixValueUnits (2 * pairs) hsmall) *
              BONG.GoodBONG.diagonalUnitDeterminant targetInit) := by
          rw [← hdsourceInitEq]
          exact initDeterminant_product_isSquare dsource target
            hdglobal hdlast
        rcases ih d hsmall targetInit hdinitClasses htargetInit
            hdinitProfile htargetInitProfile hdinitDet with
          ⟨c, hcprofile, hcpairs, hcsuffix⟩
        refine ⟨c, ?_, ?_, ?_⟩
        · intro t
          by_cases ht : t.val < pairs
          · let t' : Fin pairs := ⟨t.val, ht⟩
            have hp := hcprofile t'
            simpa [AlternatingEndpointOrderProfile,
              BONG.GoodBONG.prefixValueUnits, t'] using hp
          · have htLast : t.val = pairs := by omega
            have hp := hdprofile ⟨pairs, by omega⟩
            let j0 : Fin (n + 1) := ⟨2 * pairs, by omega⟩
            let j1 : Fin (n + 1) := ⟨2 * pairs + 1, by omega⟩
            have hc0 := hcsuffix j0 (by simp [j0])
            have hc1 := hcsuffix j1 (by simp [j1])
            constructor
            · simpa [AlternatingEndpointOrderProfile,
                BONG.GoodBONG.prefixValueUnits, j0, htLast] using
                congrArg (ordUnit K) hc0 |>.trans hp.1
            · simpa [AlternatingEndpointOrderProfile,
                BONG.GoodBONG.prefixValueUnits, j1, htLast] using
                congrArg (ordUnit K) hc1 |>.trans hp.2
        · intro t
          by_cases ht : t.val < pairs
          · let t' : Fin pairs := ⟨t.val, ht⟩
            have hp := hcpairs t'
            simpa [BONG.GoodBONG.prefixValueUnits,
              AlternatingEndpointTower.init, targetInit, t'] using hp
          · have htLast : t.val = pairs := by omega
            let j0 : Fin (n + 1) := ⟨2 * pairs, by omega⟩
            let j1 : Fin (n + 1) := ⟨2 * pairs + 1, by omega⟩
            have hc0 := hcsuffix j0 (by simp [j0])
            have hc1 := hcsuffix j1 (by simp [j1])
            have hdlast' := hdlast
            simpa [BONG.GoodBONG.prefixValueUnits,
              AlternatingEndpointTower.lastPair, dsource, j0, j1,
              htLast] using
              (show IsSquare
                (((c.valueUnit j0) * (c.valueUnit j1)) *
                  (target ⟨2 * pairs, by omega⟩ *
                    target ⟨2 * pairs + 1, by omega⟩)) from by
                  rw [hc0, hc1]
                  simpa [BONG.GoodBONG.prefixValueUnits,
                    AlternatingEndpointTower.lastPair, dsource, j0, j1]
                    using hdlast')
        · intro j hj
          calc
            c.valueUnit j = d.valueUnit j := hcsuffix j (by omega)
            _ = b.valueUnit j := hdsuffix j hj
      have hboundaryChange : pairs ≠ 0 →
          ∃ c : BONG.GoodBONG q L (n + 1),
            AlternatingEndpointOrderProfile
                (c.prefixValueUnits (2 * (pairs + 1)) hbound) R ∧
            AlternatingEndpointPairClasses
                (c.prefixValueUnits (2 * (pairs + 1)) hbound) ∧
            IsSquare
              (BONG.GoodBONG.diagonalUnitDeterminant
                  (c.prefixValueUnits (2 * (pairs + 1)) hbound) *
                BONG.GoodBONG.diagonalUnitDeterminant target) ∧
            (∀ j : Fin (n + 1), 2 * (pairs + 1) ≤ j.val →
              c.valueUnit j = b.valueUnit j) ∧
            (IsSquare
                (-(AlternatingEndpointTower.lastPair source 0 *
                  AlternatingEndpointTower.lastPair source 1)) →
              IsSquare
                (-(AlternatingEndpointTower.lastPair
                    (c.prefixValueUnits
                      (2 * (pairs + 1)) hbound) 0 *
                  AlternatingEndpointTower.lastPair
                    (c.prefixValueUnits
                      (2 * (pairs + 1)) hbound) 1) *
                  laws.discriminantUnit)) ∧
            (IsSquare
                (-(AlternatingEndpointTower.lastPair source 0 *
                    AlternatingEndpointTower.lastPair source 1) *
                  laws.discriminantUnit) →
              IsSquare
                (-(AlternatingEndpointTower.lastPair
                    (c.prefixValueUnits
                      (2 * (pairs + 1)) hbound) 0 *
                  AlternatingEndpointTower.lastPair
                    (c.prefixValueUnits
                      (2 * (pairs + 1)) hbound) 1))) := by
        intro hpairs
        let boundary : Fin (n + 1) := ⟨2 * pairs - 1, by omega⟩
        have hboundary : boundary.val + 1 < n + 1 := by
          simp only [boundary]
          omega
        let next : Fin (n + 1) := ⟨boundary.val + 1, hboundary⟩
        have hprevProfile := hsourceProfile ⟨pairs - 1, by omega⟩
        have hlastProfile := hsourceProfile ⟨pairs, by omega⟩
        have hprevLow : ordUnit K (b.valueUnit boundary) =
            R - 2 * (ramificationIndex K : Int) := by
          let prevLow : Fin (n + 1) :=
            ⟨2 * (pairs - 1) + 1, by omega⟩
          have hp : ordUnit K (b.valueUnit prevLow) =
              R - 2 * (ramificationIndex K : Int) := by
            simpa [AlternatingEndpointOrderProfile,
              BONG.GoodBONG.prefixValueUnits, prevLow] using
              hprevProfile.2
          have heq : prevLow = boundary := by
            apply Fin.ext
            simp only [prevLow, boundary]
            omega
          simpa only [heq] using hp
        have hnextHigh : ordUnit K (b.valueUnit next) = R := by
          let lastHigh : Fin (n + 1) := ⟨2 * pairs, by omega⟩
          have hp : ordUnit K (b.valueUnit lastHigh) = R := by
            simpa [AlternatingEndpointOrderProfile,
              BONG.GoodBONG.prefixValueUnits, lastHigh] using
              hlastProfile.1
          have heq : lastHigh = next := by
            apply Fin.ext
            simp only [lastHigh, next, boundary]
            omega
          simpa only [← heq] using hp
        have hparameterOrder : ordUnit K
            (b.toBONG.adjacentParameter boundary hboundary) =
              2 * (ramificationIndex K : Int) := by
          rw [b.toBONG.ordUnit_adjacentParameter]
          change ordUnit K (b.valueUnit next) -
            ordUnit K (b.valueUnit boundary) = _
          rw [hprevLow, hnextHigh]
          ring
        have hu :=
          discriminantUnitClass_mem_beliNormGeneratorGroup_of_order_eq_twoE
            (b.toBONG.adjacentParameter boundary hboundary)
            hparameterOrder
        rcases BONG.exists_adjacentMultiplierData b boundary hboundary
            (discriminantValuationUnit (K := K)) hu with ⟨C⟩
        have hcProfile : AlternatingEndpointOrderProfile
            (C.bong.prefixValueUnits (2 * (pairs + 1)) hbound) R := by
          intro t
          have hp := hsourceProfile t
          let j0 : Fin (n + 1) := ⟨2 * t.val, by omega⟩
          let j1 : Fin (n + 1) := ⟨2 * t.val + 1, by omega⟩
          have hp0 : ordUnit K (b.valueUnit j0) = R := by
            simpa [AlternatingEndpointOrderProfile,
              BONG.GoodBONG.prefixValueUnits, j0] using hp.1
          have hp1 : ordUnit K (b.valueUnit j1) =
              R - 2 * (ramificationIndex K : Int) := by
            simpa [AlternatingEndpointOrderProfile,
              BONG.GoodBONG.prefixValueUnits, j1] using hp.2
          constructor
          · calc
              ordUnit K (C.bong.valueUnit j0) = C.bong.order j0 :=
                (C.bong.toBONG.order_eq_ordUnit j0).symm
              _ = b.order j0 := C.order_eq j0
              _ = ordUnit K (b.valueUnit j0) :=
                b.toBONG.order_eq_ordUnit j0
              _ = R := hp0
          · calc
              ordUnit K (C.bong.valueUnit j1) = C.bong.order j1 :=
                (C.bong.toBONG.order_eq_ordUnit j1).symm
              _ = b.order j1 := C.order_eq j1
              _ = ordUnit K (b.valueUnit j1) :=
                b.toBONG.order_eq_ordUnit j1
              _ = R - 2 * (ramificationIndex K : Int) := hp1
        let prev0 : Fin (n + 1) := ⟨2 * (pairs - 1), by omega⟩
        let prev1 : Fin (n + 1) := ⟨2 * (pairs - 1) + 1, by omega⟩
        let last0 : Fin (n + 1) := ⟨2 * pairs, by omega⟩
        let last1 : Fin (n + 1) := ⟨2 * pairs + 1, by omega⟩
        have hprev1 : prev1 = boundary := by
          apply Fin.ext
          simp only [prev1, boundary]
          omega
        have hlast0 : last0 = next := by
          apply Fin.ext
          simp only [last0, next, boundary]
          omega
        have hcPrev0 := C.valueUnit_before prev0 (by
          simp [prev0, boundary]
          omega)
        have hcPrev1 : C.bong.valueUnit prev1 =
            laws.discriminantUnit * b.valueUnit prev1 := by
          rw [hprev1]
          simpa only [discriminantValuationUnit] using C.valueUnit_left
        have hcLast0 : C.bong.valueUnit last0 =
            laws.discriminantUnit * b.valueUnit last0 := by
          rw [hlast0]
          simpa only [next, discriminantValuationUnit] using C.valueUnit_right
        have hcLast1 := C.valueUnit_after last1 (by
          simp [last1, boundary]
          omega)
        have hcPrevProduct : C.bong.valueUnit prev0 *
              C.bong.valueUnit prev1 =
            laws.discriminantUnit *
              (b.valueUnit prev0 * b.valueUnit prev1) := by
          rw [hcPrev0, hcPrev1]
          ac_rfl
        have hcLastProduct : C.bong.valueUnit last0 *
              C.bong.valueUnit last1 =
            laws.discriminantUnit *
              (b.valueUnit last0 * b.valueUnit last1) := by
          rw [hcLast0, hcLast1]
          ac_rfl
        have hcSource : AlternatingEndpointPairClasses
            (C.bong.prefixValueUnits (2 * (pairs + 1)) hbound) := by
          intro t
          by_cases hbefore : t.val + 1 < pairs
          · let j0 : Fin (n + 1) := ⟨2 * t.val, by omega⟩
            let j1 : Fin (n + 1) := ⟨2 * t.val + 1, by omega⟩
            have hc0 := C.valueUnit_before j0 (by
              simp [j0, boundary]
              omega)
            have hc1 := C.valueUnit_before j1 (by
              simp [j1, boundary]
              omega)
            have hs := hsource t
            change IsSquare (-(C.bong.valueUnit j0 * C.bong.valueUnit j1)) ∨
              IsSquare (-(C.bong.valueUnit j0 * C.bong.valueUnit j1) *
                laws.discriminantUnit)
            rw [hc0, hc1]
            simpa [BONG.GoodBONG.prefixValueUnits, j0, j1] using hs
          · have htCases : t.val = pairs - 1 ∨ t.val = pairs := by omega
            rcases htCases with htPrev | htLast
            · have hsPrev := hsource ⟨pairs - 1, by omega⟩
              have hsPrev' : IsSquare (-(b.valueUnit prev0 *
                    b.valueUnit prev1)) ∨
                  IsSquare (-(b.valueUnit prev0 * b.valueUnit prev1) *
                    laws.discriminantUnit) := by
                simpa [BONG.GoodBONG.prefixValueUnits, prev0, prev1]
                  using hsPrev
              have hpairC : IsSquare (-(C.bong.valueUnit prev0 *
                    C.bong.valueUnit prev1)) ∨
                  IsSquare (-(C.bong.valueUnit prev0 *
                    C.bong.valueUnit prev1) * laws.discriminantUnit) := by
                rw [hcPrevProduct]
                rcases hsPrev' with hpSquare | hpDiscriminant
                · right
                  exact endpoint_square_to_discriminant_after_mul_discriminant
                    (laws := laws) _ hpSquare
                · left
                  exact endpoint_discriminant_to_square_after_mul_discriminant
                    (laws := laws) _ hpDiscriminant
              simpa [BONG.GoodBONG.prefixValueUnits, prev0, prev1,
                htPrev] using hpairC
            · have hsLast :=
                AlternatingEndpointTower.pairClasses_lastPair source hsource
              have hsLast' : IsSquare (-(b.valueUnit last0 *
                    b.valueUnit last1)) ∨
                  IsSquare (-(b.valueUnit last0 * b.valueUnit last1) *
                    laws.discriminantUnit) := by
                simpa [source, BONG.GoodBONG.prefixValueUnits,
                  AlternatingEndpointTower.lastPair, last0, last1]
                  using hsLast
              have hpairC : IsSquare (-(C.bong.valueUnit last0 *
                    C.bong.valueUnit last1)) ∨
                  IsSquare (-(C.bong.valueUnit last0 *
                    C.bong.valueUnit last1) * laws.discriminantUnit) := by
                rw [hcLastProduct]
                rcases hsLast' with hpSquare | hpDiscriminant
                · right
                  exact endpoint_square_to_discriminant_after_mul_discriminant
                    (laws := laws) _ hpSquare
                · left
                  exact endpoint_discriminant_to_square_after_mul_discriminant
                    (laws := laws) _ hpDiscriminant
              simpa [BONG.GoodBONG.prefixValueUnits, last0, last1,
                htLast] using hpairC
        have hcPrefix := C.prefixProduct_afterChangedPair
          (2 * (pairs + 1)) (by simp [boundary]; omega) hbound
        have hcDetEq : BONG.GoodBONG.diagonalUnitDeterminant
              (C.bong.prefixValueUnits (2 * (pairs + 1)) hbound) =
            laws.discriminantUnit ^ 2 *
              BONG.GoodBONG.diagonalUnitDeterminant source := by
          rw [C.bong.diagonalUnitDeterminant_prefixValueUnits,
            b.diagonalUnitDeterminant_prefixValueUnits]
          simpa only [discriminantValuationUnit] using hcPrefix
        have hcGlobal : IsSquare
            (BONG.GoodBONG.diagonalUnitDeterminant
                (C.bong.prefixValueUnits (2 * (pairs + 1)) hbound) *
              BONG.GoodBONG.diagonalUnitDeterminant target) := by
          rw [hcDetEq]
          exact squareFactor_preserves_productSquare
            laws.discriminantUnit _ _ hdet
        have hcSuffix : ∀ j : Fin (n + 1),
            2 * (pairs + 1) ≤ j.val →
              C.bong.valueUnit j = b.valueUnit j := by
          intro j hj
          exact C.valueUnit_after j (by simp [boundary]; omega)
        have hflipSquare : IsSquare
              (-(AlternatingEndpointTower.lastPair source 0 *
                AlternatingEndpointTower.lastPair source 1)) →
            IsSquare
              (-(AlternatingEndpointTower.lastPair
                  (C.bong.prefixValueUnits
                    (2 * (pairs + 1)) hbound) 0 *
                AlternatingEndpointTower.lastPair
                  (C.bong.prefixValueUnits
                    (2 * (pairs + 1)) hbound) 1) *
                laws.discriminantUnit) := by
          intro hs
          have hs' : IsSquare (-(b.valueUnit last0 * b.valueUnit last1)) := by
            simpa [source, BONG.GoodBONG.prefixValueUnits,
              AlternatingEndpointTower.lastPair, last0, last1] using hs
          have ht := endpoint_square_to_discriminant_after_mul_discriminant
            (laws := laws) (b.valueUnit last0 * b.valueUnit last1) hs'
          have ht' : IsSquare (-(C.bong.valueUnit last0 *
                C.bong.valueUnit last1) * laws.discriminantUnit) := by
            rw [hcLastProduct]
            exact ht
          simpa [BONG.GoodBONG.prefixValueUnits,
            AlternatingEndpointTower.lastPair, last0, last1] using ht'
        have hflipDiscriminant : IsSquare
              (-(AlternatingEndpointTower.lastPair source 0 *
                  AlternatingEndpointTower.lastPair source 1) *
                laws.discriminantUnit) →
            IsSquare
              (-(AlternatingEndpointTower.lastPair
                  (C.bong.prefixValueUnits
                    (2 * (pairs + 1)) hbound) 0 *
                AlternatingEndpointTower.lastPair
                  (C.bong.prefixValueUnits
                    (2 * (pairs + 1)) hbound) 1)) := by
          intro hs
          have hs' : IsSquare (-(b.valueUnit last0 * b.valueUnit last1) *
              laws.discriminantUnit) := by
            simpa [source, BONG.GoodBONG.prefixValueUnits,
              AlternatingEndpointTower.lastPair, last0, last1] using hs
          have ht := endpoint_discriminant_to_square_after_mul_discriminant
            (laws := laws) (b.valueUnit last0 * b.valueUnit last1) hs'
          have ht' : IsSquare (-(C.bong.valueUnit last0 *
                C.bong.valueUnit last1)) := by
            rw [hcLastProduct]
            exact ht
          simpa [BONG.GoodBONG.prefixValueUnits,
            AlternatingEndpointTower.lastPair, last0, last1] using ht'
        exact ⟨C.bong, hcProfile, hcSource, hcGlobal, hcSuffix,
          hflipSquare, hflipDiscriminant⟩
      have hsourceLast :=
        AlternatingEndpointTower.pairClasses_lastPair source hsource
      have htargetLast :=
        AlternatingEndpointTower.pairClasses_lastPair target htarget
      rcases hsourceLast with hsSquare | hsDiscriminant
      · rcases htargetLast with htSquare | htDiscriminant
        · apply hfinish b hsource hsourceProfile
          · exact pairProduct_isSquare_of_both_square _ _ _ _
              hsSquare htSquare
          · exact hdet
          · intro j _
            rfl
        · by_cases hpairs : pairs = 0
          · subst pairs
            have hpairGlobal : IsSquare
                ((AlternatingEndpointTower.lastPair source 0 *
                    AlternatingEndpointTower.lastPair source 1) *
                  (AlternatingEndpointTower.lastPair target 0 *
                    AlternatingEndpointTower.lastPair target 1)) := by
              simpa [source, BONG.GoodBONG.diagonalUnitDeterminant,
                AlternatingEndpointTower.lastPair] using hdet
            exact False.elim
              (false_of_square_discriminant_and_pairProduct_square
                _ _ _ _ hsSquare htDiscriminant hpairGlobal)
          · rcases hboundaryChange hpairs with
              ⟨c, hcProfile, hcSource, hcGlobal, hcSuffix,
                hflipSquare, _⟩
            have hcLastClass := hflipSquare hsSquare
            have hcLast := pairProduct_isSquare_of_both_discriminant
              _ _ _ _ hcLastClass htDiscriminant
            exact hfinish c hcSource hcProfile hcLast hcGlobal hcSuffix
      · rcases htargetLast with htSquare | htDiscriminant
        · by_cases hpairs : pairs = 0
          · subst pairs
            have hpairGlobal : IsSquare
                ((AlternatingEndpointTower.lastPair source 0 *
                    AlternatingEndpointTower.lastPair source 1) *
                  (AlternatingEndpointTower.lastPair target 0 *
                    AlternatingEndpointTower.lastPair target 1)) := by
              simpa [source, BONG.GoodBONG.diagonalUnitDeterminant,
                AlternatingEndpointTower.lastPair] using hdet
            exact False.elim
              (false_of_discriminant_square_and_pairProduct_square
                _ _ _ _ hsDiscriminant htSquare hpairGlobal)
          · rcases hboundaryChange hpairs with
              ⟨c, hcProfile, hcSource, hcGlobal, hcSuffix,
                _, hflipDiscriminant⟩
            have hcLastClass := hflipDiscriminant hsDiscriminant
            have hcLast := pairProduct_isSquare_of_both_square
              _ _ _ _ hcLastClass htSquare
            exact hfinish c hcSource hcProfile hcLast hcGlobal hcSuffix
        · apply hfinish b hsource hsourceProfile
          · exact pairProduct_isSquare_of_both_discriminant _ _ _ _
              hsDiscriminant htDiscriminant
          · exact hdet
          · intro j _
            rfl

/-- Source-faithful integral normalization for the alternating towers in
Beli (2019), Lemmas 7.17--7.18.  The proof first aligns the two endpoint-class
sequences by boundary `Delta` changes and then performs exact binary segment
replacements. -/
theorem exists_normalizedRigidEndpointPrefix
    [DyadicUnramifiedNormLaws K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    {n pairs : Nat}
    (b : BONG.GoodBONG q L (n + 1))
    (hbound : 2 * pairs ≤ n + 1)
    (target : Fin (2 * pairs) → Kˣ) (R : Int)
    (hsource : AlternatingEndpointPairClasses
      (b.prefixValueUnits (2 * pairs) hbound))
    (htarget : AlternatingEndpointPairClasses target)
    (hsourceProfile : AlternatingEndpointOrderProfile
      (b.prefixValueUnits (2 * pairs) hbound) R)
    (htargetProfile : AlternatingEndpointOrderProfile target R)
    (hdet : IsSquare
      (BONG.GoodBONG.diagonalUnitDeterminant
          (b.prefixValueUnits (2 * pairs) hbound) *
        BONG.GoodBONG.diagonalUnitDeterminant target)) :
    ∃ c : BONG.GoodBONG q L (n + 1),
      (∀ i : Fin (2 * pairs),
        c.valueUnit ⟨i.val, i.isLt.trans_le hbound⟩ = target i) ∧
      (∀ j : Fin (n + 1), 2 * pairs ≤ j.val →
        c.valueUnit j = b.valueUnit j) := by
  rcases exists_pairwiseAlignedRigidEndpointPrefix b hbound target R
      hsource htarget hsourceProfile htargetProfile hdet with
    ⟨d, hdProfile, hdPairs, hdSuffix⟩
  rcases exists_normalizedRigidEndpointPrefix_of_pairwiseDeterminants
      d hbound target R hdProfile htargetProfile hdPairs with
    ⟨c, hcPrefix, hcSuffix⟩
  refine ⟨c, hcPrefix, ?_⟩
  intro j hj
  exact (hcSuffix j hj).trans (hdSuffix j hj)

/-- The rigid normalization law is a theorem once the two genuine Beli 2003
local inputs are available. -/
instance rigidEndpointTowerNormalizationLaws
    [DyadicUnramifiedNormLaws K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K] :
    DyadicAlternatingEndpointTowerNormalizationLaws.{u, v} K where
  normalizeSplitPrefix b hbound target hsource htarget R htargetProfile
      horders hdet := by
    have hsourceProfile : AlternatingEndpointOrderProfile
        (b.prefixValueUnits _ hbound) R := by
      intro t
      have ht := htargetProfile t
      constructor
      · calc
          ordUnit K ((b.prefixValueUnits _ hbound)
              ⟨2 * t.val, by omega⟩) =
              ordUnit K (target ⟨2 * t.val, by omega⟩) :=
            (horders ⟨2 * t.val, by omega⟩).symm
          _ = R := ht.1
      · calc
          ordUnit K ((b.prefixValueUnits _ hbound)
              ⟨2 * t.val + 1, by omega⟩) =
              ordUnit K (target ⟨2 * t.val + 1, by omega⟩) :=
            (horders ⟨2 * t.val + 1, by omega⟩).symm
          _ = R - 2 * (ramificationIndex K : Int) := ht.2
    exact exists_normalizedRigidEndpointPrefix b hbound target R
      hsource htarget hsourceProfile htargetProfile hdet

end AlternatingEndpointNormalization

end Bong
