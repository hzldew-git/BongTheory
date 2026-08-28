/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma96ProjectionModel
import Bong.Bong.Beli2019Lemma96TailDefect
import Bong.Bong.Beli2019Lemma92Propagation
import Bong.Bong.Beli2019DominationOrderBound
import Bong.Bong.AlphaValueExt
import Bong.Bong.DiagonalRepresentationDeterminant
import Bong.Bong.Beli2019Lemma93TailEquality
import Bong.Bong.Beli2019Lemma93CoreTransport
import Bong.Bong.Beli2019Lemma93TailCentral
import Bong.Bong.Beli2019Lemma812
import Bong.Bong.Beli2019Lemma79TypeICaseOnePrefixDefect

/-!
# Beli (2019), Lemma 9.6: projected-tail comparison arithmetic

This file formalizes lines 9629--9697 of the revised-v2 proof.  The first
lemma isolates the argument used there twice: if the first alpha of a good
BONG attains its half-gap candidate, deleting the first coefficient does not
change any later alpha.  The proof uses P1, goodness, and Remark 1.1 exactly
as in Beli's displayed calculation.
-/

namespace Bong

open Dyadic

universe u v w x

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type x} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {P : Lattice K U}
  {n N : Nat}

set_option maxHeartbeats 800000 in
-- The nested alpha-minimum expansion requires additional simplification time.
/-- If the first alpha attains its half-gap candidate, then deleting the
head preserves every later alpha.  This is the abstract form of the two
calculations in lines 9635--9652 of Lemma 9.6. -/
theorem alphaValue_shift_eq_tail_of_head_attainsHalfGap
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2))
    (hfirst : b.AttainsHalfGap (0 : Fin (n + 1)))
    (i : Fin n) :
    b.alphaValue i.succ = b.tail.alphaValue i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
    let z₀ : Fin (m + 3) := ⟨0, by omega⟩
    let z₁ : Fin (m + 3) := ⟨1, by omega⟩
    let z₂ : Fin (m + 3) := ⟨2, by omega⟩
    have hendpoint := b.tail.alphaRightEndpoint_antitone (Fin.zero_le i)
    unfold alphaRightEndpoint at hendpoint
    simp only [b.order_goodTail] at hendpoint
    have htailQ :
        b.tail.alphaValue i ≤
          ((b.order i.succ.succ -
              b.order (0 : Fin (m + 1)).succ.succ : Int) : ℚ) +
            b.tail.alphaValue (0 : Fin (m + 1)) := by
      push_cast at hendpoint ⊢
      linarith
    have hgoodRaw := b.good z₀ (by
      dsimp only [z₀]
      omega)
    have hgood : b.order z₀ ≤ b.order z₂ := by
      let z₂' : Fin (m + 3) := ⟨z₀.val + 2, by
        dsimp only [z₀]
        omega⟩
      have hgoodRaw' : b.toBONG.order z₀ ≤ b.toBONG.order z₂' := by
        exact hgoodRaw
      have hz₂ : z₂' = z₂ := by
        apply Fin.ext
        dsimp only [z₂', z₀, z₂]
      change b.toBONG.order z₀ ≤ b.toBONG.order z₂
      exact hgoodRaw'.trans_eq (congrArg (fun j ↦ b.toBONG.order j) hz₂)
    have hgoodQ :
        (b.order z₀ : ℚ) ≤ (b.order z₂ : ℚ) := by
      exact_mod_cast hgood
    have htailHalf :=
      b.tail.alphaValue_le_halfGapValue (0 : Fin (m + 1))
    have hbaseQ :
        b.tail.alphaValue (0 : Fin (m + 1)) ≤
          ((b.order z₂ - b.order z₀ : Int) : ℚ) +
            (((b.order z₀ - b.order z₁ : Int) : ℚ) +
              b.alphaValue (0 : Fin (m + 2))) := by
      unfold AttainsHalfGap halfGapValue orderGap at hfirst
      unfold halfGapValue orderGap at htailHalf
      simp only [b.order_goodTail] at htailHalf
      change b.alphaValue (0 : Fin (m + 2)) =
        ((b.order z₁ - b.order z₀ : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) at hfirst
      change b.tail.alphaValue (0 : Fin (m + 1)) ≤
        ((b.order z₂ - b.order z₁ : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) at htailHalf
      push_cast at hfirst htailHalf ⊢
      linarith
    have hadjacent :=
      b.order_sub_add_alpha_le_adjacentDefect (0 : Fin (m + 2))
    have hbaseTop :
        (b.tail.alphaValue (0 : Fin (m + 1)) : WithTop ℚ) ≤
          ((((b.order z₂ - b.order z₀ : Int) : ℚ) : WithTop ℚ) +
            b.adjacentDefect (0 : Fin (m + 2))) := by
      calc
        (b.tail.alphaValue (0 : Fin (m + 1)) : WithTop ℚ) ≤
            (((b.order z₂ - b.order z₀ : Int) : ℚ) : WithTop ℚ) +
              (((b.order z₀ - b.order z₁ : Int) : ℚ) +
                b.alphaValue (0 : Fin (m + 2)) : ℚ) := by
          exact_mod_cast hbaseQ
        _ ≤ ((((b.order z₂ - b.order z₀ : Int) : ℚ) : WithTop ℚ) +
              b.adjacentDefect (0 : Fin (m + 2))) := by
          have hindex₀ : (0 : Fin (m + 2)).castSucc = z₀ := by
            apply Fin.ext
            rfl
          have hindex₁ : (0 : Fin (m + 2)).succ = z₁ := by
            apply Fin.ext
            rfl
          rw [hindex₀, hindex₁] at hadjacent
          gcongr
    have htailTop :
        (b.tail.alphaValue i : WithTop ℚ) ≤
          ((((b.order i.succ.succ -
              b.order (0 : Fin (m + 1)).succ.succ : Int) : ℚ) :
                WithTop ℚ) +
            (b.tail.alphaValue (0 : Fin (m + 1)) : WithTop ℚ)) := by
      exact_mod_cast htailQ
    have hindex₂ : (0 : Fin (m + 1)).succ.succ = z₂ := by
      apply Fin.ext
      rfl
    have horder₂ := congrArg (fun j ↦ b.order j) hindex₂
    rw [horder₂] at htailTop
    have hfirstBound : b.tail.alpha i ≤
        b.leftDefectCandidate i.succ (0 : Fin (m + 2)) := by
      rw [← b.tail.coe_alphaValue]
      calc
        (b.tail.alphaValue i : WithTop ℚ) ≤
            ((((b.order i.succ.succ -
                b.order (0 : Fin (m + 1)).succ.succ : Int) : ℚ) :
                  WithTop ℚ) +
              (b.tail.alphaValue (0 : Fin (m + 1)) : WithTop ℚ)) :=
          htailTop
        _ ≤ ((((b.order i.succ.succ -
                b.order (0 : Fin (m + 1)).succ.succ : Int) : ℚ) :
                  WithTop ℚ) +
              (((b.order (0 : Fin (m + 1)).succ.succ -
                  b.order z₀ : Int) : ℚ) : WithTop ℚ)) +
              b.adjacentDefect (0 : Fin (m + 2)) := by
          rw [horder₂]
          simpa only [add_comm, add_left_comm, add_assoc] using
            (add_le_add_left hbaseTop
              ((((b.order i.succ.succ - b.order z₂ : Int) : ℚ) :
                WithTop ℚ)))
        _ = b.leftDefectCandidate i.succ (0 : Fin (m + 2)) := by
          unfold leftDefectCandidate
          have hindex₀ : (0 : Fin (m + 2)).castSucc = z₀ := by
            apply Fin.ext
            rfl
          rw [hindex₀]
          congr 1
          rw [← WithTop.coe_add]
          congr 1
          push_cast
          ring
    apply WithTop.coe_injective
    rw [b.coe_alphaValue, b.tail.coe_alphaValue]
    exact le_antisymm (b.alpha_shift_le_tail i)
      (b.tailAlpha_le_shift_of_firstLeftDefectBound i hfirstBound)

/-- Two successive half-gap cuts identify a twice-shifted alpha with the
corresponding alpha of the twice-deleted suffix. -/
theorem alphaValue_shiftTwo_eq_tailTail_of_head_attainsHalfGap
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 3))
    (hfirst : b.AttainsHalfGap (0 : Fin (n + 2)))
    (hsecond : b.tail.AttainsHalfGap (0 : Fin (n + 1)))
    (i : Fin n) :
    b.alphaValue i.succ.succ = b.tail.tail.alphaValue i := by
  calc
    b.alphaValue i.succ.succ = b.tail.alphaValue i.succ :=
      b.alphaValue_shift_eq_tail_of_head_attainsHalfGap hfirst i.succ
    _ = b.tail.tail.alphaValue i :=
      b.tail.alphaValue_shift_eq_tail_of_head_attainsHalfGap hsecond i

/-- Three successive half-gap cuts identify a three-times-shifted alpha
with the corresponding alpha of the common suffix used in Lemma 9.6. -/
theorem alphaValue_shiftThree_eq_tailTailTail_of_head_attainsHalfGap
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 4))
    (hfirst : b.AttainsHalfGap (0 : Fin (n + 3)))
    (hsecond : b.tail.AttainsHalfGap (0 : Fin (n + 2)))
    (hthird : b.tail.tail.AttainsHalfGap (0 : Fin (n + 1)))
    (i : Fin n) :
    b.alphaValue i.succ.succ.succ =
      b.tail.tail.tail.alphaValue i := by
  calc
    b.alphaValue i.succ.succ.succ =
        b.tail.alphaValue i.succ.succ :=
      b.alphaValue_shift_eq_tail_of_head_attainsHalfGap hfirst i.succ.succ
    _ = b.tail.tail.tail.alphaValue i :=
      b.tail.alphaValue_shiftTwo_eq_tailTail_of_head_attainsHalfGap
        hsecond hthird i

/-- P2's zero case is exactly the half-gap case at order gap `-2e`. -/
theorem attainsHalfGap_of_orderGap_eq_neg_twoE
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hgap : b.orderGap i = -(2 * (ramificationIndex K : Int))) :
    b.AttainsHalfGap i := by
  unfold AttainsHalfGap
  rw [(b.alpha_p2 i).2.mpr hgap]
  unfold halfGapValue
  rw [hgap]
  push_cast
  ring

/-- P4 supplies a half-gap cut at every gap at least `2e`. -/
theorem attainsHalfGap_of_twoE_le_orderGap
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hgap : 2 * (ramificationIndex K : Int) ≤ b.orderGap i) :
    b.AttainsHalfGap i :=
  b.alpha_p4 i hgap

/-- Finite half-gap values shift literally under deletion of the head. -/
@[simp]
theorem halfGapValue_goodTail
    (b : GoodBONG q L (n + 2)) (i : Fin n) :
    b.tail.halfGapValue i = b.halfGapValue i.succ := by
  apply WithTop.coe_injective
  rw [b.tail.coe_halfGapValue, b.coe_halfGapValue,
    b.halfGapCandidate_tail]

end BONG.GoodBONG

end Bong

namespace Bong

open Dyadic

universe u v w x

namespace BONG.GoodBONG.Beli2019Lemma96PrefixTransport

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type x} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {P : Lattice K U}
  {N : Nat}
  {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
  {c : GoodBONG s P (N + 3)}

/-- Equal-rank prefix representation in Lemma 9.6 says that the original
prefix product differs from the source head times the projected prefix
product by an explicit square. -/
theorem exists_prefixProduct_eq_head_mul_square
    (T : Beli2019Lemma96PrefixTransport a b c)
    (tailLength : Nat) (hkTwo : 2 ≤ tailLength)
    (hk : tailLength ≤ N + 3) :
    ∃ p : Kˣ, a.prefixProduct (tailLength + 1) =
      (b.valueUnit 0 * c.prefixProduct tailLength) * p ^ 2 := by
  rcases DiagonalRepresents.exists_prod_eq_mul_square_of_sameRank
      (T.targetPrefix tailLength hkTwo hk) with ⟨p, hp⟩
  have htarget :
      (∏ i, Fin.cons (b.value 0)
          (c.prefixValues tailLength hk) i) =
        b.value 0 * (c.prefixProduct tailLength : K) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ,
      c.prod_prefixValues_eq_coe_prefixProduct tailLength hk]
  rw [a.prod_prefixValues_eq_coe_prefixProduct (tailLength + 1)
      (by omega), htarget] at hp
  refine ⟨p, ?_⟩
  apply Units.ext
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val,
    GoodBONG.coe_valueUnit] using hp

/-- The common source head occurs twice in the shifted comparison product.
After removing its square, the raw quadratic defect is exactly the raw
defect of the projected pair. -/
theorem defectOrder_shiftedPrefixes_eq_projected
    (T : Beli2019Lemma96PrefixTransport a b c)
    (epsilon : Kˣ) (targetLength sourceLength : Nat)
    (htTwo : 2 ≤ targetLength) (ht : targetLength ≤ N + 3)
    (hs : sourceLength ≤ N + 3) :
    defectOrder (K := K)
        (epsilon * a.prefixProduct (targetLength + 1) *
          b.prefixProduct (sourceLength + 1)) =
      defectOrder (K := K)
        (epsilon * c.prefixProduct targetLength *
          b.tail.prefixProduct sourceLength) := by
  rcases T.exists_prefixProduct_eq_head_mul_square
      targetLength htTwo ht with ⟨p, hp⟩
  rw [hp, b.prefixProduct_succ_eq_head_mul_tail sourceLength hs]
  have hfactor :
      epsilon *
          ((b.valueUnit 0 * c.prefixProduct targetLength) * p ^ 2) *
          (b.valueUnit 0 * b.tail.prefixProduct sourceLength) =
        (epsilon * c.prefixProduct targetLength *
            b.tail.prefixProduct sourceLength) *
          (b.valueUnit 0 * p) ^ 2 := by
    simp only [pow_two]
    ac_rfl
  rw [hfactor, defectOrder_mul_square]

end BONG.GoodBONG.Beli2019Lemma96PrefixTransport

namespace BONG.GoodBONG.Beli2019Lemma96MatchedNormalFormData

private theorem representationIndex_eq_of_val_eq_lemma96
    {largeRank smallRank : Nat}
    (i j : RepresentationIndex largeRank smallRank)
    (h : i.val = j.val) : i = j := by
  cases i
  cases j
  simp_all

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {N : Nat}
  [laws : DyadicDiscriminantClassLaws K]
  [targetLaws : Beli2006AlphaLaws.{u, v} K]
  [Beli2009AlphaParityLaws.{u, v} K]
  {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}

set_option maxHeartbeats 800000 in
-- Three successive dependent tail transports enlarge the elaborated term.
/-- The projected-tail alpha at every unchanged boundary is exactly the
corresponding original alpha.  In the paper this is
`α_i^* = α_i` for `i ≥ 4` (lines 9635--9652). -/
theorem projectedTailGoodBONG_alphaValue_later
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (i : Fin (N + 2)) (hi : 2 ≤ i.val) :
    (D.projectedTailGoodBONG S houter hfourth).alphaValue i =
      a.alphaValue i.succ := by
  let c := D.projectedTailGoodBONG S houter hfourth
  let O := D.projectedTail_orderProfile S houter hfirstGap hfourth
  have hcGap₀ : c.orderGap (0 : Fin (N + 2)) =
      -(2 * (ramificationIndex K : Int)) := by
    unfold orderGap
    change c.order (1 : Fin (N + 3)) - c.order (0 : Fin (N + 3)) = _
    rw [O.secondOrder, O.firstOrder, ← houter]
    omega
  have hcFirst : c.AttainsHalfGap (0 : Fin (N + 2)) :=
    c.attainsHalfGap_of_orderGap_eq_neg_twoE _ hcGap₀
  have hcTailGap :
      2 * (ramificationIndex K : Int) ≤
        c.tail.orderGap (0 : Fin (N + 1)) := by
    unfold orderGap
    simp only [c.order_goodTail]
    let c₁ : Fin (N + 3) := ⟨1, by omega⟩
    let c₂ : Fin (N + 3) := ⟨2, by omega⟩
    let a₀ : Fin (N + 4) := ⟨0, by omega⟩
    let a₂ : Fin (N + 4) := ⟨2, by omega⟩
    let a₃ : Fin (N + 4) := ⟨3, by omega⟩
    have htwo : c.order c₂ = a.order a₃ := by
      have h := O.laterOrders c₂ (by
        dsimp only [c₂]
        omega)
      convert h using 1
      apply congrArg (fun j ↦ a.order j)
      apply Fin.ext
      rfl
    have hone : c.order c₁ = a.order a₂ - 1 := by
      have hc₁ : c₁ = (1 : Fin (N + 3)) := by
        apply Fin.ext
        rfl
      have ha₂ : (2 : Fin (N + 4)) = a₂ := by
        apply Fin.ext
        rfl
      calc
        c.order c₁ = c.order (1 : Fin (N + 3)) :=
          congrArg (fun j ↦ c.order j) hc₁
        _ = a.order (2 : Fin (N + 4)) - 1 := O.secondOrder
        _ = a.order a₂ - 1 :=
          congrArg (fun z : Int ↦ z - 1)
            (congrArg (fun j ↦ a.order j) ha₂)
    have houter' : a.order a₀ = a.order a₂ := by
      exact houter
    have hfourth' : a.order a₀ + 2 * (ramificationIndex K : Int) ≤
        a.order a₃ := by
      exact hfourth
    change 2 * (ramificationIndex K : Int) ≤
      c.order c₂ - c.order c₁
    rw [htwo, hone]
    omega
  have hcSecond : c.tail.AttainsHalfGap (0 : Fin (N + 1)) :=
    c.tail.attainsHalfGap_of_twoE_le_orderGap _ hcTailGap
  have haFirstTwo := a.lemma96_firstTwoAttainHalfGap houter hfirstGap
  have haDeleteFirst : ∀ j : Fin (N + 2),
      a.alphaValue j.succ = a.tail.alphaValue j :=
    fun j ↦ a.alphaValue_shift_eq_tail_of_head_attainsHalfGap
      haFirstTwo.1 j
  have haSecond : a.tail.AttainsHalfGap (0 : Fin (N + 2)) := by
    unfold AttainsHalfGap
    calc
      a.tail.alphaValue (0 : Fin (N + 2)) =
          a.alphaValue (1 : Fin (N + 3)) :=
        (haDeleteFirst (0 : Fin (N + 2))).symm
      _ = a.halfGapValue (1 : Fin (N + 3)) := haFirstTwo.2
      _ = a.tail.halfGapValue (0 : Fin (N + 2)) :=
        (a.halfGapValue_goodTail (0 : Fin (N + 2))).symm
  have haGap₂ :
      2 * (ramificationIndex K : Int) ≤
        a.orderGap (2 : Fin (N + 3)) := by
    unfold orderGap
    change 2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)) - a.order (2 : Fin (N + 4))
    omega
  have haThirdGlobal : a.AttainsHalfGap (2 : Fin (N + 3)) :=
    a.attainsHalfGap_of_twoE_le_orderGap _ haGap₂
  have haDeleteSecond : ∀ j : Fin (N + 1),
      a.tail.alphaValue j.succ = a.tail.tail.alphaValue j :=
    fun j ↦ a.tail.alphaValue_shift_eq_tail_of_head_attainsHalfGap
      haSecond j
  have haThird : a.tail.tail.AttainsHalfGap (0 : Fin (N + 1)) := by
    unfold AttainsHalfGap
    calc
      a.tail.tail.alphaValue (0 : Fin (N + 1)) =
          a.tail.alphaValue (1 : Fin (N + 2)) :=
        (haDeleteSecond (0 : Fin (N + 1))).symm
      _ = a.alphaValue (2 : Fin (N + 3)) :=
        (haDeleteFirst (1 : Fin (N + 2))).symm
      _ = a.halfGapValue (2 : Fin (N + 3)) := haThirdGlobal
      _ = a.tail.halfGapValue (1 : Fin (N + 2)) :=
        (a.halfGapValue_goodTail (1 : Fin (N + 2))).symm
      _ = a.tail.tail.halfGapValue (0 : Fin (N + 1)) :=
        (a.tail.halfGapValue_goodTail (0 : Fin (N + 1))).symm
  let k : Fin N := ⟨i.val - 2, by omega⟩
  have hiIndex : i = k.succ.succ := by
    apply Fin.ext
    dsimp only [k]
    simp only [Fin.val_succ]
    omega
  have hcommonValues : ∀ j : Fin (N + 1),
      c.tail.tail.valueUnit j = a.tail.tail.tail.valueUnit j := by
    intro j
    rw [c.tail.valueUnit_goodTail j, c.valueUnit_goodTail j.succ,
      a.tail.tail.valueUnit_goodTail j,
      a.tail.valueUnit_goodTail j.succ,
      a.valueUnit_goodTail j.succ.succ]
    apply Units.ext
    simpa only [GoodBONG.coe_valueUnit] using
      D.projectedTailGoodBONG_value_later S houter hfourth
        j.succ.succ (by simp)
  have hcommonAlpha : c.tail.tail.alphaValue k =
      a.tail.tail.tail.alphaValue k :=
    c.tail.tail.alphaValue_eq_of_valueUnits_eq
      a.tail.tail.tail hcommonValues k
  change c.alphaValue i = a.alphaValue i.succ
  rw [hiIndex]
  calc
    c.alphaValue k.succ.succ = c.tail.tail.alphaValue k :=
      c.alphaValue_shiftTwo_eq_tailTail_of_head_attainsHalfGap
        hcFirst hcSecond k
    _ = a.tail.tail.tail.alphaValue k := hcommonAlpha
    _ = a.alphaValue k.succ.succ.succ :=
      (a.alphaValue_shiftThree_eq_tailTailTail_of_head_attainsHalfGap
        haFirstTwo.1 haSecond haThird k).symm

/-- At the one exceptional internal boundary, the projected alpha is larger
by exactly one half.  This is the displayed identity
`alpha_3^* = alpha_3 + 1/2` in lines 9653--9654. -/
theorem projectedTailGoodBONG_alphaValue_one_eq_original_two_add_half
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4))) :
    (D.projectedTailGoodBONG S houter hfourth).alphaValue
        (1 : Fin (N + 2)) =
      a.alphaValue (2 : Fin (N + 3)) + (1 / 2 : ℚ) := by
  let c := D.projectedTailGoodBONG S houter hfourth
  let O := D.projectedTail_orderProfile S houter hfirstGap hfourth
  have haGap : 2 * (ramificationIndex K : Int) ≤
      a.orderGap (2 : Fin (N + 3)) := by
    unfold orderGap
    change 2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)) - a.order (2 : Fin (N + 4))
    omega
  have hcGap : 2 * (ramificationIndex K : Int) ≤
      c.orderGap (1 : Fin (N + 2)) := by
    unfold orderGap
    change 2 * (ramificationIndex K : Int) ≤
      c.order (2 : Fin (N + 3)) - c.order (1 : Fin (N + 3))
    have hsuccTwo : (2 : Fin (N + 3)).succ =
        (3 : Fin (N + 4)) := by
      apply Fin.ext
      change 2 % (N + 3) + 1 = 3 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [O.laterOrders (2 : Fin (N + 3)) (by
        change 2 ≤ 2 % (N + 3)
        rw [Nat.mod_eq_of_lt (by omega)]),
      hsuccTwo, O.secondOrder]
    omega
  have haAttains :=
    a.attainsHalfGap_of_twoE_le_orderGap
      (2 : Fin (N + 3)) haGap
  have hcAttains :=
    c.attainsHalfGap_of_twoE_le_orderGap
      (1 : Fin (N + 2)) hcGap
  unfold AttainsHalfGap at haAttains hcAttains
  rw [hcAttains, haAttains]
  unfold halfGapValue orderGap
  change
    ((c.order (2 : Fin (N + 3)) - c.order (1 : Fin (N + 3)) : Int) : ℚ) /
          2 + (ramificationIndex K : ℚ) =
      ((a.order (3 : Fin (N + 4)) - a.order (2 : Fin (N + 4)) : Int) : ℚ) /
          2 + (ramificationIndex K : ℚ) + 1 / 2
  have hsuccTwo : (2 : Fin (N + 3)).succ =
      (3 : Fin (N + 4)) := by
    apply Fin.ext
    change 2 % (N + 3) + 1 = 3 % (N + 4)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [O.laterOrders (2 : Fin (N + 3)) (by
      change 2 ≤ 2 % (N + 3)
      rw [Nat.mod_eq_of_lt (by omega)]),
    hsuccTwo, O.secondOrder]
  push_cast
  ring

/-- Every shifted original prefix cap is no larger than the corresponding
projected prefix cap.  Equality holds after the exceptional boundary; at
that boundary the preceding half-unit identity gives the inequality. -/
theorem prefixAlphaCap_shift_le_projectedTail
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (i : Nat) (hiTwo : 2 ≤ i) (hi : i < N + 3) :
    a.prefixAlphaCap (i + 1) ≤
      (D.projectedTailGoodBONG S houter hfourth).prefixAlphaCap i := by
  let c := D.projectedTailGoodBONG S houter hfourth
  rw [a.prefixAlphaCap_of_internal (by omega) (by omega),
    c.prefixAlphaCap_of_internal (by omega) hi]
  by_cases hiEq : i = 2
  · subst i
    have hq : a.alphaValue (2 : Fin (N + 3)) ≤
        c.alphaValue (1 : Fin (N + 2)) := by
      rw [D.projectedTailGoodBONG_alphaValue_one_eq_original_two_add_half
        S houter hfirstGap hfourth]
      norm_num
    exact_mod_cast hq
  · let j : Fin (N + 2) := ⟨i - 1, by omega⟩
    have hjTwo : 2 ≤ j.val := by
      dsimp only [j]
      omega
    have halpha := D.projectedTailGoodBONG_alphaValue_later
      S houter hfirstGap hfourth j hjTwo
    have hsucc : j.succ = (⟨i, by omega⟩ : Fin (N + 3)) := by
      apply Fin.ext
      dsimp only [j]
      simp only [Fin.val_succ]
      omega
    rw [halpha, hsucc]
    have hcapIndex :
        (⟨i + 1 - 1, by omega⟩ : Fin (N + 3)) =
          (⟨i, by omega⟩ : Fin (N + 3)) := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    rw [hcapIndex]

/-- The capped comparison defect of the projected pair dominates the
corresponding shifted defect of the original pair.  The raw defects are
equal by the determinant square class; the two caps are handled by the
preceding target calculation and the source half-gap cut. -/
theorem truncatedPrefixDefect_shift_le_projectedTail
    (sourceLaws : Beli2006AlphaLaws.{u, w} K)
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (hsourceFirstGap :
      2 * (ramificationIndex K : Int) ≤
        b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4)))
    (epsilon : Kˣ) (i : Nat) (hiTwo : 2 ≤ i) (hi : i < N + 3) :
    a.truncatedPrefixDefect b epsilon (i + 1) (i + 1) ≤
      (D.projectedTailGoodBONG S houter hfourth).truncatedPrefixDefect
        b.tail epsilon i i := by
  let c := D.projectedTailGoodBONG S houter hfourth
  let T := D.projectedTail_prefixTransport S houter hfourth
  have hraw := T.defectOrder_shiftedPrefixes_eq_projected
    epsilon i i hiTwo (by omega) (by omega)
  have htargetCap : a.prefixAlphaCap (i + 1) ≤
      c.prefixAlphaCap i := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact D.prefixAlphaCap_shift_le_projectedTail S houter
      hfirstGap hfourth i hiTwo hi
  letI : Beli2006AlphaLaws.{u, w} K := sourceLaws
  have hbGap : 2 * (ramificationIndex K : Int) ≤
      b.orderGap (0 : Fin (N + 3)) := by
    unfold orderGap
    change 2 * (ramificationIndex K : Int) ≤
      b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4))
    exact hsourceFirstGap
  have hbFirst : b.AttainsHalfGap (0 : Fin (N + 3)) :=
    b.attainsHalfGap_of_twoE_le_orderGap _ hbGap
  have hbAlpha : ∀ j : Fin (N + 2),
      (b.alphaValue j.succ : WithTop ℚ) ≤
        (b.tail.alphaValue j : WithTop ℚ) := by
    intro j
    rw [b.alphaValue_shift_eq_tail_of_head_attainsHalfGap hbFirst j]
  unfold truncatedPrefixDefect
  apply min_le_min
  · exact hraw.le
  · apply min_le_min
    · exact htargetCap
    · exact b.prefixAlphaCap_shift_le_tail hbAlpha i (by omega) hi

/-- From the next boundary onward, the shifted original and projected
target prefix caps are exactly equal. -/
theorem prefixAlphaCap_shift_eq_projectedTail
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (i : Nat) (hiThree : 3 ≤ i) (hi : i ≤ N + 3) :
    a.prefixAlphaCap (i + 1) =
      (D.projectedTailGoodBONG S houter hfourth).prefixAlphaCap i := by
  let c := D.projectedTailGoodBONG S houter hfourth
  by_cases hin : i < N + 3
  · rw [a.prefixAlphaCap_of_internal (by omega) (by omega),
      c.prefixAlphaCap_of_internal (by omega) hin]
    let j : Fin (N + 2) := ⟨i - 1, by omega⟩
    have hjTwo : 2 ≤ j.val := by
      dsimp only [j]
      omega
    have halpha := D.projectedTailGoodBONG_alphaValue_later
      S houter hfirstGap hfourth j hjTwo
    have htarget : j.succ =
        (⟨i + 1 - 1, by omega⟩ : Fin (N + 3)) := by
      apply Fin.ext
      dsimp only [j]
      simp only [Fin.val_succ]
      omega
    have hprojected : j =
        (⟨i - 1, by omega⟩ : Fin (N + 2)) := rfl
    rw [← htarget, ← hprojected, ← halpha]
  · have hiLast : i = N + 3 := by omega
    subst i
    simp

/-- Away from the exceptional zero-length source prefix, all three parts
of the capped defect (raw defect, target cap, source cap) agree exactly. -/
theorem truncatedPrefixDefect_shift_eq_projectedTail
    (sourceLaws : Beli2006AlphaLaws.{u, w} K)
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (hsourceFirstGap :
      2 * (ramificationIndex K : Int) ≤
        b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4)))
    (epsilon : Kˣ) (targetLength sourceLength : Nat)
    (htThree : 3 ≤ targetLength) (ht : targetLength ≤ N + 3)
    (hsPos : 0 < sourceLength) (hs : sourceLength ≤ N + 3) :
    a.truncatedPrefixDefect b epsilon
        (targetLength + 1) (sourceLength + 1) =
      (D.projectedTailGoodBONG S houter hfourth).truncatedPrefixDefect
        b.tail epsilon targetLength sourceLength := by
  let c := D.projectedTailGoodBONG S houter hfourth
  let T := D.projectedTail_prefixTransport S houter hfourth
  have hraw := T.defectOrder_shiftedPrefixes_eq_projected epsilon
    targetLength sourceLength (by omega) ht hs
  have htargetCap : a.prefixAlphaCap (targetLength + 1) =
      c.prefixAlphaCap targetLength := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact D.prefixAlphaCap_shift_eq_projectedTail S houter
      hfirstGap hfourth targetLength htThree ht
  letI : Beli2006AlphaLaws.{u, w} K := sourceLaws
  have hbGap : 2 * (ramificationIndex K : Int) ≤
      b.orderGap (0 : Fin (N + 3)) := by
    unfold orderGap
    change 2 * (ramificationIndex K : Int) ≤
      b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4))
    exact hsourceFirstGap
  have hbFirst : b.AttainsHalfGap (0 : Fin (N + 3)) :=
    b.attainsHalfGap_of_twoE_le_orderGap _ hbGap
  have hbAlpha : ∀ j : Fin (N + 2),
      b.alphaValue j.succ = b.tail.alphaValue j :=
    fun j ↦ b.alphaValue_shift_eq_tail_of_head_attainsHalfGap hbFirst j
  have hsourceCap := b.prefixAlphaCap_shift_eq_tail_of_alphaValue_eq
    hbAlpha sourceLength hsPos hs
  unfold truncatedPrefixDefect
  rw [hraw, htargetCap, hsourceCap]

/-- The discriminant branch retained in `D` has raw defect exactly `2e`. -/
theorem twistedRaw_defectOrder_eq_twoE
    (D : Beli2019Lemma96MatchedNormalFormData a b) :
    defectOrder (K := K)
        ((-1) * a.prefixProduct 3 * b.prefixProduct 1) =
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
  let x : Kˣ := (-1) * a.prefixProduct 3 * b.prefixProduct 1
  have hdeltaSquare : IsSquare
      ((laws.discriminantUnit : Kˣ) ^ 2) :=
    ⟨laws.discriminantUnit, by simp only [pow_two]⟩
  have hmul : IsSquare (x * laws.discriminantUnit) := by
    have h := D.twistedRawSquare.mul hdeltaSquare
    have hreorder :
        (x / laws.discriminantUnit) * laws.discriminantUnit ^ 2 =
          x * laws.discriminantUnit := by
      dsimp only [x]
      simp only [div_eq_mul_inv, pow_two]
      group
    rw [hreorder] at h
    exact h
  exact defectOrder_eq_twoE_of_mul_discriminant_isSquare x hmul

/-- The exceptional core used at the left endpoint is `2e` on both sides:
`d[-a_(1,3)b_1] = d[-a'_(2,3)] = 2e`. -/
theorem exceptionalPreviousCore_eq
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (hdefect : a.Beli2019Lemma96DefectBound b) :
    a.truncatedPrefixDefect b (-1) 3 1 =
      (D.projectedTailGoodBONG S houter hfourth).truncatedPrefixDefect
        b.tail (-1) 2 0 := by
  let c := D.projectedTailGoodBONG S houter hfourth
  let T := D.projectedTail_prefixTransport S houter hfourth
  let twoE : WithTop ℚ :=
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)
  have hrawOriginal : defectOrder (K := K)
      ((-1) * a.prefixProduct 3 * b.prefixProduct 1) = twoE := by
    simpa only [twoE] using D.twistedRaw_defectOrder_eq_twoE
  have horiginal : a.truncatedPrefixDefect b (-1) 3 1 = twoE := by
    apply le_antisymm
    · exact (a.truncatedPrefixDefect_le_defect b (-1) 3 1).trans_eq
        hrawOriginal
    · exact hdefect
  have hrawProjected : defectOrder (K := K)
      ((-1) * c.prefixProduct 2 * b.tail.prefixProduct 0) = twoE := by
    have hraw := T.defectOrder_shiftedPrefixes_eq_projected
      (-1) 2 0 (by omega) (by omega) (by omega)
    exact hraw.symm.trans hrawOriginal
  have htargetLower : twoE ≤ c.prefixAlphaCap 2 := by
    rw [c.prefixAlphaCap_of_internal (by omega) (by omega)]
    have haLower := a.lemma96_targetThirdAlpha_ge_twoE b
      (by omega) hdefect
    have hspecial :=
      D.projectedTailGoodBONG_alphaValue_one_eq_original_two_add_half
        S houter hfirstGap hfourth
    have haLower' : 2 * (ramificationIndex K : ℚ) ≤
        a.alphaValue (2 : Fin (N + 3)) := by
      convert haLower using 1
      congr 1
    have hq : 2 * (ramificationIndex K : ℚ) ≤
        a.alphaValue (2 : Fin (N + 3)) + 1 / 2 := by
      linarith
    change twoE ≤ (c.alphaValue (1 : Fin (N + 2)) : WithTop ℚ)
    rw [hspecial]
    dsimp only [twoE]
    exact_mod_cast hq
  have hprojected : c.truncatedPrefixDefect b.tail (-1) 2 0 = twoE := by
    unfold truncatedPrefixDefect
    rw [hrawProjected, b.tail.prefixAlphaCap_zero, min_top_right,
      min_eq_left htargetLower]
  exact horiginal.trans hprojected.symm

/-- Exact primary-core transport at every nonexceptional comparison
boundary (paper index at least three). -/
theorem primaryCore_eq_projectedTail
    (sourceLaws : Beli2006AlphaLaws.{u, w} K)
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (hsourceFirstGap :
      2 * (ramificationIndex K : Int) ≤
        b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4)))
    (i : RepresentationIndex (N + 3) (N + 3)) (hiTwo : 2 ≤ i.val) :
    a.truncatedPrefixDefect b (-1) (i.val + 2) i.val =
      (D.projectedTailGoodBONG S houter hfourth).truncatedPrefixDefect
        b.tail (-1) (i.val + 1) (i.val - 1) := by
  letI : Beli2006AlphaLaws.{u, v} K := targetLaws
  have h := D.truncatedPrefixDefect_shift_eq_projectedTail sourceLaws S
    houter hfirstGap hfourth hsourceFirstGap (-1)
      (i.val + 1) (i.val - 1) (by omega)
      (by have := i.lt_large; omega) (by omega)
      (by have := i.lt_large; omega)
  simpa only [show i.val - 1 + 1 = i.val by omega] using h

/-- The adjacent core to the left is exact as well.  At the first possible
index this is the special discriminant calculation; afterwards it is the
uniform prefix-cap identity. -/
theorem previousCore_eq_projectedTail
    (sourceLaws : Beli2006AlphaLaws.{u, w} K)
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (hsourceFirstGap :
      2 * (ramificationIndex K : Int) ≤
        b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4)))
    (hdefect : a.Beli2019Lemma96DefectBound b)
    (i : RepresentationIndex (N + 3) (N + 3)) (hiTwo : 2 ≤ i.val) :
    a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) =
      (D.projectedTailGoodBONG S houter hfourth).truncatedPrefixDefect
        b.tail (-1) i.val (i.val - 2) := by
  letI : Beli2006AlphaLaws.{u, v} K := targetLaws
  by_cases hiEq : i.val = 2
  · simpa only [hiEq, Nat.reduceAdd, Nat.reduceSub] using
      D.exceptionalPreviousCore_eq S houter hfirstGap hfourth hdefect
  · have h := D.truncatedPrefixDefect_shift_eq_projectedTail sourceLaws S
      houter hfirstGap hfourth hsourceFirstGap (-1)
        i.val (i.val - 2) (by omega)
        (by have := i.lt_large; omega) (by omega)
        (by have := i.lt_large; omega)
    simpa only [show i.val - 2 + 1 = i.val - 1 by omega] using h

/-- Exact transport of the adjacent core to the right. -/
theorem nextCore_eq_projectedTail
    (sourceLaws : Beli2006AlphaLaws.{u, w} K)
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (hsourceFirstGap :
      2 * (ramificationIndex K : Int) ≤
        b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4)))
    (i : RepresentationIndex (N + 3) (N + 3)) (hiTwo : 2 ≤ i.val)
    (hinterior : i.val + 1 < N + 3) :
    a.truncatedPrefixDefect b (-1) (i.val + 3) (i.val + 1) =
      (D.projectedTailGoodBONG S houter hfourth).truncatedPrefixDefect
        b.tail (-1) (i.val + 2) i.val := by
  letI : Beli2006AlphaLaws.{u, v} K := targetLaws
  have h := D.truncatedPrefixDefect_shift_eq_projectedTail sourceLaws S
    houter hfirstGap hfourth hsourceFirstGap (-1)
      (i.val + 2) i.val (by omega)
      (by omega) (by omega) (by have := i.lt_large; omega)
  simpa only using h

/-- From the third projected coefficient onward, the half-gap comparison
candidate is literally the corresponding candidate at the shifted original
boundary. -/
theorem representationHalfGap_projectedTail_eq_original
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (i : RepresentationIndex (N + 3) (N + 3)) (hiTwo : 2 ≤ i.val) :
    (D.projectedTailGoodBONG S houter hfourth).representationHalfGap
        b.tail i = a.representationHalfGap b i.tailShift := by
  let c := D.projectedTailGoodBONG S houter hfourth
  let O := D.projectedTail_orderProfile S houter hfirstGap hfourth
  have haIndex : (⟨i.val, i.lt_large⟩ : Fin (N + 3)).succ =
      (⟨i.tailShift.val, i.tailShift.lt_large⟩ : Fin (N + 4)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have hbIndex :
      (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (N + 3)).succ =
        (⟨i.tailShift.val - 1, by have := i.tailShift.le_small; omega⟩ :
          Fin (N + 4)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  unfold representationHalfGap
  rw [O.laterOrders ⟨i.val, i.lt_large⟩ hiTwo, b.order_goodTail]
  rw [haIndex, hbIndex]

/-- Exact transport of the primary Definition 4 candidate. -/
theorem representationPrimaryDefect_projectedTail_eq_original
    (sourceLaws : Beli2006AlphaLaws.{u, w} K)
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (hsourceFirstGap :
      2 * (ramificationIndex K : Int) ≤
        b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4)))
    (i : RepresentationIndex (N + 3) (N + 3)) (hiTwo : 2 ≤ i.val) :
    (D.projectedTailGoodBONG S houter hfourth).representationPrimaryDefect
        b.tail i = a.representationPrimaryDefect b i.tailShift := by
  letI : Beli2006AlphaLaws.{u, v} K := targetLaws
  let c := D.projectedTailGoodBONG S houter hfourth
  let O := D.projectedTail_orderProfile S houter hfirstGap hfourth
  have hcore := D.primaryCore_eq_projectedTail sourceLaws S houter
    hfirstGap hfourth hsourceFirstGap i hiTwo
  have haIndex : (⟨i.val, i.lt_large⟩ : Fin (N + 3)).succ =
      (⟨i.tailShift.val, i.tailShift.lt_large⟩ : Fin (N + 4)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have hbIndex :
      (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (N + 3)).succ =
        (⟨i.tailShift.val - 1, by have := i.tailShift.le_small; omega⟩ :
          Fin (N + 4)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  unfold representationPrimaryDefect
  rw [O.laterOrders ⟨i.val, i.lt_large⟩ hiTwo, b.order_goodTail]
  rw [haIndex, hbIndex, ← hcore]
  simp only [RepresentationIndex.tailShift_val,
    show i.val + 1 + 1 = i.val + 2 by omega,
    show i.val + 1 - 1 = i.val by omega]

/-- Exact transport of Lemma 2.7(i)'s previous-form secondary candidate. -/
theorem representationSecondaryPreviousDefect_projectedTail_eq_original
    (sourceLaws : Beli2006AlphaLaws.{u, w} K)
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (hsourceFirstGap :
      2 * (ramificationIndex K : Int) ≤
        b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4)))
    (hdefect : a.Beli2019Lemma96DefectBound b)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hi : 1 < i.val ∧ i.val + 1 < N + 3) :
    (D.projectedTailGoodBONG S houter hfourth).representationSecondaryPreviousDefect
        b.tail i hi =
      a.representationSecondaryPreviousDefect b i.tailShift
        ⟨by simp only [RepresentationIndex.tailShift_val]; omega,
         by simp only [RepresentationIndex.tailShift_val]; omega⟩ := by
  letI : Beli2006AlphaLaws.{u, v} K := targetLaws
  let c := D.projectedTailGoodBONG S houter hfourth
  let O := D.projectedTail_orderProfile S houter hfirstGap hfourth
  have hcore := D.previousCore_eq_projectedTail sourceLaws S houter
    hfirstGap hfourth hsourceFirstGap hdefect i (by omega)
  have haCurrent : (⟨i.val, i.lt_large⟩ : Fin (N + 3)).succ =
      (⟨i.tailShift.val, i.tailShift.lt_large⟩ : Fin (N + 4)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have haNext : (⟨i.val + 1, hi.2⟩ : Fin (N + 3)).succ =
      (⟨i.tailShift.val + 1, by
        simp only [RepresentationIndex.tailShift_val]; omega⟩ : Fin (N + 4)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have hbPrevious :
      (⟨i.val - 2, by have := i.le_small; omega⟩ : Fin (N + 3)).succ =
        (⟨i.tailShift.val - 2, by
          have := i.tailShift.le_small; omega⟩ : Fin (N + 4)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  have hbCurrent :
      (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (N + 3)).succ =
        (⟨i.tailShift.val - 1, by
          have := i.tailShift.le_small; omega⟩ : Fin (N + 4)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  unfold representationSecondaryPreviousDefect
  rw [O.laterOrders ⟨i.val, i.lt_large⟩
      (show 2 ≤ i.val from by omega),
    O.laterOrders ⟨i.val + 1, hi.2⟩
      (show 2 ≤ i.val + 1 from by omega),
    b.order_goodTail, b.order_goodTail,
    haCurrent, haNext, hbPrevious, hbCurrent, ← hcore]
  simp only [RepresentationIndex.tailShift_val,
    show i.val + 1 - 2 = i.val - 1 by omega]

/-- Exact transport of Lemma 2.7(ii)'s current-form secondary candidate. -/
theorem representationSecondaryCurrentDefect_projectedTail_eq_original
    (sourceLaws : Beli2006AlphaLaws.{u, w} K)
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (hsourceFirstGap :
      2 * (ramificationIndex K : Int) ≤
        b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4)))
    (i : RepresentationIndex (N + 3) (N + 3))
    (hi : 1 < i.val ∧ i.val + 1 < N + 3) :
    (D.projectedTailGoodBONG S houter hfourth).representationSecondaryCurrentDefect
        b.tail i hi =
      a.representationSecondaryCurrentDefect b i.tailShift
        ⟨by simp only [RepresentationIndex.tailShift_val]; omega,
         by simp only [RepresentationIndex.tailShift_val]; omega⟩ := by
  letI : Beli2006AlphaLaws.{u, v} K := targetLaws
  let c := D.projectedTailGoodBONG S houter hfourth
  let O := D.projectedTail_orderProfile S houter hfirstGap hfourth
  have hcore := D.nextCore_eq_projectedTail sourceLaws S houter
    hfirstGap hfourth hsourceFirstGap i (by omega) hi.2
  have haCurrent : (⟨i.val, i.lt_large⟩ : Fin (N + 3)).succ =
      (⟨i.tailShift.val, i.tailShift.lt_large⟩ : Fin (N + 4)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have haNext : (⟨i.val + 1, hi.2⟩ : Fin (N + 3)).succ =
      (⟨i.tailShift.val + 1, by
        simp only [RepresentationIndex.tailShift_val]; omega⟩ : Fin (N + 4)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have hbPrevious :
      (⟨i.val - 2, by have := i.le_small; omega⟩ : Fin (N + 3)).succ =
        (⟨i.tailShift.val - 2, by
          have := i.tailShift.le_small; omega⟩ : Fin (N + 4)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  have hbCurrent :
      (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (N + 3)).succ =
        (⟨i.tailShift.val - 1, by
          have := i.tailShift.le_small; omega⟩ : Fin (N + 4)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  unfold representationSecondaryCurrentDefect
  rw [O.laterOrders ⟨i.val, i.lt_large⟩
      (show 2 ≤ i.val from by omega),
    O.laterOrders ⟨i.val + 1, hi.2⟩
      (show 2 ≤ i.val + 1 from by omega),
    b.order_goodTail, b.order_goodTail,
    haCurrent, haNext, hbPrevious, hbCurrent, ← hcore]
  simp only [RepresentationIndex.tailShift_val]

set_option maxHeartbeats 1000000 in
-- The essential-boundary proof expands all primary and secondary candidates.
/-- At every noninitial essential boundary, the complete comparison invariant
for the projected pair is the shifted invariant of the original pair.  This
expands the sentence "as in Lemma 9.3" in lines 9668--9671 into the two
Lemma 2.7 normal forms and the endpoint form. -/
theorem projectedTail_representationAlpha_eq_original_of_essential
    (sourceLaws : Beli2006AlphaLaws.{u, w} K)
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (hsourceFirstGap :
      2 * (ramificationIndex K : Int) ≤
        b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4)))
    (hdefect : a.Beli2019Lemma96DefectBound b)
    (i : RepresentationIndex (N + 3) (N + 3)) (hiTwo : 2 ≤ i.val)
    (himportant :
      (D.projectedTailGoodBONG S houter hfourth).IsCurrentEssential b.tail i ∨
      (D.projectedTailGoodBONG S houter hfourth).IsNextEssential b.tail i) :
    (D.projectedTailGoodBONG S houter hfourth).representationAlpha b.tail i =
      a.representationAlpha b i.tailShift := by
  letI : Beli2006AlphaLaws.{u, v} K := targetLaws
  let c := D.projectedTailGoodBONG S houter hfourth
  let O := D.projectedTail_orderProfile S houter hfirstGap hfourth
  have hhalf := D.representationHalfGap_projectedTail_eq_original S
    houter hfirstGap hfourth i hiTwo
  have hprimary := D.representationPrimaryDefect_projectedTail_eq_original
    sourceLaws S houter hfirstGap hfourth hsourceFirstGap i hiTwo
  rw [c.representationAlpha_eq_min_halfGap_prime b.tail i,
    a.representationAlpha_eq_min_halfGap_prime b i.tailShift, hhalf]
  by_cases hinterior : i.val + 1 < N + 3
  · have hi : 1 < i.val ∧ i.val + 1 < N + 3 := ⟨by omega, hinterior⟩
    have hiOriginal :
        1 < i.tailShift.val ∧ i.tailShift.val + 1 < N + 4 := by
      simp only [RepresentationIndex.tailShift_val]
      omega
    rcases himportant with hcurrent | hnext
    · have hcrossProjected :=
        order_previous_lt_current_of_currentEssential
          c b.tail i hi.1 hi.2 hcurrent
      have hcrossOriginal :
          b.order ⟨i.tailShift.val - 2, by
            have := i.tailShift.le_small; omega⟩ ≤
            a.order ⟨i.tailShift.val, i.tailShift.lt_large⟩ := by
        have hcross := hcrossProjected.le
        rw [b.order_goodTail,
          O.laterOrders ⟨i.val, i.lt_large⟩
            (show 2 ≤ i.val from hiTwo)] at hcross
        convert hcross using 1 <;> congr 1 <;> apply Fin.ext <;>
          simp only [RepresentationIndex.tailShift_val, Fin.val_succ] <;> omega
      have hprevious :=
        D.representationSecondaryPreviousDefect_projectedTail_eq_original
          sourceLaws S houter hfirstGap hfourth hsourceFirstGap hdefect i hi
      rw [c.representationAlphaPrime_eq_min_primary_previous
          b.tail i hi hcrossProjected.le,
        a.representationAlphaPrime_eq_min_primary_previous
          b i.tailShift hiOriginal hcrossOriginal,
        hprimary, hprevious]
    · have hcurrent :=
        D.representationSecondaryCurrentDefect_projectedTail_eq_original
          sourceLaws S houter hfirstGap hfourth hsourceFirstGap i hi
      letI : Beli2006AlphaLaws.{u, w} K := sourceLaws
      have hcrossProjected :=
        order_current_lt_next_of_nextEssential
          c b.tail i hi.1 hi.2 hnext
      have hcrossOriginal :
          b.order ⟨i.tailShift.val - 1, by
            have := i.tailShift.le_small; omega⟩ ≤
            a.order ⟨i.tailShift.val + 1, hiOriginal.2⟩ := by
        have hcross := hcrossProjected.le
        rw [b.order_goodTail,
          O.laterOrders ⟨i.val + 1, hinterior⟩
            (show 2 ≤ i.val + 1 from by omega)] at hcross
        convert hcross using 1 <;> congr 1 <;> apply Fin.ext <;>
          simp only [RepresentationIndex.tailShift_val, Fin.val_succ] <;> omega
      rw [c.representationAlphaPrime_eq_min_primary_current
          b.tail i hi hcrossProjected.le,
        a.representationAlphaPrime_eq_min_primary_current
          b i.tailShift hiOriginal hcrossOriginal,
        hprimary, hcurrent]
  · have hnotProjected : ¬(1 < i.val ∧ i.val + 1 < N + 3) := by
      omega
    have hnotOriginal :
        ¬(1 < i.tailShift.val ∧ i.tailShift.val + 1 < N + 4) := by
      simp only [RepresentationIndex.tailShift_val]
      omega
    rw [c.representationAlphaPrime_eq_primary_of_not_interior
        b.tail i hnotProjected,
      a.representationAlphaPrime_eq_primary_of_not_interior
        b i.tailShift hnotOriginal, hprimary]

/-- The new first comparison alpha is strictly negative.  Its half-gap
candidate sees the projected second order `R_3 - 1` against the source
second order, which is at least `R_1 + 2e`. -/
theorem projectedTail_representationAlpha_first_lt_zero
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (hsourceFirstOrder :
      b.order (0 : Fin (N + 4)) = a.order (0 : Fin (N + 4)))
    (hsourceFirstGap :
      2 * (ramificationIndex K : Int) ≤
        b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4)))
    (i : RepresentationIndex (N + 3) (N + 3))
    (hi : i.val = 1) :
    (D.projectedTailGoodBONG S houter hfourth).representationAlpha
        b.tail i < 0 := by
  let c := D.projectedTailGoodBONG S houter hfourth
  let O := D.projectedTail_orderProfile S houter hfirstGap hfourth
  let first : RepresentationIndex (N + 3) (N + 3) :=
    { val := 1
      pos := by omega
      lt_large := by omega
      le_small := by omega }
  have hiEq : i = first :=
    representationIndex_eq_of_val_eq_lemma96 i first (by
      simpa only [first] using hi)
  rw [hiEq]
  have hcOneIndex : (1 : Fin (N + 3)) =
      (⟨1, by omega⟩ : Fin (N + 3)) := by
    apply Fin.ext
    change 1 % (N + 3) = 1
    rw [Nat.mod_eq_of_lt (by omega)]
  have haTwoIndex : (2 : Fin (N + 4)) =
      (⟨2, by omega⟩ : Fin (N + 4)) := by
    apply Fin.ext
    change 2 % (N + 4) = 2
    rw [Nat.mod_eq_of_lt (by omega)]
  have hcOrder : c.order (⟨1, by omega⟩ : Fin (N + 3)) =
      a.order (⟨2, by omega⟩ : Fin (N + 4)) - 1 := by
    simpa only [hcOneIndex, haTwoIndex] using O.secondOrder
  have hbTailOrder : b.tail.order (⟨0, by omega⟩ : Fin (N + 3)) =
      b.order (⟨1, by omega⟩ : Fin (N + 4)) := by
    rw [b.order_goodTail]
    congr 1
  have hbZeroIndex : (0 : Fin (N + 4)) =
      (⟨0, by omega⟩ : Fin (N + 4)) := by
    apply Fin.ext
    rfl
  have hbOneIndex : (1 : Fin (N + 4)) =
      (⟨1, by omega⟩ : Fin (N + 4)) := by
    apply Fin.ext
    change 1 % (N + 4) = 1
    rw [Nat.mod_eq_of_lt (by omega)]
  have hsourceFirstOrder' :
      b.order (⟨0, by omega⟩ : Fin (N + 4)) =
        a.order (0 : Fin (N + 4)) := by
    simpa only [hbZeroIndex] using hsourceFirstOrder
  have hsourceFirstGap' :
      2 * (ramificationIndex K : Int) ≤
        b.order (⟨1, by omega⟩ : Fin (N + 4)) -
          b.order (⟨0, by omega⟩ : Fin (N + 4)) := by
    simpa only [hbOneIndex, hbZeroIndex] using hsourceFirstGap
  have horder :
      c.order (⟨1, by omega⟩ : Fin (N + 3)) -
          b.tail.order (⟨0, by omega⟩ : Fin (N + 3)) ≤
        -(2 * (ramificationIndex K : Int)) - 1 := by
    rw [hcOrder, hbTailOrder]
    have houter' : a.order (⟨2, by omega⟩ : Fin (N + 4)) =
        a.order (0 : Fin (N + 4)) := by
      rw [← haTwoIndex, ← houter]
    rw [houter', ← hsourceFirstOrder']
    omega
  have horderQ :
      ((c.order (⟨1, by omega⟩ : Fin (N + 3)) -
          b.tail.order (⟨0, by omega⟩ : Fin (N + 3)) : Int) : ℚ) ≤
        ((-(2 * (ramificationIndex K : Int)) - 1 : Int) : ℚ) := by
    exact_mod_cast horder
  have hhalf :
      (((c.order (⟨1, by omega⟩ : Fin (N + 3)) -
            b.tail.order (⟨0, by omega⟩ : Fin (N + 3)) : Int) : ℚ) /
          2 + (ramificationIndex K : ℚ)) < 0 := by
    push_cast at horderQ ⊢
    linarith
  have hcandidate : c.representationHalfGap b.tail first < 0 := by
    unfold representationHalfGap
    exact_mod_cast hhalf
  exact (c.representationAlpha_le_halfGap b.tail first).trans_lt hcandidate

set_option maxHeartbeats 800000 in
-- The exceptional first candidate uses the complete capped-defect calculation.
/-- The exceptional first projected invariant is exactly one below the second
invariant of the original pair: this is `A₂ = A₂* + 1` in lines 9672--9677. -/
theorem representationAlpha_original_eq_projectedTail_first_add_one
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (hsourceFirstOrder :
      b.order (0 : Fin (N + 4)) = a.order (0 : Fin (N + 4)))
    (hsourceFirstGap :
      2 * (ramificationIndex K : Int) ≤
        b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4)))
    (hdefect : a.Beli2019Lemma96DefectBound b)
    (i : RepresentationIndex (N + 3) (N + 3)) (hi : i.val = 1) :
    a.representationAlpha b i.tailShift =
      (D.projectedTailGoodBONG S houter hfourth).representationAlpha
          b.tail i + (1 : WithTop ℚ) := by
  letI : Beli2006AlphaLaws.{u, v} K := targetLaws
  let c := D.projectedTailGoodBONG S houter hfourth
  let O := D.projectedTail_orderProfile S houter hfirstGap hfourth
  let first : RepresentationIndex (N + 3) (N + 3) :=
    { val := 1
      pos := by omega
      lt_large := by omega
      le_small := by omega }
  let second : RepresentationIndex (N + 4) (N + 4) :=
    secondRepresentationIndex (N + 1) (N + 2)
  have hiEq : i = first :=
    representationIndex_eq_of_val_eq_lemma96 i first (by
      simpa only [first] using hi)
  rw [hiEq]
  have hshift : first.tailShift = second := by
    apply representationIndex_eq_of_val_eq_lemma96
    simp only [first, second, RepresentationIndex.tailShift_val,
      secondRepresentationIndex]
  let twoE : WithTop ℚ :=
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)
  have horiginalCore :
      a.truncatedPrefixDefect b (-1) 3 1 = twoE := by
    apply le_antisymm
    · exact (a.truncatedPrefixDefect_le_defect b (-1) 3 1).trans_eq
        (by simpa only [twoE] using D.twistedRaw_defectOrder_eq_twoE)
    · exact hdefect
  have hcore := D.exceptionalPreviousCore_eq S houter hfirstGap hfourth hdefect
  have hprojectedCore :
      c.truncatedPrefixDefect b.tail (-1) 2 0 = twoE :=
    hcore.symm.trans horiginalCore
  have hbTailZero :
      b.tail.order (0 : Fin (N + 3)) =
        b.order (1 : Fin (N + 4)) := by
    rw [b.order_goodTail]
    congr 1
  have horiginalOrder :
      a.order (2 : Fin (N + 4)) - b.order (1 : Fin (N + 4)) +
          2 * (ramificationIndex K : Int) ≤ 0 := by
    omega
  have hprojectedOrder :
      c.order (1 : Fin (N + 3)) -
          b.tail.order (0 : Fin (N + 3)) +
          2 * (ramificationIndex K : Int) ≤ 0 := by
    rw [O.secondOrder, hbTailZero]
    omega
  have horiginalCandidateQ :
      ((a.order (2 : Fin (N + 4)) - b.order (1 : Fin (N + 4)) : Int) : ℚ) +
          2 * (ramificationIndex K : ℚ) ≤
        ((a.order (2 : Fin (N + 4)) - b.order (1 : Fin (N + 4)) : Int) : ℚ) /
            2 + (ramificationIndex K : ℚ) := by
    have hq :
        ((a.order (2 : Fin (N + 4)) - b.order (1 : Fin (N + 4)) +
            2 * (ramificationIndex K : Int) : Int) : ℚ) ≤ 0 := by
      exact_mod_cast horiginalOrder
    push_cast at hq ⊢
    linarith
  have hprojectedCandidateQ :
      ((c.order (1 : Fin (N + 3)) -
          b.tail.order (0 : Fin (N + 3)) : Int) : ℚ) +
          2 * (ramificationIndex K : ℚ) ≤
        ((c.order (1 : Fin (N + 3)) -
          b.tail.order (0 : Fin (N + 3)) : Int) : ℚ) /
            2 + (ramificationIndex K : ℚ) := by
    have hq :
        ((c.order (1 : Fin (N + 3)) -
            b.tail.order (0 : Fin (N + 3)) +
            2 * (ramificationIndex K : Int) : Int) : ℚ) ≤ 0 := by
      exact_mod_cast hprojectedOrder
    push_cast at hq ⊢
    linarith
  have horiginalCandidate :
      a.secondRepresentationPrimaryFormula b ≤
        a.secondRepresentationHalfGapFormula b := by
    unfold secondRepresentationPrimaryFormula secondRepresentationHalfGapFormula
    rw [horiginalCore]
    dsimp only [twoE]
    exact_mod_cast horiginalCandidateQ
  have hprojectedCandidate :
      c.representationPrimaryDefect b.tail first ≤
        c.representationHalfGap b.tail first := by
    change
      ((((c.order (1 : Fin (N + 3)) - b.tail.order (0 : Fin (N + 3)) : Int) : ℚ) :
            WithTop ℚ) + c.truncatedPrefixDefect b.tail (-1) 2 0) ≤
        ((((c.order (1 : Fin (N + 3)) - b.tail.order (0 : Fin (N + 3)) : Int) : ℚ) /
            2 + (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)
    rw [hprojectedCore]
    dsimp only [twoE]
    exact_mod_cast hprojectedCandidateQ
  have hprojectedAlpha :
      c.representationAlpha b.tail first =
        c.representationPrimaryDefect b.tail first := by
    rw [c.representationAlpha_eq_min_halfGap_prime b.tail first,
      c.representationAlphaPrime_eq_primary_of_not_interior b.tail first (by
        simp only [first]
        omega),
      min_eq_right hprojectedCandidate]
  have horiginalAlpha :
      a.representationAlpha b first.tailShift =
        a.representationPrimaryDefect b second := by
    rw [hshift, a.beli2019Lemma812_ii b hsourceFirstOrder.symm,
      min_eq_right horiginalCandidate]
    simpa only [second] using
      (a.representationPrimaryDefect_second_eq_formula b).symm
  rw [horiginalAlpha, hprojectedAlpha]
  change
    ((((a.order (2 : Fin (N + 4)) - b.order (1 : Fin (N + 4)) : Int) : ℚ) :
          WithTop ℚ) + a.truncatedPrefixDefect b (-1) 3 1) =
      ((((c.order (1 : Fin (N + 3)) - b.tail.order (0 : Fin (N + 3)) : Int) : ℚ) :
          WithTop ℚ) + c.truncatedPrefixDefect b.tail (-1) 2 0) + 1
  rw [horiginalCore, hprojectedCore, O.secondOrder, hbTailZero]
  dsimp only [twoE]
  norm_cast
  ring

set_option maxHeartbeats 1200000 in
-- Both branches of the central trigger transport expand dependent indices.
/-- Condition (iii)'s strict central trigger passes from the exceptional
projected pair to the original pair.  The branch `i.val = 2` is the paper's
central `i = 3` calculation: both sides acquire the same missing unit through
`A₂ = A₂* + 1` and `R₃ = R₃' + 1`. -/
theorem centralAlphaTrigger_projectedTail_to_original
    (sourceLaws : Beli2006AlphaLaws.{u, w} K)
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (hsourceFirstOrder :
      b.order (0 : Fin (N + 4)) = a.order (0 : Fin (N + 4)))
    (hsourceFirstGap :
      2 * (ramificationIndex K : Int) ≤
        b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4)))
    (hdefect : a.Beli2019Lemma96DefectBound b)
    (i : CentralRepresentationIndex (N + 3) (N + 3))
    (htrigger :
      (D.projectedTailGoodBONG S houter hfourth).centralAlphaTrigger
        b.tail i) :
    a.centralAlphaTrigger b i.tailShift := by
  letI : Beli2006AlphaLaws.{u, v} K := targetLaws
  let c := D.projectedTailGoodBONG S houter hfourth
  let O := D.projectedTail_orderProfile S houter hfirstGap hfourth
  have hiTail : i.val ≤ N + 3 := i.lt_large.le
  have hiOriginal : i.tailShift.val ≤ N + 4 := by
    simp only [CentralRepresentationIndex.tailShift_val]
    omega
  have hessential :=
    c.isEssentialFor_of_centralAlphaTrigger
      (targetLaws := sourceLaws) (sourceLaws := targetLaws)
      b.tail i htrigger
  have hpreviousEssential :
      c.IsNextEssential b.tail i.previous := by
    simpa only [IsNextEssential, nextEssentialIndex,
      CentralRepresentationIndex.previous] using hessential
  have hcurrentEssential :
      c.IsCurrentEssential b.tail (i.current hiTail) := by
    simpa only [IsCurrentEssential, currentEssentialIndex,
      CentralRepresentationIndex.current] using hessential
  have hpreviousIndex :
      i.previous.tailShift = i.tailShift.previous := by
    apply representationIndex_eq_of_val_eq_lemma96
    simp only [RepresentationIndex.tailShift_val,
      CentralRepresentationIndex.previous,
      CentralRepresentationIndex.tailShift_val]
    have := i.one_lt
    omega
  have hcurrentIndex :
      (i.current hiTail).tailShift =
        i.tailShift.current hiOriginal := by
    apply representationIndex_eq_of_val_eq_lemma96
    simp only [RepresentationIndex.tailShift_val,
      CentralRepresentationIndex.current,
      CentralRepresentationIndex.tailShift_val]
  have hcurrentAlpha :
      c.representationAlpha b.tail (i.current hiTail) =
        a.representationAlpha b (i.tailShift.current hiOriginal) := by
    rw [← hcurrentIndex]
    exact D.projectedTail_representationAlpha_eq_original_of_essential
      sourceLaws S houter hfirstGap hfourth hsourceFirstGap hdefect
      (i.current hiTail) (by
        simp only [CentralRepresentationIndex.current]
        exact i.one_lt) (Or.inl hcurrentEssential)
  have hcurrentValue :
      c.representationAlphaValue b.tail (i.current hiTail) =
        a.representationAlphaValue b (i.tailShift.current hiOriginal) := by
    have h := hcurrentAlpha
    rw [← c.coe_representationAlphaValue b.tail (i.current hiTail),
      ← a.coe_representationAlphaValue b
        (i.tailShift.current hiOriginal)] at h
    exact_mod_cast h
  have hBPreviousTwo :
      b.tail.order ⟨i.val - 2, by omega⟩ =
        b.order ⟨i.tailShift.val - 2, by omega⟩ := by
    rw [b.order_goodTail]
    apply congrArg b.order
    apply Fin.ext
    change (i.val - 2) + 1 = i.tailShift.val - 2
    simp only [CentralRepresentationIndex.tailShift_val]
    have := i.one_lt
    omega
  have hACurrent :
      c.order ⟨i.val, i.lt_large⟩ =
        a.order ⟨i.tailShift.val, i.tailShift.lt_large⟩ := by
    have h := O.laterOrders ⟨i.val, i.lt_large⟩
      (show 2 ≤ i.val from i.one_lt)
    convert h using 1
    apply congrArg a.order
    apply Fin.ext
    simp only [CentralRepresentationIndex.tailShift_val, Fin.val_succ]
  have hBPrevious :
      b.tail.order ⟨i.val - 1, by omega⟩ =
        b.order ⟨i.tailShift.val - 1, by omega⟩ := by
    rw [b.order_goodTail]
    apply congrArg b.order
    apply Fin.ext
    change (i.val - 1) + 1 = i.tailShift.val - 1
    simp only [CentralRepresentationIndex.tailShift_val]
    have := i.one_lt
    omega
  unfold centralAlphaTrigger at htrigger ⊢
  constructor
  · rw [← hBPreviousTwo, ← hACurrent]
    exact htrigger.1
  · have hsum := htrigger.2
    unfold centralAdjustedAlpha at hsum ⊢
    rw [dif_pos hiTail] at hsum
    rw [dif_pos hiOriginal]
    by_cases hiSpecial : i.val = 2
    · have hpreviousVal : i.previous.val = 1 := by
        simp only [CentralRepresentationIndex.previous]
        omega
      have hpreviousAlphaAddRaw :=
        D.representationAlpha_original_eq_projectedTail_first_add_one
          S houter hfirstGap hfourth hsourceFirstOrder hsourceFirstGap
          hdefect i.previous hpreviousVal
      have hpreviousAlphaAdd :
          a.representationAlpha b i.tailShift.previous =
            c.representationAlpha b.tail i.previous + (1 : WithTop ℚ) := by
        rw [← hpreviousIndex]
        exact hpreviousAlphaAddRaw
      have hpreviousValue :
          a.representationAlphaValue b i.tailShift.previous =
            c.representationAlphaValue b.tail i.previous + 1 := by
        have h := hpreviousAlphaAdd
        rw [← a.coe_representationAlphaValue b i.tailShift.previous,
          ← c.coe_representationAlphaValue b.tail i.previous] at h
        exact_mod_cast h
      have hAPreviousSpecial :
          c.order ⟨i.val - 1, by omega⟩ =
            a.order ⟨i.tailShift.val - 1, by omega⟩ - 1 := by
        have h := O.secondOrder
        have hcIndex :
            (⟨i.val - 1, by omega⟩ : Fin (N + 3)) =
              (1 : Fin (N + 3)) := by
          apply Fin.ext
          change i.val - 1 = 1 % (N + 3)
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        have haIndex :
            (⟨i.tailShift.val - 1, by omega⟩ : Fin (N + 4)) =
              (2 : Fin (N + 4)) := by
          apply Fin.ext
          change i.tailShift.val - 1 = 2 % (N + 4)
          rw [Nat.mod_eq_of_lt (by omega)]
          simp only [CentralRepresentationIndex.tailShift_val]
          omega
        rw [hcIndex, haIndex]
        exact h
      norm_cast at hsum ⊢
      rw [hAPreviousSpecial, hBPrevious, hcurrentValue] at hsum
      rw [hpreviousValue]
      push_cast at hsum ⊢
      linarith
    · have hiThree : 3 ≤ i.val := by
        have := i.one_lt
        omega
      have hpreviousAlpha :
          c.representationAlpha b.tail i.previous =
            a.representationAlpha b i.tailShift.previous := by
        rw [← hpreviousIndex]
        exact D.projectedTail_representationAlpha_eq_original_of_essential
          sourceLaws S houter hfirstGap hfourth hsourceFirstGap hdefect
          i.previous (by
            simp only [CentralRepresentationIndex.previous]
            omega) (Or.inr hpreviousEssential)
      have hpreviousValue :
          c.representationAlphaValue b.tail i.previous =
            a.representationAlphaValue b i.tailShift.previous := by
        have h := hpreviousAlpha
        rw [← c.coe_representationAlphaValue b.tail i.previous,
          ← a.coe_representationAlphaValue b i.tailShift.previous] at h
        exact_mod_cast h
      have hAPrevious :
          c.order ⟨i.val - 1, by omega⟩ =
            a.order ⟨i.tailShift.val - 1, by omega⟩ := by
        have h := O.laterOrders ⟨i.val - 1, by omega⟩
          (show 2 ≤ i.val - 1 from by omega)
        convert h using 1
        apply congrArg a.order
        apply Fin.ext
        change i.tailShift.val - 1 = (i.val - 1) + 1
        simp only [CentralRepresentationIndex.tailShift_val]
        omega
      norm_cast at hsum ⊢
      rw [hAPrevious, hBPrevious, hpreviousValue, hcurrentValue] at hsum
      exact hsum

/-- The concrete projected good BONG carries the complete comparison profile
required to assemble conditions (ii) and (iii) of Theorem 2.1. -/
theorem projectedTail_comparisonProfile
    (sourceLaws : Beli2006AlphaLaws.{u, w} K)
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (hsourceFirstOrder :
      b.order (0 : Fin (N + 4)) = a.order (0 : Fin (N + 4)))
    (hsourceFirstGap :
      2 * (ramificationIndex K : Int) ≤
        b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4)))
    (hdefect : a.Beli2019Lemma96DefectBound b) :
    Beli2019Lemma96TailComparisonProfile a b
      (D.projectedTailGoodBONG S houter hfourth) := by
  letI : Beli2006AlphaLaws.{u, v} K := targetLaws
  exact
    { firstAlpha_lt_zero := fun i hi ↦
        D.projectedTail_representationAlpha_first_lt_zero S houter hfirstGap
          hfourth hsourceFirstOrder hsourceFirstGap i hi
      essentialAlpha_eq := fun i hi hessential ↦
        D.projectedTail_representationAlpha_eq_original_of_essential
          sourceLaws S houter hfirstGap hfourth hsourceFirstGap hdefect
          i hi hessential
      comparisonDefect_le := fun i hi ↦
        D.truncatedPrefixDefect_shift_le_projectedTail sourceLaws S houter
          hfirstGap hfourth hsourceFirstGap 1 i.val hi i.lt_large
      centralTrigger := fun i htrigger ↦
        D.centralAlphaTrigger_projectedTail_to_original sourceLaws S houter
          hfirstGap hfourth hsourceFirstOrder hsourceFirstGap hdefect i htrigger }

end BONG.GoodBONG.Beli2019Lemma96MatchedNormalFormData

end Bong
