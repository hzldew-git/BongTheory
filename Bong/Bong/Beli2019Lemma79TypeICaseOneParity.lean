/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeICaseOneProfile
import Bong.Bong.Beli2019Lemma75PrefixParity
import Bong.Bong.Beli2019Lemma79EvenTargetParity

/-!
# Beli (2019), Lemma 7.9(ii), case 1: complementary parity

The source prefix of length `t` and the third prefix of length `t - 2`
have a signed product of odd valuation.  This is the determinant parity used
to exclude the mixed unramified endpoint class.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- In case 1, the determinant complementary to the two exceptional even
prefixes has odd valuation. -/
theorem beli2019Lemma79_typeI_caseOne_complementaryProduct_odd
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch)
    (hgap : b.orderGap ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = 2 * (ramificationIndex K : Int) + 1)
    (hprevious : c.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = b.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩) :
    Odd (ordUnit K ((-1 : Kˣ) * a.prefixProduct (i.val + 1) *
      c.prefixProduct (i.val - 1))) := by
  have hiEven : Even i.val := by
    simpa only [hleft] using C.left_even
  have hiTwo : 2 ≤ i.val := by
    have hiPos := i.pos
    rcases hiEven with ⟨d, hd⟩
    omega
  have hiBound : i.val + 1 ≤ n + 2 := Nat.succ_le_of_lt i.lt_large
  let first : Fin (n + 1) := ⟨0, by omega⟩
  let lastPair : Fin (n + 1) := ⟨i.val - 2, by omega⟩
  have hfirstLast : first ≤ lastPair := by
    exact Fin.mk_le_mk.mpr (Nat.zero_le _)
  have hlastEven : Even (lastPair.val - first.val) := by
    simp only [first, lastPair, Nat.sub_zero]
    rcases hiEven with ⟨d, hd⟩
    refine ⟨d - 1, ?_⟩
    omega
  have hlastSucc : lastPair.succ =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [lastPair, Fin.val_succ]
    omega
  rcases beli2019Lemma79_typeI_caseOne_endpointOrders
      a b c D C hnorm i hleft hgap hprevious with
    ⟨hfirstOrders, _hbLast, hcLast⟩
  have hcInitial : c.order first.castSucc = b.order 0 := by
    have hindex : first.castSucc = (0 : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hindex, ← hfirstOrders]
  have hcTerminal : c.order lastPair.succ =
      b.order 0 - 2 * (ramificationIndex K : Int) := by
    rw [hlastSucc, hcLast, ← hfirstOrders]
  have hcArithmetic := c.beli2019Lemma75_arithmetic
    first lastPair (b.order 0) hfirstLast hlastEven hcInitial hcTerminal
  have hcMod := hcArithmetic.prefixSum_modEq_of_first_zero
    c first lastPair (b.order 0) rfl hlastEven (i.val - 1) (by
      simp only [lastPair]
      omega)
  let R := a.orderSequence.entryOrZero D.anchor
  have hleftPos : 0 < C.leftSwitch := by omega
  have hbZero : b.order 0 = R + 1 := by
    change b.orderSequence.entryOrZero 0 = R + 1
    exact C.target_before_left 0 hleftPos ⟨0, by omega⟩
  have hcModR : Int.ModEq 2
      (c.orderSequence.prefixSum (i.val - 1))
      (((i.val - 1 : Nat) : Int) * (R + 1)) := by
    simpa only [hbZero] using hcMod
  have haRaw := a.lemma72_typeI_source_before_of_canonical
    b D C hfirst (i.val + 1) (by
      have hleftRight := C.left_le_anchor.trans C.anchor_le_right
      omega)
  have haBridge : Int.ModEq 2
      (((i.val + 1 : Nat) : Int) * R)
      (((i.val + 1 : Nat) : Int) * ((R + 1) + 1)) := by
    rw [Int.modEq_iff_dvd]
    refine ⟨((i.val + 1 : Nat) : Int), ?_⟩
    ring
  have haMod := haRaw.trans haBridge
  exact lemma79_typeI_even_primaryProduct_odd_of_modEq
    a c i.val hiEven hiTwo hiBound (R + 1) haMod hcModR

end BONG.GoodBONG

end Bong
