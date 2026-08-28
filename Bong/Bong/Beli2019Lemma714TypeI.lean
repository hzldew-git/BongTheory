/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714NonNormTransport
import Bong.Bong.Beli2019Lemma714Primitive
import Bong.Bong.Beli2019Lemma714TypeICoefficients
import Bong.Bong.Beli2019Lemma710BONGProduct
import Bong.Bong.BeliCorollary44ThreeBlockProof
import Bong.Bong.TwoBlockProductIsometry
import Bong.Bong.GoodExistence
import Bong.Lattice.OrthogonalProductIsometry

/-!
# Beli (2019), Lemma 7.14(ii), type I

This file constructs the good BONG
`x₃,…,xₛ, πx₁,πx₂, xₛ₊₁,…,xₙ`
on the split model `πJ ⊥ T`.  Empty end blocks are handled separately,
so none of the recursive BONG constructors is applied to a fictitiously
nonempty segment.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Every order in the selected tail block `x₃,…,xₛ` is at most
`R+2`, the order of `πx₁`. -/
theorem lemma714_selected_order_le_R_add_two
    (b : GoodBONG q L (n + 3)) (R : Int) (s k : Nat)
    (D : Lemma714MinimalityData b R s) (hsFour : 4 ≤ s)
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hkTwo : 2 ≤ k) (hks : k < s) :
    b.order ⟨k, by have := D.le_rank; omega⟩ ≤ R + 2 := by
  have hsBound := D.le_rank
  let P := b.beli2019Lemma714_i R s D hsFour hthird
  rcases Nat.even_or_odd k with hkEven | hkOdd
  · have hksHigh : k ≤ s - 2 := by
      rcases D.even with ⟨d, hd⟩
      rcases hkEven with ⟨e, he⟩
      omega
    have h := P.high_positions k hkTwo hksHigh hkEven
    omega
  · have hkThree : 3 ≤ k := by
      rcases hkOdd with ⟨d, hd⟩
      omega
    have h := P.low_positions k hkThree (by omega) hkOdd
    have hePos := ramificationIndex_pos (K := K)
    omega

/-- The last order of a nonempty selected block is the low endpoint
`R-2e+1`. -/
theorem lemma714_selected_last_order
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714MinimalityData b R s) (hsFour : 4 ≤ s)
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩) :
    b.order ⟨s - 1, by have := D.le_rank; omega⟩ =
      R - 2 * (ramificationIndex K : Int) + 1 := by
  have hsBound := D.le_rank
  let P := b.beli2019Lemma714_i R s D hsFour hthird
  apply P.low_positions (s - 1) (by omega) (by omega)
  rcases D.even with ⟨d, hd⟩
  exact ⟨d - 1, by omega⟩

/-- The initial pair `x₁,x₂` and the remaining BONG form the split
used throughout Lemma 7.14. -/
theorem lemma714_hasInitialTwoBlockSplit
    [BeliCorollary44Laws.{u, v} K]
    (b : GoodBONG q L (n + 3)) (R : Int)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩) :
    b.toBONG.HasTwoBlockSplit 2 (by omega) := by
  have h1 : 1 < n + 3 := by omega
  have h2 : 2 < n + 3 := by omega
  let i : Fin (n + 3) := Fin.mk 1 h1
  have hi : i.val + 1 < n + 3 := by
    change 1 + 1 < n + 3
    omega
  refine b.toBONG.beliCorollary44_i_unconditional b.good i hi ?_
  have hiLeft : i = (⟨1, h1⟩ : Fin (n + 3)) := by
    apply Fin.ext
    rfl
  have hiRight : (⟨i.val + 1, hi⟩ : Fin (n + 3)) =
      (⟨2, h2⟩ : Fin (n + 3)) := by
    apply Fin.ext
    rfl
  have hePos := ramificationIndex_pos (K := K)
  calc
    b.toBONG.order i = b.order ⟨1, h1⟩ := by
      change b.order i = b.order ⟨1, h1⟩
      exact congrArg b.order hiLeft
    _ = R - 2 * (ramificationIndex K : Int) := hsecond
    _ ≤ R + 1 := by omega
    _ ≤ b.order ⟨2, h2⟩ := hthird
    _ = b.toBONG.order ⟨i.val + 1, hi⟩ := by
      change b.order ⟨2, h2⟩ = b.order ⟨i.val + 1, hi⟩
      exact (congrArg b.order hiRight).symm

/-- Product-model form of Lemma 7.14(ii), type I.  The result is a good
BONG of the exact lattice `πJ ⊥ T`; the subsequent theorem transports it
to the concrete non-norm-generator lattice in the original ambient space. -/
theorem exists_lemma714_typeI_productGoodBONG
    [BeliCorollary44Laws.{u, v} K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hfirst : b.order ⟨0, by omega⟩ = R)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hI : Lemma714IsTypeI b R s)
    (S : TwoBlockSplitWitness b.toBONG 2 (by omega)) :
    ∃ result : GoodBONG
        ((q.restrict S.left.carrier S.left.nondegenerate).orthogonalSum
          (q.restrict S.right.carrier S.right.nondegenerate))
        (Lattice.product
          (Lattice.rescale (uniformizerUnit K) S.left.lattice)
          S.right.lattice)
        (n + 3),
      ∀ i, result.valueUnit i =
        lemma714TypeITargetValues b s D.two_le D.le_rank i := by
  let j := S.left.toGoodBONG b.good
  let tail := S.right.toGoodBONG b.good
  let pj := j.lemma714RescaledBinary
  have hj0 : j.order 0 = R := by
    calc
      j.order 0 = b.order (S.left.sourceIndex 0) := S.left.order_eq 0
      _ = b.order 0 := by congr 1
      _ = R := hfirst
  have hj1 : j.order 1 =
      R - 2 * (ramificationIndex K : Int) := by
    calc
      j.order 1 = b.order (S.left.sourceIndex 1) := S.left.order_eq 1
      _ = b.order 1 := by congr 1
      _ = R - 2 * (ramificationIndex K : Int) := hsecond
  have hpj0 : pj.order 0 = R + 2 := by
    rw [show pj = j.lemma714RescaledBinary by rfl,
      lemma714RescaledBinary_order, hj0]
  have hpj1 : pj.order 1 =
      R - 2 * (ramificationIndex K : Int) + 2 := by
    rw [show pj = j.lemma714RescaledBinary by rfl,
      lemma714RescaledBinary_order, hj1]
  have hpjValue (i : Fin 2) : pj.valueUnit i =
      uniformizerUnit K ^ 2 * b.valueUnit ⟨i.val, by omega⟩ := by
    calc
      pj.valueUnit i = uniformizerUnit K ^ 2 * j.valueUnit i := by
        simpa only [pj, lemma714RescaledBinary] using
          (GoodBONG.valueUnit_rescale (uniformizerUnit K) j i)
      _ = uniformizerUnit K ^ 2 * b.valueUnit ⟨i.val, by omega⟩ := by
        congr 1
        change S.left.bong.valueUnit i = b.valueUnit ⟨i.val, by omega⟩
        rw [S.left.valueUnit_eq]
        congr 1
        apply Fin.ext
        simp [BONG.SegmentWitness.sourceIndex]
  have htailLength : n + 3 - 2 = n + 1 := by omega
  let tail' : GoodBONG
      (q.restrict S.right.carrier S.right.nondegenerate)
      S.right.lattice (n + 1) := tail.castLength htailLength
  have htailOrder (i : Fin (n + 1)) :
      tail'.order i = b.order ⟨2 + i.val, by omega⟩ := by
    rw [show tail' = tail.castLength htailLength by rfl,
      order_castLength]
    change S.right.bong.order ⟨i.val, by omega⟩ = _
    rw [S.right.order_eq]
    rfl
  have htailValue (i : Fin (n + 1)) :
      tail'.valueUnit i = b.valueUnit ⟨2 + i.val, by omega⟩ := by
    rw [show tail' = tail.castLength htailLength by rfl,
      lemma714TypeI_valueUnit_castLength]
    change S.right.bong.valueUnit ⟨i.val, by omega⟩ = _
    rw [S.right.valueUnit_eq]
    rfl
  by_cases hsTwo : s = 2
  · have hsInterior : s < n + 3 := by omega
    have hnext := b.lemma714_typeI_nextOrder_ge R s hI hsInterior
    have hleftOrder : ∀ i : Fin 2, pj.order i ≤ tail'.order 0 := by
      intro i
      have hi : i.val = 0 ∨ i.val = 1 := by omega
      rcases hi with hi | hi
      · have hieq : i = (0 : Fin 2) := Fin.ext hi
        subst i
        exact (show pj.order 0 ≤ tail'.order 0 by
          rw [hpj0, htailOrder]
          simpa [hsTwo] using hnext)
      · have hieq : i = (1 : Fin 2) := Fin.ext hi
        subst i
        exact (show pj.order 1 ≤ tail'.order 0 by
          rw [hpj1, htailOrder]
          have hePos := ramificationIndex_pos (K := K)
          have hbound :
              R - 2 * (ramificationIndex K : Int) + 2 ≤
                b.order ⟨2, by omega⟩ := by
            omega
          simpa [hsTwo] using hbound)
    have hlastSecond : ∀ (_hleft : 0 < 2) (hm : 1 < n + 1),
        pj.order (1 : Fin 2) ≤ tail'.order ⟨1, hm⟩ := by
      intro _ hm
      have hstop := b.lemma714_stopOrder_ge R s D (by omega)
      calc
        pj.order (1 : Fin 2) =
            R - 2 * (ramificationIndex K : Int) + 2 := by
          simpa only using hpj1
        _ ≤ b.order ⟨3, by omega⟩ := by
          simpa [hsTwo] using hstop
        _ = tail'.order ⟨1, hm⟩ := by
          symm
          simpa only using htailOrder ⟨1, hm⟩
    let raw := pj.orthogonalProductRight_of_orderBounds tail'
      hleftOrder hlastSecond
    have hresultLength : (n + 1) + 2 = n + 3 := by omega
    let result := raw.castLength hresultLength
    refine ⟨result, ?_⟩
    intro i
    rw [show result = raw.castLength hresultLength by rfl,
      lemma714TypeI_valueUnit_castLength]
    by_cases hi : i.val < 2
    · have hiCases : i.val = 0 ∨ i.val = 1 := by omega
      rcases hiCases with hiZero | hiOne
      · have hieq : i = (0 : Fin (n + 3)) := Fin.ext hiZero
        subst i
        calc
          raw.valueUnit ⟨0, by omega⟩ = pj.valueUnit 0 := by
            have hindex : (⟨0, by omega⟩ : Fin ((n + 1) + 2)) =
                BONG.orthogonalProductLeftIndex (n + 1) (0 : Fin 2) := by
              apply Fin.ext
              rfl
            rw [hindex]
            exact GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_left
              pj tail' hleftOrder hlastSecond 0
          _ = uniformizerUnit K ^ 2 * b.valueUnit 0 := by
            simpa using hpjValue (0 : Fin 2)
          _ = lemma714TypeITargetValues b s D.two_le D.le_rank 0 := by
            symm
            simpa [hsTwo] using
              (lemma714TypeITargetValues_zero b s D.two_le D.le_rank)
      · have hieq : i = (1 : Fin (n + 3)) := Fin.ext hiOne
        subst i
        calc
          raw.valueUnit ⟨1, by omega⟩ = pj.valueUnit 1 := by
            have hindex : (⟨1, by omega⟩ : Fin ((n + 1) + 2)) =
                BONG.orthogonalProductLeftIndex (n + 1) (1 : Fin 2) := by
              apply Fin.ext
              rfl
            rw [hindex]
            exact GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_left
              pj tail' hleftOrder hlastSecond 1
          _ = uniformizerUnit K ^ 2 * b.valueUnit 1 := by
            simpa using hpjValue (1 : Fin 2)
          _ = lemma714TypeITargetValues b s D.two_le D.le_rank 1 := by
            symm
            simpa [hsTwo] using
              (lemma714TypeITargetValues_one b s D.two_le D.le_rank)
    · let k : Fin (n + 1) := ⟨i.val - 2, by omega⟩
      have hindex : (⟨i.val, by omega⟩ : Fin ((n + 1) + 2)) =
          BONG.orthogonalProductRightIndex 2 k := by
        apply Fin.ext
        simp [k, BONG.orthogonalProductRightIndex]
        omega
      calc
        raw.valueUnit ⟨i.val, by omega⟩ = tail'.valueUnit k := by
          rw [hindex]
          exact GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_right
            pj tail' hleftOrder hlastSecond k
        _ = b.valueUnit ⟨2 + k.val, by omega⟩ := htailValue k
        _ = b.valueUnit i := by
          congr 1
          apply Fin.ext
          dsimp [k]
          omega
        _ = lemma714TypeITargetValues b s D.two_le D.le_rank i := by
          symm
          exact lemma714TypeITargetValues_suffix b s D.two_le D.le_rank i
            (by omega)
  · have hsFour : 4 ≤ s := by
      have hsTwoLe := D.two_le
      rcases D.even with ⟨d, hd⟩
      omega
    rcases hI with hsTerminal | ⟨hsInterior, hnext⟩
    · have hsEq : s = n + 3 := hsTerminal
      have htailAll : ∀ i : Fin (n + 1), tail'.order i ≤ pj.order 0 := by
        intro i
        rw [htailOrder, hpj0]
        apply b.lemma714_selected_order_le_R_add_two R s (2 + i.val)
          D.toLemma714MinimalityData hsFour hthird (by omega)
        omega
      have htailLast : tail'.order ⟨n, by omega⟩ ≤ pj.order 1 := by
        rw [htailOrder, hpj1]
        have hlast := b.lemma714_selected_last_order R s
          D.toLemma714MinimalityData hsFour hthird
        have hbound : b.order ⟨s - 1, by
              have := D.le_rank
              omega⟩ ≤
            R - 2 * (ramificationIndex K : Int) + 2 := by
          rw [hlast]
          omega
        simpa [hsEq, Nat.add_comm] using hbound
      let assembled := tail'.orthogonalProductRight_of_orderBounds pj
        htailAll (fun _ _ ↦ htailLast)
      let swapped := assembled.mapLatticeIsometry
        (Lattice.orthogonalProductSwap
          (q := q.restrict S.right.carrier S.right.nondegenerate)
          (r := q.restrict S.left.carrier S.left.nondegenerate)
          (L := S.right.lattice)
          (M := Lattice.rescale (uniformizerUnit K) S.left.lattice))
      have hlength : 2 + (n + 1) = n + 3 := by omega
      let result := swapped.castLength hlength
      have hswappedValue (i : Fin (2 + (n + 1))) :
          swapped.valueUnit i = assembled.valueUnit i := by
        simpa only [swapped] using
          (GoodBONG.valueUnit_mapLatticeIsometry
            (Lattice.orthogonalProductSwap
              (q := q.restrict S.right.carrier S.right.nondegenerate)
              (r := q.restrict S.left.carrier S.left.nondegenerate)
              (L := S.right.lattice)
              (M := Lattice.rescale (uniformizerUnit K) S.left.lattice))
            assembled i)
      refine ⟨result, ?_⟩
      intro i
      rw [show result = swapped.castLength hlength by rfl,
        lemma714TypeI_valueUnit_castLength]
      by_cases hprefix : i.val < s - 2
      · let k : Fin (n + 1) := ⟨i.val, by omega⟩
        have hindex : (⟨i.val, by omega⟩ : Fin (2 + (n + 1))) =
            BONG.orthogonalProductLeftIndex 2 k := by
          apply Fin.ext
          rfl
        calc
          swapped.valueUnit ⟨i.val, by omega⟩ =
              assembled.valueUnit ⟨i.val, by omega⟩ :=
            hswappedValue ⟨i.val, by omega⟩
          _ = tail'.valueUnit k := by
            rw [hindex]
            exact
              GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_left
                tail' pj htailAll (fun _ _ ↦ htailLast) k
          _ = b.valueUnit ⟨2 + k.val, by
              have hk := k.isLt
              omega⟩ := htailValue k
          _ = lemma714TypeITargetValues b s D.two_le D.le_rank i := by
            symm
            calc
              lemma714TypeITargetValues b s D.two_le D.le_rank i =
                  b.valueUnit ⟨i.val + 2, by omega⟩ :=
                lemma714TypeITargetValues_prefix b s D.two_le D.le_rank i
                  hprefix
              _ = b.valueUnit ⟨2 + k.val, by
                  have hk := k.isLt
                  omega⟩ := by
                congr 1
                apply Fin.ext
                dsimp [k]
                omega
      · have hiCases : i.val = s - 2 ∨ i.val = s - 1 := by
          omega
        rcases hiCases with hiZero | hiOne
        · have hieq : i = ⟨s - 2, by omega⟩ := Fin.ext hiZero
          rw [hieq]
          have hindex : (⟨s - 2, by omega⟩ : Fin (2 + (n + 1))) =
              BONG.orthogonalProductRightIndex (n + 1) (0 : Fin 2) := by
            apply Fin.ext
            simp [BONG.orthogonalProductRightIndex, hsEq]
          calc
            swapped.valueUnit ⟨s - 2, by omega⟩ =
                assembled.valueUnit ⟨s - 2, by omega⟩ :=
              hswappedValue ⟨s - 2, by omega⟩
            _ = pj.valueUnit 0 := by
              rw [hindex]
              exact
                GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_right
                  tail' pj htailAll (fun _ _ ↦ htailLast) 0
            _ = uniformizerUnit K ^ 2 * b.valueUnit 0 := by
              simpa using hpjValue (0 : Fin 2)
            _ = lemma714TypeITargetValues b s D.two_le D.le_rank
                ⟨s - 2, by omega⟩ := by
              symm
              exact lemma714TypeITargetValues_zero b s D.two_le D.le_rank
        · have hieq : i = ⟨s - 1, by omega⟩ := Fin.ext hiOne
          rw [hieq]
          have hindex : (⟨s - 1, by omega⟩ : Fin (2 + (n + 1))) =
              BONG.orthogonalProductRightIndex (n + 1) (1 : Fin 2) := by
            apply Fin.ext
            simp [BONG.orthogonalProductRightIndex, hsEq]
          calc
            swapped.valueUnit ⟨s - 1, by omega⟩ =
                assembled.valueUnit ⟨s - 1, by omega⟩ :=
              hswappedValue ⟨s - 1, by omega⟩
            _ = pj.valueUnit 1 := by
              rw [hindex]
              exact
                GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_right
                  tail' pj htailAll (fun _ _ ↦ htailLast) 1
            _ = uniformizerUnit K ^ 2 * b.valueUnit 1 := by
              simpa using hpjValue (1 : Fin 2)
            _ = lemma714TypeITargetValues b s D.two_le D.le_rank
                ⟨s - 1, by omega⟩ := by
              symm
              exact lemma714TypeITargetValues_one b s D.two_le D.le_rank
    · have hcut : s - 2 ≤ n + 1 := by omega
      let cutIndex : Fin (n + 1) := ⟨s - 3, by omega⟩
      have hcutNext : cutIndex.val + 1 < n + 1 := by
        dsimp [cutIndex]
        omega
      have hcutOrder :
          tail'.order cutIndex ≤
            tail'.order ⟨cutIndex.val + 1, hcutNext⟩ := by
        rw [htailOrder, htailOrder]
        have hlast := b.lemma714_selected_last_order R s
          D.toLemma714MinimalityData hsFour hthird
        have hleftIndex :
            (⟨2 + cutIndex.val, by omega⟩ : Fin (n + 3)) =
              ⟨s - 1, by have := D.le_rank; omega⟩ := by
          apply Fin.ext
          dsimp [cutIndex]
          omega
        have hrightIndex :
            (⟨2 + (cutIndex.val + 1), by omega⟩ : Fin (n + 3)) =
              ⟨s, hsInterior⟩ := by
          apply Fin.ext
          dsimp [cutIndex]
          omega
        rw [hleftIndex, hrightIndex, hlast]
        have hePos := ramificationIndex_pos (K := K)
        exact (show
          R - 2 * (ramificationIndex K : Int) + 1 ≤ R + 2 by
            omega).trans hnext
      have hsplit :
          tail'.toBONG.HasTwoBlockSplit (s - 2) hcut := by
        have hraw := tail'.toBONG.beliCorollary44_i_unconditional tail'.good cutIndex
          hcutNext hcutOrder
        simpa only [cutIndex, show s - 3 + 1 = s - 2 by omega] using hraw
      rcases hsplit with ⟨U⟩
      let a := U.left.toGoodBONG tail'.good
      let c := U.right.toGoodBONG tail'.good
      have haValue (i : Fin (s - 2)) :
          a.valueUnit i = b.valueUnit ⟨2 + i.val, by omega⟩ := by
        change U.left.bong.valueUnit i = _
        rw [U.left.valueUnit_eq]
        change tail'.valueUnit (U.left.sourceIndex i) = _
        rw [htailValue]
        congr 1
        apply Fin.ext
        simp [BONG.SegmentWitness.sourceIndex]
      have haOrder : ∀ i : Fin (s - 2), a.order i ≤ pj.order 0 := by
        intro i
        have ht := htailOrder (U.left.sourceIndex i)
        have hindex :
            (⟨2 + (U.left.sourceIndex i).val, by omega⟩ : Fin (n + 3)) =
              ⟨2 + i.val, by omega⟩ := by
          apply Fin.ext
          simp [BONG.SegmentWitness.sourceIndex]
        have ht' : tail'.order (U.left.sourceIndex i) =
            b.order ⟨2 + i.val, by omega⟩ := by
          calc
            tail'.order (U.left.sourceIndex i) =
                b.order ⟨2 + (U.left.sourceIndex i).val, by omega⟩ := ht
            _ = b.order ⟨2 + i.val, by omega⟩ :=
              congrArg b.order hindex
        calc
          a.order i = tail'.order (U.left.sourceIndex i) :=
            U.left.order_eq i
          _ = b.order ⟨2 + i.val, by omega⟩ := ht'
          _ ≤ R + 2 :=
            b.lemma714_selected_order_le_R_add_two R s (2 + i.val)
              D.toLemma714MinimalityData hsFour hthird (by omega) (by omega)
          _ = pj.order 0 := hpj0.symm
      have haLastSecond : ∀ (_ha : 0 < s - 2) (_hm : 1 < 2),
          a.order ⟨s - 2 - 1, by omega⟩ ≤ pj.order ⟨1, by omega⟩ := by
        intro _ _
        let last : Fin (s - 2) := ⟨s - 2 - 1, by omega⟩
        have ht := htailOrder (U.left.sourceIndex last)
        have ht' : tail'.order (U.left.sourceIndex last) =
            b.order ⟨s - 1, by have := D.le_rank; omega⟩ := by
          have hindex :
              (⟨2 + (U.left.sourceIndex last).val, by omega⟩ : Fin (n + 3)) =
                ⟨s - 1, by have := D.le_rank; omega⟩ := by
            apply Fin.ext
            simp [last, BONG.SegmentWitness.sourceIndex]
            omega
          calc
            tail'.order (U.left.sourceIndex last) =
                b.order ⟨2 + (U.left.sourceIndex last).val, by omega⟩ := ht
            _ = b.order ⟨s - 1, by have := D.le_rank; omega⟩ :=
              congrArg b.order hindex
        have hlast := b.lemma714_selected_last_order R s
          D.toLemma714MinimalityData hsFour hthird
        have hbound : b.order ⟨s - 1, by
              have := D.le_rank
              omega⟩ ≤
            R - 2 * (ramificationIndex K : Int) + 2 := by
          rw [hlast]
          omega
        calc
          a.order ⟨s - 2 - 1, by omega⟩ =
              tail'.order (U.left.sourceIndex last) := by
            exact U.left.order_eq last
          _ = b.order ⟨s - 1, by have := D.le_rank; omega⟩ := ht'
          _ ≤ R - 2 * (ramificationIndex K : Int) + 2 := hbound
          _ = pj.order ⟨1, by omega⟩ := by
            calc
              R - 2 * (ramificationIndex K : Int) + 2 =
                  pj.order (1 : Fin 2) := hpj1.symm
              _ = pj.order ⟨1, by omega⟩ := by congr 1
      let apj := a.orthogonalProductRight_of_orderBounds pj
        haOrder haLastSecond
      have hapjLength : 2 + (s - 2) = s := by omega
      let apj' := apj.castLength hapjLength
      have hapjPrefixValue (i : Fin (s - 2)) :
          apj'.valueUnit ⟨i.val, by omega⟩ =
            b.valueUnit ⟨2 + i.val, by omega⟩ := by
        rw [show apj' = apj.castLength hapjLength by rfl,
          lemma714TypeI_valueUnit_castLength]
        have hindex : (⟨i.val, by omega⟩ : Fin (2 + (s - 2))) =
            BONG.orthogonalProductLeftIndex 2 i := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact
          (GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_left
            a pj haOrder haLastSecond i).trans (haValue i)
      have hapjZeroValue : apj'.valueUnit ⟨s - 2, by omega⟩ =
          uniformizerUnit K ^ 2 * b.valueUnit 0 := by
        rw [show apj' = apj.castLength hapjLength by rfl,
          lemma714TypeI_valueUnit_castLength]
        have hindex : (⟨s - 2, by omega⟩ : Fin (2 + (s - 2))) =
            BONG.orthogonalProductRightIndex (s - 2) (0 : Fin 2) := by
          apply Fin.ext
          simp [BONG.orthogonalProductRightIndex]
        rw [hindex]
        exact
          (GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_right
            a pj haOrder haLastSecond 0).trans (hpjValue 0)
      have hapjOneValue : apj'.valueUnit ⟨s - 1, by omega⟩ =
          uniformizerUnit K ^ 2 * b.valueUnit 1 := by
        rw [show apj' = apj.castLength hapjLength by rfl,
          lemma714TypeI_valueUnit_castLength]
        have hindex : (⟨s - 1, by omega⟩ : Fin (2 + (s - 2))) =
            BONG.orthogonalProductRightIndex (s - 2) (1 : Fin 2) := by
          apply Fin.ext
          simp [BONG.orthogonalProductRightIndex]
          omega
        rw [hindex]
        exact
          (GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_right
            a pj haOrder haLastSecond 1).trans (hpjValue 1)
      have hcLength : (n + 1) - (s - 2) = (n + 2 - s) + 1 := by omega
      let c' := c.castLength hcLength
      have hcOrder (i : Fin ((n + 2 - s) + 1)) :
          c'.order i = b.order ⟨s + i.val, by omega⟩ := by
        rw [show c' = c.castLength hcLength by rfl, order_castLength]
        let i' : Fin ((n + 1) - (s - 2)) := ⟨i.val, by omega⟩
        change U.right.bong.order i' = _
        calc
          U.right.bong.order i' = tail'.order (U.right.sourceIndex i') :=
            U.right.order_eq i'
          _ = b.order ⟨2 + (U.right.sourceIndex i').val, by omega⟩ :=
            htailOrder (U.right.sourceIndex i')
          _ = b.order ⟨s + i.val, by omega⟩ := by
            congr 1
            apply Fin.ext
            simp [i', BONG.SegmentWitness.sourceIndex]
            omega
      have hcValue (i : Fin ((n + 2 - s) + 1)) :
          c'.valueUnit i = b.valueUnit ⟨s + i.val, by omega⟩ := by
        rw [show c' = c.castLength hcLength by rfl,
          lemma714TypeI_valueUnit_castLength]
        let i' : Fin ((n + 1) - (s - 2)) := ⟨i.val, by omega⟩
        change U.right.bong.valueUnit i' = _
        rw [U.right.valueUnit_eq]
        change tail'.valueUnit (U.right.sourceIndex i') = _
        rw [htailValue]
        congr 1
        apply Fin.ext
        simp [i', BONG.SegmentWitness.sourceIndex]
        omega
      have hapjPenultimate : apj'.order ⟨s - 2, by omega⟩ = R + 2 := by
        rw [show apj' = apj.castLength hapjLength by rfl, order_castLength]
        change apj.order ⟨s - 2, by omega⟩ = _
        have hindex : (⟨s - 2, by omega⟩ : Fin (2 + (s - 2))) =
            BONG.orthogonalProductRightIndex (s - 2) (0 : Fin 2) := by
          apply Fin.ext
          simp [BONG.orthogonalProductRightIndex]
        rw [hindex]
        exact (BONG.order_orthogonalProductRight_right
          a.toBONG pj.toBONG haOrder 0).trans hpj0
      have hapjLast : apj'.order ⟨s - 1, by omega⟩ =
          R - 2 * (ramificationIndex K : Int) + 2 := by
        rw [show apj' = apj.castLength hapjLength by rfl, order_castLength]
        change apj.order ⟨s - 1, by omega⟩ = _
        have hindex : (⟨s - 1, by omega⟩ : Fin (2 + (s - 2))) =
            BONG.orthogonalProductRightIndex (s - 2) (1 : Fin 2) := by
          apply Fin.ext
          simp [BONG.orthogonalProductRightIndex]
          omega
        rw [hindex]
        exact (BONG.order_orthogonalProductRight_right
          a.toBONG pj.toBONG haOrder 1).trans hpj1
      have hcHead : R + 2 ≤ c'.order 0 := by
        rw [hcOrder]
        simpa using hnext
      have hcSecond : ∀ hm : 1 < (n + 2 - s) + 1,
          R - 2 * (ramificationIndex K : Int) + 2 ≤
            c'.order ⟨1, hm⟩ := by
        intro hm
        rw [hcOrder]
        exact b.lemma714_stopOrder_ge R s D (by omega)
      have hapjTwo : 2 ≤ s := by omega
      have hapjPenultimateLe :
          apj'.order ⟨s - 2, by omega⟩ ≤ c'.order 0 := by
        rw [hapjPenultimate]
        exact hcHead
      have hapjLastHeadLe :
          apj'.order ⟨s - 1, by omega⟩ ≤ c'.order 0 := by
        rw [hapjLast]
        exact hcHead.trans' (by
          have hePos := ramificationIndex_pos (K := K)
          omega)
      have hapjLastSecondLe : ∀ hm : 1 < (n + 2 - s) + 1,
          apj'.order ⟨s - 1, by omega⟩ ≤ c'.order ⟨1, hm⟩ := by
        intro hm
        rw [hapjLast]
        exact hcSecond hm
      let assembled := apj'.orthogonalProductRight_of_endpointBounds c'
        hapjTwo hapjPenultimateLe hapjLastHeadLe hapjLastSecondLe
      let tailSplit : Lattice.Isometry
          (q.restrict S.right.carrier S.right.nondegenerate)
          (((q.restrict S.right.carrier S.right.nondegenerate).restrict
              U.left.carrier U.left.nondegenerate).orthogonalSum
            ((q.restrict S.right.carrier S.right.nondegenerate).restrict
              U.right.carrier U.right.nondegenerate))
          S.right.lattice
          (Lattice.product U.left.lattice U.right.lattice) :=
        U.toProductLatticeIsometry.symm
      let splitProduct :=
        Lattice.Isometry.orthogonalProductBasic
          (Lattice.Isometry.refl
          (q.restrict S.left.carrier S.left.nondegenerate)
          (Lattice.rescale (uniformizerUnit K) S.left.lattice))
          tailSplit
      let rotated := splitProduct.trans
        (Lattice.orthogonalProductRotateLeft
          (q := q.restrict S.left.carrier S.left.nondegenerate)
          (r := (q.restrict S.right.carrier S.right.nondegenerate).restrict
            U.left.carrier U.left.nondegenerate)
          (s := (q.restrict S.right.carrier S.right.nondegenerate).restrict
            U.right.carrier U.right.nondegenerate)
          (L := Lattice.rescale (uniformizerUnit K) S.left.lattice)
          (M := U.left.lattice) (N := U.right.lattice))
      let mapped := assembled.mapLatticeIsometry rotated.symm
      have hlength : ((n + 2 - s) + 1) + s = n + 3 := by omega
      let result := mapped.castLength hlength
      have hmappedValue (i : Fin (((n + 2 - s) + 1) + s)) :
          mapped.valueUnit i = assembled.valueUnit i := by
        simpa only [mapped] using
          (GoodBONG.valueUnit_mapLatticeIsometry rotated.symm assembled i)
      refine ⟨result, ?_⟩
      intro i
      rw [show result = mapped.castLength hlength by rfl,
        lemma714TypeI_valueUnit_castLength]
      by_cases hprefix : i.val < s - 2
      · let k : Fin (s - 2) := ⟨i.val, hprefix⟩
        let k' : Fin s := ⟨i.val, by omega⟩
        have hindex :
            (⟨i.val, by omega⟩ : Fin (((n + 2 - s) + 1) + s)) =
              BONG.orthogonalProductLeftIndex ((n + 2 - s) + 1) k' := by
          apply Fin.ext
          rfl
        calc
          mapped.valueUnit ⟨i.val, by omega⟩ =
              assembled.valueUnit ⟨i.val, by omega⟩ :=
            hmappedValue ⟨i.val, by omega⟩
          _ = apj'.valueUnit k' := by
            rw [hindex]
            exact
              GoodBONG.valueUnit_orthogonalProductRight_of_endpointBounds_left
                apj' c' hapjTwo hapjPenultimateLe hapjLastHeadLe
                  hapjLastSecondLe k'
          _ = b.valueUnit ⟨2 + k.val, by
              have hk := k.isLt
              omega⟩ := by
            simpa only [k, k'] using hapjPrefixValue k
          _ = lemma714TypeITargetValues b s D.two_le D.le_rank i := by
            symm
            calc
              lemma714TypeITargetValues b s D.two_le D.le_rank i =
                  b.valueUnit ⟨i.val + 2, by omega⟩ :=
                lemma714TypeITargetValues_prefix b s D.two_le D.le_rank i
                  hprefix
              _ = b.valueUnit ⟨2 + k.val, by
                  have hk := k.isLt
                  omega⟩ := by
                congr 1
                apply Fin.ext
                dsimp [k]
                omega
      · by_cases hzero : i.val = s - 2
        · rw [show i = ⟨s - 2, by omega⟩ from Fin.ext hzero]
          have hindex :
              (⟨s - 2, by omega⟩ : Fin (((n + 2 - s) + 1) + s)) =
                BONG.orthogonalProductLeftIndex ((n + 2 - s) + 1)
                  (⟨s - 2, by omega⟩ : Fin s) := by
            apply Fin.ext
            rfl
          calc
            mapped.valueUnit ⟨s - 2, by omega⟩ =
                assembled.valueUnit ⟨s - 2, by omega⟩ :=
              hmappedValue ⟨s - 2, by omega⟩
            _ = apj'.valueUnit ⟨s - 2, by omega⟩ := by
              rw [hindex]
              exact
                GoodBONG.valueUnit_orthogonalProductRight_of_endpointBounds_left
                  apj' c' hapjTwo hapjPenultimateLe hapjLastHeadLe
                    hapjLastSecondLe ⟨s - 2, by omega⟩
            _ = uniformizerUnit K ^ 2 * b.valueUnit 0 := hapjZeroValue
            _ = lemma714TypeITargetValues b s D.two_le D.le_rank
                ⟨s - 2, by omega⟩ := by
              symm
              exact lemma714TypeITargetValues_zero b s D.two_le D.le_rank
        · by_cases hone : i.val = s - 1
          · rw [show i = ⟨s - 1, by omega⟩ from Fin.ext hone]
            have hindex :
                (⟨s - 1, by omega⟩ : Fin (((n + 2 - s) + 1) + s)) =
                  BONG.orthogonalProductLeftIndex ((n + 2 - s) + 1)
                    (⟨s - 1, by omega⟩ : Fin s) := by
              apply Fin.ext
              rfl
            calc
              mapped.valueUnit ⟨s - 1, by omega⟩ =
                  assembled.valueUnit ⟨s - 1, by omega⟩ :=
                hmappedValue ⟨s - 1, by omega⟩
              _ = apj'.valueUnit ⟨s - 1, by omega⟩ := by
                rw [hindex]
                exact
                  GoodBONG.valueUnit_orthogonalProductRight_of_endpointBounds_left
                    apj' c' hapjTwo hapjPenultimateLe hapjLastHeadLe
                      hapjLastSecondLe ⟨s - 1, by omega⟩
              _ = uniformizerUnit K ^ 2 * b.valueUnit 1 := hapjOneValue
              _ = lemma714TypeITargetValues b s D.two_le D.le_rank
                  ⟨s - 1, by omega⟩ := by
                symm
                exact lemma714TypeITargetValues_one b s D.two_le D.le_rank
          · have hsuffix : s ≤ i.val := by omega
            let k : Fin ((n + 2 - s) + 1) := ⟨i.val - s, by omega⟩
            have hindex :
                (⟨i.val, by omega⟩ : Fin (((n + 2 - s) + 1) + s)) =
                  BONG.orthogonalProductRightIndex s k := by
              apply Fin.ext
              simp [k, BONG.orthogonalProductRightIndex]
              omega
            calc
              mapped.valueUnit ⟨i.val, by omega⟩ =
                  assembled.valueUnit ⟨i.val, by omega⟩ :=
                hmappedValue ⟨i.val, by omega⟩
              _ = c'.valueUnit k := by
                rw [hindex]
                exact
                  GoodBONG.valueUnit_orthogonalProductRight_of_endpointBounds_right
                    apj' c' hapjTwo hapjPenultimateLe hapjLastHeadLe
                      hapjLastSecondLe k
              _ = b.valueUnit ⟨s + k.val, by omega⟩ := hcValue k
              _ = b.valueUnit i := by
                congr 1
                apply Fin.ext
                dsimp [k]
                omega
              _ = lemma714TypeITargetValues b s D.two_le D.le_rank i := by
                symm
                exact lemma714TypeITargetValues_suffix b s D.two_le D.le_rank i
                  hsuffix

/-- Low-level actual-lattice form of Lemma 7.14(ii), type I, parameterized by
the primitive-vector property of its initial binary block. -/
theorem exists_lemma714_typeI_nonNormGoodBONG_of_everyPrimitive
    [BeliCorollary44Laws.{u, v} K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hfirst : b.order ⟨0, by omega⟩ = R)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hI : Lemma714IsTypeI b R s)
    (S : TwoBlockSplitWitness b.toBONG 2 (by omega))
    (hnorm : Lattice.normIdeal q L = Lattice.powerIdeal (K := K) R)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.powerIdeal (K := K)
        (R - ramificationIndex K + 1))
    (hprimitive : Lattice.EveryPrimitiveIsNormGenerator
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice) :
    ∃ result : GoodBONG q
        (Lattice.nonNormGeneratorLattice R hnorm hscale) (n + 3),
      ∀ i, result.valueUnit i =
        lemma714TypeITargetValues b s D.two_le D.le_rank i := by
  let j := S.left.toGoodBONG b.good
  have hj0 : j.order 0 = R := by
    calc
      j.order 0 = b.order (S.left.sourceIndex 0) := S.left.order_eq 0
      _ = b.order 0 := by congr 1
      _ = R := hfirst
  have hnormJ : Lattice.normIdeal
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice =
        Lattice.powerIdeal (K := K) R := by
    calc
      Lattice.normIdeal
          (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice =
          Lattice.powerIdeal (K := K) (j.order 0) :=
        j.toBONG.normIdeal_eq_powerIdeal_order_zero
      _ = Lattice.powerIdeal (K := K) R := by rw [hj0]
  let tail := S.right.toGoodBONG b.good
  have htailLength : n + 3 - 2 = n + 1 := by omega
  let tail' : GoodBONG
      (q.restrict S.right.carrier S.right.nondegenerate)
      S.right.lattice (n + 1) := tail.castLength htailLength
  have htail0 : tail'.order 0 = b.order ⟨2, by omega⟩ := by
    rw [show tail' = tail.castLength htailLength by rfl,
      order_castLength]
    change S.right.bong.order ⟨0, by omega⟩ = _
    rw [S.right.order_eq]
    rfl
  have hnormT : Lattice.normIdeal
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice ≤
        Lattice.powerIdeal (K := K) (R + 1) := by
    rw [tail'.toBONG.normIdeal_eq_powerIdeal_order_zero]
    apply (Lattice.powerIdeal_le_iff (K := K) (tail'.order 0) (R + 1)).2
    rwa [htail0]
  rcases b.exists_lemma714_typeI_productGoodBONG R s D hfirst hsecond
      hthird hI S with ⟨productBONG, hproductValues⟩
  let toNonNorm :=
    Lattice.rescaledLeftProductToNonNormIsometry R hnormJ hnormT
      hprimitive S.toProductLatticeIsometry hscale
  let result := productBONG.mapLatticeIsometry toNonNorm
  refine ⟨result, ?_⟩
  intro i
  calc
    result.valueUnit i = productBONG.valueUnit i := by
      simpa only [result] using
        (GoodBONG.valueUnit_mapLatticeIsometry toNonNorm productBONG i)
    _ = lemma714TypeITargetValues b s D.two_le D.le_rank i :=
      hproductValues i

/-- Actual-lattice form of Lemma 7.14(ii), type I.  The paper's condition
`a₂/a₁ ∈ -Δ/4 · O²` implies that every primitive vector of the
initial binary block is a norm generator, so no extra primitive-vector
hypothesis remains in this public theorem. -/
theorem exists_lemma714_typeI_nonNormGoodBONG
    [laws : DyadicDiscriminantClassLaws K]
    [BeliCorollary44Laws.{u, v} K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hfirst : b.order ⟨0, by omega⟩ = R)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hI : Lemma714IsTypeI b R s)
    (S : TwoBlockSplitWitness b.toBONG 2 (by omega))
    (hnorm : Lattice.normIdeal q L = Lattice.powerIdeal (K := K) R)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.powerIdeal (K := K)
        (R - ramificationIndex K + 1))
    (hdiscriminant : b.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (negativeQuarterUnit K * laws.discriminantUnit)) :
    ∃ result : GoodBONG q
        (Lattice.nonNormGeneratorLattice R hnorm hscale) (n + 3),
      ∀ i, result.valueUnit i =
        lemma714TypeITargetValues b s D.two_le D.le_rank i := by
  let j := S.left.toGoodBONG b.good
  have hjClass : j.toBONG.binaryUnitSquareClass = unitSquareClass K
      (negativeQuarterUnit K * laws.discriminantUnit) := by
    change S.left.bong.binaryUnitSquareClass = unitSquareClass K
      (negativeQuarterUnit K * laws.discriminantUnit)
    calc
      S.left.bong.binaryUnitSquareClass =
          b.toBONG.adjacentUnitSquareClass
            (0 : Fin (n + 3)) (by simp) := by
        unfold binaryUnitSquareClass binaryParameter
          adjacentUnitSquareClass adjacentParameter
        apply congrArg (unitSquareClass K)
        rw [S.left.valueUnit_eq, S.left.valueUnit_eq]
        congr 2 <;> apply Fin.ext <;>
          simp [BONG.SegmentWitness.sourceIndex]
      _ = unitSquareClass K
          (negativeQuarterUnit K * laws.discriminantUnit) := hdiscriminant
  have hprimitive : Lattice.EveryPrimitiveIsNormGenerator
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice :=
    j.toBONG.everyPrimitiveIsNormGenerator_of_binaryUnitSquareClass_discriminant
      hjClass
  exact b.exists_lemma714_typeI_nonNormGoodBONG_of_everyPrimitive
    R s D hfirst hsecond hthird hI S hnorm hscale hprimitive

end BONG.GoodBONG

end Bong
