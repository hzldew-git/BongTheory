/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714TypeIIAssembly
import Bong.Bong.Beli2019Lemma714TypeI
import Bong.Bong.BeliCorollary44ThreeBlockProof

/-!
# Beli (2019), Lemma 7.14(ii): the type-II Lemma 7.10 frame

For an interior type-II endpoint, the tail splits as
`[x_3,...,x_s] perp [x_(s+1),...,x_N]`.  The first segment can then be
adjoined to the rescaled initial binary block, giving the first good BONG
in the precise statement of Lemma 7.10:

`x_3,...,x_s, pi x_1, pi x_2`.

This file records that frame independently of the exceptional ternary
replacement.  The boundary case `s = 2` uses the canonical zero-prefix
split, so the same frame covers the empty first segment.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

private theorem lemma714TypeIIFrame_two_le_rank (n : Nat) : 2 ≤ n + 3 := by
  omega

private theorem lemma714TypeII_ambientVector_castLength
    {m length : Nat} {Q : QuadraticSpace K V} {M : Lattice K V}
    (a : GoodBONG Q M m) (h : m = length) (i : Fin length) :
    (a.castLength h).toBONG.ambientVector i =
      a.toBONG.ambientVector ⟨i.val, by omega⟩ := by
  subst length
  rfl

/-- The cut immediately before `x_(s+1)` is an actual orthogonal lattice
split.  At `s = 2` this is the canonical zero-prefix split. -/
theorem exists_lemma714_typeII_selectedTailSplit
    [BeliCorollary44Laws.{u, v} K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hII : Lemma714IsTypeII b R s)
    (S : TwoBlockSplitWitness b.toBONG 2
      (lemma714TypeIIFrame_two_le_rank n))
    (hsFour : s = 2 ∨ 4 ≤ s) :
    Nonempty ((b.lemma714Tail S).toBONG.TwoBlockSplitWitness
      (s - 2) (by have := D.le_rank; omega)) := by
  rcases hsFour with hsTwo | hsFour
  · subst s
    exact ⟨(b.lemma714Tail S).toBONG.zeroTwoBlockSplitWitness⟩
  rcases hII with ⟨hsCurrent, hcurrent⟩
  let tail := b.lemma714Tail S
  let cutIndex : Fin (n + 1) := ⟨s - 3, by
    have := D.le_rank
    omega⟩
  have hcutNext : cutIndex.val + 1 < n + 1 := by
    dsimp [cutIndex]
    omega
  have hcutOrder :
      tail.order cutIndex ≤
        tail.order ⟨cutIndex.val + 1, hcutNext⟩ := by
    have hlast := b.lemma714_selected_last_order R s
      D.toLemma714MinimalityData hsFour hthird
    rw [show tail = b.lemma714Tail S by rfl,
      b.lemma714Tail_order S, b.lemma714Tail_order S]
    have hleft :
        (⟨2 + cutIndex.val, by omega⟩ : Fin (n + 3)) =
          ⟨s - 1, by have := D.le_rank; omega⟩ := by
      apply Fin.ext
      dsimp [cutIndex]
      omega
    have hright :
        (⟨2 + (cutIndex.val + 1), by omega⟩ : Fin (n + 3)) =
          ⟨s, hsCurrent⟩ := by
      apply Fin.ext
      dsimp [cutIndex]
      omega
    rw [hleft, hright, hlast, hcurrent]
    have hePos := ramificationIndex_pos (K := K)
    omega
  have hsplit :=
    tail.toBONG.beliCorollary44_i_unconditional tail.good cutIndex hcutNext hcutOrder
  change Nonempty (tail.toBONG.TwoBlockSplitWitness
    (cutIndex.val + 1) _) at hsplit
  simpa only [tail, cutIndex, show s - 3 + 1 = s - 2 by omega] using hsplit

/-- The selected tail prefix as a good BONG. -/
noncomputable def lemma714TypeIISelectedPrefix
    (b : GoodBONG q L (n + 3))
    (S : TwoBlockSplitWitness b.toBONG 2
      (lemma714TypeIIFrame_two_le_rank n))
    (s : Nat) (hsTwo : 2 ≤ s) (hsBound : s ≤ n + 3)
    (U : (b.lemma714Tail S).toBONG.TwoBlockSplitWitness
      (s - 2) (by omega)) :
    GoodBONG
      ((q.restrict S.right.carrier S.right.nondegenerate).restrict
        U.left.carrier U.left.nondegenerate)
      U.left.lattice (s - 2) :=
  U.left.toGoodBONG (b.lemma714Tail S).good

/-- The tail beginning at `x_(s+1)` as a good BONG. -/
noncomputable def lemma714TypeIIRightSuffix
    (b : GoodBONG q L (n + 3))
    (S : TwoBlockSplitWitness b.toBONG 2
      (lemma714TypeIIFrame_two_le_rank n))
    (s : Nat) (hsTwo : 2 ≤ s) (hs : s < n + 3)
    (U : (b.lemma714Tail S).toBONG.TwoBlockSplitWitness
      (s - 2) (by omega)) :
    GoodBONG
      ((q.restrict S.right.carrier S.right.nondegenerate).restrict
        U.right.carrier U.right.nondegenerate)
      U.right.lattice (n + 3 - s) :=
  (U.right.toGoodBONG (b.lemma714Tail S).good).castLength (by omega)

@[simp]
theorem lemma714TypeIISelectedPrefix_order
    (b : GoodBONG q L (n + 3))
    (S : TwoBlockSplitWitness b.toBONG 2
      (lemma714TypeIIFrame_two_le_rank n))
    (s : Nat) (hsTwo : 2 ≤ s) (hsBound : s ≤ n + 3)
    (U : (b.lemma714Tail S).toBONG.TwoBlockSplitWitness
      (s - 2) (by omega)) (i : Fin (s - 2)) :
    (b.lemma714TypeIISelectedPrefix S s hsTwo hsBound U).order i =
      b.order ⟨2 + i.val, by omega⟩ := by
  change U.left.bong.order i = _
  rw [U.left.order_eq]
  change (b.lemma714Tail S).order (U.left.sourceIndex i) = _
  rw [b.lemma714Tail_order S]
  congr 1
  apply Fin.ext
  simp [BONG.SegmentWitness.sourceIndex]

@[simp]
theorem lemma714TypeIIRightSuffix_order
    (b : GoodBONG q L (n + 3))
    (S : TwoBlockSplitWitness b.toBONG 2
      (lemma714TypeIIFrame_two_le_rank n))
    (s : Nat) (hsTwo : 2 ≤ s) (hs : s < n + 3)
    (U : (b.lemma714Tail S).toBONG.TwoBlockSplitWitness
      (s - 2) (by omega)) (i : Fin (n + 3 - s)) :
    (b.lemma714TypeIIRightSuffix S s hsTwo hs U).order i =
      b.order ⟨s + i.val, by omega⟩ := by
  rw [lemma714TypeIIRightSuffix, order_castLength]
  change U.right.bong.order ⟨i.val, by omega⟩ = _
  rw [U.right.order_eq]
  change (b.lemma714Tail S).order
      (U.right.sourceIndex ⟨i.val, by omega⟩) = _
  rw [b.lemma714Tail_order S]
  congr 1
  apply Fin.ext
  simp [BONG.SegmentWitness.sourceIndex]
  omega

/-- Every selected prefix order is at most the first order of `pi J`. -/
theorem lemma714TypeIISelectedPrefix_order_le_rescaledBinary_head
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hfirst : b.order ⟨0, by omega⟩ = R)
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (S : TwoBlockSplitWitness b.toBONG 2
      (lemma714TypeIIFrame_two_le_rank n))
    (hsFour : s = 2 ∨ 4 ≤ s)
    (U : (b.lemma714Tail S).toBONG.TwoBlockSplitWitness
      (s - 2) (by have := D.le_rank; omega)) :
    ∀ i : Fin (s - 2),
      (b.lemma714TypeIISelectedPrefix S s D.two_le D.le_rank U).order i ≤
        ((b.lemma714InitialBinary S).lemma714RescaledBinary).order 0 := by
  intro i
  rcases hsFour with hsTwo | hsFour
  · subst s
    exact Fin.elim0 i
  rw [b.lemma714TypeIISelectedPrefix_order S s D.two_le D.le_rank U,
    lemma714RescaledBinary_order]
  have hj0 : (b.lemma714InitialBinary S).order 0 = R := by
    calc
      (b.lemma714InitialBinary S).order 0 =
          b.order (S.left.sourceIndex 0) := S.left.order_eq 0
      _ = b.order 0 := by congr 1
      _ = R := hfirst
  rw [hj0]
  exact b.lemma714_selected_order_le_R_add_two R s (2 + i.val)
    D.toLemma714MinimalityData hsFour hthird (by omega) (by omega)

/-- The low endpoint of the selected prefix also lies below the second
order of `pi J`. -/
theorem lemma714TypeIISelectedPrefix_last_le_rescaledBinary_second
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (S : TwoBlockSplitWitness b.toBONG 2
      (lemma714TypeIIFrame_two_le_rank n))
    (hsFour : s = 2 ∨ 4 ≤ s)
    (U : (b.lemma714Tail S).toBONG.TwoBlockSplitWitness
      (s - 2) (by have := D.le_rank; omega)) :
    ∀ hpos : 0 < s - 2,
      (b.lemma714TypeIISelectedPrefix S s D.two_le D.le_rank U).order
          ⟨s - 2 - 1, by omega⟩ ≤
        ((b.lemma714InitialBinary S).lemma714RescaledBinary).order 1 := by
  intro hpos
  rcases hsFour with hsTwo | hsFour
  · omega
  rw [b.lemma714TypeIISelectedPrefix_order S s D.two_le D.le_rank U,
    lemma714RescaledBinary_order]
  have hlast := b.lemma714_selected_last_order R s
    D.toLemma714MinimalityData hsFour hthird
  have hindex :
      (⟨2 + (s - 2 - 1), by have := D.le_rank; omega⟩ : Fin (n + 3)) =
        ⟨s - 1, by have := D.le_rank; omega⟩ := by
    apply Fin.ext
    change 2 + (s - 2 - 1) = s - 1
    omega
  have hj1 : (b.lemma714InitialBinary S).order 1 =
      R - 2 * (ramificationIndex K : Int) := by
    calc
      (b.lemma714InitialBinary S).order 1 =
          b.order (S.left.sourceIndex 1) := S.left.order_eq 1
      _ = b.order 1 := by congr 1
      _ = R - 2 * (ramificationIndex K : Int) := hsecond
  rw [hindex, hlast, hj1]
  omega

/-- The uncast first good BONG in the application of Lemma 7.10.  Keeping
this intermediate object named makes its two literal vector blocks available
without transporting indices through the final arithmetic length equality. -/
noncomputable def lemma714TypeIILeftProductRaw
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hfirst : b.order ⟨0, by omega⟩ = R)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (S : TwoBlockSplitWitness b.toBONG 2
      (lemma714TypeIIFrame_two_le_rank n))
    (hsFour : s = 2 ∨ 4 ≤ s)
    (U : (b.lemma714Tail S).toBONG.TwoBlockSplitWitness
      (s - 2) (by have := D.le_rank; omega)) :
    GoodBONG
      (((q.restrict S.right.carrier S.right.nondegenerate).restrict
          U.left.carrier U.left.nondegenerate).orthogonalSum
        (q.restrict S.left.carrier S.left.nondegenerate))
      (Lattice.product U.left.lattice
        (Lattice.rescale (uniformizerUnit K) S.left.lattice))
      (2 + (s - 2)) := by
  let selected := b.lemma714TypeIISelectedPrefix S s D.two_le D.le_rank U
  let pj := (b.lemma714InitialBinary S).lemma714RescaledBinary
  exact selected.orthogonalProductRight_of_orderBounds pj
    (b.lemma714TypeIISelectedPrefix_order_le_rescaledBinary_head
      R s D hfirst hthird S hsFour U)
    (fun hpos _ =>
      b.lemma714TypeIISelectedPrefix_last_le_rescaledBinary_second
        R s D hsecond hthird S hsFour U hpos)

/-- The first good BONG in the application of Lemma 7.10:
`x_3,...,x_s, pi x_1,pi x_2`. -/
noncomputable def lemma714TypeIILeftProduct
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hfirst : b.order ⟨0, by omega⟩ = R)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (S : TwoBlockSplitWitness b.toBONG 2
      (lemma714TypeIIFrame_two_le_rank n))
    (hsFour : s = 2 ∨ 4 ≤ s)
    (U : (b.lemma714Tail S).toBONG.TwoBlockSplitWitness
      (s - 2) (by have := D.le_rank; omega)) :
    GoodBONG
      (((q.restrict S.right.carrier S.right.nondegenerate).restrict
          U.left.carrier U.left.nondegenerate).orthogonalSum
        (q.restrict S.left.carrier S.left.nondegenerate))
      (Lattice.product U.left.lattice
        (Lattice.rescale (uniformizerUnit K) S.left.lattice)) s :=
  (b.lemma714TypeIILeftProductRaw R s D hfirst hsecond hthird S hsFour U).castLength
    (by omega)

/-- The selected vectors occur literally at the beginning of the left
Lemma-7.10 BONG. -/
@[simp]
theorem lemma714TypeIILeftProduct_ambientVector_selected
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hfirst : b.order ⟨0, by omega⟩ = R)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (S : TwoBlockSplitWitness b.toBONG 2
      (lemma714TypeIIFrame_two_le_rank n))
    (hsFour : s = 2 ∨ 4 ≤ s)
    (U : (b.lemma714Tail S).toBONG.TwoBlockSplitWitness
      (s - 2) (by have := D.le_rank; omega))
    (i : Fin (s - 2)) :
    (b.lemma714TypeIILeftProduct R s D hfirst hsecond hthird S hsFour U).toBONG.ambientVector
        ⟨i.val, by omega⟩ =
      ((b.lemma714TypeIISelectedPrefix S s D.two_le D.le_rank U).toBONG.ambientVector i,
        0) := by
  rw [lemma714TypeIILeftProduct, lemma714TypeII_ambientVector_castLength]
  change
    (b.lemma714TypeIILeftProductRaw R s D hfirst hsecond hthird S hsFour U).toBONG.ambientVector
        (BONG.orthogonalProductLeftIndex 2 i) = _
  unfold lemma714TypeIILeftProductRaw
  exact BONG.ambientVector_orthogonalProductRight_left _ _ _ i

/-- The selected-prefix orders are unchanged in the left Lemma-7.10
product. -/
@[simp]
theorem lemma714TypeIILeftProduct_order_selected
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hfirst : b.order ⟨0, by omega⟩ = R)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (S : TwoBlockSplitWitness b.toBONG 2
      (lemma714TypeIIFrame_two_le_rank n))
    (hsFour : s = 2 ∨ 4 ≤ s)
    (U : (b.lemma714Tail S).toBONG.TwoBlockSplitWitness
      (s - 2) (by have := D.le_rank; omega))
    (i : Fin (s - 2)) :
    (b.lemma714TypeIILeftProduct R s D hfirst hsecond hthird S hsFour U).order
        ⟨i.val, by omega⟩ =
      (b.lemma714TypeIISelectedPrefix S s D.two_le D.le_rank U).order i := by
  rw [lemma714TypeIILeftProduct, order_castLength]
  change
    (b.lemma714TypeIILeftProductRaw R s D hfirst hsecond hthird S hsFour U).order
        (BONG.orthogonalProductLeftIndex 2 i) = _
  unfold lemma714TypeIILeftProductRaw
  exact BONG.order_orthogonalProductRight_left _ _ _ i

/-- The final two vectors of the left Lemma-7.10 BONG are literally the two
vectors of `pi J`. -/
@[simp]
theorem lemma714TypeIILeftProduct_ambientVector_binary
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hfirst : b.order ⟨0, by omega⟩ = R)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (S : TwoBlockSplitWitness b.toBONG 2
      (lemma714TypeIIFrame_two_le_rank n))
    (hsFour : s = 2 ∨ 4 ≤ s)
    (U : (b.lemma714Tail S).toBONG.TwoBlockSplitWitness
      (s - 2) (by have := D.le_rank; omega))
    (j : Fin 2) :
    (b.lemma714TypeIILeftProduct R s D hfirst hsecond hthird S hsFour U).toBONG.ambientVector
        ⟨s - 2 + j.val, by omega⟩ =
      (0, ((b.lemma714InitialBinary S).lemma714RescaledBinary).toBONG.ambientVector j) := by
  rw [lemma714TypeIILeftProduct, lemma714TypeII_ambientVector_castLength]
  change
    (b.lemma714TypeIILeftProductRaw R s D hfirst hsecond hthird S hsFour U).toBONG.ambientVector
        (BONG.orthogonalProductRightIndex (s - 2) j) = _
  unfold lemma714TypeIILeftProductRaw
  exact BONG.ambientVector_orthogonalProductRight_right _ _ _ j

/-- Reassociate the concrete model `tail perp pi J` into the two factors
used in Lemma 7.10:

`([x_3,...,x_s] perp pi J) perp [x_(s+1),...,x_N]`.
-/
noncomputable def lemma714TypeIIFrameIsometry
    (b : GoodBONG q L (n + 3))
    (S : TwoBlockSplitWitness b.toBONG 2
      (lemma714TypeIIFrame_two_le_rank n))
    (s : Nat) (hsTwo : 2 ≤ s) (hsBound : s ≤ n + 3)
    (U : (b.lemma714Tail S).toBONG.TwoBlockSplitWitness
      (s - 2) (by omega)) :
    Lattice.Isometry
      ((q.restrict S.right.carrier S.right.nondegenerate).orthogonalSum
        (q.restrict S.left.carrier S.left.nondegenerate))
      ((((q.restrict S.right.carrier S.right.nondegenerate).restrict
          U.left.carrier U.left.nondegenerate).orthogonalSum
        (q.restrict S.left.carrier S.left.nondegenerate)).orthogonalSum
        ((q.restrict S.right.carrier S.right.nondegenerate).restrict
          U.right.carrier U.right.nondegenerate))
      (Lattice.product S.right.lattice
        (Lattice.rescale (uniformizerUnit K) S.left.lattice))
      (Lattice.product
        (Lattice.product U.left.lattice
          (Lattice.rescale (uniformizerUnit K) S.left.lattice))
        U.right.lattice) := by
  let tailSplit : Lattice.Isometry
      (q.restrict S.right.carrier S.right.nondegenerate)
      (((q.restrict S.right.carrier S.right.nondegenerate).restrict
          U.left.carrier U.left.nondegenerate).orthogonalSum
        ((q.restrict S.right.carrier S.right.nondegenerate).restrict
          U.right.carrier U.right.nondegenerate))
      S.right.lattice (Lattice.product U.left.lattice U.right.lattice) :=
    U.toProductLatticeIsometry.symm
  let binaryRefl := Lattice.Isometry.refl
    (q.restrict S.left.carrier S.left.nondegenerate)
    (Lattice.rescale (uniformizerUnit K) S.left.lattice)
  let splitWithBinary := tailSplit.orthogonalProductBasic binaryRefl
  let reassociate := Lattice.orthogonalProductAssoc
    (q := (q.restrict S.right.carrier S.right.nondegenerate).restrict
      U.left.carrier U.left.nondegenerate)
    (r := (q.restrict S.right.carrier S.right.nondegenerate).restrict
      U.right.carrier U.right.nondegenerate)
    (s := q.restrict S.left.carrier S.left.nondegenerate)
    (L := U.left.lattice) (M := U.right.lattice)
    (N := Lattice.rescale (uniformizerUnit K) S.left.lattice)
  let swapInside :=
    (Lattice.Isometry.refl
      ((q.restrict S.right.carrier S.right.nondegenerate).restrict
        U.left.carrier U.left.nondegenerate) U.left.lattice).orthogonalProductBasic
      (Lattice.orthogonalProductSwap
        (q := (q.restrict S.right.carrier S.right.nondegenerate).restrict
          U.right.carrier U.right.nondegenerate)
        (r := q.restrict S.left.carrier S.left.nondegenerate)
        (L := U.right.lattice)
        (M := Lattice.rescale (uniformizerUnit K) S.left.lattice))
  let finish := (Lattice.orthogonalProductAssoc
    (q := (q.restrict S.right.carrier S.right.nondegenerate).restrict
      U.left.carrier U.left.nondegenerate)
    (r := q.restrict S.left.carrier S.left.nondegenerate)
    (s := (q.restrict S.right.carrier S.right.nondegenerate).restrict
      U.right.carrier U.right.nondegenerate)
    (L := U.left.lattice)
    (M := Lattice.rescale (uniformizerUnit K) S.left.lattice)
    (N := U.right.lattice)).symm
  exact splitWithBinary.trans
    (reassociate.trans (swapInside.trans finish))

@[simp]
theorem lemma714TypeIIFrameIsometry_apply
    (b : GoodBONG q L (n + 3))
    (S : TwoBlockSplitWitness b.toBONG 2
      (lemma714TypeIIFrame_two_le_rank n))
    (s : Nat) (hsTwo : 2 ≤ s) (hsBound : s ≤ n + 3)
    (U : (b.lemma714Tail S).toBONG.TwoBlockSplitWitness
      (s - 2) (by omega))
    (z : S.right.carrier × S.left.carrier) :
    (b.lemma714TypeIIFrameIsometry S s hsTwo hsBound U).toLinearEquiv z =
      (((U.toProductLatticeIsometry.symm.toLinearEquiv z.1).1, z.2),
        (U.toProductLatticeIsometry.symm.toLinearEquiv z.1).2) := by
  simp [lemma714TypeIIFrameIsometry, Lattice.Isometry.trans,
    Lattice.orthogonalProductAssoc, Lattice.Isometry.refl,
    Lattice.Isometry.symm]
  rfl

end BONG.GoodBONG

end Bong
