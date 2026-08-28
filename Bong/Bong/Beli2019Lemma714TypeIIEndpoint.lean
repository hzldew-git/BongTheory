/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714TypeIIReframing
import Bong.Bong.Beli2019Lemma710SegmentDual

/-!
# Beli (2019), Lemma 7.14(ii): the Type-II Lemma-7.10 endpoint

This file puts the reframed Type-II candidate into the exact arithmetical
shape consumed by Lemma 7.10.  The unchanged prefix has length `s - 2`; the
stopping segment consists of the exceptional ternary block followed by
`x_(s+2),...,x_N`.

The final datum is the concrete segment-product isometry certificate.  Once
that certificate is supplied, Lemma 7.10 proves the desired lattice identity;
the identity itself is never assumed.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

private theorem lemma714TypeIIEndpoint_two_le_rank (n : Nat) :
    2 ≤ n + 3 := by
  omega

private theorem lemma714TypeIIEndpoint_ambientVector_castLength
    {m length : Nat} {Q : QuadraticSpace K V} {M : Lattice K V}
    (a : GoodBONG Q M m) (h : m = length) (i : Fin length) :
    (a.castLength h).toBONG.ambientVector i =
      a.toBONG.ambientVector ⟨i.val, by omega⟩ := by
  subst length
  rfl

/-- The `baseTail` parameter in the Lemma-7.10 API. -/
def lemma714TypeIIBaseTail (n s : Nat) : Nat :=
  n + 4 - s

/-- The full stopping-segment length: three exceptional vectors followed by
the retained suffix. -/
def lemma714TypeIIBaseLength (n s : Nat) : Nat :=
  lemma714TypeIIBaseTail n s + 1

theorem lemma714TypeIIBaseLength_add_prefix
    (n s : Nat) (hsFour : s = 2 ∨ 4 ≤ s) (hsCurrent : s < n + 3) :
    lemma714TypeIIBaseLength n s + (s - 2) = n + 3 := by
  rcases hsFour with rfl | hsFour
  · unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
    omega
  unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
  omega

theorem lemma714TypeIIRightLength_eq
    (n s : Nat) (hsCurrent : s < n + 3) :
    (n + 2 - s) + 1 = n + 3 - s := by
  omega

section Endpoint

variable [DyadicDiscriminantClassLaws K]
variable (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
variable (D : Lemma714StoppingData b R s)
variable (hfirst : b.order ⟨0, by omega⟩ = R)
variable (hsecond : b.order ⟨1, by omega⟩ =
  R - 2 * (ramificationIndex K : Int))
variable (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
variable (hsCurrent : s < n + 3)
variable (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
variable (S : BONG.TwoBlockSplitWitness b.toBONG 2
  (lemma714TypeIIEndpoint_two_le_rank n))
variable (hsFour : s = 2 ∨ 4 ≤ s)
variable (U : (b.lemma714Tail S).toBONG.TwoBlockSplitWitness
  (s - 2) (by have := D.le_rank; omega))
variable (block : GoodBONG
  ((q.restrict S.left.carrier S.left.nondegenerate).orthogonalSum
    ((q.restrict S.right.carrier S.right.nondegenerate).restrict
      (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).carrier
      (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).nondegenerate))
  (Lattice.product
    (Lattice.rescale (uniformizerUnit K) S.left.lattice)
    (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).lattice) 3)
variable {N : Lattice K (S.right.carrier × S.left.carrier)}
variable (target : GoodBONG
  ((q.restrict S.right.carrier S.right.nondegenerate).orthogonalSum
    (q.restrict S.left.carrier S.left.nondegenerate)) N (n + 3))
variable (htargetVectors : ∀ i, target.toBONG.ambientVector i =
  lemma714TypeIITargetVector b S s D.two_le hsCurrent block i)

/-- The right factor with its length normalized to the `rightLength + 1`
shape expected by Lemma 7.10. -/
noncomputable def lemma714TypeIIRightForLemma710 :
    GoodBONG
      ((q.restrict S.right.carrier S.right.nondegenerate).restrict
        U.right.carrier U.right.nondegenerate)
      U.right.lattice ((n + 2 - s) + 1) :=
  (b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).castLength
    (lemma714TypeIIRightLength_eq n s hsCurrent).symm

/-- The reframed target with its length displayed as
`baseLength + prefixLength`. -/
noncomputable def lemma714TypeIITargetForLemma710 :
    GoodBONG
      ((((q.restrict S.right.carrier S.right.nondegenerate).restrict
          U.left.carrier U.left.nondegenerate).orthogonalSum
        (q.restrict S.left.carrier S.left.nondegenerate)).orthogonalSum
        ((q.restrict S.right.carrier S.right.nondegenerate).restrict
          U.right.carrier U.right.nondegenerate))
      (Lattice.map
        (b.lemma714TypeIIFrameIsometry S s D.two_le D.le_rank U).toLinearEquiv N)
      (lemma714TypeIIBaseLength n s + (s - 2)) :=
  (b.lemma714TypeIIReframedTarget S s D.two_le D.le_rank U target).castLength
    (by
      symm
      exact lemma714TypeIIBaseLength_add_prefix n s hsFour hsCurrent)

include block htargetVectors
/-- Before the harmless length cast, the exact unchanged-prefix equation is
already the left-vector hypothesis of Lemma 7.10. -/
@[simp]
theorem lemma714TypeIIReframedTarget_leftPrefixVectors
    (i : Fin (s - 2)) :
    (b.lemma714TypeIIReframedTarget S s D.two_le D.le_rank U target).toBONG.ambientVector
        ⟨i.val, by omega⟩ =
      ((b.lemma714TypeIILeftProduct R s D hfirst hsecond hthird S hsFour U).toBONG.ambientVector
          ⟨i.val, by omega⟩, 0) := by
  rw [b.lemma714TypeIIReframedTarget_ambientVector_prefix S s D.two_le
      hsCurrent U block target htargetVectors i,
    b.lemma714TypeIILeftProduct_ambientVector_selected R s D hfirst
      hsecond hthird S hsFour U i]

/-- The unchanged-prefix formula in the exact dependent index convention of
`TargetPrefixSegmentProductIsometryData`. -/
theorem lemma714TypeIITargetForLemma710_leftVectors
    (i : Fin (s - 2)) :
    (b.lemma714TypeIITargetForLemma710 R s D hsCurrent S hsFour U target).toBONG.ambientVector
        (BONG.orthogonalProductLeftIndex (lemma714TypeIIBaseLength n s) i) =
      ((b.lemma714TypeIILeftProduct R s D hfirst hsecond hthird S hsFour U).toBONG.ambientVector
          (BONG.OrthogonalPrefixRawSeed.prefixSourceIndex (by omega) i), 0) := by
  unfold lemma714TypeIITargetForLemma710
  rw [lemma714TypeIIEndpoint_ambientVector_castLength]
  have htargetBound :
      (BONG.orthogonalProductLeftIndex
          (lemma714TypeIIBaseLength n s) i).val < n + 3 := by
    rw [← lemma714TypeIIBaseLength_add_prefix n s hsFour hsCurrent]
    exact (BONG.orthogonalProductLeftIndex
      (lemma714TypeIIBaseLength n s) i).isLt
  have htargetIndex :
      (⟨(BONG.orthogonalProductLeftIndex (lemma714TypeIIBaseLength n s) i).val,
          htargetBound⟩ : Fin (n + 3)) = ⟨i.val, by omega⟩ := by
    apply Fin.ext
    rfl
  have hsourceIndex :
      BONG.OrthogonalPrefixRawSeed.prefixSourceIndex (by omega) i =
        (⟨i.val, by omega⟩ : Fin s) := by
    apply Fin.ext
    rfl
  rw [htargetIndex, hsourceIndex]
  exact b.lemma714TypeIIReframedTarget_leftPrefixVectors R s D hfirst
    hsecond hthird hsCurrent S hsFour U block target htargetVectors i

/-- The first exceptional vector after the length normalization used by
Lemma 7.10. -/
@[simp]
theorem lemma714TypeIITargetForLemma710_block_zero :
    (b.lemma714TypeIITargetForLemma710 R s D hsCurrent S hsFour U target).toBONG.ambientVector
        ⟨s - 2, by
          rw [lemma714TypeIIBaseLength_add_prefix n s hsFour hsCurrent]
          omega⟩ =
      ((0, (block.toBONG.ambientVector 0).1),
        b.lemma714TypeIILineToRight S s D.two_le hsCurrent U
          (block.toBONG.ambientVector 0).2) := by
  unfold lemma714TypeIITargetForLemma710
  rw [lemma714TypeIIEndpoint_ambientVector_castLength]
  simpa using b.lemma714TypeIIReframedTarget_ambientVector_block_zero
    S s D.two_le hsCurrent U block target htargetVectors

/-- The middle exceptional vector after the length normalization used by
Lemma 7.10. -/
@[simp]
theorem lemma714TypeIITargetForLemma710_block_one :
    (b.lemma714TypeIITargetForLemma710 R s D hsCurrent S hsFour U target).toBONG.ambientVector
        ⟨s - 1, by
          rw [lemma714TypeIIBaseLength_add_prefix n s hsFour hsCurrent]
          omega⟩ =
      ((0, (block.toBONG.ambientVector 1).1),
        b.lemma714TypeIILineToRight S s D.two_le hsCurrent U
          (block.toBONG.ambientVector 1).2) := by
  unfold lemma714TypeIITargetForLemma710
  rw [lemma714TypeIIEndpoint_ambientVector_castLength]
  simpa using b.lemma714TypeIIReframedTarget_ambientVector_block_one
    S s D.two_le hsCurrent U block target htargetVectors

/-- The last exceptional vector after the length normalization used by
Lemma 7.10. -/
@[simp]
theorem lemma714TypeIITargetForLemma710_block_two :
    (b.lemma714TypeIITargetForLemma710 R s D hsCurrent S hsFour U target).toBONG.ambientVector
        ⟨s, by
          rw [lemma714TypeIIBaseLength_add_prefix n s hsFour hsCurrent]
          omega⟩ =
      ((0, (block.toBONG.ambientVector 2).1),
        b.lemma714TypeIILineToRight S s D.two_le hsCurrent U
          (block.toBONG.ambientVector 2).2) := by
  unfold lemma714TypeIITargetForLemma710
  rw [lemma714TypeIIEndpoint_ambientVector_castLength]
  simpa using b.lemma714TypeIIReframedTarget_ambientVector_block_two
    S s D.two_le hsCurrent U block target htargetVectors

/-- Every vector following the exceptional ternary block remains the
corresponding non-head vector of the right Lemma-7.10 factor. -/
@[simp]
theorem lemma714TypeIITargetForLemma710_suffix
    (j : Fin (n + 2 - s)) :
    (b.lemma714TypeIITargetForLemma710 R s D hsCurrent S hsFour U target).toBONG.ambientVector
        ⟨s + 1 + j.val, by
          rw [lemma714TypeIIBaseLength_add_prefix n s hsFour hsCurrent]
          omega⟩ =
      ((0, 0),
        (b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).toBONG.ambientVector
          ⟨j.val + 1, by omega⟩) := by
  unfold lemma714TypeIITargetForLemma710
  rw [lemma714TypeIIEndpoint_ambientVector_castLength]
  simpa using b.lemma714TypeIIReframedTarget_ambientVector_suffix
    S s D.two_le hsCurrent U block target htargetVectors j

omit block htargetVectors

include hcurrent
/-- The order comparison at the left endpoint of the replacement interval. -/
theorem lemma714TypeIILeftEndpointOrder :
    ∀ hpos : 0 < s - 2,
      (b.lemma714TypeIILeftProduct R s D hfirst hsecond hthird S hsFour U).order
          ⟨s - 2 - 1, by omega⟩ ≤
        (b.lemma714TypeIIRightForLemma710 R s D hsCurrent S U).order 0 := by
  intro hpos
  rcases hsFour with hsTwo | hsFour
  · subst s
    omega
  have hlast := b.lemma714_selected_last_order R s
    D.toLemma714MinimalityData hsFour hthird
  calc
    (b.lemma714TypeIILeftProduct R s D hfirst hsecond hthird S (Or.inr hsFour) U).order
          ⟨s - 2 - 1, by omega⟩ =
        (b.lemma714TypeIISelectedPrefix S s D.two_le D.le_rank U).order
          ⟨s - 2 - 1, by omega⟩ :=
      b.lemma714TypeIILeftProduct_order_selected R s D hfirst hsecond hthird
        S (Or.inr hsFour) U ⟨s - 2 - 1, by omega⟩
    _ = b.order ⟨2 + (s - 2 - 1), by omega⟩ :=
      b.lemma714TypeIISelectedPrefix_order S s D.two_le D.le_rank U
        ⟨s - 2 - 1, by omega⟩
    _ = b.order ⟨s - 1, by omega⟩ := by
      apply congrArg b.order
      apply Fin.ext
      change 2 + (s - 2 - 1) = s - 1
      omega
    _ = R - 2 * (ramificationIndex K : Int) + 1 := hlast
    _ ≤ R + 1 := by
      have hePos := ramificationIndex_pos (K := K)
      omega
    _ = b.order ⟨s, hsCurrent⟩ := hcurrent.symm
    _ = (b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).order
        ⟨0, by omega⟩ := by
      symm
      simpa using
        (b.lemma714TypeIIRightSuffix_order S s D.two_le hsCurrent U
          (⟨0, by omega⟩ : Fin (n + 3 - s)))
    _ = (b.lemma714TypeIIRightForLemma710 R s D hsCurrent S U).order 0 := by
      unfold lemma714TypeIIRightForLemma710
      rw [GoodBONG.order_castLength]
      apply congrArg
      apply Fin.ext
      rfl

include block htargetVectors
/-- The sole remaining endpoint input in the Type-II use of Lemma 7.10.  Its
fields are the concrete isometry from the extracted stopping segment to the
orthogonal product and the corresponding equations on BONG vectors. -/
abbrev Lemma714TypeIIEndpointData : Type v :=
  BONG.OrthogonalPrefixRawSeed.TargetPrefixSegmentProductIsometryData
    (M := U.right.lattice)
    (b.lemma714TypeIILeftProduct R s D hfirst hsecond hthird S hsFour U).toBONG
    (by omega)
    (b.lemma714TypeIITargetForLemma710 R s D hsCurrent S hsFour U target).toBONG
    (b.lemma714TypeIITargetForLemma710_leftVectors R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors)

/-- The paper-facing form of the remaining endpoint input: an original
consecutive replacement at the unique stopping node, together with the three
reverse-dual identifications. -/
abbrev Lemma714TypeIIStopDualReplacementData : Type (max (v + 1) u) :=
  let source :=
    (b.lemma714TypeIILeftProduct R s D hfirst hsecond hthird S hsFour U).toBONG
  let reframedTarget :=
    (b.lemma714TypeIITargetForLemma710 R s D hsCurrent S hsFour U target).toBONG
  let leftVectors :=
    b.lemma714TypeIITargetForLemma710_leftVectors R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors
  let model := BONG.OrthogonalPrefixRawSeed.extractTargetPrefixSegment
    (M := U.right.lattice) source (by omega) reframedTarget leftVectors
  model.extraction.seed.StopDualReplacementData model.segment

/-- Dualizing the original consecutive replacement produces exactly the
endpoint certificate consumed by `lemma714TypeIIReframedTarget_lattice_eq`. -/
noncomputable def Lemma714TypeIIEndpointData.ofDualReplacement
    (E : Lemma714TypeIIStopDualReplacementData (b := b) (R := R) (s := s)
      (D := D) (hfirst := hfirst) (hsecond := hsecond) (hthird := hthird)
      (hsCurrent := hsCurrent) (S := S) (hsFour := hsFour) (U := U)
      (block := block) (target := target) (htargetVectors := htargetVectors)) :
    Lemma714TypeIIEndpointData (b := b) (R := R) (s := s) (D := D)
      (hfirst := hfirst) (hsecond := hsecond) (hthird := hthird)
      (hsCurrent := hsCurrent) (S := S) (hsFour := hsFour) (U := U)
      (block := block) (target := target)
      (htargetVectors := htargetVectors) :=
  BONG.OrthogonalPrefixRawSeed.targetPrefixSegmentProductIsometryDataOfDualReplacement
      (M := U.right.lattice)
      (b.lemma714TypeIILeftProduct R s D hfirst hsecond hthird S hsFour U).toBONG
      (by omega)
      (b.lemma714TypeIITargetForLemma710 R s D hsCurrent S hsFour U target).toBONG
      (b.lemma714TypeIITargetForLemma710_leftVectors R s D hfirst hsecond hthird
        hsCurrent S hsFour U block target htargetVectors)
      E

/-- Once the concrete stopping-segment isometry data is supplied, Lemma 7.10
proves the Type-II lattice identity in the reframed coordinates. -/
theorem lemma714TypeIIReframedTarget_lattice_eq
    (E : Lemma714TypeIIEndpointData (b := b) (R := R) (s := s) (D := D)
      (hfirst := hfirst) (hsecond := hsecond) (hthird := hthird)
      (hsCurrent := hsCurrent) (S := S) (hsFour := hsFour) (U := U)
      (block := block) (target := target) (htargetVectors := htargetVectors)) :
    Lattice.map
        (b.lemma714TypeIIFrameIsometry S s D.two_le D.le_rank U).toLinearEquiv N =
      Lattice.product
        (Lattice.product U.left.lattice
          (Lattice.rescale (uniformizerUnit K) S.left.lattice))
        U.right.lattice := by
  let left :=
    b.lemma714TypeIILeftProduct R s D hfirst hsecond hthird S hsFour U
  exact
    left.beli2019Lemma710General_of_targetPrefixSegmentProductIsometryData
        (baseTail := lemma714TypeIIBaseTail n s)
        (steps := s - 2)
        (rightLength := n + 2 - s)
        (by omega)
        (b.lemma714TypeIIRightForLemma710 R s D hsCurrent S U).toBONG
        (b.lemma714TypeIITargetForLemma710 R s D hsCurrent S hsFour U target)
        (b.lemma714TypeIITargetForLemma710_leftVectors R s D hfirst hsecond
          hthird hsCurrent S hsFour U block target htargetVectors)
        E
        (b.lemma714TypeIILeftEndpointOrder R s D hfirst hsecond hthird
          hsCurrent hcurrent S hsFour U)

/-- Paper-facing corollary: the original consecutive replacement and its
reverse-dual identifications suffice for the Type-II lattice identity. -/
theorem lemma714TypeIIReframedTarget_lattice_eq_ofDualReplacement
    (E : Lemma714TypeIIStopDualReplacementData (b := b) (R := R) (s := s)
      (D := D) (hfirst := hfirst) (hsecond := hsecond) (hthird := hthird)
      (hsCurrent := hsCurrent) (S := S) (hsFour := hsFour) (U := U)
      (block := block) (target := target) (htargetVectors := htargetVectors)) :
    Lattice.map
        (b.lemma714TypeIIFrameIsometry S s D.two_le D.le_rank U).toLinearEquiv N =
      Lattice.product
        (Lattice.product U.left.lattice
          (Lattice.rescale (uniformizerUnit K) S.left.lattice))
        U.right.lattice := by
  apply lemma714TypeIIReframedTarget_lattice_eq
    (b := b) (R := R) (s := s) (D := D)
    (hfirst := hfirst) (hsecond := hsecond) (hthird := hthird)
    (hsCurrent := hsCurrent) (hcurrent := hcurrent) (S := S)
    (hsFour := hsFour) (U := U) (block := block) (target := target)
    (htargetVectors := htargetVectors)
  exact Lemma714TypeIIEndpointData.ofDualReplacement
    (b := b) (R := R) (s := s) (D := D)
    (hfirst := hfirst) (hsecond := hsecond) (hthird := hthird)
    (hsCurrent := hsCurrent) (S := S) (hsFour := hsFour) (U := U)
    (block := block) (target := target) (htargetVectors := htargetVectors) E

end Endpoint

end BONG.GoodBONG

end Bong
