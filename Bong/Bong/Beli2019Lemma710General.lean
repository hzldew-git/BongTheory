/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma710Swap

/-!
# Beli (2019), Lemma 7.10: the general two-endpoint assembly

For an internal replacement interval, the paper first proves the equality of
the replaced suffix by applying the right-end argument after reverse duality.
It then adjoins the unchanged original prefix by a second right-end argument.

`OrthogonalPrefixRawSeed` separates these two stages.  Its stopping BONG may
live on an as-yet unidentified lattice.  `StopLatticeEq` is precisely the
suffix equality supplied by the dual argument; once that equality is proved,
`toSeed` turns the raw certificate into the concrete prefix seed used by the
second endpoint argument.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v w

/-- A prefix seed whose stopping BONG has not yet been identified with the
orthogonal product lattice.  The general case of Lemma 7.10 obtains exactly
this missing equality from the reverse-dual right-end argument. -/
inductive OrthogonalPrefixRawSeed
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {W : Type w} [AddCommGroup W] [Module K W]
    (r : QuadraticSpace K W) (M : Lattice K W) (baseLength : Nat) :
    {V : Type v} → [AddCommGroup V] → [Module K V] →
    {q : QuadraticSpace K V} → {L : Lattice K V} →
    {n steps : Nat} → BONG V q L n →
      Type (max (u + 1) (v + 1) (w + 1))
  | stop
      {V : Type v} [AddCommGroup V] [Module K V]
      {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
      {N : Lattice K (V × W)}
      (source : BONG V q L n)
      (base : BONG (V × W) (q.orthogonalSum r) N baseLength) :
      OrthogonalPrefixRawSeed r M baseLength (steps := 0) source
  | cons
      {V : Type v} [AddCommGroup V] [Module K V]
      {q : QuadraticSpace K V} {L : Lattice K V} {n steps : Nat}
      {x : V}
      (generator : Lattice.IsNormGenerator q L x)
      (anisotropic : q.IsAnisotropic x)
      (tail : BONG (q.vectorOrthogonal x)
        (q.orthogonalSpace x anisotropic)
        (L.projectedLattice q x anisotropic) n)
      (tailSeed : OrthogonalPrefixRawSeed r M baseLength
        (steps := steps) tail) :
      OrthogonalPrefixRawSeed r M baseLength (steps := steps + 1)
        (BONG.cons x generator anisotropic tail)

namespace OrthogonalPrefixRawSeed

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  {n steps baseLength : Nat} {b : BONG V q L n}

/-- The one missing lattice identity at the stopping point. -/
def StopLatticeEq
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b) :
    Prop := by
  induction S with
  | @stop V _ _ q L n N source base =>
      exact N = Lattice.product L M
  | cons _ _ _ _ tailEq =>
      exact tailEq

/-- A raw seed never stores more source heads than its source BONG has. -/
theorem steps_le_length
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b) :
    steps ≤ n := by
  induction S with
  | stop => simp
  | cons _ _ _ _ ih => omega

/-- The original BONG index represented by an unchanged prefix entry. -/
def sourceIndex
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (i : Fin steps) : Fin n :=
  ⟨i.val, lt_of_lt_of_le i.isLt S.steps_le_length⟩

@[simp]
theorem sourceIndex_val
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (i : Fin steps) : (S.sourceIndex i).val = i.val :=
  rfl

/-- The stopping vectors transported through the still-unverified prefix
chain.  They are independent of the eventual proof of `StopLatticeEq`. -/
noncomputable def baseAmbientVector
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b) :
    Fin baseLength → V × W := by
  induction S with
  | stop _ base =>
      exact base.ambientVector
  | @cons V _ _ q L n steps x generator anisotropic tail
      tailSeed tailBase =>
      exact fun i =>
        (((Lattice.projectedOrthogonalProductIsometry
            (q := q) (r := r) (L := L) (M := M)
            anisotropic).symm.toLinearEquiv (tailBase i) :
              (q.orthogonalSum r).vectorOrthogonal (x, 0)) : V × W)

/-- Once the reverse-dual stage proves the stopping identity, the raw
certificate becomes the concrete seed required by the original endpoint
argument. -/
noncomputable def toSeed
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (hstop : S.StopLatticeEq) :
    OrthogonalPrefixSeed r M baseLength (steps := steps) b := by
  induction S with
  | stop source base =>
      exact .stop source (base.castLattice hstop)
  | cons generator anisotropic tail tailSeed ih =>
      exact .cons generator anisotropic tail (ih hstop)

/-- Realizing a raw seed does not alter its source indices. -/
@[simp]
theorem sourceIndex_toSeed
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (hstop : S.StopLatticeEq) (i : Fin steps) :
    (S.toSeed hstop).sourceIndex i = S.sourceIndex i := by
  apply Fin.ext
  rfl

/-- Realizing a raw seed does not alter its transported stopping vectors. -/
@[simp]
theorem baseAmbientVector_toSeed
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (hstop : S.StopLatticeEq) (j : Fin baseLength) :
    (S.toSeed hstop).baseAmbientVector j = S.baseAmbientVector j := by
  induction S with
  | stop source base =>
      cases hstop
      rfl
  | @cons V _ _ q L n steps x generator anisotropic tail
      tailSeed ih =>
      have htransport := congrArg
        (fun z =>
          (((Lattice.projectedOrthogonalProductIsometry
              (q := q) (r := r) (L := L) (M := M)
              anisotropic).symm.toLinearEquiv z :
                (q.orthogonalSum r).vectorOrthogonal (x, 0)) : V × W))
        (ih hstop)
      simpa only [toSeed, OrthogonalPrefixSeed.baseAmbientVector,
        baseAmbientVector] using htransport

/-- A proof-producing certificate for the reverse-dual endpoint at the
stopping node of a raw seed.  Recursive `cons` nodes merely carry the same
certificate down to the stopping lattice.  The `stop` node records the
factor-reversed endpoint data on the integral dual of the swapped stopping
lattice. -/
inductive DualEndpointCertificate
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {W : Type w} [AddCommGroup W] [Module K W]
    (r : QuadraticSpace K W) (M : Lattice K W) :
    {V : Type v} → [AddCommGroup V] → [Module K V] →
    {q : QuadraticSpace K V} → {L : Lattice K V} →
    {n steps baseLength : Nat} → {b : BONG V q L n} →
    OrthogonalPrefixRawSeed r M baseLength (steps := steps) b →
      Type (max (u + 1) (v + 1) (w + 1))
  | stop
      {V : Type v} [AddCommGroup V] [Module K V]
      {q : QuadraticSpace K V} {L : Lattice K V}
      {sourceLength dualPrefixLength dualRightLength : Nat}
      {baseTail dualSteps : Nat} {N : Lattice K (V × W)}
      (source : BONG V q L sourceLength)
      (base : BONG (V × W) (q.orthogonalSum r) N
        ((baseTail + 1) + dualSteps))
      (rightFactorDual : GoodBONG r (Lattice.dualLattice r M)
        dualPrefixLength)
      (hsteps : dualSteps ≤ dualPrefixLength)
      (leftFactorDual : BONG V q (Lattice.dualLattice q L)
        (dualRightLength + 1))
      (seed : OrthogonalPrefixSeed q (Lattice.dualLattice q L)
        (baseTail + 1) (steps := dualSteps) rightFactorDual.toBONG)
      (hlast : ∀ hpos : 0 < dualSteps,
        rightFactorDual.order ⟨dualSteps - 1, by omega⟩ ≤
          leftFactorDual.order 0)
      (targetDual : GoodBONG (r.orthogonalSum q)
        (Lattice.dualLattice (r.orthogonalSum q)
          (Lattice.swapLattice N))
        ((baseTail + 1) + dualSteps))
      (leftVectors : ∀ i : Fin dualSteps,
        targetDual.toBONG.ambientVector
            (orthogonalProductLeftIndex (baseTail + 1) i) =
          (rightFactorDual.toBONG.ambientVector
            (seed.sourceIndex i), 0))
      (rightVectors : ∀ j : Fin (baseTail + 1),
        targetDual.toBONG.ambientVector
            (orthogonalProductRightIndex dualSteps j) =
          seed.baseAmbientVector j) :
      DualEndpointCertificate r M
        (OrthogonalPrefixRawSeed.stop (M := M) source base)
  | cons
      {V : Type v} [AddCommGroup V] [Module K V]
      {q : QuadraticSpace K V} {L : Lattice K V}
      {n steps baseLength : Nat} {x : V}
      (generator : Lattice.IsNormGenerator q L x)
      (anisotropic : q.IsAnisotropic x)
      (tail : BONG (q.vectorOrthogonal x)
        (q.orthogonalSpace x anisotropic)
        (L.projectedLattice q x anisotropic) n)
      (tailSeed : OrthogonalPrefixRawSeed r M baseLength
        (steps := steps) tail)
      (tailCertificate : DualEndpointCertificate r M tailSeed) :
      DualEndpointCertificate r M
        (OrthogonalPrefixRawSeed.cons generator anisotropic tail tailSeed)

end OrthogonalPrefixRawSeed

namespace GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  {n rightLength : Nat}

/-- The reverse-dual endpoint argument with the factor order occurring in
the paper.  The unchanged suffix of the original right factor becomes the
left prefix after reversing; the explicit swap transports its conclusion
back to `V × W`. -/
theorem beli2019Lemma710SwappedDualRightEnd_all_of_good
    {dualPrefixLength dualRightLength baseTail s : Nat}
    {N : Lattice K (V × W)}
    (rightFactorDual : GoodBONG r (Lattice.dualLattice r M)
      dualPrefixLength)
    (hs : 1 ≤ s) (hsRank : s - 1 ≤ dualPrefixLength)
    (leftFactorDual : BONG V q (Lattice.dualLattice q L)
      (dualRightLength + 1))
    (seed : OrthogonalPrefixSeed q (Lattice.dualLattice q L)
      (baseTail + 1) (steps := s - 1) rightFactorDual.toBONG)
    (hlast : ∀ hsTwo : 2 ≤ s,
      rightFactorDual.order ⟨s - 2, by omega⟩ ≤
        leftFactorDual.order 0)
    (targetDual : GoodBONG (r.orthogonalSum q)
      (Lattice.dualLattice (r.orthogonalSum q)
        (Lattice.swapLattice N))
      ((baseTail + 1) + (s - 1)))
    (leftVectors : ∀ i : Fin (s - 1),
      targetDual.toBONG.ambientVector
          (orthogonalProductLeftIndex (baseTail + 1) i) =
        (rightFactorDual.toBONG.ambientVector (seed.sourceIndex i), 0))
    (rightVectors : ∀ j : Fin (baseTail + 1),
      targetDual.toBONG.ambientVector
          (orthogonalProductRightIndex (s - 1) j) =
        seed.baseAmbientVector j) :
    N = Lattice.product L M := by
  have hswap : Lattice.swapLattice N = Lattice.product M L :=
    rightFactorDual.beli2019Lemma710DualRightEnd_all_of_good
      (q := r) (r := q) (L := M) (M := L) (s := s) hs hsRank
      leftFactorDual seed hlast targetDual leftVectors rightVectors
  exact Lattice.eq_product_of_swapLattice_eq hswap

/-- Step-count form of the swapped reverse-dual endpoint argument. -/
theorem beli2019Lemma710SwappedDualRightEnd_steps_of_good
    {dualPrefixLength dualRightLength baseTail steps : Nat}
    {N : Lattice K (V × W)}
    (rightFactorDual : GoodBONG r (Lattice.dualLattice r M)
      dualPrefixLength)
    (hsteps : steps ≤ dualPrefixLength)
    (leftFactorDual : BONG V q (Lattice.dualLattice q L)
      (dualRightLength + 1))
    (seed : OrthogonalPrefixSeed q (Lattice.dualLattice q L)
      (baseTail + 1) (steps := steps) rightFactorDual.toBONG)
    (hlast : ∀ hpos : 0 < steps,
      rightFactorDual.order ⟨steps - 1, by omega⟩ ≤
        leftFactorDual.order 0)
    (targetDual : GoodBONG (r.orthogonalSum q)
      (Lattice.dualLattice (r.orthogonalSum q)
        (Lattice.swapLattice N))
      ((baseTail + 1) + steps))
    (leftVectors : ∀ i : Fin steps,
      targetDual.toBONG.ambientVector
          (orthogonalProductLeftIndex (baseTail + 1) i) =
        (rightFactorDual.toBONG.ambientVector (seed.sourceIndex i), 0))
    (rightVectors : ∀ j : Fin (baseTail + 1),
      targetDual.toBONG.ambientVector
          (orthogonalProductRightIndex steps j) =
        seed.baseAmbientVector j) :
    N = Lattice.product L M := by
  have hswap : Lattice.swapLattice N = Lattice.product M L :=
    rightFactorDual.beli2019Lemma710DualRightEnd_steps_of_good
      (q := r) (r := q) (L := M) (M := L) hsteps leftFactorDual
      seed hlast targetDual leftVectors rightVectors
  exact Lattice.eq_product_of_swapLattice_eq hswap

/-- The dual endpoint conclusion in the exact type required at the stopping
constructor of a raw prefix seed.  This theorem is the formal handoff between
the two applications in Beli's general-case proof. -/
theorem rawStopLatticeEq_of_swappedDualRightEnd_all_of_good
    {sourceLength dualPrefixLength dualRightLength baseTail s : Nat}
    {N : Lattice K (V × W)}
    (source : BONG V q L sourceLength)
    (base : BONG (V × W) (q.orthogonalSum r) N
      ((baseTail + 1) + (s - 1)))
    (rightFactorDual : GoodBONG r (Lattice.dualLattice r M)
      dualPrefixLength)
    (hs : 1 ≤ s) (hsRank : s - 1 ≤ dualPrefixLength)
    (leftFactorDual : BONG V q (Lattice.dualLattice q L)
      (dualRightLength + 1))
    (seed : OrthogonalPrefixSeed q (Lattice.dualLattice q L)
      (baseTail + 1) (steps := s - 1) rightFactorDual.toBONG)
    (hlast : ∀ hsTwo : 2 ≤ s,
      rightFactorDual.order ⟨s - 2, by omega⟩ ≤
        leftFactorDual.order 0)
    (targetDual : GoodBONG (r.orthogonalSum q)
      (Lattice.dualLattice (r.orthogonalSum q)
        (Lattice.swapLattice N))
      ((baseTail + 1) + (s - 1)))
    (leftVectors : ∀ i : Fin (s - 1),
      targetDual.toBONG.ambientVector
          (orthogonalProductLeftIndex (baseTail + 1) i) =
        (rightFactorDual.toBONG.ambientVector (seed.sourceIndex i), 0))
    (rightVectors : ∀ j : Fin (baseTail + 1),
      targetDual.toBONG.ambientVector
          (orthogonalProductRightIndex (s - 1) j) =
        seed.baseAmbientVector j) :
    (OrthogonalPrefixRawSeed.stop (M := M) source base).StopLatticeEq := by
  change N = Lattice.product L M
  exact rightFactorDual.beli2019Lemma710SwappedDualRightEnd_all_of_good
    (q := q) (r := r) (L := L) (M := M) hs hsRank leftFactorDual
    seed hlast targetDual leftVectors rightVectors

/-- The second half of the general proof of Lemma 7.10.  The hypothesis
`tailIdentity` is exactly the conclusion of the reverse-dual endpoint
argument; after realizing the raw seed, the unified original endpoint
theorem adjoins all unchanged prefix vectors. -/
theorem beli2019Lemma710General_of_tailIdentity
    {baseTail s : Nat} {N : Lattice K (V × W)}
    (b : GoodBONG q L n) (hs : 1 ≤ s)
    (hsRank : s - 1 ≤ n)
    (right : BONG W r M (rightLength + 1))
    (raw : OrthogonalPrefixRawSeed r M (baseTail + 1)
      (steps := s - 1) b.toBONG)
    (tailIdentity : raw.StopLatticeEq)
    (hlast : ∀ hsTwo : 2 ≤ s,
      b.order ⟨s - 2, by omega⟩ ≤ right.order 0)
    (target : BONG (V × W) (q.orthogonalSum r) N
      ((baseTail + 1) + (s - 1)))
    (targetGood : target.IsGood)
    (leftVectors : ∀ i : Fin (s - 1),
      target.ambientVector
          (orthogonalProductLeftIndex (baseTail + 1) i) =
        (b.toBONG.ambientVector (raw.sourceIndex i), 0))
    (rightVectors : ∀ j : Fin (baseTail + 1),
      target.ambientVector (orthogonalProductRightIndex (s - 1) j) =
        raw.baseAmbientVector j) :
    N = Lattice.product L M := by
  let seed := raw.toSeed tailIdentity
  apply b.beli2019Lemma710RightEnd_all_of_good s hs hsRank right seed
    hlast target targetGood
  · intro i
    rw [raw.sourceIndex_toSeed tailIdentity i]
    exact leftVectors i
  · intro j
    rw [raw.baseAmbientVector_toSeed tailIdentity j]
    exact rightVectors j

end GoodBONG

namespace OrthogonalPrefixRawSeed.DualEndpointCertificate

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  {n steps baseLength : Nat} {b : BONG V q L n}
  {raw : OrthogonalPrefixRawSeed r M baseLength
    (steps := steps) b}

/-- The reverse-dual certificate proves exactly the stopping identity stored
by its raw seed.  This recursion is the formal composition point between the
two endpoint arguments in the paper. -/
theorem tailIdentity
    (C : OrthogonalPrefixRawSeed.DualEndpointCertificate r M raw) :
    raw.StopLatticeEq := by
  induction C with
  | stop source base rightFactorDual hsteps leftFactorDual seed hlast
      targetDual leftVectors rightVectors =>
      change _ = Lattice.product _ M
      exact rightFactorDual.beli2019Lemma710SwappedDualRightEnd_steps_of_good
        hsteps leftFactorDual seed hlast targetDual leftVectors rightVectors
  | cons generator anisotropic tail tailSeed tailCertificate ih =>
      exact ih

end OrthogonalPrefixRawSeed.DualEndpointCertificate

namespace GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  {n rightLength : Nat}

/-- Certificate-level general form of Beli (2019), Lemma 7.10.  The
`dualCertificate` proves the internal tail identity by the swapped
reverse-dual endpoint argument; the theorem then realizes the raw seed and
applies the original endpoint argument to recover the entire product
lattice.  Both boundary cases are included through conditional endpoint
hypotheses. -/
theorem beli2019Lemma710General
    {baseTail steps : Nat} {N : Lattice K (V × W)}
    (b : GoodBONG q L n) (hsteps : steps ≤ n)
    (right : BONG W r M (rightLength + 1))
    (raw : OrthogonalPrefixRawSeed r M (baseTail + 1)
      (steps := steps) b.toBONG)
    (dualCertificate :
      OrthogonalPrefixRawSeed.DualEndpointCertificate r M raw)
    (hlast : ∀ hpos : 0 < steps,
      b.order ⟨steps - 1, by omega⟩ ≤ right.order 0)
    (target : BONG (V × W) (q.orthogonalSum r) N
      ((baseTail + 1) + steps))
    (targetGood : target.IsGood)
    (leftVectors : ∀ i : Fin steps,
      target.ambientVector
          (orthogonalProductLeftIndex (baseTail + 1) i) =
        (b.toBONG.ambientVector (raw.sourceIndex i), 0))
    (rightVectors : ∀ j : Fin (baseTail + 1),
      target.ambientVector (orthogonalProductRightIndex steps j) =
        raw.baseAmbientVector j) :
    N = Lattice.product L M := by
  let tailIdentity := dualCertificate.tailIdentity
  let seed := raw.toSeed tailIdentity
  apply b.beli2019Lemma710RightEnd_steps_of_good hsteps right seed
    hlast target targetGood
  · intro i
    rw [raw.sourceIndex_toSeed tailIdentity i]
    exact leftVectors i
  · intro j
    rw [raw.baseAmbientVector_toSeed tailIdentity j]
    exact rightVectors j

end GoodBONG

end BONG

end Bong
