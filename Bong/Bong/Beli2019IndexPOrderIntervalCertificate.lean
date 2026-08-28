/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019IndexPOrderCertificate

/-!
# Embedding Section 5.4 certificates in a global order sequence

The exceptional unary calculation occupies one contiguous interval of the
two global BONG order sequences.  This file transports an explicit local
coordinate certificate to that interval, assuming direct comparison outside
it.  Keeping the certificate constructors visible preserves the audit trail
for Beli's direct-or-adjacent-pair alternative.
-/

namespace Bong

namespace Beli2019IndexPOrderCertificate

/-- Embed a complete local certificate in a global interval while retaining
already constructed coordinate certificates outside that interval.  This is
the form needed when other Jordan blocks use the adjacent-pair branch rather
than a direct comparison. -/
theorem embedIntervalWithOutside
    {n length : Nat}
    {x y : BeliOrderSequence n Int}
    {localX localY : BeliOrderSequence length Int}
    (start : Nat) (hbound : start + length ≤ n)
    (localCert : Beli2019IndexPOrderCertificate localX localY)
    (hsource : ∀ (j : Nat) (hj : j < length),
      x.entry (start + j) (by omega) = localX.entry j hj)
    (htarget : ∀ (j : Nat) (hj : j < length),
      y.entry (start + j) (by omega) = localY.entry j hj)
    (houtside : ∀ (i : Nat) (hi : i < n),
      i < start ∨ start + length ≤ i →
        Beli2019IndexPOrderCoordinateCertificate x y i hi) :
    Beli2019IndexPOrderCertificate x y where
  coordinate i hi := by
    by_cases hleft : i < start
    · exact houtside i hi (Or.inl hleft)
    by_cases hright : start + length ≤ i
    · exact houtside i hi (Or.inr hright)
    let j := i - start
    have hj : j < length := by
      dsimp only [j]
      omega
    have hstartj : start + j = i := by
      dsimp only [j]
      omega
    cases localCert.coordinate j hj with
    | direct hdirect =>
        apply Beli2019IndexPOrderCoordinateCertificate.direct
        calc
          x.entry i hi = localX.entry j hj := by
            simpa only [hstartj] using hsource j hj
          _ ≤ localY.entry j hj := hdirect
          _ = y.entry i hi := by
            symm
            simpa only [hstartj] using htarget j hj
    | jordanPair positive nextBound scale sourceNorm targetNorm normBound
        sourceCurrent sourceNext targetPrevious targetCurrent =>
        have hglobalPositive : 0 < i := by omega
        have hglobalNext : i + 1 < n := by omega
        apply Beli2019IndexPOrderCoordinateCertificate.jordanPair
          hglobalPositive hglobalNext scale sourceNorm targetNorm normBound
        · calc
            x.entry i hi = localX.entry j hj := by
              simpa only [hstartj] using hsource j hj
            _ = 2 * scale - sourceNorm := sourceCurrent
        · calc
            x.entry (i + 1) hglobalNext =
                localX.entry (j + 1) nextBound := by
              have hindex : start + (j + 1) = i + 1 := by omega
              simpa only [hindex] using hsource (j + 1) nextBound
            _ = sourceNorm := sourceNext
        · calc
            y.entry (i - 1) (by omega) =
                localY.entry (j - 1) (by omega) := by
              have hindex : start + (j - 1) = i - 1 := by omega
              simpa only [hindex] using htarget (j - 1) (by omega)
            _ = targetNorm := targetPrevious
        · calc
            y.entry i hi = localY.entry j hj := by
              simpa only [hstartj] using htarget j hj
            _ = 2 * scale - targetNorm := targetCurrent

/-- Embed a complete local certificate in a global interval.  Coordinates
outside the interval are supplied by the direct branch. -/
theorem embedInterval
    {n length : Nat}
    {x y : BeliOrderSequence n Int}
    {localX localY : BeliOrderSequence length Int}
    (start : Nat) (hbound : start + length ≤ n)
    (localCert : Beli2019IndexPOrderCertificate localX localY)
    (hsource : ∀ (j : Nat) (hj : j < length),
      x.entry (start + j) (by omega) = localX.entry j hj)
    (htarget : ∀ (j : Nat) (hj : j < length),
      y.entry (start + j) (by omega) = localY.entry j hj)
    (houtside : ∀ (i : Nat) (hi : i < n),
      i < start ∨ start + length ≤ i →
        x.entry i hi ≤ y.entry i hi) :
    Beli2019IndexPOrderCertificate x y where
  coordinate i hi := by
    by_cases hleft : i < start
    · exact Beli2019IndexPOrderCoordinateCertificate.direct
        (houtside i hi (Or.inl hleft))
    by_cases hright : start + length ≤ i
    · exact Beli2019IndexPOrderCoordinateCertificate.direct
        (houtside i hi (Or.inr hright))
    let j := i - start
    have hj : j < length := by
      dsimp only [j]
      omega
    have hstartj : start + j = i := by
      dsimp only [j]
      omega
    cases localCert.coordinate j hj with
    | direct hdirect =>
        apply Beli2019IndexPOrderCoordinateCertificate.direct
        calc
          x.entry i hi = localX.entry j hj := by
            simpa only [hstartj] using hsource j hj
          _ ≤ localY.entry j hj := hdirect
          _ = y.entry i hi := by
            symm
            simpa only [hstartj] using htarget j hj
    | jordanPair positive nextBound scale sourceNorm targetNorm normBound
        sourceCurrent sourceNext targetPrevious targetCurrent =>
        have hglobalPositive : 0 < i := by omega
        have hglobalNext : i + 1 < n := by omega
        apply Beli2019IndexPOrderCoordinateCertificate.jordanPair
          hglobalPositive hglobalNext scale sourceNorm targetNorm normBound
        · calc
            x.entry i hi = localX.entry j hj := by
              simpa only [hstartj] using hsource j hj
            _ = 2 * scale - sourceNorm := sourceCurrent
        · calc
            x.entry (i + 1) hglobalNext =
                localX.entry (j + 1) nextBound := by
              have hindex : start + (j + 1) = i + 1 := by omega
              simpa only [hindex] using hsource (j + 1) nextBound
            _ = sourceNorm := sourceNext
        · calc
            y.entry (i - 1) (by omega) =
                localY.entry (j - 1) (by omega) := by
              have hindex : start + (j - 1) = i - 1 := by omega
              simpa only [hindex] using htarget (j - 1) (by omega)
            _ = targetNorm := targetPrevious
        · calc
            y.entry i hi = localY.entry j hj := by
              simpa only [hstartj] using htarget j hj
            _ = 2 * scale - targetNorm := targetCurrent

end Beli2019IndexPOrderCertificate

end Bong
