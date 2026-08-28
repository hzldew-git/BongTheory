/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019IndexPOrderIntervalCertificate
import Bong.Bong.Beli2019IndexPOrderEndpoints

/-!
# Explicit certificates for the exceptional unary block in Section 5.4

The earlier arithmetic lemmas prove the local `BeliOrderLE` statements.  The
declarations here retain the stronger, inspectable coordinate certificates
needed by the concrete Section 5 order package.
-/

namespace Bong

namespace Beli2019IndexPOrderCertificate

/-- Explicit certificate for the proper intermediate-scale unary block
`r-2, r-1, ..., r-1` versus `r-1, ..., r-1, r`. -/
theorem indexPUnaryProper (r : Int) (k : Nat) :
    Beli2019IndexPOrderCertificate
      (BeliOrderSequence.loweredLeftEndpoint
        (r - 2) (r - 1) (by omega) k)
      (BeliOrderSequence.raisedRightEndpoint
        (r - 1) r (by omega) k) where
  coordinate i hi := by
    apply Beli2019IndexPOrderCoordinateCertificate.direct
    change (if i = 0 then r - 2 else r - 1) ≤
      (if i = k + 1 then r else r - 1)
    by_cases hi0 : i = 0
    · have hnotLast : i ≠ k + 1 := by omega
      rw [if_pos hi0, if_neg hnotLast]
      omega
    · by_cases hlast : i = k + 1
      · rw [if_neg hi0, if_pos hlast]
        omega
      · rw [if_neg hi0, if_neg hlast]

/-- Explicit adjacent-pair certificate for the improper alternating unary
block `r-2, r, r-2, ...` versus its one-place shift. -/
theorem indexPUnaryExceptional (r : Int) (k : Nat) :
    Beli2019IndexPOrderCertificate
      (BeliOrderSequence.alternatingLowFirst (r - 2) r k)
      (BeliOrderSequence.alternatingHighFirst (r - 2) r k) where
  coordinate i hi := by
    by_cases heven : i % 2 = 0
    · apply Beli2019IndexPOrderCoordinateCertificate.direct
      simp only [BeliOrderSequence.alternatingLowFirst_entry,
        BeliOrderSequence.alternatingHighFirst_entry, heven, if_pos]
      omega
    · have hodd : i % 2 = 1 := by omega
      have hi0 : 0 < i := by omega
      have hiNext : i + 1 < 2 * k + 1 := by omega
      apply Beli2019IndexPOrderCoordinateCertificate.jordanPair
        hi0 hiNext (r - 1) (r - 2) r (by omega)
      · simp only [BeliOrderSequence.alternatingLowFirst_entry,
          hodd, one_ne_zero, if_false]
        omega
      · have hnext : (i + 1) % 2 = 0 := by omega
        simp only [BeliOrderSequence.alternatingLowFirst_entry,
          hnext, if_pos]
      · have hprevious : (i - 1) % 2 = 0 := by omega
        simp only [BeliOrderSequence.alternatingHighFirst_entry,
          hprevious, if_pos]
      · simp only [BeliOrderSequence.alternatingHighFirst_entry,
          hodd, one_ne_zero, if_false]
        omega

end Beli2019IndexPOrderCertificate

end Bong
