/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliCorollary44ThreeBlockProof
import Bong.Bong.BeliCorollary44ComponentProof
import Bong.Bong.BeliCorollary44ScaleProof
import Bong.Bong.BeliCorollary44GlueProof

/-!
# Unconditional realization of Beli (2003), Corollary 4.4

The legacy `BeliCorollary44Laws` record is retained as an internal compatibility
bundle.  Every field is now a theorem, so importing this module removes it from
the assumptions of downstream public results.
-/

namespace Bong

open Dyadic

universe u v

variable (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The proved, assumption-free compatibility bundle for Corollary 4.4. -/
@[reducible] noncomputable def beliCorollary44LawsProved :
    BeliCorollary44Laws.{u, v} K where
  split_of_adjacentOrder_le := BONG.beliCorollary44_i_unconditional
  split_around_adjacentOrder_gt := BONG.beliCorollary44_ii_unconditional
  adjacentOrder_gt_sameComponent := BONG.beliCorollary44_iii_unconditional
  firstScaleOrder := BONG.beliCorollary44_iv_unconditional
  glue_good_iff_boundary := fun b hleft hright hsegments =>
    BONG.beliCorollary44_v_unconditional b _ hleft hright hsegments

noncomputable instance : BeliCorollary44Laws.{u, v} K :=
  beliCorollary44LawsProved K

end Bong
