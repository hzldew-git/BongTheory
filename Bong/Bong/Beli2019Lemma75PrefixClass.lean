/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma75EndpointClass
import Bong.Bong.AlternatingEndpointProduct

/-!
# Beli (2019), Lemma 7.5: the complete prefix square class

For an alternating segment beginning at the first BONG coordinate, the
pairwise endpoint classification propagates to the signed product of the
whole even prefix.  Thus the prefix has the hyperbolic square class or the
single unramified-discriminant twist.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The complete signed prefix in Lemma 7.5 has one of the two endpoint
square classes. -/
theorem beli2019Lemma75_signedPrefixProduct_endpoint_cases
    [Beli2006AlphaLaws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 2)) (j : Fin (n + 1)) (R : Int)
    (hjeven : Even j.val)
    (hinitial : b.order 0 = R)
    (hterminal :
      b.order j.succ = R - 2 * (ramificationIndex K : Int)) :
    ∃ pairs : Nat, 2 * pairs = j.val + 2 ∧
      (IsSquare (b.toBONG.signedEvenPrefixProduct pairs) ∨
        IsSquare (b.toBONG.signedEvenPrefixProduct pairs *
          laws.discriminantUnit)) := by
  rcases hjeven with ⟨d, hd⟩
  let first : Fin (n + 1) := ⟨0, by omega⟩
  have hfirstLe : first ≤ j := by
    exact Fin.mk_le_mk.mpr (Nat.zero_le _)
  have hsegmentEven : Even (j.val - first.val) := by
    simpa only [first, Fin.val_mk, Nat.sub_zero] using ⟨d, hd⟩
  have hinitial' : b.order first.castSucc = R := by
    have hindex : first.castSucc = (0 : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact hinitial
  have hbound : 2 * (d + 1) ≤ n + 2 := by omega
  have hprefix := b.toBONG.signedEvenPrefixProduct_endpoint_cases
    (d + 1) hbound (fun t ht => by
      let k : Fin (n + 1) := ⟨2 * t, by omega⟩
      have hkLe : k ≤ j := by
        change 2 * t ≤ j.val
        omega
      have hkEven : Even (k.val - first.val) := by
        refine ⟨t, ?_⟩
        simp only [k, first, Nat.sub_zero]
        omega
      have hclasses := b.beli2019Lemma75_pairBlock_endpointClass
        first j k R hfirstLe hsegmentEven hinitial' hterminal
          (Fin.zero_le k) hkLe hkEven
      have hpair := b.toBONG.adjacentSignedProduct_endpoint_cases
        k.castSucc (Nat.succ_lt_succ k.isLt) hclasses
      simpa only [k, Fin.castSucc_mk] using hpair)
  refine ⟨d + 1, ?_, hprefix⟩
  omega

end BONG.GoodBONG

end Bong
