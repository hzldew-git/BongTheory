/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyPrimaryPrevious
import Bong.Bong.Beli2019Lemma214Current
import Bong.Bong.Beli2019Lemma29ReducedPrimeRight

/-!
# Beli (2019), Lemma 4.2: the second primary branch

In the branch `S_i < T_(i-2)`, Lemma 2.14 forces
`B_(i-1) = B'_(i-1)`: otherwise its current-index implication would give
the contradictory inequality `T_(i-2) < S_i`.  The strict adjacent-pair
comparison then gives `T_(i-1) < S_(i+1)`, and Lemma 2.9 reduces
`B'_(i-1)` to its two surviving candidates.
-/

namespace Bong

open Dyadic

universe u w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {r : QuadraticSpace K W} {s : QuadraticSpace K U}
  {M : Lattice K W} {N : Lattice K U} {n : Nat}

/-- Lines 2257--2259: in the branch `S_i < T_(i-2)`, Lemma 2.14
excludes `B_(i-1) != B'_(i-1)`. -/
theorem middleTargetAlpha_eq_prime_of_current_lt_previous
    [Beli2006AlphaLaws.{u, z} K]
    (b : GoodBONG r M (n + 1)) (c : GoodBONG s N (n + 1))
    (horder : b.RepresentationOrderCondition c le_rfl)
    (hdefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val)
    (hreverse : b.order ⟨j.val, j.lt_large⟩ <
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩) :
    b.representationAlpha c j = b.representationAlphaPrime c j := by
  have hjLt : j.val < n + 1 := j.lt_large
  let central : CentralRepresentationIndex (n + 1) (n + 1) := {
    val := j.val
    one_lt := hiTwo
    lt_large := j.lt_large
    le_small_succ := by omega }
  have hsmall : central.val ≤ n + 1 := by
    dsimp only [central]
    omega
  have hcurrent : central.current hsmall = j := by
    rfl
  by_contra hne
  have htrigger := b.centralAlphaTrigger_of_current_alpha_ne_prime
    c le_rfl horder hdefect central hsmall (by simpa only [hcurrent] using hne)
  have hforward : c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ <
      b.order ⟨j.val, j.lt_large⟩ := by
    simpa only [central] using htrigger.1
  exact (not_lt_of_ge hreverse.le) hforward

/-- Lines 2257--2261: after Lemmas 2.14 and 2.9, `B_(i-1)` is the
minimum of the primary candidate and the current secondary candidate. -/
theorem middleTargetAlpha_eq_min_primary_current_of_current_lt_previous
    [Beli2006AlphaLaws.{u, z} K]
    (b : GoodBONG r M (n + 1)) (c : GoodBONG s N (n + 1))
    (horder : b.RepresentationOrderCondition c le_rfl)
    (hdefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hpair :
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ +
          c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ <
        b.order ⟨j.val, j.lt_large⟩ +
          b.order ⟨j.val + 1, hi.2⟩)
    (hreverse : b.order ⟨j.val, j.lt_large⟩ <
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩) :
    b.representationAlpha c j =
      min (b.representationPrimaryDefect c j)
        (b.representationSecondaryCurrentDefect c j hi) := by
  have hcross : c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ ≤
      b.order ⟨j.val + 1, hi.2⟩ := by
    omega
  rw [b.middleTargetAlpha_eq_prime_of_current_lt_previous
      c horder hdefect j hi.1 hreverse,
    b.representationAlphaPrime_eq_min_primary_current c j hi hcross]

/-- Lines 2257--2261, including the primed conclusion of Lemma 2.9:
`B_(i-1) = B'_(i-1)` and `B'_(i-1)` is the minimum of the primary
candidate and the surviving reduced source-alpha candidate. -/
theorem middleTargetAlpha_eq_min_primary_sourceAlpha_of_current_lt_previous
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (b : GoodBONG r M (n + 1)) (c : GoodBONG s N (n + 1))
    (horder : b.RepresentationOrderCondition c le_rfl)
    (hdefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hpair :
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ +
          c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ <
        b.order ⟨j.val, j.lt_large⟩ + b.order ⟨j.val + 1, hi.2⟩)
    (hreverse : b.order ⟨j.val, j.lt_large⟩ <
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩) :
    b.representationAlpha c j =
      min (b.representationPrimaryDefect c j)
        (b.representationSecondarySourceAlpha c j hi) := by
  have hcross : c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ ≤
      b.order ⟨j.val + 1, hi.2⟩ := by
    omega
  have hshift : 0 <
      b.order ⟨j.val, j.lt_large⟩ + b.order ⟨j.val + 1, hi.2⟩ -
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ := by
    omega
  have heqPrime := b.middleTargetAlpha_eq_prime_of_current_lt_previous
    c horder hdefect j hi.1 hreverse
  have hcomparison : b.representationAlphaPrime c j ≤
      b.truncatedPrefixDefect c 1 j.val j.val := by
    rw [← heqPrime]
    simpa only [← b.coe_representationAlphaValue c j] using hdefect j
  have hprimeReduced := b.representationAlphaPrime_eq_primeReduced_of_rightCross
    (sourceLaws := middleLaws) (targetLaws := targetLaws)
    c j hi j.lt_large hcross hshift hcomparison
  rw [heqPrime, hprimeReduced,
    b.representationAlphaPrimeReduced_eq_min_primary_source_of_cross
      c j hi j.lt_large hcross]

end BONG.GoodBONG

end Bong
