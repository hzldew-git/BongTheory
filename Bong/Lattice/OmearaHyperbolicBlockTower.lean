import Bong.Lattice.OrthogonalDecompositionSuffixProduct
import Bong.Lattice.OmearaScaledHyperbolicTowerSpace

/-!
# Finite products of displayed hyperbolic towers
-/

namespace Bong

open Dyadic Module

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A nonempty block product whose every block is a two-plane scaled
hyperbolic tower is itself the corresponding finite hyperbolic tower. -/
noncomputable def blockTwoPlaneTowerIsometry (s : Kˣ) :
    (n : Nat) →
    (C : Fin (n + 1) → Type v) →
    [(i : Fin (n + 1)) → AddCommGroup (C i)] →
    [(i : Fin (n + 1)) → Module K (C i)] →
    (qs : (i : Fin (n + 1)) → QuadraticSpace K (C i)) →
    (∀ i, (qs i).IsIsometric (scaledZeroOmearaTowerForm s 2)) →
    Isometry (BONG.blockOrthogonalForm n C qs)
      (scaledZeroOmearaTowerForm s (2 * (n + 1)))
  | 0, C, _, _, qs, hq => by
      let singleton := BONG.blockOrthogonalSingletonIsometry C qs
      exact singleton.trans (Classical.choice (hq 0))
  | n + 1, C, _, _, qs, hq => by
      let tailC : Fin (n + 1) → Type v := fun i ↦ C i.succ
      let tailQ : (i : Fin (n + 1)) → QuadraticSpace K (tailC i) :=
        fun i ↦ qs i.succ
      let split := BONG.blockOrthogonalSplitIsometry n C qs
      let head := Classical.choice (hq 0)
      let tail := blockTwoPlaneTowerIsometry s n tailC tailQ
        (fun i ↦ hq i.succ)
      let joined := head.orthogonalSum tail
      let appended := scaledZeroOmearaTowerAppendSpaceIsometry s 2
        (2 * (n + 1))
      refine split.trans (joined.trans ?_)
      exact appended

end QuadraticSpace

end Bong
