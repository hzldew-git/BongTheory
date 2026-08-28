/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Mathlib.Order.RelClasses

/-!
# The rank-volume descent in Beli (2019), Sections 7--9

The sufficiency proof first descends in rank and, at fixed rank, descends in
the nonnegative volume gap.  This file fixes the corresponding lexicographic
relation and proves its well-foundedness once and for all.
-/

namespace Bong

/-- The two natural-number parameters used by Beli's nested induction. -/
structure Beli2019RankVolumeMeasure where
  rank : Nat
  volumeGap : Nat
deriving DecidableEq

namespace Beli2019RankVolumeMeasure

/-- The lexicographic order: rank is the primary induction parameter and the
volume gap is the secondary parameter. -/
def Smaller (x y : Beli2019RankVolumeMeasure) : Prop :=
  Prod.Lex (fun p q : Nat ↦ p < q) (fun p q : Nat ↦ p < q)
    (x.rank, x.volumeGap) (y.rank, y.volumeGap)

/-- A strict rank drop decreases the rank-volume measure. -/
theorem smaller_of_rank_lt {x y : Beli2019RankVolumeMeasure}
    (h : x.rank < y.rank) : Smaller x y :=
  Prod.Lex.left _ _ h

/-- At fixed rank, a strict decrease of the volume gap decreases the measure. -/
theorem smaller_of_volumeGap_lt {x y : Beli2019RankVolumeMeasure}
    (hrank : x.rank = y.rank) (hgap : x.volumeGap < y.volumeGap) :
    Smaller x y := by
  exact Prod.lex_def.mpr (Or.inr ⟨hrank, hgap⟩)

/-- The concrete rank-volume relation is well founded. -/
theorem smaller_wellFounded : WellFounded Smaller := by
  unfold Smaller
  exact InvImage.wf (fun x : Beli2019RankVolumeMeasure ↦
    (x.rank, x.volumeGap)) (wellFounded_lt.prod_lex wellFounded_lt)

end Beli2019RankVolumeMeasure

/-- Pull the rank-volume relation back along the measure of a coded problem. -/
def Beli2019ProblemSmaller {P : Type*}
    (measure : P → Beli2019RankVolumeMeasure) : P → P → Prop :=
  InvImage Beli2019RankVolumeMeasure.Smaller measure

/-- Every problem relation obtained from the concrete measure is well founded. -/
theorem beli2019ProblemSmaller_wellFounded {P : Type*}
    (measure : P → Beli2019RankVolumeMeasure) :
    WellFounded (Beli2019ProblemSmaller measure) :=
  InvImage.wf measure Beli2019RankVolumeMeasure.smaller_wellFounded

/-- A strict rank decrease between coded problems is a valid descent step. -/
theorem beli2019ProblemSmaller_of_rank_lt {P : Type*}
    {measure : P → Beli2019RankVolumeMeasure} {x y : P}
    (h : (measure x).rank < (measure y).rank) :
    Beli2019ProblemSmaller measure x y :=
  Beli2019RankVolumeMeasure.smaller_of_rank_lt h

/-- At equal rank, a strict volume-gap decrease is a valid descent step. -/
theorem beli2019ProblemSmaller_of_volumeGap_lt {P : Type*}
    {measure : P → Beli2019RankVolumeMeasure} {x y : P}
    (hrank : (measure x).rank = (measure y).rank)
    (hgap : (measure x).volumeGap < (measure y).volumeGap) :
    Beli2019ProblemSmaller measure x y :=
  Beli2019RankVolumeMeasure.smaller_of_volumeGap_lt hrank hgap

end Bong
