/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Mathlib.Tactic

/-!
# Elementary truth parity

This file contains the propositional parity calculation used in Beli's
quadratic-space cycle arguments.  It is independent of lattices and of every
paper-specific approximation construction.
-/

namespace Bong

/-- An even number of four propositions is true.  The formulation by two
pairwise equivalences has exactly the truth table with 0, 2, or 4 truths. -/
def EvenTruthParity (p q r s : Prop) : Prop :=
  (p ↔ q) ↔ (r ↔ s)

namespace EvenTruthParity

variable {p q r s : Prop}

/-- If the first two propositions hold, the remaining two are equivalent. -/
theorem remaining_iff_of_first_second (h : EvenTruthParity p q r s)
    (hp : p) (hq : q) : r ↔ s := by
  unfold EvenTruthParity at h
  tauto

/-- If the first and fourth propositions hold, the middle pair are
equivalent. -/
theorem second_iff_third_of_first_fourth (h : EvenTruthParity p q r s)
    (hp : p) (hs : s) : q ↔ r := by
  unfold EvenTruthParity at h
  tauto

/-- If the second and fourth propositions hold, the first and third are
equivalent. -/
theorem first_iff_third_of_second_fourth (h : EvenTruthParity p q r s)
    (hq : q) (hs : s) : p ↔ r := by
  unfold EvenTruthParity at h
  tauto

/-- All six choices of two known true propositions give equivalence of the
remaining pair. -/
theorem all_pair_consequences (h : EvenTruthParity p q r s) :
    (p → q → (r ↔ s)) ∧
    (p → r → (q ↔ s)) ∧
    (p → s → (q ↔ r)) ∧
    (q → r → (p ↔ s)) ∧
    (q → s → (p ↔ r)) ∧
    (r → s → (p ↔ q)) := by
  unfold EvenTruthParity at h
  tauto

/-- Every choice of three true propositions forces the fourth. -/
theorem all_triple_consequences (h : EvenTruthParity p q r s) :
    (p → q → r → s) ∧
    (p → q → s → r) ∧
    (p → r → s → q) ∧
    (q → r → s → p) := by
  unfold EvenTruthParity at h
  tauto

end EvenTruthParity

end Bong
