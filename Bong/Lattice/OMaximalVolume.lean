/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.OMaximalUniqueness
import Bong.Lattice.OrthogonalDecompositionVolume

/-!
# Recognizing maximal lattices by volume

An integral lattice in the same quadratic space as a fixed maximal lattice is
maximal exactly when their volume orders agree. This supplies the converse in
He (2025), Lemmas 4.11 and 4.12, once the displayed BONG orders are summed.
-/

namespace Bong.Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- On a fixed local quadratic space, an integral lattice is maximal precisely
when its volume order agrees with that of a maximal reference lattice. -/
theorem isOMaximal_iff_volumeOrder_eq_of_ambientlyIsometric
    (hL : IsIntegral q L) (hM : IsOMaximal r M) (ambient : q.IsIsometric r) :
    IsOMaximal q L ↔ volumeOrder q L = volumeOrder r M := by
  constructor
  · intro hmaximal
    obtain ⟨f⟩ := oMaximal_isIsometric_of_isometric hmaximal hM ambient
    exact volumeOrder_eq_of_isometry f
  · intro hvolume
    obtain ⟨P, hLP, hP⟩ := exists_oMaximal_superlattice hL
    obtain ⟨f⟩ := oMaximal_isIsometric_of_isometric hP hM ambient
    have heq : L = P := eq_of_le_of_volumeOrder_eq q L P hLP
      (hvolume.trans (volumeOrder_eq_of_isometry f).symm)
    rwa [heq]

/-- The equal-volume criterion also identifies the lattice with the chosen
maximal representative, as in the conclusions of He (2025), Lemmas 4.11--4.12. -/
theorem isIsometric_iff_volumeOrder_eq_of_isOMaximal
    (hL : IsIntegral q L) (hM : IsOMaximal r M) (ambient : q.IsIsometric r) :
    IsIsometric q r L M ↔ volumeOrder q L = volumeOrder r M := by
  constructor
  · rintro ⟨f⟩
    exact volumeOrder_eq_of_isometry f
  · intro hvolume
    exact oMaximal_isIsometric_of_isometric
      ((isOMaximal_iff_volumeOrder_eq_of_ambientlyIsometric hL hM ambient).2 hvolume)
      hM ambient

end Bong.Lattice
