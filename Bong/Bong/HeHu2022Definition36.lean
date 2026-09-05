/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022SectionThreeSpaces
import Bong.Bong.BeliUniversalLemma44

/-!
# He--Hu (2024), Definition 3.6

For every diagonal presentation of a quadratic space, this file chooses an
`O`-maximal lattice in that space.  Applying the construction to the two
families from Definition 3.4 gives the lattices `N_1^n(c)` and `N_2^n(c)`.

The choice made here is intentionally intrinsic: Proposition 3.7 will prove
that it is integrally isometric to the corresponding explicit row of Table 2.
-/

namespace Bong

open Dyadic Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A canonical `O`-maximal lattice on the finite diagonal space with
coefficient family `a`. -/
noncomputable def heHuOMaximalLattice {n : Nat} (a : Fin n → Kˣ) :
    Lattice K (Fin n → K) :=
  Classical.choose <|
    Lattice.exists_oMaximal_lattice
      (BONG.coefficientDiagonalSpace a)
      (Lattice.basisLattice (Pi.basisFun K (Fin n)))

/-- The chosen lattice is maximal in the displayed diagonal space. -/
theorem heHuOMaximalLattice_isOMaximal {n : Nat} (a : Fin n → Kˣ) :
    Lattice.IsOMaximal (BONG.coefficientDiagonalSpace a)
      (heHuOMaximalLattice a) :=
  Classical.choose_spec <|
    Lattice.exists_oMaximal_lattice
      (BONG.coefficientDiagonalSpace a)
      (Lattice.basisLattice (Pi.basisFun K (Fin n)))

/-- A bundled form of the canonical maximal representative. -/
noncomputable def heHuOMaximalModel {n : Nat} (a : Fin n → Kˣ) :
    Lattice.QuadraticLatticeModel (K := K) where
  Carrier := Fin n → K
  form := BONG.coefficientDiagonalSpace a
  lattice := heHuOMaximalLattice a

@[simp]
theorem heHuOMaximalModel_rank {n : Nat} (a : Fin n → Kˣ) :
    (heHuOMaximalModel a).rank = n := by
  change finrank K (Fin n → K) = n
  exact finrank_fin_fun K

theorem heHuOMaximalModel_isOMaximal {n : Nat} (a : Fin n → Kˣ) :
    (heHuOMaximalModel a).IsOMaximal := by
  exact heHuOMaximalLattice_isOMaximal a

/-- Definition 3.6, even-dimensional first column: `N_1^(2p+2)(c)`. -/
noncomputable def heHuEvenFirstMaximalModel (pairs : Nat) (c : Kˣ) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heHuOMaximalModel (heHuEvenFirst pairs c)

/-- Definition 3.6, even-dimensional second column, with the source's
definedness condition made explicit. -/
noncomputable def heHuEvenSecondMaximalModel (pairs : Nat) (c : Kˣ)
    (hdefined : HeHuEvenSecondDefined pairs c) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heHuOMaximalModel (heHuEvenSecond pairs c hdefined)

/-- Definition 3.6, odd-dimensional first column: `N_1^(2p+3)(c)`. -/
noncomputable def heHuOddFirstMaximalModel (pairs : Nat) (c : Kˣ) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heHuOMaximalModel (heHuOddFirst pairs c)

/-- Definition 3.6, odd-dimensional second column: `N_2^(2p+3)(c)`. -/
noncomputable def heHuOddSecondMaximalModel (pairs : Nat) (c : Kˣ) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heHuOMaximalModel (heHuOddSecond pairs c)

@[simp]
theorem heHuEvenFirstMaximalModel_rank (pairs : Nat) (c : Kˣ) :
    (heHuEvenFirstMaximalModel pairs c).rank = 2 * pairs + 2 := by
  exact heHuOMaximalModel_rank _

@[simp]
theorem heHuEvenSecondMaximalModel_rank (pairs : Nat) (c : Kˣ)
    (hdefined : HeHuEvenSecondDefined pairs c) :
    (heHuEvenSecondMaximalModel pairs c hdefined).rank = 2 * pairs + 2 := by
  exact heHuOMaximalModel_rank _

@[simp]
theorem heHuOddFirstMaximalModel_rank (pairs : Nat) (c : Kˣ) :
    (heHuOddFirstMaximalModel pairs c).rank = 2 * pairs + 3 := by
  exact heHuOMaximalModel_rank _

@[simp]
theorem heHuOddSecondMaximalModel_rank (pairs : Nat) (c : Kˣ) :
    (heHuOddSecondMaximalModel pairs c).rank = 2 * pairs + 3 := by
  exact heHuOMaximalModel_rank _

/-- Direct checked endpoint for Definition 3.6 in the even first column. -/
theorem heHu2022Definition36EvenFirst (pairs : Nat) (c : Kˣ) :
    (heHuEvenFirstMaximalModel pairs c).IsOMaximal :=
  heHuOMaximalModel_isOMaximal _

/-- Direct checked endpoint for Definition 3.6 in the even second column. -/
theorem heHu2022Definition36EvenSecond (pairs : Nat) (c : Kˣ)
    (hdefined : HeHuEvenSecondDefined pairs c) :
    (heHuEvenSecondMaximalModel pairs c hdefined).IsOMaximal :=
  heHuOMaximalModel_isOMaximal _

/-- Direct checked endpoint for Definition 3.6 in the odd first column. -/
theorem heHu2022Definition36OddFirst (pairs : Nat) (c : Kˣ) :
    (heHuOddFirstMaximalModel pairs c).IsOMaximal :=
  heHuOMaximalModel_isOMaximal _

/-- Direct checked endpoint for Definition 3.6 in the odd second column. -/
theorem heHu2022Definition36OddSecond (pairs : Nat) (c : Kˣ) :
    (heHuOddSecondMaximalModel pairs c).IsOMaximal :=
  heHuOMaximalModel_isOMaximal _

end Bong
