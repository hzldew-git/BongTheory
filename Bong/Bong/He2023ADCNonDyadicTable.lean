/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCSectionFive

/-!
# He (2025), Lemma 4.7(i): the non-dyadic maximal-lattice table

This file transcribes the literal block decompositions in the published
non-dyadic table.  A symbolic atom is either a unimodular hyperbolic plane or
a unary square-class block.  The four square classes determine whether a
unary block has Jordan scale zero or one.

The resulting certificate proves the rank and `J_0`/`J_1` rank arithmetic of
every defined row, including the missing binary row `N_2^2(1)`.  It also
proves the table-level assertion `J_{0,1}(N) = N` used in Lemma 4.8.  This is
a certificate for the printed finite data; it does not prove that the
symbolic rows classify actual maximal lattices or the representation theorem
in the second sentence of Lemma 4.8.
-/

namespace Bong

/-- A block occurring in the published non-dyadic maximal-lattice table. -/
inductive HeADC2025NonDyadicJordanAtom
  | hyperbolic
  | unary (squareClass : HeADC2025NonDyadicSquareClass)
  deriving DecidableEq

namespace HeADC2025NonDyadicJordanAtom

/-- Rank contributed by a symbolic table block. -/
def rank : HeADC2025NonDyadicJordanAtom → Nat
  | .hyperbolic => 2
  | .unary _ => 1

/-- Rank of the scale-zero Jordan part contributed by a table block. -/
def jordanZeroRank : HeADC2025NonDyadicJordanAtom → Nat
  | .hyperbolic => 2
  | .unary .one => 1
  | .unary .delta => 1
  | .unary .uniformizer => 0
  | .unary .deltaUniformizer => 0

/-- Rank of the scale-one Jordan part contributed by a table block. -/
def jordanOneRank : HeADC2025NonDyadicJordanAtom → Nat
  | .hyperbolic => 0
  | .unary .one => 0
  | .unary .delta => 0
  | .unary .uniformizer => 1
  | .unary .deltaUniformizer => 1

@[simp]
theorem jordanZeroRank_add_jordanOneRank
    (a : HeADC2025NonDyadicJordanAtom) :
    a.jordanZeroRank + a.jordanOneRank = a.rank := by
  cases a with
  | hyperbolic => rfl
  | unary c => cases c <;> rfl

end HeADC2025NonDyadicJordanAtom

/-- Multiplication by the nonsquare unit class `Delta`. -/
def HeADC2025NonDyadicSquareClass.deltaTwist :
    HeADC2025NonDyadicSquareClass → HeADC2025NonDyadicSquareClass
  | .one => .delta
  | .delta => .one
  | .uniformizer => .deltaUniformizer
  | .deltaUniformizer => .uniformizer

/-- Whether a square class has valuation zero. -/
def HeADC2025NonDyadicSquareClass.IsUnit :
    HeADC2025NonDyadicSquareClass → Prop
  | .one | .delta => True
  | .uniformizer | .deltaUniformizer => False

/-- The only excluded row in positive ranks at least two is `N_2^2(1)`. -/
def HeADC2025NonDyadicRowIsDefined (m : Nat)
    (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass) : Prop :=
  m ≠ 2 ∨ nu ≠ .two ∨ c ≠ .one

/-- Symbolic rank of a list of published Jordan blocks. -/
def heADC2025NonDyadicSymbolicRank
    (blocks : List HeADC2025NonDyadicJordanAtom) : Nat :=
  (blocks.map HeADC2025NonDyadicJordanAtom.rank).sum

/-- Symbolic rank of the scale-zero Jordan component. -/
def heADC2025NonDyadicSymbolicJordanZeroRank
    (blocks : List HeADC2025NonDyadicJordanAtom) : Nat :=
  (blocks.map HeADC2025NonDyadicJordanAtom.jordanZeroRank).sum

/-- Symbolic rank of the scale-one Jordan component. -/
def heADC2025NonDyadicSymbolicJordanOneRank
    (blocks : List HeADC2025NonDyadicJordanAtom) : Nat :=
  (blocks.map HeADC2025NonDyadicJordanAtom.jordanOneRank).sum

@[simp]
theorem heADC2025NonDyadicSymbolicJordanZeroRank_add_oneRank
    (blocks : List HeADC2025NonDyadicJordanAtom) :
    heADC2025NonDyadicSymbolicJordanZeroRank blocks +
        heADC2025NonDyadicSymbolicJordanOneRank blocks =
      heADC2025NonDyadicSymbolicRank blocks := by
  induction blocks with
  | nil => rfl
  | cons a blocks ih =>
      have ha :=
        HeADC2025NonDyadicJordanAtom.jordanZeroRank_add_jordanOneRank a
      simp only [heADC2025NonDyadicSymbolicJordanZeroRank,
        heADC2025NonDyadicSymbolicJordanOneRank,
        heADC2025NonDyadicSymbolicRank, List.map_cons, List.sum_cons]
        at ih ⊢
      omega

def heADC2025NonDyadicHyperbolicPower
    (k : Nat) : List HeADC2025NonDyadicJordanAtom :=
  List.replicate k .hyperbolic

def heADC2025NonDyadicEvenTail
    (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass) :
    List HeADC2025NonDyadicJordanAtom :=
  match nu, c with
  | .one, .one => []
  | .two, .one =>
      [.unary .one, .unary .delta, .unary .uniformizer,
        .unary .deltaUniformizer]
  | .one, .delta => [.unary .one, .unary .delta]
  | .two, .delta => [.unary .uniformizer, .unary .deltaUniformizer]
  | .one, .uniformizer => [.unary .one, .unary .uniformizer]
  | .two, .uniformizer => [.unary .delta, .unary .deltaUniformizer]
  | .one, .deltaUniformizer => [.unary .one, .unary .deltaUniformizer]
  | .two, .deltaUniformizer => [.unary .delta, .unary .uniformizer]

def heADC2025NonDyadicEvenHyperbolicCount
    (k : Nat) (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass) : Nat :=
  match nu, c with
  | .one, .one => k
  | .two, .one => k - 2
  | _, _ => k - 1

/-- The even-rank rows of Lemma 4.7(i), with rank written as `2*k`. -/
def heADC2025NonDyadicEvenTableRow
    (k : Nat) (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass) :
    List HeADC2025NonDyadicJordanAtom :=
  heADC2025NonDyadicHyperbolicPower
      (heADC2025NonDyadicEvenHyperbolicCount k nu c) ++
    heADC2025NonDyadicEvenTail nu c

/-- Definedness of an even-rank row.  The sole missing positive-rank row is
`N_2^2(1)`. -/
def HeADC2025NonDyadicEvenRowIsDefined
    (k : Nat) (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass) : Prop :=
  1 ≤ k ∧ (k ≠ 1 ∨ nu ≠ .two ∨ c ≠ .one)

instance (k : Nat) (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass) :
    Decidable (HeADC2025NonDyadicEvenRowIsDefined k nu c) := by
  unfold HeADC2025NonDyadicEvenRowIsDefined
  infer_instance

def heADC2025NonDyadicOddTail
    (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass) :
    List HeADC2025NonDyadicJordanAtom :=
  match nu, c with
  | .one, _ => [.unary c]
  | .two, .one =>
      [.unary .uniformizer, .unary .deltaUniformizer, .unary .delta]
  | .two, .delta =>
      [.unary .uniformizer, .unary .deltaUniformizer, .unary .one]
  | .two, .uniformizer =>
      [.unary .one, .unary .delta, .unary .deltaUniformizer]
  | .two, .deltaUniformizer =>
      [.unary .one, .unary .delta, .unary .uniformizer]

/-- Hyperbolic multiplicity in an odd row of the published table. -/
def heADC2025NonDyadicOddHyperbolicCount
    (k : Nat) (nu : HeADC2025NonDyadicColumn) : Nat :=
  match nu with
  | .one => k
  | .two => k - 1

/-- The odd-rank rows of Lemma 4.7(i), with rank written as `2*k+1`. -/
def heADC2025NonDyadicOddTableRow
    (k : Nat) (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass) :
    List HeADC2025NonDyadicJordanAtom :=
  heADC2025NonDyadicHyperbolicPower
      (heADC2025NonDyadicOddHyperbolicCount k nu) ++
    heADC2025NonDyadicOddTail nu c

/-- In rank one only the first column is defined; from rank three onward all
odd rows are defined. -/
def HeADC2025NonDyadicOddRowIsDefined
    (k : Nat) (nu : HeADC2025NonDyadicColumn) : Prop :=
  nu = .one ∨ 1 ≤ k

@[simp]
private theorem symbolicRank_hyperbolicPower (k : Nat) :
    heADC2025NonDyadicSymbolicRank
      (heADC2025NonDyadicHyperbolicPower k) = 2 * k := by
  simp [heADC2025NonDyadicSymbolicRank,
    heADC2025NonDyadicHyperbolicPower,
    HeADC2025NonDyadicJordanAtom.rank, Nat.mul_comm]

@[simp]
private theorem symbolicJordanZeroRank_hyperbolicPower (k : Nat) :
    heADC2025NonDyadicSymbolicJordanZeroRank
      (heADC2025NonDyadicHyperbolicPower k) = 2 * k := by
  simp [heADC2025NonDyadicSymbolicJordanZeroRank,
    heADC2025NonDyadicHyperbolicPower,
    HeADC2025NonDyadicJordanAtom.jordanZeroRank, Nat.mul_comm]

@[simp]
private theorem symbolicJordanOneRank_hyperbolicPower (k : Nat) :
    heADC2025NonDyadicSymbolicJordanOneRank
      (heADC2025NonDyadicHyperbolicPower k) = 0 := by
  simp [heADC2025NonDyadicSymbolicJordanOneRank,
    heADC2025NonDyadicHyperbolicPower,
    HeADC2025NonDyadicJordanAtom.jordanOneRank]

private theorem symbolicRank_append (a b : List HeADC2025NonDyadicJordanAtom) :
    heADC2025NonDyadicSymbolicRank (a ++ b) =
      heADC2025NonDyadicSymbolicRank a +
        heADC2025NonDyadicSymbolicRank b := by
  simp [heADC2025NonDyadicSymbolicRank]

private theorem symbolicJordanZeroRank_append
    (a b : List HeADC2025NonDyadicJordanAtom) :
    heADC2025NonDyadicSymbolicJordanZeroRank (a ++ b) =
      heADC2025NonDyadicSymbolicJordanZeroRank a +
        heADC2025NonDyadicSymbolicJordanZeroRank b := by
  simp [heADC2025NonDyadicSymbolicJordanZeroRank]

private theorem symbolicJordanOneRank_append
    (a b : List HeADC2025NonDyadicJordanAtom) :
    heADC2025NonDyadicSymbolicJordanOneRank (a ++ b) =
      heADC2025NonDyadicSymbolicJordanOneRank a +
        heADC2025NonDyadicSymbolicJordanOneRank b := by
  simp [heADC2025NonDyadicSymbolicJordanOneRank]

/-- Every defined even row has the printed rank `2*k`. -/
theorem heADC2025NonDyadicEvenTableRow_rank
    (k : Nat) (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass)
    (h : HeADC2025NonDyadicEvenRowIsDefined k nu c) :
    heADC2025NonDyadicSymbolicRank
      (heADC2025NonDyadicEvenTableRow k nu c) = 2 * k := by
  rcases h with ⟨hk, hDefined⟩
  cases nu <;> cases c <;>
    simp only [heADC2025NonDyadicEvenTableRow,
      heADC2025NonDyadicEvenHyperbolicCount,
      heADC2025NonDyadicEvenTail, symbolicRank_append,
      symbolicRank_hyperbolicPower] <;>
    simp [
      heADC2025NonDyadicSymbolicRank,
      HeADC2025NonDyadicJordanAtom.rank] at hDefined ⊢ <;> omega

/-- Every defined odd row has the printed rank `2*k+1`. -/
theorem heADC2025NonDyadicOddTableRow_rank
    (k : Nat) (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass)
    (h : HeADC2025NonDyadicOddRowIsDefined k nu) :
    heADC2025NonDyadicSymbolicRank
      (heADC2025NonDyadicOddTableRow k nu c) = 2 * k + 1 := by
  cases nu <;> cases c <;>
    simp only [heADC2025NonDyadicOddTableRow,
      heADC2025NonDyadicOddHyperbolicCount,
      heADC2025NonDyadicOddTail, symbolicRank_append,
      symbolicRank_hyperbolicPower] <;>
    simp [HeADC2025NonDyadicOddRowIsDefined,
      heADC2025NonDyadicSymbolicRank,
      HeADC2025NonDyadicJordanAtom.rank] at h ⊢ <;> omega

/-- Scale zero and scale one exhaust every defined even table row.  This is
the symbolic `J_{0,1}(N)=N` assertion of Lemma 4.8. -/
theorem heADC2025NonDyadicEvenTableRow_jordanZeroOne
    (k : Nat) (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass)
    (h : HeADC2025NonDyadicEvenRowIsDefined k nu c) :
    heADC2025NonDyadicSymbolicJordanZeroRank
        (heADC2025NonDyadicEvenTableRow k nu c) +
      heADC2025NonDyadicSymbolicJordanOneRank
        (heADC2025NonDyadicEvenTableRow k nu c) = 2 * k := by
  rw [heADC2025NonDyadicSymbolicJordanZeroRank_add_oneRank]
  exact heADC2025NonDyadicEvenTableRow_rank k nu c h

/-- Scale zero and scale one exhaust every defined odd table row. -/
theorem heADC2025NonDyadicOddTableRow_jordanZeroOne
    (k : Nat) (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass)
    (h : HeADC2025NonDyadicOddRowIsDefined k nu) :
    heADC2025NonDyadicSymbolicJordanZeroRank
        (heADC2025NonDyadicOddTableRow k nu c) +
      heADC2025NonDyadicSymbolicJordanOneRank
        (heADC2025NonDyadicOddTableRow k nu c) = 2 * k + 1 := by
  rw [heADC2025NonDyadicSymbolicJordanZeroRank_add_oneRank]
  exact heADC2025NonDyadicOddTableRow_rank k nu c h

/-- In either even column, a uniformizer-class row has scale-zero rank one
less than its total rank, as used in Lemma 5.3(i). -/
theorem heADC2025NonDyadicEvenUniformizerRow_jordanZeroRank
    (k : Nat) (hk : 1 ≤ k) (nu : HeADC2025NonDyadicColumn)
    (u : HeADC2025NonDyadicUnitClass) :
    heADC2025NonDyadicSymbolicJordanZeroRank
      (heADC2025NonDyadicEvenTableRow k nu u.timesUniformizer) =
        2 * k - 1 := by
  cases nu <;> cases u <;>
    simp only [heADC2025NonDyadicEvenTableRow,
      heADC2025NonDyadicEvenHyperbolicCount,
      HeADC2025NonDyadicUnitClass.timesUniformizer,
      heADC2025NonDyadicEvenTail, symbolicJordanZeroRank_append,
      symbolicJordanZeroRank_hyperbolicPower] <;>
    simp [
      heADC2025NonDyadicSymbolicJordanZeroRank,
      HeADC2025NonDyadicJordanAtom.jordanZeroRank]
  all_goals omega

/-- In either odd column, a uniformizer-class row has scale-zero rank one
less than its total rank, as used in Lemma 5.3(i). -/
theorem heADC2025NonDyadicOddUniformizerRow_jordanZeroRank
    (k : Nat) (hk : 1 ≤ k) (nu : HeADC2025NonDyadicColumn)
    (u : HeADC2025NonDyadicUnitClass) :
    heADC2025NonDyadicSymbolicJordanZeroRank
      (heADC2025NonDyadicOddTableRow k nu u.timesUniformizer) =
        2 * k := by
  cases nu <;> cases u <;>
    simp only [heADC2025NonDyadicOddTableRow,
      heADC2025NonDyadicOddHyperbolicCount,
      HeADC2025NonDyadicUnitClass.timesUniformizer,
      heADC2025NonDyadicOddTail, symbolicJordanZeroRank_append,
      symbolicJordanZeroRank_hyperbolicPower] <;>
    simp [
      heADC2025NonDyadicSymbolicJordanZeroRank,
      HeADC2025NonDyadicJordanAtom.jordanZeroRank]
  all_goals omega

/-- The first-column unit rows are wholly scale zero in even rank. -/
theorem heADC2025NonDyadicEvenFirstUnitRow_jordanZeroRank
    (k : Nat) (hk : 1 ≤ k) (u : HeADC2025NonDyadicUnitClass) :
    heADC2025NonDyadicSymbolicJordanZeroRank
      (heADC2025NonDyadicEvenTableRow k .one u.toSquareClass) = 2 * k := by
  cases u <;>
    simp only [heADC2025NonDyadicEvenTableRow,
      heADC2025NonDyadicEvenHyperbolicCount,
      HeADC2025NonDyadicUnitClass.toSquareClass,
      heADC2025NonDyadicEvenTail, symbolicJordanZeroRank_append,
      symbolicJordanZeroRank_hyperbolicPower] <;>
    simp [
      heADC2025NonDyadicSymbolicJordanZeroRank,
      HeADC2025NonDyadicJordanAtom.jordanZeroRank]
  all_goals omega

/-- The first-column unit rows are wholly scale zero in odd rank. -/
theorem heADC2025NonDyadicOddFirstUnitRow_jordanZeroRank
    (k : Nat) (u : HeADC2025NonDyadicUnitClass) :
    heADC2025NonDyadicSymbolicJordanZeroRank
      (heADC2025NonDyadicOddTableRow k .one u.toSquareClass) =
        2 * k + 1 := by
  cases u <;>
    simp only [heADC2025NonDyadicOddTableRow,
      heADC2025NonDyadicOddHyperbolicCount,
      HeADC2025NonDyadicUnitClass.toSquareClass,
      heADC2025NonDyadicOddTail, symbolicJordanZeroRank_append,
      symbolicJordanZeroRank_hyperbolicPower] <;>
    simp [
      heADC2025NonDyadicSymbolicJordanZeroRank,
      HeADC2025NonDyadicJordanAtom.jordanZeroRank]

/-- The only undefined positive-rank even row at the binary boundary is
`N_2^2(1)`. -/
theorem heADC2025NonDyadicEvenBinaryRow_defined_iff
    (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass) :
    HeADC2025NonDyadicEvenRowIsDefined 1 nu c ↔
      nu ≠ .two ∨ c ≠ .one := by
  simp [HeADC2025NonDyadicEvenRowIsDefined]

/-- The even-table definedness predicate agrees with the common catalogue
predicate in every positive even rank. -/
theorem heADC2025NonDyadicEvenRowIsDefined_iff
    (k : Nat) (hk : 1 ≤ k) (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass) :
    HeADC2025NonDyadicEvenRowIsDefined k nu c ↔
      HeADC2025NonDyadicRowIsDefined (2 * k) nu c := by
  cases nu <;> cases c <;>
    simp [HeADC2025NonDyadicEvenRowIsDefined,
      HeADC2025NonDyadicRowIsDefined] <;> omega

/-- In every odd rank at least three, all eight rows are defined, agreeing
with the common catalogue predicate. -/
theorem heADC2025NonDyadicOddRowIsDefined_iff
    (k : Nat) (hk : 1 ≤ k) (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass) :
    HeADC2025NonDyadicOddRowIsDefined k nu ↔
      HeADC2025NonDyadicRowIsDefined (2 * k + 1) nu c := by
  cases nu <;>
    simp [HeADC2025NonDyadicOddRowIsDefined,
      HeADC2025NonDyadicRowIsDefined]
  all_goals omega

/-- There are exactly seven defined rows in rank two. -/
theorem card_heADC2025NonDyadicEvenBinaryDefinedRows :
    (Finset.univ.filter fun
      p : HeADC2025NonDyadicColumn × HeADC2025NonDyadicSquareClass =>
        HeADC2025NonDyadicEvenRowIsDefined 1 p.1 p.2).card = 7 := by
  decide

end Bong
