# Trust and axiom report

The audit module prints the transitive axioms of classic-maximal existence,
the testing reduction, the local parity criteria, the proved Theorem 1.1,
both branches of the local Theorem 1.5, the even testing result, Lemma 7.7,
all three clauses of Lemma 7.10, the even literal-minimal endpoint, and the
source refutation.
Expected foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The volume-minimal construction is noncomputable but proved, not a new axiom.

`HeClassicTheorem11Statement` is still a proposition-valued definition, but
the separate `he2022ClassicTheorem11` is now its proof. This corrects the old
statement-only description. The audit must inspect the proof's axioms as well
as the proposition's meaning.

The explicit arithmetic law interfaces and the lower-even J2 premise of the
qualified odd testing result remain visible in the hidden-assumption report.
A standard-only axiom set does not discharge arbitrary theorem premises or
turn a special case into the full publisher statement.

The audit prints `he2022ClassicTheorem15_unary` and
`he2022ClassicTheorem15_allRanks`; both report only the three expected
foundational axioms. This does not create the still-absent number-field layer.

The ambient exactness, lattice misses, integral `represents_other` endpoints,
exceptional-row witnesses, unified rowwise witness, and even Theorem 1.3
literal-minimal endpoint report the same three foundational axioms. Their
explicit pair, defect, order, and nonisometry arguments are theorem premises,
not hidden axioms.

No source assertion is added as a custom axiom to bypass the Lemma 7.1(ii)
obstruction. Kernel acceptance and semantic correspondence are separate
checks, and independent human review is still pending.

Independent review distinguishes the generic proved instances
`quadraticDefectLawsOfHensel`, `hilbertSymbolLawsProved`, and
`dyadicDiscriminantClassLawsProved` from the still-undischarged
`HeClassicPublishedCountingLaws`. The latter is a mathematical premise of the
displayed numerical-count formulas, even when their axiom sets are standard.

At checkpoint `981f044`, the generic volume-order maximality theorem and both
published-table maximality endpoints compile in the canonical Classic build
and focused audit. Their selected transitive dependency reports contain
exactly `propext`, `Classical.choice`, and `Quot.sound`. No classification or
odd-testing premise is hidden in these endpoints; Report 19 records their
scope.
