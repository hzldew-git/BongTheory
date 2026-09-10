# Trust and axiom report

The audit module prints the transitive axioms of classic-maximal existence,
the testing reduction, the local parity criteria, the proved Theorem 1.1,
both branches of the local Theorem 1.5, both v5 testing results, Lemma 7.7,
all three clauses of Lemma 7.10, Lemma 7.11, both literal-minimal endpoints,
the comparison-source regression, and the conditional Section 8 endpoints.
Expected foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The volume-minimal construction is noncomputable but proved, not a new axiom.

`HeClassicTheorem11Statement` is still a proposition-valued definition, but
the separate `he2022ClassicTheorem11` is now its proof. This corrects the old
statement-only description. The audit must inspect the proof's axioms as well
as the proposition's meaning.

The explicit arithmetic law interfaces remain visible in the
hidden-assumption report. The final v5 odd-testing and minimality endpoints do
not take a paper-specific lower-even J2 premise. A standard-only axiom set
does not discharge arbitrary theorem premises or replace source-fidelity
review.

The audit prints `he2022ClassicTheorem15_unary` and
`he2022ClassicTheorem15_allRanks`; both report only the three expected
foundational axioms. The Section 8 endpoints likewise introduce no custom
axioms, but they take `Lemma81Laws`, `SectionEightLaws`, or `Lemma83Laws` as
ordinary theorem premises. Those uninstantiated packages are a trust and
coverage boundary even when `#print axioms` is standard-only; see Report 23.

The ambient exactness, lattice misses, integral `represents_other` endpoints,
exceptional-row witnesses, unified rowwise witness, and even Theorem 1.3
literal-minimal endpoint report the same three foundational axioms. Their
explicit pair, defect, order, and nonisometry arguments are theorem premises,
not hidden axioms.

No source assertion is added as a custom axiom to bypass the obsolete Lemma
7.1(ii). The corrected v5 branches are proved from the representation
criterion and earlier checked lemmas. Kernel acceptance and semantic
correspondence are separate checks, and independent human review is pending.

Independent review distinguishes the generic proved instances
`quadraticDefectLawsOfHensel`, `hilbertSymbolLawsProved`, and
`dyadicDiscriminantClassLawsProved` from ordinary theorem premises. O'Meara
63:5 and 63:9, together with all three Proposition 2.8(ii) numerical formulas,
are now internally proved; no `HeClassicPublishedCountingLaws` interface or
caller-supplied counting premise remains.

At checkpoint `981f044`, the generic volume-order maximality theorem and both
published-table maximality endpoints compile in the canonical Classic build
and focused audit. Their selected transitive dependency reports contain
exactly `propext`, `Classical.choice`, and `Quot.sound`. No classification or
odd-testing premise is hidden in these endpoints; Report 19 records their
scope.

At code checkpoint `ea0f9f1`, the focused Proposition 8.2 audit reports no
axioms for the lower derivation, the public compatibility endpoint, or the
second sentence.  The canonical 5,016-job incremental build succeeds and the
combined imported-closure gate checks 62,655 declarations.  This empty axiom
set does not construct the four `Proposition82Laws` premises; Report 27 keeps
that arithmetic boundary explicit.

At code checkpoint `a5b50fb`, the focused even-extension audit gives an empty
axiom set for `he2022ClassicLemma83_even` and only `propext` plus `Quot.sound`
for `he2022ClassicTheorem18_even`.  The 5,017-job canonical build and
62,656-declaration imported-closure gate pass.  These facts certify the
conditional deduction, not the uninstantiated obstruction premise or the
missing odd branch; Report 28.
