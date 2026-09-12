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

At code checkpoint `7c615fc`, the local-to-global derivation and its public
compatibility endpoint have empty axiom sets, while the full conditional
Theorem 1.9 reports only `propext`.  The canonical 5,018-job build and the
62,668-declaration imported-closure gate pass.  The explicit
`strong_approximation` premise is still a mathematical implementation
boundary and is not discharged by these axiom reports; Report 29.

At code checkpoint `46bf941`, the global Theorem 1.5 and conditional Theorem
1.9 endpoints have empty axiom sets after replacing the discriminant
biconditional by a one-way law.  The derived ramified-place witness and
Theorem 1.7 use only the three expected foundational axioms.  The canonical
5,019-job build and 62,676-declaration imported-closure gate pass; Report 30.

At code checkpoint `83aec42`, the finite-place branch derivation, its
compatibility theorem, and the full conditional Theorem 1.9 use only
`propext`, `Classical.choice`, and `Quot.sound`.  The focused build completes
5,000 jobs, the canonical build completes 5,020 jobs, and the imported-closure
gate checks 62,689 declarations; Report 31.

At code checkpoint `2293431`, the concrete number-field
discriminant--ramification equivalence, its even-discriminant witness,
ramification-index positivity, and all place-bridge constructions use only
`propext`, `Classical.choice`, and `Quot.sound`. The combined canonical and
focused audit build completes 5,660 jobs, and the imported-closure gate checks
62,721 declarations; Report 32.

At code checkpoint `89714ff`, the unrestricted Theorem 1.7 endpoint is
removed.  `he2022ClassicTheorem17_even` and the parity-independent
`he2022ClassicTheorem17_of_localAdjacentDefectsLarge` use only `propext`,
`Classical.choice`, and `Quot.sound`.  The combined canonical and focused
audit build completes 5,665 jobs; all 30 policy tests pass; the scanner checks
2,796 tracked Lean sources; and the full imported-closure gate reports
`AXIOM_GATE_PASS: 70695 declarations checked`.  These checks certify the
scope-safe deductions, not the absent odd coefficient calculation; Report 33.

At code checkpoint `48956eb`, the height-one-spectrum identification derives
the older discriminant bridge, including primality and coverage, using only
`propext`, `Classical.choice`, and `Quot.sound`. The combined canonical and
focused audit build completes 5,665 jobs; all 30 policy tests and the
2,796-source scanner pass; and the full imported-closure gate reports
`AXIOM_GATE_PASS: 70718 declarations checked`. The remaining equivalence and
compatibility fields are ordinary premises of a future concrete global model;
Report 34.

At code checkpoint `129f19e`, the canonical number-field global-data adapter
defines the dyadic predicate, ramification index, and discriminant proposition
from the height-one spectrum. Its identification, bridge, and complete
Section 8 constructor use only `propext`, `Classical.choice`, and `Quot.sound`.
The focused build completes 5,646 jobs and the combined canonical/audit build
completes 5,667 jobs. All 30 policy tests pass, the scanner checks 2,798 Lean
sources, and the focused imported-closure gate checks 62,790 declarations.
This removes the three compatibility premises but does not construct the
remaining global lattice and localization laws; Report 36.

At code checkpoint `6d5c434`, the finite-prime order-scaling theorem,
relative ramification positivity, absolute ramification tower, and partial
Lemma 8.1 adapter use only `propext`, `Classical.choice`, and `Quot.sound`.
The focused build completes 5,651 jobs and the combined canonical/audit build
completes 5,674 jobs. All 30 policy tests pass, and the scanner checks 2,800
Lean sources. The focused imported-closure gate checks 62,819 declarations.
These reports do not prove the two remaining input fields or extend the
coefficient type from `Kˣ` to the completion; Report 38.

At code checkpoint `82a2b04`, the map between finite completions, its
dense-subfield compatibility, and its continuity use only `propext`,
`Classical.choice`, and `Quot.sound`. Scoped instances additionally allow Lean
to infer that the upper completion is finite-dimensional over the lower one.
The focused build completes 5,651 jobs and the combined canonical/audit build
completes 5,674 jobs. All 30 policy tests pass, the scanner checks 2,800 Lean
sources, and the focused imported-closure gate checks 62,830 declarations.
This proves completion-extension infrastructure, not the outstanding
completed-field valuation or defect laws; Report 39.

At code checkpoint `a5c1002`, `completionMap_valuation`,
`completionAdicOrder_liesOver`, and the completed Lemma 8.1 adapter use only
`propext`, `Classical.choice`, and `Quot.sound`. The focused build completes
5,651 jobs and the combined canonical/audit build completes 5,674 jobs. All
30 policy tests pass, the scanner checks 2,800 Lean sources, and the focused
imported-closure gate checks 62,857 declarations. Lemma 8.1(i) is now proved
at completed-field scope; defect scaling and good-BONG transfer remain
explicit; Report 40.

At code checkpoint `c6d22da`, `completionQuadraticDefect_scale`,
`completionQuadraticDefectQ_scale`,
`completionGoodBONGCoefficients_map`, and `completionLemma81Laws` use only
`propext`, `Classical.choice`, and `Quot.sound`. The focused build completes
5,651 jobs and the canonical paper plus all eight manifest-listed audits
complete 5,674 jobs. All 30 policy tests pass, the scanner checks 2,800 Lean
sources, and the focused imported-closure gate reports
`AXIOM_GATE_PASS: 62850 declarations checked`. This closes every arithmetic
field of the finite-completion Lemma 8.1 adapter at coefficient-criterion
scope. It does not discharge the global lattice/localization or orthogonal-
basis identification boundary; Report 41.

At code checkpoint `e3b18be`, the concrete finite-residue-field and local-
compactness construction, the normalized dyadic context, all bridges between
the direct completion invariants and BONG invariants, both directions of the
good-BONG coefficient criterion at realization level, and the mapped upper
realization use only `propext`, `Classical.choice`, and `Quot.sound`. The
focused build completes 5,653 jobs and the canonical paper plus all eight
manifest-listed audits complete 5,676 jobs. All 30 policy tests pass, the
scanner checks 2,802 tracked Lean sources, and the focused imported-closure
gate reports `AXIOM_GATE_PASS: 62917 declarations checked`. These checks prove
existence of an actual upper realization; they do not prove that it is the
preassigned localized scalar-extension lattice in v5 Lemma 8.1(iii). The
carrier gap is semantic and remains visible in Report 42.

At packaged source-and-audit commit `ab1901a`, a resumed new-extraction build
completes 5,682 jobs, all nine manifest-selected checks pass separately, and
the enforcing imported-closure gate reports
`AXIOM_GATE_PASS: 62917 declarations checked`. The allowed set remains exactly
`propext`, `Classical.choice`, and `Quot.sound`; Report 43 records the archive,
payload, dependency, and Windows-verifier receipt. This mechanical result does
not change either v5 semantic blocker.
