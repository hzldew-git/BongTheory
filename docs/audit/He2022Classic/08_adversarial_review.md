# Adversarial review

Primary risks are confusing norm integrality with scale integrality, reversing
the over-lattice inclusion in maximality, omitting source integrality from
universality, and calling an abstract test family minimal. The BONG criteria
must separately check parity, the theorem's exclusion of ranks `m=n+1` and
`m=n+2`, and residue characteristic two. In the statement transcription,
paper adjacent index `j` is Lean index `j-1`; the lower bound `j >= n+2` in the
odd upper branch is therefore Lean bound `n+1 <= j.val`.

The current code supplies both directions of Theorem 1.1 and explicitly
eliminates low source ranks. This is no longer a statement-only project. The
earlier unary gap in Theorem 1.5 is closed by a separate proof: classic
1-universality is first converted to scalar universality, and the actual
finite alpha-candidate set is bounded term by term. The remaining limitation
is global, not unary: Section 8 deductions now exist, but their number-field
localization, extension, and strong-approximation inputs are uninstantiated
proof-data packages and must not be reported as unconditional theorems. The
discriminant--ramification theorem itself is concrete after Report 32.

There is also a source-level parity failure. V5 Corollary 6.3 and Lemma 8.3
are stated without restricting `n`, but each proof assumes without a supplied
reduction that `n` is even. The even and odd clauses of Theorem 1.1 have
different terminal hypotheses. The code proves the even Corollary 6.3 and
constructs an `e=2`, `n=3` counterexample to its odd conclusion. The
downstream Lemma 8.3/Theorem 1.8 step remains conditional and requires a new
odd proof or a parity restriction. See Reports 24 and 26.
Report 28 implements the conservative parity restriction in Lean: only the
`n >= 2`, even-rank Lemma 8.3 and Theorem 1.8 endpoints exist.  Reviewers
should treat any downstream use in odd rank as unsupported by this project.
Theorem 1.7 has the same source-evidence problem: v5 calculates only the even
case and calls the odd case similar. Report 33 therefore leaves only an
`n >= 2`, even-rank source-facing endpoint. Its parity-independent logical
tail is available with the omitted local-defect calculation as an explicit
premise and must not be mistaken for an odd-rank proof.

The broader Lemma 7.1(ii) disjunction in the publisher comparison copy fails
when `e>1`; the repository retains its checked refutation. Author-corrected v5
instead restricts part (ii) and adds the `C_1(1)` exceptional test. The new
proof keeps those branches explicit and promotes odd testing only through the
v5 statement. See `SOURCE_DELTA.md` for the exact witnesses and scope.

Constructed testing rows, their integrality, cardinalities of an index type,
testing sufficiency, and proper-subset minimality are distinct claims. The
two parity branches now have separate proofs of testing sufficiency and
rowwise deletion-minimality, and the numerical counts are proved internally.
These local results and the conditional Section 8 logic are not a certificate
for concrete global number-field conclusions or for semantic agreement
without human review.

For Proposition 8.2, a proof that merely stores local `n`-universality as a
field would circularly reproduce the proposition.  Report 27 removes that
field and checks the published route through an arbitrary local target,
positive-definite globalization, global representation, localization, and
equivalence transport.  Reviewers must still reject any claim that the
abstract globalization law is already a concrete O'Meara 81:14 instance.

The same circularity test applies to Theorem 1.9: a field asserting global
universality from local universality would merely restate the target.  Report
29 replaces it by target-wise rank/integrality localization and an explicit
strong-approximation representation law.  Reviewers must still require a
concrete number-field instance of that law.

The discriminant interface is also checked for excess strength.  Report 30
separates the necessity-side implication and derives the ramified-place witness
by contradiction.  Report 31 reveals and separately names the converse needed
by the unary sufficiency branch. Report 32 proves both directions for actual
prime ideals and transports them through an explicit place bridge. Reviewers
must therefore check the bridge, rather than demand new arithmetic axioms.
Report 34 removes the bridge's separate primality and coverage fields by
deriving them from an equivalence with the standard height-one spectrum.
Report 36 removes the dyadic, ramification, and discriminant compatibility
statements from the canonical interface by defining them from the spectrum.
Reviewers must still inspect the place equivalence and the actual global
lattice/localization model.

Report 38 lowers part of the finite-extension interface without overstating
its domain. Reviewers should verify that `adicOrder_liesOver` concerns
`x : Kˣ`, whereas v5 Lemma 8.1(i) quantifies over the completed local field.
The adapter correctly keeps defect scaling and good-BONG transfer as inputs.
Any claim that Report 38 proves all of Lemma 8.1 would be a scope error.

Report 39 closes the structural gap that `K_p` and `L_P` must be linked by an
actual finite continuous extension. Reviewers should still reject an argument
that infers valuation scaling merely from continuity or density: the map is
proved, but its discrete-valuation compatibility on arbitrary completion
elements is not. Likewise, no quadratic-defect or lattice scalar-extension
claim follows automatically from the new algebra instances.

The same anti-circularity test is applied to the finite-place half of Theorem
1.9.  Report 31 removes the former field that asserted the complete quantified
local conclusion and replaces it by the three source branches.  Reviewers
must still verify concrete number-field/completion instances of those branch
laws and their bridge to the local BONG criteria.
