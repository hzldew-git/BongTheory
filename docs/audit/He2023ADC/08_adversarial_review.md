# Adversarial review

Independent source-first review of `0aa3848` actively tested the complete
binary catalogue, parameter normalization, infinity handling, all literal
Theorem 3.6 caps, lattice-isometry directions, universe scope, nonvacuity, and
circularity. It found no semantic blocker. The candidate meets every printed
Lemma 6.8(iv) hypothesis at n=2 but is not maximal and hence is not the asserted
`N_2^4(Delta)`. The publisher proof invokes Lemma 6.7(ii), whose n>=4 premise
does not cover this case. Commit `fe2a459` records the exact negated statement
and a `Q_2` witness. This is a `SEMANTIC_MISMATCH`, while a corrected complete
classification remains `INSUFFICIENT_EVIDENCE`.

Independent review of `074f2cd` found no substantive mismatch in full
(iii) or the explicitly restricted n>=4 part of (iv). It checked same-lattice
BONG construction, internal kappa and tests, the leading-order-2 tower case,
space-only square normalization, signed full determinant, raw/capped defects,
and e=1. Five modules, entry, audit and the focused gate independently passed.
The printed (iv) includes n=2; its proof uses N_2^n(1) with n>=4. Report 25
records the earlier restricted positive result; reports 30--31 supersede its
then-open status by proving and auditing the binary counterexample.

Independent review of `b728bce` passed all four frozen new modules, entry,
full ADC audit and 16 standard-only queries for Lemma 6.8(v),(vi).
It checked actual tests, finite full signed defect, raw/capped distinctions,
normalization back to the original parameter, n=2/e=1, and the explicit
Delta-in-U convention. No blocker was found on this disclosed scope.
The connection-interrupted review was resumed and completed. Report 24
does not certify clean CI or human approval; that checkpoint supplied 4/6.

Independent review of `b624d40` found no mismatch or trust blocker for
Lemma 6.8(i)--(ii), only 2/6 clauses. It independently replayed all three
modules, 15 standard-only queries, the entry and full audit. The actual
n=2 embeddings, missing binary square model, full determinant signs and
prefix bounds, raw/capped domination, e=1 and integral-isometry conclusion
were checked. No testing table or classification law is assumed. Report 23
records the provisional verdict; clean CI for that addition is not certified.

Independent review of full Lemma 6.7 at `b0f832e` found no mismatch or
hidden assumption. It checked the actual named lattice representation,
the literal central-condition contradiction, alpha discreteness, both
endpoint caps and strict uncapping. The binary Delta and e=1 cases are
included, while the undefined binary square model remains excluded.
The source, five queries, entry and full audit passed independent cached
replay. Report 22 records the provisional verdict and unsigned human cards.

The aggregate independent Lemma 6.6 review at `cd8ecbd` found no mismatch
or hidden law. It checked full capped-trigger bounds, arbitrary even next
order, raw-defect class selection, the hypotheses of endpoint-tower
classification, the same-parameter exactly-one exclusion and actual-target
isometry transport. The binary Delta and e=1 cases are included; the
binary square second model is correctly absent. All three source modules,
12 queries, entry and full audit passed independent cached replay. See
report 21; no human approval or clean-release certificate is implied.

Independent frozen-code review of Theorem 6.1 at `272d810` found no
mismatch, hidden target assumption or circularity. It checked the arbitrary
lattice endpoint, internal BONG construction, maximal-superlattice volume
index argument, the direction of both actual ambient embeddings, all four
normalized ambient rows, and n=2/e=1. All three modules, 12 queries, entry
and full audit passed independent cached replay. The needed `9fb5f14`
concrete-test support was separately reviewed and unchanged. Report 19
records the provisional verdict and unsigned human approval fields.

The independent frozen-code review of Lemma 6.5(i) at `2a5d3af` and (ii)
at `9d6a4b` found no mismatch or circularity. It checked exact pointwise
failure, both actual target classes, capped rather than raw defect bounds,
the empty target head and omitted secondary candidate at n=2, and e=1.
Both files, eight queries, the canonical entry and full audit passed the
reviewer's separate cached replay. Full result-level evidence is in report
18; this is not human approval or a clean-environment certificate.

An independent read-only AI reviewer checked each frozen Lemma 6.4 clause
through final code `d94cc797ad8ed83c53447c139b496d5a2ca8f4fb`. It confirmed
all four clauses, the five actual tests, derived profiles and ranks, raw
defects, both kappa columns, binary/e=1/codimension-one boundaries, and
absence of circularity. It independently recompiled every new module with
queries, each frozen entry and complete audit; all twenty new axiom sets
were standard-only. It also checked that earlier clauses were unchanged at
the final commit. Combined local proof coverage: `FULLY_FORMALIZED`;
semantics: `PROVISIONAL_MATCH`. See report 17. Clean-kit CI and human
sign-off remain separate, unfulfilled gates.

The separate reviewer audited the frozen dyadic Proposition 4.16 code at
`5fff59784a0a3dd4442405f204519c36e0a8e468` after independently extracting
the published scope. No semantic blocker was found. Both directions of the
exception, integral rather than only ambient isometry, the exact half-scaled
Gram matrix, form rather than vector scaling, and all public premises were
checked. The reviewer reran the module, entry and complete audit successfully.
The dyadic restriction is `FULLY_FORMALIZED` / `PROVISIONAL_MATCH`; the whole
published proposition remains `SPECIAL_CASE_ONLY`. See report 16.

The focused independent review of Proposition 4.13 at `9c432a6` found no
blocking mismatch. It checked all three clauses, the n=3 and e=1 boundaries,
the capped rather than raw defect, finite rational embedding into `WithTop`,
all derived auxiliary data, and absence of circularity. Report 15 records
the evidence and remaining human-review and clean-build obligations.

Primary risks are omitting the ambient-space representation hypothesis,
confusing local with global `n`-ADC, replacing integral representation by space
representation, and overstating the dyadic specialization. Boundary ranks and
the preservation of rank when passing to maximal over-lattices require explicit
checking.

The volume proof was checked for a potentially circular converse. It chooses
a maximal integral superlattice `P` of the arbitrary lattice `L`, identifies
`P` with the independently proved maximal reference `M`, and uses equal
volume to prove `L=P`. It does not assume that `L` was maximal.

The predicate `HeADCMaximalProfileCriterion` was expanded for inspection:
its reference BONG selects the reference space, lattice and length. Its
conclusion still quantifies over every good BONG of the arbitrary input
lattice. The new endpoints do not have a classification-law hypothesis.

An independent read-only AI review of code snapshot
`2a151a8024d10ae094df958cd3626dbd13c447c2` compared the publisher's
pages 994--995 with the expanded declarations. It confirmed both logical
directions, all ten displayed order profiles, the signed odd-row parameters,
rank-one inclusion in the first column, and exclusion of the undefined
binary second-column square row. Its live type and axiom inspection found
only the three disclosed foundational axioms.

The review identified a correspondence gap: the criteria use concrete
half-hyperbolic extensions, whereas Definition 4.1 uses chosen diagonal
`W` spaces and their chosen maximal `N` lattices. Explicit whole-row
transport, generic-row parameter specializations, and the named-lattice
existence component of Remark 4.10 remain to be assembled at this snapshot.
Thus these are complete concrete-model proofs, not yet fully connected
paper-definition endpoints. No sign error or false converse was found.

That finding applies to checkpoint `2a151a8`. The subsequent checkpoint
`976883e6cda7c17402c4c1f0bc768db555460eae` adds the whole-row transport
and all thirteen published-family endpoints. The follow-up independent
review found no blocking semantic issue in all thirteen public endpoints.
It confirmed the named `W/N` linkage, the source's standing integrality
convention, the rank boundaries, finite-defect arithmetic and absence of
undischarged auxiliary-unit or project-law premises. It recommends
`FULLY_FORMALIZED` coverage for these two lemmas with `PROVISIONAL_MATCH`
semantics pending human confirmation. Its scope is recorded in report 14.

The rank-one portion of Lemma 4.9(ii) is closed by report 50. Remaining
small-rank and unrestricted-field checks stay separately listed. This AI
review is not human author or expert sign-off.

The downstream audit of Theorem 7.1 found that its published statement is
not refuted by the Theorem 6.2 counterexample, but its printed proof is
incomplete. At `n=3`, the proof lists only the first-discriminant exceptional
lattice and omits the independently realized second-discriminant boundary.
The formal repair is noncircular: it proves a corrected exhaustive three-way
binary classification, proves the omitted class is not 3-ADC using the
representation criterion, and uses only the valid stable Theorem 6.2 branch
when `n>=5`. Report 35 records the exact theorem and remaining human-review
questions.

The follow-up source-first audit at `2417a4f` covers Theorem 7.4 and Lemmas
7.5--7.13. It found complete proof-supported correspondences for Theorem 7.4
and Lemmas 7.5--7.10 and 7.12, a deliberately partial odd-valuation endpoint
for Lemma 7.11, and a new quantifier mismatch in Lemma 7.13. The latter proof
rules out simultaneous representation of two targets but does not establish
their separate failures; the downstream necessity proof needs only the weaker
disjunction. Report 36 records the exact statements and open human-review
questions. Theorem 7.2, Remark 7.3, and results from Lemma 7.14 onward have
not yet received this downstream audit.

Report 37 supersedes only the partial-coverage conclusion for Lemma 7.11.
At `832d10c`, the unit row was added with its own central-defect estimate and
prefix non-representation proof, and the two normalized rows were combined
into one all-parameter endpoint. The proof does not import a caller-supplied
classification law or defect-`2e-1` unit. This does not change the independent
Lemma 7.13 quantifier mismatch or the ten Section 7 items pending at that
checkpoint.

Report 38 audits Lemma 7.14 against p. 1013 of the publisher PDF. The proof
does not identify the two ambient columns; it uses their square-related
determinants only to transfer parity. It also proves that all orders before
the last have even total from Theorem 7.4, instead of assuming the displayed
congruence in (7.3). No parity converse, field-uniformizer normalization, or
last-order dichotomy is left as caller data. Nine Section 7 items remain
pending, independently of the Lemma 7.13 mismatch.

Report 39 audits Lemma 7.15 against pp. 1013--1014. The public theorem keeps
the source's two invariants and derives the full order sequence using ambient
determinant parity. In the nonmaximal branch it verifies each of Beli Theorem
3.1(i)--(iv), including the actual prefix map at the sole alpha-sum trigger;
in the maximal branch it derives `O`-maximality before invoking uniqueness.
No uniqueness trigger, alpha profile, classification law, or maximality fact
is assumed. Eight Section 7 items now remain pending, independently of the
Lemma 7.13 mismatch.

Reports 40--42 audit the next four numbered items. Definition 7.16 does not
silently assert existence, and Remark 7.17 constructs both its finite index
and normalized ambient row. Lemma 7.18 derives the forbidden endpoint via an
actual named maximal-lattice profile. Lemma 7.19 derives its sharp-domain and
odd-defect data, proves `alpha_n=1`, and identifies both explicit bases with
the named `N` lattices before transporting `n`-ADC. No definitional equality
between explicit and chosen maximal models is assumed. Four Section 7 items
now remain pending, independently of the Lemma 7.13 mismatch.

Report 43 audits Lemma 7.20 against pp. 1015--1016. The maximal rows use the
actual profiles from Lemma 4.12. In the lower rows, all four column choices
are derived from determinant--Hasse classification after common-tower
cancellation; the Hilbert equation is not assumed as an ambient-isometry
law. The missing determinant line is proved to have square class `omega*c`,
and Lemma 7.19 supplies the actual named product. Existence of every required
odd-defect unit is constructed from the dyadic defect spectrum. Lemma 7.18
proves the converse exceptional case, yielding an exact definedness
biconditional. Three Section 7 items now remain pending, independently of the
Lemma 7.13 mismatch.

Report 44 audits Theorem 7.2 against pp. 1006 and 1016. The intrinsic theorem
does not depend on a chosen representative system, while a separate theorem
reconstructs the exact finite family printed by the publisher. Unit-square
normalization is transported through integral isometries in both columns.
For the overlap assertion, the proof compares the Lemma 7.19 penultimate
order with every Proposition 4.13 maximal row and eliminates three rows; it
does not assume the desired second-column model. Remark 7.3 and Corollary
7.21 remain pending, independently of the Lemma 7.13 mismatch.

Report 45 audits every sign, scale, exponent, factor order, and lattice in
Remark 7.3 against p. 1006. In particular, the negative exponents `-l` and
`-2l` are not replaced by absolute values; the second formula retains the
external `delta#`; and the third formula is ordered as the scaled `A` block
followed by `<Delta epsilon>`. The proof identifies arbitrary admissible
binary shears integrally and uses maximal-lattice uniqueness only after an
ambient isometry is derived. Corollary 7.21 remains pending, independently
of the Lemma 7.13 mismatch.

Report 46 supersedes that final pending conclusion. The Corollary 7.21 index
is not merely a list with the right cardinality: every model has the required
rank and ADC property, every arbitrary qualifying lattice maps to a model,
and Lemma 7.15 plus ambient-row uniqueness proves irredundancy. The maximal
overlap is placed in the maximal summand and proved to be the only maximal
lower row. The resulting `(4e+3)|U|` and `(4e-1)|U|` counts are unconditional.
Report 57 later proves the final substitution `|U|=2(N p)^e` from the
principal-unit filtration and representative equivalence. The reviewer must
still check its normalization and proof correspondence; a standard-only axiom
report alone does not establish semantic fidelity. Lemma 7.13's independent
source mismatch is unchanged.

Report 50 audits the unary boundary directly against Definition 4.1,
Proposition 4.2, Remark 4.3, and Lemma 4.9(ii). It checks that there is no
second unary column, that every rank-one ambient space is represented exactly
once by the finite normalized parameter family, and that `W_2^3(c)` is the
actual excluding witness. The deletion theorem quantifies over every index
and supplies an integral witness representing all other rows. The exact
`2|U|` count is unconditional; only the publisher's `4(N p)^e` conversion
uses the disclosed O'Meara premise. The local kernel and transitive axiom
checks pass, while clean-kit CI and human review remain pending.

Report 55 tests the main ways a conditional Lemma 2.2 formalization could
overstate the source. The returned object is an actual submodule of the
original global space, not an unrelated diagonal model; dimensions are
preserved by the indexed diagonal list; scalar extension is implemented via
tensor product; and cancellation removes the same descended line on both
sides. Report 56 then checks the formerly open base case: density comes from
the actual finite-completion embedding, the selected global quadratic value
is proved nonzero, and square-equivalence is converted into an actual scaled-
line isometry. Square-class openness is proved by the inverse function theorem
rather than hidden in a project axiom. Human source comparison remains open.

Report 67 tests the principal ways the dyadic Lemma 4.6 specialization could
be weaker than the publisher statement. Each part-(i) result includes one
positive and one negative actual-lattice conclusion; neither is reduced to
ambient representation. Part (ii) ranges over an arbitrary integral target,
not only a named maximal row. Both possible source columns and both parities
are present, and the exceptional target is the opposite column. The rank
indices of the large rows are transported by explicit finite-family casts.
The remaining review questions are the determinant square-class convention,
the equal-rank diagonal/isometry bridge, and human confirmation that the even
definedness boundary matches the publisher's notation.

Report 68 checks the same failure modes in the non-dyadic interface. The
binary omitted row is excluded by the standing table-definedness premise;
`nu.other` is definitionally the paper's `3-nu`; and the large rank-`n+2` row
is proved defined from `n>=2`. Report 70 removes the ambient exactly-one fields:
Lemma 4.5 is derived from explicit determinant/Hasse classification and four
codimension criteria. Report 71 additionally removes the target-pair and
Proposition 4.2(iii) fields. It checks all omitted-row domains, both directions
of every Lemma 4.4 biconditional, the negative exception, and the uniqueness
quantifier in Proposition 4.2(iii). Reviewers must still validate the concrete
non-dyadic determinant--Hasse--Hilbert package and both representation
transport orientations.

Report 73 tests the former class-number-one regularity shortcut in Section 8.
The proof no longer receives `HasClassNumberOne M -> IsNRegular M n` as a
field. It must obtain one genus representative that globally represents each
locally represented target, apply class number one to that representative,
and transport representation in the source-lattice direction. The target
rank and integrality hypotheses and the universal quantifier over finite
places remain explicit. The theorem is nonvacuous only after a concrete
number-field model supplies the genus-lifting law; that construction and
human confirmation of the genus orientation remain open.

Report 74 adversarially separates the two directions of Theorem 1.5(i).
Maximal sufficiency may no longer enter as the finished `IsNADCAt` predicate:
the proof must extend each integral target to a maximal one, represent that
extension, and compose representations. The reverse direction remains the
explicit place where Proposition 4.15 and Theorems 5.1, 6.1, and 7.1 must be
instantiated. Reviewers must still check that the ambient-transport clause of
the extension law really expresses an extension on the same local quadratic
space and that the rank hypotheses match localization.

Report 75 tests the former Theorem 8.2 shortcut. The indefinite branch must
now exhibit a single rank-`n` lattice, show that every genus representative
which represents it lies in the base spinor genus, and only then use the
one-class theorem to obtain integral isometry. Reviewers must verify the
orientation of `inSpinorGenus M' M`, the definite/indefinite split, and the
rank and signature hypotheses of Meyer, Xu, and O'Meara 104:5.
