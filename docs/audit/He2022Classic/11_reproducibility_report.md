# Reproducibility report

Run `lake build Bong.Papers.He2022Classic` and then
`lake env lean BongTest/He2022ClassicAudit.lean`. The independent Review Kit is
generated from `papers/he2022classic/paper.json`. The author-corrected v5
source is excluded; its manifest filename and hash identify the artifact
reviewers must obtain independently.
The audit output must distinguish the proposition-valued definition from the
proof `he2022ClassicTheorem11`, and print the latter's transitive axioms.
The unary and all-ranks local Theorem 1.5 endpoints, Lemma 7.7, all three
clauses of Lemma 7.10, Lemma 7.11, both literal-minimal endpoints, the v5
Lemma 7.1 branches, and the comparison-source regression are audited too.
The actual finite-completion arithmetic for Lemma 8.1(i)--(ii), the
proof-supported good-BONG realization for part (iii),
the conditional Proposition 8.2, Theorem 1.5 global deduction, Theorem 1.9,
and the even-rank Lemma 8.3, Theorem 1.7, and Theorem 1.8 endpoints are checked
and have their axioms printed. The parity-independent logical tail of Theorem
1.7 is audited separately with its local-defect premise visible.

Current code checkpoint: `e3b18be95c813885a421b83fe0a0148d6b561ae0`
on the local v5 branch. Lean: 4.32.1; dependency versions: the committed
`lake-manifest.json`. Reproducibility status for this exact checkpoint:
`FRESH_EXTRACTION_RESUMED_LOCAL_PASS` at packaged source-and-audit commit
`ab1901a`; see Report 43. Successful local verification is not GitHub CI or
clean-extraction evidence for a later release commit.

On 10 September 2026, the exact source-only Review Kit for the older
`b8c379a` commit passed
structural verification of 1,993 payload files, a fresh-extraction 5,028-job
build, `BongTest.He2022ClassicAudit`, and the enforcing
`BongTest.PaperAxiomGate` over 62,622 declarations. Report 25 fixes the archive
hash and complete receipt. This is kernel and local-environment evidence only;
that archive predates the subsequently proved Corollary 6.3 odd
counterexample. It remains valid evidence for its exact older commit, but it
is not a current semantic or complete-paper certificate.

## Subsequent clean-kit CI checkpoint

[Paper Review Kits run 33929872783](https://github.com/hzldew-git/BongTheory/actions/runs/33929872783),
Classic job `101206371200`, completed successfully at 03:05:13 UTC on
5 September 2026. Its actual packaged source is merge-test commit
`6bf3bdf8bd272109e898335683f05bb76664330c`, whose tree was independently
checked equal to branch commit `db0398506b2e242288bc979217972c6a1d175674`.
The inspected log records a successful 5010-job build and the expanded Classic
audit, including the full local Theorem 1.1, the then-restricted Theorem 1.5,
literal Lemma 7.1(ii) refutation, conditional odd testing and full even testing.

The separate source-only artifact is
[`paper-review-he2022classic-6bf3bdf8bd272109e898335683f05bb76664330c`](https://github.com/hzldew-git/BongTheory/actions/runs/33929872783/artifacts/9961760603),
ID `9961760603`, 5800025 bytes. It is a 30-day workflow artifact, not a
permanent tagged release. Its green build does not complete the remaining
odd testing, source-resolution or global obligations.

This checkpoint predates the new enforcing transitive-axiom gate. Its
individually inspected axiom reports are not a successful run of that later
gate, nor a certificate for a newer source revision. See the deployment
correction in `../HePaperDeploymentCheckpoint-20260905.md`.

The current checkpoint includes the unary branch, a complete local n >= 1
dispatcher, corrected v5 Lemma 7.1, Lemma 7.7, complete Lemmas 7.10--7.11,
both literal-minimal halves of Theorem 1.3, and the conditional Section 8
logic of Reports 23 and 27--36, with the v5 source failure separated in
Reports 24 and 26. The exact local Review Kit in Report 25 predates later
formalization work. A newly generated fresh-extraction kit and GitHub artifact
for the eventual release commit are still required; the historical artifacts
below do not certify that future commit.

## First clean-kit checkpoint with enforced dependencies

[Run 33942437722, Classic job 101242489505](https://github.com/hzldew-git/BongTheory/actions/runs/33942437722/job/101242489505)
completed successfully on actual merge-test source
`c82668b97ed80f0cead4493206cb6483c4e8d77d`. Its tree
`821e857945c1f9a3b556d877075e67c28524866a` was checked equal to head
`f6f7485b6a3acabedbec5a7facce46f8ee7365ab`. The inspected log verifies
1967 payload hashes, a 5004-job build and the real `PaperAxiomGate`
success marker on 61,515 declarations. Its nonfatal generated-driver lint
warnings are not proof or gate failures.

[Independent Classic download](https://github.com/hzldew-git/BongTheory/actions/runs/33942437722/artifacts/9962386381),
artifact `9962386381`, 5802993 outer ZIP bytes. The inner source ZIP
SHA-256 is `079D6DFCFB9982415F0D3271C29C6AF0E2C560111B79FB08828D6131C4F97987`.
This certifies the new gate for this fixed kit, not complete paper coverage,
human semantic approval, the separate whole-production CI or a permanent
release. The source discrepancy and odd/global obligations are unchanged.

## Even-extension scope checkpoint

Code commit `a5b50fbe9fa7648a3a78e6de3cdaf94b46732540` removes the
unrestricted Lemma 8.3 and Theorem 1.8 endpoints and adds their explicit
`n >= 2`, even-rank versions.  The focused 5,000-job build, direct audit,
5,017-job canonical build, 30 policy tests, 2,791-source scan, and
62,656-declaration imported-closure gate pass locally.  Report 28 records the
source-fidelity reason.  Exact clean-kit verification remains pending.

## Theorem 1.9 strong-approximation checkpoint

Code commit `7c615fcb35e2d8e85d9ab5883019c1505d27f132` replaces the
final local-to-global universality field by lower localization and
strong-approximation inputs.  The focused 5,000-job build, direct audit,
5,018-job canonical build, 30 policy tests, 2,792-source scan, and
62,668-declaration imported-closure gate pass locally.  Report 29 records the
remaining concrete arithmetic boundary.  Exact clean-kit verification is a
later gate.

## Discriminant/ramification direction checkpoint

Code commit `46bf941e3edc83b7dc2fb115bdd8b0215a73653f` replaces the unused
full biconditional by the direction used in the global proofs and derives the
ramified dyadic-place witness.  The focused 5,000-job build, direct audit,
5,019-job canonical build, 30 policy tests, 2,794-source scan, and
62,676-declaration imported-closure gate pass locally. Report 30 records the
then-remaining concrete number-field premise, later closed by Report 32. Exact
clean-kit verification is a
later gate.

## Theorem 1.9 finite-place checkpoint

Code commit `83aec42841ecb1b75b010ac15fddd72555939d36` replaces the final
all-finite-places universality field by the three local branches used in v5
and derives their quantified conclusion.  The focused 5,000-job build, direct
audit, 5,020-job canonical build, 30 policy tests, 2,794-source scan, and
62,689-declaration imported-closure gate pass locally.  Report 31 records the
remaining concrete local arithmetic interfaces.  Exact clean-kit verification
is a later gate.

## Proposition 8.2 derivation checkpoint

Code commit `ea0f9f1516d41d18c87b8c0ee0757fd8d5e58e1b` replaces the final
Proposition 8.2 field by four lower globalization/localization inputs.  The
focused 5,000-job build, canonical 5,016-job build, direct audit, 30 policy
tests, 2,790-source unfinished-proof scan, and a 62,655-declaration combined
axiom gate pass locally.  Report 27 records the semantic boundary.  This is
not yet a fresh-extraction Review Kit receipt or GitHub result for that exact
commit.

## Concrete number-field discriminant checkpoint

Code commit `229343195a243e1f2f946a8c5827d2610fb51f61` proves the
discriminant--ramification equivalence for actual number fields, its two
directed consequences, the even-discriminant ramified-prime witness, and
ramification-index positivity. It also constructs the abstract Section 8 laws
from a typed place bridge. The combined canonical and focused audit build
completes 5,660 jobs, all 30 policy tests pass, the scanner checks 2,795
tracked Lean sources, and the imported-closure gate reports
`AXIOM_GATE_PASS: 62721 declarations checked`. Report 32 records the exact
boundary. Fresh-extraction Review Kit verification is still pending.

## Theorem 1.7 even-scope checkpoint

Code commit `89714ff139144299a56853131c23725d1b426374` removes the
unrestricted source-facing Theorem 1.7 endpoint. It adds
`he2022ClassicTheorem17_even`, requiring `n >= 2` and `Even n`, and separates
the parity-independent final contradiction as
`he2022ClassicTheorem17_of_localAdjacentDefectsLarge` with the missing local
coefficient/defect calculation explicit. The combined canonical and focused
audit build completes 5,665 jobs, all 30 policy tests pass, the scanner checks
2,796 tracked Lean sources, and the full imported-closure gate reports
`AXIOM_GATE_PASS: 70695 declarations checked`. Report 33 records the exact
scope. Fresh-extraction Review Kit verification is still pending.

## Height-one-spectrum bridge checkpoint

Code commit `48956eb32d2aa1ba7220ef5d9fb2c8c06904b0c8` derives
`NumberFieldDiscriminantBridge` from an equivalence with the standard
height-one spectrum and three arithmetic compatibility statements. Primality
and dyadic-prime coverage are proved. The combined canonical and focused
audit build completes 5,665 jobs, all 30 policy tests pass, the scanner checks
2,796 tracked Lean sources, and the full imported-closure gate reports
`AXIOM_GATE_PASS: 70718 declarations checked`. Report 34 records the
then-remaining concrete-model boundary, later reduced by Report 36.
Fresh-extraction Review Kit verification is pending.

## Canonical number-field arithmetic checkpoint

Code commit `129f19e896c38f70b7c63bea9d8b3bd48ed0ffcb` defines the
dyadic predicate, ramification index, and discriminant proposition directly
from the standard height-one spectrum and derives the bridge plus the
arithmetic fields of `SectionEightLaws`. The focused build completes 5,646
jobs and the combined canonical/audit build completes 5,667 jobs. The audited
constructors use only `propext`, `Classical.choice`, and `Quot.sound`.
All 30 policy tests pass, the scanner checks 2,798 tracked Lean sources, and
the focused imported-closure gate reports
`AXIOM_GATE_PASS: 62790 declarations checked`. Report 36 records the reduced
boundary. Fresh-extraction Review Kit evidence for this later checkpoint is
still pending.

## Current exact v5 source-only Review Kit checkpoint

Commit `c1ee018dd9eb6c788165a51fe08bdfe8f9ff7b2e` was packaged from a
clean tree into a source-only Review Kit. All 2,010 payload hashes and the
paper-isolation checks pass. A fresh extraction, transparently resumed in the
same extraction after an external process interruption, completes a
5,671-job build, all six Classic audit modules, and the generated enforcing
gate. The gate reports `AXIOM_GATE_PASS: 62746 declarations checked`; all nine
dependency heads equal their pinned revisions and are clean.

Report 35 fixes the archive identity and complete local receipt. This is an
exact local reproducibility result, not GitHub CI, a tagged release, whole-paper
completion, or semantic approval. GitHub deployment remains disabled.

## Number-field coefficient extension checkpoint

At exact code commit `6d5c434a76afc46bed1904516d33c9c8fd6f811b`, the new
finite-prime order and ramification module plus its focused audit complete a
5,651-job build. The canonical paper entry and combined audit complete 5,674
jobs. The five audited declarations report only `propext`,
`Classical.choice`, and `Quot.sound`. All 30 policy tests and the scan of 2,800
tracked Lean sources pass. The focused imported-closure gate reports
`AXIOM_GATE_PASS: 62819 declarations checked`. Report 38 records the semantic
scope.

This incremental checkpoint is newer than the exact Review Kit described
above. It therefore requires its own later clean extraction and does not
inherit exact-kit status from Report 35 or from the in-progress historical
kit for commit `00629d4`.

## Finite-completion extension checkpoint

At exact code commit `82a2b047f168e6de7a8d0a869bec38ead1f01a8d`, the
continuous ring homomorphism between the finite completions, its
dense-subfield compatibility, and scoped algebra, scalar-tower, and
continuous-scalar instances are kernel checked. The focused audit additionally
infers `Module.Finite` and `FiniteDimensional` for the completed extension.
The focused build completes 5,651 jobs and the canonical paper plus combined
Classic audit completes 5,674 jobs. All 30 policy tests pass, the scanner
checks 2,800 tracked Lean sources, and the focused imported-closure gate
reports `AXIOM_GATE_PASS: 62830 declarations checked`. Report 39 records the
strict semantic boundary. An exact fresh-extraction kit for this newer commit
remains pending.

## Completed-field order-scaling checkpoint

At exact code commit `a5c100249faf6ef2d10eb1385cd06fd54a1cb1d5`, the
valuation identity on all completion elements, the additive order formula on
completion units, and the completed Lemma 8.1 adapter are kernel checked. The
focused build completes 5,651 jobs and the canonical paper plus combined
Classic audit completes 5,674 jobs. All 30 policy tests pass, the scanner
checks 2,800 tracked Lean sources, and the focused imported-closure gate
reports `AXIOM_GATE_PASS: 62857 declarations checked`. Report 40 records the
semantic scope. A fresh exact Review Kit for this checkpoint remains pending.

## Completed defect and good-BONG coefficient-scaling checkpoint

At exact code commit `c6d22da9282e112597f805e9104eae1cb88fb938`, the
completed relative quadratic-defect definition, its ramification-scaled
inequality, the exact good-BONG coefficient criterion, its transfer under the
completed embedding, and the fully constructed local Lemma 8.1 arithmetic
adapter are kernel checked. The focused completion build completes 5,651 jobs,
and the canonical paper plus all eight manifest-listed Classic audits complete
5,674 jobs. The new audited declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. All 30 policy tests pass, the scanner
checks 2,800 tracked Lean sources, and the focused imported-closure gate
reports `AXIOM_GATE_PASS: 62850 declarations checked`. Report 41 records the
semantic scope.

This count is not expected to be monotone: the checkpoint replaces the former
caller-supplied completed adapter and removes declarations as well as adding
proofs. A fresh exact Review Kit for this code-and-audit checkpoint remains
pending.

## Concrete dyadic completion and actual-realization checkpoint

At exact code commit `e3b18be95c813885a421b83fe0a0148d6b561ae0`, every
number-field finite completion receives the concrete local-field structure
needed by the BONG library, and every dyadic prime receives its normalized
`DyadicContext`. The direct completed order, relative defect, and absolute
ramification index are proved equal to the corresponding BONG notions. The
coefficient criterion is proved necessary for every actual lower good BONG
and sufficient for an actual upper integral-lattice realization. Consequently
`goodBONG_mappedValues_haveRealization` proves exactly the existential
good-BONG conclusion supported by the proof of v5 Lemma 8.1(iii).

The focused build completes 5,653 jobs, and the canonical paper plus all eight
manifest-listed Classic audits complete 5,676 jobs. The audited declarations
use only `propext`, `Classical.choice`, and `Quot.sound`. All 30 policy tests
pass, the scanner checks 2,802 tracked Lean sources, and the focused imported-
closure gate reports `AXIOM_GATE_PASS: 62917 declarations checked`.

This checkpoint does not identify the constructed upper lattice with the
preassigned localized scalar-extension lattice `L_P`; Report 42 records that
the written source proof also omits this identification. A fresh exact Review
Kit for the newer code-and-audit commit remains pending.

## Current v5 code-and-audit Review Kit

Report 43 supersedes the pending exact-kit sentence immediately above. The
source-only archive for packaged commit
`ab1901ac9df3e659a40a8cd4e1c0590997622217`, containing Lean code checkpoint
`e3b18be95c813885a421b83fe0a0148d6b561ae0`, has SHA-256
`92AD5F18A70386948D970C627BC7C94835B3B380ADBF1FE9265949BFF09A336A`.
All 2,023 payload hashes and all structural-isolation checks pass. A resumed
new-extraction build completes 5,682 jobs, all nine manifest-selected audits
pass separately, and the enforcing gate reports
`AXIOM_GATE_PASS: 62917 declarations checked`. All nine dependency heads equal
their clean pinned revisions.

The corrected Windows verifier now treats a native command's exit code, rather
than ordinary Git/Lake stderr progress, as the success criterion. This exact
local receipt remains distinct from GitHub CI, a release asset, whole-paper
completion, and semantic approval.
