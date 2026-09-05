# He-paper deployment checkpoint: 5 September 2026

This is a versioned progress record, not a completed-release certificate.
The three papers retain separate canonical entries, audit folders, manifests
and source-only Review Kits in the shared repository.

## Later workflow and boundary status

The later Paper Review Kits run 33942437722 completed successfully for all
eight paper jobs at source `c82668b97ed80f0cead4493206cb6483c4e8d77d`,
tree-identical to remote branch head `f6f7485b6a3acabedbec5a7facce46f8ee7365ab`.
This supplies independent clean extraction, payload verification, builds,
paper audits, and enforcing gates for He--Hu, He classic, and He ADC at that
source. The He--Hu, He classic, and He ADC artifacts are respectively
`9965063239`, `9962386381`, and `9962394872`.

Lean CI run 33942437720 did not pass: the monolithic complete build reached its
configured 360-minute limit and was cancelled. Later deployment work must
replace that single build with sharded complete coverage; no green status is
inferred from the successful paper-kit workflow.

Local ADC work through `fe2a459a4152ade94299a61d1c4958fefa646ba0` is newer
than both remote workflows. It proves and independently audits a concrete
counterexample to the n=2 instance of published Lemma 6.8(iv). Reports 28--31
record the exact mathematical, trust, and reproducibility scope. This source
has not yet been pushed or included in a clean Review Kit.

## Remote revision and observations

At the time of inspection, both remote workflows concern branch head
`db0398506b2e242288bc979217972c6a1d175674`, not the later local proofs.
The recorded merge-test commit is
`6bf3bdf8bd272109e898335683f05bb76664330c`; its tree was checked against
the branch tree. Later local commits must pass their own remote gates.

[Paper Review Kits run 33929872783](https://github.com/hzldew-git/BongTheory/actions/runs/33929872783)
completed successfully for all eight papers. The last He classic job,
`101206371200`, completed at 03:05:13 UTC on 5 September after a successful
5010-job build. Its source-only artifact is `9961760603`. The He ADC artifact
contains the published maximal profiles,
not the later Proposition 4.13, dyadic 4.16 or Section 6 additions.

## Whole-repository CI false positive

[Lean CI run 33929872826](https://github.com/hzldew-git/BongTheory/actions/runs/33929872826)
finished with a failure. Its full default build succeeded (5700 jobs),
from 23:32:44 UTC on 4 September to 02:20:32 UTC on 5 September.
Despite its former step name, this was NOT an enforcing namespace-wide
axiom audit. Independent inspection found that the pinned
[Lean action definition](https://raw.githubusercontent.com/leanprover/lean-action/38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9/action.yml)
does not support `axiom-audit`, `axiom-audit-root` or `axiom-audit-allow`;
the remote log explicitly warns about these unexpected inputs. Earlier
descriptions of this step as a successful complete axiom audit are withdrawn.
The next textual gate matched the word `sorry` inside the
module documentation at `Bong/Lattice/GlobalNADC.lean:21`, in a sentence
explicitly explaining that no unfinished proof was used. The public-signature
and clean-generated-state steps were subsequently skipped, so the workflow
as a whole has not passed.

The repair replaces flat text matching with a comment-aware supplemental
source check. Nested block comments and line
comments are masked while preserving line numbers. Quoted markers and
escaped identifiers do not begin comments; forbidden words in quoted
literals are conservatively reported. Ordinary strings with an unescaped
opening brace are rejected for parser review, because they may contain
nested interpolated terms and quotes. Unterminated comments, literals and
escaped identifiers fail closed. Actual `sorry`,
`sorryAx`, `admit` and `axiom` tokens remain rejected. This is not a Lean
parser and cannot replace a transitive proof-dependency gate. No mathematical declaration or
documentation was rewritten to evade the scan.

Independent review found two valid-Lean evasion cases in the initial repair
at `d920f4d`: comment markers inside escaped identifiers and nested
interpolated strings could hide later actual proof tokens. The first repair
is therefore not sufficient. Follow-up regression tests include those cases;
the scanner now recognizes escaped identifiers and fails closed on ambiguous
braced ordinary strings. These limitations are explicit, not a claim of
complete Lean parsing. A further valid-Lean custom-command regression at
`391a896` exposed a character literal wrongly starting inside a primed
identifier. The follow-up guards that token boundary and tests both an
unfinished theorem and an actual custom-axiom declaration.

The 18-test and 2673-source successes at `391a896` did not cover that later
counterexample. The source gate runs before the
expensive build. The job limit
is extended to 360 minutes, matching the paper-kit build allowance; the
previous successful build step already took about 168 minutes.
No gate is bypassed and no build result is inferred from the timeout change.
The repair still requires a fresh remote run after push.

## Replacement enforcing gate

`BongTest/AxiomGate.lean` uses Lean's transitive `collectAxioms`, not textual
output matching, and throws an elaboration error for every dependency outside
the fixed allowance `propext`, `Classical.choice`, `Quot.sound`. It selects
declarations by namespace and by defining module, including private helpers
and helpers declared outside the project's namespace. An empty selection is
also an error. The source scanner is only supplemental.

`scripts/ci/check_axiom_gate_fixtures.py` exercises the actual Lean command
on constructive and standard proofs, unfinished proofs, direct and transitive
custom dependencies, private helpers, native computation and empty scope.
A negative fixture must return nonzero with the gate's own rejection marker;
an import or syntax error cannot stand in for a rejection.

The default CI gate imports every tracked production `Bong` module and the
standard `BongTest` audit-root closure. The production library glob builds
every production module, including ones not reached by the umbrella import.
Legacy milestone-only test modules outside that closure remain subject to
the tracked-source scan, not a newly claimed full compiled-module audit.
The explicit `--entry` mode is a focused local check and is not used by CI.

New Review Kits contain the same enforcing gate and a generated paper-specific
driver, listed in their audit manifest and built from their own source closure.
The verifier requires its success marker. Older kits without it may still be
structure-checked but cannot receive a new full-verification result from the
updated verifier. Historical build receipts are not retroactively upgraded.

Local replacement-gate results: all 19 source-scanner regression tests pass;
all 11 actual-Lean positive/negative fixture cases pass, including unreferenced
private and out-of-namespace declarations selected by module ownership.
The current ADC imported closure passes the enforcing gate on 57,453
declarations. This remains a focused local check using the existing modified
dependency worktrees, not the full-production CI result or a clean rebuild.

Independent review at `e77a50bbf929d9d23533e4b07f11535d0c87040f` confirmed
the enforcing command, all 11 fixtures, the 57,453-declaration ADC result,
the 2,063 production/audit roots and the generated-kit wiring. It also checked
five additional cases: opaque unfinished bodies, type-only dependencies,
namespace-component boundaries, choice/quotient permission and a source-scan
evasion that the enforcing gate correctly rejects.

That review found that the supplemental scanner's primed-identifier guard
still omitted `!`, `?` and Lean-specific Unicode continuation characters.
The follow-up implements the pinned Lean 4.32.1 `isIdRest` predicate from
`Init/Meta/Defs.lean`, rather than Python's different alphanumeric predicate.
All 20 scanner tests now pass, including the complete custom-command probes
for bang, question mark and representative Unicode endings. All 16 actual-Lean
gate fixtures pass after adding the independent reviewer's five probes.
The enforcing gate itself was not weakened or changed by this follow-up.

Review of `01140a7` then identified two further supplemental boundaries:
the end of an escaped identifier really is a boundary before a raw/character
literal, and Python regex word characters do not determine Lean token ends
(for example, a postfix lambda token after an unfinished term). The follow-up
removes the special escaped-closer exclusion and uses the pinned Lean
predicate for forbidden-token boundaries too. Regression cases retain all
three complete valid-Lean examples. The unchanged enforcing gate was
independently confirmed to reject each example, including its transitive
unfinished-proof dependency. No claim of a complete Lean lexer is made.

After these follow-ups, all 23 supplemental-scanner tests, all 2675 tracked
source checks, and all 19 actual-Lean gate fixtures pass locally. Each
negative fixture exits nonzero for the gate's own reason. These test counts
do not upgrade the earlier frozen scanner revisions or certify fresh CI.

The later local imported `Bong` umbrella closure passed the enforcing gate
on 66,608 declarations. This is still explicit focused mode, not the default
all-production/audit-root check: a missing cached `BongTest.Q2` module prevented
the latter local import. The fresh CI build must supply its own complete
artifacts; local cached checks do not replace that obligation.

## First clean-kit results with the enforcing gate

The new [Paper Review Kits run 33942437722](https://github.com/hzldew-git/BongTheory/actions/runs/33942437722)
uses branch head `f6f7485b6a3acabedbec5a7facce46f8ee7365ab`. Its actual checkout
and packaged source is merge-test commit
`c82668b97ed80f0cead4493206cb6483c4e8d77d`, not the head SHA. The GitHub
commit object and local head independently give the same source tree:
`821e857945c1f9a3b556d877075e67c28524866a`.

| Paper | Successful job | Checked payload hashes | Build jobs | Enforcing gate declarations | Download |
|---|---|---|---|---|---|
| ADC | `101242489577` | 1934 | 4963 | 57,480 | [ADC artifact 9962394872](https://github.com/hzldew-git/BongTheory/actions/runs/33942437722/artifacts/9962394872) |
| Classic | `101242489505` | 1967 | 5004 | 61,515 | [Classic artifact 9962386381](https://github.com/hzldew-git/BongTheory/actions/runs/33942437722/artifacts/9962386381) |

Both inspected logs contain the actual `BongTest.PaperAxiomGate` build and
`AXIOM_GATE_PASS` with these counts. The ADC log also prints both full
Lemma 6.7 statements and their standard-only dependencies. These are the
first recorded independent clean-kit results for the replacement gate;
they do not retroactively certify the unsupported action inputs.

The inner ADC source archive SHA-256 is
`204B0619DCE9D60463EDD58166387DA2D152CC4386213CEA62DD5ED838CE6053`;
the inner Classic source archive SHA-256 is
`079D6DFCFB9982415F0D3271C29C6AF0E2C560111B79FB08828D6131C4F97987`.
These differ from the outer workflow artifact ZIP digests and local
head-SHA packages, whose manifests name a different commit.

The ADC closure includes Proposition 4.13, dyadic Proposition 4.16,
Theorem 6.1 and full Lemmas 6.4--6.7. It does not include the subsequent
Lemma 6.8(i)--(ii) code at `b624d40`. Classic remains a partial paper with
its source discrepancy and odd/global obligations. The artifacts have
30-day retention and are not permanent tagged releases. The separate
whole-production [Lean CI run 33942437720](https://github.com/hzldew-git/BongTheory/actions/runs/33942437720)
was still in progress when these two receipts were inspected.

The generated driver produced nonfatal documentation/scoped-option lint
warnings, which are distinct from proof or gate failures and remain visible
in the frozen logs. No human semantic approval is inferred from these runs.
The subsequent generator repair adds its copyright/module documentation
and scopes the heartbeat option to the one gate command. The same command
on the newer locally imported ADC closure passed on 57,526 declarations
without those lint warnings. This focused cached check is not a clean-kit
certificate for either the generator change or the newer Lemma 6.8 code.

## Later local generic-column checkpoint

`b728bce20942191785d0b50f2c068e0b5ee7c2f7` proves ADC Lemma 6.8(v),(vi)
and the printed-domain bridge with explicit Delta in U. Four modules,
entry and full audit passed both main and independent cached checks;
all 16 new query sets contain exactly the standard three axioms. Report 24
records scope and source convention. With b624d40, the lemma has 4/6
clauses. This code is not in the f6f7485/c82668b clean artifacts above and
still requires its own exact-revision kit and clean run. No release is
promoted and no whole-paper completion is claimed by this local increment.

Independent follow-up at frozen `f6f7485` also passed all 23 scanner tests,
the 2675-source scan, and the three actual escaped-identifier/postfix probes
against the unchanged enforcing gate. It certified those bounded repairs,
not the later mathematics or a release.

## Later independently selectable local package

The ADC source-only package at clean commit
`a7345459f9737fffb482b3ef8d215f8feeca24b2` includes complete Theorem 6.1:
`BongTheory-He2023ADC-checkpoint-20260905-even-corank-one-review-kit.zip`.
It contains 1886 Lean sources and 1926 files, with 1925 payload hashes
verified after extraction. Archive SHA-256:
`7D0DD1177B92D091C86B0ABF23EB6D945298FAD075EBD8967C2895DEC4048C59`.
It predates the later Lemma 6.6 code. Structure verification is not a clean
Lean build, and this package has not been uploaded or promoted to a release.

The later clean `391a896759e18accb3f14156a00991f3c076c332` kit includes both
complete Lemma 6.6 clauses:
`BongTheory-He2023ADC-checkpoint-20260905-central-obstruction-review-kit.zip`.
It has 1889 closure Lean sources, 1931 packaged files and 5765705 bytes;
all 1930 payload hashes passed extraction checks. Archive SHA-256:
`FB59500BB4911DE8F317E9CE56AE5EC67170E758BA97CEE7584D53F77BBCBCB6`.
This is also structure-only and not uploaded. It predates the replacement
enforcing gate and cannot certify that later deployment repair.

The subsequent source-only `e77a50b` package includes the enforcing gate:
`BongTheory-He2023ADC-checkpoint-20260905-enforcing-gate-review-kit.zip`.
It has 1890 closure Lean sources, 1933 packaged files and 5768227 bytes;
all 1932 payload hashes passed extraction checks. Archive SHA-256:
`F1DAE1673BB68F876EFC2520A46BA697AEB994C452499B8E4B3234170FEE275C`.
Its generated driver, checksum coverage, manifest and build-root wiring
were independently inspected. It is not a clean-build certificate and
predates both Lemma 6.7 and the later identifier-boundary scanner repair.

PR 10 remains draft. No new merge, tag, final release or human semantic
approval is certified here. Remaining Classic source-obstruction and ADC
local/global classification gaps stay explicit in their paper audits.

The clean-head `f6f7485` local ADC package additionally includes full
Lemma 6.7 and the enforcing gate:
`BongTheory-He2023ADC-checkpoint-20260905-terminal-alpha-review-kit.zip`.
It has 1891 closure Lean sources, 1935 packaged files and 5775446 bytes;
all 1934 payload hashes passed extraction checks. Archive SHA-256:
`D1D3C85B94B035282DF7602F8A0E23028AA9E5B1ECFC857C94C7ED6418DAFD06`.
This particular ZIP was structure-checked locally. The separate clean
CI receipt above names the tree-identical merge-test source and its own ZIP.

The clean detached `d05a89885573dd17ec097f059f4a635a96736b7b` source
was subsequently packaged as
`BongTheory-He2023ADC-checkpoint-20260905-generic-review-kit.zip`.
It contains 1898 project Lean sources, 1944 files and 5806365 bytes;
all 1943 payload hashes passed extraction checks. Archive SHA-256:
`FB75D0711589F584E2C8B7AE054CFCBA97B6FD172271D51CB747484BFE41C646`.
This clean-source package contains Lemma 6.8(i),(ii),(v),(vi), reports
23--24, and the scoped enforcing-gate driver. It has not been cleanly
compiled or uploaded as a release. It predates the second-endpoint
addition at `074f2cd`; neither that addition nor a complete paper is
certified by this structure-only receipt.

## Later second-endpoint proof increment

At `074f2cdcd63637fb6f6d8c65879e55968a1dc675`, full ADC Lemma 6.8(iii)
and the explicit n>=4 part of (iv) passed main and independent replay of
five new modules, canonical entry and the complete paper audit. All twelve
new queries use exactly the standard three axioms. An independent focused
imported-environment gate passed on 57,667 declarations; the main scanner
checks passed 23 regression tests and 2687 tracked Lean sources.

Report 25 records the historical distinction between five complete whole
clauses and the then-partial (iv). Reports 26--31 subsequently prove and
independently audit a counterexample to its n=2 boundary. The
local d05a898 package and remote f6f7485/c82668b clean kit both predate this
increment. Existing dependency-state warnings remain disclosed; cached
checks are not clean CI. No release is promoted by this proof increment.
