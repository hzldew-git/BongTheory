# He-paper deployment checkpoint: 5 September 2026

This is a versioned progress record, not a completed-release certificate.
The three papers retain separate canonical entries, audit folders, manifests
and source-only Review Kits in the shared repository.

## Remote revision and observations

At the time of inspection, both remote workflows concern branch head
`db0398506b2e242288bc979217972c6a1d175674`, not the later local proofs.
The recorded merge-test commit is
`6bf3bdf8bd272109e898335683f05bb76664330c`; its tree was checked against
the branch tree. Later local commits must pass their own remote gates.

[Paper Review Kits run 33929872783](https://github.com/hzldew-git/BongTheory/actions/runs/33929872783)
has successful clean-extract jobs for Beli 2003, 2006, 2009, 2019, 2020,
He--Hu, and He ADC. The He classic job remains in progress at the
inspection. The He ADC artifact contains the published maximal profiles,
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
