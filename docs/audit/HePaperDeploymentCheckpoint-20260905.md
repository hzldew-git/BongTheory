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
has successful clean-extract jobs for Beli 2003, 2006, 2009, 2020, He--Hu,
and He ADC. The He classic and Beli 2019 jobs remain in progress at the
inspection. The He ADC artifact contains the published maximal profiles,
not the later Proposition 4.13, dyadic 4.16 or Section 6 additions.

## Whole-repository CI false positive

[Lean CI run 33929872826](https://github.com/hzldew-git/BongTheory/actions/runs/33929872826)
finished with a failure, but its build-and-complete-namespace-axiom-audit
step succeeded from 23:32:44 UTC on 4 September to 02:20:32 UTC on
5 September. The next textual gate matched the word `sorry` inside the
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
parser, and the complete-namespace kernel axiom audit is preserved unchanged
as a separate, stronger trust check. No mathematical declaration or
documentation was rewritten to evade the scan.

Independent review found two valid-Lean evasion cases in the initial repair
at `d920f4d`: comment markers inside escaped identifiers and nested
interpolated strings could hide later actual proof tokens. The first repair
is therefore not sufficient. Follow-up regression tests include those cases;
the scanner now recognizes escaped identifiers and fails closed on ambiguous
braced ordinary strings. These limitations are explicit, not a claim of
complete Lean parsing.

All 18 regression tests and the follow-up scan of 2673 tracked Lean sources
passed locally, without generated files. The source gate runs before the
expensive build. The job limit
is extended to 360 minutes, matching the paper-kit build allowance; the
previous successful build-and-audit step already took about 168 minutes.
No gate is bypassed and no build result is inferred from the timeout change.
The repair still requires a fresh remote run after push.

## Later independently selectable local package

The ADC source-only package at clean commit
`a7345459f9737fffb482b3ef8d215f8feeca24b2` includes complete Theorem 6.1:
`BongTheory-He2023ADC-checkpoint-20260905-even-corank-one-review-kit.zip`.
It contains 1886 Lean sources and 1926 files, with 1925 payload hashes
verified after extraction. Archive SHA-256:
`7D0DD1177B92D091C86B0ABF23EB6D945298FAD075EBD8967C2895DEC4048C59`.
It predates the later Lemma 6.6 code. Structure verification is not a clean
Lean build, and this package has not been uploaded or promoted to a release.

PR 10 remains draft. No new merge, tag, final release or human semantic
approval is certified here. Remaining Classic source-obstruction and ADC
local/global classification gaps stay explicit in their paper audits.
