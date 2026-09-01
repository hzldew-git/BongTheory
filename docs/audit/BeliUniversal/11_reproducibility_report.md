# Reproducibility report

## Frozen inputs

- source PDF SHA-256:
  `35ECB7CB20A42768A6F55D80E69D4699837419854FAB021515020CCC7488986C`;
- audited committed revision:
  `5befe079dbf3569d1760b8e66bc52aef0de21745`;
- Lean: `4.32.1`;
- mathlib: `520045ab14e26149ee970e2e617ca04b09bde5d6`.

The implementation is committed on
`release/beli-universal-v0.2.0-rc.1`.  A separate GitHub clone of that branch,
with no pre-existing `.lake` directory and without invoking the mathlib binary
cache, was used for the audited source rebuild.

## Verification commands

```powershell
$env:LEAN_NUM_THREADS = '4'
lake --log-level=error build
lake env lean BongTest/FinalPublicTheoremAudit.lean
lake env lean BongTest/Beli2006Audit.lean
lake env lean BongTest/Beli2009Audit.lean
lake env lean BongTest/Beli2019Audit.lean
lake env lean BongTest/BeliUniversalAudit.lean
rg -n -g 'BeliUniversal*.lean' -g 'GoodBONGScalarAgreementClassification.lean' -g 'OMaximal*.lean' -g 'Universality.lean' -g 'BeliUniversalAudit.lean' '\bsorry\b|\badmit\b|\bsorryAx\b|^\s*axiom\b|^\s*opaque\b|^\s*unsafe\b|^\s*extern\b|implemented_by|native_decide|run_tac' Bong BongTest
git status --porcelain
```

The complete default target exited successfully after 5,597 jobs and
17,213.742 seconds.  The five focused audit commands then exited zero.
`BongTest.BeliUniversalAudit` checks the public endpoints for Theorem 2.1,
Theorem 3.1, Lemmas 4.1--4.9, Corollary 4.5(i)--(iv), and Corollary 4.10.

Every reported theorem used only `propext`, `Classical.choice`, and
`Quot.sound`.  The trust-boundary scan returned no matches (the expected `rg`
exit code is 1), and the final worktree was clean.  Thus the audited committed
implementation contains no `sorry`, `admit`, `sorryAx`, custom `axiom`,
`opaque`, unsafe/extern declaration, code-generation override,
`native_decide`, or `run_tac` escape hatch in the stated source scope.

Exact commands, host and tool versions, dependency revisions, timings, log
hashes, and cache boundaries are recorded in
[`../../reproducibility/clean-clone-5befe079.md`](../../reproducibility/clean-clone-5befe079.md).
This is project-author/AI-run technical evidence, not independent human
review.  Exact-tag Ubuntu and Windows evidence remains pending until the
`v0.2.0-rc.1` tag workflows finish.

The successful build does not resolve the frozen paper's documented `r_1`
versus `2r_1` coefficient discrepancy in Theorem 3.1 and does not upgrade the
semantic status beyond `PROVISIONAL_MATCH`.
