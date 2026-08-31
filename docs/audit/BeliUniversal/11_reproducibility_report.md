# Reproducibility report

## Frozen inputs

- source PDF SHA-256:
  `35ECB7CB20A42768A6F55D80E69D4699837419854FAB021515020CCC7488986C`;
- repository base: `3b9b0aef8e5882ea750d6e73b872af4ef9ba9044`;
- Lean: `4.32.1`;
- mathlib: `520045ab14e26149ee970e2e617ca04b09bde5d6`.

The implementation is currently an uncommitted working-tree overlay on that
base, so the base hash alone does not reproduce the new files. A commit or tag
is required before external circulation.

## Verification commands

```powershell
$env:LEAN_NUM_THREADS = '4'
lake build Bong.Bong.BeliUniversalTheorem31Proof BongTest.BeliUniversalAudit
lake --quiet build
rg -n -g 'BeliUniversal*.lean' -g 'OMaximal*.lean' -g 'Universality.lean' '\bsorry\b|\badmit\b|\bsorryAx\b|^\s*axiom\b|^\s*opaque\b|^\s*unsafe\b|^\s*extern\b|implemented_by|native_decide|run_tac' Bong BongTest
```

The focused build completed successfully with 4883 jobs on 1 September 2026.
`BongTest.BeliUniversalAudit` checks the public endpoints for Theorem 2.1,
Theorem 3.1, Lemmas 4.1--4.9, Corollary 4.5(i)--(iv), and Corollary 4.10. Its
`#print axioms` output contains only `propext`, `Classical.choice`, and
`Quot.sound`.

The final repository-wide build, run with four Lean worker threads, exited
successfully after 5602 jobs. Earlier unrestricted-concurrency attempts on the
same Windows checkout encountered transient `.olean`/`.olean.private` read
failures and `bad_alloc` in unrelated `BongTest.M*` modules; the four-thread
run is the verified result. The remaining output consists of linter warnings,
not proof errors.

The placeholder/trust-boundary scan returns no matches (the expected `rg` exit
code is 1). Thus the audited implementation contains no `sorry`, `admit`,
`sorryAx`, custom `axiom`, `opaque`, unsafe/extern declaration, code-generation
override, `native_decide`, or `run_tac` escape hatch.

Lake warns that the mathlib, aesop, and batteries dependency checkouts contain
local changes. This does not alter the successful kernel check, but a clean
clone build and a repository commit/tag remain required before an archival
release.
