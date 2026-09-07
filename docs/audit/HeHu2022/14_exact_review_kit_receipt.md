# Exact Review Kit receipt

This receipt records an independently extracted local Review Kit verification
for commit `8bff7e2298c8fa3a87c5e4ca5e69513ba15532a0`. That checkpoint contains the
complete He--Hu (2022) paper closure summarized in Reports 12--13.

## Archive identity

- generated archive:
  `BongTheory-HeHu2022-ci-8bff7e2-review-kit.zip`;
- SHA-256:
  `922339B3185A0BAF6D4C09E58FF3A6C2C1DB9CB9486BA5`;
- recorded source commit:
  `8bff7e2298c8fa3a87c5e4ca5e69513ba15532a0`;
- recorded source-tree state: `clean`;
- recorded tracked local Lean sources: 1,880;
- recorded packaged files: 1,914.

The archive structure verifier checked all 1,913 payload entries after a
fresh extraction and reported success. The difference between packaged files
and payload entries is the outer archive itself.

## Independent extraction and build

A second fresh extraction contained no project build products. The nine
dependencies were copied from an exact, clean local mirror at the revisions
locked by `lake-manifest.json`; the Mathlib cache was then restored without
changing those revisions. This dependency-acquisition route is disclosed
because GitHub connectivity was unavailable during extraction setup.

With `LEAN_NUM_THREADS=1`, `lake build` completed all 4,952 jobs using Lean
4.32.1. The build included the enforcing paper gate and reported:

```text
AXIOM_GATE_PASS: 57843 declarations checked
```

The two exact paper checks were then rerun in the extracted tree and both
exited successfully:

```text
lake env lean BongTest/HeHu2022Audit.lean
lake env lean BongTest/PaperAxiomGate.lean
```

The final standalone gate again reported 57,843 checked declarations.

## Scope of this receipt

This closes the local mechanical reproducibility requirement for the exact
clean source checkpoint `8bff7e2`. It does not certify later commits, an
uploaded GitHub artifact, a tagged release, or the still-running remote CI
jobs. It also does not replace independent human semantic review of the
publisher-to-Lean correspondence. Those are separate release and review
requirements.
