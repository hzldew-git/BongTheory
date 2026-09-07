# Exact Review Kit receipt through Report 53

This receipt fixes the independently extracted local Review Kit evidence for
commit `26dc39191383942f238f2b0419ca1fdd1865dfab`. That clean commit includes
the dyadic unary table and minimality result, every dyadic rank branch of
Theorem 1.10, the conditional non-dyadic Theorem 1.10 catalogue, and the
finite logical deductions for Corollary 1.8 and Theorem 1.11 recorded in
Reports 50--53.

## Archive identity

- generated archive:
  `BongTheory-He2023ADC-ci-26dc391-review-kit.zip`;
- archive size: 6,173,205 bytes;
- SHA-256:
  `612891897582B5C314FAAF46598B550F72242022A218A50D9F893A867124FF28`;
- recorded source commit:
  `26dc39191383942f238f2b0419ca1fdd1865dfab`;
- recorded source-tree state: `clean`;
- recorded tracked local Lean sources: 1,973;
- recorded packaged files: 2,048.

The archive contains 2,047 payload hashes in `FILES.sha256`. A separate
structure inspection found no packaged `.lake` directory or compiled Lean
artifact.

## Independent extraction and build

The archive was expanded into a second directory that initially contained
exactly the 2,048 packaged files and no project build products. All nine Lake
dependencies were copied from a clean mirror, and every dependency `HEAD`
matched the revision in `lake-manifest.json`. Dependency cache restoration
then completed successfully.

The complete build began with one worker. It was deliberately interrupted
after job 3,705 and resumed with two workers, interrupted after job 4,137 and
resumed with three workers, then interrupted after job 4,174 and resumed with
four workers in the same otherwise fresh extraction to improve throughput. No
project artifact predating this verification session was introduced or reused.
The resumed `lake build` completed all
`5,051` jobs with Lean 4.32.1.

The following four paper gates were then rerun directly in that extracted
tree; each exited successfully:

```text
lake env lean BongTest/He2023ADCAudit.lean
lake env lean BongTest/He2023ADCQuaternaryBoundaryQ2.lean
lake env lean BongTest/He2023ADCExceptionalQuaternaryQ2.lean
lake env lean BongTest/PaperAxiomGate.lean
```

The standalone enforcing gate reported:

```text
AXIOM_GATE_PASS: 60374 declarations checked
```

## Scope of this receipt

This closes local mechanical reproducibility for the exact clean source
checkpoint `26dc391` through Reports 50--53. It does not certify a later
commit, GitHub-hosted CI, an uploaded artifact, or a tagged release. It also
does not turn the conditional arithmetic and external-catalogue inputs into
concrete instances, resolve the recorded publisher mismatches, or provide
independent human semantic sign-off. The paper therefore remains Grade D and
`NOT_COMPLETE`.
