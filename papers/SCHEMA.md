# Adding a BONG-related paper

Every later paper formalized in this repository must be considered for the
same paper-specific review-kit workflow. A new paper is complete as a
distributable formal artifact only when all of the following are present:

1. `papers/<paper-id>/paper.json`, using schema 2 for new papers (schema 1
   remains supported for the existing five manifests);
2. a canonical `Bong.Papers.<PaperName>` entry module;
3. at least one `BongTest.<PaperName>Audit` module printing public signatures
   and transitive axiom sets;
4. a dedicated `docs/audit/<PaperName>/` fidelity package;
5. a generated source-only Review Kit whose local import closure is computed
   from the entry and audit modules;
6. clean-extract CI that builds the generated kit and runs every listed audit,
   including the enforcing transitive-axiom gate described below;
7. a Release asset, outer SHA-256, exact source commit, and frozen-paper hash;
8. explicit semantic status and every known source discrepancy.

The manifest discovery workflow reads `papers/*/paper.json`. Consequently, a
new BONG-related paper automatically enters the packaging matrix once its
manifest is committed; it must not be omitted by maintaining a handwritten
list elsewhere.

Internal implementation prefixes may be retained for compatibility, but the
canonical paper name, year, entry module, audit module, audit directory, and
release asset must follow the year-based naming convention used here.

Compilation establishes kernel acceptance, not semantic fidelity. Review Kits
must preserve `PROVISIONAL_MATCH`, discrepancies, boundary cases, and pending
human-signoff requirements from the authoritative audit package.

## Manifest schema 2

New manifests separate the historical work year from the publication year and
make source authority machine-readable. Required paper-source fields are:

- `workYear` and `publicationYear`;
- the complete publisher `citation` and DOI URL in `doi`;
- `authoritativeSource`, with `authority: true`, URL, description, uppercase
  SHA-256, and redistribution status;
- `comparisonSources`, each with `authority: false` and its own SHA-256;
- `formalizedScope` and `excludedScope`, so packaging cannot turn partial
  coverage into a completion claim.

The publisher version of record is the sole semantic authority. Preprints may
be listed only as comparison sources. Review Kits never contain publisher
PDFs; their hashes let reviewers verify an independently obtained copy.

## Enforcing trust gate for every new kit

The generator includes `BongTest.AxiomGate` and generates the paper-local
`BongTest.PaperAxiomGate`. The latter imports the paper and its audits, checks
all in-scope declarations by namespace and defining module, and fails if
their transitive axioms exceed `propext`, `Classical.choice`, `Quot.sound`.
The generated manifest records it as `formalization.enforcingAxiomGate` and
adds it to `formalization.auditModules`; the verifier requires its success
marker after execution. Human-readable `#print axioms` reports alone are
not an enforcing gate. This requirement applies automatically to all future
BONG-related papers and does not change their semantic coverage grades.
