# Reproducibility report

The formal baseline built successfully with 5,555 jobs.  A separate clone of
commit `ee826e7a8e67dda053563c01e027b2379bd68e6f` rebuilt the complete default
target from source.  `BongTest/Beli2009Audit.lean` and
`BongTest/FinalPublicTheoremAudit.lean` then completed with exit status zero;
the former printed 65 axiom reports.

Local status: `REPRODUCIBLE_WITH_DOCUMENTED_EXTERNAL_DEPENDENCIES`.
Cross-platform GitHub CI remains pending.  The paper PDF is provenance
material and is not a build dependency.
