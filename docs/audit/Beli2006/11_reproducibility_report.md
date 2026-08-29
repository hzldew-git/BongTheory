# Reproducibility report

The proof-and-test baseline built successfully with 5,555 Lake jobs and both
public wrappers passed the axiom/signature audit.  A separate clone of commit
`ee826e7a8e67dda053563c01e027b2379bd68e6f` then rebuilt the complete default
target from source.  `Beli2006Audit.lean` exited zero in 15.13 seconds.

Local status: `REPRODUCIBLE_WITH_DOCUMENTED_EXTERNAL_DEPENDENCIES`.
Exact-tag public Ubuntu and Windows evidence also passed under the documented
scopes.  No 2006 PDF is needed to compile the Lean project; see the shared
local and GitHub Actions receipts for exact evidence.
