# Reproducibility report

The development checkout built successfully at baseline commit
`10e8c666bfda81dcac44332cd38f481d8d02e31a`.  A separate clone of committed
revision `ee826e7a8e67dda053563c01e027b2379bd68e6f`, initially containing no
`.lake` directory, then completed a source build with 5,555 jobs.  The final
public-theorem audit exited zero in that clone.

Local status: `REPRODUCIBLE_WITH_DOCUMENTED_EXTERNAL_DEPENDENCIES`.
Exact-tag public Ubuntu and Windows evidence also passed under the documented
scopes.  See `REPRODUCING.md`,
`docs/reproducibility/clean-clone-ee826e7.md`, and
`docs/reproducibility/github-actions-v0.1.0-rc.1.md` for the protocol and
receipts.
