# Reproducibility report

Build the canonical module with `lake build Bong.Papers.HeHu2022` and run
`lake env lean BongTest/HeHu2022Audit.lean`. The paper Review Kit is generated
from `papers/hehu2022/paper.json`; it contains only the transitive local source
closure and audit files. Verify the independently obtained publisher PDF against
the manifest hash; the PDF is not bundled.

Report 14 records a clean, independently extracted verification of the
source-only kit for commit `8bff7e2`: all 1,913 payload hashes, all 4,952 build
jobs, the paper audit, and the 57,843-declaration enforcing gate passed. That
receipt is local evidence for the exact recorded commit; the release artifact
must still be regenerated and checked at the eventual release tag.
