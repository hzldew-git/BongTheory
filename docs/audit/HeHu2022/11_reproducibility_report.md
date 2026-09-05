# Reproducibility report

Build the canonical module with `lake build Bong.Papers.HeHu2022` and run
`lake env lean BongTest/HeHu2022Audit.lean`. The paper Review Kit is generated
from `papers/hehu2022/paper.json`; it contains only the transitive local source
closure and audit files. Verify the independently obtained publisher PDF against
the manifest hash; the PDF is not bundled.
