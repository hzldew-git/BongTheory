import Bong
import BongTest.AxiomGate

/-! Enforce the fixed foundational axiom allowance on the reusable foundation. -/

set_option maxHeartbeats 0 in
run_cmd BongCI.checkAxioms #[`Bong]
