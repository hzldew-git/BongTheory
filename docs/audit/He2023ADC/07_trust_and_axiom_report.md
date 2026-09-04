# Trust and axiom report

`BongTest.He2023ADCAudit` prints public signatures and the transitive axiom
sets of selected endpoints. Expected foundational axioms are `propext`, `Classical.choice`, and
`Quot.sound`; no project-specific axiom or `sorry` is permitted. Successful
compilation alone does not validate the definition dictionary.

At code commit `2a151a8024d10ae094df958cd3626dbd13c447c2`, the new volume
criterion, Remark 4.10 and all ten profile criteria passed the focused audit
with only these standard axioms. The odd second-column Lemma 4.9 endpoint
also now uses the proved Beli classification internally instead of retaining
a `GoodBONGClassificationLaws` parameter.

At checkpoint `976883e6cda7c17402c4c1f0bc768db555460eae`, the paper entry
and complete current audit file passed incremental compilation. All thirteen
new published-family endpoints report only `propext`, `Classical.choice`
and `Quot.sound`. Neither new source file contains `sorry`, `admit`, custom
axioms or native computation. The new proofs reuse the proved Beli and
He--Hu transport, classification and maximal-lattice results.

The global `Theorem13Laws` parameter remains undischarged. Its absence from
`#print axioms` is not evidence that the supplied arithmetic laws have been
proved: explicit premises are not Lean axioms. Imported He--Hu and Beli
results are reused, as the published ADC paper itself reuses those results.
