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

The global `Theorem13Laws` parameter remains undischarged. Its absence from
`#print axioms` is not evidence that the supplied arithmetic laws have been
proved: explicit premises are not Lean axioms. Imported He--Hu and Beli
results are reused, as the published ADC paper itself reuses those results.
