# Trust and axiom report

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for
both wrappers. No project law/data class is an endpoint parameter, and no
`sorry`, project axiom, oracle, external solver, or native trusted computation
lies on the proof path.

The 2006 classification wrapper depends on the independently built 2009 proof;
the representation wrapper depends on the independently built 2019 proof.
Neither later main theorem imports the corresponding 2006 wrapper, so the
dependency direction is not circular.
