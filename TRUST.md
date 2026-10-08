# Trust boundary

Lean kernel checking covers the declarations compiled from this repository
and their pinned dependencies. The project permits only `propext`,
`Classical.choice`, and `Quot.sound` in the transitive axiom sets selected by
the enforcing gate.

The gate does not certify bibliographic accuracy, completeness of a paper,
semantic equivalence to printed statements, or mathematical claims supplied
as explicit hypotheses. Those checks belong to the paper repositories.
