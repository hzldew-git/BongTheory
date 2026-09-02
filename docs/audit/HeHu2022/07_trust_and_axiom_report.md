# Trust and axiom report

`BongTest.HeHu2022Audit` prints the transitive axioms of every proved public
endpoint in current scope. Expected foundational axioms are `propext`,
`Classical.choice`, and `Quot.sound`; no project-specific axiom or `sorry` is
permitted.  The audit now includes the direct Section 2 endpoints,
Propositions 3.2--3.7, Lemmas 3.9--3.11, Lemmas 3.13--3.14, the abstract
maximal-testing theorem, and the proved Section 4 reduction and invariant
conversion declarations. The
codimension-two theorem used for Proposition 3.5(iii) is itself proved in
`DiagonalCodimensionTwoRepresentationProof`; it is not a paper-specific law
assumption. The unproved Theorem 1.1 target is not disguised as an axiom.
Likewise, `heHuTheorem41_of_component_equivalences` quantifies the three
still-open component equivalences explicitly; the audit does not present it
as the completed Theorem 4.1.
