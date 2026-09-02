# Hidden assumptions

The Lean context makes explicit that the coefficient field has the repository's
dyadic local-field interface, the source is a full lattice in a finite-dimensional
quadratic space, and BONG data are good BONG data of the same lattice. The paper's
standing source integrality and `n >= 2` restrictions are explicit arguments of
the Theorem 1.1 target. Nondegeneracy and completeness are supplied by
`DyadicContext`; this
dependency must be rechecked before semantic promotion.
