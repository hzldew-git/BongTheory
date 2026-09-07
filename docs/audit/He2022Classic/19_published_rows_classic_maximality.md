# Published table rows are classic-maximal

Code checkpoint: `981f044`.

## Result

Every literal model in both the even and odd published testing tables has
volume order zero or one. Since every model was already proved classic
integral, the generic volume lemma now proves that every such row is maximal
among classic integral lattices in its own ambient quadratic space.

The generic theorem is
`Bong.Lattice.isClassicMaximal_of_volumeOrder_le_one`. It uses the proved
facts that an inclusion of full lattices changes volume order by twice a
nonnegative integer, while classic integrality forces nonnegative volume
order. Consequently, a proper classic integral over-lattice cannot exist
when the initial volume order is at most one.

The table-level endpoints are:

- `HeClassicPublishedEvenTestingIndex.model_volumeOrder_le_one`;
- `HeClassicPublishedEvenTestingIndex.model_isClassicMaximal`;
- `HeClassicPublishedOddTestingIndex.model_volumeOrder`;
- `HeClassicPublishedOddTestingIndex.model_isClassicMaximal`.

The supporting calculations cover both `C` columns, both valuation-parity
rows in odd rank, and the exceptional alternating `H_e` rows. The focused
Classic audit and canonical paper module compile with Lean 4.32.1, and the
new selected dependency reports contain exactly `propext`,
`Classical.choice`, and `Quot.sound`.

## Semantic boundary

This strengthens the audit of the literal table in Proposition 2.8: the
listed rows are not only classic integral but classic-maximal. It does not
prove odd testing sufficiency, does not convert ambient quadratic-space
isometry into integral lattice isometry, and does not classify every classic
maximal lattice by the published rows. In particular, it does not repair the
false literal Lemma 7.1(ii) or close the odd half of Theorem 1.3.
