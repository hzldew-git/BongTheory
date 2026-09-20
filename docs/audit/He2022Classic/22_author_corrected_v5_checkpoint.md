# Author-corrected v5 checkpoint

The semantic basis for the continuing formalization is the author-corrected
TeX file `classic_dyadic-n-uni-v5.tex`, approved for use on 9 September 2026.

- TeX SHA-256:
  `C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`
- rendered PDF SHA-256:
  `48F5B687DDA27D32732CF4DEA6F5B8FED378FAE420F0BCA49426C4F001721237`
- v4-to-v5 latexdiff TeX SHA-256:
  `B6F68AFAB1F228E905B551BE57A583685CBE8BF1BCCE346171C982DB5E638C7D`
- v4-to-v5 latexdiff PDF SHA-256:
  `41752BD699861E26C7DC2BED83FC47A8C3F0EEBB96ED5963F3D1EF30E48DB30A`

These manuscript artifacts are author-held and are not copied into the
repository or a Review Kit. The publisher version and arXiv v3 are retained
only as comparison sources.

## Source changes reflected in Lean

The v5 changes resolve the previously recorded proof-text issues rather than
asking the formalization to infer an unofficial repair.

- Lemma 2.9(iii) separates the defect-one odd `C_2` terminal calculation and
  uses the preceding defect-one adjacent product. The existing formal proof
  already uses this argument.
- Lemma 3.1(iv) now has the proof-supported range `2 < j <= m-2`, matching
  `he2022ClassicLemma31iv_corrected`.
- Lemma 3.4 replaces the incorrect parity sentence by good-BONG two-step
  monotonicity. The formal proof uses the same replacement.
- Corollary 3.13(iii) now includes the preceding-gap hypothesis already
  exposed by the formal endpoint.
- Lemma 7.1(ii) is restricted to `e=1` or to the two low-defect `C` target
  families. Its final assertion separately uses `C_1^(n+1)(1)` when `e>1`.

## New kernel-checked endpoints

`He2022ClassicLemma71V5.lean` proves the v5 Lemma 7.1 bridge in separate,
reviewable layers: ambient-space dichotomy, the general `e=1` representation,
both low-defect `C` columns, and the exceptional integral identity from
`C_1^(n+1)(1)` to `H_e^n(1)`.

`He2022ClassicSectionSeven.lean` then proves
`all_publishedOdd_implies_all_publishedEven_v5`, so every even test row one
rank lower is represented by a source representing the full odd table. This
feeds the already checked even `J2_E` necessity theorem and yields:

- `all_publishedOdd_implies_classicUniversal_v5_auto`;
- `he2022ClassicLemma74_odd_v5`;
- `he2022ClassicTheorem13_odd_literalMinimal_v5`, after combining sufficiency
  with the rowwise deletion witnesses of Lemma 7.11.

Thus both parity branches of Theorem 1.3 are formalized from the v5 source.
The counterexample to the obsolete broader publisher Lemma 7.1(ii) remains in
the repository as a regression theorem and is not used in the v5 proof.

## Scope and trust

This checkpoint closes the previously open local odd-testing obligation.  It
is a historical checkpoint: Report 23 subsequently added conditional Section
8 logic, and Reports 24 and 26 subsequently upgrade the odd-parity concern
to a checked counterexample to unrestricted Corollary 6.3. Concrete
number-field instances, independent
human semantic sign-off, exact clean-kit reproducibility, and deployment
remain separate gates. GitHub deployment is still disabled by the paper
manifest.
