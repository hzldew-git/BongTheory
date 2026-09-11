# Theorem 6.2 boundary and Remark 6.3 checkpoint

Status: Theorem 6.2 is `SEMANTIC_MISMATCH` at `n=2`; its `n>=4`
restriction is `FULLY_FORMALIZED` / `PROVISIONAL_MATCH`. Remark 6.3 is
`FULLY_FORMALIZED` / `PROVISIONAL_MATCH`.

Code checkpoint: `70580bbd2b4386bec53f046b54a96e3dd69bcaae`.

## Source authority

The sole semantic authority is the publisher version of record:

- Zilong He, *On n-ADC integral quadratic lattices over algebraic number
  fields*, *Documenta Mathematica* 30 (2025), no. 4, 981--1022;
- DOI: <https://doi.org/10.4171/DM/1003>;
- publisher PDF SHA-256:
  `E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Theorem 6.2 states that a rank-`n+2` lattice, for every even `n>=2`, is
`n`-ADC exactly when it is maximal or, only at `n=2`, is the exceptional
lattice from Lemma 6.12. Remark 6.3 gives the alternate exceptional model
`H perp <1,-Delta>` when `e=1`.

## Formal refutation at n=2

`GoodBONG.HeADC2025Theorem62BinaryStatement` freezes the exact rank-four
biconditional printed in Theorem 6.2. The theorem
`GoodBONG.not_heADC2025Theorem62BinaryStatement` proves its negation.

The witness is the already audited boundary lattice in `W_2^4(Delta)`. It is
an actual integral 2-ADC lattice, not merely a numerical order profile. It is
not maximal. A new ambient-space proof also shows that it cannot be isometric
to the Lemma 6.12 exceptional lattice: the former lies in the second member
and the latter in the first member of the proved nonisometric
`W_1^4(Delta)`/`W_2^4(Delta)` pair. Thus the witness satisfies neither branch
of the printed conclusion.

This is a direct counterexample to Theorem 6.2 itself, not only a failure of
its printed proof. The counterexample is nonvacuous over `Q_2` through the
existing concrete boundary module.

## Correct n>=4 theorem

`Lattice.heADC2025Theorem62_of_four_le` proves that, for every `k>0`, an
arbitrary full lattice of rank `2*k+4` is `(2*k+2)`-ADC if and only if it is
maximal. This is exactly the `n>=4` restriction of the published theorem.

The necessity proof diagonalizes an arbitrary ambient space and applies the
complete even-dimensional exhaustion from Proposition 4.2(ii). It handles
both columns and splits every scalar parameter into three cases:

- the square class of `1`;
- the square class of `Delta`;
- the sharp domain outside both classes.

Square changes of parameter are transported by explicit ambient isometries.
The six resulting branches invoke precisely Lemma 6.8(i)--(vi), with the
proved `n>=4` boundary in clause (iv). Each branch gives integral isometry to
the appropriate maximal lattice. The converse is the general
maximal-implies-ADC theorem. No representative system, ambient classification
premise, or good BONG remains in the public statement.

## Remark 6.3

`GoodBONG.heADC2025Remark63` proves an actual integral lattice isometry. Under
`ramificationIndex K = 1`, the raised exceptional tail coefficient is proved
equal to `-Delta`; an exact good BONG on `<1,-Delta>` is constructed, and the
two full quaternary BONG value sequences are identified coordinate by
coordinate. The resulting value-preserving BONG isometry gives

`H perp <1,-Delta*pi^(2-2e)> ~= H perp <1,-Delta>`.

This is stronger than an equality of square classes and matches the integral
isometry asserted in the remark.

## Mechanical trust checks

The three new modules, canonical paper entry, and full audit compile directly
with Lean 4.32.1. Eight new transitive dependency reports contain exactly
`propext`, `Classical.choice`, and `Quot.sound`. The focused enforcing gate
checks 57,933 declarations. The comment-aware scanner checks 2,711 tracked
Lean sources and finds no forbidden proof token outside comments. All new
source lines satisfy the 100-column limit.

Exact-revision Review Kit CI and release promotion remain separate deployment
gates. Human author, domain-expert, and formalization-expert decisions remain
unsigned.

## Consequences for coverage

Remark 6.3 raises the count of fully matched Section 6 items to 10/12. The
other two numbered items, Lemma 6.8 and Theorem 6.2, each contain a false
`n=2` boundary. Their valid clauses or restriction are proved, and their
invalid statements are formally refuted. Section 6 is therefore completely
triaged theorem by theorem, but it is not a section in which all publisher
statements can receive proofs.

Any downstream theorem that invokes the unqualified published Theorem 6.2
must be re-audited. This report does not automatically invalidate every such
result, but the printed dependency can no longer be accepted without a new
argument or a corrected exceptional list.

## Author review card

Reviewers should confirm:

1. the frozen binary biconditional is exactly the `n=2` specialization of
   Theorem 6.2;
2. the two quaternary ambient spaces used to separate the counterexample and
   Lemma 6.12 lattice are the nonisometric pair in Proposition 4.2(i);
3. the `n>=4` proof exhausts both columns and all three parameter domains;
4. the coefficient and lattice model in Remark 6.3 matches the publisher's
   sign and normalization conventions.

Author decision: unsigned. Domain-expert decision: unsigned.
Formalization-expert decision: unsigned.
