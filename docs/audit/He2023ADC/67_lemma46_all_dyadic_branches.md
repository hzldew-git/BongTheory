# He ADC Lemma 4.6: all dyadic branches

Authoritative source: Zilong He, *On n-ADC integral quadratic lattices over
algebraic number fields*, *Documenta Mathematica* 30 (2025), no. 4,
981--1022, pp. 993--994. Publisher-PDF SHA-256:
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Code checkpoint:
`bc043fea518a57864f93f22c072352f60f83afc6`.

Classification: `FULLY_FORMALIZED_DYADIC_SPECIALIZATION` /
`PROVISIONAL_MATCH`. This is not a claim for the unrestricted non-dyadic
part of the published lemma.

## Source statement and formal coverage

The publisher states that an `n`-ADC lattice `M`:

1. represents exactly one of `N_1^n(c)` and `N_2^n(c)` when its rank is
   `n+1`, or when its rank is `n+2` and the displayed determinant condition
   holds; and
2. when `FM` is isometric to `W_nu^(n+2)(c)`, represents every rank-`n`
   integral lattice outside `W_(3-nu)^n(c)`, hence every maximal one outside
   `N_(3-nu)^n(c)`.

`Bong.Bong.He2023ADCLemma46` supplies the actual-lattice endpoints for every
dyadic parity, column, and source-rank alternative:

- `heADC2025Lemma46iEvenCorankOne` and
  `heADC2025Lemma46iEvenCorankTwo`;
- `heADC2025Lemma46iOddCorankOne` and
  `heADC2025Lemma46iOddCorankTwo`; and
- `heADC2025Lemma46iiEvenFirst`, `heADC2025Lemma46iiEvenSecond`,
  `heADC2025Lemma46iiOddFirst`, and `heADC2025Lemma46iiOddSecond`.

All conclusions use `Lattice.Represents`, not only ambient-space or diagonal
representation. The negative half of each exactly-one conclusion is retained.
Part (ii) quantifies over an arbitrary integral rank-`n` target carrying a
good BONG, rather than only the named maximal representative.

## Semantic bridges

The public `hLarge` premise in part (ii) is equal-rank diagonal
representation from the published `W_nu^(n+2)(c)` row to the source BONG.
At equal finite rank this records the paper's ambient-space isometry premise.
The negated equal-rank diagonal representation in `hNotExceptional` records
`FN` not isometric to `W_(3-nu)^n(c)`. The proof then applies the exact
excluding-space result from Proposition 4.2(iii), transports representation
through exact BONG diagonalizations, and uses `n`-ADC-ness to lift ambient
representation to actual lattice representation.

For the corank-two clauses of part (i), the `IsSquare` premise is the
repository's ordinary-determinant translation already used for Lemma 4.5(i).
The even second row retains its published definedness boundary. The first
even clause of part (ii) also retains the definedness of the excluded
`N_2^n(c)` row; the corresponding rank-`n+2` second row is automatically
defined.

## Mechanical evidence

The focused audit `BongTest.He2023ADCLemma46Audit` prints all eight public
types and reports exactly the standard axiom set
`[propext, Classical.choice, Quot.sound]` for each. It completes 4,946 build
jobs. The canonical paper entry, canonical audit, and focused audit complete
5,560 build jobs. The comment-aware proof-command scanner checks 2,780
tracked Lean sources, all 27 CI unit tests pass, and JSON, line-length, and
staged-diff checks pass.

These are local kernel and source-audit results. Existing dependency
worktrees reported local-change warnings, so this checkpoint is not a clean
Review-Kit receipt. Exact clean extraction, GitHub exact-tag CI, and
independent mathematical sign-off remain separate gates.

Later status: Report 68 adds the complete non-dyadic deduction over explicit
lower-level laws. Its concrete local-field instance remains pending.
