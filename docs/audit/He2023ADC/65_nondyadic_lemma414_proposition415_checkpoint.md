# Non-dyadic Lemma 4.14 and Proposition 4.15 checkpoint

## Status

Checkpoint: `66c6e66`.

Classification: `CONDITIONAL_FORMALIZATION` for Lemma 4.14 and Proposition
4.15 over non-dyadic local fields.

## Authoritative source

The statement authority is Zilong He, *On n-ADC integral quadratic lattices
over algebraic number fields*, *Documenta Mathematica* 30 (2025), no. 4,
981--1022, DOI 10.4171/DM/1003. The publisher PDF has SHA-256

`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Lemma 4.14 and Proposition 4.15 occur on pp. 995--996. Lemma 4.14 says that
a maximal lattice represents every integral lattice whose ambient quadratic
space is represented, and hence is `n`-ADC for the literal range
`1 <= n <= rank M`. Proposition 4.15 characterizes rank-`n` `n`-ADC
lattices for `n >= 2` as precisely the maximal lattices.

## Formal deduction

`SectionFiveLaws.heADC2025Lemma414_represents` exposes the first sentence of
Lemma 4.14. `SectionFiveLaws.heADC2025Lemma414` retains both printed rank
bounds and derives its `n`-ADC consequence.

The earlier non-dyadic catalogue interface contained the necessity direction
of Proposition 4.15 as a field. That conclusion has been removed. The new
proof `CatalogueLaws.heADC2025Proposition415_isMaximal` instead:

1. chooses a maximal rank-`n` lattice on a represented ambient space;
2. applies `n`-ADC to represent that integral maximal lattice; and
3. transfers maximality across the resulting same-rank representation.

`CatalogueLaws.heADC2025Proposition415` combines this necessity argument with
Lemma 4.14 and retains the source hypotheses `n >= 2` and `rank M = n`.
The non-dyadic Theorem 1.10 catalogue now calls this derived necessity theorem
in its equal-rank and binary branches.

## Exposed mathematical inputs

This checkpoint does not construct concrete non-dyadic local lattices.
`SectionFiveLaws` still supplies the local maximal-lattice representation
fact used in Lemma 4.14. `CatalogueLaws` supplies existence of a maximal
lattice on the represented rank-`n` space and the same-rank maximality
transfer fact used in Proposition 4.15. These are lower-level source inputs,
not either final theorem statement, and must still be instantiated for a
concrete local-field completion.

## Mechanical evidence

The canonical paper entry, the expanded main audit, and the focused
Proposition 4.15 audit complete a 5,559-job build with Lean 4.32.1. All four
new endpoints report no axioms. The comment-aware scanner checks 2,777
tracked Lean sources, all 27 CI policy and scanner tests pass, changed Lean
lines are at most 100 columns, and `git diff --check` passes.

An exact clean Review Kit containing this checkpoint, concrete instances of
the listed local-lattice laws, and independent human semantic sign-off remain
separate gates.
