# He Classic v6: concrete ramified local obstruction at finite completions

Status: `G_WORKTREE_DEVELOPMENT` / `FOCUSED_PARTIAL_FIDELITY_AUDIT` /
`DIRECT_SOURCE_CHECKED` / `MANIFEST_AUDITS_BUILT` /
`LOWER_GOOD_BONG_EXPLICIT` / `NOT_RELEASE_EVIDENCE`.

The semantic source is the author-approved `classic_dyadic-n-uni-v6.tex`,
SHA-256 `4D3903083188E2823CCA930477A43F82A1FC3C69AD96056ADB099D924B14EC5A`,
held outside Git and Review Kits. This report examines v6 Lemma 8.3,
TeX lines 1680-1693; it is not a whole-paper audit or a release receipt.

## Source claim and author clarification

For an even integer `n >= 2`, a finite ramified extension of dyadic local
fields `E_P/K_p`, and a classic `n`-universal integral lattice `L_p` of rank
`n+3`, the integral scalar extension `L_P` is not classic `n`-universal.
The author confirmed that the vectors denoted again by `x_i` after extension
are the canonical images `1 ⊗ x_i`, and that comparison with the constructed
upper lattice is by **integral quadratic-lattice isometry class**, not literal
equality of two subsets in a fixed ambient presentation. Neither rational
quadratic-space isometry alone nor equality of genera would suffice.

## Formal conclusion

`Bong.HeClassic2024NumberFieldScalarExtension.completionScalarExtension_not_evenUniversal_of_ramified`
in `Bong/Lattice/He2022ClassicCompletionDefectGrowth.lean` uses actual
height-one primes `p` and `P` of finite number fields with `P | p`, the
actual finite-completion algebra map, `p` dyadic, relative ramification
index greater than one, an **explicitly supplied** rank-`n+3` lower good
BONG on the specified lower lattice, even `n >= 2`, and
classic `n`-universality of the specified lower lattice. It concludes the
negation of classic `n`-universality of the **literal integral tensor scalar
extension** of that lower lattice. Lower classic integrality is extracted
from lower universality, not introduced as an additional mathematical
restriction. No common-ambient equality of a separate upper realization is
used.

The proof has the following checked dependencies:

1. Corollary 6.3 and the actual completion map give an integral isometry
   between the literal scalar extension and a mapped-value upper diagonal
   realization. Transport supplies a good BONG *on the literal scalar
   extension* with every exact value equal to the mapped lower value
   (Reports 48-49).
2. Theorem 1.1 on the hypothetically universal upper lattice and relative
   order scaling force its first `n+2` BONG orders, hence their lower
   counterparts, to vanish. A positive relative ramification index greater
   than one excludes the order-one alternatives.
3. On an actual dyadic lower completion, every zero-order square class has
   quadratic-defect order at least one. Proven completion defect scaling
   makes the mapped signed prefix defect strictly greater than one. The
   even branch of Theorem 1.1 then forces the final order to zero as well.
4. The same concrete scaling makes every mapped **unsigned** adjacent
   defect strictly greater than one. The proved local Theorem 1.5 forces
   the upper absolute ramification index to equal one. The ideal-theoretic
   ramification tower and the relative index greater than one contradict
   this conclusion.

The numerical core keeps signed-prefix and unsigned-adjacent defect bounds
as explicit premises; the finite-completion theorem discharges both from
the concrete completion map before reaching the source-facing conclusion.
Thus no field of the abstract `HeClassic2024ExtensionData.Lemma83Laws` is
being mistaken for an independently proved obstruction.

## Semantic boundary and remaining work

At the local theorem level, the rank, parity, ramification, universality,
specified scalar-extension lattice, and negative conclusion match the
author-clarified v6 claim **once a lower good BONG is supplied**. The source
chooses such a BONG for an arbitrary lattice. The current Lean endpoint
does not prove the existence of that choice for every lattice satisfying the
source hypotheses. This is a remaining quantifier/coverage obligation, not
merely a formatting detail: the theorem must not be advertised as the fully
unconditional Lemma 8.3 until a general good-BONG existence theorem is
connected. The generic basis-preserving
isometry of Report 50 is stronger vector-level evidence but is not required
for this class-level conclusion.

The theorem passed direct Lean source checking and a focused Lake target
build in the G worktree. The focused audit printed only `propext`,
`Classical.choice`, and `Quot.sound` for the new declarations. On this
uncommitted source, all eight manifest audit modules plus `BongTest.AxiomGate`
built successfully (`5689` Lake jobs), the focused enforcing axiom gate
reported `AXIOM_GATE_PASS: 63075 declarations checked`, the comment-aware
scan found no forbidden proof tokens in all `2822` staged/tracked Lean
sources (including the three new modules), five deployment-policy tests passed, and
JSON parsing and `git diff --check` passed. These are local development
checks, not clean-extraction, exact-head CI, or independent human review.

This does **not** instantiate the abstract global `Lemma83Laws` for every
global lattice. A general lower good-BONG existence bridge, concrete global
lattice localization, scalar-extension compatibility at `P`, Proposition
8.2's globalization ingredients, the
remaining Theorems 1.7-1.9 arithmetic instances, and independent author and
formalization-expert sign-off remain open. A local proof alone therefore
does not justify Grade B for the whole paper. The project's recorded grade
is unchanged pending a comprehensive re-audit.
