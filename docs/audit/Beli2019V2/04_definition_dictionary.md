# Definition Dictionary

| Paper notion | Lean notion | Alignment note |
|---|---|---|
| Dyadic local field \(F\) | `K` with `Field`, `CharZero`, `ValuativeRel`, `TopologicalSpace`, `DyadicContext`, plus local law classes | The extra laws are not shown to follow from being a finite extension of \(\mathbb Q_2\). |
| Quadratic space \(FM\) | `QuadraticSpace K V` | Uses a bilinear presentation whose diagonal is the quadratic value. |
| Ambient representation \(FN\to FM\) | `q.Represents r` | `q` is the larger/target space; `r` is the smaller/source space. |
| Integral representation \(N\to M\) | `Lattice.Represents q r L M` | `L` is the larger/target lattice; `M` is the smaller/source lattice. |
| Quadratic lattice | `Lattice K V` | Coupled to a quadratic space in representation statements. |
| BONG | `BONG q L n` | Carries an ordered orthogonal basis presentation. |
| Good BONG | `BONG.GoodBONG q L n` | Carries the good-BONG inequalities and length/finrank facts. |
| Rank \(m,n\) | Lean lengths `m + 1` and `n + 1` | One-based paper ranks are encoded by nonempty `Fin` lengths. |
| \(a_i,b_i\) | `GoodBONG.valueUnit` / `value` | Lean indices are zero based. |
| \(R_i,S_i\) | `GoodBONG.order` | Paper index \(i\) corresponds to Lean index `i - 1`. |
| \(\alpha_i,\beta_i\) | `GoodBONG.alphaValue` | Values live in extended nonnegative rationals as appropriate. |
| Quadratic defect \(d(c)\) | `Dyadic.quadraticDefect` and `GoodBONG.defectOrder` | The project bridges natural, rational, and top-extended codomains explicitly. |
| Truncated defect \(d[\varepsilon a_{1,i}b_{1,j}]\) | `GoodBONG.truncatedPrefixDefect` | Prefix caps are encoded directly rather than by an informal convention. |
| Prefix product \(a_{1,i}\) | `GoodBONG.prefixProduct i` | Empty and terminal prefixes are totalized by bounded natural indices. |
| \(A_i\) | `GoodBONG.representationAlphaValue` / related `representationAlpha` definitions | The formal development decomposes the paper's minimum into named candidates. |
| \(A'_i\) and alternate \(A_i\) | `Beli2019AuxiliaryAlpha*` and `Beli2019CappedDefectAlternative` declarations | Formalized as separate definitions and equality theorems. |
| Essential index | `Beli2019EssentialIndex` family | Boundary cases use typed index structures. |
| \(\mathcal B\) order | `Beli2019NestedOrder` family and `RepresentationOrderCondition` | Condition (i) is exposed directly in the main package. |
| Scalar approximation | `Beli2019Approximation` declarations | Square-class and defect bounds are explicit. |
| Space approximation | `Beli2019Approximation` and `Beli2019Lemma310*` | Left/right approximation is represented by prefix-space representation data. |
| \(N\leq M\) | `Beli2019RepresentationProblem` data and `RepresentationConditions` | The project does not overload Lean's ordinary lattice order for this paper-specific relation. |
| Conditions (i)--(iv) | `RepresentationConditions a b hRank` | A four-field proposition-valued structure. |
| Revised conditions | `RepresentationConditionsPrime a b hRank` | Replaces only the central representation condition. |
| Condition (iii) trigger | `centralAlphaTrigger` | Includes the order side condition and alpha sum inequality. |
| Condition (iii') trigger | `centralDefectTrigger` | Includes the same order side condition and the sum of two truncated defects. |
| Prefix diagonal representation | `DiagonalRepresents` | Used for the finite prefix conclusions in conditions (iii) and (iv). |
| Types I, II, III | `Beli2019IndexPType` and `Beli2019Lemma67*` data | Formal classification is split into profile structures and exhaustive cases. |
| Non-norm-generator lattice \(M'\) | `Beli2019Lemma71Data` and associated construction | The lattice and index-\(\mathfrak p\) certificate are constructed explicitly. |
| Counterexample descent | `Beli2019RepresentationProblem.Counterexample` and `Beli2019ProblemSmaller` | Measure is lexicographic rank/volume data, with proved well-foundedness. |

## Boundary conventions

The paper suppresses conditions whose indices do not make sense. Lean instead
uses dedicated finite index structures such as `RepresentationIndex` and
`CentralRepresentationIndex`, together with separate terminal definitions.
This is a sound way to avoid out-of-range expressions, but every endpoint
translation remains a semantic review point. The terminal cases of conditions
(iii), (iii'), and (iv) are handled by dedicated lemmas in the rank-completion
and Lemma 2.16 modules.

## Source/target convention

The names can be misleading unless read with the definitions:

- `target.Represents source` means an injective map from `source` into
  `target`;
- therefore `Lattice.Represents q r L M` means the paper's smaller lattice
  represented by the larger lattice;
- `a` is the larger-lattice good BONG and `b` is the smaller-lattice good
  BONG.

This orientation matches Theorem 2.1.
