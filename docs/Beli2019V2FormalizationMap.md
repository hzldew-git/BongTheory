# Beli 2006/2019 representation formalization map

## Authoritative sources

The formalization uses the revised arXiv v2 of Beli's 2019 paper as the
proof source and the 2006 paper as the public specification.

- 2019 PDF: `Beli - 2019 - Representations of quadratic lattices over dyadic local fields-v2.pdf`
- 2019 TeX: `Beli - 2019 - Representations of quadratic lattices over dyadic local fields-v2.tex`
- arXiv version: `1905.04552v2`, 30 May 2022, 139 pages
- PDF SHA256: `1669C626A6D01AF297E07C2CB9584C5BD34F4CEE0F2B188EE0B351BD091C387C`
- TeX SHA256: `00D58B232A331E559D175C2DF383DE82A49BC7B044E035092B7AC96015858292`

The v2 condition `(iii')` following Theorem 2.1 is part of the target. It is
not present in the earlier local v1 snapshot and must not be omitted.

## Paper-to-Lean map

| 2006 source | 2019 v2 source | Lean layer |
|---|---|---|
| Definition 4.1, Lemma 4.2 | Definition 1, Lemma 1.2 | truncated defects and invariance |
| Definition 4.3 | Definition 4 | `representationAlpha` and terminal adjustment |
| Theorem 4.5 | Theorem 2.1 | `RepresentationConditions` and the final equivalence |
| Definitions 5.1-5.2 | Definitions 9-10 | approximation and Jordan data |
| Lemmas 5.3-5.7 | Section 3 | approximation/Jordan comparison |
| Section 6 | Sections 4-9 | transitivity, reduction, and final induction |

## Milestone routing

- M119: common defect arithmetic, Lemma 4.2, and Definition 4 invariance.
- M120: Definitions 2-3 and Lemmas 1.6-1.8.
- M121: sequence reversal, `B_n(2e)`, and reverse-dual order sequences.
- M122: the `W`-sequence and `W(L*) = W(L)*`.
- M123: determinant endpoint and discharge of the prefix-change interface.
- M124: Lemma 1.3, the Lemma 1.5 parity mechanism, and v2 condition (iii').
- M125: Section 3 approximation definitions, invariance, and propagation.
- M126: Lemma 3.2's Jordan-block scalar approximation induction.
- M127: Corollary 3.3's exact complementary-prefix dual transport.
- M128: Lemma 3.8 trigger invariance and the explicit representation bridge.
- M129: Definition 4 approximation formulas and Lemma 3.10(ii).
- M130: condition (i) transitivity and the direct condition (ii) branch.
- M131: Definition 7 and duality of essential indices.
- M132: Section 4 key-lemma branches and the complete condition (ii) assembly.
- M133: Section 4 representation certificates and four-condition composition.
- M134: Lemma 5.5(i), cumulative sums in the order poset.
- M135: Lemma 5.5(ii)-(iii), suffix sums and fixed-volume rigidity.
- M136: Lemma 5.5(iv), interval gaps and equality.
- M137: Lemma 5.6, adjacent-pair equality propagation.
- M138-M140: Lemma 5.6(i)-(ii), minimum, maximum, and extremal profiles.
- M141: Lemma 5.7's complete order-theoretic profile.
- M142: Corollary 5.8's order reconstruction formula.
- M143: Corollary 5.9(i)'s second-order criterion.
- M144: canonical maximal plateau and tail-threshold indices.
- M145: Corollary 5.9(i), projected norm-ideal inclusion and equality.
- M146: Corollary 5.9(ii), the three sufficient goodness conditions.
- M147: Corollary 5.10's tail-stable prefix-extension induction data.
- M148-M152: prescribed heads, exact one-step comparison data, good-tail
  replacement, ambient-prefix semantics, and comparison-data constructors.
- M153-M156: adjoining the norm generator, Lemma 5.7's enlarged lattice,
  nested order, and volume-order identities.
- M157-M162: projection under rescaling, isometric good-BONG transport, the
  enlarged candidate, and the complete Lemma 5.7 comparison datum.
- M163-M167: automatic comparison choice, automatic one-step extension, and
  the arbitrary-length ambient-prefix conclusion of Corollary 5.10.
- M168: scalar and prefix-product consequences of ambient-prefix agreement.
- M169: the odd cumulative-order branch and vanishing truncated defect.
- M170: pointwise assembly of the common-approximation and odd-order branches
  into condition 2.1(ii).
- M171: Lemma 5.13's common-or-odd dichotomy and its global defect-condition
  consequence.
- M172: Lemma 5.17's alpha comparison, prefix agreement, and Corollary 5.10
  bridge.
- M173: the complete index-`p` Section 5 package, including conditions (ii),
  (iii), (iv), and the revised condition (iii').
- M174: prime-step chains, Section 4 composition, and necessity for literal
  same-rank inclusions.
- M175: the well-founded Section 7--9 descent with the Lemmas 9.3, 9.6, and
  9.12 outcomes.
- M176: unequal-rank completion, necessity, sufficiency, and both forms of
  Theorem 2.1.
- M177--M196: Definitions 4--5 and the complete proof of Lemma 2.16,
  including its ordinary and exceptional terminal indices.
- M197: the shifted alternating Jordan block in the exceptional unary case
  of Section 5.4's proof of condition 2.1(i).
- M198: the proper unary block with lowered left and raised right endpoints
  in Section 5.4's proof of condition 2.1(i).
- M199: the general equal-scale Jordan block comparison, using ordered norm
  entries and equality of adjacent sums in Section 5.4.
- M200: the pointwise Section 5.4 certificate whose direct and Jordan-pair
  constructors assemble to the complete condition 2.1(i) order relation.
- M201: integration of that explicit order certificate into Section 5 and
  removal of `Beli2019OrderNecessityLaws` from Theorem 2.1's assumptions.
- M202: DVR factorization of every nonzero Smith coefficient as a power of
  the selected uniformizer times a unit of the normalized valuation ring.
- M203: Smith normal form for a lattice inclusion, with all diagonal units
  absorbed into the small-lattice basis so only uniformizer powers remain.
- M204: the one-coordinate uniformizer scaling, proved to be a literal
  index-`\mathfrak p` lattice inclusion with volume-order increment two.
- M205: strong induction on the total Smith exponent, constructing a finite
  index-`\mathfrak p` chain for every literal lattice inclusion.
- M206: correction of the zero-length certificate so that two different
  good BONGs of the same endpoint lattice can be related explicitly.
- M207: removal of `Beli2019PrimeChainLaws`; the prime-index chain is now
  constructed in Lean from Smith normal form, and only its Section 4 and 5
  decorations remain as precise local interfaces.
- M208: the zero-length endpoint is proved directly.  The identity order,
  defect, central-prefix, and long-prefix conditions require no paper-specific
  law; only Corollary 3.11's change-of-BONG transport remains as
  `Beli2019Corollary311Laws`.
- M209: conditions (i) and (ii) in Lemma 3.10 are proved BONG-independent
  from good-BONG classification and capped-defect invariance.  Corollary 3.11
  is now derived; `Beli2019Lemma310RepresentationLaws` retains only the
  prefix-representation transport in conditions (iii) and (iv).
- M210: the numerical triggers in Lemma 3.10(iii)--(iv), including the
  exceptional terminal value `S_(n+1) + A_(n+1)`, are proved independent of
  both good BONGs.  `Beli2019Lemma310PrefixLaws` now isolates only the
  pointwise prefix-space representation bridge; the packaged Lemma 3.10 law
  and Corollary 3.11 are derived instances.
- M211: canonical unit-valued BONG prefixes are constructed, their diagonal
  determinants are proved equal to the corresponding prefix products, and
  every prefix is proved to be a two-sided approximation to itself.  The
  precise Lemma 3.8 bridge now transports this self-approximation to the
  original BONG, matching the construction used in Corollary 3.11.
- M212: Lemma 3.10 is restated at the arbitrary-approximation level used in
  the paper.  Concrete coordinate changes prove that complete BONG
  presentations represent one another; canonical prefixes, the Lemma 3.8
  bridge, and the four target/source replacement clauses now derive the
  pointwise change-of-BONG law.  Theorem 2.1 therefore depends publicly on
  the exact Lemma 3.8 and Lemma 3.10 approximation interfaces, rather than
  directly assuming the conclusion of Corollary 3.11.
- M213: the Lemma 3.8 interface is removed.  Its bridge is made conditional,
  exactly as in Definition 10, and the canonical-prefix case needed by
  Corollary 3.11 is proved from the 2009 classification theorem.  The left
  endpoint is the zero-dimensional representation, internal boundaries use
  the classification prefix condition, and the right endpoint uses the
  concrete full-BONG coordinate change.
- M214: the central replacement in Lemma 3.10 is corrected to depend on both
  conditions 2.1(i) and 2.1(ii), as in its invocation of Lemma 2.18.  The
  three parity cycles of Lemma 1.5 are extracted into the paper-independent
  `DiagonalRepresentationParityLaws`; the two logical consequences needed by
  the central target/source replacements are proved from `EvenTruthParity`.
- M215: both central target/source replacements in Lemma 3.10(iii) are proved
  from the two scalar alternatives of Lemma 2.18, Definition 10's left/right
  approximation clauses, the quadratic-defect criterion for the Hilbert
  symbol, and the generic Lemma 1.5 parity cycles.  The rational `WithTop`
  defect scale is connected rigorously to the underlying `ℕ∞` Hilbert-symbol
  law.  The former four-field `Beli2019Lemma310ApproximationLaws` is removed;
  only the two long-prefix clauses of (iv) remain isolated.
- M216: both scalar alternatives of Lemma 2.18 are proved.  Remark 1.1 is
  derived from Beli 2009, Corollary 2.5(i); the capped quadratic-defect
  triangle alternative and its `WithTop` arithmetic are proved separately.
  The former paper-specific Lemma 2.18 interface is removed, so the central
  clauses of Lemma 3.10 now depend only on the reusable local alpha,
  Hilbert-symbol, and parity foundations.
- M217: both long-prefix replacements in Lemma 3.10(iv) are proved from
  condition (iv)'s order inequalities.  These inequalities force the relevant
  alpha above `2e`; determinant approximation then gives equality of square
  classes, and generic codimension-one Witt cancellation identifies the
  approximating space with the BONG prefix.  The paper-specific long-prefix
  interface is removed.
- M218: Lemmas 2.20--2.21 are separated into their two geometric cases.  The
  equal-rank case is constructed from the literal image lattice of an ambient
  isometry; the strict-rank case retains only the deep orthogonal-complement
  construction as a local interface, while all four representation conditions
  are transported by proved prefix and scalar agreement theorems.
- M219: the Section 7--9 induction measure is the concrete lexicographic pair
  `(rank, volume gap)`.  Its well-foundedness and both decrease constructors
  are proved, and Section 9 is split into the exact Lemmas 9.3, 9.6, and 9.12
  branches used by the final contradiction.
- M220: Lemma 7.1 is formalized as the full sublattice of non-norm generators.
  Additive closure follows from Beli 2003, Lemma 3.19's mixed-pairing order;
  residue-field square roots reduce every vector modulo this sublattice to the
  norm-generator line.  A sheared adapted integral basis and a one-coordinate
  uniformizer scaling then prove the literal index-`p` inclusion, with the
  exact volume jump forced by the general even volume-jump theorem.
- M221: Lemma 7.3(i) is proved from the monotonicity of `R_i + alpha_i`, an
  explicit adjacent plateau calculation, and finite transitivity of parity.
  Part (ii) is then derived exactly as in the paper by constructing the
  reverse-dual good BONG and transporting orders, gaps, alpha values, and
  interval indices.  No Lemma 7.3-specific local-law interface is introduced.
- M222: Lemma 6.6 is proved directly from the two-step monotonicity of a good
  BONG.  Equal same-parity endpoints force every intervening order into one
  congruence class and bound all internal forward gaps by `2e`; opposite-parity
  endpoints in descending order give an even closed interval sum.  The proof
  uses explicit finite-index interval sums and introduces no Section 6 law.
- M223: Lemma 6.5 is derived from condition 2.1(ii).  The displayed prefix-sum
  congruence makes the comparison-prefix product have odd valuation, hence
  zero capped defect.  Expanding the half-gap, primary, and secondary
  candidates of `A_i` then proves the two cross-order alternatives used in
  Lemma 6.7, without adding a Lemma 6.5 interface.
- M224: the fixed-total-gap opening of Lemma 6.7 is formalized.  Every target
  order is at most two above the matching source order, every prefix gap is
  `0`, `1`, or `2`, and an entry attaining gap two forces equality of the
  complementary prefix and suffix sums.
- M225: the gap-two branch now constructs the first and last unequal indices
  by finite minima and maxima.  Lemma 5.6 supplies both constant parity chains
  and all adjacent-pair equalities surrounding the gap-two anchor.
- M226: in the branch with no pointwise gap two, finite prefix-gap extrema
  produce the last zero before the first two.  They are strictly separated;
  the two transition entries rise by one and all intermediate entries agree.
- M227: the no-gap-two branch now also has its outer profiles.  Prefix gap zero
  gives the left prefix equality; prefix gap two plus total gap two gives the
  right suffix equality; Lemma 5.6 then supplies the first/last difference
  chains and adjacent-pair equalities shared by types II and III.
- M228: the middle-interval induction of Lemma 6.7 is proved for abstract
  order sequences.  Once its first source entry equals the left target
  boundary, two-step monotonicity and either cross-order alternative propagate
  that value through every common entry before the right transition.
- M229: each intermediate prefix gap one is converted into the exact parity
  hypothesis of Lemma 6.5.  Its two concrete BONG inequalities are translated
  back to zero-extended order sequences and supply the cross alternatives used
  by M228.
- M230: the left seed `R_{t+1}=S_t=R+1` is proved.  The proof handles both
  positions of the first difference, derives the final outer pair equality,
  and uses Lemma 6.6 to exclude the two parity-obstructed alternatives.  The
  seed and M228 then give the full constant middle interval.
- M231: Lemma 6.5 at the final middle prefix gives `S-1 <= R+1`; strict
  inequality would make the final source and target gaps nonpositive with
  opposite parity.  Lemma 6.6 rules this out, proving `S-R=2`.
- M232: all preceding layers are assembled into the exhaustive type-I,
  type-II, and type-III classification of Lemma 6.7.  The gap-two branch is
  type I, adjacent prefix transitions are type III, and longer transitions
  are type II with the verified middle plateau and endpoint relation.
- M233: finite interval congruences are summed and attached to a controlled
  prefix, providing the reusable arithmetic core of Lemma 7.2.
- M234: Lemma 6.6 and the type-II plateau give every entrywise congruence in
  Lemma 6.11(ii), including both transition entries.
- M235: the type-II entrywise profile is summed to obtain all four formulas
  of Lemma 7.2(ii), with the one-based odd-endpoint correction checked.
- M236: in the nonoverlapping type-III branch, the Lemma 6.9 boundary bound
  forces the central gap to be nonpositive and even; Lemma 6.6 then proves
  the two constant parity classes of Lemma 6.11(iii).
- M237: the two type-III parity classes are summed to prove Lemma 7.2(iii).
- M238: finite minima and maxima recover the canonical type-I switches from
  the arbitrary gap-two anchor used by the proof of Lemma 6.7.
- M239: Lemma 6.6 controls the four long type-I parity blocks, while the two
  pair identities of Lemma 6.7 prove the otherwise uncovered crossing terms;
  this is Lemma 6.11(i).
- M240: summing the type-I blocks proves the four formulas of Lemma 7.2(i).
  The even left switch removes its correction and the even right switch gives
  the paper's `-1` correction.
- M241: Remark 1.1 is propagated from any earlier capped adjacent defect to a
  later alpha value, using the proved endpoint monotonicity and alpha caps.
- M242: the type-III case needed from Lemma 6.9(i) is proved by defect
  domination.  Condition 2.1(ii) forces the central primary candidate to
  vanish, contradicting every branch under `alpha > 1`.  Consequently the
  public Lemma 6.11(iii) and 7.2(iii) wrappers now derive their alpha bound
  from `RepresentationDefectCondition` rather than accepting it as input.
- M243: Lemma 7.4 is proved in full.  Alternating adjacent capped defects are
  joined by the domination principle for (i)--(ii).  In (iii), the endpoint
  alpha caps give the reverse inequalities, while Corollary 2.3 identifies
  both critical expressions with the neighboring alpha values.
- M244: the arithmetic core of Lemma 7.5 is proved.  Its endpoint hypotheses
  force the even and odd order chains to be constant at `R` and `R - 2e`,
  respectively; the terminal alpha vanishes and Lemma 7.4(i) supplies the
  capped-defect bound `2e`.  The binary-lattice and quadratic-space
  classifications are tracked separately as the remaining geometric part.
- M245: the splitting part of Lemma 7.5 is reduced to the existing concrete
  decomposition witnesses of Beli 2003, Corollary 4.4.  Every descending
  `R, R - 2e` pair is the middle binary component of a three-block
  orthogonal decomposition, and every boundary between consecutive pairs
  admits the corresponding two-block split.
- M246: the endpoint square-class part of Lemma 7.5 is isolated from the
  paper-specific argument.  Each descending binary block has parameter class
  `-1/4` or `-Δ/4`, using a general dyadic discriminant-class law.  The
  remaining geometric refinement is to assemble these alternatives over the
  entire alternating segment.
- M247: every binary BONG is identified with its normalized explicit Gram
  model by an actual lattice isometry.  Equality of endpoint parameters modulo
  a valuation-unit square is realized by scaling the second integral basis
  vector, so the two endpoint square classes give two concrete model lattices.
- M248: the model theorem is applied to every descending pair in Lemma 7.5.
  Each pair now comes with both its three-block orthogonal split witness and a
  lattice isometry to the `-1/4` or `-Δ/4` rescaled endpoint model.
- M249: the arbitrary integral shear is removed.  Both endpoint classes use
  the fixed shear `1/2`, giving the paper's two standard binary lattices; their
  ambient quadratic spaces are explicitly diagonalized as `[a,-a]` and
  `[a,-Δa]` by a concrete linear isometry.
- M250: Lemma 7.5 is assembled over the complete alternating segment.  The
  certificate includes the segment itself, the fixed lattice and diagonal
  space model of every descending pair, and an actual orthogonal split at
  every boundary between consecutive pairs.
- M251: Lemma 7.6's initial type-I branches are derived from the canonical
  transition indices.  Strictly before the switch the alternating target
  prefix defect is computed exactly; at the switch boundary its required
  lower bound follows directly from Lemma 7.4(i).
- M252: Lemma 7.11 is proved for ternary lattices in one ambient quadratic
  space.  Equality of the first alpha forces equality of the second, the two
  prefix-defect bounds follow by two-step domination, and property P6 makes
  the final representation condition vacuous; Beli 2009 classification then
  gives the desired lattice isometry.
- M253: the switch-boundary dichotomy in Lemma 7.6 is proved abstractly.
  Alpha integrality below `2e`, P2, and P3 show that a jump at most `2e`
  gives equality with the next alpha, whereas a jump of `2e+1` gives the
  required defect lower bound `2e`.
- M254: Lemma 7.14(i)'s alternating plateau is proved from the literal
  minimal-even-endpoint predicate.  Two-step monotonicity pins all low-parity
  orders at `R-2e+1`, and the adjacent-gap lower bound then pins the
  intervening high-parity orders at `R+1`.
- M255: the type-I/type-II split following Lemma 7.14 is proved exhaustive
  and disjoint.  Same-parity monotonicity makes the first order after the
  selected segment at least `R+1`; integrality leaves equality (type II) or
  a jump of at least two (type I), with the terminal case included in type I.
- M256: the full stopping clause in Lemma 7.14 is formalized.  It gives the
  right boundary order `R-2e+2`; in type II this equality is excluded because
  it would create the negative odd adjacent gap `1-2e`, so the sharp gluing
  bound is `R-2e+3` as in the paper.
- M257: the abstract switch dichotomy of M253 is instantiated at the canonical
  type-I index.  Lemmas 6.6 and 6.7 force the crossing gap to be odd and the
  same-parity orders to differ by one.  Together with M251 this proves both
  boundary alternatives of Lemma 7.6, leaving only Lemma 6.9's `beta <= 1`
  premise to discharge.
- M258: Lemma 6.9(i)'s remaining type-I bound `beta <= 1` is derived from the
  odd valuation of the adjacent product crossing the canonical switch.  Its
  quadratic defect is zero, so the relevant right-defect candidate is exactly
  one.  This discharges the final premise of the type-I case of Lemma 7.6.
- M259: the two numerical branches of Lemma 7.7 are formalized.  A
  nonpositive target follows from defect nonnegativity; on an order plateau,
  Lemma 7.4(i) and `alpha >= 2` give the stated lower bound after removing
  prefix caps.  The required source-order plateau through the canonical
  type-I right switch is derived directly from Lemma 6.7.
- M260: on the canonical type-I middle interval, the target order is proved
  to be exactly two above the source order.  Equality of the corresponding
  even `W`-coordinates then gives `alpha = beta + 2`, so property P2 closes
  the `alpha >= 2` premise in the middle branch of Lemma 7.7.
- M261: Lemma 5.5(iii) is localized to an arbitrary contiguous interval.
  The interval inherits Beli's order relation from direct comparisons at
  its two endpoints; equality of its segment sums then forces equality of
  every coordinate.  This is the sequence-theoretic core of Lemma 6.9(v).
- M262: the localized rigidity theorem is instantiated on the canonical
  type-I `W`-block.  Its even coordinates yield
  `R_i + alpha_i = S_i + beta_i` throughout the block, and hence Lemma 7.7's
  middle branch, from the two boundary comparisons and the telescoping sum.
- M263: every even-odd pair of `W(L)` is proved to telescope to the adjacent
  order sum `R_i + R_(i+1)`.  A general paired-segment induction therefore
  turns equality of adjacent order sums into equality of the full type-I
  `W`-block sum required by M262.
- M264: the canonical type-I profile is sharpened to the exact alternating
  order gaps `+2` at even positions and `-2` at odd positions.  Adjacent order
  sums, and hence the complete type-I `W`-block sum, are now equal by theorem;
  Lemma 7.7's middle branch retains only the two boundary comparisons and the
  global `W`-order relation from Lemma 6.9(v).
- M265: the half-integral endpoint argument in Lemma 6.9(v) is isolated as a
  general theorem for Beli's sequence order.  An adjacent-pair inequality and
  a one-half bound on the neighboring coordinate force the direct endpoint
  comparison once both endpoint coordinates are rational integers.  The
  first and last coordinates are handled without extra hypotheses.
- M266: Lemma 6.6 and Corollary 2.8 are connected to the canonical type-I
  interval.  Every internal adjacent order gap is even, the relevant even and
  odd coordinates of `W(L)` and `W(M)` are rational integers, and M265 turns
  the two neighboring-coordinate half-unit estimates into the exact boundary
  comparisons needed by M264.  Thus Lemma 7.7's middle branch now retains only
  those two local estimates and the global `W`-order relation.
- M267: the left neighboring-coordinate estimate in Lemma 6.9(v) is reduced
  to the precise `alpha <= 1` assertion from Lemma 6.9(i).  The canonical
  type-I profile gives the preceding target order, Corollary 2.8 forces the
  preceding source alpha to equal one, Corollary 2.3 transports the source
  coordinate, and Corollary 2.9 bounds the odd target coordinate by one half.
- M268: the dual right-tail calculation in Lemma 6.9(v) is formalized when
  the canonical right switch precedes the last unequal order.  The source
  two-step jump and the intervening source-target shift are derived from the
  canonical profile.  The next target alpha is forced to equal one from the
  corresponding `alpha <= 1` input, and Corollaries 2.3 and 2.9 give the
  required following-coordinate half-unit estimate.
- M269: the finite minimal pivot used in the type-I proof of Lemma 6.9(i) is
  constructed.  Among the even indices before the left switch it is the
  first whose following source order reaches the terminal odd-position
  value.  Two-step monotonicity proves strict inequality before the pivot
  and equality from the pivot through the end of the left tail.
- M270: the pivot alpha bound is propagated to the entire even left tail.
  Monotonicity of `R_i + alpha_i` controls indices before the pivot, while
  antitonicity of `-R_(i+1) + alpha_i` and M269's constant tail control the
  remaining indices.  Consequently M267's neighboring-coordinate estimate
  now retains only the single pivot inequality `alpha_l <= 1`.
- M271: the remaining pivot inequality `alpha_l <= 1` is proved directly
  from the representation defect condition.  Pair equality gives cumulative
  order gap one at `l`; capped adjacent defects propagate above the critical
  cut.  The half-gap and primary candidates contradict that strict bound,
  while minimality of `l` makes the secondary candidate positive.
- M272: pivot existence, M271, and M270 are assembled into the unconditional
  source-alpha bound on the whole even left tail.  The target-alpha bound is
  propagated backwards from the already proved switch estimate, and the
  left neighboring `W`-coordinate conclusion of Lemma 6.9(v) is discharged.
- M273: the right-tail dual pivot is constructed as the last odd index on the
  initial target-order plateau.  Target odd orders are constant up to this
  pivot and strictly larger afterwards.
- M274: a bound `beta <= 1` at M273's pivot is propagated over every odd
  target-alpha in the right tail.  This reduces the right neighboring
  `W`-coordinate estimate to one canonical pivot inequality.
- M275: Remark 1.1 is proved in the rightward direction: a later adjacent
  capped defect controls every earlier alpha after the exact order shift.
  The proof uses P1 directly and introduces no additional local-law interface.
- M276: for equal-rank good BONGs in one quadratic space, the capped comparison
  defect at full rank is infinite.  This gives the global endpoint case of the
  right-boundary argument without adding a paper-specific axiom; a profile
  ending before full rank still requires the prefix-rigidity/duality step of
  Lemma 6.3.
- M277: exact alternating order shifts are proved on the canonical type-I
  right tail.  Iterating the equal adjacent-pair sums gives cumulative order
  gap one at the maximal right pivot.
- M278: both local capped defects are shown to lie strictly above the pivot
  cutoff.  Assuming the comparison defect at the right boundary, the
  domination inequality propagates this strict bound backwards, two entries
  at a time, to the pivot.
- M279: the representation-alpha candidate analysis at the maximal right
  pivot is completed.  The primary and half-gap branches are impossible; the
  remaining conclusion `beta_p <= 1` is reduced transparently to the right
  boundary seed and positivity of the optional secondary candidate.  These
  are the precise obligations to be discharged by Lemma 6.3 and its dual.
- M280: the optional secondary candidate is proved strictly positive whenever
  the maximal right pivot is not adjacent to the last unequal order.  Its
  coefficient is the strict increase along the target odd-order tail.
- M281: Lemma 6.3 is proved by strong induction for equal-rank BONGs whose
  orders agree before the comparison index.  All three explicit candidates
  are bounded from below by the preceding source alpha.
- M282: the right-end, same-space form of Lemma 6.3 is proved by reverse
  induction.  Full-rank comparison supplies the terminal case, and suffix
  order agreement identifies the representation invariant with the target
  alpha immediately to its left.
- M283: M282 and condition 2.1(ii) give the concrete comparison-defect seed
  after the last unequal order.  Target endpoint monotonicity places this
  seed strictly above the maximal-pivot cutoff whenever `beta_p > 1`.
- M284: the terminal optional-secondary branch is closed without a new law.
  Nonpositivity forces the first exterior target order to be exactly one
  above the pivot order; Lemma 6.11(i) makes the intervening adjacent product
  odd, so its defect is zero and the right alpha candidate gives
  `beta_p <= 1`.
- M285: the interior and terminal secondary branches are assembled with the
  M283 boundary seed.  The maximal type-I right-pivot inequality
  `beta_p <= 1` is therefore fully concrete in the common quadratic-space
  setting used by the representation theorem.
- M286: the maximal-pivot bound is propagated over the complete odd right
  tail.  The first target alpha after the canonical right switch is therefore
  at most one, and the right neighboring `W`-coordinate estimate in Lemma
  6.9(v) follows from the already formalized Corollaries 2.3 and 2.9 argument.
- M287: the concrete left and right neighboring-coordinate estimates are
  assembled with boundary rounding and middle-block rigidity.  This proves
  the type-I part of Lemma 7.7 whenever the canonical right switch precedes
  the last unequal order; the remaining terminal switch is isolated as the
  reverse-dual endpoint used explicitly in the paper.
- M288: Lemma 7.8's central source arithmetic is derived.  The initial gap
  bound propagates to the type-III transition; Lemmas 6.9(i), 6.11(iii), and
  Corollary 2.8 force the central source alpha to equal one, while parity
  gives the sharp lower bound corresponding to `S - R >= 3 - 2e`.
- M289: the capped comparison defect is transported through reverse duality.
  Complementary prefix products differ only by the square of the total-value
  correction, and alpha caps reverse exactly.  Thus swapping a chosen pair
  of reverse-dual BONGs identifies every capped prefix defect with its
  complementary original defect, providing the common duality layer used by
  the remaining right-end and target-side arguments.
- M290: all three candidates defining the representation alpha are invariant
  under swapped reverse duality at complementary equal-rank boundaries.
  Hence both the `WithTop` invariant and its rational value are transported
  without a new local-law assumption.
- M291: condition 2.1(ii) is proved invariant under the same swapped
  reverse-dual construction.  The result packages compatible order, alpha,
  and capped-defect identities for later endpoint arguments.
- M292: reverse-negated prefixes are identified with negative complementary
  suffixes.  This proves duality of condition 2.1(i), the total order gap two,
  and every prefix-gap value.
- M293: the complementary transition of a type-III pair is constructed
  explicitly and completed to its full outer profile.  Applying Lemma 6.9(i)
  to that pair proves the target bound `beta_t <= 1`; central-gap equality,
  parity, and positivity then give the complete conclusions
  `alpha_t = beta_t = 1` and `S - R >= 3 - 2e` from Lemma 7.8.
- M294: the representation-alpha minimum is connected to its primary and
  secondary defect candidates.  Vanishing alpha now yields the exact central
  mixed-defect value needed in the first prefix computation.
- M295: the type-III secondary coefficient at the transition is proved
  positive from the central order profile and ramification bound.
- M296: the corresponding primary defect candidate is proved nonnegative.
  Together with M295 this excludes every negative candidate at the center.
- M297: the central representation alpha is therefore zero, and the mixed
  prefix defect is identified exactly with the order shift `R - S + 2`.
- M298: a strict comparison between the two capped factors gives a sharp
  multiplication formula.  Its zero-endpoint specializations identify mixed
  and self prefix defects without a new propagation interface.
- M299: the first source prefix value in Lemma 7.8 follows from the exact
  central defect and the sharp capped-defect formula.
- M300: Lemma 7.4(ii) is specialized to natural prefix indices, giving the
  right source plateau and the strict tail bound required for propagation.
- M301: the first source value propagates across every even prefix in the
  type-III interval, including the full-rank endpoint.
- M302: every nonterminal even target boundary has
  `R - S + 2 <= beta_(i-1)`, by the right plateau, P3 equality cases,
  parity, and integrality.
- M303: Remark 6.16 is formalized as a generic sharp right-prefix formula:
  when `A_i = beta_(i-1)`, the target prefix is the minimum of the source
  prefix and that target alpha.
- M304: every preceding alternating source alpha on the normalized left
  type-III profile equals one.  A core statement isolates the central-alpha
  input from the Section 7 wrapper.
- M305: Lemma 6.9(ii)'s left type-III classification is proved by strong
  induction over the explicit half-gap, primary, and secondary candidates.
- M306: swapped reverse duality transports M305 to the right interval and
  proves `A_i = beta_(i-1)` at every nonterminal even target boundary.
- M307: M302, M303, and M306 determine all nonterminal target prefixes; a
  full-rank infinity argument closes the endpoint.  The fixed-index theorem
  `beli2019Lemma78_typeIII` now contains every assertion of Lemma 7.8.
- M308: generic order-condition transport is isolated for unchanged entries,
  pointwise domination, and intervals beyond the last unequal order.
- M309: condition 2.1(i) is reduced to the finite altered interval in each
  of the three Lemma 6.7 profile types.
- M310--M315: the elementary type-I middle, both left outer intervals, the
  type-II constant middle, and both alternating right intervals are proved
  directly from the order profiles and the strict norm-ideal inequality.
- M316--M320: the third-BONG prefix parity calculation, hard type-II right
  class, transition predecessor, terminal determinant-parity argument, and
  the complete type-II branch of Lemma 7.9(i) are kernel checked.
- M321--M322: in the hard type-III class, the third self-prefix defect is
  strictly above the central mixed shift, so the comparison-prefix defect is
  exactly `R - S + 2`.
- M323--M325: the active representation-alpha candidate is extracted; Lemma
  7.8 excludes the half-gap candidate, and the primary candidate gives the
  required adjacent-pair inequality.
- M326: the source-alpha branch of Lemma 2.9 is proved from capped-defect
  domination and Remark 1.1, without a paper-specific replacement law.
- M327: Corollary 2.8 shows every nonzero alpha is at least one.  The unique
  zero-alpha exception is excluded by P2, two-step monotonicity, and the
  impossibility of a negative odd good-BONG gap.
- M328: the comparison-defect, half-gap, primary, current-defect, and
  source-alpha branches are assembled into the complete hard interior
  type-III adjacent-pair theorem.
- M329: the left outer, alternating right, and hard interior pieces are
  assembled for every nonterminal coordinate of the normalized full-span
  type-III branch.  The terminal coordinate remains a separate endpoint
  obligation because condition 2.1(i) has no pair alternative there.
- M584: the nonoverlapping type-III case-8 branch is closed at every even
  boundary.  Domination, integral and nonintegral candidates, and the
  equality-parity endpoint together give the required `B_i <= beta_i` bound.
- M585: the odd branch is extended to the full-rank endpoint by explicit
  source-prefix propagation and the full self-prefix defect formula.  Its
  domination, nonintegral, and equality cases then give the same beta bound.
- M586: strict and half-gap exits are assembled with the overlapping and
  nonoverlapping profiles.  Consequently Lemma 7.9(ii), case 8 is now
  complete for type I, type II, and type III, including full-rank endpoints.
- M587: the six pointwise cases of Lemma 7.9(ii), including both type-III
  overlap regimes and their endpoints, are assembled into a single theorem
  for each of types I, II, and III.
- M588: the three-type dispatcher packages the pointwise proofs in the
  explicit full-span special case.  The normalized classification used by
  the paper has only `first = 0`; removing the stronger terminal hypothesis
  from the type-II and type-III branches remains necessary before this can be
  called the complete condition 2.1(ii).
- M589: condition 2.1(i) is complete for the central-gap-one type-III branch.
  The formerly missing full-rank coordinate is discharged by Lemma 7.2(ii),
  the norm-ideal first-order bound, and full-determinant parity; no new local
  arithmetic interface is introduced.
- M590: condition 2.1(i) is complete for type I under the actual normalized
  hypotheses, with no full-span restriction.  The terminal right-switch
  equality branch retains the sharp primary-defect identity, rules out the
  lost one-unit shift by a parity-zero contradiction, covers the full-rank
  endpoint separately, and assembles the unchanged suffix into
  `beli2019Lemma79_i_typeI_orderCondition`.
- M591: Lemma 7.9(ii)'s type-II and type-III dispatchers now use the paper's
  normalized classification with an arbitrary common suffix.  The former
  full-span hypothesis is retained only by compatibility wrappers, and the
  normalized three-type result is wired into both representation-condition
  packages.
- M592: the decreasing-induction core of Lemma 7.10 is concrete.  The
  dependent relations `Lattice.CommonNormGeneratorExtension` and
  `BONG.PrefixLatticeExtension` reconstruct equality through any finite
  common prefix of norm generators.  The two parity chains of a good BONG
  also propagate the paper's last-two boundary estimates to every earlier
  prefix order.  Constructing the chain from the orthogonal-sum hypotheses
  and transporting the general case through reverse duality remain the next
  geometric obligations.
- M593: full lattice products now provide a concrete coordinate model for
  orthogonal sums.  Their norm ideal is proved to be the sum of the component
  norm ideals, so a component norm generator remains a norm generator of the
  product whenever the other norm ideal is contained in its ideal.  The BONG
  order version is exactly the norm-generator step used in the right-end
  proof of Lemma 7.10.
- M594: orthogonal projection along `(x, 0)` is now proved to be projection
  along `x` on the left factor and the identity on the right factor.  The
  induced equivalence `(x,0)^perp ≃ x^perp × W` identifies the projected
  product lattice with `pr_(x^perp)(L) × M` and is bundled as a lattice
  isometry.  The zero-dimensional left-factor endpoint is also treated
  canonically, so the recursion has a genuine base case.
- M595: the projection identity is lifted to an explicit recursive BONG
  concatenation for orthogonal products.  Its left and right value/order
  subsequences are proved unchanged, and an exact cross-boundary predicate
  yields preservation of good-BONG status.  Thus the product-geometric
  portion of the right-end case of Lemma 7.10 is kernel checked; connecting
  this construction to arbitrary internal BONG segments and then applying
  reverse duality are the remaining Lemma 7.10 obligations.
- M596: the right-end decreasing induction of Lemma 7.10 is represented by
  `BONG.OrthogonalPrefixData`.  Starting from an arbitrary replacement BONG
  at the stopping projection, it adjoins the unchanged heads one at a time
  through the proved projection-product lattice isometry.  The resulting
  BONG preserves every original prefix value/order and every stored
  replacement-tail value/order.  Its smart constructor derives the required
  norm-ideal containment directly from the paper's head-order inequality,
  and its output can be bundled as a good BONG from the lemma's explicit
  goodness hypothesis.  Constructing this certificate from a concrete
  `SegmentWitness`, and transporting the right-end result by reverse duality
  to the general internal case, remain the next Lemma 7.10 obligations.
- M597: the abstract certificate is now generated by the paper-facing
  `BONG.OrthogonalPrefixSeed`.  A stopping replacement may be imported from
  an arbitrary lattice-isometric model, with a dedicated
  `stopOfSegmentWitness` constructor for consecutive replacement blocks.
  The seed contains no ideal hypotheses: `toData` derives every one from
  comparison with the head of the fixed right BONG.  Finally,
  `GoodBONG.beli2019Lemma710RightEndData` feeds the two boundary comparisons
  into the previously proved parity-chain propagation theorem, yielding all
  decreasing-induction steps required in the `u = n` case.  The remaining
  geometric input for that case is the concrete lattice isometry expressing
  the hypothesis on the replacement block; the general `u < n` case still
  requires reverse-dual transport of this right-end theorem.
- M598: the right-end certificate now tracks ambient vectors, not only values
  and orders.  `OrthogonalPrefixData.baseAmbientVector` transports the
  replacement block through every projection-product isometry, while the
  unchanged prefix is proved to remain `(x_i, 0)`.  Matching these two literal
  vector blocks with a target BONG yields equality of its lattice with the
  original orthogonal product; `beli2019Lemma710RightEnd` combines this with
  the parity-chain order propagation.  Integral duality is functorial under
  lattice isometries, and the dual of a concrete orthogonal product is proved
  equal to the product of the component duals.  A reverse-dual good BONG is
  therefore transported to that concrete product with its vectors, reciprocal
  values, and negated reversed orders all verified.  The former
  `BONGStructuralLaws` dependency has been split into three independent
  interfaces; this step uses only the minimal `BONGReverseDualLaws` field.
  Eliminating that arbitrary-rank realization theorem (Beli 2003, Lemma 4.8)
  and assembling the two right-end applications remain the obligations for
  the general `u < n` case.
- M599: the right-end order interface has been reduced to the hypotheses in
  Beli's proof.  The converse bridge
  `BONG.head_order_le_of_normIdeal_le` turns inclusion of norm ideals back
  into comparison of head orders.  An `OrthogonalPrefixSeed` now has
  intrinsic stopping-block values, orders, and ambient vectors, independent
  of the later head-order proof used by `toData`; their agreement with the
  constructed data is proved recursively.  From the norm ideal of the
  stopping orthogonal product one obtains `S_s <= R_(t+1)`, while goodness of
  the proposed combined BONG gives `R_(s-2) <= S_s`.  Thus
  `beli2019Lemma710_previous_order_le_right_of_good` proves the formerly
  explicit penultimate comparison, and
  `beli2019Lemma710RightEnd_of_good` leaves only the paper's last-order
  hypothesis.  The entire bridge, including the new vector-coherence layer,
  is checked with only `propext`, `Classical.choice`, and `Quot.sound`.
  The next obligation is the general internal interval, obtained by two
  applications of this endpoint theorem across reverse duality.
- M600: the two endpoint applications in the general internal-interval case
  of Lemma 7.10 are now assembled in one kernel-checked theorem.  The
  right-end construction was first extended uniformly to the empty-prefix
  case and re-indexed by the number of unchanged prefix vectors.  Integral
  duality was then made injective on lattices, and an explicit factor-swap
  isometry was added so that reversing a BONG exchanges the two orthogonal
  factors exactly as in Beli's proof.  The theorem
  `exists_swappedReverseDual_with_values` records the transported vectors,
  reciprocal values, and negated reversed orders.  An
  `OrthogonalPrefixRawSeed` postpones the unknown stopping-product identity,
  while its synchronized `DualEndpointCertificate` proves that identity by
  the dual right-end argument.  Finally `beli2019Lemma710General` realizes the
  raw seed and applies the original right-end theorem, including both boundary
  cases through conditional endpoint hypotheses.  This completes the
  certificate-level assembly of general Lemma 7.10.  What remains is to build
  that certificate directly from the paper's literal consecutive-block
  replacement witness and to eliminate the arbitrary-rank
  `BONGReverseDualLaws` interface by formalizing Beli 2003, Lemma 4.8.
- M601: the original-side dependent certificate in Lemma 7.10 is now
  generated from the paper's literal unchanged-prefix condition.  Given that
  the first `steps` candidate vectors are `(x_i,0)`,
  `extractTargetPrefix` recursively transports the candidate tail through
  `(x,0)^perp ~= x^perp x W`, constructs the raw seed, and proves that its
  stopping vectors transport back to the literal candidate suffix.  The
  reverse-dual certificate is reduced to its unique stopping node, with all
  outer prefix constructors lifted automatically.  At that node,
  `DualEndpointCertificate.stopOfTargetPrefix` performs the same automatic
  extraction on the swapped dual target, so its only remaining geometric
  datum is the stopping product identity for the replaced block.  Thus
  `beli2019Lemma710General_of_targetPrefixStop` no longer exposes either
  recursive seed or either family of suffix-vector coherence proofs.  The
  next step is to derive that last stopping identity and the swapped-dual
  prefix agreement directly from the consecutive replacement witness and
  explicit reverse-dual realizations.
- M602: the swapped-dual prefix agreement in the second endpoint application
  is now derived rather than supplied.  The theorem
  `swappedReverseDualVector_prefix_eq_of_suffixVectors` computes directly
  that an unchanged literal right suffix `(0,x_i)` becomes the corresponding
  prefix `(x_i^*,0)` after reverse normalization and factor exchange; its
  family form also rewrites through explicit reverse-dual good-BONG
  realizations.  Consequently
  `DualEndpointCertificate.stopOfSuffixVectors` constructs the complete
  stopping certificate from the original candidate's unchanged suffix and
  the two reverse-dual vector formulas.  The only geometric datum still
  exposed at the stopping node is the dual lattice identity corresponding to
  the paper's equality of the consecutive replacement blocks.  The next
  obligation is to identify the twice-projected stopping lattices with the
  duals of those concrete `SegmentWitness` lattices, so that this identity is
  obtained from the stated block equality itself.
- M603: the hidden stopping lattice in Lemma 7.10 is now realized as the
  literal consecutive suffix segment of the candidate BONG.  The reusable
  `SegmentWitness` transport layer maps, unmaps, rebases, and lifts segments
  through ambient isometries while carrying explicit lattice isometries.
  `extractTargetPrefixSegment` follows every orthogonal-complement projection
  in `extractTargetPrefix`, builds the concrete suffix segment, and composes
  the resulting stopping-lattice isometry.  The paper's block equality is
  expressed by `TargetPrefixSegmentProductEq`: the segment lattice is the
  image of the expected orthogonal product under that same isometry.
  Injectivity of lattice transport then proves the formerly supplied
  `StopLatticeEq`.  Both target-prefix and unchanged-suffix constructors now
  build the dual endpoint certificate from this geometric equality, and
  `beli2019Lemma710General_of_targetPrefixSegmentProductEq` is the direct
  paper-facing conclusion.  All declarations are kernel checked without a
  new axiom.  The remaining Lemma 7.10 task is to derive the dual instance of
  this block equality from the original consecutive replacement equality;
  after that the corresponding Sections 7--9 law fields can be removed.
- M604: the dual-side replacement block is now connected to the M603
  stopping model by an explicit lattice-isometry diagram.  Lattice
  isometries can be multiplied orthogonally; dualizing a replacement
  isometry, identifying the dual product componentwise, and swapping its two
  factors gives `dualReplacementOrthogonalProduct`.  Consecutive segments
  carry concrete normalized-dual and reverse-dual vector formulas, including
  the prefix-to-reversed-suffix index identity.  At the unique dependent
  stopping node, `DualReplacementAtStop` stores the original replacement
  isometry, the three reverse-dual identifications, and their literal BONG
  vector commutativity.  Its recursive propagation constructs
  `TargetPrefixSegmentProductIsometryData`, hence the exact segment-product
  equality and the general conclusion of Lemma 7.10.  The new declarations
  pass the project axiom audit with only `propext`, `Classical.choice`, and
  `Quot.sound`.
- M605: the final vector commutativity in M604 is now derived from literal
  consecutive-block data.  A lattice isometry agreeing on the vectors of two
  BONGs automatically agrees on all their normalized reverse-dual vectors,
  and the segment reverse-dual isometry is proved to send every normalized
  vector to its prescribed target vector.  The theorem
  `factorVectors_of_consecutiveBONGs` splits the common finite index into the
  reversed right block and reversed left block, proves the corresponding
  value-unit identities, and verifies the factor-swapped product coordinate
  by coordinate.  Consequently
  `DualReplacementAtStop.ofConsecutiveBONGDiagram` needs only the original
  left/right block formulas and the two concrete reverse-dual block formulas;
  the whole-product commuting equation is no longer an input.  The remaining
  foundational obligation for a fully closed Lemma 7.10 is the arbitrary-rank
  realization currently exposed as `BONGReverseDualLaws`, corresponding to
  Beli 2003, Lemma 4.8.
- M606: integral duality is now proved to commute with an arbitrary finite
  orthogonal decomposition.  Reversing the component order and replacing
  every component lattice by its integral dual gives an exact decomposition
  of the global dual lattice, with explicit projection and inclusion
  formulas.  This removes the last ambient-lattice identification that had
  previously been hidden inside the reverse-dual interface.
- M607: Beli 2003, Lemma 4.8 is now derived from the explicit Section 4
  construction interfaces.  A good BONG is decomposed into the unary and
  improper modular binary components of Lemma 4.3(iii); each component is
  reverse-dualized, the components are reversed, and the resulting family is
  proved to be another maximal norm splitting.  Its scale and norm orders are
  the exact affine transforms `r_i^* = -r_i` and
  `u_i^* = u_i - 2r_i`.  Concatenation by Lemma 4.1 gives a good BONG of the
  integral dual lattice, while the two-level finite-index argument proves its
  global vectors are exactly the normalized dual vectors in reverse order.
  The resulting theorem `exists_reverseDual_of_beli` constructs
  `BONGReverseDualLaws` rather than assuming it.  Lemma 7.10's dual-product,
  factor-swap, and segment-isometry modules now depend directly on the two
  Section 4 construction interfaces and contain no independent
  `BONGReverseDualLaws` hypothesis.

- M608: the common geometric conclusion of Beli 2019, Lemmas 9.3 and 9.6 is
  now fully formalized.  An isometry between the two orthogonal complements
  is extended across equal-valued anisotropic head lines by the explicit
  formula
  `z ↦ (B(y,z)/Q(y))x + f(pr_{y⊥} z)`.  The inverse formula, preservation of
  the bilinear form, the image of the source head, and exact commutation with
  orthogonal projection are all proved.  An equal-rank integral
  representation of the projected lattices is automatically promoted to the
  required tail isometry.  `ofProjectedRepresentation` then constructs the
  ambient solved-head certificate, and Beli 2003, Lemma 2.2 yields the
  original lattice representation.  Thus the Section 9 induction step itself
  is no longer part of the trust boundary.
- M609: the final well-founded descent no longer ranges over an arbitrary
  code type with user-chosen counterexample and measure predicates.
  `Beli2019RepresentationProblem` packages the actual source and target
  quadratic lattices, their good BONGs, rank bound, ambient representation,
  and the four conditions of Theorem 2.1.  Its counterexample is
  definitionally failure of the concrete lattice representation, while its
  lexicographic measure is computed from the source rank and the literal
  source-minus-target volume order.  The root problem is constructed from the
  theorem arguments.  The Lemma 9.3 and 9.6 branches were initially reduced
  to literal `HeadReduction` certificates; `solvedHead_of_projected` reduces
  their geometric conclusion exactly to equal-valued norm-generating heads
  and the lower-rank projected representation.
- M610: Lemma 9.3's lower-rank problem is now concrete.  Equality of the two
  heads transports condition (i), the shifted prefix-factor identity and
  capped-defect inequalities transport condition (ii), the central trigger
  is lifted through the selected essential alpha equality, and diagonal
  common-head cancellation transports conditions (iii) and (iv).  These four
  pieces assemble into `representationConditions_tail`, and
  `lemma93HeadReduction` constructs the literal projected recursive problem.
- M611: the two directions of Lemma 2.11 used in Lemma 2.13 are proved from
  adjacent capped-defect bounds and the Key Lemma.  Consequently condition
  (ii) at two nonessential neighboring indices is automatic.  Together with
  the proved essential-index forcing at the central trigger, this removes
  both former local hypotheses `hnonessential` and `hcentralTrigger` from the
  public Lemma 9.3 reduction.
- M612: rank-index transport for bundled recursive problems is formalized by
  `representationConditions_castIndices` and `ofData_castIndices_eq`.
  `Lemma93Input` now records only the paper's ordinary-branch arithmetic:
  common positive rank, equal first values, the second-order comparison, and
  selected `A=A*` equalities at essential endpoints.  Its `headReduction`
  theorem constructs the rank drop for an arbitrary bundled problem.  The
  old `ordinaryHead` predicate and proof-producing `lemma93` field have been
  deleted from `Beli2019FinalStepData`; the Section 9 classifier must instead
  return this inspectable input.
- M613: Section 8 has started at the local residue-field layer.  Lemma 8.1 is
  formalized in both forms, with its square-class equivalence derived from
  strict defect growth.  Lemma 8.2(i)--(iii) is then derived from Hilbert
  multiplicativity, the `2e` defect bound, and Lemma 8.1.  The genuinely
  local Hensel and Hilbert-pairing choices are exposed as the field-level
  interfaces `DyadicResidueDefectProductLaws` and
  `DyadicHilbertDefectChoiceLaws`, rather than being hidden in a Section 8 or
  theorem-level package.
- M614: Lemma 8.4 is fully formalized from adjacent-order monotonicity,
  half-gap bounds, and Corollary 2.3.  For Lemma 8.5, the sets `A`, `B`, and
  `C` are literal predicates on finite indices.  The proof extracts an actual
  alpha candidate attaining the finite minimum, proves the endpoint-equality
  consequences in both orientations, and carries out the paper's extremal
  construction using the least left-boundary or greatest right-boundary
  index.  The resulting theorem `beli2019Lemma85` has no new Section 8 law or
  theorem-level interface: every witness and equality is constructed from the
  existing good-BONG alpha arithmetic.
- M615: Lemma 8.6(i)--(iii) is fully formalized.  For a prescribed orthogonal
  basis, literal prefix products and adjacent parameters reduce part (i) to
  the existing binary admissibility and good-realization criteria.  Part (ii)
  proves lower bounds for every left, right, and half-gap alpha candidate and
  then takes the finite minimum.  Under property A, the extremal index
  `j ∈ C` supplied by Lemma 8.5 has source adjacent defect strictly below
  both neighboring comparison-prefix defects.  Exact defect domination and
  the prefix-product square identity therefore identify its target adjacent
  defect, providing the reverse candidate bound and all equalities in part
  (iii).  No Lemma 8.6-specific law or theorem-level interface is introduced.
- M616: Remark 8.7 is formalized uniformly for every three-entry window with
  equal outer orders, including the terminal window.  Its package records the
  order congruences modulo two, both endpoint and alpha identities, the
  equivalence of the two half-gap equalities, the `alpha`-sum bound and its
  equality criterion, and both capped and raw adjacent-defect bounds.  The
  proof uses Lemma 6.6, Corollary 2.3, and the general capped-defect estimates;
  no new local-law interface is required.
- M617: Lemma 8.8(i) now has an exact dependent statement, including all
  rank-two, rank-three, and rank-four qualifications in exceptions (a)--(c),
  and its necessity direction is complete.  Exception (a) is excluded by the
  realized valuation-unit defect.  Exception (b) is excluded by the binary
  representation and the boundary Hilbert obstruction.  For exception (c),
  classification condition (iv) embeds the transformed binary prefix in the
  original ternary prefix; adjoining the determinant line and applying the
  paper-independent codimension-one cancellation theorem transfers
  anisotropy.  Lemma 8.1(ii) then gives strict product-defect growth, while
  Remark 8.7 forces the opposite Hilbert value.  The sufficiency direction,
  including the induction and its Lemma 8.3 quaternary step, remains next.
- M618: the lattice-theoretic part of Lemma 8.3 and the binary branch of
  Lemma 8.8's sufficiency proof are now kernel checked.  Alpha candidates are
  defined directly for an ambient orthogonal basis and proved invariant under
  good-BONG realization.  In rank four, alternating orders force all three
  alpha values from the first one and make classification condition (iv)
  vacuous; Lemma 8.6 therefore constructs the candidate lattice, Beli's four
  classification conditions identify it with the source, and the resulting
  BONG is transported back to the original lattice.  The analogous rank-two
  construction is proved and then lifted to arbitrary rank by replacing the
  first good binary segment via Beli (2003), Lemma 4.9.  The only new inputs
  are field-level ambient-basis certificates for the binary norm equation and
  the quaternary Hasse-scaling argument; neither interface assumes a target
  lattice or the desired good BONG.
- M619: the recursive tail-splicing geometry in Lemma 8.8 is formalized.  A
  first-value transform of the projected tail is prepended to the unchanged
  head, with exact formulas for the first two values and the new first
  adjacent product.  When the tail alpha is strictly below the old adjacent
  defect, exact quadratic-defect domination identifies the new adjacent
  defect with that tail alpha.  The paper's global-alpha equality then proves
  that the modified BONG has its first alpha already realized by its first
  binary segment, so the verified binary replacement theorem applies.
- M620: Lemma 8.2's Hilbert-symbol choices are strengthened to the exact
  valuation-unit representatives required by Lemma 8.8.  A nonzero-defect
  square class has even valuation, so division by a uniformizer square
  normalizes it to valuation zero while preserving both quadratic defect and
  every fixed Hilbert pairing.  Applying this normalization to Lemma 8.2(ii)
  and (iii) supplies unit-valued choices without extending the field-level
  trust boundary.
- M621: the strict binary-prefix branch of Lemma 8.8 is complete.  The new
  field-level `DyadicUnitDefectSpectrumLaws` states only the interior
  unit-defect spectrum (nonnegative odd integral depths below `2e`).  Lemma
  2.7(iv) and Corollary 2.8 prove that a first alpha strictly below its
  half-gap lies in that spectrum.  The binary alpha formula then gives a
  strict defect-sum bound; the unit-valued Lemma 8.2 choices produce the
  required Hilbert-positive multiplier, and the verified binary segment
  replacement lifts it to arbitrary rank.
- M622: the direct nonexceptional half-gap binary branch is complete as
  well.  Rational and extended-natural defect-sum boundary tests are proved
  equivalent in the directions required by Lemma 8.2.  If the raw first
  adjacent defect differs from the complementary value, cancellation in
  `ℚ ∪ {∞}` shows that the Hilbert-choice sum is not `2e`; negation of
  exception (a) supplies the unit representative and the same binary segment
  replacement finishes the branch.

- M623: the first-index induction formula in Lemma 8.8 is now kernel checked.
  The suffix segment in Corollary 2.5(ii) is identified, by scalar agreement,
  with the projected tail, giving exactly
  `alpha_1(M) = min (alpha_1([a_1,a_2]), R_2-R_1+alpha_1(M*))`.  Both
  numerical alternatives are proved: if the first adjacent defect is at most
  the tail alpha, the original binary branch applies directly; in the
  strict-tail case the tail transformation is spliced under the unchanged
  head, exact defect domination returns the result to the strict binary
  theorem, and the two successive transformations are composed into a
  transform of the original good BONG.

- M624: the critical residue-two half-gap identities are complete.  Failure
  of exception (b) identifies both the second alpha and the projected-tail
  alpha with the complementary defect.  A successful tail transform raises
  the first adjacent defect by Lemma 8.1(ii), returning to the direct binary
  branch.  Exception (b) for an exceptional tail is proved to propagate to
  exception (c) for the original ternary prefix.
- M625: the final quaternary branch is complete.  The first four entries are
  localized as a good segment; the two alternating order equalities identify
  its first alpha with the global alpha.  Lemma 8.3 changes its first value,
  and Beli (2003), Lemma 4.9 replaces that segment in the ambient BONG.
- M626: the projected-tail exception-(a) branch and the rank-two endpoint
  are complete.  The parity and interior unit-defect spectrum force the
  realized global defect to be `2e`; the discriminant unit then supplies the
  required multiplier, and the unramified norm criterion proves its Hilbert
  symbol is one.  The unordered endpoint pair `{0,2e}` is excluded directly.
- M627: the full rank induction and exact Lemma 8.8(i) equivalence are kernel
  checked.  `beli2019Lemma88_sufficiency` assembles the strict, recursive,
  exception-(a), exception-(b), and exception-(c) branches, while
  `beli2019Lemma88_i` combines it with the previously proved necessity
  direction.  No Lemma 8.8-specific theorem-level interface remains.
- M628: Corollary 8.10 is kernel checked.  If the original first binary
  segment does not already realize the global first alpha, the exact
  two-term recursion forces a strict projected-tail branch.  The completed
  Lemma 8.8 is applied to that tail, its replacement is spliced below the
  unchanged head, and defect domination proves that the new literal first
  binary segment realizes the invariant global alpha.
- M629: Corollary 8.11 is kernel checked.  Reverse duality and integral
  biduality first give the right-endpoint counterpart of Corollary 8.10.
  The global candidate minimum is then proved to equal the minimum of the
  alpha at the end of the full left prefix and the alpha at the beginning of
  the full right suffix.  Whichever endpoint realizes that minimum is put in
  normal form and replaced inside the ambient BONG by Lemma 4.9.  Thus every
  literal adjacent pair can be made to realize the invariant global alpha,
  without a Corollary 8.11-specific law.
- M630: Lemma 8.12 is kernel checked in all three rank regimes.  The named
  lattice invariant `alphaPrime` realizes the paper's `alpha'_i`; equality of
  the first orders gives `A_1 = alpha_1` and `A'_1 = alpha'_1`.  At the second
  boundary, Lemma 2.7(i), the antitonicity of `-R_(i+1) + alpha_i`, and the
  capped adjacent-defect inequality prove that the primary term dominates
  the optional secondary term.  This yields the explicit formulas for
  `A_2` and `A'_2` when the source rank is at least two, and the terminal
  `S_2 + A_2` formula when the source rank is one.  No Lemma 8.12-specific
  law or additional trust boundary is introduced.
- M631: Lemma 8.13 is kernel checked without circular use of Theorem 2.1.
  For a unary source with equal first order, condition (i) is automatic and
  condition (ii) is equivalent to `d[a_1 b_1] = alpha_1`; the latter is also
  proved equivalent to the uncapped inequality `d(a_1 b_1) >= alpha_1`.
  The unique condition-(iii) and condition-(iv) indices reduce to the exact
  binary and ternary triggers displayed in the paper.  Target ranks two and
  three are discharged by converting the ambient quadratic-space embedding
  into a representation of the complete diagonal BONG presentations.  The
  main result is first stated as the noncircular equivalence
  `RepresentationConditions <-> Lemma813Conditions`; the literal lattice
  representation iff is then a wrapper parameterized by the already-proved
  main-theorem equivalence.  No Lemma 8.13-specific law is introduced.
- M632: the exact statement and proof boundary of Lemma 8.14 are kernel
  checked.  Its target has rank at least three, all clauses of exceptions
  (a)--(c) are represented literally, and the qualifications at ranks four
  and five are dependent hypotheses rather than invented values at absent
  indices.  The ternary isotropy predicate is expressed by its diagonal
  quadratic form.  In the paper's notation `V \top W` denotes a complement
  `U` satisfying `V ≅ W ⊥ U`; accordingly
  `[a_1,a_2,a_3,a_4] \top [b_1]` is encoded by an anisotropic ternary
  diagonal complement whose extension by `[b_1]` represents the quaternary
  prefix.  The conclusion is a good BONG of the same target lattice
  with first value exactly `b_1`.  The paper-facing statement assumes the
  literal lattice representation, while the Section 8 proof target assumes
  `Lemma813Conditions`; a checked bridge exposes the eventual Theorem 2.1
  dependency as an explicit argument.  Rank-three exception (c), the
  rank-three tail of (b), and the rank-four tail of (c) have their intended
  boundary behavior.  This milestone fixes the statement; milestones
  M633--M640 subsequently discharge its geometric invariance, necessity, and
  rank-stratified sufficiency without a Lemma 8.14-specific law.
- M633: the numerical and low-rank change-of-good-BONG invariance used at the
  start of Lemma 8.14 is kernel checked.  Order and alpha invariance together
  with Beli (2006), Lemma 4.2 transport both capped defects and the third-gap
  complementary quantity.  Consequently each exceptional structure
  transports once its geometric isotropy predicate is transported.  A
  general checked theorem isolates exactly those two geometric obligations.
  In target rank three, ternary isotropy is invariant by a full BONG
  coordinate change and exception (c) is impossible, giving invariance of
  the complete exceptional disjunction.  In target rank four, composing a
  complement presentation with the full four-dimensional coordinate change
  proves invariance of exception (c).  The higher-rank ternary comparison is
  discharged in M634 and the complement-space Hasse-symbol comparison in
  M635; no Lemma 8.14-specific law is added.
- M634: the high-rank ternary-prefix part of the geometric invariance proof
  is kernel checked.  Under `R_1 = R_3` and
  `alpha_2 + alpha_3 > 2e`, classification condition (iv) embeds the first
  binary prefix of a second good BONG into the original ternary prefix.
  Determinant completion produces the comparison ternary form.  Remark 8.7
  bounds the first adjacent defect by `alpha_2`, the general prefix-change
  theorem bounds the comparison-product defect by `alpha_3`, and the dyadic
  defect criterion makes the residual Hilbert symbol trivial.  Hence the two
  ternary prefixes are isotropic simultaneously.  Exception (a)'s displayed
  defect bound is proved to imply the required alpha sum, while exception
  (b) supplies it directly; as a result, the disjunction of exceptions (a)
  and (b) is fully invariant in every target rank at least four.
- M635: exception (c)'s remaining complement-space comparison is kernel
  checked.  The numerical hypotheses force the residual Hilbert symbol to be
  one, and a quaternary complement presentation transports anisotropy across
  a change of good BONG.  Together with M633--M634 this proves invariance of
  the complete exceptional disjunction in every relevant rank.  The public
  API is in `Beli2019Lemma814ComplementInvariants.lean`.
- M636: the necessity direction of Lemma 8.14 is kernel checked.  After the
  first binary segment is normalized by Corollary 8.10, each of exceptions
  (a), (b), and (c) contradicts the existence of a good BONG whose first
  value is the prescribed unary value.  The public theorem is
  `beli2019Lemma814_necessity`.
- M637: the complete ternary sufficiency argument and its ambient lifting are
  kernel checked.  The equal- and unequal-outer ternary cases follow the
  paper's defect/Hilbert-symbol split; Beli (2003), Lemma 4.9(ii), inserts a
  safe transformed ternary prefix into any longer BONG.
- M638: rank-four sufficiency is kernel checked in all three alpha-sum
  regimes.  Corollary 8.11 localizes the endpoint alphas; the strict-below and
  equality-boundary branches perform the final-binary normalization and
  eliminate the induced exceptions.  The doubly alternating endpoint is a
  direct application of Lemma 8.3.
- M639: the higher-rank equal-outer branch is kernel checked.  Its strict and
  equal second/fourth order subbranches normalize the initial quaternary
  segment, eliminate exception (c), apply the rank-four result, and splice
  the transformed segment back into the original lattice.
- M640: the higher-rank unequal-outer branch and the final assembly are
  kernel checked.  The strict third-alpha branch is reduced by a suffix
  scaling.  At the half-gap boundary, the right endpoint plateau and unit
  defects reduce the binary exception to case (b); reduction (II), Corollary
  8.9, and Lemma 8.1(ii) then force a strict adjacent-defect rise and remove
  that last exception.  `beli2019Lemma814Explicit` combines ranks three,
  four, and at least five and proves the noncircular explicit statement of
  Lemma 8.14 for every target rank at least three.  Its axiom audit reports
  only `propext`, `Classical.choice`, and `Quot.sound`.
- M641: four direct branches of Lemma 9.1 are kernel checked.  If
  `R_1 < R_3`, all three Lemma 8.14 exceptions contradict their common
  equality `R_1 = R_3`.  If `R_2 = R_4`, Remark 8.7 gives
  `alpha_2 + alpha_3 <= 2e`, excluding exceptions (a)--(c).  Finally,
  `R_2 - R_1 = 2e` gives `alpha_1 = 2e` and the first-binary half-gap normal
  form.  The prescribed multiplier has defect at least `2e`; the first
  adjacent product has even order and therefore positive defect, so the
  defect-sum criterion makes the required Hilbert symbol one and the binary
  scaling branch of Lemma 8.14 constructs the new first value.  For
  `d[-a_1,3b_1] = alpha_1 < beta_1`, the strict inequality removes the
  full-source alpha cap, the canonical unary first segment preserves the
  first prefix product, and the resulting equality excludes all three
  Lemma 8.14 exceptions.  No Lemma 9.1-specific law is introduced.  The
  remaining `R_2 = S_2` branch and the wrapper deriving the unary Lemma 8.13
  hypotheses from the full representation assumptions remain in the
  Section 9 worklist.
- M642: the shared rigidity calculation for Lemma 9.1's remaining
  `R_2 = S_2` branch is kernel checked.  At the first boundary,
  condition 2.1(ii), Lemma 8.12(i), and the source alpha cap prove
  `alpha_1 <= beta_1`.  Under `R_1 = R_3`, if the full first-three defect is
  `beta_1`, Lemma 8.12(ii) identifies `A_2` with its primary candidate,
  condition 2.1(ii) caps it by `alpha_2`, and Remark 8.7 supplies the reverse
  comparison.  Hence `A_2 = alpha_2` and `beta_1 = alpha_1`.  This is proved
  in `Bong.Bong.Beli2019Lemma91SecondOrder` without a Section 9-specific
  law.  Exceptions (b) and (c) are additionally proved to force the source
  cap: choosing the unary defect makes both Lemma 8.12(ii) candidates
  strictly larger than `alpha_2`, contradicting condition 2.1(ii).  Hence
  both automatically satisfy the displayed rigidity equalities.  The final
  binary/ternary geometric contradictions to Lemma 8.14(a)--(c) are still
  open.
- M643: the local geometric contradiction to Lemma 8.14(a) in the
  `R_2 = S_2` branch is kernel checked, conditional only on the literal
  lower-rank binary-prefix representation used by the paper.  The first
  source adjacent defect is at least `alpha_2`, the other defect dominates
  `d[-a_1,3b_1]`, and exception (a) makes their sum exceed `2e`; hence the
  relevant Hilbert symbol is one.  Determinant completion transfers this to
  isotropy of `[a_1,a_2,a_3]`, contradicting exception (a).
- M644: the binary-prefix representation is extracted directly from the
  revised-v2 condition (iii') at `i = 3`.  Lemma 2.16 converts the stored
  condition (iii) to (iii'), so no recursive invocation of Theorem 2.1 is
  used.  The normalized trigger is `R_4 > S_2` together with the paper's
  strict sum of the two capped defects.
- M645: exception (a) is completely excluded in the `R_2 = S_2` branch.
  The strict condition-(iii') inequality is proved separately when the
  first defect selects its unary term and when it selects the source alpha
  cap; condition (ii), P1, Remark 8.7, and domination then provide the
  binary-prefix representation.  Target rank three is handled directly by
  restricting the ambient representation to the first binary source
  segment.  The combined theorem is
  `not_lemma814ExceptionA_of_equalSecondOrder_allRanks`.
- M646: exception (b) is completely excluded in the `R_2 = S_2` branch.
  The displayed lower bound for `A_3` is proved by checking its half-gap,
  primary, and Lemma 2.7 previous-defect candidates.  Condition (ii) bounds
  both the raw equal-prefix determinant defect and the source third-alpha
  cap.  Multiplying this raw defect by the uncapped first-three defect leaves
  the second source adjacent product up to a square; P1 then excludes every
  later right-defect candidate for the first source alpha.  The resulting
  exact first adjacent defect and determinant completion contradict the
  residue-two Hilbert-symbol boundary in exception (b).  The ternary target/
  ternary source endpoint uses the standard equal-rank determinant-square
  invariant in place of the nonexistent `A_3`.  The combined theorem is
  `not_lemma814ExceptionB_of_equalSecondOrder`.
- M647: exception (c) and the complete Lemma 9.1 are kernel checked.  The
  source-rank-two, source-rank-three, and higher-rank branches derive the
  binary, ternary, or quaternary prefix representations required by condition
  (iii), then contradict the Hilbert-symbol obstruction in exception (c).
  The canonical unary source is now an actual prefix witness whose lattice
  embeds into the full source lattice.  Composing this inclusion with
  `N ≤ M` and applying the independently proved necessity direction yields
  the unary Lemma 8.13 conditions without using sufficiency.  The theorem
  `beli2019Lemma91` combines this bridge, all five displayed alternatives,
  and all three exception exclusions.  Its trust audit reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- M648: Lemma 9.2 is complete for every rank at least four.  The rank-four
  strict branch extracts the lost first left-defect candidate and derives
  the two quaternary numerical certificates.  In rank five, Corollary 8.10
  normalizes the first binary alpha; the same endpoint argument proves the
  three alpha recursions, the strict last-adjacent bound, oddness, and
  `alpha_3 + alpha_4 < 2e`.  The explicit unit scalings are realized as good
  BONGs, inserted into arbitrary-rank initial segments, and the resulting
  base equality is propagated to every later index.  The public theorem is
  `BONG.GoodBONG.beli2019Lemma92`; its focused audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- M649: the Case 1 normalization and its large-defect subcase in Lemma 9.3 are
  kernel checked.  Corollary 8.11 is applied to the source before Lemmas 9.1
  and 9.2 select the target, so the selected source retains alpha/tail-alpha
  equality at every shifted boundary.  Mixed primary, secondary, and
  Lemma 2.7(ii) current-candidate transport reduces the reverse inequality to
  the paper's `A_2` and `A_3` calculations.  Under
  `d[-a_(1,3)b_1] >= (S_2-R_3)/2 + e`, both are proved, combined into
  `lowReverse_of_largeDefect`, and assembled into the concrete
  `toLemma93Input_of_largeDefect`.  The terminal, current-essential, and
  next-essential `A_3` cases are all explicit.  The remaining two Case 1
  subcases and Case 2 are not yet discharged.

## Historical status through M649 (superseded)

This section records the state at M649 and is retained as development
history. Its references to unfinished Lemmas 9.3, 9.6, 9.12 and to
`Beli2019FinalStepLaws` are superseded by the completion update below.

Theorem 2.1's logical assembly is kernel checked in both its original and
revised-v2 forms, `beli2019Theorem21` and `beli2019Theorem21_prime`, but the
current sufficiency theorem is still parameterized by the explicit
`Beli2019FinalStepLaws` package for the unresolved arithmetic and lattice
constructions in Sections 7 and 9.  Consequently this is not yet a complete formalization of the
2019 v2 paper.  Neither formulation assumes `GoodBONGRepresentationLaws`;
that legacy theorem-level interface is derived from the parameterized
assembly rather than used circularly.

As elsewhere in this project, deep local arithmetic is represented by
non-default, proof-producing interfaces rather than by hidden axioms.  The
remaining trust boundary is explicit:

- `Beli2006AlphaLaws` supplies the previously isolated local alpha formulas;
- `Beli2019SectionFiveOrderData` contains a pointwise certificate for
  condition 2.1(i); its constructors expose the direct and common-Jordan
  arithmetic used in Section 5.4.  `Beli2019OrderNecessityLaws` remains only
  in auxiliary prefix-construction APIs and is not an assumption of Theorem
  2.1;
- `Lattice.indexPChain_of_le` now proves, without a paper-specific
  interface, that every literal lattice inclusion admits a finite
  index-`\mathfrak p` chain.  Its zero-length endpoint is the concrete theorem
  `BONG.GoodBONG.representationConditions_self`.  Conditions (i) and (ii) are
  transported by proved theorems; all numerical triggers in (iii) and (iv)
  are invariant as well.  The canonical-prefix case of Lemma 3.8 is a proved
  theorem derived from `GoodBONGClassificationLaws` and concrete endpoint
  maps.  Lemma 3.10(iii)'s target/source replacements are proved from the
  generic `HilbertSymbolLaws`, `DiagonalRepresentationParityLaws`, the local
  alpha formula derived from `Beli2006AlphaLaws`, and the proved scalar
  alternatives of Lemma 2.18.
  Lemma 3.10(iv)'s target/source replacements are proved from
  `DiagonalCodimensionOneCancellationLaws`, the paper-independent Witt
  cancellation statement for a one-dimensional extension.
  `Beli2019Lemma310PrefixLaws`, the packaged Lemma 3.10 law, and Corollary
  3.11 are derived from these inputs together with
  `GoodBONGClassificationLaws`.  The other decorations are
  `Beli2019SectionFiveLaws` for one prime step and
  `Beli2019SectionFourLaws` for each transitivity junction;
- the equal-rank part of Lemma 2.21 is now proved directly: an integral
  representation between spaces with equally long BONG bases is promoted to
  an ambient isometry, its image is a literal sublattice, and the transported
  good BONG has the same scalar sequence.  For strict rank inequality,
  `GoodBONGDeepIntegralExtensionLaws` supplies only Lemma 2.20's geometric
  deep-complement construction (prefix, boundary order, and boundary alpha).
  The descent of all four conditions, including the exceptional terminal
  cases of `(iii')` and `(iv)`, is proved in
  `Beli2019RankCompletion.lean`;
- `DyadicResidueDefectProductLaws` supplies the leading-residue calculation
  in Lemma 8.1, while `DyadicHilbertDefectChoiceLaws` supplies the local
  nondegenerate Hilbert partners used in Lemma 8.2.  All residue-cardinality
  case analysis and the three conclusions of Lemma 8.2 are proved from these
  field-level inputs.  Lemmas 8.4 and 8.5 are then concrete consequences of
  the already formalized alpha minimum formula and adjacent-order arithmetic.
  Lemma 8.6 is concrete as well: its prescribed-basis realization uses the
  general binary construction laws already isolated for Beli (2006), while
  its alpha inequalities and property-A equality case follow from finite
  candidates, Lemma 8.5, and exact quadratic-defect domination.  These lemmas
  introduce no additional Section 8 trust boundary.  Remark 8.7 is likewise
  a proved package of the three-entry consequences needed by Lemma 8.8.  The
  exact Lemma 8.8 exceptional predicate and both directions of its final
  equivalence are now proved as well, using only the existing field-level
  defect interfaces, good-BONG classification, and codimension-one
  cancellation.  The binary realization and arbitrary-rank first-segment
  lift are proved.  Lemma 8.3 is reduced to the field-level
  `DyadicQuaternaryFirstScalingLaws`, whose output is only a checkable
  orthogonal-basis certificate; all subsequent lattice construction and
  classification are proved.  `DyadicBinaryFirstScalingLaws` similarly
  isolates the binary norm-equation basis construction.  The recursive
  projected-tail replacement, the exact two-term alpha recursion, both
  numerical branches, the strict-defect return to the binary branch, all
  three exceptional-tail alternatives, the discriminant endpoint, and the
  final quaternary replacement are concrete.  Section 8 introduces no
  remaining Lemma 8.8 theorem-level obligation.  Corollaries 8.10--8.11 and
  Lemmas 8.12--8.14 are also kernel checked; in particular,
  `beli2019Lemma814Explicit` contains the full rank-stratified, noncircular
  proof of Lemma 8.14 and introduces no theorem-level interface;
- the nested induction of Sections 7--9 now uses concrete bundled
  representation problems and the lexicographic pair `(rank, volume gap)`;
  its counterexample predicate, root, measure, and well-foundedness are fixed
  rather than stored in `Beli2019FinalStepLaws`.  Section 9 is split into an
  exhaustive case classifier and remaining proof-producing fields for the
  unfinished Lemma 9.3 cases and for Lemmas 9.6 and 9.12.  The ordinary
  Lemma 9.3 branch now returns only
  `Lemma93Input`, from which the complete projected `HeadReduction` is proved;
  it is no longer a proof-producing field of `Beli2019FinalStepData`.
  Lemma 9.1 is complete (M641--M647), including construction of the unary
  Lemma 8.13 input and exclusion of exceptions (a)--(c) in the
  equal-second-order branch.  Lemma 9.2 is complete (M648).  The exceptional
  remaining Lemma 9.3 cases, the exceptional Lemma 9.6 head, Section 7's
  global volume reduction, and Lemma 9.12's residual prime-index descent
  remain.  Lemma 7.1's first reduction is
  now concrete: non-norm generators form a full lattice and its inclusion has
  index `p`.  This uses only the foundational residue-field perfection law and
  the existing BONG scale formula, not a Lemma 7.1-specific interface.  Lemma
  7.3 is also concrete: its left plateau is proved by adjacent alpha arithmetic
  and its right plateau is the verified reverse-dual image of the left one.
  Lemma 6.6 is also concrete: both its same-parity rigidity and
  opposite-parity sum statement are derived from good-BONG two-step
  monotonicity and the proved parity law for nonpositive adjacent gaps.
  Lemma 6.5 is concrete as well: condition 2.1(ii), odd prefix valuation, and
  the three explicit representation-alpha candidates yield its cross-order
  dichotomy.  Lemma 6.7 is now concrete through its complete type-I/type-II/
  type-III classification: fixed-gap bounds, extremal indices, outer profiles,
  the central type-II plateau, both parity exclusions, and `S-R=2` are all
  kernel-checked finite-order arguments.  Lemmas 6.11(i)--(ii) and
  7.2(i)--(ii) are now derived from this classification and Lemma 6.6 without
  a new local-law interface.  Their nonoverlapping type-III counterparts now
  derive the required `alpha <= 1` conclusion directly from condition 2.1(ii)
  through the type-III case of Lemma 6.9(i), capped-defect propagation, and
  defect domination.  Lemma 7.8 is now concrete as well: both self-prefix
  defect formulas, both central alpha equalities, and the sharp central-gap
  bound are obtained from the explicit alpha candidates, capped-defect
  multiplication, Remark 6.16, and proved reverse-dual transport.  The final
  case-8 comparison in Lemma 7.9(ii) is also concrete for all three profile
  types, with the type-III overlap split and full-rank odd endpoint discharged
  without an additional paper-specific law;
- `BONG.GoodBONG.beli2019Lemma216` proves the pointwise trigger equivalence
  used by the revised `(iii')` formulation.  Milestones M186--M196 establish
  its ordinary-index and exceptional terminal-index cases from Definitions
  4--5, Remark 1.1, Lemma 1.4(c), Lemma 2.7, and Lemma 2.14.

Thus the theorem-level logical assembly, all reductions, and the absence of
circular use of the desired equivalence are checked by Lean.  Expanding the
listed interfaces down to raw DVR/Jordan arithmetic remains a separate
foundational refinement, not an unreported dependency of Theorem 2.1.

## M650--M660 completion update

- M650 completes every remaining Case 1 and Case 2 branch of Lemma 9.3,
  including the literal rank-three and rank-four endpoints. The public
  outputs are concrete head-reduction inputs, not proofs stored in a final
  theorem interface.
- M651 completes Lemmas 9.4--9.6. The exceptional bad-BONG head is realized
  geometrically in ranks three and four and uniformly in higher rank.
- M652 completes Lemmas 9.7--9.12, including the low-rank scalar
  realizations, the type-I and type-III residual branches, and the literal
  index-`\mathfrak p` counterexample descent.
- M653 assembles `Beli2019SectionNineComplete` for rank three, rank four,
  and every rank at least five.
- M654 assembles `Beli2019SectionSevenReduction`: an equal-rank
  counterexample of rank at least three either has equal norm ideal or
  descends to a strictly smaller counterexample.
- M655 proves the unary and binary base cases, including
  `Beli2019RankTwoComplete`.
- M656 substitutes the concrete Sections 7 and 9 results into the
  well-founded lexicographic rank-volume induction. The public endpoint is
  `Beli2019RepresentationProblem.not_counterexample_of_equalRank_complete`.
- M657 proves the numerical and terminal-index content of Lemmas 2.20--2.21
  for strict rank: all four conditions lift to a sufficiently deep
  equal-rank completion.
- M658 constructs the ambient envelope, applies the explicit deep-complement
  interface, and transports the equal-rank representation back to the
  original source. The result is `beli2019_sufficiency_complete`.
- M659 combines complete sufficiency with `beli2019_necessity` and Lemma
  2.16. The public theorems are `beli2019Theorem21` and
  `beli2019Theorem21_prime`.
- M660 removes the theorem-level `Beli2019FinalStepLaws` class and the old
  sufficiency placeholder, updates the focused audits, and records a full
  paper/formalization fidelity audit under `docs/audit/Beli2019V2`.
- M661 proves the dyadic local square theorem by Hensel lifting over the
  normalized valuation ring and installs the resulting
  `QuadraticDefectLaws` instance. The Beli 2019 main theorem consequently has
  48 rather than 49 project-specific law/data-instance slots.

## Current status and trust boundary

The original and revised-v2 logical assemblies are kernel checked.
`beli2019Theorem21` and `beli2019Theorem21_prime` do not assume
`GoodBONGRepresentationLaws`, `Beli2019FinalStepLaws`, or an arbitrary
problem/measure/final-representation oracle. Sections 7--9, both low-rank
base cases, strict-rank completion, necessity, and Lemma 2.16 are connected
by concrete Lean theorems.

This is a complete formalization at the project's explicit modular
local-law boundary, but it is not yet an unconditional proof over every
dyadic local field. The public theorem still has non-default proof-producing
parameters. The highest-impact remaining ones are:

- `Beli2019SectionFiveLaws` for the complete one-prime-step Section 5 data;
- the lower-level `BeliSectionFourLaws`, `BeliCorollary44Laws`, and related
  construction interfaces from Beli 2003 that feed the now-derived
  `Beli2019SectionFourLaws` package;
- `Beli2019UnaryBinaryJordanLaws` for the local Lemma 9.5 Jordan/weight
  computations;
- `DyadicBinaryFirstScalingLaws` and
  `DyadicQuaternaryFirstScalingLaws` for the Section 8 ambient basis changes;
- the remaining refined defect, Hilbert-symbol, diagonal-classification,
  BONG, Jordan, and earlier-Beli law classes listed in the main theorem
  signature. The basic `QuadraticDefectLaws` package itself was discharged in
  M661.

The exact statement-strength verdict is `FORMALIZATION_WEAKER`, project
grade C. This wording distinguishes a kernel-checked conditional theorem
from an unconditional formal proof of the paper. See
`docs/audit/Beli2019V2/12_executive_summary.md`.

## M662--M663 closure update

M662 derives the refined unit-defect parity and spectrum packages from the
normalized dyadic local-field context.  M663 derives the generic
codimension-one diagonal cancellation package from nondegenerate
finite-dimensional linear algebra and determinant square classes.  The main
theorem also constructs its two Lemma 3.10 representation packages from the
already present approximation, classification, Hilbert, alpha, and
cancellation inputs instead of accepting them as separate parameters.

The `beli2019Theorem21_prime` signature therefore has 43 project-specific
law/data slots.  These closures do not yet change the semantic verdict: the
remaining Hilbert, local diagonal classification, Beli 2003/2009 Jordan,
Section 4/5, scaling, and deep local-lattice interfaces must still be proved.

## Final unconditional completion update

The preceding 43-slot statement is historical.  The remaining local-field,
Hilbert, diagonal, Jordan, Section 4/5, scaling, and deep-lattice interfaces
have now been discharged by concrete proof modules.  Both public endpoints

- `Bong.beli2019Theorem21`, and
- `Bong.beli2019Theorem21_prime`

now quantify only over the ambient field/topology/valuation structures,
`DyadicContext`, the two modules and quadratic spaces, the two lattices, the
rank inequality, the ambient-space representation, and the chosen good
BONGs.  Their elaborated signatures contain zero project-specific law/data
slots.

The v2 statement was rechecked directly against source lines 791--827.  The
formal definitions preserve the direct-or-pair disjunction in condition (i),
the truncated-defect bound in condition (ii), the strict inequalities and
prefix ranks in conditions (iii) and (iii'), and the terminal `i = n + 1`
convention in condition (iv).  `BONG.GoodBONG.beli2019Lemma216` proves that
only the central trigger changes between the original and v2 packages.

The concrete proof path is noncircular: Beli 2019 imports the proved Beli
2009 classification theorem, but not either 2006 public wrapper; the 2006
announcement wrappers are downstream corollaries of the later complete
proofs.  The Beli 2009 final binary-connectivity result may use the completed
2019 representation theorem without feeding back into that theorem's import
graph.

Current semantic status: `PROVISIONAL_MATCH`, project grade B.  This replaces
the historical `FORMALIZATION_WEAKER`, grade-C verdict.  Independent author
or expert confirmation is still required before assigning
`VERIFIED_MATCH`/grade A.  See
`docs/audit/Beli2019V2/15_unconditional_completion_audit.md` for the current
trust, coverage, and reproducibility audit.
