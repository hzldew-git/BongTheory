# Paper Theorem Inventory

## Counting convention

The paper declares `theorem`, `lemma`, `proposition`, `corollary`, and the
unnamed `bof` environment on one section-indexed counter. The `bof` entries
are called “Note” below. Definitions use a separate global counter.
Accounting for `bof` is essential: omitting it shifts such references as
Lemma 2.16 and Lemma 8.14.

Counts:

| Kind | Count |
|---|---:|
| Definitions | 11 |
| Theorems | 1 |
| Lemmas | 81 |
| Propositions | 2 |
| Corollaries | 12 |
| Numbered notes | 31 |
| Total | 138 |

Source lines refer to the audited v2 TeX file.

## Definitions

| ID | Line | Paper content |
|---|---:|---|
| Definition 1 | 420 | Truncated mixed-prefix defect \(d[\varepsilon a_{1,i}b_{1,j}]\). |
| Definition 2 | 605 | The ordered set \(\mathcal B\) of two-step-monotone order sequences. |
| Definition 3 | 657 | The bounded-gap subposets \(\mathcal B_n(\kappa)\) and \(\mathcal B(\kappa)\). |
| Definition 4 | 766 | The invariant \(A_i\), including the terminal convention. |
| Definition 5 | 905 | The auxiliary invariants \(\alpha'_i\) and \(A'_i\). |
| Definition 6 | 983 | Alternate invariants \(\underline A_i\) and \(\underline A'_i\). |
| Definition 7 | 1114 | Essential indices. |
| Definition 8 | 1376 | The relation \(N\leq M\): ambient representation plus conditions (i)--(iv). |
| Definition 9 | 1481 | Scalar approximations to prefix products. |
| Definition 10 | 1488 | Left, right, and two-sided quadratic-space approximations. |
| Definition 11 | 4248 | Types I, II, and III for an index-\(\mathfrak p\) pair. |

## Section 1

| ID | Line | Role |
|---|---:|---|
| Note 1.1 | 446 | Rewrites the alpha minimum using truncated defect. |
| Lemma 1.2 | 461 | Proves Definition 1 is independent of chosen good BONGs. |
| Note 1.3 | 476 | Gives the domination principle for truncated mixed defects. |
| Lemma 1.4 | 493 | Supplies the minimum-comparison arithmetic used throughout. |
| Lemma 1.5 | 525 | Gives the parity relation among four prefix-representation assertions. |
| Lemma 1.6 | 617 | Derives adjacent and cross inequalities from the order on \(\mathcal B\). |
| Lemma 1.7 | 638 | Proves that the relation on \(\mathcal B\) is an order. |
| Lemma 1.8 | 662 | Gives coordinate consequences inside \(\mathcal B(\kappa)\). |
| Note 1.9 | 683 | Records reverse-dual sequence notation and order compatibility. |
| Note 1.10 | 692 | Places the good-BONG order sequence \(\mathcal R(L)\) in \(\mathcal B\). |
| Note 1.11 | 703 | Introduces the interleaved weight sequence \(\mathfrak W(L)\). |

## Section 2

| ID | Line | Role |
|---|---:|---|
| Theorem 2.1 | 791 | Characterizes integral representation, assuming ambient-space representation, by conditions (i)--(iv). |
| Note 2.2 | 833 | Identifies condition (i) with the order relation in \(\mathcal B\). |
| Note 2.3 | 844 | Computes dualization of orders, alphas, and \(A_i\). |
| Note 2.4 | 869 | Gives the index dictionary under dualization. |
| Note 2.5 | 895 | States dual invariance of conditions (i)--(iv). |
| Note 2.6 | 913 | Lists lower bounds for \(A'_i\). |
| Lemma 2.7 | 948 | Replaces the long defect candidate in the definitions of \(A_i,A'_i\). |
| Note 2.8 | 996 | Explains endpoint conventions and simplifications of alternate \(A_i\). |
| Lemma 2.9 | 1011 | Relates \(A_i,A'_i\) to their alternate forms under the strict pair inequality. |
| Corollary 2.10 | 1064 | Reduces a high-gap defect condition to a square-class condition. |
| Lemma 2.11 | 1088 | Reduces the defect condition in the complementary adjacent-order cases. |
| Lemma 2.12 | 1125 | Makes condition (ii) vacuous between consecutive nonessential indices. |
| Lemma 2.13 | 1150 | Makes condition (iii) vacuous at a nonessential index. |
| Lemma 2.14 | 1160 | Propagates the alpha trigger when \(A_i\neq A'_i\). |
| Note 2.15 | 1199 | Characterizes \(A_i\neq A'_i\) by a strict truncated-defect inequality. |
| Lemma 2.16 | 1215 | Proves equivalence of the original alpha trigger and v2 defect trigger. |
| Corollary 2.17 | 1271 | Gives simple sufficient hypotheses for the trigger of Lemma 2.16. |
| Lemma 2.18 | 1277 | Produces alpha/defect alternatives needed for prefix representation. |
| Lemma 2.19 | 1305 | Derives a prefix representation from a sufficiently deep order gap. |
| Lemma 2.20 | 1387 | Adjoins a sufficiently deep orthogonal lattice in the unequal-rank case. |
| Lemma 2.21 | 1440 | Reduces the main theorem to the equal-rank case. |

Theorem 2.1 has the following logical shape. If the larger ambient quadratic
space represents the smaller one, then the larger lattice represents the
smaller lattice exactly when:

1. each source order is controlled by a direct or adjacent-pair inequality;
2. every relevant mixed-prefix truncated defect is at least \(A_i\);
3. each triggered central prefix of rank \(i\) represents the source prefix
   of rank \(i-1\);
4. each triggered long prefix of rank \(i+1\) represents the source prefix
   of rank \(i-1\), with the printed terminal convention.

The v2 formulation replaces the trigger in item 3 by the equivalent sum of
two truncated defects established in Lemma 2.16.

## Section 3

| ID | Line | Role |
|---|---:|---|
| Note 3.1 | 1517 | Explains when determinant approximation alone implies left/right approximation. |
| Lemma 3.2 | 1530 | Constructs prefix-product approximations from a Jordan splitting. |
| Corollary 3.3 | 1605 | Gives the reverse-end form of Lemma 3.2. |
| Lemma 3.4 | 1627 | Produces space approximations at Jordan-block boundaries. |
| Lemma 3.5 | 1702 | Computes norm-ideal order under scale truncation. |
| Lemma 3.6 | 1732 | Identifies boundary binary Jordan blocks independently of splitting. |
| Lemma 3.7 | 1744 | Collects the approximation cases used later. |
| Lemma 3.8 | 1826 | Proves the approximation definitions are BONG-independent. |
| Note 3.9 | 1870 | Replaces BONG prefix products by arbitrary valid approximations in defects. |
| Lemma 3.10 | 1897 | Reformulates conditions (ii)--(iv) using scalar and space approximations. |
| Corollary 3.11 | 1997 | Proves the main conditions are independent of good-BONG choice. |

## Section 4

| ID | Line | Role |
|---|---:|---|
| Note 4.1 | 2025 | Gives the duality dictionary for a composable triple of lattices. |
| Lemma 4.2 | 2086 | Compares the three families of \(A\)-invariants at essential indices. |
| Lemma 4.3 | 2447 | Gives the principal three-way comparison alternative. |
| Corollary 4.4 | 2528 | Gives the dual comparison alternative. |
| Lemma 4.5 | 2540 | Supplies the prefix representations and Hilbert-symbol identities for transitivity. |

## Section 5

| ID | Line | Role |
|---|---:|---|
| Lemma 5.1 | 2798 | Decomposes an index-\(\mathfrak p\) inclusion into unary/binary modular parts. |
| Note 5.2 | 2846 | Uses duality to halve the case analysis. |
| Note 5.3 | 2892 | Computes norm-ideal orders for the common and exceptional blocks. |
| Note 5.4 | 2914 | Expresses the order sequences through Jordan data. |
| Lemma 5.5 | 3010 | Proves prefix and suffix sum inequalities in \(\mathcal B\). |
| Lemma 5.6 | 3047 | Proves rigidity when a cumulative-order equality occurs. |
| Lemma 5.7 | 3114 | Analyzes projection away from a norm generator. |
| Corollary 5.8 | 3159 | Gives the possibly-bad-BONG projection form. |
| Corollary 5.9 | 3181 | Characterizes norm generators that begin a good BONG. |
| Corollary 5.10 | 3207 | Extends an admissible ambient prefix to a good BONG. |
| Note 5.11 | 3243 | Records the dual reduction in the binary exceptional case. |
| Note 5.12 | 3266 | Chooses explicit norm generators for the modular blocks. |
| Lemma 5.13 | 3309 | Controls approximations and the odd prefix-product case. |
| Lemma 5.14 | 3382 | Computes alpha at a Jordan boundary. |
| Lemma 5.15 | 3407 | Characterizes a binary modular lattice with a norm of order \(u+1\). |
| Note 5.16 | 3433 | Records an inclusion between scale truncations. |
| Lemma 5.17 | 3437 | Proves alpha comparison and equality of preceding orders. |

## Section 6

| ID | Line | Role |
|---|---:|---|
| Note 6.1 | 3901 | Expands adjacent sums in the interleaved weight sequence. |
| Proposition 6.2 | 3915 | Derives \(\mathfrak W(M)\leq\mathfrak W(N)\) from conditions (i)--(ii). |
| Lemma 6.3 | 3979 | Identifies \(A_j\) with target alphas along an equal prefix. |
| Proposition 6.4 | 4020 | Proves the main theorem for equal rank and equal volume. |
| Lemma 6.5 | 4054 | Gives the cross-order dichotomy at an odd cumulative-order difference. |
| Lemma 6.6 | 4070 | Proves parity and gap rigidity on equal-order plateaux. |
| Lemma 6.7 | 4094 | Classifies an index-\(\mathfrak p\) pair by intervals and types I--III. |
| Note 6.8 | 4253 | Describes types I--III under reverse duality. |
| Lemma 6.9 | 4268 | Computes alpha and \(A_i\) values across the classified interval. |
| Note 6.10 | 4658 | Describes overlap of types II and III. |
| Lemma 6.11 | 4674 | Gives the complete parity profile for types I--III. |
| Note 6.12 | 4708 | Sharpens selected alpha bounds to equalities. |
| Note 6.13 | 4719 | Locates whether \(A_i=\alpha_i\) or \(A_i=\beta_i\). |
| Note 6.14 | 4733 | Bounds the left order plateau. |
| Note 6.15 | 4743 | Bounds consecutive source-order gaps and identifies equality. |
| Note 6.16 | 4766 | Gives the local alpha comparison outside the odd prefix-sum case. |

## Section 7

| ID | Line | Role |
|---|---:|---|
| Lemma 7.1 | 4806 | Constructs the non-norm-generator sublattice of index \(\mathfrak p\). |
| Lemma 7.2 | 4850 | Computes cumulative-order parity for types I--III. |
| Lemma 7.3 | 4891 | Propagates equal endpoints through alpha/order plateaux. |
| Lemma 7.4 | 4927 | Bounds defects of alternating prefix products. |
| Lemma 7.5 | 4957 | Identifies the scaled hyperbolic maximal block at an extremal gap. |
| Lemma 7.6 | 4998 | Computes alternating defects for type I. |
| Lemma 7.7 | 5040 | Gives the corresponding source defect bound. |
| Lemma 7.8 | 5063 | Computes central defects and alphas for the strict type-III case. |
| Lemma 7.9 | 5122 | Shows the four-condition relation descends to the non-norm sublattice. |
| Lemma 7.10 | 6285 | Controls replacement of adjacent good-BONG segments. |
| Lemma 7.11 | 6335 | Classifies equal-order ternary lattices by one alpha. |
| Lemma 7.12 | 6356 | Gives explicit unary plus hyperbolic binary normal forms. |
| Corollary 7.13 | 6453 | Iterates the explicit normal form. |
| Lemma 7.14 | 6480 | Constructs the exceptional non-norm sublattice. |
| Lemma 7.15 | 6580 | Compares orders, alphas, and prefixes after that construction. |
| Lemma 7.16 | 6641 | Descends the four-condition relation in the exceptional construction. |
| Lemma 7.17 | 6994 | Finds the maximal alternating hyperbolic prefix. |
| Lemma 7.18 | 7065 | Gives normal forms in the three classified cases. |
| Lemma 7.19 | 7175 | Proves the required prefix isometries and alpha equalities. |
| Lemma 7.20 | 7205 | Completes the second exceptional descent. |

## Section 8

| ID | Line | Role |
|---|---:|---|
| Lemma 8.1 | 7355 | Supplies residue-field defect products, with the residue-two exception. |
| Lemma 8.2 | 7388 | Constructs elements with prescribed defect and Hilbert symbol. |
| Lemma 8.3 | 7424 | Changes the first value of a quaternary good BONG. |
| Lemma 8.4 | 7532 | Proves rigidity of alpha endpoint equalities. |
| Lemma 8.5 | 7563 | Selects the essential alpha indices used by the induction. |
| Lemma 8.6 | 7649 | Realizes prescribed diagonal values and classifies the resulting lattice. |
| Note 8.7 | 7717 | Collects consequences of \(R_{i-1}=R_{i+1}\). |
| Lemma 8.8 | 7739 | Changes the first good-BONG value, with three explicit exceptions. |
| Corollary 8.9 | 7908 | Gives the reverse-end version of Lemma 8.8. |
| Corollary 8.10 | 7921 | Normalizes the first alpha of the tail. |
| Corollary 8.11 | 7939 | Realizes each alpha on its adjacent binary segment. |
| Lemma 8.12 | 7966 | Computes the first two \(A_i,A'_i\) under equal first order. |
| Note 8.13 | 7992 | Expands the condition that a unary lattice satisfies \(N\leq M\). |
| Lemma 8.14 | 8032 | Realizes a prescribed first value unless one of three obstructions occurs. |

## Section 9

| ID | Line | Role |
|---|---:|---|
| Lemma 9.1 | 8724 | Excludes the Lemma 8.14 obstructions in five ordinary situations. |
| Lemma 9.2 | 8962 | Normalizes the source good BONG for the final descent. |
| Lemma 9.3 | 9078 | Deletes a common good head and transfers the four conditions. |
| Lemma 9.4 | 9434 | Characterizes the four-condition relation for equal-order ternary lattices. |
| Lemma 9.5 | 9459 | Gives the ternary anisotropic/isotropic normal form and alpha arithmetic. |
| Lemma 9.6 | 9571 | Handles the exceptional bad-BONG head and dual tail. |
| Lemma 9.7 | 9705 | Gives binary integral representation criteria. |
| Lemma 9.8 | 9733 | Converts the ternary condition criterion to integral representation. |
| Lemma 9.9 | 9765 | Characterizes realizable ternary order/alpha data. |
| Lemma 9.10 | 9832 | Constructs a neighboring ternary lattice with shifted second order. |
| Lemma 9.11 | 9906 | Identifies a binary non-norm sublattice with a scaled lattice. |
| Lemma 9.12 | 9930 | Produces a strict index-\(\mathfrak p\) intermediate lattice in the residual case. |
