# Lemma 6.5: pointwise even-rank obstructions

Date: 2026-09-05. Authority: Zilong He, *On n-ADC integral quadratic
lattices over algebraic number fields*, Doc. Math. 30 (2025), Lemma 6.5,
pp. 999--1000. The publisher PDF is the sole semantic authority, SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

## Frozen scope and verdict

| Code checkpoint | Clause | Independent AI verdict |
|---|---|---|
| `2a5d3afc90cbb55fef284c0678336aa58484c847` | Lemma 6.5(i) | `FULLY_FORMALIZED` / `PROVISIONAL_MATCH` |
| `9d6a4b103449e387d4c9d78de4899bd53e81e374` | Lemma 6.5(ii), with clause (i) unchanged | `FULLY_FORMALIZED` / `PROVISIONAL_MATCH` |

Both clauses of one numbered lemma are locally complete. This is not
completion of Theorem 6.1, Theorem 6.2, Section 6, or the paper. Exact-revision
clean-kit CI and human semantic approval are separate, pending gates.

## Mathematical statements and formal correspondence

Write n=2k+2, m=n+1. The source is integral with a supplied good BONG.
Its first n-2 orders alternate 0,-2e. The target is any integral-isometric
copy of either named maximal lattice N_1^n(epsilon*pi) or
N_2^n(epsilon*pi), with a supplied arbitrary good BONG and valuation-unit
epsilon. Both target classes exist at n=2.

| Clause | Additional source orders | Exact conclusion | Public endpoint |
|---|---|---|---|
| (i) | R_(n-1)=0, R_n in {-2e,2-2e}, R_(n+1)>=2 | Theorem 3.6(ii)'s single inequality fails at i=n | `Bong.BONG.GoodBONG.heADC2025Lemma65i` |
| (ii) | R_(n-1)=1, R_n=1-2e | The same single inequality fails at i=n-1 | `Bong.BONG.GoodBONG.heADC2025Lemma65ii` |

Logical strength is `LOGICALLY_EQUIVALENT` to the published clauses under
the coordinate dictionary: BONG coordinates are zero-based, whereas
`RepresentationIndex.val` is the one-based paper index. Thus the two
conclusions use index values 2k+2 and 2k+1, not 2k+1 and 2k.
Each conclusion negates the actual inequality A_i <= d[a_(1,i)b_(1,i)].
The finite rational `representationAlphaValue` equals `representationAlpha`
after coercion to extended rationals. Mere non-representation is not
substituted for this pointwise conclusion.

## Proof dependencies and trust boundary

`heADCUniformizerTest_orders` derives every target good-BONG order from
the two published Lemma 4.11(iii) unit-uniformizer endpoints. The public
Lemma 6.5 endpoints do not assume target order profiles, ambient
representations, integral representations, determinant classes or project
law interfaces. Source and target integrality remain explicit; target
integrality also follows from its isometry with the named maximal lattice.

For (i), the same-length comparison prefix has odd valuation, so its
**capped** defect is zero. The source index is terminal; the nonexistent
secondary candidate is omitted. A supposed nonpositive half-gap or primary
candidate contradicts the strict cross-order gap. The support lemma uses
only the alleged inequality at that index, not the whole family of
Theorem 3.6(ii) inequalities.

For (ii), every source adjacent pair has order gap -2e, including the final
pair (1,1-2e). Proposition 3.4 proves alpha zero and adjacent capped defect
at least 2e. Alternating capped domination joins those pairs. A second
self-prefix domination joins the signed full source prefix to the signed
target head, proving d[-a_(1,n)b_(1,n-2)] >= 2e. This retains both endpoint
alpha caps; it is not merely a statement about raw quadratic defect.
The half-gap candidate is positive, the primary candidate is at least one,
and any present secondary candidate is positive by the good-BONG two-step
order inequality. The comparison defect is zero by odd valuation. Exporting
positivity, rather than the optional stronger value A_(n-1)=1/2, proves the
complete literal source conclusion.

## Boundary and adversarial checks

- At n=2, the head is `Fin 0`, so there are no head-order assumptions.
- The empty signed prefix has defect infinity and no alpha_0 cap.
  `heADCExtremalPairs_prefixDefect` proves this base case explicitly.
- At i=n-1=1, the secondary candidate is absent. No S_0, negative index,
  or artificial beta_0 is used. The printed proof's reference to the
  n-2 head entries needs this boundary explanation; the statement is valid.
- At e=1, the source-pair alternatives and strict positivity remain valid.
- The sign product in (ii) is (-1)^(k+1)*(-1)^k = -1.
- No assumption that an ADC classification theorem already holds is used.

## Independent review and unsigned author card

The separate read-only reviewer inspected each frozen source, public type,
source correspondence and boundary case, and independently re-elaborated
both modules, their queries, the canonical entry and complete ADC audit.
No mismatch or circularity was found; all eight new transitive axiom sets
are exactly `propext`, `Classical.choice`, and `Quot.sound`. At the second
checkpoint the reviewer confirmed that clause (i)'s file was unchanged.

Author/domain-expert questions: confirm the exact failing indices, the
empty-head interpretation at n=2, and the distinction between bracketed
capped defects and raw relative quadratic defects. Formalization-expert
questions: inspect both alpha caps in self-prefix domination and the
conditional omission of the secondary candidate.

Author decision, name, date and signature: not supplied. Human domain-expert
and formalization-expert approval: not supplied. Independent AI review is
not a human sign-off.

## Reproducibility and release status

Lean 4.32.1 and the committed Lake dependency lock are unchanged. Both new
modules, canonical entry and complete audit passed local kernel checks.
No admitted proof, custom axiom or native-evaluation shortcut occurs in them.
Existing modified mathlib, aesop and batteries worktrees were preserved;
these cached-local checks do not certify a clean build.

The local Lemma 6.4 kit at code/document checkpoint
`0a49c89f5f4455756403a9fa3cc98c7a71626fee` passed extraction and 1916 file
hash checks. Its archive SHA-256 is
`2012E324DA7332B81CD16F37C463C80E97141EFD92C88E82E1BB79092F9FA585`.
That earlier kit contains neither Lemma 6.5 clause. The older successful
published-profile remote artifact likewise cannot certify these additions.
New source-only packaging and exact-revision clean-kit CI remain required.

Whole-paper grade: C. Whole-paper verdict: `NOT_COMPLETE`.
