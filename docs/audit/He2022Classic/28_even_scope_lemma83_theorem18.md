# Even scope of Lemma 8.3 and Theorem 1.8

Status: `EVEN_SCOPE_CONDITIONAL_FORMALIZATION` /
`UNRESTRICTED_V5_PROOF_INCOMPLETE`.

Code checkpoint:
`a5b50fbe9fa7648a3a78e6de3cdaf94b46732540` on
`release/heclassic-v0.5.0-rc.1-prep`.

## Source authority and locator

The sole semantic authority is the author-corrected v5 TeX manuscript
`classic_dyadic-n-uni-v5.tex`, SHA-256
`C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
Lemma 8.3 and its proof occupy lines 1680--1693; Theorem 1.8 is stated at
lines 231--232 and proved at lines 1694--1696.

The v5 Lemma 8.3 statement has no parity restriction, but its proof begins by
assuming without justification that `n >= 2` is even.  The subsequent use of
Corollary 6.3 cannot justify the missing odd case because Report 26 gives a
kernel-checked odd counterexample to that corollary.  This does not by itself
disprove Lemma 8.3, but it leaves its odd branch and the corresponding branch
of Theorem 1.8 unproved.

## Formal change

The former declarations `he2022ClassicLemma83` and
`he2022ClassicTheorem18` exposed unrestricted conclusions while accepting
the local obstruction itself as a field.  They are removed.  The replacement
declarations are:

- `he2022ClassicLemma83_even`, with explicit hypotheses `2 <= n` and
  `Even n`; and
- `he2022ClassicTheorem18_even`, with the same rank restriction.

`Lemma83Laws.local_ramified_obstruction` now has this exact even scope.
Theorem 1.8's remaining deduction is proved: Proposition 8.2 localizes global
universality over the base field, the even Lemma 8.3 endpoint supplies the
local obstruction, and Proposition 8.2 localizes any alleged universality
over the extension field to obtain a contradiction.

No unrestricted compatibility theorem remains.  Thus downstream users cannot
accidentally invoke the unsupported odd statement.

## Mechanical evidence

With Lean 4.32.1, `BongTest.He2022ClassicEvenExtensionAudit` completes a
5,000-job focused build and runs directly.  The even Lemma 8.3 endpoint has an
empty axiom set; the even Theorem 1.8 endpoint reports only `propext` and
`Quot.sound`.

The canonical paper and audit build completes 5,017 jobs.  The focused
imported-closure gate reports `AXIOM_GATE_PASS: 62656 declarations checked`.
All 30 policy tests pass, and the comment-aware scanner checks 2,791 tracked
Lean sources without finding a forbidden proof token.  These checks reuse
local artifacts; exact clean-kit verification remains separate.

## Fidelity boundary

The new endpoints formalize only what the written proof supports.  They are
still conditional on a concrete implementation of the local
scalar-extension obstruction.  The odd branch of Lemma 8.3 and Theorem 1.8
remains outside formalized scope until a new mathematical proof or an
author-approved source restriction is supplied.

This scope correction does not change the Grade-D whole-paper verdict.  The
authoritative v5 Corollary 6.3 remains false as stated, and concrete global
number-field instances remain incomplete.
