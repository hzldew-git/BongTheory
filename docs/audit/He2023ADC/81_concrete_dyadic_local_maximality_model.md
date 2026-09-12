# Concrete dyadic local maximality model

Status: `CONCRETE_DYADIC_LOCAL_FORMALIZATION` / `SOURCE_LOGIC_MATCH`.

Code checkpoint:
`c939c9fa80ff455f2b4c13933c720c9ad1fbe76d` on
`feat/he2023adc-dyadic-local-model`.

## Source authority and locators

The semantic authority is Zilong He, *On n-ADC integral quadratic lattices
over algebraic number fields*, *Documenta Mathematica* 30 (2025), no. 4,
981--1022, DOI 10.4171/DM/1003. The publisher PDF used by this repository has
SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Theorem 1.5 appears on publisher page 984. Its proof on page 1016 uses
Proposition 4.15, Theorems 5.1, 6.1, and 7.1 for the local equivalence, then
O'Meara section 82K for its global form. Lemma 8.1(ii), on page 1017, uses
local maximality and Lemma 4.14.

## Formal change

`He2023ADCDyadicLocalModel` gives the abstract Section 8 local interface an
actual interpretation over one dyadic local field. Its lattice objects are
the repository's bundled `QuadraticLatticeModel`s, its unique place is
`Unit`, and localization is the identity. The following facts are proved:

1. abstract pointwise `IsNADCAt` is equivalent to the concrete bundled
   `IsNADC` predicate, including its quantification over arbitrary rank-`n`
   carrier types;
2. every integral bundled target has an actual maximal superlattice, with the
   required integral representation and ambient-space compatibility;
3. an actual maximal source represents an actual maximal target whenever its
   ambient quadratic space represents the target space;
4. actual integral lattice representations compose;
5. in equal rank, `n`-ADC implies maximality by the proved Proposition 4.15;
6. in rank `n+1`, the same necessity follows by `Nat.even_or_odd`: Theorem
   6.1 handles even `n >= 2`, while the repaired Theorem 7.1 handles odd
   `n >= 3`.

Consequently `localMaximalityLaws` is a concrete proof term with no additional
proposition-valued parameter, and `local_theorem15` proves the local dyadic
Theorem 1.5(i) for ranks `n` and `n+1`.

The intermediate
`localMaximalityLaws_of_rank_succ_necessity` remains public because it records
the exact assembly boundary independently of the available classification
theorems; it is not used to weaken the unconditional dyadic endpoint.

## Mechanical evidence

Using Lean 4.32.1, the new module, canonical paper entry, and focused audit
all elaborate successfully against the already-built exact predecessor
closure at `a57373b`. The focused audit checks ten declarations and prints
nine transitive axiom reports. Every report contains exactly the permitted
set

```text
propext
Classical.choice
Quot.sound
```

The comment-aware source scanner checks 2,740 tracked Lean files and finds no
forbidden proof token outside comments. All 30 deployment, scanner, and shard
planner tests pass, the new Lean files have no line longer than 100 columns,
and the staged diff check is clean.

This is focused local evidence. A fresh-extraction Review Kit, its complete
paper audit set, the enforcing namespace gate, and GitHub exact-head CI remain
separate reproducibility gates for the new checkpoint.

## Fidelity boundary

The construction is intentionally a one-place dyadic local model. Copying the
same bundled local object into the structure's global fields is only a typed
adapter for the local theorem; it is not a model of lattices over a number
field, its set of finite places, localization, genus, regularity, or class
number.

Thus this checkpoint closes the dyadic local-maximality instance formerly
listed in Report 74, but it does not instantiate the non-dyadic branch, the
all-place number-field `SectionEightLaws`, Meyer--Xu--O'Meara genus inputs,
scaling laws, or O'Meara 82K. It also does not alter the disclosed publisher
mismatches, the Grade-D `NOT_COMPLETE` verdict, or the unsigned human semantic
review status.
