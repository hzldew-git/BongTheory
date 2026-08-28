# Audit Scope: Beli 2019 v2

> Current-scope notice (29 August 2026): the original comparison was made
> against the 15 August working-tree snapshot. The formal proof-and-test
> baseline is now commit `10e8c666bfda81dcac44332cd38f481d8d02e31a`.
> Reports `03`, `05`, `06`, `08`, `09`, and `11`--`14` retain explicitly
> marked historical stages; report `15` and the current review cards record
> complete local-law discharge and the remaining human-review boundary.

## Identification

- Paper: Constantin N. Beli, *Representations of quadratic lattices over dyadic local fields*.
- Version audited: arXiv v2 source dated 30 May 2022.
- PDF SHA-256: `1669C626A6D01AF297E07C2CB9584C5BD34F4CEE0F2B188EE0B351BD091C387C`.
- TeX SHA-256: `00D58B232A331E559D175C2DF383DE82A49BC7B044E035092B7AC96015858292`.
- Formal project: `BongTheory`, formal baseline commit
  `10e8c666bfda81dcac44332cd38f481d8d02e31a` on `main`.
- Principal Lean declarations:
  - `Bong.beli2019Theorem21`;
  - `Bong.beli2019Theorem21_prime`;
  - `Bong.beli2019_sufficiency_complete`.

## Scope

The paper-side inventory covers every numbered mathematical object in the v2
TeX source: 11 definitions, 96 theorem-like results, and 31 numbered notes,
for 138 objects in total. The main theorem, its revised condition (iii'), the
four condition packages, the rank reduction, and the Sections 7--9 descent
receive statement-level review. Supporting results receive declaration and
dependency mapping, with representative statement checks at each section
boundary.

The formal-side audit covers:

1. source/target orientation and rank conventions;
2. the definitions of ambient and integral representation;
3. the four conditions of Theorem 2.1 and the v2 replacement of condition
   (iii);
4. equal-rank and strict-rank sufficiency;
5. necessity;
6. all explicit typeclass assumptions;
7. admitted declarations, axioms, and kernel dependencies;
8. build and repository reproducibility.

## Method and status vocabulary

Paper extraction preceded inspection of the Lean declarations. A successful
Lean build is treated only as evidence of type correctness. It is not treated
as evidence that the formal statement matches the paper.

The audit uses the following current statuses:

- `PROVISIONAL_MATCH`: the statements appear aligned, subject to independent
  author/domain and formalization review;
- `VERIFIED_MATCH`: all semantic, trust, coverage, reproducibility, and human
  confirmation requirements have been met;
- `FORMALIZATION_WEAKER`: retained only in historical stage reports for the
  former explicit-law endpoint;
- `INSUFFICIENT_EVIDENCE`: a point cannot yet be assessed reliably.

No item is marked `VERIFIED_MATCH`, because this audit has not received the
required independent human confirmation.

## Principal conclusion

The logical assembly of Theorem 2.1, including the v2 condition `(iii')`, is
kernel checked and contains no `sorry`, project `axiom`, or theorem-level
final-step law. The current public signatures contain no project-specific
local-field, BONG, Jordan, scaling, or representation law/data parameters;
those modular interfaces are constructed by checked proof terms on the public
paths.

Accordingly, the current semantic status is `PROVISIONAL_MATCH`, Grade B.
Independent human confirmation of definitions, quantifiers, endpoints, and
normalizations is still required before `VERIFIED_MATCH` or Grade A.
