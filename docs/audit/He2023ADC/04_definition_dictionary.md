# Definition dictionary

| Paper notion | Lean declaration |
|---|---|
| local `n`-ADC | `Bong.Lattice.IsNADC` |
| integral lattice | `Bong.Lattice.IsIntegral` |
| ambient space representation | `QuadraticSpace.Represents` |
| integral lattice representation | `Bong.Lattice.Represents` |
| `O_F`-maximal | `Bong.Lattice.IsOMaximal` |
| global `n`-ADC | `GlobalLocalLatticeSystem.IsGloballyNADC` (abstract system) |
| global `n`-universality with compatible signatures | `GlobalLocalLatticeSystem.IsGloballyNUniversal` (abstract system) |
| `n`-regular | `GlobalLocalLatticeSystem.IsNRegular` (abstract system) |
| alternating orders followed by a table tail | `heADCMaximalOrderProfile` |
| arbitrary-lattice equivalence on a specified table space | `GoodBONG.HeADCMaximalProfileCriterion` |
| unary `W_1^1(c)` and its maximal lattice | `heADCW1Unary`, `heADCN1Unary` |
| finite integral defect index `d(c)` in the nonexceptional unit rows | integer cast of `(quadraticDefect K c).toNat`, with finiteness proved from `HeHuSharpDomain` |
| signed even n-prefix in Lemma 6.4, n=2k+2 | `(-1 : Kˣ) ^ (k+1) * a.prefixProduct (2*k+2)` |
| raw defect in Lemma 6.4(i)(iv) | `Dyadic.quadraticDefect K`, valued in extended naturals with infinity retained |
| unit kappa in Lemma 6.4(iv) | valuation unit with raw defect the finite natural `2*e-1`; its sharp domain is proved |
| failing indices in Lemma 6.5(i)(ii) | `RepresentationIndex.val` is one-based: n and n-1, respectively |
| bracketed defects in Lemma 6.5 | `truncatedPrefixDefect`, retaining source and target endpoint alpha caps |
| omitted empty-prefix alpha cap | infinity, not a defined alpha_0 or beta_0 |

The `*Published` endpoints use the named `heADCW*` and `heADCN*` families
directly. `isIsometric_publishedModel_iff_orderProfile` transports the concrete
model by an equal-rank space isometry and maximal-lattice uniqueness.

The concrete-model predicate expands to: for every good BONG `a` of `L`, if `L` is
integral and its space is isometric to the reference space, then `L` is
integrally isometric to the reference lattice if and only if every order of
`a` equals the displayed profile. Its BONG argument identifies the reference
space, lattice and rank; it does not assume the desired equivalence.

The source uses one-based indices. In Lean the even zero-based positions
correspond to the source's odd positions, with order zero; the odd zero-based
positions of a hyperbolic block have order `-2e`.

In Theorem 6.1, O-maximal means maximal among norm-integral full lattices
in the same quadratic space. A volume-order difference is twice a
nonnegative inclusion index; it is not a count of BONG order profiles.
The ADC and maximality predicates both include norm-integrality.

For Lemma 6.6, `quadraticDefect K (signedEvenPrefixProduct ...)` is raw,
whereas `heADCAdjacentCappedDefect` includes the source endpoint alpha cap.
`centralDefectTrigger` is the publisher's sum-of-two-defects trigger, not
the auxiliary-alpha trigger. Its conjunction with failure of the full
target-to-(n+1)-prefix embedding expresses the exact pointwise failure.

`HeADCEvenCentralAlphaAlternatives` in Lemma 6.7 is exactly alpha_(n+1)=0,
or alpha_(n+1)=1 and raw adjacent defect = capped adjacent defect =
1-R_(n+2). `adjacentDefect` contains no alpha cap. Equality with
`heADCAdjacentCappedDefect` is a proved conclusion, not a definitional alias.

In Lemma 6.8(i)--(ii), `q.IsIsometric` is the hypothesis on the ambient
quadratic space, while `Lattice.IsIsometric` is the stronger integral
conclusion on the actual lattices. The signed full product uses all m
values and sign (-1)^(m/2); a proper head prefix is kept distinct from it.
