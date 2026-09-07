# Local monodromy and constituent exclusion: published-input audit

This audit concerns the actual corrected rank-six correlation family and
Sections 6–7 of `finite_exceptional_type_iii_revised.tex`. It separates
published general results from their application to this family. It does
not assert that the local Fourier proposition has already been proved in
Lean, and it does not change the manuscript or the foundational modules.

The preferred route uses coefficient covariance and the existing
`ScalingLines` result to reduce proper Fourier supports to origin lines
and the origin. It can therefore omit the manuscript's curve-to-line
lemma. The generic line-support/descent argument and its scalar contradiction
are now checked under explicit geometric laws in
`TypeIIIPublishedFourierRules`. The actual local-Fourier realization of the
rank-six family remains application data.

## Primary sources and exact locators

* [Lei Fu, *Calculation of ℓ-adic Local Fourier Transformations*, final
  arXiv version](https://arxiv.org/pdf/math/0702436v5), Theorem 0.1(iii),
  pp. 5–6, and Proposition 0.8, p. 13. The published article is
  *Manuscripta Mathematica* **133** (2010), 409–464,
  [DOI](https://doi.org/10.1007/s00229-010-0377-x). Proposition 0.8 gives
  the geometric Kloosterman inertia models; Theorem 0.1(iii) computes
  infinity-to-zero local Fourier transforms of the stated tame rank-one
  twists and monomial pushforwards. For the application below its
  conditions reduce to characteristic greater than 3 and a nonzero
  phase coefficient.
* [Gérard Laumon, *Transformation de Fourier, constantes d'équations
  fonctionnelles et conjecture de Weil*](https://www.numdam.org/article/PMIHES_1987__65__131_0.pdf),
  *Publ. Math. IHÉS* **65** (1987), 131–210. The finite-origin exact
  sequence is in §2.3.2, pp. 159–160; Proposition 2.3.2.1(iii) and
  Lemma 2.4.2.1(ii) identify its local contribution. Theorem 2.4.3
  gives exactness and rank/Swan rules. Proposition 2.3.3.1(iii) is the
  infinity stationary-phase decomposition, and Proposition 2.5.3.1
  treats tame characters. Fourier inversion and linear-map compatibility
  are Theorems 1.2.2.1 and 1.2.2.4; base change is Proposition 1.2.2.9;
  translation is Proposition 1.2.3.2. These statements concern the actual
  Fourier functors over a perfect field of characteristic different from
  the coefficient characteristic, with the paper's constructibility and
  finiteness conventions.
* [Nicholas Katz, *Gauss Sums, Kloosterman Sums, and Monodromy
  Groups*](https://web.math.princeton.edu/~nmk/Katz-GKM.pdf), Theorem
  7.4.3, pp. 108–109: the zero-inertia representation of the Kloosterman
  sheaf has one unipotent Jordan block, with the specified arithmetic
  action. This supports the boundary calculation; Fu's Proposition 0.8
  already supplies its geometric part.

Neither curve-exclusion lemma is a theorem quoted verbatim from these
sources. Both are deductions specific to the argument under audit.

## Actual rank-six representation and exhaustive phases

Work geometrically over an algebraically closed field of characteristic
`p > 3`, with characteristic-zero ℓ-adic coefficients and `ℓ ≠ p`.
Let `K` be the normalized rank-three Kloosterman sheaf, let

```
F_λ = K(x) ⊗ K(λx)^∨,
K_λ = j_* F_λ[1],          j : G_m → A¹,
```

where `j_*` in this expression is the ordinary middle-extension sheaf.
Use the positive Fourier kernel `AS_ψ(ξx)`. The actual core is the
parabolic image, or equivalently its identified Fourier description on
`ξ ≠ 0`; this identification is a family application and must remain
visible in an imported-theorem interface.

The rank computation uses actual cohomology. At zero the common regular
unipotent block has a three-dimensional commuting algebra. Twisting by
`AS_ψ(ξx)` gives all nine slopes equal to one at infinity when `ξ ≠ 0`.
The Euler characteristic of the ordinary middle extension is therefore
`−9 + 3 = −6`. The degree-zero and degree-two compact cohomology vanish,
so the core has rank six. This is a deduction from the generic conductor
and cohomology laws, not a statement in Fu asserting the rank of this
correlation family.

For `λ ≠ 0,1`, the geometric infinity representation decomposes as three
blocks indexed by `q³ = λ`:

```
[3]_* AS_ψ(3(1−q)x),
```

up to the harmless tame and unramified factors. Put `d = 1−q`. Substitution
in the local Fourier formula gives

```
γ(x) = x³,       δ(x) = −d/x²,       β(x) = 2dx.
```

Each block contributes rank two and is entirely wild. After the
quadratic cover its two pole-one coefficients are, with signs absorbing
the square-root choice,

```
±2 sqrt(A(q−1)³),                 A = 1/ξ.
```

Here is the necessary **exhaustion argument**. It cannot be replaced by
the observation that six expressions have been displayed. The actual
finite-origin vanishing-cycle sequence has the form

```
0 → A₀ → H → V → B₀ → 0,
```

where `H` is the generic inertia representation of the Fourier core,
`V` is the infinity-to-zero local Fourier output, and `A₀,B₀` have
trivial geometric inertia. In particular, the natural arrow points
`H → V`, not `V → H`. The computed `V` has no tame quotient, hence its
map to `B₀` is zero. Exactness makes `H → V` surjective. Both spaces
have dimension six, so this map is an isomorphism and `A₀ = B₀ = 0`.
This establishes the complete list on the actual representation.

The generic angular parameter is `λ = m/(nz³)`, so it avoids 1. At
`λ = 1` one cubic branch has `q = 1`, and its input is tame. The local
Fourier calculation then has a tame part; the rank-six core has a
two-dimensional tame remainder and four wild dimensions. An imported
statement claiming six wild characters for every nonzero `λ` is false.
The generic-ray argument and its chosen constant-ray specialization
exclude these finitely many directions, so they do not require that
false strengthening.

## Literal connection with the proved rectangle phases

On the ray `(r₁,r₂)=(t,zt)`, put `t=T²`. The actual parameters are

```
A = αz/(mt),      λ = m/(nz³),      q = γ/z,      γ³ = m/n.
```

The local coefficient is then

```
A_e (γ_e−z)^(3/2)/z,              A_e² = 4α/m_i.
```

For every nonempty subset `s` of the four entries, the wild characters
of the tensor subproduct have coefficients

```
Σ e∈s, A_e (γ_e−z) R_e / z,       R_e² = γ_e−z.
```

Duals reverse signs; the weight-normalized conjugate factor is
`H^∨(−1)`, not merely `H^∨`. Signs and independent choices of the roots
are already permitted in the formal scalar theorem. The Tate twist has
trivial geometric inertia. Distinct rows and columns are needed for
noncancellation; opposite-corner coincidences of cubic roots are allowed
and are handled by that theorem.

The exact existing endpoint is
`PrimeGap182.TypeIII.algebraicDistinctRectanglePhase_ne_linearReciprocalSqrt`
in `formal/TypeIIIPhaseObstruction.lean`. Its left side is literally

```
Σ e∈s, radialPhaseScalar (A e) (γ e) • R e
```

in `AlgebraicClosure (RatFunc k)`. It excludes `C(c)/u` for `c ≠ 0`
and `u² = C(a)+C(b)X`, under the cube and amplitude-square equations,
nonzero parameters, nonempty `s`, distinct rows and columns, and
characteristic different from two. The existing
`distinctRectanglePhase_ne_zero` excludes zero under the same
rectangle conditions. These are unconditional scalar results.
`TypeIIIPublishedPhaseApplication` derives the representation profile and
containment from Fu's general rule and the supplied exact maps. Identifying
those maps and representations with the physical family remains explicit.

`TypeIIIPublishedLocalPhases` packages these coefficients into
`rectangleAllowedPhases α m n s`, proves that this set is finite, and
proves that it contains neither zero nor any such reciprocal-square-root
coefficient. The separate representation argument establishes exhaustion
from its stated Mackey and finite-origin data.

## Origin-line support and the generic geometric bridge

For a linear inclusion `i : A¹ → A²`, write `π` for its transpose.
The normalized Fourier convention gives

```
FT₂(i_* P) ≅ π* FT₁(P)[1].
```

Consequently a full-support simple perverse sheaf whose Fourier
transform is supported on that origin line has generic lisse part
`J(ar₁+br₂)` for a nonzero one-variable sheaf `J`, with `(a,b) ≠ (0,0)`.
This follows from the genuine Fourier equivalence, the simple-support
description, and inversion; it is not a hypothesis asserting exclusion.
Reflection can be absorbed in `(a,b)`, and Tate twists do not change
geometric inertia.

The following application then produces an explicit scalar contradiction.

1. Choose a constant direction `z₀` outside the branch directions, the
   zero/pole images of the finite phase list, the locus `a+bz₀=0`, and
   the finitely many lines wholly contained in the complement of the
   generic lisse identification. An algebraically closed field is
   infinite, so this is possible.
2. Restrict the actual nonzero lisse subquotient. Its rank is unchanged.
   Its wild characters on that ray form a nonempty sublist of
   `AS_ψ(β_j(z₀)/T)`, with every coefficient nonzero.
3. Choose `u₀²=a+bz₀` and set `Y=u₀T`. This identifies the wild
   characters of the fixed sheaf `J(Y²)` as `AS_ψ(c_j/Y)` for constants
   `c_j=u₀β_j(z₀) ≠ 0` in `k`.
4. Over the generic direction choose `u(z)²=a+bz`. The same fixed
   representation is base changed, and `Y=u(z)T`; thus its coefficients
   are `c_j/u(z)`. Matching any constituent character to the exhaustive
   list gives the equality excluded by the existing scalar theorem.

This uses exact pullback on lisse representations, semisimplicity of the
finite wild image with characteristic-zero coefficients, local base
change, and Artin–Schreier character transport under a change of
parameter. A nonzero pole-one coefficient cannot be an
Artin–Schreier coboundary: a pole of `g^p−g` has order divisible by `p`.
It is therefore legitimate to match coefficients, not just slopes.

An alternative is to use the existing
`rescaled_distinctRectanglePhase_not_mem_finite_invariant_artinSchreier_set`
from `TypeIIIArtinSchreierAction.lean`. Descent of `J(Y²)` gives an
automorphism-invariant finite set of actual Artin–Schreier characters;
the proved orbit obstruction rules out the rescaled coefficient. This
avoids the constant-direction selection but still needs the genuine
descent and inertia-functoriality bridge. A finite set simply declared
to be invariant is not a published realization theorem.

## Audit of the two curve-exclusion lemmas

The manuscript correctly presents its curve-to-line lemma as a result
of the paper. The degree hypothesis `D<p` is substantive: it makes the
generic degree-`D` projection separable with tame ramification, and
prevents constant Gauss direction or an Euler derivative identity from
hiding characteristic-`p` terms. At a generic tangent direction there is
a smooth lisse point with nonzero critical value. Its ramification index
may exceed two. The nontrivial tame characters in the local permutation
representation survive middle extension because they have no inertia
invariants. The stationary-phase contribution is a direct summand, so
other critical points cannot cancel it. This yields a wild linear phase
at radial infinity, contradicting tameness. For an offset line,
uniqueness of a linear twist making a nonzero representation tame forces
the offset to lie on the direction line. No defect was found in this
argument with its stated hypotheses.

The origin-line lemma uses more than the absence of tame characters:
the constant-direction step above is essential to obtain a coefficient
in the constant field. Its final obstruction agrees with the formal
scalar result, including one-group and opposite-corner cases. No defect
was found provided the exhaustive actual local list is supplied by the
finite-origin sequence, rather than by rank counting in isolation.

The covariance route bypasses the first lemma altogether.
`TypeIIIInvariantSupportComponents` combines containment in a finite union
of origin lines with closedness, irreducibility and dimension to put a
one-dimensional simple support in a whole origin line. The generic support
classification supplies these geometric hypotheses.

For repeated indices, the current Lean route uses the bounded cardinality
and eight-dilation invariance of the union of punctual supports to put that
union at the origin. It needs no separate radial-infinity tameness argument.
Constant constituents remain possible, consistently with the larger permitted
Fourier-origin value. In the manuscript's alternative tameness argument,
the local lemma for `V_![1]` cannot be applied directly as an equality for
`j_*V[1]` when zero-inertia invariants are nonzero; the middle-extension
boundary sequence accounts for the extra constant Fourier terms.

## Minimal generic theorem interface and unproved applications

The following separation is suitable for explicit Lean hypotheses.

| Generic law that may be imported with its source | Family application and current Lean status |
| --- | --- |
| Kloosterman geometric inertia model; monomial local Fourier formula with its nonvanishing and characteristic hypotheses | The three Mackey blocks are supplied as actual representation data; Fu's general rule then gives the checked six-dimensional profile. |
| Finite-origin vanishing-cycle sequence and its local-Fourier identification | `CoreLocalData` supplies the map `H → V`, its exactness and tame target; its geometric identification remains explicit. |
| Finite-dimensional exactness and absence of maps from all-wild to tame representations | Surjectivity and then bijectivity of that same map are proved; no omitted remainder is assumed. |
| Fourier inversion, linear-map compatibility, simple-support classification | The generic rules identify the inverse of an origin-line constituent with a linear pullback. The support exclusion applies that identification. |
| Functoriality of actual inertia under lisse subquotients, field extension and parameter scaling | The generic descended phase set is finite and invariant; the checked descent lemma supplies the forbidden constant-field coefficient. |
| Existing exact scalar phase theorems | The contradiction for distinct rows and columns is proved. |

The checked elementary exhaustion lemma has inputs linear maps
`f : H → V`, `g : V → T`, `range(f)=ker(g)`, `g=0`, and equal finite
dimensions of `H,V`; its output is bijectivity of **that same** `f`.
The representation application derives `g=0` from its phase rules and Fu's
formula, then applies this lemma. The actual vanishing-cycle and Mackey
identifications still have to supply the stated maps. No field simply
asserts that the finished correlation has no omitted constituents.

The resulting phase exclusions are progress on the arithmetic end of
the argument, but the complete Type III conclusion additionally needs
the audited trace, weight, strict-support and complexity inputs. In
particular, coefficient covariance is not norm preservation; the
prime-field corrected trace formula must not be asserted unchanged over
every finite extension. With the stated constant sign twist the trace
over `F_(p^d)` is `(-1)^(d+1)(C_(p^d)+κ_(p^d))`.
