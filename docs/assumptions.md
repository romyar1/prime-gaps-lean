# Assumptions and theorem scope

The prime-gap endpoint is a conditional theorem. In
[`PrimeGaps182Analytic.lean`](../formal/PrimeGaps182Analytic.lean),
`PrimeGap182.infinite_consecutive_prime_pairs182_of_local_inputs` proves that
infinitely many consecutive natural primes have gap at most 182, given the
inputs below. Its conclusion concerns actual primes and excludes every
intervening prime.

| Input | What must be supplied | Formal status |
| --- | --- | --- |
| `PhysicalSourceBounds182` | 262 fixed integral inequalities | Explicit numerical premises |
| `PublicPrimeLocalBounds182` | Two established finite-field estimates, at every prime | Explicit premises |
| `AllIncidenceRankFourBounds` | The established scalar rank-four Kloosterman estimate, at every prime | Explicit premise |
| `0 ≤ C` and `TypeIII.LocalFourierHypothesis C D p₀` | The Type III estimates with constants uniform in primes and parameters | Supplied by the September 18 conditional derivation from common published-theorem interfaces; no closed proof |

No global bilinear, distribution, support, or sieve-moment estimate is supplied
as an additional hypothesis of this endpoint. The repository formalizes those
analytic reductions from the displayed inputs. The more general many-primes
companion result is outside this endpoint's scope.

## The 262 numerical premises

The exact integral definitions are in
[`PhysicalTrial182.lean`](../formal/PhysicalTrial182.lean) and
[`SourceBounds182.lean`](../formal/SourceBounds182.lean). The coefficients,
regions, and rational bounds are fixed in
[`TrialData182.lean`](../formal/TrialData182.lean) and
[`SourceData182.lean`](../formal/SourceData182.lean).

| Field | Inequality, with rational constants cast to the reals | Count |
| --- | --- | ---: |
| `cap.denominator_lower` | `trialDenominatorLower ≤ trialSquareIntegral` | 1 |
| `cap.denominator_upper` | `trialSquareIntegral ≤ trialDenominatorUpper` | 1 |
| `cap.base_lower` | `trialJ0Lower ≤ trialBaseIntegral` | 1 |
| `cap.enlargement_lower` | `trialJPlusLower ≤ trialEnlargementIntegral` | 1 |
| `cap.tail_upper` | `trialTailIntegral ≤ trialTailUpper` | 1 |
| `outerRoot` | `trialSourceOuterRoot j ≤ (trialOuterCertificates j).rootUpper`, every `j : Fin 60` | 60 |
| `outerFace` | `trialSourceOuterFace j ≤ (trialOuterCertificates j).faceUpper`, every `j : Fin 60` | 60 |
| `innerMass` | `trialSourceInnerMass j ≤ (trialInnerCertificates j).faceUpper`, every `j : Fin 137` | 137 |
| **Total** | Five cap bounds, 120 outer bounds, and 137 inner bounds | **262** |

These are inequalities for the actual fragment-law integrals. The 60 outer
components each require two inequalities; the 137 inner components each require
one. This explains the separate count of 197 source components.

The files under [`inputs/source_certificates`](../inputs/source_certificates/)
are supporting numerical records. The Lean kernel does not read those JSON
files as proofs of `PhysicalSourceBounds182`. Checking their hashes or their
arithmetic consistency does not discharge the integral inequalities. See
[`numerical-data.md`](numerical-data.md) for their provenance and limits.

The [external verification package](../research/numerical_182/README.md)
completed a fresh run of the numerical programs on 9 September 2026. All 262
rational target comparisons, 14 implementation audits, and four deliberate
rejection controls passed. This supports the numerical premises externally;
it does not replace them with Lean proofs or complete the separate Type III
argument. The algorithm-to-integral reasoning remains subject to mathematical
review.

## The three established finite-field estimates

Write `eₚ` for the standard nontrivial additive character of the prime field.
All parameters declared nonzero below range over that field, and every bound
is required for every prime, including 2.

1. The normalized rank-three sum
   `Kl₃(c) = p⁻¹ Σ_{u,v ≠ 0} eₚ(u+v+c/(uv))` satisfies
   `|Kl₃(c)| ≤ 3` for `c ≠ 0`.
2. With `Kl₂,raw(c) = Σ_{u ≠ 0} eₚ(u+c/u)`,
   `|Σ_{t ≠ 0,−1} Kl₂,raw(A/t) Kl₂,raw(B/(t+1))| ≤ 8p√p`
   for all `A,B ≠ 0`; there is no assumption `A ≠ B`.
3. The raw rank-four sum
   `|Σ_{u,v,w ≠ 0} eₚ(u+v+w+c/(uvw))| ≤ 4p√p`
   for `c ≠ 0`.

Items 1 and 2 are precisely the conjuncts of
[`PublicPrimeLocalBounds182`](../formal/PrimeSourcePublic182.lean). Item 3 is
[`IncidenceRankFourBound`](../formal/IncidenceRankFour.lean), quantified over
all primes by [`AllIncidenceRankFourBounds`](../formal/IncidenceSquarefree.lean).
The third estimate is an additional rank specialization; it is not derived
from the two fixed-rank premises in this code.

The rank-three and rank-four bounds follow from the general Kloosterman-sheaf
rank, trace, and purity theorem: specialize the raw bound
`n p^((n−1)/2)` to `n=3,4`, and divide by `p` for the normalized rank-three
sum. See [Katz, Theorem 4.1.1](https://web.math.princeton.edu/~nmk/Katz-GKM.pdf).
The two-Kloosterman correlation is
[Fouvry–Kowalski–Michel, Proposition 2](https://people.math.ethz.ch/~kowalski/friedlander-iwaniec-sum.pdf),
after multiplying its two normalized sums by `√p` each. These source matches
identify established mathematical inputs; the cited geometric proofs have
not been formalized here.

## The Type III premise and axiom reports

[`TypeIIILocal.lean`](../formal/TypeIIILocal.lean) defines the actual finite
sums and the exact target `HasFiniteExceptionalTypeIIIInput`. The same positive
real constant `C`, integer bound `D`, and cutoff `p₀` must work for every prime
`p > p₀` and every nonzero `α,m,m′,n,n′`. The distinct-index branch has a
bounded finite exceptional set; the repeated-index branch has a bounded-degree
exceptional curve and a separate origin term. See
[`type-iii.md`](type-iii.md) for the statement and progress map.

The [September 18 derivation](type-iii-published-general-application.md)
constructs this exact Type III input from precisely stated general-theorem
interfaces. The ordinary, derived and perverse categories, inverse images,
primitive objects, cohomology, local observers and arithmetic lifts must belong
to one common theory fixed before the prime. The source derives the actual
family applications and uniform constants from those interfaces, instead of
assuming a finished Type III application.

The existence and joint continuous-adic interpretation of that theory and the
applicability of the cited results remain external mathematical inputs. The
prime-gap theorem retains its original Type III argument, which can be supplied
by this conditional derivation once those inputs are provided. Full local
verification of the integrated snapshot passed; its evidence and exact scope
are recorded in [STATUS.md](../STATUS.md).
A standard-only `#print axioms` result for a conditional theorem says that its
proof term uses only the permitted logical axioms. The mathematical premises
remain arguments to that theorem. Consequently, a successful build and axiom
audit do not prove the numerical inequalities, the three established bounds,
or the Type III proposition.
