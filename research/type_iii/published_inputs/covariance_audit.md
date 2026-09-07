# All-extension covariance: scope and primary-source audit

Review date: 2026-09-05. The mathematical body of
`formal/TypeIIIPublishedCovarianceRules.lean` was reviewed read-only after its
strict PASS10. The ten printed declarations use only the standard Lean
axioms. The source snapshot was
`c3a044408ce47fdce3d4efff3bf4bf0c9464a559ff567755b970fc1163d18516`;
the log snapshot was
`dd2f70315aad55fa1e7291adcabe48db11feb07065833ed261b662dd7a7ce750`.
The owner may append generated-declaration probes without changing this
mathematical body. This audit did not compile or edit that source.

## Finding

**CLEAN, with the explicitly conditional scope retained.** The file proves
geometric coefficient/dilation covariance from general transport and
Chebotarev laws, the actual signed trace identity over every finite extension,
and the separately stated `TorusIC` property. It does not construct the
rank-six sheaf, prove its trace formula, identify an arbitrary arithmetic
extension, or prove a Fourier norm bound.

* `ExpectedCoreTrace` quantifies over every finite field with its actual
  `ZMod p` algebra structure and over every point of the whole unit torus.
  These fields are in `Type 0`; this includes models of all finite extensions
  and is sufficient for the intended closed-point test. One fixed `sigma`
  acts throughout. The scalar, correction, extension-degree sign, and four
  conjugation positions are the ones in `FiniteFieldSums.expectedTrace`.
* `trace_coefficient` explicitly supplies the compatibility between the
  coefficient functor and the chosen complex embedding. It is not inferred
  from the existence of an arbitrary complex automorphism.
* `TorusIC` is an uninterpreted predicate in this abstract interface. Its
  intended realization must mean intermediate extension from the whole
  smooth torus of a geometrically semisimple lisse sheaf, with the fixed
  perverse shift `[2]`. The general `chebotarev` field then has the correct
  **geometric** conclusion. No arithmetic semisimplicity is required.
* `physical_covariance_of_expected_trace` derives dilation by `a^-2` from
  the exact finite-sum theorem and the literal pullback trace rule. Nonzero
  row and column parameters suffice for this arithmetic step; existence of
  the intended torus family additionally uses the usual nonzero `alpha`.
* For the positive Fourier kernel, `FT_(psi_b)(s_c^* P)` is
  `s_(b/c)^* FT_psi(P)`. Thus `b=a`, `c=a^-2` gives `a^3`; at `a=2`
  this is exactly eight. The two-dimensional Fourier shift has even sign,
  and this automorphism change of variables adds no Tate twist or power of
  the field cardinality.
* Geometric isomorphism is used only with the already explicit geometric
  support/stalk laws. Neither this file nor its imported finite-sum proof
  assumes that complex coefficient automorphisms preserve absolute values.

No mathematical correction to the reviewed file is indicated.

## Primary Chebotarev locators

1. Nicholas M. Katz, *Twisted L-Functions and Monodromy*, Remark 7.0.5,
   printed p. 125, author PDF page 131 (zero-based index 130): a lisse
   characteristic-zero adic sheaf is determined up to semisimplification
   by its local Frobenius characteristic polynomials. The subsequent
   isomorphism statement there uses the particular sheaf's irreducibility;
   that extra conclusion is not being imported indiscriminately here.
   [Author's complete text](https://web.math.princeton.edu/~nmk/twistedLfctnov052001.pdf#page=131).

2. Katz, *Moments, Monodromy, and Perversity: a Diophantine Perspective*,
   §6.7.10, author Chapter 6 p. 46 (PDF page 46, index 45), gives the
   precise argument needed here. Equal trace functions give isomorphic
   arithmetic semisimplifications by Chebotarev; their geometric
   semisimplifications consequently agree. Geometric semisimplicity of
   the pure lisse sheaves then gives a geometric isomorphism.
   [Author's Chapter 6](https://web.math.princeton.edu/~nmk/mmp/chpt6midconv78.pdf#page=46).

3. Pierre Deligne, *La conjecture de Weil II*, Theorem 3.4.1(iii), printed
   p. 207 (PDF page 71, index 70), states geometric semisimplicity for
   a lisse pointwise iota-pure sheaf on a **normal** finite-type scheme over
   a finite field. The torus satisfies normality. Corollary 3.3.6, printed
   p. 206, supplies the separate purity of the image of compactly supported
   cohomology in ordinary cohomology of a smooth variety.
   [Author's text](https://publications.ias.edu/sites/default/files/Number40.pdf#page=71).

The passage from this module's all-extension trace premise to the
characteristic-polynomial formulation is elementary: a closed point and its
base changes to extensions of its residue field give the traces of every
positive power of its invertible Frobenius. In characteristic zero these
power traces determine `det(1-T Frob)`, for example by Newton identities.
Chebotarev and the characteristic-zero character criterion then determine
semisimplification. Restrict to geometric monodromy, use the semisimplicity
specified by `TorusIC`, and extend the isomorphism by intermediate-extension
uniqueness. This is a deduction from the stated inputs, not an assertion that
prime-field traces alone determine sheaves.

For the Fourier direction, Laumon's Theorem 1.2.2.4, printed p. 143
(PDF page 14), gives compatibility with a linear map and its transpose.
Specializing to invertible scalar maps has no dimension-shift discrepancy;
replacing the character by `psi_b` gives the displayed factor `b/c`.
[Original article](https://www.numdam.org/article/PMIHES_1987__65__131_0.pdf#page=14).

## A bounded parabolic trace/rank adapter

The next useful module can prove the numerical consequences of a supplied
**actual Frobenius-equivariant short exact sequence**. It should not assume
the final corrected-core trace or rank as fields of a record called
published theory. The existing `TypeIIIJordanCorrection` already proves

```
dim J = 3,
Tr(Frob_J) = 1 + q^-1 + q^-2,
```

for the actual centralizer `J` of the three-by-three nilpotent Jordan block
and actual conjugation by `diag(1,q,q^2)`.

Use spaces and linear maps

```
0 -> J --i--> Vc --pi--> Vpar -> 0
```

with finite-dimensional `Vc`, literal injectivity, surjectivity and
`range i = ker pi`, and commuting squares for the three Frobenius operators.
Trace additivity and dimension additivity should then prove

```
dim Vc = 9                  ==> dim Vpar = 6,
Tr(Frob_Vc) = -correlation  ==> Tr(Frob_Vpar) = -(correlation + kappa_q).
```

Multiplying the last operator by `(-1)^d` gives the required
`(-1)^(d+1)(correlation+kappa_q)`. Identifying the supplied spaces/maps with
the actual curve cohomology remains explicit construction data. The
three-dimensional boundary Frobenius identification must be justified using
the arithmetic local model; the matrix computation alone is not that
identification.

The published inputs and their family applications should stay separated:

| General input | Application still to be supplied or proved |
|---|---|
| Kloosterman rank, normalized trace, and local inertia/Frobenius model | Form `Kl3(x) tensor Kl3(lambda*x)^dual tensor AS(ksi*x)` and match its literal trace with the existing finite sums. |
| Tensor/dual slope rules and Artin–Schreier slope one | At every unit `(lambda,ksi)`, derive rank nine, Swan zero at zero, nine slopes one at infinity, and absence of invariants at infinity. This includes `lambda=1`. |
| Grothendieck–Ogg–Shafarevich and cohomological vanishing/duality | Derive the actual `dim Hc1=9` and vanishing of `Hc0,Hc2`; these numerical outputs are applications, not quoted correlation theorems. |
| Boundary cohomology exact sequence and trace formula | Identify `i,pi,Vc,Vpar` and their Frobenius actions. Reindex the curve variable to obtain `C_q(ksi^-1,lambda*ksi^-1,1)` with the original sign. |
| Katz's arithmetic regular-unipotent local description | Identify the zero-boundary representation with the Jordan calculation, including the effect of multiplication by `lambda` on a Frobenius lift. |
| Conductor-constancy theorem, relative duality, and exactness of lisse stalk pullback | Prove whole-torus lissity and base change of the parabolic image. A dense-open theorem or constant fiber dimension alone is insufficient. The finite-coefficient-to-adic passage must be retained if that form of the conductor theorem is used. |
| Deligne parabolic purity, tensor/pullback purity and geometric semisimplicity; BBD intermediate extension | After constructing the signed image and the original nonlinear torus maps, obtain the pure torus product and its `TorusIC` property. |
| Trace under tensor product, dual and Tate twist | Match every factor, using `H^dual(-1)` for conjugation of a weight-one factor, and recover `expectedTrace` for every extension, with one sign per factor. |

The existing detailed source checks for these inputs are in
`support_and_weights_audit.md`, `local_monodromy_audit.md`, and
`../geometry/relative_core_lissity.md`. The last identifies the relevant
Katz, Laumon and Deligne locators and explains the whole-torus argument.

This trace/rank adapter would discharge meaningful arithmetic consequences
without proving the whole sheaf realization. In particular it supplies no
local-Fourier exhaustion, no realization of the rectangle phase list, and no
Type III Fourier bound. Those must not be relabeled as published general
theorems.

## Implemented bounded adapter

The proposed linear-algebra step was subsequently implemented, with the
owner's authorization, in `formal/TypeIIIPublishedParabolicTrace.lean`.
It strictly compiled with all 26 explicit/generated declaration probes
using only standard axioms. Source SHA256:
`bf9bf10186bf2b0c9e4aae48c70a221ffa18b94a66626251cfca261fd8053581`.
Log SHA256:
`4152e0a68d809f1a26c45f054d4ed09a679134f4f29480f995d6150edd329e74`.

`PublishedParabolicTrace.trace_add_of_short_exact` proves the generic trace
additivity rather than accepting it as a premise. Its proof derives linear
splittings over a field and uses cyclicity of trace; it does not require a
Frobenius-stable complement. `JordanBoundaryData.finrank_eq_six`, `.trace_eq`,
and `.signed_trace_eq` apply this to the existing Jordan model. Target finite
dimensionality follows from the supplied quotient map. The endpoints
`signed_correlation_trace` and `signed_kernel_trace` retain the original
finite-field definitions and extension-degree sign. Identification with the
actual geometric cohomology sequence, its compact rank/trace formula and its
boundary Frobenius model remain explicit application data.
