# Mellin energy of the centered origin

The diagonal terms in the Gauss expansion of the Mellin energy are
exactly constant over all nontrivial characters. Their contribution to
the centered origin is \(O(p^3)\) when the fixed column ratio is
different from one. The full energy also contains off-diagonal phase
terms; the formulas below isolate them, but do not bound their
contribution by \(O(p^3)\).

Throughout, \(G=\mathbf F_p^\times\), \(N=p-1\), and \(\widehat G\)
is its group of unitary multiplicative characters. The trivial
character is denoted by \(1\). All multiplicative transforms here use
the unnormalized convention

\[
 \mathcal M g(\chi)=\sum_{x\in G}g(x)\overline{\chi(x)}.
 \tag{1}
\]

Write \(C(A,B)=\operatorname{correlation}(A,B,1)\),
\(a,b\in G\setminus\{1\}\), and

\[
 P_A(B)=C(A,B)\overline{C(aA,B)},\qquad
 Q_A(B)=P_A(B)-N^{-1}\sum_{D\in G}P_A(D).
 \tag{2}
\]

The object studied in this note is

\[
 S(a,b)=\sum_{A,B\in G}Q_A(B)\overline{Q_A(bB)}.
 \tag{3}
\]

It is the centered actual origin when \(\gcd(3,p-1)=1\). The actual
cubic fiber weights when \(\gcd(3,p-1)=3\), and all nonzero physical
Fourier frequencies, require the weight retained in
[centered_fourier_reduction.md](centered_fourier_reduction.md).
They are not silently discarded in the interpretation of this note.

## 1. Energy identity with both fixed ratios retained

For \(\chi\ne1\), centering changes no Mellin coefficient. Define

\[
 M_{a,A}(\chi)=\sum_{B\in G}
       C(A,B)\overline{C(aA,B)}\,\overline{\chi(B)},\qquad
 E_a(\chi)=\sum_{A\in G}|M_{a,A}(\chi)|^2.
 \tag{4}
\]

Multiplicative Fourier inversion and orthogonality give

\[
 \boxed{\;
 S(a,b)=\frac1N\sum_{\substack{\chi\in\widehat G\\\chi\ne1}}
                \overline{\chi(b)}E_a(\chi).
 \;}
 \tag{5}
\]

To check the sign, use
\(Q_A(B)=N^{-1}\sum_\chi\mathcal M Q_A(\chi)\chi(B)\).
The conjugate of \(Q_A(bB)\) contributes
\(\overline{\chi(b)}\). The term \(\chi=1\) vanishes because \(Q_A\)
has mean zero. There is no average over the fixed row ratio \(a\) in
(4)--(5).

## 2. Exact Gauss expansion

Let

\[
 \tau(\rho)=\sum_{x\in G}\rho(x)\psi(x),\qquad
 F_\rho=\mathcal M f(\rho)
       =p^{-1}\tau(\overline\rho)^3,\qquad f=\mathrm{kl}_3.
 \tag{6}
\]

The last equality follows immediately from the two-unit definition of
\(f\): in its Mellin transform, put \(t=uvw\), and the three unit
sums separate. It includes the trivial character:
\(F_1=-p^{-1}\).

Expanding the two copies of \(f\) in the actual correlation gives

\[
 C(A,B)=\frac1{N^2}\sum_{\rho,\sigma\in\widehat G}
 F_\rho\overline{F_\sigma}\,
 \tau(\rho\overline\sigma)\rho(A)\overline{\sigma(B)}.
 \tag{7}
\]

For clarity, define the following term with every conjugation present:

\[
 \begin{aligned}
 T_{a,\chi}(\eta;\rho,\sigma)
 ={}&
 F_{\eta\rho}\overline{F_\rho}\,
 \overline{F_\sigma}F_{\chi\sigma}\\
 &{}\times\tau(\eta\rho\overline\sigma)\,
          \overline{\tau(\rho\overline\chi\,\overline\sigma)}\,
          \overline{\rho(a)}.
 \end{aligned}
 \tag{8}
\]

Put

\[
 Z_{a,\chi}(\eta)=\sum_{\rho,\sigma\in\widehat G}
                             T_{a,\chi}(\eta;\rho,\sigma).
 \tag{9}
\]

Substituting (7) into (4), the \(B\)-sum forces the second column
character to equal \(\chi\sigma\); then setting the first row
character equal to \(\eta\rho\) gives

\[
 M_{a,A}(\chi)=N^{-3}\sum_{\eta\in\widehat G}
                               Z_{a,\chi}(\eta)\eta(A).
 \tag{10}
\]

Consequently,

\[
 \boxed{\;
 E_a(\chi)=N^{-5}\sum_{\eta\in\widehat G}
                                      |Z_{a,\chi}(\eta)|^2.
 \;}
 \tag{11}
\]

Equations (8)--(11) are exact. In particular, a modulus cannot be
passed through the \((\rho,\sigma)\)-sum without retaining its
off-diagonal terms.

## 3. The part determined by Gauss magnitudes

The elementary exact Gauss identities are

\[
 |\tau(\theta)|^2=
 \begin{cases}1,&\theta=1,\\p,&\theta\ne1,\end{cases}
 \qquad
 |F_\theta|^2=
 \begin{cases}p^{-2},&\theta=1,\\p,&\theta\ne1.\end{cases}
 \tag{12}
\]

For example, the nontrivial Gauss identity follows by setting \(x=ry\)
in \(|\tau(\theta)|^2\) and applying
\(\sum_{y\in G}\psi((r-1)y)=p\mathbf1_{r=1}-1\).
Thus (12) is an orthogonality calculation, not a Weil estimate.

Expand the square in (11). The terms with identical
\((\rho,\sigma)\) on its two sides contribute

\[
 D_p(\chi)=N^{-5}\sum_{\eta,\rho,\sigma}
                  |T_{a,\chi}(\eta;\rho,\sigma)|^2.
 \tag{13}
\]

This expression is independent of \(a\). It is also independent of
every nontrivial \(\chi\), with the following exact value:

\[
 \boxed{\;
 D_p=\frac{(p-3)B_p^2+2A_pB_p}{(p-1)^5},\qquad
 A_p=p-2+p^{-4},\qquad
 B_p=p^4-3p^3+p^2+1 .
 \;}
 \tag{14}
\]

Here and below (14) is used only when a nontrivial character exists.
To verify it, let

\[
 s(\theta)=|F_\theta|^2,\quad
 t(\theta)=|\tau(\theta)|^2,\quad
 L(y)=\sum_{z\in\widehat G}s(z)t(z\overline y).
 \tag{15}
\]

In the summand of (13), make the change
\(x=\rho,\ y=\sigma,\ z=\eta\rho\). The \(x,z\) sums separate,
and (13) becomes

\[
 N^{-5}\sum_{y\in\widehat G}
                     s(y)L(y)\,s(\chi y)L(\chi y).
 \tag{16}
\]

By (12),

\[
 L(1)=p^2(p-2)+p^{-2},\qquad
 L(y)=p^3-3p^2+p+p^{-1}\quad(y\ne1).
 \tag{17}
\]

It follows that \(s(y)L(y)\) is \(A_p\) at \(y=1\) and \(B_p\)
otherwise. For \(\chi\ne1\), the two exceptional positions
\(y=1,\chi^{-1}\) are distinct, proving (14).

Thus the diagonal energy is constant over all \(\chi\ne1\).
Since \(b\ne1\),

\[
 \frac1N\sum_{\chi\ne1}\overline{\chi(b)}D_p=-D_p/N.
 \tag{18}
\]

This contribution has the desired order. Indeed, each squared
summand in (13) is at most \(p^6\), so

\[
 0\le D_p/N\le p^6/N^3\le8p^3.
 \tag{19}
\]

Also \(D_p/N=p^3+O(p^2)\) follows directly from (14).

## 4. The interference term that remains

Define the exact off-diagonal energy by

\[
 \begin{aligned}
 O_a(\chi)=N^{-5}\sum_\eta
 \sum_{\substack{(\rho,\sigma),(\rho',\sigma')\\
                        (\rho,\sigma)\ne(\rho',\sigma')}}
 T_{a,\chi}(\eta;\rho,\sigma)\,
        \overline{T_{a,\chi}(\eta;\rho',\sigma')}.
 \end{aligned}
 \tag{20}
\]

Then

\[
 \boxed{\;
 S(a,b)=-\frac{D_p}{N}
    +\frac1N\sum_{\chi\ne1}\overline{\chi(b)}O_a(\chi).
 \;}
 \tag{21}
\]

The first term is completely evaluated and bounded in (14), (19).
The second term is not. Its Gauss phases depend on \(\chi\) and on
the fixed row ratio through
\(\overline{\rho(a)}\rho'(a)\). Knowing the magnitudes in (12)
does not remove these factors.

One sufficient remaining estimate for a uniform \(O(p^3)\) bound at
this unweighted origin is

\[
 \left|\sum_{\chi\ne1}\overline{\chi(b)}O_a(\chi)\right|
       \ll Np^3\qquad(a,b\ne1).
 \tag{22}
\]

Alternatively, a uniform \(O(p^3)\) bound on \(O_a(\chi)\) would
suffice by the triangle inequality, but no such bound has been
proved here. The desired finite-exceptional proposition could allow
a weaker \(O(p^{7/2})\) origin bound if the origin is included among
its exceptional frequencies.

The full energy is not automatically exactly constant. For the
actual correlation at \(p=5,a=2\), exact calculation gives

\[
 E_2(\chi_{\mathrm{quadratic}})=\frac{40366}{625},\qquad
 E_2(\chi_{\mathrm{quartic}})=\frac{89216}{625},
 \tag{23}
\]

where \(\chi_{\mathrm{quartic}}(2)=i\). Its conjugate has the same
energy, since \(P_A\) is real. Both energies have the same diagonal
contribution \(D_5=1503993/10000\).

This finite example shows that the off-diagonal term is nonzero and
can depend on the character. It does not disprove a uniform
near-constancy theorem with controlled errors or a bounded set of
exceptional characters. Such a theorem would be new input, not a
consequence already supplied by (12).

## 5. What does become nearly constant after averaging the row ratio

There is a shorter exact formula if the fixed row ratio is averaged
over all \(a\in G\). This is useful for locating the loss of
information, but it cannot replace the fixed-\(a\) estimate.

Let \(D_{\overline\chi}\) be the diagonal matrix with entries
\(\overline{\chi(B)}\), and set

\[
 X_\chi=C D_{\overline\chi}C^*.
 \tag{24}
\]

Its \((A,aA)\)-entry is \(M_{a,A}(\chi)\). Therefore

\[
 \sum_{a\in G}E_a(\chi)=\|X_\chi\|_{\mathrm{HS}}^2.
 \tag{25}
\]

The column Gram identity is

\[
 C^*C=p^2I-\kappa(pJ+VV^*),\qquad
 V_B=S_2(B)-p^{-1},\qquad
 \|V\|^2=pN-\kappa .
 \tag{26}
\]

For \(\chi\ne1\), define the Jacobi sum

\[
 J_\chi=\sum_{z\in\mathbf F_p}
                 \overline{\chi(z)}\,\overline{\chi(1-z)},
 \tag{27}
\]

with nontrivial characters extended by zero at zero. Elementary
Mellin calculations give

\[
 \mathcal M V(\chi)=\tau(\overline\chi)^2,\qquad
 \mathcal M(V^2)(\chi)
       =\tau(\overline\chi)^2(J_\chi-2/p).
 \tag{28}
\]

For the second identity, expand \(S_2(t)^2\) and take its Mellin
transform. The inner \(t\)-sum is
\(\tau(\overline\chi)\chi(u^{-1}+v^{-1})\); write
\(u=wz,v=w(1-z)\). The remaining \(w\) and \(z\) sums give a second
Gauss sum and \(J_\chi\). Subtracting the \(2S_2/p\) term produces
the correction in (28).

Expanding
\(\operatorname{tr}(D_{\overline\chi}(C^*C)D_\chi(C^*C))\)
with (26), and using (28), now gives

\[
 \boxed{\;
 \sum_{a\in G}E_a(\chi)
 =p^4N-4\kappa p^3N+2\kappa^2p^2
       +\kappa^2\left(2p^3+p^2|J_\chi-2/p|^2\right).
 \;}
 \tag{29}
\]

In detail, the \(J\)-\(J\) cross term vanishes because
\(\sum_B\chi(B)=0\). The two mixed \(J\)-\(VV^*\) terms total
\(2p|\mathcal M V(\chi)|^2=2p^3\). The \(VV^*\)-\(VV^*\) term is
\(|\mathcal M(V^2)(\chi)|^2\).

For \(\chi^2\ne1\),

\[
 J_\chi=\frac{\tau(\overline\chi)^2}{\tau(\overline{\chi}^2)},
 \qquad |J_\chi|=\sqrt p,
 \qquad
 p^2|J_\chi-2/p|^2=p^3+4-4p\,\operatorname{Re}J_\chi.
 \tag{30}
\]

For the one nontrivial quadratic character, when it exists,
\(J_\chi=-\chi(-1)\). Thus (29) is nearly constant across generic
characters: its deviation from a character-independent expression
is at most \(4\kappa^2p^{3/2}\). The only additional case is the
quadratic character.

The exact step that made (29) possible was summing over all \(a\):
the entries \((A,aA)\) then run over the whole matrix and permit its
Hilbert--Schmidt norm to be evaluated from \(C^*C\).
For fixed \(a\), they select only one permutation diagonal. Neither
Gauss magnitudes nor the complete Gram identity determine that
restricted energy. Equation (20) is the remaining phase-sensitive
term at that fixed ratio.

## 6. Exact validation and scope

[centered_mellin_exact.py](centered_mellin_exact.py)
checks all constants and signs in (7), (10), (11), (14), and (29)
in the single \(p=3,a=2,\chi\ne1\) case, using exact integer
cyclotomic vectors. The resulting values are

\[
 E_2(\chi)=98/81,\qquad D_3=205/324,\qquad
 O_2(\chi)=187/324,\qquad
 \sum_{a\in\mathbf F_3^\times}E_a(\chi)=187/81.
 \tag{31}
\]

The same checker records the two fixed \(p=5\) energies in (23).
The quartic calculation uses real and imaginary coefficient vectors;
no approximate complex arithmetic enters it. There is no parameter
scan or claim of an asymptotic bound in this validation.

The receipt is
[centered_mellin_exact.json](centered_mellin_exact.json).
From the repository root:

    python3 research/type_iii/contractions/centered_mellin_exact.py

The symbolic identities apply generally, with the hypotheses stated
above. They isolate an evaluated \(O(p^3)\) term and the remaining
fixed-ratio Mellin interference. They do not prove (22), the
individual centered origin bound, or the full local Fourier
hypothesis.
