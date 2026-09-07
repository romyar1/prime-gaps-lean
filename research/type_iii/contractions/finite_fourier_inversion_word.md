# A Fourier--inversion word linking the actual correlation to rank four

This is an exact operator relation, including the unit-boundary
corrections. It does not yet recouple the fixed-index four-cycle. The
obstruction to using it there is described explicitly in Section 4.

Let \(G=\mathbf F_p^\times\), \(N=p-1\), and use the actual normalized
\(f=\mathrm{kl}_3\), actual \(C_t(A,B)=\operatorname{correlation}(A,B,t)\),
and raw \(S_2\) from the adjacent notes. Matrices are indexed by \(G\).
Let \(J\) be the all-ones matrix. A partial permutation matrix for a
map \(g\) has entry \(1\) in row \(x\), column \(g(x)\), whenever both
points lie in its specified unit domain.

## 1. Finite Fourier and inversion operators

Put

\[
 M_{A,h}=\psi(Ah),\qquad
 I_{x,y}=\mathbf1_{y=x^{-1}},\qquad
 K=MIM.
 \tag{1}
\]

Changing the intermediate unit variable gives

\[
 K(A,B)=S_2(AB),\qquad
 H_{A,h}=f(Ah)=p^{-1}(MIMIM)_{A,h}.
 \tag{2}
\]

Thus \(C_t=H D_tH^*\), where \(D_t(h,h)=\psi(th)\), is exactly the
correlation in the Lean source.

The elementary first and second rank-two moments give

\[
 KJ=JK=J,\qquad K^2=p^2I-(p+1)J.
 \tag{3}
\]

Consequently the corrected rank-two transform

\[
 T=\frac{K+J}{p},\qquad
 T(A,B)=\frac{S_2(AB)+1}{p}
 \tag{4}
\]

is real, symmetric, and exactly involutive:

\[
 T^2=I,\qquad T\mathbf1=\mathbf1.
 \tag{5}
\]

It also has a direct full-field realization. Let
\(\mathcal F_{x,y}=p^{-1/2}\psi(xy)\) on \(\mathbf F_p\), and let
\(\mathcal I\) be inversion with \(0\) fixed. Then
\(\mathcal F\mathcal I\mathcal F\) fixes the coordinate \(0\), has
zero cross entries between \(0\) and \(G\), and has unit block \(T\).
The plus-one correction in (4) is therefore essential.

## 2. Actual \(C_t\), its correction, and the rank-four operator

For \(t\ne0\), let \(L_t\) be the partial Möbius permutation

\[
 x\longmapsto\frac{x}{1+tx},
 \qquad x\in G\setminus\{-1/t\}.
 \tag{6}
\]

Its image is \(G\setminus\{1/t\}\). Since
\((M D_t M^*)_{x,y}=p\mathbf1_{y=x+t}-1\), equations (1)--(2)
give the exact factorization

\[
 C_t=p^{-1}K L_tK-p^{-2}J.
 \tag{7}
\]

This is the operator form of the previously known two-rank-two
expression for the correlation.

Define \(u_x=T e_x\) and \(B_t=T L_tT\). Expanding \(K=pT-J\)
in (7), and retaining both omitted unit points, gives

\[
 \boxed{\;
 C_t=pB_t+u_{-1/t}\mathbf1^*
             +\mathbf1u_{1/t}^*
             -(1+p^{-1})^2J .
 \;}
 \tag{8}
\]

For example, \(L_t\mathbf1=\mathbf1-e_{-1/t}\) and
\(\mathbf1^*L_t=\mathbf1^*-e_{1/t}^*\), which determine the signs
in this correction.

Now define the orthogonal involution \(R=TIT\). Multiplicative
convolution of two raw rank-two sums gives

\[
 (KIK)(A,B)=
 \sum_{x\in G}S_2(Ax)S_2(B/x)=S_4(AB),
 \tag{9}
\]

where

\[
 S_4(c)=\sum_{u,v,w\in G}
            \psi\left(u+v+w+\frac{c}{uvw}\right).
 \tag{10}
\]

This is exactly the raw sum named
incidenceKloosterman4Raw in
[IncidenceRankFour.lean](../../../formal/IncidenceRankFour.lean#L23).
Equations (3)--(4) give

\[
 \boxed{\;
 R(A,B)=\frac{S_4(AB)+p+1}{p^2},\qquad R^2=I.
 \;}
 \tag{11}
\]

Thus the existing scalar rank-four input implies
\[
 |R(A,B)|\le4p^{-1/2}+p^{-1}+p^{-2}.
 \tag{12}
\]

## 3. An exact three-operator contraction

Let \(s\ne0\) and \(t=-1/s\). With the row-to-column convention above,
the partial permutation word \(L_s I L_t\) is exactly

\[
 x\longmapsto-s^2x-s,\qquad x\in G\setminus\{-1/s\}.
 \tag{13}
\]

Indeed,

\[
 \frac{x}{1+sx}
 \longmapsto\frac1x+s
 \longmapsto
 \frac{1+sx}{t+(1+st)x}
 =-s^2x-s.
 \tag{14}
\]

The second \(L_t\) introduces no additional excluded unit point:
the equation \(1/x+s=-1/t=s\) has no unit solution.

Using \(T^2=I\) twice,
\(B_s R B_{-1/s}=T(L_s I L_{-1/s})T\). Its entries evaluate as

\[
 \boxed{\;
 (B_s R B_{-1/s})(A,B)
      =\frac{S_2(-A/s-sB)+1}{p}.
 \;}
 \tag{15}
\]

For a direct check of the last evaluation, the general additive
orthogonality identity, for \(A,D,t\ne0\), is

\[
 \sum_{\substack{x\in G\\x\ne-t}}
       S_2(Ax)S_2(D(x+t))
 =pS_2(-t(A-D))+S_2(Dt)+S_2(-At).
 \tag{16}
\]

To prove it, first sum over all \(x\in\mathbf F_p\); the two
Kloosterman variables satisfy \(A/u+D/v=0\), leaving
\(pS_2(-t(A-D))\). Then subtract \(x=0,-t\), using \(S_2(0)=-1\).
The case \(A=D\) gives the same formula since \(t\ne0\).

In the product of the two numerators \(S_2+1\) in (4), take
\(D=-s^2B,t=1/s\). The two single-\(S_2\) sums cancel the boundary
terms in (16), while the constant and first-moment terms total \(p\).
Division by \(p^2\) proves (15).

The right side vanishes when \(A+s^2B=0\). Elsewhere the existing
scalar rank-two bound gives \(2p^{-1/2}+p^{-1}\). This is an
entrywise evaluation of a composed operator, not merely a bound
obtained from its operator norm.

## 4. The fixed four-cycle retains a different tensor constraint

At the unweighted origin define

\[
 \Delta e_B=e_B\otimes e_B,\qquad
 J_a e_A=e_A\otimes e_{aA}.
 \tag{17}
\]

The actual row-pair product matrix is exactly

\[
 P_a=J_a^*(C\otimes\overline C)\Delta,\qquad
 P_a(A,B)=C(A,B)\overline{C(aA,B)}.
 \tag{18}
\]

Its fixed column-ratio autocorrelation contracts \(P_a(A,B)\)
against \(\overline{P_a(A,bB)}\), keeping both tensor-diagonal
constraints. Equation (15), by contrast, requires an \(R\) operator
between two ordinary matrix factors.

Inserting \(R\otimes\overline R\) around the column constraint is
an exact operation, but it transforms that constraint into the
tensor with entries

\[
 \sum_{B\in G}
 R(u,B)\overline{R(v,B)}\,
 \overline{R(u',bB)}R(v',bB).
 \tag{19}
\]

This is a four-factor rank-four correlation. Neither the scalar
bound (12) nor the two-rank-two baseline bound evaluates it. The
scalar estimate bounds each summand, but the remaining sums lose
the proposed square-root saving.

Physical inversion is a permutation and preserves the type of the
embeddings in (17), changing \(a\) to \(a^{-1}\). The conjugated
operator \(R=TIT\) is dense and does not preserve those embeddings.
Changing to the \(T\) basis moves the same obstruction into the
transformed diagonal projectors. Thus the simple permutation word
(14) cannot currently be inserted into (18) with the original
constraints unchanged.

The physical Fourier fiber weight from
[centered_fourier_reduction.md](centered_fourier_reduction.md)
adds another dependence on \(A,B\). It does not resolve this
obstruction, which already occurs at the bijective-cube origin.
No local Fourier hypothesis follows from (15) here.

## 5. Selected exact verification

[fourier_inversion_word_exact.py](fourier_inversion_word_exact.py)
checks \(p=5,7\), \(s=2\), and every unit pair \(A,B\) at each of
those two primes. It verifies (5), the actual original-definition
correlation in (8), the raw rank-four normalization (11), and the
word evaluation (15). Every equality passed in integer cyclotomic
arithmetic. The cases have 16 and 36 matrix entries, respectively.

The record is
[fourier_inversion_word_exact.json](fourier_inversion_word_exact.json).
From the repository root:

    python3 research/type_iii/contractions/fourier_inversion_word_exact.py

These checks validate the displayed finite identities at the stated
primes. The general derivations are given above; no numerical or
formal claim about four-cycle Fourier cancellation is made.
