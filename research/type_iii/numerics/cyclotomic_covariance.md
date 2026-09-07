# Exact cyclotomic covariance and the Type III origin

This note concerns precisely the finite sums in
[`TypeIIILocal.lean`](../../../formal/TypeIIILocal.lean). The arguments below
are mathematical derivations; the [formalization map](../../../docs/type-iii.md)
records the corresponding checked components. They use no character-sum
estimate. The separate numerical receipts do not enter these arguments.

Let \(p\) be a prime, put \(\zeta=\exp(2\pi i/p)\), and write

\[
\psi(t)=\zeta^t,\qquad L=\mathbf Q(\zeta),\qquad
\mathcal R=\mathbf Z[\zeta].
\]

Every occurrence of an exponent or division inside \(\psi\) is interpreted
in \(\mathbf F_p\). An automorphism \(\sigma_a\), for
\(a\in\mathbf F_p^\times\), is characterized by
\(\sigma_a(\zeta)=\zeta^a\). These are all automorphisms of \(L/\mathbf Q\).
Complex conjugation is \(\sigma_{-1}\), and therefore commutes with every
\(\sigma_a\).

The normalizations are

\[
\operatorname{Kl}_3(t)=p^{-1}\sum_{u,v\ne0}
 \psi\!\left(u+v+\frac{t}{uv}\right),
\qquad
C(A,B,c)=\sum_{h\ne0}\operatorname{Kl}_3(Ah)
 \overline{\operatorname{Kl}_3(Bh)}\psi(ch).
\]

For nonzero \(\alpha,m,n\), let

\[
K_{\alpha;m,n}(r_1,r_2)=
C\!\left(\frac{\alpha r_2}{mr_1^2},
         \frac{\alpha r_1}{nr_2^2},1\right)
\]

on the torus, with value zero on either coordinate axis. The four-cycle is

\[
W(r)=K_{\alpha;m,n}(r)\,
 \overline{K_{\alpha;m',n}(r)}\,
 K_{\alpha;m',n'}(r)\,
 \overline{K_{\alpha;m,n'}(r)},
\]

and the positive, unnormalized Fourier transform is

\[
\widehat W(h,k)=\sum_{r_1,r_2\in\mathbf F_p}
 W(r_1,r_2)\psi(hr_1+kr_2).
\]

## 1. Covariance of the Kloosterman sum

Applying \(\sigma_a\) gives

\[
\begin{aligned}
\sigma_a(\operatorname{Kl}_3(t))
 &=p^{-1}\sum_{u,v\ne0}
   \psi\!\left(au+av+\frac{at}{uv}\right)\\
 &=p^{-1}\sum_{u',v'\ne0}
   \psi\!\left(u'+v'+\frac{a^3t}{u'v'}\right)\\
 &=\operatorname{Kl}_3(a^3t).
\end{aligned}
\]

The middle equality uses \(u'=au\), \(v'=av\), so
\(uv=a^{-2}u'v'\). In particular,
\(\overline{\operatorname{Kl}_3(t)}=\operatorname{Kl}_3(-t)\).

## 2. Covariance and reality of the correlation

Because \(\sigma_a\) commutes with complex conjugation,

\[
\begin{aligned}
\sigma_a(C(A,B,c))
 &=\sum_{h\ne0}\operatorname{Kl}_3(a^3Ah)
     \overline{\operatorname{Kl}_3(a^3Bh)}\psi(ach)\\
 &=\sum_{x\ne0}\operatorname{Kl}_3(a^2Ax)
     \overline{\operatorname{Kl}_3(a^2Bx)}\psi(cx)\\
 &=C(a^2A,a^2B,c).
\end{aligned}
\]

Here \(x=ah\). Thus the third parameter is unchanged after the change of
variable; the first two parameters acquire \(a^2\), not \(a^3\).

Taking \(a=-1\) proves \(\overline{C(A,B,c)}=C(A,B,c)\): every correlation
is real, with no nonzero condition needed on \(A,B,c\). Equivalently,
conjugate its defining sum and replace \(h\) by \(-h\), using
\(\overline{\operatorname{Kl}_3(t)}=\operatorname{Kl}_3(-t)\).

## 3. Covariance of the actual physical kernel and Fourier transform

At a torus point,

\[
\begin{aligned}
\sigma_a(K_{\alpha;m,n}(r_1,r_2))
 &=K_{a^2\alpha;m,n}(r_1,r_2)\\
 &=K_{\alpha;m,n}(a^{-2}r_1,a^{-2}r_2).
\end{aligned}
\]

For example,

\[
\frac{\alpha(a^{-2}r_2)}{m(a^{-2}r_1)^2}
 =a^2\frac{\alpha r_2}{mr_1^2}.
\]

The corresponding identity for the other correlation parameter is identical.
Multiplication by \(a^{-2}\) preserves each coordinate axis, so the equality
also holds for the kernel extended by zero. Applying it to the four factors,
including the conjugated factors, yields

\[
\sigma_a(W(r_1,r_2))=W(a^{-2}r_1,a^{-2}r_2).
\]

Consequently,

\[
\begin{aligned}
\sigma_a(\widehat W(h,k))
 &=\sum_{r_1,r_2}W(a^{-2}r_1,a^{-2}r_2)
      \psi\bigl(a(hr_1+kr_2)\bigr)\\
 &=\sum_{s_1,s_2}W(s_1,s_2)
      \psi\bigl(a^3(hs_1+ks_2)\bigr)\\
 &=\widehat W(a^3h,a^3k).
\end{aligned}
\tag{1}
\]

The second equality uses \(r_i=a^2s_i\). The parameters
\(\alpha,m,m',n,n'\) are unchanged in (1). This proves, in particular,

\[
\widehat W(0,0)\in\mathbf Q.
\tag{2}
\]

Neither index distinctness nor index repetition is needed for (1) or (2).
When \(p\equiv2\pmod3\), the values at all nonzero scalar multiples of a
frequency lie in one Galois orbit, with possible stabilizers. When
\(p\equiv1\pmod3\), the scalar multiples split into at most three such
orbits. This says nothing by itself about the size of an individual conjugate.

## 4. The reduced denominator of the origin is exactly \(p^8\)

Define the algebraic integer

\[
S(A,B,c)=
\sum_{\substack{u,v,x,y\ne0\\A/(uv)-B/(xy)+c=0}}
 \psi(u+v-x-y)\in\mathcal R.
\]

Expanding the two Kloosterman sums inside the correlation, the sum over the
unit variable is

\[
\sum_{h\ne0}\psi(hT)=p\,1_{T=0}-1.
\]

The term with \(-1\) factors into four unit sums. Since
\(\sum_{u\ne0}\psi(u)=\sum_{u\ne0}\psi(-u)=-1\), their product is one.
Therefore the following identity is exact:

\[
C(A,B,c)=p^{-1}S(A,B,c)-p^{-2},
\qquad p^2C(A,B,c)=pS(A,B,c)-1.
\tag{3}
\]

For every point on the physical torus, multiplying the four identities (3),
with the required conjugations, shows

\[
p^8W(r_1,r_2)\in\mathcal R,\qquad
p^8W(r_1,r_2)\equiv1\pmod{p\mathcal R}.
\]

There are \((p-1)^2\) torus points and the axes contribute zero. Thus

\[
N:=p^8\widehat W(0,0)\in\mathcal R,\qquad
N\equiv(p-1)^2\pmod{p\mathcal R}.
\tag{4}
\]

By (2), \(N\) is rational. Every element of \(\mathcal R\) is an algebraic
integer, and a rational algebraic integer is an integer. Hence \(N\in\mathbf Z\).
Furthermore, \((N-(p-1)^2)/p\) is both rational and in \(\mathcal R\), so it
is an integer. Equation (4) therefore implies the ordinary congruence

\[
N\equiv1\pmod p.
\]

It follows that

\[
\boxed{\displaystyle
\widehat W(0,0)=\frac{N}{p^8},\quad N\in\mathbf Z,\quad N\equiv1\pmod p.}
\tag{5}
\]

Thus this fraction has reduced denominator exactly \(p^8\), and the origin
coefficient never vanishes. This conclusion holds in both branches of the
Type III statement. It supplies no useful upper bound for \(|N|\).

The script [`exact_origin_check.py`](exact_origin_check.py) independently
evaluates (3) in the integral group ring for the listed small primes. It
checks that the accumulated polynomial for \(N\) has the same coefficient at
each nonzero power of \(\zeta\); subtracting that common coefficient from the
constant coefficient gives its integer value. For example, at
\(p=7,\alpha=m=n=1,m'=n'=-1\), it gives

\[
\widehat W(0,0)=-\frac{9\,133\,198\,500}{5\,764\,801},
\qquad 5\,764\,801=7^8.
\]

These computations are checks of the identities, not premises in their proof.

### Every frequency is nonzero and has the same integrality denominator

The pointwise congruence above gives a stronger statement before specializing
to the origin. For every \((h,k)\),

\[
\begin{aligned}
p^8\widehat W(h,k)
 &\equiv \sum_{r_1,r_2\ne0}\psi(hr_1+kr_2)\\
 &=\bigl(p\,1_{h=0}-1\bigr)\bigl(p\,1_{k=0}-1\bigr)\\
 &\equiv1\pmod{p\mathcal R}.
\end{aligned}
\tag{6}
\]

Moreover \(p^8\widehat W(h,k)\in\mathcal R\). Write it as \(1+pT\), with
\(T\in\mathcal R\). It cannot be zero, because \(-1/p\) is not an algebraic
integer. Also

\[
p^7\widehat W(h,k)=\frac1p+T
\]

is not an algebraic integer: otherwise subtracting the algebraic integer
\(T\) would make \(1/p\) an algebraic integer. Therefore **every Fourier
coefficient is nonzero**, and eight is the least nonnegative exponent
\(e\) for which \(p^e\widehat W(h,k)\) is an algebraic integer. Indeed,
integrality with \(e<7\) would imply integrality with \(e=7\) by
multiplication by an integer. No identification of the full ring of
integers of \(L\) with \(\mathcal R\) is needed for this argument.

This uses algebraic integrality, not ordinary rational denominators at
nonzero frequencies. The rational denominator statement (5) remains the
special conclusion at the origin.

## 5. Reduction of all residue parameters to ratios and cube classes

Put \(R=m'/m\) and \(T=n'/n\). Choose \(a\ne0\), and set

\[
b=\frac{ma^2}{\alpha},\qquad
\eta=\frac{nm^2a^3}{\alpha^3}.
\]

Direct substitution gives

\[
K_{\alpha;m,n}(ax,by)=K_{1;1,\eta}(x,y).
\]

Indeed the two correlation arguments on the left are
\(y/x^2\) and \(x/(\eta y^2)\). The same calculation for the other three
factors yields

\[
W_{\alpha;m,m';n,n'}(ax,by)
 =W_{1;1,R;\eta,T\eta}(x,y),
\]

and therefore

\[
\widehat W_{\alpha;m,m';n,n'}(h,k)
 =\widehat W_{1;1,R;\eta,T\eta}(ah,bk).
\tag{7}
\]

The frequency change is a bijection. As \(a\) varies, \(\eta\) runs over the
cube class of \(nm^2\). If \(g\) generates \(\mathbf F_p^\times\), it suffices
to take \(\eta=g^c\) with
\(0\le c<\gcd(3,p-1)\). Distinctness of both pairs is exactly
\(R\ne1\) and \(T\ne1\).

Thus an exhaustive computation over those cube classes, all
\(R,T\in\mathbf F_p^\times\setminus\{1\}\), and all \((h,k)\), covers all
the nonzero residue parameters in the distinct-index branch at that fixed
prime. The numerical receipts state exactly which listed primes receive
this exhaustive treatment.

## What remains

Equations (1)--(7) do not give the uniform \(O(p^3)\) Fourier bound, its
bounded finite exceptional set, or the repeated-index exceptional-curve
bound. The cyclotomic orbit relation alone is not a norm estimate. In
particular, rationality and denominator control of the origin do not rule
out a term of order \(p^4\). Proving the required cancellation remains a
separate mathematical task.
