# Self-contained two-step Eulerian interlacing lemma

## Statement
For every n>=3, (1+x) A_(n-2)(x) weakly interlaces A_n(x).
When n is odd, interlacing is strict. When n is even, the only equality
in the ordered zero pattern is at x=-1: (1+x) A_(n-2) has a double zero
there and A_n has a simple zero there; all other inequalities are strict.
Equivalently, the zeros of A_(n-2) and A_n strictly alternate separately
on (-infinity,-1) and (-1,0), with A_n contributing one additional zero
on each side.

This is also Corollary 1 of Shi-Mei Ma, The Eulerian Combinations,
preprint, August 2026 (author-uploaded full text):
https://www.researchgate.net/publication/413485066_THE_EULERIAN_COMBINATIONS

The proof below rederives the specialized assertion directly, rather
than relying on the full two-operator theorem in that paper.

## Inputs
Use the classical Eulerian facts, which follow inductively from the
Eulerian recurrence by signs at roots: A_j is monic, reciprocal of degree
j-1, and has j-1 simple roots in (-infinity,0) for j>=2. Define

C_j(z)=(1+z)^(j-1) A_j((z-1)/(z+1)).

Then C_j has degree j-1, leading coefficient j!>0, parity j-1, and all
its roots simple in (-1,1). In particular its zero at 0 occurs exactly
when j is even, and is simple. The recurrence becomes

C_(j+1) = ((z^2-1) C_j)' = (z^2-1) C_j' + 2z C_j.

## Positive squared-variable residues
Set F_n=(z^2-1) C_(n-2), so

F_n'=C_(n-1),
F_(n+1)=(z^2-1)F_n',
C_(n+1)=(z^2-1)C_n'+2z C_n.

Both F_n and C_n have degree n-1 and the same parity. All zeros of F_n
are simple, lie in [-1,1], and include the endpoints. We prove by
induction that, after canceling the common zero at z=0 when present,

C_n(z)/F_n(z) = rho_n + sum_j lambda_j/(z^2-a_j),

where rho_n>0, every lambda_j>0, and the a_j are exactly the squares of
the positive roots of F_n, so 0<a_j<=1.

For n=3, F_3=z^2-1, C_3=6z^2-2, and the ratio is
6+4/(z^2-1).

Suppose the assertion holds at n and write R=C_n/F_n. Consider a positive
zero xi in (0,1) of F_n'. It is a simple critical point of the real-rooted
polynomial F_n, and F_n(xi)!=0. Therefore

F_n''(xi)/F_n(xi) = -sum_{s:F_n(s)=0} 1/(xi-s)^2 <0.

By differentiation of the recurrence,

F_(n+1)'(xi)/F_n(xi) = (xi^2-1)F_n''(xi)/F_n(xi)>0.

On the other hand, because F_n'(xi)=0,

C_(n+1)(xi)/F_n(xi)
 = (xi^2-1)R'(xi)+2xi R(xi)
 = 2xi [rho_n + sum_j lambda_j(1-a_j)/(xi^2-a_j)^2]>0.

It follows that the ordinary residue of C_(n+1)/F_(n+1) at xi is
positive. Its residue as a rational function of z^2 is 2xi times the
ordinary residue, and is also positive.

The endpoint xi=1 is handled directly:

C_(n+1)(1)=2 C_n(1)>0,
F_(n+1)'(1)=2 F_n'(1)>0.

Thus its residue is positive too. Parity handles the negative poles. If
there is a common zero at 0, it is simple in both numerator and
denominator and cancels. This lists every pole. The ratio is even and
its numerator and denominator have the same degree and positive leading
coefficients, so its polynomial part is a positive constant. The partial
fraction decomposition consequently has exactly the claimed form at
n+1. This completes the induction.

## Extracting the zero order
List the squared poles increasingly as 0<a_1<...<a_k=1. As a function of
t=z^2, the rational function is strictly decreasing on every interval
avoiding its poles, since its derivative is -sum_j lambda_j/(t-a_j)^2.
There is one numerator zero between each pair of poles, and none above
a_k. The remaining numerator zero lies below a_1; because C_n already
has all simple real zeros in (-1,1), this remaining squared zero is
strictly positive (the parity zero at 0 has been removed).
Hence, writing b_j for the squared positive zeros of C_n,

0<b_1<a_1<b_2<a_2<...<b_k<a_k=1.

The poles a_1,...,a_(k-1) are precisely the squared positive zeros of
C_(n-2). Reflection through 0 and the parity zero now give the stated
interlacing of z C_(n-2) with C_n. The Cayley map x=(z-1)/(z+1) is strictly
increasing on (-1,1), and z=0 corresponds to x=-1. Returning to x gives
the desired lemma, including the double/simple central zero when n is
even.

## Application: a complete all-degree strip
For n>=4 and 0<=c<=n-1, let

K_c=A_n-c x A_(n-2), g=A_(n-1), H=(1+x)A_(n-2).

The positive-sum identity in the main proof shows g strictly interlaces
K_c: at a zero r<0 of g, putting f=A_(n-2),

-A_n(r)/f(r)=(-r)J(r),
J(r)=2+sum_{a>0:A_(n-2)(-a)=0}(1+a)(a+r^2)/(r+a)^2>n-1.

Each term is >1 because
(1+a)(a+r^2)-(r+a)^2=a(r-1)^2>0.
Thus K_c has the same signs as A_n at all g roots, and sign counting
proves the assertion (including simplicity of K_c).

The two-step lemma then shows H weakly interlaces K_c as follows.
For odd n, H has simple roots, namely the A_(n-2) roots and -1.
At each former root K_c=A_n. At -1, the preceding J bound applies because
A_(n-1)(-1)=0, and ensures K_c(-1)/A_n(-1)>0. Thus the signs at all roots
of H agree with those of A_n, proving strict interlacing.

For even n, factor out x+1 from K_c and H. The quotient H/(x+1) has only
simple roots. At roots other than -1, its sign test is unchanged. At -1,

[K_c/(x+1)](-1)=A_n'(-1)+c A_(n-2)'(-1).

The Eulerian recurrence at -1 gives A_(j+1)(-1)=-2 A_j'(-1) for even j.
Consequently,

-A_n'(-1)/A_(n-2)'(-1)
 =-A_(n+1)(-1)/A_(n-1)(-1)>n,

where the final inequality is the same J bound at the zero -1 of A_n.
So the signs agree also at -1. Sign counting proves strict interlacing
of the quotients, and multiplying back by x+1 proves weak interlacing of
H with K_c.

Since both g and H interlace K_c and have positive leading coefficients,
every nonnegative combination b g+c H interlaces K_c. Hence

K_c+b g+c H = A_n+b A_(n-1)+c A_(n-2)

is real-rooted for all b>=0 and 0<=c<=n-1, n>=4.
For n=3 the direct discriminant covers every b>=0 and 0<=c<=3.
Thus the uniform strip b>=0, 0<=c<=3 is proved.
