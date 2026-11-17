# Independent adversarial review of the full hybrid-sign proof

The `countersearch` agent independently audited the candidate supplied by the
`proof_transform` agent. The review checked the algebra, root counts, sign
orientations, shared roots at zero, endpoint signs, and the limit at b=0.

**Review conclusion:** the full conjecture is proved by the candidate argument,
provided its elementary squared-residue lemma is included. That lemma was also
independently audited below and found valid. No computational certificate is a
dependency of the proof.

## 1. Definitions used in the review

Set

    C_k(z)=(1+z)^(k-1) A_k((z-1)/(z+1)),
    T=(z^2-1)D+2z,

so C_(k+1)=T C_k. For m=n-2>=2 write

    f=C_m, g=C_(m+1), h=C_(m+2),
    alpha=b/2+1>=1,
    Q=g+alpha(1+z)f,
    P=h+b(1+z)g+c(1+z)^2 f.

The conjectured bound is exactly c<=alpha^2+2. The Cayley transform is strictly
increasing from (-1,1) onto (-infinity,0), so proving every root of P lies in
(-1,1) proves the required result in x. Eulerian real-rootedness and ordinary
consecutive interlacing are proved separately from the standard recurrence;
they are not inferred from the new theorem.

## 2. Exact algebraic identity

Direct expansion gives the polynomial identity

    P*f = Q^2 + (1+z)^2(c-alpha^2-2)f^2
          -(1-z^2)[(1-z^2)(f'^2-f f'')-2f f'].

This was independently derived by treating f,f',f'' as independent symbols,
and is checked symbolically in `verify_hybrid_proof.py`. In particular, at a
root r of Q,

    P(r)/f(r)
      = (1+r)^2(c-alpha^2-2) -(1-r^2)E_f(r),

where

    E_f(r)=(1-r^2) sum_j 1/(r-r_j)^2 -2 sum_j 1/(r-r_j),

and r_j are the roots of f. Roots of Q are not roots of f, because f and g
strictly interlace.

For -1<r<0 and symmetric f with simple roots in (-1,1), E_f(r)>0. For a pair
of roots +/-sqrt(a), put w=-r in (0,1), a in (0,1). Apart from the positive
factor 2/(w^2-a)^2, its contribution is

    w^2(1+2w-w^2)+a(1-2w-w^2).

This affine function of a is strictly positive on [0,1]: at a=0 it is
w^2(1+2w-w^2)>0, and at a=1 it is (1-w)^3(1+w)>0. An unpaired root zero
contributes (1-r^2)/r^2-2/r>0. Since m>=2, f has at least one root. Therefore

    P(r)/f(r)<0

at every negative root of Q, including the parameter boundary.

## 3. Audit of the squared-residue lemma

Define F_k=(z^2-1)C_(k-2), k>=3. Then

    F_k'=C_(k-1),
    F_(k+1)=(z^2-1)F_k'.

The induction establishes

    C_k/F_k = rho_k + sum_j lambda_j/(z^2-a_j),

after canceling the common simple zero at zero when present, with rho_k>0,
lambda_j>0, and 0<a_j<=1. The base is

    C_3/F_3=6+4/(z^2-1).

At a positive interior root xi of F_k', F_k(xi)!=0 and

    C_(k+1)(xi)/F_k(xi)
      =2xi[rho_k+sum_j lambda_j(1-a_j)/(xi^2-a_j)^2]>0.

Also

    F_(k+1)'(xi)/F_k(xi)
      =(xi^2-1)F_k''(xi)/F_k(xi)>0,

because at a critical point of the real-rooted polynomial F_k,

    F_k''/F_k=-sum_r 1/(xi-r)^2<0.

Thus the coefficient of 1/(z^2-xi^2) is

    2xi*C_(k+1)(xi)/F_(k+1)'(xi)>0.

The endpoint pole at 1 has positive residue, since C_k(1)>0. Parity handles
the negative poles. When zero is shared, both zeros are simple by ordinary
Eulerian real-rootedness and Rolle interlacing, so cancellation is legitimate.
The leading-coefficient quotient rho_(k+1)>0 completes the partial fractions.

In the squared variable y, the quotient is strictly decreasing between its
poles and has precisely one zero before each successive pole. The independent
ordinary real-rootedness of C_k guarantees that the leftmost squared zero is
positive. There is no circular use of the desired theorem here.

For a positive root r of f=C_m, the positive residue of C_(m+2)/[(z^2-1)C_m]
is

    2r*h(r)/[(r^2-1)f'(r)] = 2r*h(r)/g(r)>0.

Consequently h(r)/g(r)>0. Since b>=0 and 1+r>0,

    sign P(r)=sign g(r)

at every positive root of f. The term involving c vanishes there.

## 4. Testpoint count and sign audit

Q has simple roots in (-1,1) and strictly interlaces f. This follows from
ordinary Eulerian interlacing applied to A_(m+1)+alpha A_m and the Cayley map.

### f even, degree 2p

Q has p+1 negative roots and p positive roots. The central root is negative:
as alpha increases from zero, each root of A_(m+1)+alpha A_m moves left,
because (A_(m+1)/A_m)'>0 between its poles. All other root counts follow from
strict interlacing.

Use, in increasing order, the p+1 negative Q roots and then the p positive
f roots. There are 2p+1=deg(P)-1 points. The negative Q points have P signs

    -, +, -, ... , (-1)^(p+1).

The positive f points have signs

    (-1)^p, (-1)^(p-1), ... , -.

The junction signs are opposite. Both endpoint signs P(-1),P(1) are positive.
Thus there are exactly deg(P)=2p+2 disjoint sign-change intervals within
(-1,1), proving simple real roots.

### f odd, degree 2p+1, b>0

Q has p+1 negative and p+1 positive roots. Use its negative roots, then zero,
then the p positive roots of f. There are 2p+2=deg(P)-1 points. Their signs are

    negative Q points: +, -, +, ... , (-1)^p;
    zero:              sign(b*g(0))=(-1)^(p+1);
    positive f points: (-1)^p, (-1)^(p-1), ... , -.

The endpoint signs are P(-1)<0 and P(1)>0. Again every successive pair has
opposite signs, producing deg(P)=2p+3 simple roots in (-1,1).

### b=0 and repeated-root boundary

For odd f and b=0, keep c fixed in [0,3] and let positive b decrease to zero.
Every approximating pair satisfies c<=b^2/4+b+3. The original polynomials in
x are monic of the same degree and converge coefficientwise, so their
real-rooted limit is real-rooted. No unsupported simplicity claim is made
for this limit. The n=3 case is handled independently by the given quadratic
discriminant, including its possible double root.

## 5. Exact computational review

`verify_hybrid_proof.py` verifies the generic algebraic identity, the pair
positivity factorization, and the hybrid testpoint counts/signs for selected
rational parameters. Each nonrational testpoint is represented by an exact
rational isolating interval; exact Horner interval arithmetic certifies the
polynomial's sign throughout that interval. The output JSON retains all
intervals and sign vectors. Separate exact counts handle b=0 limit cases and
the n=3 double-root boundary, restoring multiplicities via square-free
factorization. All **279 hybrid-sign cases** and **22 limit/boundary cases**
completed successfully. The sampled n range was 4,...,14 for the hybrid signs,
with positive b ranging from 1/10^6 through 10^6 and c equal to 0, half the
conjectured boundary, or the boundary; b=0 was additionally included where the
strict-sign argument applies directly. The generic symbolic identity and pair
factorization checks also passed. See the log and JSON for exact inputs.

The earlier `finite_auxiliary_certificate.py` completed all m=2,...,27 cases,
with full polynomial coefficients and exact Sturm endpoint sign vectors. Those
certificates are retained as unused research diagnostics. They are not needed
for, and are not dependencies of, the full analytical proof above.
