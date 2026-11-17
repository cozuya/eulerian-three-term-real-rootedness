"""Independent exact checks of algebra used by the final hybrid proof.

Run: python research/sturm/verify_full_proof_identities.py
These are checks of identities, not the logical source of the all-degree proof.
"""
import json
import platform
import sympy as s

x, z, alpha, c, rp, rho, lam, a = s.symbols(
    "x z alpha c rp rho lam a")

# Exact full-boundary evaluation at a Q=g+alpha*h root.
R_at_q = -alpha
f_over_h = R_at_q*(R_at_q+x)+x*(1-x)*rp
E_at_q = -x*(1-x)*rp+(2-x)*R_at_q-2
P_at_q = f_over_h+(2*alpha-2)*R_at_q+c
assert s.expand(P_at_q-(c-alpha**2-2-E_at_q)) == 0

# One-pole verification of the positive-residue induction identity.
Rz = rho+lam/(z*z-a)
kernel = (z*z-1)*s.diff(Rz,z)+2*z*Rz
expected = 2*z*(rho+lam*(1-a)/(z*z-a)**2)
assert s.cancel(kernel-expected) == 0

# Direct convention and transformed-recurrence checks.
A = [s.Integer(1), s.Integer(1)]
for n in range(1,12):
    A.append(s.expand((1+n*x)*A[n]+x*(1-x)*s.diff(A[n],x)))
C = {n:s.cancel((z+1)**(n-1)*A[n].subs(x,(z-1)/(z+1)))
     for n in range(1,13)}
for n in range(1,12):
    assert s.expand(C[n+1]-s.diff((z*z-1)*C[n],z)) == 0
for n in range(3,13):
    F = (z*z-1)*C[n-2]
    assert s.expand(s.diff(F,z)-C[n-1]) == 0
    assert s.expand(C[n].subs(z,-z)-(-1)**(n-1)*C[n]) == 0
    assert C[n].subs(z,1) == 2**(n-1)
    assert C[n].subs(z,-1) == (-2)**(n-1)
assert s.cancel(C[3]/((z*z-1)*C[1])-(6+4/(z*z-1))) == 0

print(json.dumps({
    "python":platform.python_version(),
    "sympy":s.__version__,
    "Q_root_boundary_identity":"PASS",
    "positive_residue_induction_kernel":"PASS",
    "Cayley_recurrence_n_1_through_11":"PASS",
    "F_derivative_parity_endpoints_n_3_through_12":"PASS",
    "positive_residue_base_case":"PASS",
    "all_degree_proof_is_analytical":True
},indent=2))
