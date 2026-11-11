#!/usr/bin/env python3
"""Finite exact rational regression checks, NOT a general or formal proof.

Run from any working directory. Writes only the adjacent JSON report.
SymPy is required. No floating-point eigenvalues or tolerances are used.
The actual implicit-function two-jet is checked by the separate existing
formal/scripts/check_hessian_examples.py, not by this coordinate regression.
"""
import json
from pathlib import Path
import sympy as s


def psd_exact(M):
    """Exact symmetric Schur-complement PSD test, including zero pivots."""
    assert M == M.T
    M = M.copy()
    pivots = []
    while M.rows:
        p = M[0, 0]
        assert p.is_Rational
        assert p >= 0, 'Negative pivot'
        pivots.append(str(p))
        if p == 0:
            assert all(v == 0 for v in M[0, :]), 'Zero diagonal with nonzero row'
            M = M[1:, 1:]
        else:
            v = M[1:, 0]
            M = M[1:, 1:] - v*v.T/p
    return pivots


def check(d, paley=False):
    A = s.Matrix(d, d, lambda i,j: int((j-i)%d in {1,2,4}) if paley
                 else int(bool(0 < (j-i)%d <= (d-1)//2)))
    I, one = s.eye(d), s.ones(d, 1)
    assert A + A.T == s.ones(d)-I
    C = (A-A.T)/d
    assert C.T == -C and C*one == s.zeros(d, 1)
    E = s.Matrix(d, d-1, lambda i,j: int(i == j)-int(i == d-1))
    G = E.T*E
    assert G == s.eye(d-1)+s.ones(d-1)
    assert G.det() == d and E.T*one == s.zeros(d-1, 1)
    assert E*G.inv()*E.T == I-one*one.T/d
    Q = (I+C*C)*(I-C*C).inv()
    H = E.T*Q*E
    assert Q == Q.T and Q*one == one and H == H.T
    a = s.Rational(d+1, 3*d-1)
    lower = psd_exact(H-a*G)
    upper = psd_exact(G-H)
    t = s.Symbol('t')
    # det(H-tG)=det(G)*det(G^{-1}H-tI), computed by charpoly.
    h_det = G.det()*(-1)**(d-1)*(G.inv()*H).charpoly(t).as_expr()
    q_det = (-1)**d*Q.charpoly(t).as_expr()
    assert s.expand((1-t)*h_det-d*q_det) == 0
    assert H.det() == d*Q.det()
    out = {'d':d, 'graph':'Paley7' if paley else 'carousel',
           'a_d':str(a), 'E_G_projection_identities':True,
           'Q_symmetric_fixes_constant_direction':True,
           'H_equals_E_transpose_Q_E':True,
           'lower_bound_exact_psd_pivots':lower,
           'upper_bound_exact_psd_pivots':upper,
           'generalized_characteristic_identity':True,
           'det_H_minus_tG':str(s.factor(h_det)),
           'det_H_equals_d_det_Q':True}
    if d == 3:
        assert H == G/2
        assert H.eigenvals() == {s.Rational(1,2):1, s.Rational(3,2):1}
        assert (G.inv()*H).eigenvals() == {s.Rational(1,2):2}
        out['triangle_ordinary_spectrum'] = ['1/2', '3/2']
        out['triangle_generalized_spectrum'] = ['1/2', '1/2']
    return out


if __name__ == '__main__':
    result = {'kind':'finite exact rational regression only; not a general or formal proof',
              'sympy_version':s.__version__,
              'cases':[check(d) for d in (3,5,7,9)] + [check(7, True)],
              'status':'PASS'}
    target = Path(__file__).with_suffix('.json')
    target.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
