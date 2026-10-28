#!/usr/bin/env python3
"""Exact rational regression checks, NOT a general formal proof.

Compute the two-jet of the actual implicit determinant equation by determinant
multilinearity, independently of the proposed matrix Hessian expression.
Requires SymPy. No finite differences, floating-point tolerance, or API calls.
"""
import json
from pathlib import Path
import sympy as sp


def carousel(d):
    return sp.Matrix(d, d, lambda i, j: int(bool(0 < (j-i) % d <= (d-1)//2)))


def check(d, A=None, label='carousel'):
    A = carousel(d) if A is None else A
    z = sp.Rational(2, d)
    I = sp.eye(d)
    P = A + I/2
    B = I - z*P
    assert B.det() == 0
    # Differentiation of column j of I-P diag(y) replaces it with -P[:,j].
    def derivative(cols):
        M = B.copy()
        for j in cols:
            M[:, j] = -P[:, j]
        return M.det()
    first = [derivative([j]) for j in range(d)]
    last = d-1
    assert first[last] != 0
    first_h = [-first[j]/first[last] for j in range(last)]
    assert first_h == [-1] * last
    def k2(j, k):
        return sp.Integer(0) if j == k else derivative([j, k])
    second_h = sp.Matrix(last, last, lambda j, k:
        -(k2(j,k) + k2(j,last)*first_h[k] + k2(last,k)*first_h[j]) / first[last])
    # f(theta)=log h(z exp(i theta)); two i factors reverse the sign.
    direct = sp.Matrix(last, last, lambda j, k:
        -z*second_h[j,k] + first_h[j]*first_h[k] - int(j == k)*first_h[j])
    C = (A-A.T)/d
    E = sp.Matrix(d,last,lambda i,j: int(i==j)-int(i==last))
    Q = (I+C*C)*(I-C*C).inv()
    formula = E.T*Q*E
    assert direct == formula
    assert direct.det() == d*(I+C*C).det()/(I-C*C).det()
    assert all(direct[:k,:k].det()>0 for k in range(1,d))
    ratio = sp.simplify((I+C).det()/(I+sp.I*C).det())
    assert ratio.is_Rational and ratio > 0
    assert ratio**2 * direct.det() == d
    return {'d':d,'graph':label,'implicit_partial':str(first[last]),
            'hessian_determinant':str(direct.det()),'positive_ratio':str(ratio),
            'actual_implicit_two_jet_equals_matrix_formula':True}


if __name__ == '__main__':
    result = {'kind':'finite exact regression only, not general proof',
              'sympy_version':sp.__version__,
              'cases':[check(d) for d in (3,5,7,9)] + [
                  check(7,sp.Matrix(7,7,lambda i,j:int(int((j-i)%7) in {1,2,4})),
                        'Paley7 quadratic residues')]}
    print(json.dumps(result,indent=2))
