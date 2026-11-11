#!/usr/bin/env python3
"""Exact checks for elementary additions; not an asymptotic or Lean proof."""
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]


def path_count(out, n):
    dp = [[0] * n for _ in range(1 << n)]
    for v in range(n):
        dp[1 << v][v] = 1
    for mask in range(1, 1 << n):
        for v in range(n):
            if not dp[mask][v]:
                continue
            for w in out[v]:
                if not mask & (1 << w):
                    dp[mask | (1 << w)][w] += dp[mask][v]
    return sum(dp[-1])


def main():
    n = sp.symbols("n", integer=True, positive=True)
    j = sp.symbols("j", integer=True)
    transitive = sp.simplify(sp.summation((j - (n - 1) / 2) ** 2, (j, 0, n - 1)))
    assert sp.simplify(transitive - n * (n ** 2 - 1) / 12) == 0
    c0, k0, delta = sp.symbols("C_0 K_0 delta", nonnegative=True)
    excess = sp.factor(c0 * (k0 + 1) * (delta * n ** 2 + n)
                       - c0 * (delta * n ** 2 + (k0 + 1) * n))
    assert excess == c0 * delta * k0 * n ** 2

    records = []
    for order in range(1, 6):
        pairs = list(combinations(range(order), 2))
        maximum = -1
        variances = set()
        for bits in range(1 << len(pairs)):
            out = [[] for _ in range(order)]
            for bit, (u, v) in enumerate(pairs):
                a, b = (u, v) if bits & (1 << bit) else (v, u)
                out[a].append(b)
            degrees = list(map(len, out))
            variance4 = sum((2 * d - order + 1) ** 2 for d in degrees)
            if order % 2 == 0:
                balanced = all(d in (order // 2 - 1, order // 2) for d in degrees)
                assert variance4 >= order
                assert (variance4 == order) == balanced
            paths = path_count(out, order)
            if paths > maximum:
                maximum, variances = paths, {variance4}
            elif paths == maximum:
                variances.add(variance4)
        records.append({
            "order": order,
            "labelled_tournaments": 1 << len(pairs),
            "maximum_paths": maximum,
            "exact_maximizer_variances": [str(Fraction(v, 4)) for v in sorted(variances)],
        })

    for stem, heading in (("02_combined.en", "## Abstract"),
                          ("01_combined.zh", "## 摘要")):
        text = (ROOT / "manuscripts" / (stem + ".md")).read_text()
        abstract = text.split(heading, 1)[1].split("## 1.", 1)[0]
        assert r"0\le\varepsilon\le(L-1)/2" in abstract
        assert r"\mu_n=n!/2^{n-1}" in abstract
        assert r"L=\cosh1/\cos1" in abstract
        assert r"\delta_0=(L-1)/4" in text
        assert r"V_{\rm deg}(T)=O_A(n)" in text
    print(json.dumps({
        "passed": True,
        "scope": "Exact elementary identities and finite examples only; not a proof of the asymptotic stability theorem.",
        "transitive_variance": str(transitive),
        "constant_absorption_nonnegative_excess": str(excess),
        "even_order_lower_bound_and_equality_checked": [2, 4],
        "abstract_parameter_guards": "both languages passed",
        "records": records,
    }, indent=2))


if __name__ == "__main__":
    main()
