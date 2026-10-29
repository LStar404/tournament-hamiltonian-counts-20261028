#!/usr/bin/env python3
"""Exhaustive exact-integer regression, independent of Lean (not a proof)."""
from itertools import combinations, permutations
import json
from math import prod
from pathlib import Path


def matrix_sum(matrix, signed=False):
    n = len(matrix)
    total = 0
    for p in permutations(range(n)):
        sign = (-1) ** sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n))
        total += (sign if signed else 1) * prod(matrix[i][p[i]] for i in range(n))
    return total


def check():
    records = []
    for n in range(6):
        edges = list(combinations(range(n), 2))
        counts = []
        for mask in range(1 << len(edges)):
            a = [[0] * n for _ in range(n)]
            for k, (i, j) in enumerate(edges):
                a[i][j] = (mask >> k) & 1
                a[j][i] = 1 - a[i][j]
            paths = sum(all(a[p[i]][p[i+1]] for i in range(n-1))
                        for p in permutations(range(n)))
            convolution = 0
            for subset in range(1 << n):
                u = [i for i in range(n) if subset >> i & 1]
                v = [i for i in range(n) if not subset >> i & 1]
                determinant = matrix_sum([[int(i == j) + a[i][j] for j in u] for i in u], True)
                permanent = matrix_sum([[a[i][j] for j in v] for i in v])
                convolution += determinant * permanent
            if paths != convolution:
                raise AssertionError((n, mask, paths, convolution))
            counts.append(paths)
        records.append({'order': n, 'tournaments': len(counts),
                        'min_paths': min(counts), 'max_paths': max(counts)})
    return {'passed': True, 'method': 'integer permutation sums, all labelled tournaments of orders 0..5',
            'empty_determinant': matrix_sum([], True), 'empty_permanent': matrix_sum([]),
            'records': records}


if __name__ == '__main__':
    report = check()
    out = Path(__file__).resolve().parents[1] / '.lake' / 'verification'
    out.mkdir(parents=True, exist_ok=True)
    (out / 'convolution_regressions.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
