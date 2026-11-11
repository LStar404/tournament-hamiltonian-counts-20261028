#!/usr/bin/env python3
"""Check English coverage metadata and pinned source identities; never invoke Lean."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def main():
    index = json.loads((HERE / 'lean_coverage.json').read_text())
    old = json.loads((ROOT / 'review/revision-20261111/lean_correspondence.json').read_text())
    require(index['this_revision_full_lean_build'] is False, 'Unexpected build claim')
    require(index['this_revision_new_lean_endpoints'] is False, 'Unexpected endpoint claim')
    base = index['repository_base_commit']
    prefix = 'https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/' + base + '/'
    for path, evidence in index['pinned_evidence'].items():
        current = (ROOT / path).read_bytes()
        pinned = subprocess.check_output(['git', 'show', base + ':' + path], cwd=ROOT)
        require(current == pinned, 'Historical evidence changed: ' + path)
        require(hashlib.sha256(current).hexdigest() == evidence['sha256'], 'Hash mismatch: ' + path)
        require(evidence['url'] == prefix + path, 'Incorrect pinned URL: ' + path)
    require(index['endpoint_catalog'] == old['endpoint_catalog'], 'Historical catalog changed')
    for name, endpoint in index['endpoint_catalog'].items():
        source = ROOT / 'formal' / endpoint['source']
        require(hashlib.sha256(source.read_bytes()).hexdigest() == endpoint['source_sha256'], 'Source mismatch: ' + name)
    entries = {entry['stable_id']: entry for entry in index['entries']}
    require(len(entries) == len(index['entries']) == 37, 'Duplicate/missing summary rows')
    for historical in old['entries']:
        current = entries[historical['stable_id']]
        for field in ('status', 'endpoints', 'source_version', 'build_record'):
            require(current[field] == historical[field], 'Coverage changed: ' + historical['stable_id'])
    for ident in ('even_order_variance_scale', 'actual_optimum_deficit', 'score_sensitive_upper', 'degree_stability'):
        entry = entries[ident]
        require(entry['status'] == 'no_new_endpoint' and not entry['endpoints']
                and entry['source_version'] is None and entry['build_record'] is None,
                'Unsupported new formalization claim: ' + ident)
    subprocess.run([sys.executable, str(ROOT / 'review/revision-20261111/check_lean_correspondence.py')], check=True)
    print('PASS: 37 English summary rows; 85 unchanged endpoint identities; 10 pinned evidence files.')
    print('No Lean compilation, new axiom audit, type printing, or verification of new mathematics performed.')


if __name__ == '__main__':
    main()
