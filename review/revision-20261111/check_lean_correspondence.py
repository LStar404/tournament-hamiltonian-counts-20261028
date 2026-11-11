#!/usr/bin/env python3
"""Read-only index/hash/source checks. Does not run Lean or certify mathematics."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    index = json.loads((HERE / 'lean_correspondence.json').read_text())
    assert index['this_revision_full_lean_build'] is False
    for rel, digest in index['evidence_sha256'].items():
        assert sha(ROOT / rel) == digest, f'Evidence changed: {rel}'
    historical = json.loads((ROOT / 'formal/coverage.json').read_text())
    for name, endpoint in index['endpoint_catalog'].items():
        assert endpoint == {k: historical['endpoint_catalog'][name][k] for k in endpoint}
        assert sha(ROOT / 'formal' / endpoint['source']) == endpoint['source_sha256'], name
    manifest = json.loads((ROOT / 'review/lean-rerun-20261107/input_manifest.json').read_text())
    inputs = {e['path']: e for e in manifest['entries']}
    for rel in manifest['production_sources']:
        assert sha(ROOT / 'formal' / rel) == inputs[rel]['sha256'], rel
    seen = set()
    for entry in index['entries']:
        assert entry['stable_id'] not in seen
        seen.add(entry['stable_id'])
        assert all(n in index['endpoint_catalog'] for n in entry['endpoints'])
        if entry['status'] in ('no_new_endpoint', 'composition_not_mapped'):
            assert not entry['endpoints'] and entry['build_record'] is None
        elif entry['endpoints']:
            assert entry['build_record'] == 'H' and entry['source_version'] == 'S'
    run = json.loads((ROOT / 'review/lean-rerun-20261107/summary.json').read_text())['actual_run']
    assert run['state'] == 'PASS' and len(run['commands']) == 318
    assert all(c['exit_code'] == 0 for c in run['commands'])
    for script in ('check_release_manifest.py', 'check_sources.py'):
        subprocess.run([sys.executable, str(ROOT / 'formal/scripts' / script)], check=True)
    print(f'PASS: {len(seen)} mapping rows; {len(index["endpoint_catalog"])} endpoint source identities; '
          f'{len(manifest["production_sources"])} frozen production sources. No Lean compilation performed.')


if __name__ == '__main__':
    main()
