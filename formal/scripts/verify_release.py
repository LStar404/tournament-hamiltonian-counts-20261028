#!/usr/bin/env python3
"""Verify the exact release inputs with optional bounded fresh production build.

A --fresh run refuses existing project artifacts. Fixed external dependencies may
already have their official caches; this is NOT a cold rebuild of all mathlib.
All new execution output stays in .lake/verification/release-runs/.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from check_release_manifest import ROOT, validate


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fresh', action='store_true')
    parser.add_argument('--width', type=int, choices=[1, 2], default=2)
    args = parser.parse_args()
    data, graph = validate()
    if args.fresh and (ROOT / '.lake/build').exists():
        raise SystemExit('--fresh requires a new project build directory; no caches are removed automatically')
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    out = ROOT / '.lake/verification/release-runs' / stamp
    out.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ)
    for key in ['LEAN_PATH', 'LEAN_SRC_PATH']:
        env.pop(key, None)
    env.update(LEAN_NUM_THREADS='2', LAKE_NO_CACHE='true', LAKE_ARTIFACT_CACHE='false',
               LAKE_RESTORE_ARTIFACTS='false', LAKE_CACHE_DIR='')
    commands = []
    result = {'started': now(), 'input_manifest_sha256': sha(ROOT / 'verification/release/input_manifest.json'),
              'production_module_count': len(graph), 'registered_endpoint_count': data['registered_endpoint_count'],
              'fresh_project_start': args.fresh, 'upstream_caches_may_be_reused': True,
              'not_all_mathlib_cold_build': True, 'ready_target_width': args.width,
              'state': 'running'}

    def save():
        (out / 'RESULTS.json').write_text(json.dumps({**result, 'commands': commands}, indent=2) + '\n')

    def run(name, argv):
        start, tick = now(), time.monotonic()
        with (out / (name + '.log')).open('w', encoding='utf-8') as log:
            proc = subprocess.run(argv, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        commands.append({'name': name, 'command': argv, 'started': start, 'finished': now(),
                         'elapsed_seconds': round(time.monotonic() - tick, 3), 'exit_code': proc.returncode})
        (out / (name + '.exitcode')).write_text(str(proc.returncode) + '\n')
        save()
        if proc.returncode:
            raise RuntimeError(f'{name}: exit {proc.returncode}; see {out.relative_to(ROOT)}')
        print(f'PASS {name}', flush=True)

    def dependencies():
        records = []
        for dep in json.loads((ROOT / 'lake-manifest.json').read_text())['packages']:
            path = ROOT / '.lake/packages' / dep['name']
            head = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
            status = subprocess.check_output(['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=no'], text=True)
            if head != dep['rev'] or status:
                raise ValueError(f"Unpinned or tracked-dirty dependency: {dep['name']}")
            records.append({'package': dep['name'], 'revision': head, 'tracked_clean': True})
        return records

    save()
    try:
        before = dependencies()
        run('lean_version', ['lake', 'env', 'lean', '--version'])
        version = (out / 'lean_version.log').read_text().strip()
        if '4.35.0' not in version:
            raise ValueError('Unexpected compiler version')
        result['lean_version'] = version
        result['dependencies'] = before
        if args.fresh:
            done = set()
            while len(done) < len(graph):
                batch = [m for m in sorted(graph) if m not in done and set(graph[m]) <= done][:args.width]
                if not batch:
                    raise ValueError('Project dependency cycle')
                run('fresh_' + str(len(done)).zfill(4), ['lake', '--no-cache', 'build', *batch])
                for module in batch:
                    for suffix in ['.olean', '.ilean']:
                        artifact = ROOT / '.lake/build/lib/lean' / Path(module.replace('.', '/') + suffix)
                        if not artifact.is_file() or artifact.is_symlink():
                            raise ValueError(f'Missing newly compiled project artifact: {module}{suffix}')
                done.update(batch)
            result['fresh_compiled_production_modules'] = len(done)
        run('default_build', ['lake', 'build'])
        run('source_scan', ['python3', 'scripts/check_sources.py'])
        run('registry_axioms', ['python3', 'scripts/audit_axioms.py'])
        for filename in ['axioms.json', 'axioms.log', 'AxiomAudit.lean']:
            shutil.copy2(ROOT / '.lake/verification' / filename, out / filename)
        audit = json.loads((out / 'axioms.json').read_text())
        if not audit['passed'] or audit['theorem_count'] != data['registered_endpoint_count']:
            raise ValueError('Recursive axiom audit did not cover the full registry')
        run('key_endpoint_types', ['lake', 'env', 'lean', 'verification/release/KeyEndpointAudit.lean'])
        run('actual_definitions', ['lake', 'env', 'lean', 'verification/release/DefinitionsAudit.lean'])
        key = (out / 'key_endpoint_types.log').read_text()
        found = {n: v for n, v in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", key)}
        found.update({n: '' for n in re.findall(r"'([^']+)' does not depend on any axioms", key)})
        expected = json.loads((ROOT / 'verification/release/key_endpoints.json').read_text())
        if set(found) != set(expected):
            raise ValueError('Key endpoint recursive axiom set mismatch')
        for axioms in found.values():
            names = {re.sub(r'\.\{[^{}]*\}$', '', x.strip()) for x in axioms.split(',') if x.strip()}
            if not names <= {'propext', 'Classical.choice', 'Quot.sound'}:
                raise ValueError('Unexpected key endpoint axiom')
        validate()
        if dependencies() != before:
            raise ValueError('Dependency identity changed during verification')
        result.update(state='PASS', finished=now(), recursive_axioms_standard_only=True,
                      key_endpoint_count=len(expected), source_identity_unchanged=True)
        save()
        print(f"PASS: results in {out.relative_to(ROOT)}")
    except Exception as exc:
        result.update(state='FAIL', finished=now(), reason=str(exc))
        save()
        raise


if __name__ == '__main__':
    main()
