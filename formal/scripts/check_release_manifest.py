#!/usr/bin/env python3
"""Fail-closed integrity checks for the release's explicitly listed local inputs.

No Git HEAD lookup, parent repository discovery, downloads, or source rewriting.
This is a byte/shape check; Lean compilation and recursive axiom audits are separate.
"""
from pathlib import Path, PurePosixPath
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(root=ROOT, manifest=None):
    path = root / 'verification/release/input_manifest.json' if manifest is None else manifest
    data = json.loads(path.read_text(encoding='utf-8'))
    entries = data['entries']
    if not entries or not isinstance(entries, list):
        raise ValueError('Input manifest must be a nonempty list')
    names = set()
    for entry in entries:
        name = entry['path']
        pp = PurePosixPath(name)
        if not name or pp.is_absolute() or '..' in pp.parts or '\\' in name or str(pp) != name:
            raise ValueError(f'Noncanonical relative input path: {name!r}')
        if name in names or '.lake' in pp.parts:
            raise ValueError(f'Duplicate or cache input path: {name}')
        names.add(name)
        current = root
        for part in pp.parts:
            current = current / part
            if current.is_symlink():
                raise ValueError(f'Symlink in release input: {name}')
        if not current.is_file() or current.stat().st_size != entry['bytes'] or sha(current) != entry['sha256']:
            raise ValueError(f'Input byte identity mismatch: {name}')
    production = {'Tournament.lean'}
    for folder in ['Tournament', 'TournamentHamiltonian']:
        production.update(str(p.relative_to(root)) for p in (root / folder).rglob('*.lean'))
    declared = set(data['production_sources'])
    if not declared or len(declared) != data['production_module_count'] or production != declared or not declared <= names:
        raise ValueError('Production module count/set mismatch, missing or extra source')
    graph = {}
    for rel in sorted(declared):
        module = rel[:-5].replace('/', '.')
        imports = []
        for line in (root / rel).read_text(encoding='utf-8').splitlines():
            match = re.match(r'^(?:public )?import (.+)$', line)
            if match:
                imports.extend(n for n in match[1].split('--')[0].split()
                               if n == 'Tournament' or n.startswith(('Tournament.', 'TournamentHamiltonian.')))
        graph[module] = imports
    reached, active = set(), set()

    def visit(module):
        if module in active:
            raise ValueError('Project import cycle')
        if module in reached:
            return
        if module not in graph:
            raise ValueError(f'Missing project import: {module}')
        active.add(module)
        for imported in graph[module]:
            visit(imported)
        active.remove(module)
        reached.add(module)

    visit('Tournament')
    if reached != set(graph):
        raise ValueError('Project source outside default-root closure')
    registry = json.loads((root / 'theorems.json').read_text(encoding='utf-8'))
    if not registry or len(registry) != len(set(registry)) or len(registry) != data['registered_endpoint_count']:
        raise ValueError('Endpoint registry size/uniqueness mismatch')
    required = {'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'theorems.json'}
    if not required <= names:
        raise ValueError('Toolchain/configuration/registry missing from integrity scope')
    return data, graph


if __name__ == '__main__':
    data, graph = validate()
    print(f"PASS: {len(data['entries'])} exact input files; {len(graph)} root-reachable production modules; "
          f"{data['registered_endpoint_count']} unique registered endpoints.")
