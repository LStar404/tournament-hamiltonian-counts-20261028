#!/usr/bin/env python3
"""Compile a #print axioms inventory of the explicitly listed public theorems.

The inventory is source-controlled and reviewed against the coverage table.
This checks transitive dependencies, not just source spellings.
"""
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def main():
    names = json.loads((ROOT / 'theorems.json').read_text())
    if not names or len(names) != len(set(names)):
        raise SystemExit('The theorem inventory must be nonempty and unique')
    if any(not re.fullmatch(r'(?:[^\W\d]\w*\.)*[^\W\d]\w*', n) for n in names):
        raise SystemExit('Invalid theorem identifier')
    outdir = ROOT / '.lake' / 'verification'
    outdir.mkdir(parents=True, exist_ok=True)
    source = outdir / 'AxiomAudit.lean'
    source.write_text('import Tournament\n\n' + ''.join(f'#print axioms {n}\n' for n in names))
    run = subprocess.run(['lake', 'env', 'lean', str(source)], cwd=ROOT,
                         text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (outdir / 'axioms.log').write_text(run.stdout)
    if run.returncode:
        print(run.stdout)
        return run.returncode
    found = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", run.stdout):
        found[name] = [a.strip() for a in axioms.split(',') if a.strip()]
    for name in re.findall(r"'([^']+)' does not depend on any axioms", run.stdout):
        found[name] = []
    missing = set(names) - set(found)
    unexpected = {n: sorted(set(a)-ALLOWED) for n,a in found.items() if set(a)-ALLOWED}
    report = {'theorem_count':len(names), 'allowlisted_foundational_axioms':sorted(ALLOWED),
              'checked':found, 'missing':sorted(missing), 'unexpected':unexpected,
              'passed':not missing and not unexpected}
    (outdir / 'axioms.json').write_text(json.dumps(report,indent=2)+'\n')
    if not report['passed']:
        print(json.dumps(report,indent=2))
        return 1
    print(f'PASS: {len(names)} declared theorems; transitive axioms restricted to standard foundations.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
