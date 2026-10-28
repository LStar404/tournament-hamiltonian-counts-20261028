#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check_sources.py
lake build
python3 scripts/audit_axioms.py
echo 'Lean compilation and the declared-theorem axiom audit passed.'
echo 'Read the coverage document: this does not certify the whole manuscript.'
