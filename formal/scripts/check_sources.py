#!/usr/bin/env python3
"""Fail closed on proof placeholders or locally introduced trust extensions.

This lexical check supplements (does not replace) compilation and #print axioms.
Nested Lean comments and strings are removed before token inspection.
"""
from pathlib import Path
import re
import sys


def code_only(text: str) -> str:
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1; i += 2
            elif text.startswith('-/', i):
                depth -= 1; i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif string:
            if text[i] == '\\':
                i += 2
            elif text[i] == '"':
                string = False; out.append(' '); i += 1
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('/-', i):
            depth = 1; out.append(' '); i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            string = True; out.append(' '); i += 1
        else:
            out.append(text[i]); i += 1
    if depth or string:
        raise ValueError('Unterminated Lean comment or string')
    return ''.join(out)


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    files = sorted((root / 'Tournament').rglob('*.lean'))
    files += sorted((root / 'TournamentHamiltonian').rglob('*.lean'))
    if (root / 'Tournament.lean').exists():
        files.append(root / 'Tournament.lean')
    if not files:
        raise SystemExit('No project Lean source files found')
    forbidden = {'sorry', 'admit', 'axiom', 'unsafe', 'native_decide'}
    errors = []
    for path in files:
        code = code_only(path.read_text(encoding='utf-8'))
        for token in re.finditer(r"[A-Za-z_][A-Za-z_0-9']*", code):
            if token.group() in forbidden:
                line = code[:token.start()].count('\n') + 1
                errors.append(f'{path.relative_to(root)}:{line}: {token.group()}')
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        return 1
    print(f'PASS: {len(files)} local Lean sources have no forbidden proof placeholders/trust extensions.')
    return 0


if __name__ == '__main__':
    sys.exit(main())

