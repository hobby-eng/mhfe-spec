"""Check the late error-disclosure allegation using synthetic input only.

Every child fails during word lookup before Argon2. This probe binds its
conclusion to the actual Python runtime, since list.index diagnostics vary.
"""

import json
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]


def main():
    token = 'audit-only-secret-token'
    phrase = ' '.join(['abandon'] * 11 + [token])
    results = []
    for suite in (3, 4):
        for operation in ('encrypt', 'decrypt'):
            supplied = phrase + '\npublic audit password\n'
            if operation == 'encrypt':
                supplied += 'public audit password\n'
            child = subprocess.run(
                [sys.executable, '-B', f'scripts/independent-suite{suite}.py', operation],
                input=supplied, text=True, capture_output=True, timeout=10, cwd=ROOT,
            )
            results.append({'suite': suite, 'operation': operation,
                            'exitCode': child.returncode, 'stderr': child.stderr,
                            'tokenInStderr': token in child.stderr})
            if child.returncode == 0 or 'ValueError' not in child.stderr:
                raise AssertionError('case did not fail at the intended word-lookup boundary')
    print(json.dumps({'python': platform.python_version(), 'results': results}, indent=2))
    return 1 if any(item['tokenInStderr'] for item in results) else 0


if __name__ == '__main__':
    raise SystemExit(main())
