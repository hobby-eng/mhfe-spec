"""Validate the AUD-010 pair, baseline bindings and local command/log identities.

Requires jsonschema from inspection-requirements.txt or the existing runtime.
No schema/report/source is rewritten. Validation evidence remains local.
"""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

import jsonschema

ROOT = Path(__file__).resolve().parents[3]
EVIDENCE = ROOT / 'docs/audits/AUD-010-evidence'
REPORT = ROOT / 'docs/audits/AUD-010-2026-10-27'


def unique(pairs):
    value = {}
    for key, item in pairs:
        if key in value:
            raise ValueError('duplicate JSON key: ' + key)
        value[key] = item
    return value


def load(path):
    return json.loads(path.read_text(), object_pairs_hook=unique)


def validate():
    data = load(REPORT.with_suffix('.json'))
    markdown = REPORT.with_suffix('.md').read_text()
    schema_path = ROOT.parent / 'multi-chain-wallet-tools/docs/audit-report.schema.json'
    schema = load(schema_path)
    jsonschema.Draft202012Validator(schema).validate(data)
    ids = [item['id'] for item in data['findings']]
    if len(ids) != len(set(ids)):
        raise ValueError('duplicate finding ID')
    expected_ids = set(re.findall(r'(?m)^#### (AUD-\d+-(?:SEC|FUN|API|BLD|DOC|UI|ARC)\d+)', markdown))
    if set(ids) != expected_ids:
        raise ValueError('Markdown/JSON finding sets differ')
    for item in data['findings']:
        if f"| {item['id']} | {item['category']} | finding | {item['severity']} | {item['status']} |" not in markdown:
            raise ValueError('finding register disagrees with JSON')
        if not item['id'].startswith('AUD-010-' + item['category']):
            raise ValueError('category/ID mismatch')
    checks = data['checks']['coverage']
    guide = (ROOT.parent / 'multi-chain-wallet-tools/docs/FULL_AUDIT_GUIDE.md').read_text()
    required_checks = set(re.findall(r'### (CHECK-[A-Z]+-\d+)', guide))
    if len(checks) != 32 or {item['checkId'] for item in checks} != required_checks:
        raise ValueError('incomplete checklist')
    if any(item['outcome'] in ('not-run', 'blocked') for item in checks):
        raise ValueError('unreconciled checklist')
    published = markdown + REPORT.with_suffix('.json').read_text()
    if re.search(r'/home/(?!user(?:/|\b))[^/\s"\']+', published):
        raise ValueError('machine owner path leaked into report')
    for reference in re.findall(r'\]\(([^)]+)\)', markdown):
        if re.match(r'[a-z]+:', reference):
            continue
        path = (REPORT.parent / reference.split('#')[0]).resolve()
        if not path.exists():
            raise ValueError('missing report link: ' + reference)
    snapshot = load(EVIDENCE / 'snapshot.json')
    for item in snapshot['files']:
        if item['path'] == 'docs/audits/README.md':
            continue  # Only audit-owned baseline edit: the index gains the new report.
        if hashlib.sha256((ROOT / item['path']).read_bytes()).hexdigest() != item['sha256']:
            raise ValueError('baseline source changed: ' + item['path'])
    commands = []
    for directory in (EVIDENCE, EVIDENCE / 'interrupted-attempt'):
        for path in directory.glob('*.command.json'):
            record = load(path)
            log = path.with_name(path.name.removesuffix('.command.json') + '.log')
            if hashlib.sha256(log.read_bytes()).hexdigest() != record['logSha256']:
                raise ValueError('command log digest mismatch: ' + str(log))
            commands.append({'record': str(path.relative_to(ROOT)), 'exitCode': record['exitCode']})
    coverage = load(EVIDENCE / 'file-coverage.json')
    if len(coverage) != 173 or not all(item['reviewed'] for item in coverage.values()):
        raise ValueError('unreconciled file coverage')
    for raw in load(EVIDENCE / 'procedure-hashes.json').items():
        name, digest = raw
        if hashlib.sha256((ROOT.parent / name).read_bytes()).hexdigest() != digest:
            raise ValueError('procedure changed: ' + name)
    for item in data['artifacts']['trackedDocuments']:
        if hashlib.sha256((ROOT / item['file']).read_bytes()).hexdigest() != item['sha256']:
            raise ValueError('tracked PDF changed')
    index = (ROOT / 'docs/audits/README.md').read_text()
    if 'AUD-010-2026-10-27.md' not in index or 'AUD-010-2026-10-27.json' not in index:
        raise ValueError('index links absent')
    if subprocess.check_output(['git', 'diff', '--name-only'], cwd=ROOT, text=True).splitlines() != ['docs/audits/README.md']:
        raise ValueError('unexpected tracked source modification')
    return {'validatedUtc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
            'schemaSha256': hashlib.sha256(schema_path.read_bytes()).hexdigest(),
            'reportMdSha256': hashlib.sha256(REPORT.with_suffix('.md').read_bytes()).hexdigest(),
            'reportJsonSha256': hashlib.sha256(REPORT.with_suffix('.json').read_bytes()).hexdigest(),
            'findings': len(ids), 'checkIds': len(checks), 'trackedBaselinePaths': len(coverage),
            'commandRecords': commands, 'model': None, 'reasoningEffort': None}


def main():
    result = validate()
    (EVIDENCE / 'report-validation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'commandRecords'}, indent=2))


if __name__ == '__main__':
    main()
