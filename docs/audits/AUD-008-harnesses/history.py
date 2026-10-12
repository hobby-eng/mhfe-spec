"""Check current historical report envelopes without revalidating their conclusions."""

import json
from pathlib import Path
import jsonschema


ROOT = Path(__file__).resolve().parents[3]


def main():
    schema = json.loads((ROOT.parent / "multi-chain-wallet-tools/docs/audit-report.schema.json").read_text())
    result = []
    # Publication/import provenance files are not audit-report envelopes.
    for path in sorted((ROOT / "docs/audits").glob("audit-*.json")):
        data = json.loads(path.read_text())
        jsonschema.validate(data, schema)
        ids = [item["id"] for key in ("findings", "observations") for item in data[key]]
        markdown = path.with_suffix(".md").read_text()
        if len(set(ids)) != len(ids) or not all(identifier in markdown for identifier in ids):
            raise AssertionError("paired report identifiers disagree: " + path.name)
        result.append(path.name)
    if len(result) != 7:
        raise AssertionError("unexpected historical report inventory")
    print(json.dumps({"outcome": "passed", "reports": result,
                      "limitation": "Envelope/identifier consistency only, not historical checks."}))


if __name__ == "__main__":
    main()
