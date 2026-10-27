"""Replay three published repair cases with the frozen independent AUD-007 decoder."""

import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]


def main():
    path = ROOT / 'docs/audits/AUD-007-harnesses/vectors_probe.py'
    spec = importlib.util.spec_from_file_location('audit007_vectors', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    inputs = module.CapturedInputs()
    wordlist = (ROOT.parent / 'workingspace/cargo/registry/src/'
                'index.crates.io-1949cf8c6b5b557f/bip39-3.0.0/src/language/english.rs')
    words = module.Bip39(inputs.read(wordlist))
    result = module.repair_examples(inputs, words)
    if inputs.changed():
        raise RuntimeError('input changed during replay')
    print(json.dumps({'cases': result, 'inputHashes': inputs.hashes(),
                      'argon2Recomputed': False}, indent=2))


if __name__ == '__main__':
    main()
