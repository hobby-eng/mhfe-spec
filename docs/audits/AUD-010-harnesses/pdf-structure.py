"""Strictly parse tracked and fresh PDFs and compare their extracted body text.

Requires the existing runtime's pypdf. No PDF is changed. Extracted-text equality
does not establish mathematical equivalence or replace full-size visual review.
"""

import hashlib
import json
from pathlib import Path
import re
import resource

from pypdf import PdfReader

ROOT = Path(__file__).resolve().parents[3]
resource.setrlimit(resource.RLIMIT_AS, (512 * 1024**2,) * 2)


def main():
    verification = json.loads((ROOT / 'output/documents/verification.json').read_text())
    result = []
    for document in verification['documents']:
        texts = []
        for directory in ('docs/pdf', 'output/documents'):
            path = ROOT / directory / document['file']
            reader = PdfReader(path, strict=True)
            if reader.is_encrypted:
                raise AssertionError('unexpected encrypted PDF')
            page_texts = [page.extract_text() for page in reader.pages]
            text = '\n'.join(page_texts)
            source_sha = hashlib.sha256((ROOT / document['source']).read_bytes()).hexdigest()
            if source_sha not in re.sub(r'\s+', '', text[:1600]):
                raise AssertionError('PDF header does not bind the current Markdown bytes')
            annotations = 0
            for page in reader.pages:
                for reference in page.get('/Annots', []):
                    annotation = reference.get_object()
                    annotations += 1
                    if annotation.get('/AA') or annotation.get('/A', {}).get('/S') in ('/JavaScript', '/Launch'):
                        raise AssertionError('unexpected active PDF action')
            # Force destination resolution, rather than only counting xref entries.
            destinations = reader.named_destinations
            for destination in destinations.values():
                reader.get_destination_page_number(destination)
            record = {'file': str(path.relative_to(ROOT)),
                      'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                      'pages': len(page_texts), 'annotations': annotations,
                      'namedDestinations': len(destinations), 'sourceSha256': source_sha,
                      'strictParsing': 'passed', 'textSha256': hashlib.sha256(text.encode()).hexdigest()}
            if directory == 'docs/pdf':
                record['requirementMarkers'] = len(re.findall(r'\b[A-Z]+-\d+\b', text))
            result.append(record)
            # Build revision can differ while source bytes remain identical.
            texts.append(re.sub(r'\s+', '', re.sub(r'revision\s+[0-9a-f]+', 'revision', text)))
        if texts[0] != texts[1]:
            raise AssertionError('tracked and fresh PDF extracted body text differs')
    print(json.dumps({'documents': result, 'trackedFreshTextEqualExceptBuildRevision': True,
                      'pypdf': __import__('pypdf').__version__}, indent=2))


if __name__ == '__main__':
    main()
