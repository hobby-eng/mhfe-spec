"""Create labelled contact sheets from the current PDF build's page rasters.

Run after node scripts/build-pdfs.mjs. Requires Pillow from the existing runtime.
All files are local ignored audit evidence. Contact sheets support visual review;
they do not establish that small mathematical glyphs were rendered correctly.
"""

import hashlib
import json
from pathlib import Path

from PIL import Image, ImageDraw

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / 'docs/audits/AUD-010-evidence'
BUILD = ROOT / 'output/documents'


def main():
    verification = json.loads((BUILD / 'verification.json').read_text())
    candidates = sorted(BUILD.glob('build-*'), key=lambda p: p.stat().st_mtime)
    expected = (BUILD / 'verification.json').read_bytes()
    matching = [path for path in candidates
                if (path / 'verification.json').is_file()
                and (path / 'verification.json').read_bytes() == expected]
    if verification['status'] != 'pass' or not matching:
        raise RuntimeError('no successful build matches the current verification record')
    source = matching[-1]
    for document in verification['documents']:
        path = source / document['file']
        if hashlib.sha256(path.read_bytes()).hexdigest() != document['sha256']:
            raise RuntimeError('per-attempt PDF hash differs from verification record')
    records = []
    for document in verification['documents']:
        stem = Path(document['file']).stem
        pages = len(document['pages'])
        for first in range(1, pages + 1, 12):
            sheet = Image.new('RGB', (1440, 1620), 'gray')
            draw = ImageDraw.Draw(sheet)
            numbers = list(range(first, min(first + 12, pages + 1)))
            for index, page in enumerate(numbers):
                path = source / f'{stem}-after-{page}.png'
                picture = Image.open(path).convert('RGB')
                picture.thumbnail((350, 500))
                x, y = (index % 4) * 360, (index // 4) * 540
                sheet.paste(picture, (x, y + 24))
                draw.text((x + 5, y + 5), f'{stem}: page {page}', fill='white')
            target = OUT / f'{stem}-contact-{first:03}.png'
            sheet.save(target)
            records.append({'file': str(target.relative_to(ROOT)), 'pages': numbers,
                            'sha256': hashlib.sha256(target.read_bytes()).hexdigest()})
    (OUT / 'contact-sheets.json').write_text(json.dumps({
        'buildDirectory': str(source.relative_to(ROOT)),
        'verificationSha256': hashlib.sha256((BUILD / 'verification.json').read_bytes()).hexdigest(),
        'sheets': records}, indent=2) + '\n')
    print(json.dumps({'build': str(source.relative_to(ROOT)), 'sheets': len(records),
                      'pages': sum(len(item['pages']) for item in records)}))


if __name__ == '__main__':
    main()
