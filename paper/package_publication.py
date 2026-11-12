#!/usr/bin/env python3
"""Build and test a self-contained Hexagon TeX upload, then install the PDF.

Run from any directory: python3 -B paper/package_publication.py
Only the manuscript's TeX/BibTeX closure and its generated figure enter the
ZIP. The extracted ZIP is compiled independently, with no repository paths.
The default Hexagon upload is hexagon-standalone.tex, with full PDF navigation.
The basic-file source/PDF are a frozen fallback and are never overwritten.
Requires TeX Live, Poppler utilities and Python pikepdf.
"""
from pathlib import Path
from hashlib import sha256
import json
import os
import re
import shutil
import subprocess
import tempfile
import zipfile

import build
import submission

PAPER = Path(__file__).resolve().parent
RECORD = PAPER/'build_record.json'


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def command(args, cwd):
    env = dict(os.environ, SOURCE_DATE_EPOCH='1794268800', FORCE_SOURCE_DATE='1')
    result = subprocess.run(args, cwd=cwd, env=env, capture_output=True, text=True, errors='replace')
    if result.returncode:
        raise RuntimeError(' '.join(map(str, args))+'\n'+result.stdout[-6000:]+result.stderr[-1000:])
    return result.stdout


def package():
    basic = json.loads((PAPER/'publication_manifest.json').read_text())['basic_fallback']
    basic_files = {basic['source']: basic['sha256'], basic['pdf']: basic['pdf_sha256']}
    for name, expected in basic_files.items():
        assert digest(PAPER/name) == expected, f'Preserved basic fallback changed: {name}'
    with tempfile.TemporaryDirectory(prefix='sarkozy-publication-') as tmp:
        work = Path(tmp)
        compiled = work/'built'
        build.build(compiled)
        record = json.loads((compiled/'build_record.json').read_text())
        closure = build.closure()
        assert {str(p.relative_to(PAPER.parent)): h for p, h in closure.items()} == record['closure']
        files = {str(path.relative_to(PAPER)): path.read_bytes() for path in closure}
        files['figures/dependency_graph.pdf'] = (compiled/'figures/dependency_graph.pdf').read_bytes()
        assert all(Path(name).suffix in ('.tex', '.bib', '.pdf') for name in files)
        archive = work/'hexagon-source.zip'
        with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as bundle:
            for name, raw in sorted(files.items()):
                info = zipfile.ZipInfo(name, date_time=(2026, 11, 10, 0, 0, 0))
                info.compress_type = zipfile.ZIP_DEFLATED
                info.external_attr = 0o100644 << 16
                bundle.writestr(info, raw)
        expanded = sum(map(len, files.values()))
        assert archive.stat().st_size <= 100*2**20
        assert expanded+archive.stat().st_size <= 250*2**20
        upload = work/'upload'
        with zipfile.ZipFile(archive) as bundle:
            assert bundle.testzip() is None
            bundle.extractall(upload)
        latex = ['pdflatex', '-interaction=nonstopmode', '-halt-on-error', 'main.tex']
        command(latex, upload)
        command(['bibtex', 'main'], upload)
        command(latex, upload)
        command(latex, upload)
        for _ in range(2):
            log = (upload/'main.log').read_text(errors='replace')
            if 'Label(s) may have changed' not in log and 'Rerun to get' not in log:
                break
            command(latex, upload)
        log = (upload/'main.log').read_text(errors='replace')
        problems = [line for line in log.splitlines() if any(term in line for term in build.REJECT)]
        assert not problems, problems
        # Compare rendered text, allowing PDF metadata and creation times to differ.
        text_built = command(['pdftotext', '-layout', str(compiled/'main.pdf'), '-'], work)
        text_upload = command(['pdftotext', '-layout', 'main.pdf', '-'], upload)
        assert text_built == text_upload, 'Uploaded sources produce different text'
        pages = int(re.search(r'Pages:\s+(\d+)', command(['pdfinfo', 'main.pdf'], upload)).group(1))
        assert pages == record['pages']
        upload_text = build.check_pdf_text(upload/'main.pdf', pages)
        single = work/'standalone'
        standalone = submission.verify(PAPER, compiled, single, command)
        assert standalone['pages'] == pages
        assert build.closure() == closure, 'Sources changed while packaging'
        for path, expected in closure.items():
            assert sha256(files[str(path.relative_to(PAPER))]).hexdigest() == expected
        for name, expected in basic_files.items():
            assert digest(PAPER/name) == expected, f'Preserved basic fallback changed: {name}'
        shutil.copy2(compiled/'main.pdf', PAPER/'main.pdf')
        shutil.copy2(compiled/'figures/dependency_graph.pdf', PAPER/'figures/dependency_graph.pdf')
        shutil.copy2(archive, PAPER/'hexagon-source.zip')
        shutil.copy2(single/'hexagon-standalone.tex', PAPER/'hexagon-standalone.tex')
        shutil.copy2(single/'output/paper.pdf', PAPER/'hexagon-standalone.pdf')
        RECORD.parent.mkdir(parents=True, exist_ok=True)
        RECORD.write_text(json.dumps(record, indent=2)+'\n')
        manifest = dict(status='PASS_CLEAN_BUILD_AND_EXTRACTED_UPLOAD',
            pages=pages, main='main.tex', pdf='main.pdf', pdf_sha256=digest(PAPER/'main.pdf'),
            archive='hexagon-source.zip', archive_sha256=digest(PAPER/'hexagon-source.zip'),
            archive_bytes=archive.stat().st_size, expanded_bytes=expanded,
            files_sha256={name: sha256(raw).hexdigest() for name, raw in sorted(files.items())},
            upload_verification=dict(clean_final_log=True, identical_rendered_text=True,
                structured_text=upload_text,
                pages=pages, build_commands=['pdflatex main.tex', 'bibtex main',
                                             'pdflatex main.tex', 'pdflatex main.tex']),
            standalone_upload=standalone,
            basic_fallback=basic,
            package_script_sha256=digest(Path(__file__)))
        (PAPER/'publication_manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
        print(json.dumps({k: v for k, v in manifest.items() if k != 'files_sha256'}, indent=2))


if __name__ == '__main__':
    package()
