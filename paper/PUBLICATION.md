# Publication files

The recommended upload is [hexagon-standalone.tex](hexagon-standalone.tex).
This single file includes every section, appendix, macro, numerical table,
the typeset bibliography, and the dependency diagram as vector drawing code.
It needs standard TeX packages but no other manuscript files or shell escape.
It produces the same 603-page paper, with the same labels, page references
and citations as [main.pdf](main.pdf).

The export initializes references, table widths and the table of contents
from a clean build. These are starting values: ordinary auxiliary files are
regenerated and take precedence on subsequent passes. Together with the
inline bibliography, this reduced a clean local build from four PDFLaTeX
passes plus BibTeX to two PDFLaTeX passes. Edit the modular sources and run
`make paper` to regenerate the export; do not maintain it separately.

The original [hexagon-source.zip](hexagon-source.zip), with `main.tex` as its
entry point, remains available. The publication date is fixed so later builds
do not silently change the date printed on the paper.

From the repository root:

```sh
make paper
make manifest
make check
```

The packaging command builds the dependency figure and manuscript in a
temporary directory, rejects unresolved references, citations and other final
log errors, then extracts and independently compiles the source ZIP. It also
compiles the single-file export in an empty directory with job name `paper`,
a separate output directory and shell escape disabled. The checks compare
extracted text and page counts, and compare all labels and citations for
the single-file export. Its text comparison uses `pdftotext -raw`, since
combining the diagram's font subsets changes spatial extraction heuristics.
[publication_manifest.json](publication_manifest.json) records the archive
members and hashes; [build_record.json](build_record.json) records the source
closure and PDF hash.

To compile the single-file upload:

```sh
pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape hexagon-standalone.tex
pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape hexagon-standalone.tex
```

Run another pass if requested, or use `latexmk -pdf`. A different TeX version
may need additional passes. The hosted Hexagon compiler has not been tested
by this packaging command.

The upload can also be compiled after extraction with ordinary TeX tools:

```sh
python3 -m zipfile -e paper/hexagon-source.zip _build/upload
cd _build/upload
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

Run another `pdflatex` pass if the log requests it. The archive contains only
the manuscript sources, bibliography and dependency figure. Lean files are
distributed in the repository. The paper and code are licensed under Apache
2.0, as specified in the root [LICENSE](../LICENSE) and [NOTICE](../NOTICE).

These commands prepare files locally. They do not create a Hexagon submission.

The original ZIP attempt was terminated during pass three. The subsequent
single-file attempt completed both passes and produced all 603 pages, but
Hexagon rejected the preview and highlighted `ignored error: Infinite glue
shrinkage`. This is a known interaction between longtable and LaTeX's page-mark
handling, documented in [LaTeX issue 1907](https://github.com/latex3/latex2e/issues/1907).
It does not make PDFLaTeX fail; the log alone does not establish why Hexagon's
subsequent preview processing rejected the PDF.

The manuscript now backports the upstream longtable v4.25 fix to older package
versions: page-break glue retains infinite stretch but uses finite shrink.
Newer longtable versions are left alone. The export also initializes AMS
contents indentation without producing duplicate-label warnings. In an
isolated installation of final TeX Live 2025, matching the reported pdfTeX
1.40.28, LaTeX 2025-11-01, L3 2026-01-19 and longtable v4.24, the original
file reproduced 21 glue diagnostics per pass and five initial duplicate
labels; the corrected file produced none. Both builds took two PDFLaTeX
passes and agreed on all 603 pages' extracted text and all 2,345 label and
citation records. All pages also rendered successfully with MuPDF.
The packaging checks reject these diagnostics, and the manifest records the
tested TeX versions. Hexagon's custom format and preview processor are not
available locally; hosted acceptance still requires a fresh preview.
