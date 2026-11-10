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

The latest hosted retry completed both PDFLaTeX passes, produced a 603-page
PDF, and ended with `Latexmk: All targets ... are up-to-date`. It had no
remaining glue errors or duplicate labels, but Hexagon still reported
“could not prepare a safe preview PDF.” The remaining failure is in preview
processing after PDF generation; its cause is not exposed in the compiler
log. [Hexagon's compatibility page](https://hexagonmath.org/compilation)
identifies the toolchain and recommends reporting failures that do not
reproduce locally. It does not document an additional PDF restriction.

The manuscript emits PDF 1.4 with ordinary objects and cross-reference tables,
without object streams or an automatic opening action. Internal links,
bookmarks and the vector diagram are retained. These are conservative
compatibility changes, not a confirmed explanation of Hexagon's rejection.
The PDF version is checked when packaging the single-file export. Hexagon's
custom format and preview processor are unavailable locally; acceptance still
requires a successful hosted preview.

The local warning audit uses final TeX Live 2025: pdfTeX 1.40.28,
LaTeX 2025-11-01, L3 2026-01-19 and longtable v4.24, matching the hosted log.
The main manuscript's 318 package warnings have been resolved: headings have
explicit text alternatives for PDF bookmarks, two old `\over` expressions use
`\frac`, and the unused automatic EPS converter is disabled. The final main
log has zero package warnings, undefined references, duplicate labels or
overfull boxes. It retains 20 underfull horizontal boxes and 43 underfull
vertical boxes: spacing diagnostics for the existing justified paragraphs
and page layout. These messages have not been suppressed. Compiling the
separate dependency figure also reports that shell escape is disabled; no
external conversion is requested. That warning is absent from the single-file
upload, which includes the drawing directly. Build receipts and the
publication manifest record the remaining warning counts.

The earlier longtable repair remains in place. It backports the upstream
v4.25 finite-shrink fix to older versions, as documented in
[LaTeX issue 1907](https://github.com/latex3/latex2e/issues/1907). Newer package
versions are left alone. The export initializes AMS contents indentation
without redefining labels, and packaging rejects a recurrence of the glue,
bookmark, fraction-command or unused-EPS warnings.

The revised PDF preserves all 603 pages' extracted text, and all 2,345 label
and citation records agree after removing the PDF-only title alternatives.
The generated single-file export is checked against the revised canonical
build with exact text and reference comparisons. Independent qpdf syntax
checks and MuPDF rendering also pass. These checks validate the local PDF;
they do not reproduce Hexagon's private preview processor.

If a fresh preview of this export still fails after both passes finish, use
Hexagon's **Report a problem** link and include the source file, its SHA-256
from the manifest, the compiler log and the exact preview message. Ask for
the PDF-processing error or resource limit: the displayed TeX log contains
no such diagnostic. No automatic report or submission is sent by these tools.
