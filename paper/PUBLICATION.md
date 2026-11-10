# Publication files

The canonical upload is [hexagon-standalone.tex](hexagon-standalone.tex).
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

The latest hosted retry of this PDF 1.4 export completed both PDFLaTeX passes,
produced a 603-page, 7,323,843-byte PDF, and ended with
`Latexmk: All targets ... are up-to-date`. Its final pass had no TeX errors
or package warnings, but Hexagon still reported “could not prepare a safe
preview PDF.” The PDF profile changes have not resolved the hosted failure.
The remaining failure is in preview processing after PDF generation; its
cause is not exposed in the compiler log.
[Hexagon's compatibility page](https://hexagonmath.org/compilation) identifies
the toolchain and recommends reporting failures that do not reproduce locally.
It does not document an additional PDF restriction.

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

The [static diagnostic source](preview-diagnostics/static/hexagon-standalone.tex)
contains the complete manuscript with PDF links, bookmarks and page anchors
disabled using hyperref's supported `NoHyper` environment and package options.
It is a controlled diagnostic, with hosted acceptance still unconfirmed.
The canonical paper and upload remain unchanged by this experiment.

Local tests with the matching final TeX Live 2025 engine gave:

| Source | Pages | PDF bytes | PDF objects | Link annotations |
| --- | ---: | ---: | ---: | ---: |
| Canonical single-file export | 603 | 7,323,843 | 15,402 | 8,314 |
| Complete static diagnostic | 603 | 5,149,913 | 2,149 | 0 |
| Simple 603-page control | 603 | 397,456 | 1,943 | 0 |
| Simple one-page control | 1 | 31,872 | 16 | 0 |

Both complete versions have identical text after removing whitespace from
`pdftotext -raw` output, identical page counts and all 2,345 label and citation
records identical. A few paragraphs wrap differently when links are disabled.
All four PDFs pass qpdf syntax checks and have no final package warnings or
overfull boxes. The complete versions retain the same 63 underfull spacing
messages. [verification.json](preview-diagnostics/verification.json) records
source and PDF hashes, counts, toolchain and comparison results. This reproduces
the hosted PDF byte count, but not Hexagon's custom format or preview processor.
There is no confirmed page, file-size or object-count limit.

Before spending another preview, inspect the existing status response in your
browser: open Developer Tools (F12 in Chrome or Edge, Command-Option-I on macOS),
select **Network**, filter by `preview`, and refresh the failed preview page.
Select the GET request ending in `/preview`, without `/log`, `/check` or `/pdf`,
and open **Response**. Its JSON may contain an `errorCode` or a more specific
message. Read this response rather than copying request headers, cookies or
tokens. Refreshing and reading status do not request another compilation.

If the status response does not identify the cause, replace the staged source
with the static diagnostic, preserving the filename `hexagon-standalone.tex`,
and request one preview. Success would narrow the failure to PDF features or
processing resources affected by this change; it would not identify a specific
limit. If needed, the [603-page control](preview-diagnostics/pages-603/hexagon-standalone.tex)
and [one-page control](preview-diagnostics/pages-1/hexagon-standalone.tex) can
separately test simple documents. These two controls contain no manuscript
and must never be used for final submission. Restore the complete manuscript
after testing a control.

To regenerate and verify these diagnostics with `pdflatex`, `pdftotext` and
the Python package `pikepdf` available:

```sh
python3 -B paper/preview_diagnostics.py --verify
python3 -B paper/preview_diagnostics.py --check
```

The first command compiles all four versions in separate temporary directories
with shell escape disabled, then installs the diagnostic sources and receipt
only after the checks pass. The second checks saved source and receipt hashes;
it does not recompile. Regenerate the diagnostics after changing the canonical
export. Neither command calls Hexagon or changes the canonical publication files.

For Hexagon's **Report a problem** form, include the canonical source and its
SHA-256 from the publication manifest, the status JSON, the compiler log and
any controlled preview result. Ask for the PDF-processing diagnostic or resource
limit behind the rejection. No automatic report or submission is sent by these tools.
