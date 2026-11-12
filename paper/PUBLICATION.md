# Publication files

Upload **[hexagon-standalone.tex](hexagon-standalone.tex)** to Hexagon under
that exact filename. Its matching **[hexagon-standalone.pdf](hexagon-standalone.pdf)**
is provided for inspection. No copying or renaming is required.

The default export includes the complete 603-page paper, bibliography and vector
diagram, with the same clickable contents, 291 bookmarks and 8,314 links as
[main.pdf](main.pdf). It retains the Unicode delimiter mappings, PDF 1.4
compatibility settings, longtable repair and PDF bookmark text corrections.
It needs standard TeX packages but no other manuscript files or shell escape.

The earlier navigation-free source and PDF are preserved byte-for-byte as
**[hexagon-standalone-basic-file.tex](hexagon-standalone-basic-file.tex)** and
[hexagon-standalone-basic-file.pdf](hexagon-standalone-basic-file.pdf).
This is a frozen fallback: packaging checks its hashes and never overwrites it.
Use the default `hexagon-standalone.tex` to try the richer PDF on Hexagon;
upload only that file, not both alternatives together.

On 12 November the author reported that the Hexagon bug was fixed and requested
restored navigation. The richer export is verified locally; its acceptance by
Hexagon still requires a new hosted preview. The old source/PDF and the
historical diagnostic record remain available for comparison.

The editable manuscript remains in [main.tex](main.tex) and its modular inputs;
[main.pdf](main.pdf) retains links and bookmarks for ordinary reading. The
[hexagon-source.zip](hexagon-source.zip) is the modular source archive for
reproducing that manuscript. Use the single-file export above for Hexagon.
The normal packaging command rebuilds the default export; the basic fallback
retains the earlier source and PDF.

The export seeds references, table widths and contents on the first pass only.
Ordinary auxiliary files are regenerated and take precedence on later passes.
It compiles in two PDFLaTeX passes on the tested final TeX Live 2025 toolchain.
The publication date remains 10 November 2026.

To regenerate and check the publication files from the repository root,
with TeX Live, Poppler utilities and Python `pikepdf` available:

```sh
make paper
make manifest
make check
```

The packaging command updates the single-file upload and matching PDF
automatically. To compile just the upload in a standard TeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape hexagon-standalone.tex
pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape hexagon-standalone.tex
```

Run another pass if requested, or use `latexmk -pdf`. Other TeX versions may
need additional passes. Python `pikepdf` is needed for the repository's build
validation, not for compiling the exported TeX on Hexagon.

The packaging command builds the manuscript, extracts and independently
compiles the modular ZIP, then compiles the single-file upload in a clean
directory with job name `paper` and shell escape disabled. The upload has
603 pages and the same 2,345 label and citation records as the manuscript.
Text comparisons remove whitespace only: inlining the diagram can affect
spatial extraction heuristics. Every link and bookmark must match `main.pdf`
in its source page, title and target as applicable; every internal destination
must resolve to the same page.

The upload must pass qpdf syntax checks, retain the manuscript navigation,
and produce valid `pdftotext -bbox-layout` XHTML for every page.
These checks run before the source and matching PDF are installed together.
[publication_manifest.json](publication_manifest.json) records the upload
source/PDF hashes, toolchain, text and reference comparisons, PDF checks and
structured-text results. The build also rejects unresolved references,
duplicate labels, overfull boxes and the previously repaired package warnings.

The earlier investigation found missing Unicode mappings for large mathematical
delimiters: a correctly rendered PDF could produce malformed extraction XHTML.
[math_unicode.tex](math_unicode.tex) repairs those mappings without changing
glyphs or mathematical content. The repair remains in both export variants.

[text-extraction-audit.json](text-extraction-audit.json) preserves the 10 November
investigation of intermittent preview failures and final identifier-stamping
failures, including the independent parser checks and source comparisons.
Its audited source/PDF now have the `hexagon-standalone-basic-file` names;
their hashes are unchanged. Its older hosted preview is a separate historical
artifact and lacks the Unicode repair. The author's 12 November report of a
Hexagon fix does not establish which internal error caused those failures.

[publication_manifest.json](publication_manifest.json) records the new default
export's own build, text, reference and navigation checks. The frozen fallback
retains its original verification receipt and original exporter hash. These
tools prepare local files; they do not submit a deposit or contact Hexagon.

Validation uses final TeX Live 2025: pdfTeX 1.40.28, LaTeX 2025-11-01,
L3 2026-01-19 and longtable v4.24, matching the hosted log. Final manuscript and
upload logs have no package warnings, undefined references, duplicate labels
or overfull boxes. The 20 underfull horizontal and 43 underfull vertical boxes
are unchanged layout diagnostics and have not been suppressed. The separate
diagram build reports disabled shell escape; it needs no external conversion.
That warning is absent from the single-file upload.

The earlier PDF 1.4 settings, bookmark text alternatives, `\frac` replacements,
disabled automatic EPS conversion and
[longtable finite-shrink repair](https://github.com/latex3/latex2e/issues/1907)
remain in place. The mathematical content and proof-review scope are unchanged.

The source archive contains only manuscript sources, bibliography and the
vector diagram. Lean material is distributed separately in the repository.
The paper and code are licensed under Apache 2.0, as specified in the root
[LICENSE](../LICENSE) and [NOTICE](../NOTICE).
