# Publication files

Upload **[hexagon-standalone.tex](hexagon-standalone.tex)** to Hexagon under
that exact filename. Its matching **[hexagon-standalone.pdf](hexagon-standalone.pdf)**
is provided for inspection. No copying or renaming is required.

This is the only single-file Hexagon export. It includes the complete paper,
bibliography and vector diagram, disables PDF navigation using the configuration
that passed the hosted preview, and includes the Unicode text-extraction repair.
It needs standard TeX packages but no other manuscript files or shell escape.

The editable manuscript remains in [main.tex](main.tex) and its modular inputs;
[main.pdf](main.pdf) retains links and bookmarks for ordinary reading. The
[hexagon-source.zip](hexagon-source.zip) is the modular source archive for
reproducing that manuscript. Use the single-file export above for Hexagon.
The temporary alternative export and diagnostic copies have been removed;
their checks are now part of the normal packaging command.

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
Text comparisons remove whitespace only: disabling links can rewrap a few
paragraphs, and inlining the diagram affects spatial extraction heuristics.

The upload must pass qpdf syntax checks, contain no link annotations or
bookmarks, and produce valid `pdftotext -bbox-layout` XHTML for every page.
These checks run before the source and matching PDF are installed together.
[publication_manifest.json](publication_manifest.json) records the upload
source/PDF hashes, toolchain, text and reference comparisons, PDF checks and
structured-text results. The build also rejects unresolved references,
duplicate labels, overfull boxes and the previously repaired package warnings.

The preceding submission passed Hexagon's private preview, then failed during
its final identifier-stamping step with `text_extraction_failed`. A local audit
found 1,194 XML-invalid control characters across 324 pages, caused by missing
Unicode mappings for large mathematical delimiters. `pdftotext` returned zero
while writing malformed XHTML, despite correct page rendering.

[math_unicode.tex](math_unicode.tex) supplies the missing font-specific mappings
for all four delimiter sizes and the two vertical delimiter pieces. The repaired
PDF has no invalid control characters and extracts valid XHTML across all
603 pages. The repair changes the font's Unicode map, with unchanged page
content and reference values; a 72-dpi comparison of all rendered pages also
matched. It is included directly in the single-file export.

The 10 November retry also reported `text_extraction_failed`. The two receipt
emails confirm that two source packages were received under the same identifier;
receipt and preview success do not establish successful final processing or
publication. The submission page now offers **Fix and resubmit** under that
identifier.

An audit of the downloaded hosted preview found that it still has the old
Unicode map. Its PDF creation time is 18:48:58 UTC, before the repair was
committed at 19:35 UTC. All 2,149 PDF objects match the earlier local PDF except
the metadata object; the trailer identifier also differs. Its bounding-box
XHTML contains the same 1,194 invalid control characters, first appearing on
page 12. Metadata alone cannot establish whether this preview came from an
earlier attempt or was reused during the latest one; the final-stage compiled
PDF has not been made available for comparison.

The current upload PDF passes full-document extraction with Poppler 25.03.0,
PDF.js 6.5.438, pypdf 7.0.1 and pdfminer.six 20260107. Poppler's bounding-box
XHTML parses across all 603 pages with zero invalid control characters.
[text-extraction-audit.json](text-extraction-audit.json) records the artifact
hashes and comparisons. The [downloaded hosted preview](hexagon-preview-026c6d05e1a9.pdf)
is retained as diagnostic evidence; it does not match the current local PDF.

Hexagon's stored source for the 20:08 package was then downloaded and compared:
it is **byte-for-byte identical** to the current `hexagon-standalone.tex`.
Both individual files have SHA-256
`038d18837786be84048785c35eed37a3884e64c26d29b367959e50d7736d3d8e`.
The received copy is preserved in commit
[dc43a8a](https://github.com/enaslund/sarkozy-upper-bound-0.9999875/commit/dc43a8a).
Its duplicate working-tree copy was removed after the comparison, retaining
one upload file. The receipt's **source-package** hash identifies a package
and must not be compared directly with this individual file hash.

An outdated upload is therefore ruled out for the latest failure. The current
source already contains the repair, and no further extraction defect has been
reproduced locally. The exact failure in Hexagon's stamping processor remains
unknown. Use **Report a problem** on the existing submission, include its
receipt and this audit, and request the extractor's command, version, exit
status, stderr, output size and applicable resource limits. Ask which compiled
PDF was processed and request reprocessing of the received package. A local
Node.js experiment failed with a 1 MiB stdout buffer and succeeded with 8 MiB;
the extracted plain text is 2,353,114 bytes. This is only a resource-limit
example, not evidence that Hexagon uses that implementation or limit.

The receipt means the source was received; the displayed processing failure
still needs attention. There is no evidence supporting another TeX change or
a new submission identifier. If Hexagon identifies a necessary source change,
**Fix and resubmit** can apply it to the existing identifier. These tools do
not submit a deposit or contact Hexagon.

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
