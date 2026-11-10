# Publication files

For Hexagon, use the revised [hexagon-submit.tex](hexagon-submit.tex) and
inspect its matching [hexagon-submit.pdf](hexagon-submit.pdf). Both are directly
in `paper/`. This revision repairs invalid characters in the PDF's extracted
mathematical text while preserving the printed pages. The preceding static
version passed Hexagon's preview but failed the final identifier-stamping step
with `text_extraction_failed`. The repaired version still needs a hosted retry.
If replacing the staged source, rename `hexagon-submit.tex` to
`hexagon-standalone.tex` so it replaces the existing file.

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

The preceding static submission passed Hexagon's private preview and rendered
correctly. Final submission then failed with `text_extraction_failed` while
applying the repository-controlled identifier stamp. This is a later processing
stage than the earlier `invalid_generated_pdf` preview rejection. Neither
message exposes Hexagon's internal parser or its detailed failure.

A local audit reproduced a concrete extraction defect in the accepted static
PDF: 1,194 XML-invalid C0 control characters across 324 pages. For example,
`pdftotext -f 12 -l 12 -bbox-layout paper/hexagon-submit.pdf -` on the preceding
version exited successfully but wrote malformed XHTML. The first failure was
an unmapped large delimiter. All fonts reported a Unicode map, but the Latin
Modern math-extension font's map omitted these glyphs. Successful compilation,
PDF syntax validation and a zero exit status from `pdftotext` did not detect it.

[math_unicode.tex](math_unicode.tex) now supplies font-specific Unicode mappings
for all four sizes of parentheses, brackets, floors, ceilings, braces, angle
brackets and slashes, plus the two vertical delimiter pieces. These mappings
only affect the extracted text layer. They do not change glyph shapes, metrics,
page contents or mathematical source. The mapping is shared by the manuscript
and diagram and is inlined into both single-file exports. It follows pdfTeX's
[documented `tfm:` glyph-mapping mechanism](https://ctan.math.washington.edu/tex-archive/systems/doc/pdftex/manual/pdftex-a.pdf).

The repaired static PDF has zero invalid control characters, and its complete
bounding-box XHTML parses successfully for all 603 pages. Comparison with the
preceding static PDF found identical page content streams and page dimensions;
the only changed PDF stream is the math font's Unicode map. All 2,345 label and
citation records remain unchanged. The new build check rejects the preceding
PDF and accepts the repaired one. This fixes a demonstrated defect relevant to
text extraction; it does not establish that Hexagon uses the same parser or
that its final stamping stage will now succeed.

Every manuscript, extracted-ZIP, standalone and static build now parses the
full `pdftotext -bbox-layout` output with an XML parser, checks the page count
and requires extracted words. The output is written to a temporary file and
parsed incrementally. The checks do not discard invalid characters or suppress
extraction errors. Results are recorded in the build and publication receipts
and [verification.json](preview-diagnostics/verification.json).

The static submission still omits PDF navigation using hyperref's `NoHyper`
environment and package options. The canonical [main.pdf](main.pdf) and
[hexagon-standalone.tex](hexagon-standalone.tex) retain links and bookmarks and
also include the text-layer repair. The revised canonical and static exports
have identical text after whitespace removal, 603 pages, and all 2,345 label
and citation records identical. Disabling links changes a few paragraph wraps;
the Unicode repair itself does not. Both use PDF 1.4 without object streams
or an automatic opening action. Exact sizes and hashes are in the receipts.

Validation uses final TeX Live 2025: pdfTeX 1.40.28, LaTeX 2025-11-01,
L3 2026-01-19 and longtable v4.24, matching the hosted log. The final manuscript
and submission logs have no package warnings, undefined references, duplicate
labels or overfull boxes. The 20 underfull horizontal and 43 underfull vertical
boxes are unchanged spacing diagnostics and have not been suppressed. The
separate diagram compilation reports that shell escape is disabled; it needs
no external conversion, and the warning is absent from the single-file upload.

The earlier repairs remain: text alternatives for PDF bookmarks, `\frac` in
place of two old `\over` expressions, disabled automatic EPS conversion and the
[longtable finite-shrink backport](https://github.com/latex3/latex2e/issues/1907).
The export seeds contents and references only on the first pass. The Unicode
repair preserves the mathematical content and the existing proof-review scope.

If the submission page still permits source replacement, upload the revised
complete source under the existing filename, apply **Process changes**, then
retry the preview and final processing offered by that page. If the record is
locked, use **Report a problem** on that record and ask Hexagon to enable source
replacement or rerun processing with the repaired file. A concise report is:

> The private preview succeeded, but final processing failed while applying
> the identifier stamp with `text_extraction_failed`. We reproduced malformed
> `pdftotext -bbox-layout` XHTML caused by missing Latin Modern delimiter
> mappings. The attached revised TeX fixes those mappings; all 603 pages now
> extract valid XHTML with unchanged printed content. Please allow the source
> replacement and rerun final processing, or provide the underlying extraction
> diagnostic if it still fails.

Include the actual revised source and its hash from the verification receipt.
These tools do not send a report, stamp a PDF or submit a deposit. The local
checks cannot reproduce Hexagon's private stamping implementation.
[Hexagon's compatibility page](https://hexagonmath.org/compilation) recommends
reporting processing failures that cannot be resolved locally.

After regenerating the canonical publication files, regenerate the static
submission with `pdflatex`, `pdftotext` and Python `pikepdf` available:

```sh
python3 -B paper/preview_diagnostics.py --verify
cp paper/preview-diagnostics/static/hexagon-standalone.tex paper/hexagon-submit.tex
cp paper/preview-diagnostics/static/paper.pdf paper/hexagon-submit.pdf
python3 -B paper/preview_diagnostics.py --check
```

The verification compiles the canonical and static sources and two simple
page-count controls in separate clean directories with shell escape disabled.
It checks PDF syntax, full structured text, manuscript text and references
before installing artifacts. The `--check` command checks saved hashes, not a
new compilation. The two simple controls contain no manuscript and are never
submission candidates. No hosted page, file-size or object-count limit has
been established.
