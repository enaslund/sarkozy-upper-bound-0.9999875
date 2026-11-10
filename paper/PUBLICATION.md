# Publication files

The submission source archive is [hexagon-source.zip](hexagon-source.zip),
with `main.tex` as its entry point. [main.pdf](main.pdf) is built from the same
sources. The publication date in the TeX source is fixed so that later builds
do not silently change the date printed on the paper.

From the repository root:

```sh
make paper
make manifest
make check
```

The packaging command builds the dependency figure and manuscript in a
temporary directory, rejects unresolved references, citations and other final
log errors, then extracts and independently compiles the source ZIP. It checks
that both compilations have identical rendered text and page counts.
[publication_manifest.json](publication_manifest.json) records the archive
members and hashes; [build_record.json](build_record.json) records the source
closure and PDF hash.

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
