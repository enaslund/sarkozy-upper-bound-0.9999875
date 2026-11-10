# An upper bound for square-difference-free sets

Publication materials for **An Upper Bound Exponent of 0.9999873 for
Square-Difference-Free Sets**, by Eric Naslund, prepared to accompany
publication in Hexagon Math.

For a set `A ⊆ {1, …, N}` with no two distinct elements differing by a
nonzero square, the paper proves

$$|A| \le C N^{0.9999873}.$$

The exact saving obtained in the paper is
`ε = 1814179 / 141970826000`. The repository name uses the slightly weaker
exponent `0.9999875`; the manuscript states the stronger bound above.

| Material | Entry point |
| --- | --- |
| Complete manuscript | [603-page PDF](paper/main.pdf) |
| Manuscript sources and reading guide | [paper/](paper/README.md) |
| TeX upload for Hexagon | [Single TeX file](paper/hexagon-standalone.tex) (recommended), [source ZIP](paper/hexagon-source.zip), and [build instructions](paper/PUBLICATION.md) |
| Partial Lean formalization | [lean/](lean/README.md) |
| What the formalization assumes | [Trust map](lean/TRUST_MAP.md) |

**The Lean companion is partial.** Its principal theorem establishes a bound
with exponent **0.99999**, conditional on explicit analytic and numerical
hypotheses and remaining statements from Part V. It does not constitute a
complete formal proof of the paper's exponent. The hypotheses and the exact
theorem are described in the trust map.

## Build and check

Python 3 and Poppler (`pdfinfo`, `pdftotext`, `pdfdetach`) are needed for the
release checks. Building the paper also requires TeX Live with `pdflatex`,
BibTeX and the packages imported by the manuscript. The Lean project pins its
compiler and mathlib dependency.

```sh
make check          # File inventory, hashes, local imports, archives and privacy checks
make paper          # Build the PDF and independently compile both TeX upload formats
make lean-check     # Build the partial formalization and audit its axiom dependencies
```

For a first Lean build, see [lean/README.md](lean/README.md). Its generated
certificates make this a substantial project. Build products and dependency
caches are excluded from version control.

## Scope of this release

This repository contains the complete manuscript, its standalone TeX sources,
and the companion's Lean definitions, proofs and embedded certificates.
Historical paths and verification commands cited in the manuscript refer to
the research record. Those historical Python/C++ verification packages are
**not included in this initial release** and their commands cannot be run here.
Building the PDF or checking the partial Lean companion does not replay all
of the paper's finite computations.

The manuscript retains its AI-use disclosure. Development transcripts,
working notes, orchestration scripts and earlier Git history are outside this
publication repository. Some development comments have been removed from the
Lean sources; definitions, statements and proof code are unchanged.

The [release manifest](release-manifest.json) records the published files and
their SHA-256 hashes. After intentional edits and regeneration, run
`make manifest` followed by `make check` to update and validate that inventory.

## License and citation

The paper, original code and documentation are licensed under
[Apache 2.0](LICENSE). [NOTICE](NOTICE) and
[lean/NOTICES.md](lean/NOTICES.md) preserve third-party attribution.
Citation metadata is in [CITATION.cff](CITATION.cff).
