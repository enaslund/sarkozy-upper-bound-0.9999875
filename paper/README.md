# Reading the paper

For Hexagon, upload **[hexagon-standalone.tex](hexagon-standalone.tex)**
under that exact name. Its matching [PDF](hexagon-standalone.pdf) is directly
beside it in `paper/`. This is the only single-file upload; no copying or
renaming is required. It includes the text-extraction repair and the preview's
working PDF configuration. See [PUBLICATION.md](PUBLICATION.md) for checks and
build instructions.

The downloaded `hexagon-preview-026c6d05e1a9.pdf` is historical diagnostic
evidence: it lacks the Unicode repair and does not match the current local PDF.

[main.pdf](main.pdf) is the complete manuscript. The TeX entry point is
[main.tex](main.tex). The single-file export
contains the full paper, bibliography and vector diagram and initializes
references from the verified build to reduce compilation passes.
[hexagon-source.zip](hexagon-source.zip) retains the modular sources and figure.

| Part | Content |
| --- | --- |
| I | Main result, proof outline and local construction |
| II | Analytic framework, reflection positivity and the square kernel |
| III | Comparison theorem and its estimates |
| IV | Counting, correlations, spectra, character sums and extraction |
| V | Construction, local estimates, density induction and final closing |
| VI | Development, obstructions and scope of the argument |
| Appendices A–F | External inputs, finite Peyre theorem, kernel proof, certificates, data and the earlier OpenAI exponent |

The numerical conclusion for the main theorem is assembled in
[32_four_routes_closing.tex](sections/32_four_routes_closing.tex).
Earlier numerical tables describe intermediate constructions and are retained
as part of the manuscript. Source filenames retain their existing numbering;
the input order in `main.tex` determines the printed order.

The historical verification packages cited in the appendices are not part of
this initial release. Their names are retained as references in the finished
paper, rather than as runnable commands for this repository. The Lean
companion is described separately in [lean/README.md](../lean/README.md).

See [PUBLICATION.md](PUBLICATION.md) for build and upload instructions.
