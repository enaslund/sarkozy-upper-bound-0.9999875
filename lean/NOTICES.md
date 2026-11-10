# Reused proof material

The square-difference predicate and square-step preservation proofs in
[Definitions.lean](Sarkozy/Definitions.lean) adapt
`OAI/Combinatorics/SquareDifference/GaussSum.lean` and `ResidueLift.lean` from
[OpenAI's math repository at revision 1581d4c](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SquareDifference).
The root-extraction and density-to-cardinality proofs in
[PowerBounds.lean](Sarkozy/PowerBounds.lean) adapt `Main.lean` from that revision.
The one-cut Cauchy–Schwarz and regularized Hölder arguments in
[Reflection/Basic.lean](Sarkozy/Reflection/Basic.lean) and
[Reflection/Holder.lean](Sarkozy/Reflection/Holder.lean) adapt `MarkedTuples.lean`.
The mean-to-energy argument in the latter adapts `AffineTuples.lean`.
The cut-kernel and positive semidefinite matrix arguments in
[Reflection/Matrix.lean](Sarkozy/Reflection/Matrix.lean) adapt `WordReflection.lean`.
The point-mass expansion and tensor-law arguments in
[Reflection/Tensor.lean](Sarkozy/Reflection/Tensor.lean) adapt `MarkedTuples.lean`
and `WordReflection.lean`.
The general Walsh-moment and symmetrization arguments in
[FourierArithmetic/Walsh.lean](Sarkozy/FourierArithmetic/Walsh.lean) adapt
`LiftMoments.lean` from the same revision. Its unrelated upstream imports
are replaced with direct mathlib imports.
The frequency-spacing, arithmetic progression, conditional Parseval, and
subpower moment proofs in
[FourierArithmetic/ResidueMoments.lean](Sarkozy/FourierArithmetic/ResidueMoments.lean)
adapt `RationalLift.lean` from that revision, with no dependence on the
upstream reference law or existential exponent theorem.
The kernel estimate in [Kernel/](Sarkozy/Kernel/) (added on 1 November 2026) ports
`PrimeGauss.lean`, `SievedFourier.lean`, `PrimaryKernel.lean`, `CompleteWeights.lean`,
`CircleDistance.lean`, `PhaseBounds.lean`, `RationalApproximation.lean`, `FiniteKernel.lean`,
`UniformRates.lean` and `DualCoordinates.lean` from the same revision.
- **Pruning.** Declarations outside the dependency closure of the kernel theorems were
  removed. The rest are unchanged apart from the namespace.
- **Adapted arguments.** The bilinear (Plancherel) and rate arguments of `DualCoordinates.lean`
  and `UniformRates.lean` are adapted in `Pairing.lean`, `RatesTwentieth.lean`,
  `GeneralKernel.lean` and `AdmissibleRates.lean`/`Admissible.lean`.
- **New material.** The root classes for non-squarefree moduli, the partial-fraction
  coefficient comparison, the paper's normalizations and the symbolic exponents.

The fibre-scale freeze lemmas in [Functional/FibreScale.lean](Sarkozy/Functional/FibreScale.lean)
follow the ideas of `squareStep_padded_sum`, `fiber_squareStep_lift` and
`liftPiece_frozen_complete` in `ResidueLift.lean`. They were rewritten for one-based intervals,
a general square step and prime-power coordinates; no code was copied verbatim.

The upstream code is distributed under the [Apache License 2.0](LICENSE.openai).
The original source files contain no separate copyright notice.

Changes made here: the namespace and interfaces are specific to this paper;
the root extraction accepts a positive real degree; the density factor is
divided out with a separate zero-density case; and the final interval embedding
uses the selected fixed block scale. These files also contain new definitions
and proofs for the explicit parameters and conclusions.
The reflection arguments are stated for arbitrary finite cuts, then specialized
to the paper's explicit 72-slot array, rather than the upstream word-slot
construction. All adapted material has been ported to the explicit module
system and the pinned compiler and mathlib versions.

The project uses Lean 4.35.0-rc3 and the mathlib revision pinned in
`lakefile.lean` and `lake-manifest.json`. It does not import or claim to
strengthen the upstream existential power-saving theorem. No upstream
repository access is needed to build the adapted proofs; Lake fetches mathlib
and its dependencies.

Development commentary has been removed from selected source comments for
this publication copy. Definitions, theorem statements and proof code are
unchanged.
