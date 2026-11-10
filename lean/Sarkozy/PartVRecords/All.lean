module

public import Sarkozy.PartVRecords.Frame
public import Sarkozy.PartVRecords.Gram
public import Sarkozy.PartVRecords.MatchingReserved
public import Sarkozy.PartVRecords.Prices
public import Sarkozy.PartVRecords.Polarization
public import Sarkozy.PartVRecords.OneStage
public import Sarkozy.PartVRecords.OneStageBlock
public import Sarkozy.PartVRecords.OneStageMarginals
public import Sarkozy.PartVRecords.OneStageNorms
public import Sarkozy.PartVRecords.OneStageDelta
public import Sarkozy.PartVRecords.OneStageSym
public import Sarkozy.PartVRecords.Eligible
public import Sarkozy.PartVRecords.Mixture
public import Sarkozy.PartVRecords.MergeRecords
public import Sarkozy.PartVRecords.MergeMarginals
public import Sarkozy.PartVRecords.MergeQueried
public import Sarkozy.PartVRecords.DenseComparison
public import Sarkozy.PartVRecords.SideFunction
public import Sarkozy.PartVRecords.TailMixing
public import Sarkozy.PartVRecords.Sanity

/-!
# Part V, the middle frame and records (umbrella)

* `Frame`: `def:record:frame` (`F_fold`, `E_fold`, `E_add`, `G`, `H`, `E_new`, `ρ`, `λ`, `δ_E`, `Ñ`,
  `Ñ₀` and the decomposition identities).
* `Gram`: `lem:record:gram`, the `2 × 2` bracket at `ι`, in the shape of (CP3).
* `MatchingReserved`: its hypothesis `MatchingReservedBound` at one prime, from the disjoint-triple
  bound (`sec:frontier:empty-triple-negative`(c)).
* `Prices`: `lem:record:middle-prices` and the two tags of `δ_E`.
* `Polarization`: `lem:middle-polarization`, (CP2)(a) at `ϑ₀`.
* `OneStage`: `lem:record:one-stage-folded-e`(a), (b) and the one-prime replacement law of (e).
* `OneStageNorms`, `OneStageDelta`, `OneStageSym`: part (c) at one prime (`‖𝒦₊‖ ≤ (√q + 3)/(q - 3)`,
  `‖Δ‖ ≤ k_new(p) r`, `‖Sym Δ‖ = 1/(p - 2)` attained at the sector contrast).
* `OneStageBlock`, `OneStageMarginals`: part (e) on a block (the block replacement, its acceptance
  of `𝓔₆`, its half laws, and the frame of a middle block).
* `Eligible`: `def:record:eligible`, repairs and record differences, `eq:record:zero-marginal`.
* `Mixture`: `def:record:mixture`, the signed whole-block fold record.
* `MergeRecords`, `MergeMarginals`, `MergeQueried`: `def:merge-records`, the merge replacements,
  their acceptance, their half marginals and their queried pairs (`lem:merge-repair`, first
  sentence).
* `DenseComparison`: `def:dense-comparison`, the softened laws.
* `SideFunction`: `def:side-function`, the auxiliary sides.
* `TailMixing`: `lem:record:tail-mixing`, (R4) for the tail laws.
* `Sanity`: toy instances of the new hypothesis bundles.
-/
