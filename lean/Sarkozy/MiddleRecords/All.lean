module

public import Sarkozy.MiddleRecords.TwoFeature
public import Sarkozy.MiddleRecords.Channels
public import Sarkozy.MiddleRecords.Mirror
public import Sarkozy.MiddleRecords.MirrorKernel
public import Sarkozy.MiddleRecords.RectStar
public import Sarkozy.MiddleRecords.EOrthogonal
public import Sarkozy.MiddleRecords.EOrthogonalBound
public import Sarkozy.MiddleRecords.EOrthogonalSym
public import Sarkozy.MiddleRecords.ActualFeatures
public import Sarkozy.MiddleRecords.ActualFeaturesOps
public import Sarkozy.MiddleRecords.ActualFeaturesA3
public import Sarkozy.MiddleRecords.ActualFeaturesA3V0
public import Sarkozy.MiddleRecords.ActualFeaturesNorms
public import Sarkozy.MiddleRecords.ActualFeaturesSynthesis
public import Sarkozy.MiddleRecords.Geometry
public import Sarkozy.MiddleRecords.OneStageCert
public import Sarkozy.MiddleRecords.OldFCapCert
public import Sarkozy.MiddleRecords.MergePrices
public import Sarkozy.MiddleRecords.QueriedPairs
public import Sarkozy.MiddleRecords.ComparisonPrices
public import Sarkozy.MiddleRecords.AcceptingC2
public import Sarkozy.MiddleRecords.MatchingCoefficients
public import Sarkozy.MiddleRecords.CollisionMatrix
public import Sarkozy.MiddleRecords.CollisionSchur
public import Sarkozy.MiddleRecords.Sanity
public import Sarkozy.MiddleRecords.PieceCompletion

/-!
# Part V, the middle records of section 21 (umbrella)

`paper/sections/21_middle_records.tex`:
* `TwoFeature` — `lem:two-feature-spectrum` (in full, abstract);
* `Channels`, `Mirror`, `MirrorKernel` — the Paley channels, `eq:middle:transpose`, and
  `lem:mirror` ((a), (b), (d) in full; (c): the kernel identity `L_p = A_⋆V₀^* - V₀A_⋆^*` on
  `L²(ν_F)` and the norm bound given the Gram data);
* `RectStar` — `lem:record:projected-nonstar`(b), the Gram of a rectangular star, and the
  independent-label part of `lem:record:e-orthogonal`(a);
* `EOrthogonal`, `EOrthogonalBound`, `EOrthogonalSym` — `lem:record:e-orthogonal`(a), (b), and
  (c) given the decomposition of `lem:record:e-law`(c), (d);
* `ActualFeatures`, `ActualFeaturesOps`, `ActualFeaturesA3`, `ActualFeaturesA3V0`,
  `ActualFeaturesNorms`, `ActualFeaturesSynthesis` — `lem:actual-features`(a), (b), the four Gram
  identities of (c) and `‖A₁‖ = ‖A₂‖ = r`, `‖A₃‖ ≤ r`, and the synthesis bound `Γ_A` of (d);
* `Geometry` — `cert:record:middle-geometry` for the two-layer fold and matching records;
* `OneStageCert` — `cert:record:one-stage`, the explicit part (endpoint values, monotonicity,
  gates);
* `OldFCapCert` — `cert:record:old-f-cap` at `Q₃` (`e_o`, `H̄_X`, `k_D(Q₃, 585)`, `n_X = 34`);
* `MergePrices` — `cor:merge-repair` from the bounds of `lem:merge-repair`, and
  `cert:merge-coefficients` at `Q₃`;
* `QueriedPairs` — the transitivity argument of section 21 for uniform queried pairs, with a
  cross-check on V3's first-coordinate merge replacement;
* `ComparisonPrices` — `lem:middle-comparison-prices` (decomposition, variation, prices,
  auxiliary prices);
* `AcceptingC2`, `MatchingCoefficients`, `CollisionMatrix` (W6's fork) —
  `lem:record:accepting-c2`, the arithmetic of `lem:record:exact-marginal-e` and
  `lem:oct24:matching-star`, and the matrix step of `lem:record:conditional-collision`(d);
* `CollisionSchur` — `lem:record:conditional-collision`(a);
* `Sanity` — toy instances of the new bundles.
-/
