module

public import Sarkozy.PartV.CoherentDictionaryBounds
public import Sarkozy.PartV.CoherentDictionarySymmetry
public import Sarkozy.PartV.CoherentDictionaryGeometry
public import Sarkozy.PartV.CoherentPinBounds
public import Sarkozy.PartV.CoherentCovarianceData
public import Sarkozy.PartV.CoherentDiagonalOperator
public import Sarkozy.PartV.CoherentDiagonalCollection
public import Sarkozy.PartV.KernelErrorSupport
public import Sarkozy.PartV.CoherentSquareSplit
public import Sarkozy.PartV.CoherentUnrestricted
public import Sarkozy.PartV.CoherentCancellationBound
public import Sarkozy.PartV.CoherentCollisionWeight
public import Sarkozy.PartV.CoherentChamberDensity
public import Sarkozy.PartV.CoherentChamberCollision
public import Sarkozy.PartV.CoherentChamberOperator

public import Sarkozy.PartV.Parameters
public import Sarkozy.PartV.BlockLaw
public import Sarkozy.PartV.Components
public import Sarkozy.PartV.MiddleReference
public import Sarkozy.PartV.PositiveRoot
public import Sarkozy.PartV.UpperReference
public import Sarkozy.PartV.NonVacuity
public import Sarkozy.PartV.Acceptance
public import Sarkozy.PartV.LayerCut
public import Sarkozy.PartV.Construction
public import Sarkozy.PartV.Blocks
public import Sarkozy.PartV.IndexIncrement
public import Sarkozy.PartV.TailCoefficients
public import Sarkozy.PartV.ChamberCut
public import Sarkozy.PartV.PositiveRootRP
public import Sarkozy.PartV.CoherentRP
public import Sarkozy.PartV.SixQuery
public import Sarkozy.PartV.LocalDomain
public import Sarkozy.PartV.Protection
public import Sarkozy.PartV.TailSplit
public import Sarkozy.PartV.MiddleInvariance
public import Sarkozy.PartV.TailFamily
public import Sarkozy.PartV.RootAffine
public import Sarkozy.PartV.LayerSwap

/-!
# Part V: the construction's definitions (umbrella)

`Parameters` (`def:record:parameters`, piece endpoints, upper bands), `BlockLaw` (block graph
laws), `Components` (pattern types, emissions, completions), `MiddleReference`
(`lem:front12:reference`), `PositiveRoot` (`def:positive-root`), `UpperReference`
(`def:upper-reference`, `def:tail-law`, the tail datum), `NonVacuity`, `Acceptance` (query
acceptance of the roots, positivity of the aligned components at `ϑ₀`), `LayerCut` (positivity
at `ι` by fold pairing, from the layer caps), `Construction` (the reference law of every atom,
`def:construction`(b)), `Blocks` (the block rules of `def:record:exact-blocks`), `IndexIncrement`
(the index increments of `def:construction`(a)), `TailCoefficients` (`C_j`, `S₇₂`, the nonroot
mass of the tail law), `ChamberCut` (the first-coordinate chamber cuts of the middle law through
`Sarkozy.FiveType`, and (R2) at every cut of the family), `PositiveRootRP` (`𝒢₆`-invariance of the
individual-square root and (R2) on the six pieces from `2³⁰` to `2⁴⁰`), `CoherentRP` (the same for
the coherent root of an invariant dictionary, on `[2⁴⁵, P₃)`), `SixQuery`
(`lem:six-query-retention`, the enumeration of the accepting upper records), `LocalDomain`
(`lem:record:local-domain`(i),(ii)), `Protection` (`lem:front12:reference`(iv)), `TailSplit`
(the root and remainder of the tail law, `lem:tail-law`(iii)), `MiddleInvariance` (the `R_h`- and
`𝒢₆`-invariance of the middle law, `lem:oct24:invariant-background`(i)), `TailFamily` (the fields
`invp` and `unifp` of `TheoremC.Reference` for the tail family), `RootAffine` ((R3) for the positive
roots and the middle law on every piece), `LayerSwap` (the layer-swap invariance of the middle law).
-/
