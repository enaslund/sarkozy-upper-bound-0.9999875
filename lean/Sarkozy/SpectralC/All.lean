module

public import Sarkozy.SpectralC.Fourier
public import Sarkozy.SpectralC.Gauss
public import Sarkozy.SpectralC.AffinePairs
public import Sarkozy.SpectralC.CovariantFields
public import Sarkozy.SpectralC.CouplingModes
public import Sarkozy.SpectralC.CouplingData
public import Sarkozy.SpectralC.PaleyStars
public import Sarkozy.SpectralC.DegreeOne
public import Sarkozy.SpectralC.Commutant
public import Sarkozy.SpectralC.PaleyOne
public import Sarkozy.SpectralC.PaleyA
public import Sarkozy.SpectralC.Intertwiners
public import Sarkozy.SpectralC.SmallPairs
public import Sarkozy.SpectralC.MatrixNorms
public import Sarkozy.SpectralC.DegreeOneEquiv
public import Sarkozy.SpectralC.GramComparison
public import Sarkozy.SpectralC.StarGrams
public import Sarkozy.SpectralC.HiddenFeature
public import Sarkozy.SpectralC.CondExp
public import Sarkozy.SpectralC.StarSingleton

/-!
# Brief C of `14_spectral` (WP-K)

Imports the `Sarkozy.SpectralC` package (`paper/sections/14_spectral.tex`):
* `lem:spec:gauss` (`Gauss`, on the Fourier basics of `Fourier`);
* `lem:spec:affpair` (a), (b), (d)(iii) (`AffinePairs`), (c) (`CovariantFields`), (d)(i)
  (`Commutant`), (d)(ii) (`Intertwiners`);
* `def:coupling-data` (`CouplingData`) and `lem:coupling-modes` (`CouplingModes`, `CouplingData`);
* `lem:spec:degone` (a) and the identities of (c) (`DegreeOne`), (b) and the bound of (c)
  (`MatrixNorms`), the norm equivalence of (c) (`DegreeOneEquiv`);
* `lem:spec:small` (`SmallPairs`, `DegreeOne.deltaX_swap`);
* `lem:spec2:gram` (`GramComparison`);
* `lem:spec2:paley` (a) (`PaleyA`) and (c) (`PaleyStars`); `lem:spec2:paley-one` and
  `lem:spec2:parity-transfer` (`PaleyOne`);
* `eq:star-traces` and `lem:general-star` (a), (b), (f) and the singleton claims
  (`StarGrams`);
* `lem:hidden-feature` (`HiddenFeature`, `CondExp`);
* the Gram of two covariant kernels from its traces, and the case `i ∈ S`, `|S| = 2` of
  `lem:general-star`(d) (`StarSingleton`).
-/
