module

public import Sarkozy.SpectralD.SmallMatrices.C6
public import Sarkozy.SpectralD.SmallFast.LyFF

/-! Kernel checks for the lyFF tail cut. -/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

theorem lyFF_models : ModelChecks .lyFF :=
  lyFF_modelChecks

theorem lyFF_tests : TestChecks .lyFF :=
  lyFF_testChecks

theorem lyFF_residuals : ResidualChecks .lyFF :=
  lyFF_residualChecks

theorem lyFF_rows : RowChecks .lyFF := by
  unfold RowChecks
  decide +kernel

end Sarkozy.SpectralD.SmallMatrices
