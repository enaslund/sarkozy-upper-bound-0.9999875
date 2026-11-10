module

public import Sarkozy.SpectralD.SmallMatrices.C7
public import Sarkozy.SpectralD.SmallFast.LyFE

/-! Kernel checks for the lyFE tail cut. -/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

theorem lyFE_models : ModelChecks .lyFE :=
  lyFE_modelChecks

theorem lyFE_tests : TestChecks .lyFE :=
  lyFE_testChecks

theorem lyFE_residuals : ResidualChecks .lyFE :=
  lyFE_residualChecks

theorem lyFE_rows : RowChecks .lyFE := by
  unfold RowChecks
  decide +kernel

end Sarkozy.SpectralD.SmallMatrices
