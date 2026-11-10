module

public import Sarkozy.SpectralD.SmallMatrices.C5
public import Sarkozy.SpectralD.SmallFast.LyLE

/-! Kernel checks for the lyLE tail cut. -/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

theorem lyLE_models : ModelChecks .lyLE :=
  lyLE_modelChecks

theorem lyLE_tests : TestChecks .lyLE :=
  lyLE_testChecks

theorem lyLE_residuals : ResidualChecks .lyLE :=
  lyLE_residualChecks

theorem lyLE_rows : RowChecks .lyLE := by
  unfold RowChecks
  decide +kernel

end Sarkozy.SpectralD.SmallMatrices
