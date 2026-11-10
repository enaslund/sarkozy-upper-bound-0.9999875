module

public import Sarkozy.SpectralD.SmallMatrices.C4
public import Sarkozy.SpectralD.SmallFast.LyLF

/-! Kernel checks for the lyLF tail cut. -/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

theorem lyLF_models : ModelChecks .lyLF :=
  lyLF_modelChecks

theorem lyLF_tests : TestChecks .lyLF :=
  lyLF_testChecks

theorem lyLF_residuals : ResidualChecks .lyLF :=
  lyLF_residualChecks

theorem lyLF_rows : RowChecks .lyLF := by
  unfold RowChecks
  decide +kernel

end Sarkozy.SpectralD.SmallMatrices
