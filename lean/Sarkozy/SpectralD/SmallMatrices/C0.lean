module

public import Sarkozy.SpectralD.SmallMatrixDefs
public import Sarkozy.SpectralD.SmallFast.ChLL1

/-! Kernel checks for the chLL1 tail cut. -/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

theorem chLL1_models : ModelChecks .chLL1 :=
  chLL1_modelChecks

theorem chLL1_tests : TestChecks .chLL1 :=
  chLL1_testChecks

theorem chLL1_residuals : ResidualChecks .chLL1 :=
  chLL1_residualChecks

theorem chLL1_rows : RowChecks .chLL1 := by
  unfold RowChecks
  decide +kernel

end Sarkozy.SpectralD.SmallMatrices
