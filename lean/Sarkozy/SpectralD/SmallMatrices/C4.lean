module

public import Sarkozy.SpectralD.SmallMatrices.C3
public import Sarkozy.SpectralD.SmallFast.ChLE2

/-! Kernel checks for the chLE2 tail cut. -/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

theorem chLE2_models : ModelChecks .chLE2 :=
  chLE2_modelChecks

theorem chLE2_tests : TestChecks .chLE2 :=
  chLE2_testChecks

theorem chLE2_residuals : ResidualChecks .chLE2 :=
  chLE2_residualChecks

theorem chLE2_rows : RowChecks .chLE2 := by
  unfold RowChecks
  decide +kernel

end Sarkozy.SpectralD.SmallMatrices
