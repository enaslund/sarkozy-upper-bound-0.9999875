module

public import Sarkozy.SpectralD.SmallMatrices.C2
public import Sarkozy.SpectralD.SmallFast.ChLE1

/-! Kernel checks for the chLE1 tail cut. -/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

theorem chLE1_models : ModelChecks .chLE1 :=
  chLE1_modelChecks

theorem chLE1_tests : TestChecks .chLE1 :=
  chLE1_testChecks

theorem chLE1_residuals : ResidualChecks .chLE1 :=
  chLE1_residualChecks

theorem chLE1_rows : RowChecks .chLE1 := by
  unfold RowChecks
  decide +kernel

end Sarkozy.SpectralD.SmallMatrices
