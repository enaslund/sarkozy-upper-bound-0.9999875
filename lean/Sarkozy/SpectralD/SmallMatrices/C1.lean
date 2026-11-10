module

public import Sarkozy.SpectralD.SmallMatrices.C0
public import Sarkozy.SpectralD.SmallFast.ChLF1

/-! Kernel checks for the chLF1 tail cut. -/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

theorem chLF1_models : ModelChecks .chLF1 :=
  chLF1_modelChecks

theorem chLF1_tests : TestChecks .chLF1 :=
  chLF1_testChecks

theorem chLF1_residuals : ResidualChecks .chLF1 :=
  chLF1_residualChecks

theorem chLF1_rows : RowChecks .chLF1 := by
  unfold RowChecks
  decide +kernel

end Sarkozy.SpectralD.SmallMatrices
