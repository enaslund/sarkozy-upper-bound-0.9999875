module

public import Sarkozy.SpectralD.SmallMatrices.C1
public import Sarkozy.SpectralD.SmallFast.ChLF2

/-! Kernel checks for the chLF2 tail cut. -/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

theorem chLF2_models : ModelChecks .chLF2 :=
  chLF2_modelChecks

theorem chLF2_tests : TestChecks .chLF2 :=
  chLF2_testChecks

theorem chLF2_residuals : ResidualChecks .chLF2 :=
  chLF2_residualChecks

theorem chLF2_rows : RowChecks .chLF2 := by
  unfold RowChecks
  decide +kernel

end Sarkozy.SpectralD.SmallMatrices
