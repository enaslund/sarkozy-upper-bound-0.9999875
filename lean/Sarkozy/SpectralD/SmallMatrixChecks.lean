module

public import Sarkozy.SpectralD.SmallMatrices.C8

/-! All nine smaller tail cuts have verified integer matrix certificates. -/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

open Sarkozy.PartVLaws.FieldGraphs

theorem models (c : SmallCut) : ModelChecks c := by
  cases c
  · exact chLL1_models
  · exact chLF1_models
  · exact chLF2_models
  · exact chLE1_models
  · exact chLE2_models
  · exact lyLF_models
  · exact lyLE_models
  · exact lyFF_models
  · exact lyFE_models

theorem tests (c : SmallCut) : TestChecks c := by
  cases c
  · exact chLL1_tests
  · exact chLF1_tests
  · exact chLF2_tests
  · exact chLE1_tests
  · exact chLE2_tests
  · exact lyLF_tests
  · exact lyLE_tests
  · exact lyFF_tests
  · exact lyFE_tests

theorem residuals (c : SmallCut) : ResidualChecks c := by
  cases c
  · exact chLL1_residuals
  · exact chLF1_residuals
  · exact chLF2_residuals
  · exact chLE1_residuals
  · exact chLE2_residuals
  · exact lyLF_residuals
  · exact lyLE_residuals
  · exact lyFF_residuals
  · exact lyFE_residuals

theorem rows (c : SmallCut) : RowChecks c := by
  cases c
  · exact chLL1_rows
  · exact chLF1_rows
  · exact chLF2_rows
  · exact chLE1_rows
  · exact chLE2_rows
  · exact lyLF_rows
  · exact lyLE_rows
  · exact lyFF_rows
  · exact lyFE_rows

end Sarkozy.SpectralD.SmallMatrices
