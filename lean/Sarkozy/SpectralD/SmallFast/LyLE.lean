module

public import Sarkozy.SpectralD.SmallFast.Models

/-!
# Model, test and residual checks on codes for the lyLE tail cut

The code `code .lyLE` maps the half onto `range 18` (`lyLE_code_lt`, `lyLE_code_onto`,
`lyLE_code_inj`). Over the half, only the sign table and the adjacency masks of `G⁺` are
checked against the graph (`lyLE_sign_code`, `lyLE_adj_masks`). Everything else is checked on
codes: the model tables (`lyLE_models_code`), the test tables (`lyLE_tests_0`, `lyLE_tests_1`)
and, with upper triangular factor tables (`lyLE_factor_len`, `lyLE_factor_tri`) and symmetric
test tables (`lyLE_test_symm`), the residual row sums, one check for each `a` and `e`
(`lyLE_rows_00` to `lyLE_rows_12`). `modelChecks_of`, `testChecks_of` and
`residualChecks_of` assemble `ModelChecks .lyLE`, `TestChecks .lyLE` and `ResidualChecks .lyLE`.
The masks are generated, but they are checked here and not trusted.
-/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

open Finset Sarkozy.PartVLaws.FieldGraphs Sarkozy.SpectralD.Root

/-- The neighbours in `G⁺` of each code of the lyLE half, as bit masks of codes. -/
def lyLE_adjMasks : List ℕ :=
  [
    24960, 20800, 12480, 199680, 166400, 99840,
    24582, 20485, 12291, 196656, 163880, 98328,
    390, 325, 195, 3120, 2600, 1560
  ]

/-- The mask of the neighbours in `G⁺` of the code `x`. -/
def lyLE_adj (x : ℕ) : ℕ := maskTable lyLE_adjMasks x

theorem lyLE_code_lt : ∀ h : SmallCut.lyLE.data.cut.Half, code .lyLE h.1 < 18 := by
  decide +kernel

theorem lyLE_code_onto : ∀ x, x < 18 →
    ∃ h : SmallCut.lyLE.data.cut.Half, code .lyLE h.1 = x := by
  decide +kernel

theorem lyLE_code_inj : ∀ h₁ h₂ : SmallCut.lyLE.data.cut.Half,
    code .lyLE h₁.1 = code .lyLE h₂.1 → h₁ = h₂ := by
  decide +kernel

theorem lyLE_table_len :
    (signTable .lyLE).length = 18 ∧ ∀ a, (dTable .lyLE a).length = 18 := by
  decide +kernel

theorem lyLE_sign_code : ∀ i j : SmallCut.lyLE.data.cut.Half,
    edgeSign SmallCut.lyLE.edge SmallCut.lyLE.data.cut.flip i.1 j.1 =
      entry (signTable .lyLE) (code .lyLE i.1) (code .lyLE j.1) := by
  decide +kernel

theorem lyLE_adj_masks : ∀ i j : SmallCut.lyLE.data.cut.Half,
    (i ≠ j ∧ FiniteModel.Adj SmallCut.lyLE.edge SmallCut.lyLE.data.cut i j ↔
      (lyLE_adj (code .lyLE i.1) >>> code .lyLE j.1) % 2 = 1) := by
  decide +kernel

theorem lyLE_models_code : ∀ x, x < 18 → ∀ y, y < 18 →
    ModelCode .lyLE 18 lyLE_adj x y := by
  decide +kernel

theorem lyLE_modelChecks : ModelChecks .lyLE :=
  modelChecks_of .lyLE 18 lyLE_code_lt lyLE_code_onto lyLE_code_inj lyLE_table_len.1
    lyLE_sign_code lyLE_adj lyLE_adj_masks lyLE_models_code

theorem lyLE_tests_0 : ∀ e, ∀ x, x < 18 → ∀ y, y < 18 → TestCode .lyLE 0 e x y := by
  decide +kernel

theorem lyLE_tests_1 : ∀ e, ∀ x, x < 18 → ∀ y, y < 18 → TestCode .lyLE 1 e x y := by
  decide +kernel

theorem lyLE_tests_code : ∀ a e, ∀ x, x < 18 → ∀ y, y < 18 → TestCode .lyLE a e x y
  | 0, e => lyLE_tests_0 e
  | 1, e => lyLE_tests_1 e

theorem lyLE_testChecks : TestChecks .lyLE :=
  testChecks_of .lyLE 18 lyLE_code_lt lyLE_code_onto lyLE_code_inj lyLE_table_len.2
    lyLE_tests_code

theorem lyLE_factor_len : ∀ a e, (factorRealTable .lyLE a e).length = 18 ∧
    (factorImagTable .lyLE a e).length = 18 := by
  decide +kernel

theorem lyLE_factor_tri : ∀ a e, ∀ k, k < 18 → ∀ x, x < k →
    entry (factorRealTable .lyLE a e) k x = 0 ∧ entry (factorImagTable .lyLE a e) k x = 0 := by
  decide +kernel

theorem lyLE_test_symm : ∀ a e, ∀ x, x < 18 → ∀ y, y < 18 →
    entry (testRealTable .lyLE a e) x y = entry (testRealTable .lyLE a e) y x ∧
      entry (testImagTable .lyLE a e) x y = -entry (testImagTable .lyLE a e) y x := by
  decide +kernel

theorem lyLE_rows_00 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .lyLE 0 0 x y ≤ shift .lyLE 0 0 := by
  decide +kernel

theorem lyLE_rows_01 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .lyLE 0 1 x y ≤ shift .lyLE 0 1 := by
  decide +kernel

theorem lyLE_rows_02 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .lyLE 0 2 x y ≤ shift .lyLE 0 2 := by
  decide +kernel

theorem lyLE_rows_10 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .lyLE 1 0 x y ≤ shift .lyLE 1 0 := by
  decide +kernel

theorem lyLE_rows_11 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .lyLE 1 1 x y ≤ shift .lyLE 1 1 := by
  decide +kernel

theorem lyLE_rows_12 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .lyLE 1 2 x y ≤ shift .lyLE 1 2 := by
  decide +kernel

theorem lyLE_rows_code : ∀ a e, ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .lyLE a e x y ≤ shift .lyLE a e
  | 0, 0 => lyLE_rows_00
  | 0, 1 => lyLE_rows_01
  | 0, 2 => lyLE_rows_02
  | 1, 0 => lyLE_rows_10
  | 1, 1 => lyLE_rows_11
  | 1, 2 => lyLE_rows_12

theorem lyLE_residualChecks : ResidualChecks .lyLE :=
  residualChecks_of .lyLE 18 lyLE_code_lt lyLE_code_onto lyLE_code_inj lyLE_factor_len
    lyLE_factor_tri lyLE_test_symm lyLE_rows_code

end Sarkozy.SpectralD.SmallMatrices
