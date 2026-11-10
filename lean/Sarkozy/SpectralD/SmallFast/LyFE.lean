module

public import Sarkozy.SpectralD.SmallFast.Models

/-!
# Model, test and residual checks on codes for the lyFE tail cut

The code `code .lyFE` maps the half onto `range 9` (`lyFE_code_lt`, `lyFE_code_onto`,
`lyFE_code_inj`). Over the half, only the sign table and the adjacency masks of `G⁺` are
checked against the graph (`lyFE_sign_code`, `lyFE_adj_masks`). Everything else is checked on
codes: the model tables (`lyFE_models_code`), the test tables (`lyFE_tests_0`, `lyFE_tests_1`)
and, with upper triangular factor tables (`lyFE_factor_len`, `lyFE_factor_tri`) and symmetric
test tables (`lyFE_test_symm`), the residual row sums, one check for each `a` and `e`
(`lyFE_rows_00` to `lyFE_rows_12`). `modelChecks_of`, `testChecks_of` and
`residualChecks_of` assemble `ModelChecks .lyFE`, `TestChecks .lyFE` and `ResidualChecks .lyFE`.
The masks are generated, but they are checked here and not trusted.
-/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

open Finset Sarkozy.PartVLaws.FieldGraphs Sarkozy.SpectralD.Root

/-- The neighbours in `G⁺` of each code of the lyFE half, as bit masks of codes. -/
def lyFE_adjMasks : List ℕ :=
  [
    384, 320, 192, 0, 0, 0,
    6, 5, 3
  ]

/-- The mask of the neighbours in `G⁺` of the code `x`. -/
def lyFE_adj (x : ℕ) : ℕ := maskTable lyFE_adjMasks x

theorem lyFE_code_lt : ∀ h : SmallCut.lyFE.data.cut.Half, code .lyFE h.1 < 9 := by
  decide +kernel

theorem lyFE_code_onto : ∀ x, x < 9 →
    ∃ h : SmallCut.lyFE.data.cut.Half, code .lyFE h.1 = x := by
  decide +kernel

theorem lyFE_code_inj : ∀ h₁ h₂ : SmallCut.lyFE.data.cut.Half,
    code .lyFE h₁.1 = code .lyFE h₂.1 → h₁ = h₂ := by
  decide +kernel

theorem lyFE_table_len :
    (signTable .lyFE).length = 9 ∧ ∀ a, (dTable .lyFE a).length = 9 := by
  decide +kernel

theorem lyFE_sign_code : ∀ i j : SmallCut.lyFE.data.cut.Half,
    edgeSign SmallCut.lyFE.edge SmallCut.lyFE.data.cut.flip i.1 j.1 =
      entry (signTable .lyFE) (code .lyFE i.1) (code .lyFE j.1) := by
  decide +kernel

theorem lyFE_adj_masks : ∀ i j : SmallCut.lyFE.data.cut.Half,
    (i ≠ j ∧ FiniteModel.Adj SmallCut.lyFE.edge SmallCut.lyFE.data.cut i j ↔
      (lyFE_adj (code .lyFE i.1) >>> code .lyFE j.1) % 2 = 1) := by
  decide +kernel

theorem lyFE_models_code : ∀ x, x < 9 → ∀ y, y < 9 →
    ModelCode .lyFE 9 lyFE_adj x y := by
  decide +kernel

theorem lyFE_modelChecks : ModelChecks .lyFE :=
  modelChecks_of .lyFE 9 lyFE_code_lt lyFE_code_onto lyFE_code_inj lyFE_table_len.1
    lyFE_sign_code lyFE_adj lyFE_adj_masks lyFE_models_code

theorem lyFE_tests_0 : ∀ e, ∀ x, x < 9 → ∀ y, y < 9 → TestCode .lyFE 0 e x y := by
  decide +kernel

theorem lyFE_tests_1 : ∀ e, ∀ x, x < 9 → ∀ y, y < 9 → TestCode .lyFE 1 e x y := by
  decide +kernel

theorem lyFE_tests_code : ∀ a e, ∀ x, x < 9 → ∀ y, y < 9 → TestCode .lyFE a e x y
  | 0, e => lyFE_tests_0 e
  | 1, e => lyFE_tests_1 e

theorem lyFE_testChecks : TestChecks .lyFE :=
  testChecks_of .lyFE 9 lyFE_code_lt lyFE_code_onto lyFE_code_inj lyFE_table_len.2
    lyFE_tests_code

theorem lyFE_factor_len : ∀ a e, (factorRealTable .lyFE a e).length = 9 ∧
    (factorImagTable .lyFE a e).length = 9 := by
  decide +kernel

theorem lyFE_factor_tri : ∀ a e, ∀ k, k < 9 → ∀ x, x < k →
    entry (factorRealTable .lyFE a e) k x = 0 ∧ entry (factorImagTable .lyFE a e) k x = 0 := by
  decide +kernel

theorem lyFE_test_symm : ∀ a e, ∀ x, x < 9 → ∀ y, y < 9 →
    entry (testRealTable .lyFE a e) x y = entry (testRealTable .lyFE a e) y x ∧
      entry (testImagTable .lyFE a e) x y = -entry (testImagTable .lyFE a e) y x := by
  decide +kernel

theorem lyFE_rows_00 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .lyFE 0 0 x y ≤ shift .lyFE 0 0 := by
  decide +kernel

theorem lyFE_rows_01 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .lyFE 0 1 x y ≤ shift .lyFE 0 1 := by
  decide +kernel

theorem lyFE_rows_02 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .lyFE 0 2 x y ≤ shift .lyFE 0 2 := by
  decide +kernel

theorem lyFE_rows_10 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .lyFE 1 0 x y ≤ shift .lyFE 1 0 := by
  decide +kernel

theorem lyFE_rows_11 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .lyFE 1 1 x y ≤ shift .lyFE 1 1 := by
  decide +kernel

theorem lyFE_rows_12 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .lyFE 1 2 x y ≤ shift .lyFE 1 2 := by
  decide +kernel

theorem lyFE_rows_code : ∀ a e, ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .lyFE a e x y ≤ shift .lyFE a e
  | 0, 0 => lyFE_rows_00
  | 0, 1 => lyFE_rows_01
  | 0, 2 => lyFE_rows_02
  | 1, 0 => lyFE_rows_10
  | 1, 1 => lyFE_rows_11
  | 1, 2 => lyFE_rows_12

theorem lyFE_residualChecks : ResidualChecks .lyFE :=
  residualChecks_of .lyFE 9 lyFE_code_lt lyFE_code_onto lyFE_code_inj lyFE_factor_len
    lyFE_factor_tri lyFE_test_symm lyFE_rows_code

end Sarkozy.SpectralD.SmallMatrices
