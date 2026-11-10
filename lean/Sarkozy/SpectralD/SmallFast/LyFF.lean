module

public import Sarkozy.SpectralD.SmallFast.Models

/-!
# Model, test and residual checks on codes for the lyFF tail cut

The code `code .lyFF` maps the half onto `range 9` (`lyFF_code_lt`, `lyFF_code_onto`,
`lyFF_code_inj`). Over the half, only the sign table and the adjacency masks of `G⁺` are
checked against the graph (`lyFF_sign_code`, `lyFF_adj_masks`). Everything else is checked on
codes: the model tables (`lyFF_models_code`), the test tables (`lyFF_tests_0`, `lyFF_tests_1`)
and, with upper triangular factor tables (`lyFF_factor_len`, `lyFF_factor_tri`) and symmetric
test tables (`lyFF_test_symm`), the residual row sums, one check for each `a` and `e`
(`lyFF_rows_00` to `lyFF_rows_12`). `modelChecks_of`, `testChecks_of` and
`residualChecks_of` assemble `ModelChecks .lyFF`, `TestChecks .lyFF` and `ResidualChecks .lyFF`.
The masks are generated, but they are checked here and not trusted.
-/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

open Finset Sarkozy.PartVLaws.FieldGraphs Sarkozy.SpectralD.Root

/-- The neighbours in `G⁺` of each code of the lyFF half, as bit masks of codes. -/
def lyFF_adjMasks : List ℕ :=
  [
    416, 320, 136, 260, 0, 65,
    34, 5, 11
  ]

/-- The mask of the neighbours in `G⁺` of the code `x`. -/
def lyFF_adj (x : ℕ) : ℕ := maskTable lyFF_adjMasks x

theorem lyFF_code_lt : ∀ h : SmallCut.lyFF.data.cut.Half, code .lyFF h.1 < 9 := by
  decide +kernel

theorem lyFF_code_onto : ∀ x, x < 9 →
    ∃ h : SmallCut.lyFF.data.cut.Half, code .lyFF h.1 = x := by
  decide +kernel

theorem lyFF_code_inj : ∀ h₁ h₂ : SmallCut.lyFF.data.cut.Half,
    code .lyFF h₁.1 = code .lyFF h₂.1 → h₁ = h₂ := by
  decide +kernel

theorem lyFF_table_len :
    (signTable .lyFF).length = 9 ∧ ∀ a, (dTable .lyFF a).length = 9 := by
  decide +kernel

theorem lyFF_sign_code : ∀ i j : SmallCut.lyFF.data.cut.Half,
    edgeSign SmallCut.lyFF.edge SmallCut.lyFF.data.cut.flip i.1 j.1 =
      entry (signTable .lyFF) (code .lyFF i.1) (code .lyFF j.1) := by
  decide +kernel

theorem lyFF_adj_masks : ∀ i j : SmallCut.lyFF.data.cut.Half,
    (i ≠ j ∧ FiniteModel.Adj SmallCut.lyFF.edge SmallCut.lyFF.data.cut i j ↔
      (lyFF_adj (code .lyFF i.1) >>> code .lyFF j.1) % 2 = 1) := by
  decide +kernel

theorem lyFF_models_code : ∀ x, x < 9 → ∀ y, y < 9 →
    ModelCode .lyFF 9 lyFF_adj x y := by
  decide +kernel

theorem lyFF_modelChecks : ModelChecks .lyFF :=
  modelChecks_of .lyFF 9 lyFF_code_lt lyFF_code_onto lyFF_code_inj lyFF_table_len.1
    lyFF_sign_code lyFF_adj lyFF_adj_masks lyFF_models_code

theorem lyFF_tests_0 : ∀ e, ∀ x, x < 9 → ∀ y, y < 9 → TestCode .lyFF 0 e x y := by
  decide +kernel

theorem lyFF_tests_1 : ∀ e, ∀ x, x < 9 → ∀ y, y < 9 → TestCode .lyFF 1 e x y := by
  decide +kernel

theorem lyFF_tests_code : ∀ a e, ∀ x, x < 9 → ∀ y, y < 9 → TestCode .lyFF a e x y
  | 0, e => lyFF_tests_0 e
  | 1, e => lyFF_tests_1 e

theorem lyFF_testChecks : TestChecks .lyFF :=
  testChecks_of .lyFF 9 lyFF_code_lt lyFF_code_onto lyFF_code_inj lyFF_table_len.2
    lyFF_tests_code

theorem lyFF_factor_len : ∀ a e, (factorRealTable .lyFF a e).length = 9 ∧
    (factorImagTable .lyFF a e).length = 9 := by
  decide +kernel

theorem lyFF_factor_tri : ∀ a e, ∀ k, k < 9 → ∀ x, x < k →
    entry (factorRealTable .lyFF a e) k x = 0 ∧ entry (factorImagTable .lyFF a e) k x = 0 := by
  decide +kernel

theorem lyFF_test_symm : ∀ a e, ∀ x, x < 9 → ∀ y, y < 9 →
    entry (testRealTable .lyFF a e) x y = entry (testRealTable .lyFF a e) y x ∧
      entry (testImagTable .lyFF a e) x y = -entry (testImagTable .lyFF a e) y x := by
  decide +kernel

theorem lyFF_rows_00 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .lyFF 0 0 x y ≤ shift .lyFF 0 0 := by
  decide +kernel

theorem lyFF_rows_01 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .lyFF 0 1 x y ≤ shift .lyFF 0 1 := by
  decide +kernel

theorem lyFF_rows_02 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .lyFF 0 2 x y ≤ shift .lyFF 0 2 := by
  decide +kernel

theorem lyFF_rows_10 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .lyFF 1 0 x y ≤ shift .lyFF 1 0 := by
  decide +kernel

theorem lyFF_rows_11 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .lyFF 1 1 x y ≤ shift .lyFF 1 1 := by
  decide +kernel

theorem lyFF_rows_12 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .lyFF 1 2 x y ≤ shift .lyFF 1 2 := by
  decide +kernel

theorem lyFF_rows_code : ∀ a e, ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .lyFF a e x y ≤ shift .lyFF a e
  | 0, 0 => lyFF_rows_00
  | 0, 1 => lyFF_rows_01
  | 0, 2 => lyFF_rows_02
  | 1, 0 => lyFF_rows_10
  | 1, 1 => lyFF_rows_11
  | 1, 2 => lyFF_rows_12

theorem lyFF_residualChecks : ResidualChecks .lyFF :=
  residualChecks_of .lyFF 9 lyFF_code_lt lyFF_code_onto lyFF_code_inj lyFF_factor_len
    lyFF_factor_tri lyFF_test_symm lyFF_rows_code

end Sarkozy.SpectralD.SmallMatrices
