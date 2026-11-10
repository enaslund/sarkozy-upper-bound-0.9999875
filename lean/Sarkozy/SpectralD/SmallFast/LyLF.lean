module

public import Sarkozy.SpectralD.SmallFast.Models

/-!
# Model, test and residual checks on codes for the lyLF tail cut

The code `code .lyLF` maps the half onto `range 18` (`lyLF_code_lt`, `lyLF_code_onto`,
`lyLF_code_inj`). Over the half, only the sign table and the adjacency masks of `G⁺` are
checked against the graph (`lyLF_sign_code`, `lyLF_adj_masks`). Everything else is checked on
codes: the model tables (`lyLF_models_code`), the test tables (`lyLF_tests_0`, `lyLF_tests_1`)
and, with upper triangular factor tables (`lyLF_factor_len`, `lyLF_factor_tri`) and symmetric
test tables (`lyLF_test_symm`), the residual row sums, one check for each `a` and `e`
(`lyLF_rows_00` to `lyLF_rows_12`). `modelChecks_of`, `testChecks_of` and
`residualChecks_of` assemble `ModelChecks .lyLF`, `TestChecks .lyLF` and `ResidualChecks .lyLF`.
The masks are generated, but they are checked here and not trusted.
-/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

open Finset Sarkozy.PartVLaws.FieldGraphs Sarkozy.SpectralD.Root

/-- The neighbours in `G⁺` of each code of the lyLF half, as bit masks of codes. -/
def lyLF_adjMasks : List ℕ :=
  [
    139680, 20800, 45192, 197892, 166400, 67137,
    26658, 20485, 8715, 82224, 163880, 102480,
    133254, 325, 33474, 19476, 2600, 5145
  ]

/-- The mask of the neighbours in `G⁺` of the code `x`. -/
def lyLF_adj (x : ℕ) : ℕ := maskTable lyLF_adjMasks x

theorem lyLF_code_lt : ∀ h : SmallCut.lyLF.data.cut.Half, code .lyLF h.1 < 18 := by
  decide +kernel

theorem lyLF_code_onto : ∀ x, x < 18 →
    ∃ h : SmallCut.lyLF.data.cut.Half, code .lyLF h.1 = x := by
  decide +kernel

theorem lyLF_code_inj : ∀ h₁ h₂ : SmallCut.lyLF.data.cut.Half,
    code .lyLF h₁.1 = code .lyLF h₂.1 → h₁ = h₂ := by
  decide +kernel

theorem lyLF_table_len :
    (signTable .lyLF).length = 18 ∧ ∀ a, (dTable .lyLF a).length = 18 := by
  decide +kernel

theorem lyLF_sign_code : ∀ i j : SmallCut.lyLF.data.cut.Half,
    edgeSign SmallCut.lyLF.edge SmallCut.lyLF.data.cut.flip i.1 j.1 =
      entry (signTable .lyLF) (code .lyLF i.1) (code .lyLF j.1) := by
  decide +kernel

theorem lyLF_adj_masks : ∀ i j : SmallCut.lyLF.data.cut.Half,
    (i ≠ j ∧ FiniteModel.Adj SmallCut.lyLF.edge SmallCut.lyLF.data.cut i j ↔
      (lyLF_adj (code .lyLF i.1) >>> code .lyLF j.1) % 2 = 1) := by
  decide +kernel

theorem lyLF_models_code : ∀ x, x < 18 → ∀ y, y < 18 →
    ModelCode .lyLF 18 lyLF_adj x y := by
  decide +kernel

theorem lyLF_modelChecks : ModelChecks .lyLF :=
  modelChecks_of .lyLF 18 lyLF_code_lt lyLF_code_onto lyLF_code_inj lyLF_table_len.1
    lyLF_sign_code lyLF_adj lyLF_adj_masks lyLF_models_code

theorem lyLF_tests_0 : ∀ e, ∀ x, x < 18 → ∀ y, y < 18 → TestCode .lyLF 0 e x y := by
  decide +kernel

theorem lyLF_tests_1 : ∀ e, ∀ x, x < 18 → ∀ y, y < 18 → TestCode .lyLF 1 e x y := by
  decide +kernel

theorem lyLF_tests_code : ∀ a e, ∀ x, x < 18 → ∀ y, y < 18 → TestCode .lyLF a e x y
  | 0, e => lyLF_tests_0 e
  | 1, e => lyLF_tests_1 e

theorem lyLF_testChecks : TestChecks .lyLF :=
  testChecks_of .lyLF 18 lyLF_code_lt lyLF_code_onto lyLF_code_inj lyLF_table_len.2
    lyLF_tests_code

theorem lyLF_factor_len : ∀ a e, (factorRealTable .lyLF a e).length = 18 ∧
    (factorImagTable .lyLF a e).length = 18 := by
  decide +kernel

theorem lyLF_factor_tri : ∀ a e, ∀ k, k < 18 → ∀ x, x < k →
    entry (factorRealTable .lyLF a e) k x = 0 ∧ entry (factorImagTable .lyLF a e) k x = 0 := by
  decide +kernel

theorem lyLF_test_symm : ∀ a e, ∀ x, x < 18 → ∀ y, y < 18 →
    entry (testRealTable .lyLF a e) x y = entry (testRealTable .lyLF a e) y x ∧
      entry (testImagTable .lyLF a e) x y = -entry (testImagTable .lyLF a e) y x := by
  decide +kernel

theorem lyLF_rows_00 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .lyLF 0 0 x y ≤ shift .lyLF 0 0 := by
  decide +kernel

theorem lyLF_rows_01 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .lyLF 0 1 x y ≤ shift .lyLF 0 1 := by
  decide +kernel

theorem lyLF_rows_02 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .lyLF 0 2 x y ≤ shift .lyLF 0 2 := by
  decide +kernel

theorem lyLF_rows_10 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .lyLF 1 0 x y ≤ shift .lyLF 1 0 := by
  decide +kernel

theorem lyLF_rows_11 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .lyLF 1 1 x y ≤ shift .lyLF 1 1 := by
  decide +kernel

theorem lyLF_rows_12 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .lyLF 1 2 x y ≤ shift .lyLF 1 2 := by
  decide +kernel

theorem lyLF_rows_code : ∀ a e, ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .lyLF a e x y ≤ shift .lyLF a e
  | 0, 0 => lyLF_rows_00
  | 0, 1 => lyLF_rows_01
  | 0, 2 => lyLF_rows_02
  | 1, 0 => lyLF_rows_10
  | 1, 1 => lyLF_rows_11
  | 1, 2 => lyLF_rows_12

theorem lyLF_residualChecks : ResidualChecks .lyLF :=
  residualChecks_of .lyLF 18 lyLF_code_lt lyLF_code_onto lyLF_code_inj lyLF_factor_len
    lyLF_factor_tri lyLF_test_symm lyLF_rows_code

end Sarkozy.SpectralD.SmallMatrices
