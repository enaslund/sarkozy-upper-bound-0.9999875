module

public import Sarkozy.SpectralD.SmallFast.Models

/-!
# Model, test and residual checks on codes for the chLL1 tail cut

The code `code .chLL1` maps the half onto `range 18` (`chLL1_code_lt`, `chLL1_code_onto`,
`chLL1_code_inj`). Over the half, only the sign table and the adjacency masks of `G⁺` are
checked against the graph (`chLL1_sign_code`, `chLL1_adj_masks`). Everything else is checked on
codes: the model tables (`chLL1_models_code`), the test tables (`chLL1_tests_0`, `chLL1_tests_1`)
and, with upper triangular factor tables (`chLL1_factor_len`, `chLL1_factor_tri`) and symmetric
test tables (`chLL1_test_symm`), the residual row sums, one check for each `a` and `e`
(`chLL1_rows_00` to `chLL1_rows_12`). `modelChecks_of`, `testChecks_of` and
`residualChecks_of` assemble `ModelChecks .chLL1`, `TestChecks .chLL1` and `ResidualChecks .chLL1`.
The masks are generated, but they are checked here and not trusted.
-/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

open Finset Sarkozy.PartVLaws.FieldGraphs Sarkozy.SpectralD.Root

/-- The neighbours in `G⁺` of each code of the chLL1 half, as bit masks of codes. -/
def chLL1_adjMasks : List ℕ :=
  [
    156928, 154112, 107584, 92288, 168256, 103040,
    81940, 163880, 69649, 139298, 20485, 40970,
    1330, 2573, 1099, 2228, 364, 659
  ]

/-- The mask of the neighbours in `G⁺` of the code `x`. -/
def chLL1_adj (x : ℕ) : ℕ := maskTable chLL1_adjMasks x

theorem chLL1_code_lt : ∀ h : SmallCut.chLL1.data.cut.Half, code .chLL1 h.1 < 18 := by
  decide +kernel

theorem chLL1_code_onto : ∀ x, x < 18 →
    ∃ h : SmallCut.chLL1.data.cut.Half, code .chLL1 h.1 = x := by
  decide +kernel

theorem chLL1_code_inj : ∀ h₁ h₂ : SmallCut.chLL1.data.cut.Half,
    code .chLL1 h₁.1 = code .chLL1 h₂.1 → h₁ = h₂ := by
  decide +kernel

theorem chLL1_table_len :
    (signTable .chLL1).length = 18 ∧ ∀ a, (dTable .chLL1 a).length = 18 := by
  decide +kernel

theorem chLL1_sign_code : ∀ i j : SmallCut.chLL1.data.cut.Half,
    edgeSign SmallCut.chLL1.edge SmallCut.chLL1.data.cut.flip i.1 j.1 =
      entry (signTable .chLL1) (code .chLL1 i.1) (code .chLL1 j.1) := by
  decide +kernel

theorem chLL1_adj_masks : ∀ i j : SmallCut.chLL1.data.cut.Half,
    (i ≠ j ∧ FiniteModel.Adj SmallCut.chLL1.edge SmallCut.chLL1.data.cut i j ↔
      (chLL1_adj (code .chLL1 i.1) >>> code .chLL1 j.1) % 2 = 1) := by
  decide +kernel

theorem chLL1_models_code : ∀ x, x < 18 → ∀ y, y < 18 →
    ModelCode .chLL1 18 chLL1_adj x y := by
  decide +kernel

theorem chLL1_modelChecks : ModelChecks .chLL1 :=
  modelChecks_of .chLL1 18 chLL1_code_lt chLL1_code_onto chLL1_code_inj chLL1_table_len.1
    chLL1_sign_code chLL1_adj chLL1_adj_masks chLL1_models_code

theorem chLL1_tests_0 : ∀ e, ∀ x, x < 18 → ∀ y, y < 18 → TestCode .chLL1 0 e x y := by
  decide +kernel

theorem chLL1_tests_1 : ∀ e, ∀ x, x < 18 → ∀ y, y < 18 → TestCode .chLL1 1 e x y := by
  decide +kernel

theorem chLL1_tests_code : ∀ a e, ∀ x, x < 18 → ∀ y, y < 18 → TestCode .chLL1 a e x y
  | 0, e => chLL1_tests_0 e
  | 1, e => chLL1_tests_1 e

theorem chLL1_testChecks : TestChecks .chLL1 :=
  testChecks_of .chLL1 18 chLL1_code_lt chLL1_code_onto chLL1_code_inj chLL1_table_len.2
    chLL1_tests_code

theorem chLL1_factor_len : ∀ a e, (factorRealTable .chLL1 a e).length = 18 ∧
    (factorImagTable .chLL1 a e).length = 18 := by
  decide +kernel

theorem chLL1_factor_tri : ∀ a e, ∀ k, k < 18 → ∀ x, x < k →
    entry (factorRealTable .chLL1 a e) k x = 0 ∧ entry (factorImagTable .chLL1 a e) k x = 0 := by
  decide +kernel

theorem chLL1_test_symm : ∀ a e, ∀ x, x < 18 → ∀ y, y < 18 →
    entry (testRealTable .chLL1 a e) x y = entry (testRealTable .chLL1 a e) y x ∧
      entry (testImagTable .chLL1 a e) x y = -entry (testImagTable .chLL1 a e) y x := by
  decide +kernel

theorem chLL1_rows_00 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLL1 0 0 x y ≤ shift .chLL1 0 0 := by
  decide +kernel

theorem chLL1_rows_01 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLL1 0 1 x y ≤ shift .chLL1 0 1 := by
  decide +kernel

theorem chLL1_rows_02 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLL1 0 2 x y ≤ shift .chLL1 0 2 := by
  decide +kernel

theorem chLL1_rows_10 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLL1 1 0 x y ≤ shift .chLL1 1 0 := by
  decide +kernel

theorem chLL1_rows_11 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLL1 1 1 x y ≤ shift .chLL1 1 1 := by
  decide +kernel

theorem chLL1_rows_12 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLL1 1 2 x y ≤ shift .chLL1 1 2 := by
  decide +kernel

theorem chLL1_rows_code : ∀ a e, ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLL1 a e x y ≤ shift .chLL1 a e
  | 0, 0 => chLL1_rows_00
  | 0, 1 => chLL1_rows_01
  | 0, 2 => chLL1_rows_02
  | 1, 0 => chLL1_rows_10
  | 1, 1 => chLL1_rows_11
  | 1, 2 => chLL1_rows_12

theorem chLL1_residualChecks : ResidualChecks .chLL1 :=
  residualChecks_of .chLL1 18 chLL1_code_lt chLL1_code_onto chLL1_code_inj chLL1_factor_len
    chLL1_factor_tri chLL1_test_symm chLL1_rows_code

end Sarkozy.SpectralD.SmallMatrices
