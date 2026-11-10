module

public import Sarkozy.SpectralD.SmallFast.Models

/-!
# Model, test and residual checks on codes for the chLF1 tail cut

The code `code .chLF1` maps the half onto `range 9` (`chLF1_code_lt`, `chLF1_code_onto`,
`chLF1_code_inj`). Over the half, only the sign table and the adjacency masks of `G⁺` are
checked against the graph (`chLF1_sign_code`, `chLF1_adj_masks`). Everything else is checked on
codes: the model tables (`chLF1_models_code`), the test tables (`chLF1_tests_0`, `chLF1_tests_1`)
and, with upper triangular factor tables (`chLF1_factor_len`, `chLF1_factor_tri`) and symmetric
test tables (`chLF1_test_symm`), the residual row sums, one check for each `a` and `e`
(`chLF1_rows_00` to `chLF1_rows_12`). `modelChecks_of`, `testChecks_of` and
`residualChecks_of` assemble `ModelChecks .chLF1`, `TestChecks .chLF1` and `ResidualChecks .chLF1`.
The masks are generated, but they are checked here and not trusted.
-/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

open Finset Sarkozy.PartVLaws.FieldGraphs Sarkozy.SpectralD.Root

/-- The neighbours in `G⁺` of each code of the chLF1 half, as bit masks of codes. -/
def chLF1_adjMasks : List ℕ :=
  [
    416, 320, 136, 260, 0, 65,
    34, 5, 11
  ]

/-- The mask of the neighbours in `G⁺` of the code `x`. -/
def chLF1_adj (x : ℕ) : ℕ := maskTable chLF1_adjMasks x

theorem chLF1_code_lt : ∀ h : SmallCut.chLF1.data.cut.Half, code .chLF1 h.1 < 9 := by
  decide +kernel

theorem chLF1_code_onto : ∀ x, x < 9 →
    ∃ h : SmallCut.chLF1.data.cut.Half, code .chLF1 h.1 = x := by
  decide +kernel

theorem chLF1_code_inj : ∀ h₁ h₂ : SmallCut.chLF1.data.cut.Half,
    code .chLF1 h₁.1 = code .chLF1 h₂.1 → h₁ = h₂ := by
  decide +kernel

theorem chLF1_table_len :
    (signTable .chLF1).length = 9 ∧ ∀ a, (dTable .chLF1 a).length = 9 := by
  decide +kernel

theorem chLF1_sign_code : ∀ i j : SmallCut.chLF1.data.cut.Half,
    edgeSign SmallCut.chLF1.edge SmallCut.chLF1.data.cut.flip i.1 j.1 =
      entry (signTable .chLF1) (code .chLF1 i.1) (code .chLF1 j.1) := by
  decide +kernel

theorem chLF1_adj_masks : ∀ i j : SmallCut.chLF1.data.cut.Half,
    (i ≠ j ∧ FiniteModel.Adj SmallCut.chLF1.edge SmallCut.chLF1.data.cut i j ↔
      (chLF1_adj (code .chLF1 i.1) >>> code .chLF1 j.1) % 2 = 1) := by
  decide +kernel

theorem chLF1_models_code : ∀ x, x < 9 → ∀ y, y < 9 →
    ModelCode .chLF1 9 chLF1_adj x y := by
  decide +kernel

theorem chLF1_modelChecks : ModelChecks .chLF1 :=
  modelChecks_of .chLF1 9 chLF1_code_lt chLF1_code_onto chLF1_code_inj chLF1_table_len.1
    chLF1_sign_code chLF1_adj chLF1_adj_masks chLF1_models_code

theorem chLF1_tests_0 : ∀ e, ∀ x, x < 9 → ∀ y, y < 9 → TestCode .chLF1 0 e x y := by
  decide +kernel

theorem chLF1_tests_1 : ∀ e, ∀ x, x < 9 → ∀ y, y < 9 → TestCode .chLF1 1 e x y := by
  decide +kernel

theorem chLF1_tests_code : ∀ a e, ∀ x, x < 9 → ∀ y, y < 9 → TestCode .chLF1 a e x y
  | 0, e => chLF1_tests_0 e
  | 1, e => chLF1_tests_1 e

theorem chLF1_testChecks : TestChecks .chLF1 :=
  testChecks_of .chLF1 9 chLF1_code_lt chLF1_code_onto chLF1_code_inj chLF1_table_len.2
    chLF1_tests_code

theorem chLF1_factor_len : ∀ a e, (factorRealTable .chLF1 a e).length = 9 ∧
    (factorImagTable .chLF1 a e).length = 9 := by
  decide +kernel

theorem chLF1_factor_tri : ∀ a e, ∀ k, k < 9 → ∀ x, x < k →
    entry (factorRealTable .chLF1 a e) k x = 0 ∧ entry (factorImagTable .chLF1 a e) k x = 0 := by
  decide +kernel

theorem chLF1_test_symm : ∀ a e, ∀ x, x < 9 → ∀ y, y < 9 →
    entry (testRealTable .chLF1 a e) x y = entry (testRealTable .chLF1 a e) y x ∧
      entry (testImagTable .chLF1 a e) x y = -entry (testImagTable .chLF1 a e) y x := by
  decide +kernel

theorem chLF1_rows_00 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .chLF1 0 0 x y ≤ shift .chLF1 0 0 := by
  decide +kernel

theorem chLF1_rows_01 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .chLF1 0 1 x y ≤ shift .chLF1 0 1 := by
  decide +kernel

theorem chLF1_rows_02 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .chLF1 0 2 x y ≤ shift .chLF1 0 2 := by
  decide +kernel

theorem chLF1_rows_10 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .chLF1 1 0 x y ≤ shift .chLF1 1 0 := by
  decide +kernel

theorem chLF1_rows_11 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .chLF1 1 1 x y ≤ shift .chLF1 1 1 := by
  decide +kernel

theorem chLF1_rows_12 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .chLF1 1 2 x y ≤ shift .chLF1 1 2 := by
  decide +kernel

theorem chLF1_rows_code : ∀ a e, ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .chLF1 a e x y ≤ shift .chLF1 a e
  | 0, 0 => chLF1_rows_00
  | 0, 1 => chLF1_rows_01
  | 0, 2 => chLF1_rows_02
  | 1, 0 => chLF1_rows_10
  | 1, 1 => chLF1_rows_11
  | 1, 2 => chLF1_rows_12

theorem chLF1_residualChecks : ResidualChecks .chLF1 :=
  residualChecks_of .chLF1 9 chLF1_code_lt chLF1_code_onto chLF1_code_inj chLF1_factor_len
    chLF1_factor_tri chLF1_test_symm chLF1_rows_code

end Sarkozy.SpectralD.SmallMatrices
