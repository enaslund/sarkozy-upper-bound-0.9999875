module

public import Sarkozy.SpectralD.SmallFast.Models

/-!
# Model, test and residual checks on codes for the chLF2 tail cut

The code `code .chLF2` maps the half onto `range 18` (`chLF2_code_lt`, `chLF2_code_onto`,
`chLF2_code_inj`). Over the half, only the sign table and the adjacency masks of `G⁺` are
checked against the graph (`chLF2_sign_code`, `chLF2_adj_masks`). Everything else is checked on
codes: the model tables (`chLF2_models_code`), the test tables (`chLF2_tests_0`, `chLF2_tests_1`)
and, with upper triangular factor tables (`chLF2_factor_len`, `chLF2_factor_tri`) and symmetric
test tables (`chLF2_test_symm`), the residual row sums, one check for each `a` and `e`
(`chLF2_rows_00` to `chLF2_rows_12`). `modelChecks_of`, `testChecks_of` and
`residualChecks_of` assemble `ModelChecks .chLF2`, `TestChecks .chLF2` and `ResidualChecks .chLF2`.
The masks are generated, but they are checked here and not trusted.
-/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

open Finset Sarkozy.PartVLaws.FieldGraphs Sarkozy.SpectralD.Root

/-- The neighbours in `G⁺` of each code of the chLF2 half, as bit masks of codes. -/
def chLF2_adjMasks : List ℕ :=
  [
    248832, 248832, 208896, 208896, 49344, 49344,
    196656, 196656, 0, 0, 12291, 12291,
    3084, 3084, 51, 51, 207, 207
  ]

/-- The mask of the neighbours in `G⁺` of the code `x`. -/
def chLF2_adj (x : ℕ) : ℕ := maskTable chLF2_adjMasks x

theorem chLF2_code_lt : ∀ h : SmallCut.chLF2.data.cut.Half, code .chLF2 h.1 < 18 := by
  decide +kernel

theorem chLF2_code_onto : ∀ x, x < 18 →
    ∃ h : SmallCut.chLF2.data.cut.Half, code .chLF2 h.1 = x := by
  decide +kernel

theorem chLF2_code_inj : ∀ h₁ h₂ : SmallCut.chLF2.data.cut.Half,
    code .chLF2 h₁.1 = code .chLF2 h₂.1 → h₁ = h₂ := by
  decide +kernel

theorem chLF2_table_len :
    (signTable .chLF2).length = 18 ∧ ∀ a, (dTable .chLF2 a).length = 18 := by
  decide +kernel

theorem chLF2_sign_code : ∀ i j : SmallCut.chLF2.data.cut.Half,
    edgeSign SmallCut.chLF2.edge SmallCut.chLF2.data.cut.flip i.1 j.1 =
      entry (signTable .chLF2) (code .chLF2 i.1) (code .chLF2 j.1) := by
  decide +kernel

theorem chLF2_adj_masks : ∀ i j : SmallCut.chLF2.data.cut.Half,
    (i ≠ j ∧ FiniteModel.Adj SmallCut.chLF2.edge SmallCut.chLF2.data.cut i j ↔
      (chLF2_adj (code .chLF2 i.1) >>> code .chLF2 j.1) % 2 = 1) := by
  decide +kernel

theorem chLF2_models_code : ∀ x, x < 18 → ∀ y, y < 18 →
    ModelCode .chLF2 18 chLF2_adj x y := by
  decide +kernel

theorem chLF2_modelChecks : ModelChecks .chLF2 :=
  modelChecks_of .chLF2 18 chLF2_code_lt chLF2_code_onto chLF2_code_inj chLF2_table_len.1
    chLF2_sign_code chLF2_adj chLF2_adj_masks chLF2_models_code

theorem chLF2_tests_0 : ∀ e, ∀ x, x < 18 → ∀ y, y < 18 → TestCode .chLF2 0 e x y := by
  decide +kernel

theorem chLF2_tests_1 : ∀ e, ∀ x, x < 18 → ∀ y, y < 18 → TestCode .chLF2 1 e x y := by
  decide +kernel

theorem chLF2_tests_code : ∀ a e, ∀ x, x < 18 → ∀ y, y < 18 → TestCode .chLF2 a e x y
  | 0, e => chLF2_tests_0 e
  | 1, e => chLF2_tests_1 e

theorem chLF2_testChecks : TestChecks .chLF2 :=
  testChecks_of .chLF2 18 chLF2_code_lt chLF2_code_onto chLF2_code_inj chLF2_table_len.2
    chLF2_tests_code

theorem chLF2_factor_len : ∀ a e, (factorRealTable .chLF2 a e).length = 18 ∧
    (factorImagTable .chLF2 a e).length = 18 := by
  decide +kernel

theorem chLF2_factor_tri : ∀ a e, ∀ k, k < 18 → ∀ x, x < k →
    entry (factorRealTable .chLF2 a e) k x = 0 ∧ entry (factorImagTable .chLF2 a e) k x = 0 := by
  decide +kernel

theorem chLF2_test_symm : ∀ a e, ∀ x, x < 18 → ∀ y, y < 18 →
    entry (testRealTable .chLF2 a e) x y = entry (testRealTable .chLF2 a e) y x ∧
      entry (testImagTable .chLF2 a e) x y = -entry (testImagTable .chLF2 a e) y x := by
  decide +kernel

theorem chLF2_rows_00 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLF2 0 0 x y ≤ shift .chLF2 0 0 := by
  decide +kernel

theorem chLF2_rows_01 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLF2 0 1 x y ≤ shift .chLF2 0 1 := by
  decide +kernel

theorem chLF2_rows_02 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLF2 0 2 x y ≤ shift .chLF2 0 2 := by
  decide +kernel

theorem chLF2_rows_10 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLF2 1 0 x y ≤ shift .chLF2 1 0 := by
  decide +kernel

theorem chLF2_rows_11 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLF2 1 1 x y ≤ shift .chLF2 1 1 := by
  decide +kernel

theorem chLF2_rows_12 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLF2 1 2 x y ≤ shift .chLF2 1 2 := by
  decide +kernel

theorem chLF2_rows_code : ∀ a e, ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLF2 a e x y ≤ shift .chLF2 a e
  | 0, 0 => chLF2_rows_00
  | 0, 1 => chLF2_rows_01
  | 0, 2 => chLF2_rows_02
  | 1, 0 => chLF2_rows_10
  | 1, 1 => chLF2_rows_11
  | 1, 2 => chLF2_rows_12

theorem chLF2_residualChecks : ResidualChecks .chLF2 :=
  residualChecks_of .chLF2 18 chLF2_code_lt chLF2_code_onto chLF2_code_inj chLF2_factor_len
    chLF2_factor_tri chLF2_test_symm chLF2_rows_code

end Sarkozy.SpectralD.SmallMatrices
