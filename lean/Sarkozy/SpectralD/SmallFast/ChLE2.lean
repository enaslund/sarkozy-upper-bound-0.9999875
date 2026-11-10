module

public import Sarkozy.SpectralD.SmallFast.Models

/-!
# Model, test and residual checks on codes for the chLE2 tail cut

The code `code .chLE2` maps the half onto `range 18` (`chLE2_code_lt`, `chLE2_code_onto`,
`chLE2_code_inj`). Over the half, only the sign table and the adjacency masks of `G⁺` are
checked against the graph (`chLE2_sign_code`, `chLE2_adj_masks`). Everything else is checked on
codes: the model tables (`chLE2_models_code`), the test tables (`chLE2_tests_0`, `chLE2_tests_1`)
and, with upper triangular factor tables (`chLE2_factor_len`, `chLE2_factor_tri`) and symmetric
test tables (`chLE2_test_symm`), the residual row sums, one check for each `a` and `e`
(`chLE2_rows_00` to `chLE2_rows_12`). `modelChecks_of`, `testChecks_of` and
`residualChecks_of` assemble `ModelChecks .chLE2`, `TestChecks .chLE2` and `ResidualChecks .chLE2`.
The masks are generated, but they are checked here and not trusted.
-/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

open Finset Sarkozy.PartVLaws.FieldGraphs Sarkozy.SpectralD.Root

/-- The neighbours in `G⁺` of each code of the chLE2 half, as bit masks of codes. -/
def chLE2_adjMasks : List ℕ :=
  [
    245760, 245760, 208896, 208896, 61440, 61440,
    0, 0, 0, 0, 0, 0,
    60, 60, 51, 51, 15, 15
  ]

/-- The mask of the neighbours in `G⁺` of the code `x`. -/
def chLE2_adj (x : ℕ) : ℕ := maskTable chLE2_adjMasks x

theorem chLE2_code_lt : ∀ h : SmallCut.chLE2.data.cut.Half, code .chLE2 h.1 < 18 := by
  decide +kernel

theorem chLE2_code_onto : ∀ x, x < 18 →
    ∃ h : SmallCut.chLE2.data.cut.Half, code .chLE2 h.1 = x := by
  decide +kernel

theorem chLE2_code_inj : ∀ h₁ h₂ : SmallCut.chLE2.data.cut.Half,
    code .chLE2 h₁.1 = code .chLE2 h₂.1 → h₁ = h₂ := by
  decide +kernel

theorem chLE2_table_len :
    (signTable .chLE2).length = 18 ∧ ∀ a, (dTable .chLE2 a).length = 18 := by
  decide +kernel

theorem chLE2_sign_code : ∀ i j : SmallCut.chLE2.data.cut.Half,
    edgeSign SmallCut.chLE2.edge SmallCut.chLE2.data.cut.flip i.1 j.1 =
      entry (signTable .chLE2) (code .chLE2 i.1) (code .chLE2 j.1) := by
  decide +kernel

theorem chLE2_adj_masks : ∀ i j : SmallCut.chLE2.data.cut.Half,
    (i ≠ j ∧ FiniteModel.Adj SmallCut.chLE2.edge SmallCut.chLE2.data.cut i j ↔
      (chLE2_adj (code .chLE2 i.1) >>> code .chLE2 j.1) % 2 = 1) := by
  decide +kernel

theorem chLE2_models_code : ∀ x, x < 18 → ∀ y, y < 18 →
    ModelCode .chLE2 18 chLE2_adj x y := by
  decide +kernel

theorem chLE2_modelChecks : ModelChecks .chLE2 :=
  modelChecks_of .chLE2 18 chLE2_code_lt chLE2_code_onto chLE2_code_inj chLE2_table_len.1
    chLE2_sign_code chLE2_adj chLE2_adj_masks chLE2_models_code

theorem chLE2_tests_0 : ∀ e, ∀ x, x < 18 → ∀ y, y < 18 → TestCode .chLE2 0 e x y := by
  decide +kernel

theorem chLE2_tests_1 : ∀ e, ∀ x, x < 18 → ∀ y, y < 18 → TestCode .chLE2 1 e x y := by
  decide +kernel

theorem chLE2_tests_code : ∀ a e, ∀ x, x < 18 → ∀ y, y < 18 → TestCode .chLE2 a e x y
  | 0, e => chLE2_tests_0 e
  | 1, e => chLE2_tests_1 e

theorem chLE2_testChecks : TestChecks .chLE2 :=
  testChecks_of .chLE2 18 chLE2_code_lt chLE2_code_onto chLE2_code_inj chLE2_table_len.2
    chLE2_tests_code

theorem chLE2_factor_len : ∀ a e, (factorRealTable .chLE2 a e).length = 18 ∧
    (factorImagTable .chLE2 a e).length = 18 := by
  decide +kernel

theorem chLE2_factor_tri : ∀ a e, ∀ k, k < 18 → ∀ x, x < k →
    entry (factorRealTable .chLE2 a e) k x = 0 ∧ entry (factorImagTable .chLE2 a e) k x = 0 := by
  decide +kernel

theorem chLE2_test_symm : ∀ a e, ∀ x, x < 18 → ∀ y, y < 18 →
    entry (testRealTable .chLE2 a e) x y = entry (testRealTable .chLE2 a e) y x ∧
      entry (testImagTable .chLE2 a e) x y = -entry (testImagTable .chLE2 a e) y x := by
  decide +kernel

theorem chLE2_rows_00 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLE2 0 0 x y ≤ shift .chLE2 0 0 := by
  decide +kernel

theorem chLE2_rows_01 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLE2 0 1 x y ≤ shift .chLE2 0 1 := by
  decide +kernel

theorem chLE2_rows_02 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLE2 0 2 x y ≤ shift .chLE2 0 2 := by
  decide +kernel

theorem chLE2_rows_10 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLE2 1 0 x y ≤ shift .chLE2 1 0 := by
  decide +kernel

theorem chLE2_rows_11 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLE2 1 1 x y ≤ shift .chLE2 1 1 := by
  decide +kernel

theorem chLE2_rows_12 : ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLE2 1 2 x y ≤ shift .chLE2 1 2 := by
  decide +kernel

theorem chLE2_rows_code : ∀ a e, ∀ x, x < 18 →
    ∑ y ∈ range 18, rowTermCode .chLE2 a e x y ≤ shift .chLE2 a e
  | 0, 0 => chLE2_rows_00
  | 0, 1 => chLE2_rows_01
  | 0, 2 => chLE2_rows_02
  | 1, 0 => chLE2_rows_10
  | 1, 1 => chLE2_rows_11
  | 1, 2 => chLE2_rows_12

theorem chLE2_residualChecks : ResidualChecks .chLE2 :=
  residualChecks_of .chLE2 18 chLE2_code_lt chLE2_code_onto chLE2_code_inj chLE2_factor_len
    chLE2_factor_tri chLE2_test_symm chLE2_rows_code

end Sarkozy.SpectralD.SmallMatrices
