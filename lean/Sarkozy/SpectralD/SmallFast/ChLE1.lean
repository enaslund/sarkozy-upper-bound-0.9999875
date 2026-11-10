module

public import Sarkozy.SpectralD.SmallFast.Models

/-!
# Model, test and residual checks on codes for the chLE1 tail cut

The code `code .chLE1` maps the half onto `range 9` (`chLE1_code_lt`, `chLE1_code_onto`,
`chLE1_code_inj`). Over the half, only the sign table and the adjacency masks of `G⁺` are
checked against the graph (`chLE1_sign_code`, `chLE1_adj_masks`). Everything else is checked on
codes: the model tables (`chLE1_models_code`), the test tables (`chLE1_tests_0`, `chLE1_tests_1`)
and, with upper triangular factor tables (`chLE1_factor_len`, `chLE1_factor_tri`) and symmetric
test tables (`chLE1_test_symm`), the residual row sums, one check for each `a` and `e`
(`chLE1_rows_00` to `chLE1_rows_12`). `modelChecks_of`, `testChecks_of` and
`residualChecks_of` assemble `ModelChecks .chLE1`, `TestChecks .chLE1` and `ResidualChecks .chLE1`.
The masks are generated, but they are checked here and not trusted.
-/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

open Finset Sarkozy.PartVLaws.FieldGraphs Sarkozy.SpectralD.Root

/-- The neighbours in `G⁺` of each code of the chLE1 half, as bit masks of codes. -/
def chLE1_adjMasks : List ℕ :=
  [
    384, 320, 192, 0, 0, 0,
    6, 5, 3
  ]

/-- The mask of the neighbours in `G⁺` of the code `x`. -/
def chLE1_adj (x : ℕ) : ℕ := maskTable chLE1_adjMasks x

theorem chLE1_code_lt : ∀ h : SmallCut.chLE1.data.cut.Half, code .chLE1 h.1 < 9 := by
  decide +kernel

theorem chLE1_code_onto : ∀ x, x < 9 →
    ∃ h : SmallCut.chLE1.data.cut.Half, code .chLE1 h.1 = x := by
  decide +kernel

theorem chLE1_code_inj : ∀ h₁ h₂ : SmallCut.chLE1.data.cut.Half,
    code .chLE1 h₁.1 = code .chLE1 h₂.1 → h₁ = h₂ := by
  decide +kernel

theorem chLE1_table_len :
    (signTable .chLE1).length = 9 ∧ ∀ a, (dTable .chLE1 a).length = 9 := by
  decide +kernel

theorem chLE1_sign_code : ∀ i j : SmallCut.chLE1.data.cut.Half,
    edgeSign SmallCut.chLE1.edge SmallCut.chLE1.data.cut.flip i.1 j.1 =
      entry (signTable .chLE1) (code .chLE1 i.1) (code .chLE1 j.1) := by
  decide +kernel

theorem chLE1_adj_masks : ∀ i j : SmallCut.chLE1.data.cut.Half,
    (i ≠ j ∧ FiniteModel.Adj SmallCut.chLE1.edge SmallCut.chLE1.data.cut i j ↔
      (chLE1_adj (code .chLE1 i.1) >>> code .chLE1 j.1) % 2 = 1) := by
  decide +kernel

theorem chLE1_models_code : ∀ x, x < 9 → ∀ y, y < 9 →
    ModelCode .chLE1 9 chLE1_adj x y := by
  decide +kernel

theorem chLE1_modelChecks : ModelChecks .chLE1 :=
  modelChecks_of .chLE1 9 chLE1_code_lt chLE1_code_onto chLE1_code_inj chLE1_table_len.1
    chLE1_sign_code chLE1_adj chLE1_adj_masks chLE1_models_code

theorem chLE1_tests_0 : ∀ e, ∀ x, x < 9 → ∀ y, y < 9 → TestCode .chLE1 0 e x y := by
  decide +kernel

theorem chLE1_tests_1 : ∀ e, ∀ x, x < 9 → ∀ y, y < 9 → TestCode .chLE1 1 e x y := by
  decide +kernel

theorem chLE1_tests_code : ∀ a e, ∀ x, x < 9 → ∀ y, y < 9 → TestCode .chLE1 a e x y
  | 0, e => chLE1_tests_0 e
  | 1, e => chLE1_tests_1 e

theorem chLE1_testChecks : TestChecks .chLE1 :=
  testChecks_of .chLE1 9 chLE1_code_lt chLE1_code_onto chLE1_code_inj chLE1_table_len.2
    chLE1_tests_code

theorem chLE1_factor_len : ∀ a e, (factorRealTable .chLE1 a e).length = 9 ∧
    (factorImagTable .chLE1 a e).length = 9 := by
  decide +kernel

theorem chLE1_factor_tri : ∀ a e, ∀ k, k < 9 → ∀ x, x < k →
    entry (factorRealTable .chLE1 a e) k x = 0 ∧ entry (factorImagTable .chLE1 a e) k x = 0 := by
  decide +kernel

theorem chLE1_test_symm : ∀ a e, ∀ x, x < 9 → ∀ y, y < 9 →
    entry (testRealTable .chLE1 a e) x y = entry (testRealTable .chLE1 a e) y x ∧
      entry (testImagTable .chLE1 a e) x y = -entry (testImagTable .chLE1 a e) y x := by
  decide +kernel

theorem chLE1_rows_00 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .chLE1 0 0 x y ≤ shift .chLE1 0 0 := by
  decide +kernel

theorem chLE1_rows_01 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .chLE1 0 1 x y ≤ shift .chLE1 0 1 := by
  decide +kernel

theorem chLE1_rows_02 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .chLE1 0 2 x y ≤ shift .chLE1 0 2 := by
  decide +kernel

theorem chLE1_rows_10 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .chLE1 1 0 x y ≤ shift .chLE1 1 0 := by
  decide +kernel

theorem chLE1_rows_11 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .chLE1 1 1 x y ≤ shift .chLE1 1 1 := by
  decide +kernel

theorem chLE1_rows_12 : ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .chLE1 1 2 x y ≤ shift .chLE1 1 2 := by
  decide +kernel

theorem chLE1_rows_code : ∀ a e, ∀ x, x < 9 →
    ∑ y ∈ range 9, rowTermCode .chLE1 a e x y ≤ shift .chLE1 a e
  | 0, 0 => chLE1_rows_00
  | 0, 1 => chLE1_rows_01
  | 0, 2 => chLE1_rows_02
  | 1, 0 => chLE1_rows_10
  | 1, 1 => chLE1_rows_11
  | 1, 2 => chLE1_rows_12

theorem chLE1_residualChecks : ResidualChecks .chLE1 :=
  residualChecks_of .chLE1 9 chLE1_code_lt chLE1_code_onto chLE1_code_inj chLE1_factor_len
    chLE1_factor_tri chLE1_test_symm chLE1_rows_code

end Sarkozy.SpectralD.SmallMatrices
