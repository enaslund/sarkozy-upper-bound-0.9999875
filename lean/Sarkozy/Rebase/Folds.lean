module

public import Sarkozy.CompSharp.Constructor
public import Sarkozy.HsumProof.PaperKappa

@[expose] public section

/-!
# The fold side conditions at RB's loosened `κ` (RG)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(a),(b),(c),(e), `cert:signed-local`.

C38's `CompSharp.hNr4_of_symSkew38` gives the fold families `Fs`, `Fa` (`hNr4`) at any piece table
`κ` from the one-prime statements `sym`, `skew` alone (the component norms at `38 r` proved,
`comp38_paper`), once the 33 side conditions `FoldSides κ 38 0 k` hold:
`(Γ_X + e_o r_X)² + (1 + t)·38² ≤ s_F`, `(1 + t)·38² ≤ a_F`, `38 r_X ≤ 1`, `0 ≤ ℓ_t`, with `e_o` at
the crude collision constant `c_col = 73`. RB's package R raised `s_F`, `a_F` to make them hold
(`HsumProof.PaperKappaData.kappaTab`, RG's rebase of 7 November 2026).

* **`foldSides_check`** (kernel, exact rationals): the conditions at `c_B = 38, R = 0` and at C38's
  sharper `c_B = 34, R = 1000` (`c' = 34 + 1000 r_X ≤ 38`) on the table;
* **`foldSides38_paperKappa`**, **`foldSides34_paperKappa`**: `FoldSides paperKappa 38 0 k` and
  `FoldSides paperKappa 34 1000 k` at every piece.
-/

namespace Sarkozy.Rebase

open Sarkozy.HsumProof (paperKappa kSF kAF kL)
open Sarkozy.SignedDecomp (gamX rX)
open Sarkozy.NormBoundsPaper4 (eo73)
open Sarkozy.CompSharp (FoldSides)

/-- **The fold side conditions on RB's table** (kernel, exact rationals), at `c' = 38` and at
`c' = 34 + 1000 r_X`. -/
theorem foldSides_check : ∀ k : Fin 33,
    0 ≤ kL k ∧ (gamX k + eo73 k * rX k) ^ 2 + 627 / 500 * 38 ^ 2 ≤ kSF k ∧
      627 / 500 * 38 ^ 2 ≤ kAF k ∧ 38 * rX k ≤ 1 ∧
      (gamX k + eo73 k * rX k) ^ 2 + 627 / 500 * (34 + 1000 * rX k) ^ 2 ≤ kSF k ∧
      627 / 500 * (34 + 1000 * rX k) ^ 2 ≤ kAF k ∧ (34 + 1000 * rX k) * rX k ≤ 1 := by
  decide +kernel

/-- **`FoldSides paperKappa 38 0`** at every piece: C38's `hNr4_of_symSkew38` applies to RB's
table. -/
theorem foldSides38_paperKappa (k : Fin 33) : FoldSides paperKappa 38 0 k := by
  obtain ⟨h0, h1, h2, h3, -, -, -⟩ := foldSides_check k
  have e0 : (paperKappa k).ℓ = ((kL k : ℚ) : ℝ) := rfl
  have e1 : (paperKappa k).sF = ((kSF k : ℚ) : ℝ) := rfl
  have e2 : (paperKappa k).aF = ((kAF k : ℚ) : ℝ) := rfl
  unfold FoldSides
  rw [e0, e1, e2]
  have h0' : ((0 : ℚ) : ℝ) ≤ ((kL k : ℚ) : ℝ) := by exact_mod_cast h0
  have h1' : (((gamX k + eo73 k * rX k) ^ 2 + 627 / 500 * 38 ^ 2 : ℚ) : ℝ) ≤ ((kSF k : ℚ) : ℝ) := by
    exact_mod_cast h1
  have h2' : ((627 / 500 * 38 ^ 2 : ℚ) : ℝ) ≤ ((kAF k : ℚ) : ℝ) := by exact_mod_cast h2
  have h3' : ((38 * rX k : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by exact_mod_cast h3
  push_cast at h0' h1' h2' h3' ⊢
  simp only [zero_mul, add_zero]
  refine ⟨h0', ?_, ?_, ?_⟩ <;> linarith

/-- **`FoldSides paperKappa 34 1000`** at every piece: C38's `hNr4_of_symSkew34` applies to RB's
table. -/
theorem foldSides34_paperKappa (k : Fin 33) : FoldSides paperKappa 34 1000 k := by
  obtain ⟨h0, -, -, -, h1, h2, h3⟩ := foldSides_check k
  have e0 : (paperKappa k).ℓ = ((kL k : ℚ) : ℝ) := rfl
  have e1 : (paperKappa k).sF = ((kSF k : ℚ) : ℝ) := rfl
  have e2 : (paperKappa k).aF = ((kAF k : ℚ) : ℝ) := rfl
  unfold FoldSides
  rw [e0, e1, e2]
  have h0' : ((0 : ℚ) : ℝ) ≤ ((kL k : ℚ) : ℝ) := by exact_mod_cast h0
  have h1' : (((gamX k + eo73 k * rX k) ^ 2 + 627 / 500 * (34 + 1000 * rX k) ^ 2 : ℚ) : ℝ) ≤
      ((kSF k : ℚ) : ℝ) := by
    exact_mod_cast h1
  have h2' : ((627 / 500 * (34 + 1000 * rX k) ^ 2 : ℚ) : ℝ) ≤ ((kAF k : ℚ) : ℝ) := by
    exact_mod_cast h2
  have h3' : (((34 + 1000 * rX k) * rX k : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by exact_mod_cast h3
  push_cast at h0' h1' h2' h3' ⊢
  refine ⟨h0', ?_, ?_, ?_⟩ <;> linarith

end Sarkozy.Rebase
