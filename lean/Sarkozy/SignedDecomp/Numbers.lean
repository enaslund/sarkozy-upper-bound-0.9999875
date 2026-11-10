module

public import Sarkozy.SignedDecomp.Paper
public import Sarkozy.MiddleRefinement.Numbers

@[expose] public section

/-!
# The gates of the signed record at the 33 piece starts (SD2, kernel-checked)

`paper/sections/21_middle_records.tex`, `cert:signed-local`, `prop:signed-bounds`(d);
`paper/sections/24_matching_mean.tex`, `prop:signed-sides`(i); `tab:data:sides`.

At the start `X = X_i` of each middle piece, with `q_X = 1/X`, `r_X = 1/s` (`s = ⌊√X⌋`, so
`r_X ≥ X^{-1/2}`, as in the paper), the rational atoms `atomsQ X s Γ_X` and the rational majorant
`Γ_X = gamQ X s` of `Γ_A`:
* `eoX`, `esgX`, `cpX`, `ccolX`: `e_o`, `e_sg`, `c_+`, `c_col` evaluated in exact rational
  arithmetic at the atoms (majorants of the paper's values at every prime `p ≥ X`, `Paper.lean`);
* `hX i = (1 + e₀(X))^{n_i}`, with `n_i` (`nTab`) a bound for the number of primes of a block of the
  piece (`table_check`: `e^{570} < X^{n_i + 1}` via `e < 2.7182818286`, so `n_i` primes at most,
  the budget being `∑ log p ≤ 570`);
* **`gate_check`** (kernel, exact rationals), at every piece:
  - `(s_t Γ_X + (e_o + e_sg) r_X) (1 + e₀)^{n_i} ≤ d_i` — the paper's
    `r_p d_t(1/p, p^{-1/2}) ≤ σ` (`prop:signed-sides`(i)), with `d_i` MRG's chosen side
    (`sideQ i`, `tab:data:sides`);
  - `((Γ_X + e_o r_X)² + (1 + t) c_+²) r_X (1 + e₀)^{n_i} ≤ d_i` — the paper's `c_{≥2} q ≤ σ`;
  - `(Γ_X + e_o r_X) r_X ≤ 1` and `c_+ r_X ≤ 1` (`cert:signed-local`: `c_+ r < 1`).
* `sT_le`: `s_t ≤ stU` at `t = 127/500`.

The margins of the first gate were between `1.0·10⁻⁷` and `2·10⁻⁷` at the paper's sides
(`H̄_X d_t(X)` rounded up at `10⁻⁷`, plus `10⁻⁷`). **RG (7 November 2026):** the sides `sideQ`
are now RB's loosened sides, the paper's plus `0.02` (`MiddleRefinement.sideTab`), and
`gate73_check` checks the gates with `e_o` at the crude collision constant `c_col = 73` and
`c₊ = 38`.
-/

namespace Sarkozy.SignedDecomp

open Sarkozy.MiddleRefinement (sideQ paperSide)
open Sarkozy.MainFinal2 (tPaper)

/-- `⌊√X_i⌋` at the 33 piece starts. Data (checked: `table_check`). -/
def sqrtTab : List ℕ :=
  [4466, 4664, 4870, 5042, 5086, 5311, 5792, 6316, 6888, 7512, 8192, 8933, 9741, 10623, 11585,
    12633, 13777, 15024, 16384, 17866, 19483, 21247, 23170, 25267, 27554, 30048, 32768, 46340,
    65536, 131072, 262144, 1048576, 5931641]

/-- The bound `n_i` on the number of primes of a block of piece `i`. Data (checked:
`table_check`). -/
def nTab : List ℕ :=
  [33, 33, 33, 33, 33, 33, 32, 32, 32, 31, 31, 31, 31, 30, 30, 30, 29, 29, 29, 29, 28, 28, 28, 28,
    27, 27, 27, 26, 25, 24, 22, 20, 18]

/-- The piece start `X_i`. -/
def XQ (i : Fin 33) : ℕ := PartV.pieceStart i

/-- `s_i`, with `r_X = 1/s_i`. -/
def sX (i : Fin 33) : ℕ := sqrtTab.getD i.val 0

/-- `n_i`. -/
def nX (i : Fin 33) : ℕ := nTab.getD i.val 0

/-- `r_X = 1/s_i`. -/
def rX (i : Fin 33) : ℚ := 1 / (sX i : ℚ)

/-- The rational majorant of `s_t = (4 - 2t + 2t² + 2(1 + t²)^{1/2})^{1/2}` at `t = 127/500`. -/
def stU : ℚ := 23842272739 / 10 ^ 10

/-- `Γ_X`. -/
def gamX (i : Fin 33) : ℚ := gamQ (XQ i) (sX i)

/-- The rational atoms at `X_i`. -/
def AX (i : Fin 33) : Atoms ℚ := atomsQ (XQ i) (sX i) (gamX i)

/-- `c_col` at `X_i`. -/
def ccolX (i : Fin 33) : ℚ := ccolPoly (AX i)

/-- `e_o` at `X_i`. -/
def eoX (i : Fin 33) : ℚ := eoPoly (AX i) (ccolX i)

/-- `e_sg` at `X_i`. -/
def esgX (i : Fin 33) : ℚ := esgPoly (AX i)

/-- `c_+` at `X_i`. -/
def cpX (i : Fin 33) : ℚ := cpPoly (AX i)

/-- `(1 + e₀(X_i))^{n_i}`, a bound for the density `H_𝔅` of a block of the piece. -/
def hX (i : Fin 33) : ℚ := (1 + eQ (XQ i)) ^ nX i

/-- **The tables** (kernel): `X_i ≥ 2²⁴`, `1 ≤ s_i`, `s_i² ≤ X_i`, and
`2.7182818286^{570} < X_i^{n_i + 1}`. -/
theorem table_check : ∀ i : Fin 33, 2 ^ 24 ≤ XQ i ∧ 1 ≤ sX i ∧ sX i ^ 2 ≤ XQ i ∧
    27182818286 ^ 570 < XQ i ^ (nX i + 1) * 10 ^ 5700 := by
  decide +kernel

/-- **The gates of the signed record at the 33 piece starts** (kernel, exact rationals). -/
theorem gate_check : ∀ i : Fin 33,
    (stU * gamX i + (eoX i + esgX i) * rX i) * hX i ≤ sideQ i ∧
    ((gamX i + eoX i * rX i) ^ 2 + 627 / 500 * cpX i ^ 2) * rX i * hX i ≤ sideQ i ∧
    (gamX i + eoX i * rX i) * rX i ≤ 1 ∧ cpX i * rX i ≤ 1 := by
  decide +kernel

/-- **The component gates at the crude constant `c_B = 80`** (kernel): the paper's `c_+ ≈ 1.74`
has a large slack here; also `c_+(X_i) ≤ 80`. -/
theorem crude_check : ∀ i : Fin 33,
    ((gamX i + eoX i * rX i) ^ 2 + 627 / 500 * 80 ^ 2) * rX i * hX i ≤ sideQ i ∧
    80 * rX i ≤ 1 ∧ cpX i ≤ 80 := by
  decide +kernel

/-- `0.02 + 5·10⁻⁷` (RG: the sides are the paper's plus `0.02`; it was `5·10⁻⁷`). -/
def tightEps : ℚ := 200005 / 10 ^ 7

/-- **The first gate is tight up to the loosening** (kernel): at every piece start the left side of
the first gate of `gate_check` is at least `d_i - 0.02 - 5·10⁻⁷`. At the paper's sides (MRG's table
without RG's `+ 0.02`) it was at least `d_i - 5·10⁻⁷`, so the paper's constants had no room; the
`0.02` added to every side by RG's rebase (7 November 2026) is the room used by `gate73_check`. -/
theorem gate_tight : ∀ i : Fin 33,
    sideQ i ≤ (stU * gamX i + (eoX i + esgX i) * rX i) * hX i + tightEps := by
  decide +kernel

/-- **The gates at the crude collision constant `c_col = 73`** (kernel; RG, 7 November 2026): at
RB's loosened sides (`sideQ`, the paper's plus `0.02`), the first gate holds with `e_o` at
`c_col = 73` (FD's `collisionBound_73`) in place of the paper's `c_col ≈ 5.62`, and the second with
the component constant `c₊ = 38` (C38's `comp38_paper`); also `38 r_X ≤ 1` and `c₊(X_i) ≤ 38`. -/
theorem gate73_check : ∀ i : Fin 33,
    (stU * gamX i + (eoPoly (AX i) 73 + esgX i) * rX i) * hX i ≤ sideQ i ∧
    ((gamX i + eoPoly (AX i) 73 * rX i) ^ 2 + 627 / 500 * 38 ^ 2) * rX i * hX i ≤ sideQ i ∧
    (gamX i + eoPoly (AX i) 73 * rX i) * rX i ≤ 1 ∧ 38 * rX i ≤ 1 ∧ cpX i ≤ 38 ∧
    ccolX i ≤ 73 := by
  decide +kernel

/-- The majorants are nonnegative (kernel). -/
theorem pos_check : ∀ i : Fin 33, 0 ≤ gamX i ∧ 0 ≤ eoX i ∧ 0 ≤ esgX i ∧ 0 ≤ cpX i ∧ 0 ≤ rX i ∧
    0 ≤ stU := by
  decide +kernel

/-- `s_t ≤ stU` at `t = 127/500`. -/
theorem sT_le : Sarkozy.Envelopes.sT tPaper ≤ ((stU : ℚ) : ℝ) := by
  unfold Sarkozy.Envelopes.sT
  have h1 : √(1 + tPaper ^ 2) ≤ 103175384662 / 10 ^ 11 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num [tPaper]
  rw [Real.sqrt_le_left (by norm_num [stU])]
  have : (4 - 2 * tPaper + 2 * tPaper ^ 2 + 2 * √(1 + tPaper ^ 2) : ℝ) ≤
      4 - 2 * tPaper + 2 * tPaper ^ 2 + 2 * (103175384662 / 10 ^ 11) := by linarith
  refine this.trans ?_
  norm_num [tPaper, stU]

end Sarkozy.SignedDecomp
