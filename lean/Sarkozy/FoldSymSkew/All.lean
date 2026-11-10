module

public import Sarkozy.FoldSymSkew.Prime
public import Sarkozy.FoldSymSkew.Block
public import Sarkozy.FoldSymSkew.Constructor
public import Sarkozy.FoldSymSkew.RebaseCheck
public import Sarkozy.FoldSymSkew.Sanity

/-!
# FS: `prop:signed-bounds`(c) at one prime (`sym`, `skew`) and all four fold bounds (umbrella)

* `Prime`: `aNorm` (`|a_t|`), **`lForm_bound`** (`‖L^m_t‖ ≤ |a_t| Γ r`), **`sym_of_decomp`**
  (`‖D^s_{t,p}‖ ≤ (e_o + e_sg) q`), **`skew_of_decomp`** (`‖D^a_{t,p}‖ ≤ |a_t| Γ r + e_sg q`).
* `Block`: `newDecomp_mono`, `aNU`, `aNorm_le`, **`symSkew_block`** (FD's `SymPrime`, `SkewPrime` at
  every prime of a middle block of piece `k`), `esgP_le_esgX`.
* `Constructor`: `NewDecompAt`, `SpecNewDecomp`, `SpecNewDecompF`, **`SymSkewSides`**,
  `symSkew_of_newDecomp`, `specSymSkew_of_newDecomp`, **`hNr4_of_newDecomp38/34`**,
  **`hNr4_of_newDecompF38`** (at `e_sg′ = esgF(p)`), `specNewDecomp_of_analytic2`,
  **`hNr4_of_SDB38/34`** (NB3's `hNr4` from SD2's `SDB` at any piece table, given the sides).
* `RebaseCheck`: RB's candidate table `rbKappa`, **`rb_check`** (kernel), `rb_sides`,
  **`hNr4_rb`** (`hNr4` at `rbKappa` from `SDB` alone).
* `Sanity`: `symSkew_crude` (non-vacuity at the paper's objects), `paper_table_fails` (kernel).
-/
