module

public import Sarkozy.BlockSpecPaper.AllpConsts

@[expose] public section

/-!
# A size check of the recorded per-prime constants

`allpG_le_six`: every recorded per-prime constant `g` (`clean_g` of the cuts L20, L10, L21, F21,
E21 on the 33 ALLp pieces, `AllpConsts.lean`) is at most `6`, so `g p^{-1/2} < 1` at every middle
prime (`p ≥ Q₃ > 36`), the side condition of the tensor step (`cut_block_cap`); and
`allp_e21Check`, the rational gate of the E21 collision bound (`E21.lean`). Checked by
`decide +kernel`.
-/

namespace Sarkozy.BlockAdapter

open Sarkozy.BlockSpecPaper.AllpData

/-- Every recorded per-prime constant `g` is at most `6`. -/
theorem allpG_le_six : ∀ i : Fin 33, ∀ c : Fin 5, allpG i c ≤ 6 := by
  decide +kernel

/-- **The gate of the E21 collision bound** on every piece: with `s₀ = 2^⌊k/2⌋ ≤ √X` and
`g = allpG i 4` (the recorded `clean_g` of E21), `9 + 9g/s₀ ≤ g s₀`. (`E21.lean` turns it into
`9/(p - 9) ≤ g p^{-1/2}` for every prime `p ≥ X`.) -/
theorem allp_e21Check : ∀ i : Fin 33,
    9 + 9 * allpG i 4 / 2 ^ (allpLog2 i / 2) ≤ allpG i 4 * 2 ^ (allpLog2 i / 2) := by
  decide +kernel

end Sarkozy.BlockAdapter
