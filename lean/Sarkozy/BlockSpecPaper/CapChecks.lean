module

public import Sarkozy.BlockSpecPaper.AllpConsts

@[expose] public section

/-!
# The rational block-cap checks of the ALLp caps

`allp_capCheck`: for every piece `i` and each cut `c` among L20, L10, L21, E21, with
`ℓ = k · 0.6931471803 + (1 - 2^k/X_i)` (a lower bound of `log X_i`) and `t̄ = B·570/(X_i ℓ)`:
`t̄ < 1` and `g/(1 - t̄) ≤ cap`, where `cap` is the record's `d`, `d₁`, `k_L`, `k_D`, `k_E`. Checked
by `decide +kernel`; `Caps.lean` turns it into `g exp(B·570/(X_i log X_i)) ≤ cap`. (Kept in a file
with no other namespaces open: there the kernel check reduces.)
-/

namespace Sarkozy.BlockSpecPaper.AllpData

/-- The recorded cap of cut `c` (L20, L10, L21, F21, E21) on piece `i`: `d`, `d₁`, `k_L`, `k_D`,
`k_E`. -/
def allpCap (i : Fin 33) : Fin 5 → ℚ :=
  ![(allpRecord i).d, (allpRecord i).d₁, (allpRecord i).kL, (allpRecord i).kD, (allpRecord i).kE]

/-- A rational lower bound for `log X`: `k · 0.6931471803 + (1 - 2^k/X)`. -/
def logLower (X k : ℕ) : ℚ := k * (6931471803 / 10 ^ 10) + (1 - 2 ^ k / X)

/-- The rational conditions of the block-cap inequality. -/
def CapCheck (X k : ℕ) (g B cap : ℚ) : Prop :=
  2 ^ k ≤ X ∧ 0 < logLower X k ∧ 0 ≤ g ∧ 0 ≤ B ∧ B * 570 / (X * logLower X k) < 1 ∧
    g / (1 - B * 570 / (X * logLower X k)) ≤ cap

instance (X k : ℕ) (g B cap : ℚ) : Decidable (CapCheck X k g B cap) := by
  unfold CapCheck
  infer_instance

/-- **The rational block-cap checks on all 33 pieces, for the cuts L20, L10, L21, E21.** (The F21
cap `k_D` is not of this form: its recorded `clean_g` exceeds the cap, which comes from the
`advance_old_negative` route; it is kept at its recorded value.) -/
theorem allp_capCheck : ∀ i : Fin 33, ∀ c : Fin 5, c ≠ 3 →
    CapCheck (PartV.pieceStart i) (allpLog2 i) (allpG i c) (allpB i c) (allpCap i c) := by
  decide +kernel

end Sarkozy.BlockSpecPaper.AllpData
