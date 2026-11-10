module

public import Sarkozy.UpperComparison.Domain
public import Sarkozy.UpperComparison.DenseLaws

@[expose] public section

/-!
# From the gates of the three propositions to the block gates (`lem:record:domain`, Step 3)

`paper/sections/26_upper_comparison.tex`, proof of `lem:record:domain`, Step 3: "For (F9) it follows
from the gates of the three propositions ((G7)): for the forest records `c_old = ρ_old < 1/2` and
`c_new² < min(s_new, a_new)` …; for the dense laws and the mixture `c_old = c₀`, `c_new = c₁`, and
`c₀² + c₁² < min(k_s, k_a) r₀ ≤ min(d_s, d_a) ≤ min(C^s, C^a) r₀`, because `e^{ℓ₀} ≥ 1` and
`Γ ≥ 1`."

The gates of part (c) of `prop:forest-records` and `prop:dense-comparison` (and of
`prop:le-mixture`, which uses `DenseBlockGates` for the mixture) are the propositions
`ForestBlockGates`, `ForestBlockGatesFE` and `DenseBlockGates` of `ForestRecords` and `DenseLaws`.
They imply the block gates `eq:upper-block-gate` with the coefficients `C^s, C^a` of the record
(`C^ε r₀` at least the bound it rounds up), and the bounds `c_old, c_new < 1/2` that Step 3 needs
for `δ, δ' ≤ 1`:
* `forest_block_gates` (FF records), `forest_block_gates_FE` (FE and EF records);
* `dense_block_gates` (the dense EL laws and the LE mixtures), with `d_s`, `d_a` given by the
  formula `denseD` of `prop:dense-comparison`(b).
-/

namespace Sarkozy.UpperComparison

/-- **FF records**: the gates of `prop:forest-records`(c) with `ρ_old < 1/2` ((G5)), and the
coefficients `C^s r₀ ≥ ρ_old + s_new`, `C^a r₀ ≥ a_new`, give the block gates, with
`c_old, c_new < 1/2`. -/
theorem forest_block_gates {ρold cNew sNew aNew Cs Ca r₀ : ℝ} (hg : ForestBlockGates cNew sNew aNew)
    (h0 : 0 ≤ ρold) (hold : ρold < 1 / 2) (hs : ρold + sNew ≤ Cs * r₀) (ha : aNew ≤ Ca * r₀) :
    (ρold ^ 2 + cNew ^ 2 ≤ Cs * r₀ ∧ cNew ^ 2 ≤ Ca * r₀) ∧ ρold < 1 / 2 ∧ cNew < 1 / 2 :=
  ⟨block_gate_forest h0 hold hg.2 hs ha, hold, hg.1⟩

/-- **FE and EF records**: with the further gate `ρ_old² + c_new² < d_sym` and `C^s r₀ ≥ d_sym`. -/
theorem forest_block_gates_FE {ρold cNew sNew aNew dsym Cs Ca r₀ : ℝ}
    (hg : ForestBlockGates cNew sNew aNew) (hFE : ForestBlockGatesFE ρold cNew dsym)
    (hold : ρold < 1 / 2) (hs : dsym ≤ Cs * r₀) (ha : aNew ≤ Ca * r₀) :
    (ρold ^ 2 + cNew ^ 2 ≤ Cs * r₀ ∧ cNew ^ 2 ≤ Ca * r₀) ∧ ρold < 1 / 2 ∧ cNew < 1 / 2 :=
  ⟨block_gate_forest_diff hFE hs (lt_of_lt_of_le hg.2 (min_le_right _ _)) ha, hold, hg.1⟩

/-- **The dense EL laws and the LE mixtures**: the gates `DenseBlockGates c₀ d_s d_a k_s k_a r₀` of
`prop:dense-comparison`(c) (`prop:le-mixture`), with `d_s`, `d_a` of the form
`e^{ℓ₀}(Γ k r₀ + E + 2F_N(C₁ + u₁))` (`denseD`, part (b)) and the coefficients
`C^s r₀ ≥ d_s`, `C^a r₀ ≥ d_a`, give the block gates for `c_old = c₀` and
`c_new = c₁ = c₀ + d_s + d_a`, with `c₀, c₁ < 1/2`. Here `ℓ₀ ≥ 0` (a marginal density of mean
one has minimum at most one), `Γ ≥ 1`, and the remaining constants are nonnegative. -/
theorem dense_block_gates {c0 ks ka r₀ ℓ0 Γ E FN C1 u1 Cs Ca : ℝ}
    (hg : DenseBlockGates c0 (denseD ℓ0 Γ ks r₀ E FN C1 u1) (denseD ℓ0 Γ ka r₀ E FN C1 u1) ks ka r₀)
    (hks : 0 ≤ ks) (hka : 0 ≤ ka) (hr0 : 0 ≤ r₀) (hℓ : 0 ≤ ℓ0) (hΓ : 1 ≤ Γ) (hE : 0 ≤ E)
    (hFN : 0 ≤ FN) (hCu : 0 ≤ C1 + u1) (hCs : denseD ℓ0 Γ ks r₀ E FN C1 u1 ≤ Cs * r₀)
    (hCa : denseD ℓ0 Γ ka r₀ E FN C1 u1 ≤ Ca * r₀) :
    let c1 := c0 + denseD ℓ0 Γ ks r₀ E FN C1 u1 + denseD ℓ0 Γ ka r₀ E FN C1 u1
    (c0 ^ 2 + c1 ^ 2 ≤ Cs * r₀ ∧ c1 ^ 2 ≤ Ca * r₀) ∧ c0 < 1 / 2 ∧ c1 < 1 / 2 := by
  intro c1
  have hds : ks * r₀ ≤ denseD ℓ0 Γ ks r₀ E FN C1 u1 := by
    unfold denseD
    have h := dense_coef_ge (k := ks) hks hr0 hℓ hΓ hE hFN hCu
    simpa only [mul_assoc] using h
  have hda : ka * r₀ ≤ denseD ℓ0 Γ ka r₀ E FN C1 u1 := by
    unfold denseD
    have h := dense_coef_ge (k := ka) hka hr0 hℓ hΓ hE hFN hCu
    simpa only [mul_assoc] using h
  refine ⟨block_gate_dense hg.2 hr0 hds hda hCs hCa, ?_, ?_⟩
  · exact lt_of_le_of_lt (le_max_left _ _) hg.1
  · exact lt_of_le_of_lt (le_max_right _ _) hg.1

end Sarkozy.UpperComparison
