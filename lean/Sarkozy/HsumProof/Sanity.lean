module

public import Sarkozy.HsumProof.PaperKappa

@[expose] public section

/-!
# Non-vacuity of HS's hypotheses

* `PaperLedgers` (`Ledgers.lean`) is satisfiable, with equality in every state: `uniformCs`,
  `uniformCa` split each band's ledger `Λ^s(𝔱)`, `Λ^a(𝔱)` equally over the changed records of the
  state (`uniform_state_sums`). For the `LR` and `RL` states this is the paper's per-record value
  (`UpperComparison.ledger_LR_binding`, `ledger_RL_binding`: the ledger is the number of records
  times one coefficient); for the 84 one-way repairs ((F7)) the paper's per-record coefficients
  differ inside a state, and only their sums are exported.
* `upperPart_uniform`: the upper part of `hsum` at these data is at most `0.021`.
* `SAParts3K.hκB` is satisfiable, at the paper's constants: `paperKappa` is nonnegative and
  satisfies it (`kappa_sanity`), and `middlePart paperKappa ≤ 0.8349`.
* The hypotheses of `upperPart_le` are only `0 ≤ Cs`, `0 ≤ Ca` and `PaperLedgers`; the band side
  (`bandCheck_all`, `round_sum`) is proved, not assumed.

Field-by-field comparison with the paper (`def:upper-comparison`): `Λ^s_k(𝔱)` is "the sum of the
symmetric coefficients of the changed records of state `𝔱` and degree `k`"; `PaperLedgers` asks
`∑_{ρ changed, state 𝔱} C^s_ρ ≤ Λ^s(𝔱)` per band, with `Λ` read from the band record the paper
names (`upper_dense_refined.json`); `lower_ledgers_eq` checks the 45 lower bands against the
table printed in `cert:upper-lower-bands`.
-/

open Finset

namespace Sarkozy.HsumProof

open Sarkozy.PartV Sarkozy.UpperComparison

/-- The equal split of the symmetric ledger over the changed records of a state. -/
noncomputable def uniformCs (k : Fin 310) (ρ : UpIdx) : ℝ :=
  if upperFate ρ = .changed then (ledS k ρ.2.1 : ℝ) / (changedOf ρ.2.1).card else 0

/-- The equal split of the skew ledger. -/
noncomputable def uniformCa (k : Fin 310) (ρ : UpIdx) : ℝ :=
  if upperFate ρ = .changed then (ledA k ρ.2.1 : ℝ) / (changedOf ρ.2.1).card else 0

theorem uniformCs_nonneg (k : Fin 310) (ρ : UpIdx) : 0 ≤ uniformCs k ρ := by
  unfold uniformCs
  have := ledS_nonneg k ρ.2.1
  split_ifs
  · have h : (0 : ℝ) ≤ (ledS k ρ.2.1 : ℝ) := by exact_mod_cast this
    positivity
  · exact le_rfl

theorem uniformCa_nonneg (k : Fin 310) (ρ : UpIdx) : 0 ≤ uniformCa k ρ := by
  unfold uniformCa
  have := ledA_nonneg k ρ.2.1
  split_ifs
  · have h : (0 : ℝ) ≤ (ledA k ρ.2.1 : ℝ) := by exact_mod_cast this
    positivity
  · exact le_rfl

theorem sum_split (t : PType × PType) (L : ℝ) (hL : 0 ≤ L)
    (f : UpIdx → ℝ) (hf : ∀ ρ ∈ changedOf t, f ρ = L / (changedOf t).card) :
    ∑ ρ ∈ changedOf t, f ρ ≤ L ∧ ((changedOf t).Nonempty → ∑ ρ ∈ changedOf t, f ρ = L) := by
  rw [sum_congr rfl hf, sum_const, nsmul_eq_mul]
  rcases (changedOf t).eq_empty_or_nonempty with h | h
  · rw [h, card_empty]
    simp only [Nat.cast_zero, zero_mul]
    exact ⟨hL, fun hn => absurd hn (by simp)⟩
  · have hc : ((changedOf t).card : ℝ) ≠ 0 := by
      have := h.card_pos
      positivity
    have e : ((changedOf t).card : ℝ) * (L / (changedOf t).card) = L := by field_simp
    rw [e]
    exact ⟨le_rfl, fun _ => rfl⟩

/-- **The equal split has the paper's state sums, with equality** on the states with changed
records. -/
theorem uniform_state_sums (k : Fin 310) (t : PType × PType) :
    (∑ ρ ∈ changedOf t, uniformCs k ρ ≤ (ledS k t : ℝ) ∧
      ((changedOf t).Nonempty → ∑ ρ ∈ changedOf t, uniformCs k ρ = (ledS k t : ℝ))) ∧
    (∑ ρ ∈ changedOf t, uniformCa k ρ ≤ (ledA k t : ℝ) ∧
      ((changedOf t).Nonempty → ∑ ρ ∈ changedOf t, uniformCa k ρ = (ledA k t : ℝ))) := by
  have hmem : ∀ ρ ∈ changedOf t, upperFate ρ = .changed ∧ ρ.2.1 = t := fun ρ hρ => by
    simpa [changedOf] using hρ
  constructor
  · apply sum_split t _ (by exact_mod_cast ledS_nonneg k t)
    intro ρ hρ
    obtain ⟨h1, h2⟩ := hmem ρ hρ
    simp only [uniformCs, h1, ↓reduceIte, h2]
  · apply sum_split t _ (by exact_mod_cast ledA_nonneg k t)
    intro ρ hρ
    obtain ⟨h1, h2⟩ := hmem ρ hρ
    simp only [uniformCa, h1, ↓reduceIte, h2]

theorem uniform_paperLedgers : PaperLedgers uniformCs uniformCa := fun k t =>
  ⟨(uniform_state_sums k t).1.1, (uniform_state_sums k t).2.1⟩

/-- **The upper part of `hsum` at the equal split** is at most `0.021`. -/
theorem upperPart_uniform :
    upperPart uniformCs uniformCa uniformCs_nonneg uniformCa_nonneg ≤ 21 / 1000 :=
  upperPart_le _ _ _ _ uniform_paperLedgers

/-- **The paper's constants satisfy the side conditions on `κ`**, and the middle part at them
is within E3's budget. -/
theorem kappa_sanity : (∀ i, NumericalFields.KappaNonneg (paperKappa i)) ∧
    (∀ i, (paperKappa i).sE + (paperKappa i).aE + (paperKappa i).ℓ ≤ 23 / 10 ∧
      (paperKappa i).sF + (paperKappa i).aF ≤ 3700) ∧ middlePart paperKappa ≤ middleBudget :=
  ⟨paperKappa_nonneg, paperKappa_bounds, middlePart_paperKappa⟩

end Sarkozy.HsumProof
