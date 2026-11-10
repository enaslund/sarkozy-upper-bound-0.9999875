module

public import Sarkozy.NormBoundsPaper4.ENum

@[expose] public section

/-!
# `lem:record:e-orthogonal`(c) at one prime, at the paper's constant `s^E_p` (FD)

* **`EPrimeInputs p`**: the two one-prime inputs of `eorth_unnorm` — `ε` (`lem:record:e-law`(d):
  `‖ε_E‖ ≤ 18q²/(1 − q)`, by the Schur test over the 18 compatible coincidence patterns) and `cd`
  (`lem:record:e-orthogonal`(b): `‖𝖢𝖣 V c‖` on `V(H₀³)`).
* **`eorth_prime`**: `EOrthPrime p (s^E_p)` (NB3's statement of `lem:record:e-orthogonal`(c), with
  NB3's transcription `sEpaper` of the paper's `s^E_p`) at every prime `p ≡ 3 (mod 4)`, `p ≥ 10`,
  from `EPrimeInputs p`. The normalizations `z^E_0 = D₀/M`, `z₁ = D₁/M` are exact
  (`NL_eq`, NB3's `eSet_card`) and the constants are compared with the paper's in `ENum`.
* **`eOrthPaperInput_of`**: NB3's `EOrthPaperInput` from `EPrimeInputs` at every prime `p ≥ 2^20`.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper4

open Sarkozy.NormBoundsPaper3
open Sarkozy.PartV Sarkozy.Labellings Sarkozy.PartVRecords Sarkozy.MiddleComparison
open Sarkozy.NormBoundsPaper2 (chg1)

/-- **The two one-prime inputs of `lem:record:e-orthogonal`(c)** (unnormalized):
* `eps`: `lem:record:e-law`(d), `‖ε_E‖ ≤ 18q²/(1 − q)`: `|Ef u v| ≤ 18(p − 2)√Nq u √Nq v`;
* `cd`: `lem:record:e-orthogonal`(b), the form of `𝖢𝖣` against `V c` (`c_i` mean-zero):
  `|CHf w (V c)| ≤ eK √Nq w √Nq (V c)`. -/
structure EPrimeInputs (p : ℕ) [Fact p.Prime] : Prop where
  eps : ∀ u v : (ZMod p × ZMod p) × ZMod p → ℝ,
    |Ef u v| ≤ 18 * ((p : ℝ) - 2) * Real.sqrt (Nq u) * Real.sqrt (Nq v)
  cd : ∀ (c : Fin 3 → ZMod p → ℝ), (∀ i, ∑ t, c i t = 0) →
    ∀ w : (ZMod p × ZMod p) × ZMod p → ℝ,
      |CHf w (lift c)| ≤ eK p * Real.sqrt (Nq w) * Real.sqrt (Nq (lift c))

variable {p : ℕ} [Fact p.Prime]

/-- **`lem:record:e-orthogonal`(c) at one prime** (`EOrthPrime p (s^E_p)`), from `EPrimeInputs`. -/
theorem eorth_prime (hp : 10 ≤ p) (h3 : p % 4 = 3) (H : EPrimeInputs p) :
    EOrthPrime p (sEpaper (1 / (p : ℝ)) (1 / Real.sqrt p)) := by
  intro hE hne u v hu hv
  have hp' : (10 : ℝ) ≤ p := by exact_mod_cast hp
  have hp3 : 3 ≤ p := by omega
  have hp7 : 7 ≤ p := by omega
  have hp6 : 6 ≤ p := by omega
  have hp2 : p ≠ 2 := by omega
  set P : ℝ := (p : ℝ) with hPdef
  set M : ℝ := P * (P - 1) * (P - 2) with hM
  have hM0 : 0 < M := M3_pos hp3
  have hu' : ∑ x, ind3 x * u x = 0 := by rw [m3_sum_eq hp3, hu, mul_zero]
  have hv' : ∑ x, ind3 x * v x = 0 := by rw [m3_sum_eq hp3, hv, mul_zero]
  -- the exact normalizations
  have hNL : NL (p := p) = M * ((P - 3) * (P - 4) * (P - 5)) := NL_eq hp6
  have hNk : 4 * Nk (p := p) = M * ((P - 2) * (P ^ 2 - 3 * P + 4)) := by
    rw [eSet_card hE hp2 h3]; unfold Rf; ring
  have hD0 : 0 < (P - 3) * (P - 4) * (P - 5) := by
    have : 0 < P - 3 := by linarith
    have : 0 < P - 4 := by linarith
    have : 0 < P - 5 := by linarith
    positivity
  have hq : 0 < P ^ 2 - 3 * P + 4 := by nlinarith
  have hD1 : 0 < (P - 2) * (P ^ 2 - 3 * P + 4) := by
    have : 0 < P - 2 := by linarith
    positivity
  set fS := frakS (1 / P)
  have hσ : P * (P - 2) * ((1 + Real.sqrt 2) / NL (p := p) +
      |1 / NL (p := p) - 1 / (4 * Nk (p := p))|) ≤ fS / M := by
    rw [hNL, hNk]
    have e : P * (P - 2) * ((1 + Real.sqrt 2) / (M * ((P - 3) * (P - 4) * (P - 5))) +
        |1 / (M * ((P - 3) * (P - 4) * (P - 5))) - 1 / (M * ((P - 2) * (P ^ 2 - 3 * P + 4)))|) =
        (P * (P - 2) * ((1 + Real.sqrt 2) / ((P - 3) * (P - 4) * (P - 5)) +
        |1 / ((P - 3) * (P - 4) * (P - 5)) - 1 / ((P - 2) * (P ^ 2 - 3 * P + 4))|)) / M := by
      have e2 : 1 / (M * ((P - 3) * (P - 4) * (P - 5))) - 1 / (M * ((P - 2) * (P ^ 2 - 3 * P + 4)))
          = (1 / ((P - 3) * (P - 4) * (P - 5)) - 1 / ((P - 2) * (P ^ 2 - 3 * P + 4))) / M := by
        field_simp
      rw [e2, abs_div, abs_of_pos hM0]
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (num_star hp') hM0.le
  have hξ : P * (P - 2) / (4 * Nk (p := p)) ≤ fS / M := by
    rw [hNk]
    have e : P * (P - 2) / (M * ((P - 2) * (P ^ 2 - 3 * P + 4))) = P / (P ^ 2 - 3 * P + 4) / M := by
      have : P - 2 ≠ 0 := by linarith
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (num_cd hp') hM0.le
  have key := eorth_unnorm hE hne h3 hp7 H.eps H.cd hσ hξ u v hu' hv'
  -- the normalization `Nq u = M ‖u‖²`
  have hnu : Real.sqrt (Nq u) = Real.sqrt M * Real.sqrt (∑ x, m3 p x * u x ^ 2) := by
    rw [← Real.sqrt_mul hM0.le]; unfold Nq; rw [m3_sq_eq hp3]
  have hnv : Real.sqrt (Nq v) = Real.sqrt M * Real.sqrt (∑ x, m3 p x * v x ^ 2) := by
    rw [← Real.sqrt_mul hM0.le]; unfold Nq; rw [m3_sq_eq hp3]
  rw [hnu, hnv] at key
  have hMM : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM0.le
  refine key.trans ?_
  have hK : (fS / M + 2 * (eK p / (4 * Nk (p := p))) + (P - 2) / (4 * Nk (p := p)) +
      18 * (P - 2) / NL (p := p)) * M ≤ sEpaper (1 / P) (1 / Real.sqrt P) := by
    rw [hNL, hNk]
    have e : (fS / M + 2 * (eK p / (M * ((P - 2) * (P ^ 2 - 3 * P + 4)))) +
        (P - 2) / (M * ((P - 2) * (P ^ 2 - 3 * P + 4))) +
        18 * (P - 2) / (M * ((P - 3) * (P - 4) * (P - 5)))) * M =
        fS + 2 * (Real.sqrt P * Real.sqrt ((2 * (P - 2) ^ 2 + 4) / ((P - 2) * (P - 3))) /
          (P ^ 2 - 3 * P + 4)) + 1 / (P ^ 2 - 3 * P + 4) +
        18 * (P - 2) / ((P - 3) * (P - 4) * (P - 5)) := by
      unfold eK
      have : P - 2 ≠ 0 := by linarith
      field_simp
      ring
    rw [e]
    unfold sEpaper
    have n1 := num_e hp'
    have n2 := num_zz hp'
    have n3 := num_eps hp'
    have e2 : 2 * eEc (1 / P) (1 / Real.sqrt P) / (1 - 2 * (1 / P)) =
        2 * (eEc (1 / P) (1 / Real.sqrt P) / (1 - 2 * (1 / P))) := by ring
    rw [e2]
    linarith
  have hu0 : 0 ≤ Real.sqrt (∑ x, m3 p x * u x ^ 2) := Real.sqrt_nonneg _
  have hv0 : 0 ≤ Real.sqrt (∑ x, m3 p x * v x ^ 2) := Real.sqrt_nonneg _
  calc _ = (fS / M + 2 * (eK p / (4 * Nk (p := p))) + (P - 2) / (4 * Nk (p := p)) +
        18 * (P - 2) / NL (p := p)) * (Real.sqrt M * Real.sqrt M) *
        Real.sqrt (∑ x, m3 p x * u x ^ 2) * Real.sqrt (∑ x, m3 p x * v x ^ 2) := by ring
    _ = (fS / M + 2 * (eK p / (4 * Nk (p := p))) + (P - 2) / (4 * Nk (p := p)) +
        18 * (P - 2) / NL (p := p)) * M *
        Real.sqrt (∑ x, m3 p x * u x ^ 2) * Real.sqrt (∑ x, m3 p x * v x ^ 2) := by rw [hMM]
    _ ≤ _ := by gcongr

/-- **NB3's `EOrthPaperInput` from the one-prime inputs** at every prime `p ≡ 3 (mod 4)`,
`p ≥ 2^20`. -/
theorem eOrthPaperInput_of
    (H : ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → 2 ^ 20 ≤ p → EPrimeInputs p) :
    EOrthPaperInput := fun p _ h3 hp =>
  eorth_prime (by omega) h3 (H p h3 hp)

end Sarkozy.NormBoundsPaper4
