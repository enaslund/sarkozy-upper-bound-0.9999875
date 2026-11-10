module

public import Sarkozy.DensityMoments.Unconditional
public import Sarkozy.DensityMoments.PrefixEqualityEvents
public import Mathlib.Tactic.NormNum.Prime

/-!
# Non-vacuity checks for `Sarkozy/DensityMoments/`

* The range hypotheses of `clique36_proved` and `cliqueIidLaw_moment_proved` are satisfiable:
  `p = 65537 = 2^16 + 1` is a prime (`≡ 1 (mod 4)`) in the first band.
* The deleted measure `E_p` of `thm:density:iid-prefix`(c) is nontrivial and leaves positive
  mass: `0 < η < 1` for every `ℓ ≥ 1`, in particular at the paper's `m = 8192`.
-/

@[expose] public section

namespace Sarkozy.DensityMoments.Sanity

open CliqueCopies

instance fact_prime_65537 : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

theorem lt_two_pow_of_le {n : ℕ} (hn : 17 ≤ n) : 65537 < 2 ^ n :=
  lt_of_lt_of_le (by norm_num : 65537 < 2 ^ 17) (Nat.pow_le_pow_right (by norm_num) hn)

theorem lt_two_pow_512 : 65537 < 2 ^ 512 := lt_two_pow_of_le (n := 512) (by norm_num)

/-- `lem:density:clique36` at `p = 65537`. -/
theorem clique36_at_65537 :
    MixedLpBound (drawLaw (digitPairLaw 65537) (pairB 65537) (pairA 65537) (Fin 36))
      (600 / 17) 1 :=
  clique36_proved 65537 (by norm_num) (by norm_num) lt_two_pow_512

/-- `thm:density:iid-prefix`(b) at `p = 65537`, for every number of digit pairs. -/
theorem cliqueIidLaw_at_65537 (ℓ : ℕ) : MixedLpBound (cliqueIidLaw 65537 ℓ) (1200 / 17) 1 :=
  cliqueIidLaw_moment_proved 65537 ℓ (by norm_num) (by norm_num) lt_two_pow_512

theorem prefixEta_pos (ℓ : ℕ) : 0 < prefixEta ℓ := by
  unfold prefixEta
  have h0 : (0 : ℝ) < 1 / (2 : ℝ) ^ ℓ := by positivity
  have h1 : 1 / (2 : ℝ) ^ ℓ ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have h2 : (1 - 1 / (2 : ℝ) ^ ℓ) ^ 6 < 1 := pow_lt_one₀ (by linarith) (by linarith) (by norm_num)
  linarith

/-- At the paper's `m = 8192`: `0 < η < 1`. -/
theorem prefixEta_8192 : 0 < prefixEta 8192 ∧ prefixEta 8192 < 1 :=
  ⟨prefixEta_pos 8192, prefixEta_lt_one 8192 (by norm_num)⟩

end Sarkozy.DensityMoments.Sanity
