module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The price of the prefix (`lem:frontier:iidenergy`(iii))

`paper/sections/19_prefix.tex`. With `η_ℓ = 2^{1-ℓ} - 2^{-2ℓ}` the exception mass bound and
`p^{2ℓa}` the selection factor of a clique atom, the total price of the deletions over any set
of primes below `P` is `H_iid = η_ℓ ∑_p p^{2ℓa} ≤ η_ℓ P^{1+2ℓa} < 2P (P^{2a}/2)^ℓ`
(`prefix_price_le`). The numerical value at the baseline (part (iv)) depends on the selected `a`
and is not evaluated here.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy

/-- `η_ℓ = 2^{1-ℓ} - 2^{-2ℓ}`, the exception mass bound of `lem:frontier:iidlocal`(v). -/
noncomputable def etaClique (ℓ : ℕ) : ℝ := 2 * (1 / 2 : ℝ) ^ ℓ - ((1 / 2 : ℝ) ^ ℓ) ^ 2

theorem etaClique_lt (ℓ : ℕ) : etaClique ℓ < 2 * (1 / 2 : ℝ) ^ ℓ := by
  unfold etaClique
  have : 0 < ((1 / 2 : ℝ) ^ ℓ) ^ 2 := by positivity
  linarith

theorem etaClique_nonneg (ℓ : ℕ) : 0 ≤ etaClique ℓ := by
  unfold etaClique
  have h1 : (1 / 2 : ℝ) ^ ℓ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h0 : 0 ≤ (1 / 2 : ℝ) ^ ℓ := by positivity
  nlinarith

/-- **`lem:frontier:iidenergy`(iii).** For any set `s` of primes below `P` (`P ≥ 2`), `a > 0` and
`ℓ ≥ 1`: `η_ℓ ∑_{p ∈ s} p^{2ℓa} ≤ η_ℓ P^{1+2ℓa} < 2P (P^{2a}/2)^ℓ`. -/
theorem prefix_price_le {s : Finset ℕ} {P a : ℝ} (ℓ : ℕ) (hP : 2 ≤ P) (ha : 0 < a)
    (hs : ∀ p ∈ s, (p : ℝ) < P) (hs0 : ∀ p ∈ s, 1 ≤ p) (hcard : (s.card : ℝ) ≤ P) :
    etaClique ℓ * ∑ p ∈ s, (p : ℝ) ^ (2 * ℓ * a) ≤ etaClique ℓ * P ^ (1 + 2 * ℓ * a) ∧
      etaClique ℓ * P ^ (1 + 2 * ℓ * a) < 2 * P * (P ^ (2 * a) / 2) ^ ℓ := by
  have hP0 : 0 < P := by linarith
  have hexp : 0 ≤ 2 * (ℓ : ℝ) * a := by positivity
  have hterm : ∀ p ∈ s, (p : ℝ) ^ (2 * ℓ * a) ≤ P ^ (2 * ℓ * a) := fun p hp =>
    Real.rpow_le_rpow (by have := hs0 p hp; positivity) (hs p hp).le hexp
  have hsum : ∑ p ∈ s, (p : ℝ) ^ (2 * ℓ * a) ≤ P ^ (1 + 2 * ℓ * a) := by
    calc ∑ p ∈ s, (p : ℝ) ^ (2 * ℓ * a) ≤ ∑ _p ∈ s, P ^ (2 * ℓ * a) := sum_le_sum hterm
      _ = s.card * P ^ (2 * ℓ * a) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ P * P ^ (2 * ℓ * a) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = P ^ (1 + 2 * ℓ * a) := by rw [Real.rpow_add hP0, Real.rpow_one]
  refine ⟨mul_le_mul_of_nonneg_left hsum (etaClique_nonneg ℓ), ?_⟩
  have hpos : 0 < P ^ (1 + 2 * ℓ * a) := by positivity
  calc etaClique ℓ * P ^ (1 + 2 * ℓ * a) < 2 * (1 / 2 : ℝ) ^ ℓ * P ^ (1 + 2 * ℓ * a) :=
        mul_lt_mul_of_pos_right (etaClique_lt ℓ) hpos
    _ = 2 * P * (P ^ (2 * a) / 2) ^ ℓ := by
        have hpow : (P ^ (2 * a)) ^ ℓ = P ^ (2 * ℓ * a) := by
          rw [← Real.rpow_natCast (P ^ (2 * a)) ℓ, ← Real.rpow_mul hP0.le]
          congr 1; ring
        rw [div_pow (P ^ (2 * a)) 2 ℓ, hpow, Real.rpow_add hP0, Real.rpow_one, one_div_pow]
        field_simp
