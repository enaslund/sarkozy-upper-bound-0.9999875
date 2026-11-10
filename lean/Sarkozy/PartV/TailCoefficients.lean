module

public import Sarkozy.PartV.UpperReference

@[expose] public section

/-!
# The tail coefficients and the nonroot mass of the tail law (`def:tail-law`, `lem:tail-law`(iii))

`paper/sections/27_tail_index.tex`, `def:tail-law` (`eq:tail-coefficients`) and `lem:tail-law`(iii);
the bounds on `C₁, C₂, C₃` are the `C_j` part of item (S7) of `cert:record:analytic-stage`.

* `tailC j = ∑_{d ≥ j} c_d P₄^{-(d-j)/2}` (`j = 1, 2, 3`), with `P₄^{-1/2} = 2^{-256}`, and
  `S72 p = 2⁹²/p + C₁/p^{1/2} + C₂/p + C₃/p^{3/2}`;
* `tailC_bounds`: `C₁ < 1197.601`, `C₂ < 609305.05`, `C₃ < 1.4176·10⁸` (exact rational arithmetic);
* `tail_nonroot_mass`: for a prime `p ≥ P₄`, the nonroot mass `h_p = P_μ(r) - 1` of the tail law
  satisfies `0 ≤ h_p ≤ C₁ p^{-1/2}` (`lem:tail-law`(iii)).
-/

namespace Sarkozy.PartV

open Finset

/-- The coefficients `c_0, …, c_7` of the tail polynomial (`def:tail-law`). -/
def tailCoeff : ℕ → ℚ
  | 0 => 1
  | 1 => 5988 / 5
  | 2 => 15232626 / 25
  | 3 => 24807984744 / 175
  | 4 => 50638290432 / 5
  | 5 => 621170191872 / 5
  | 6 => 1877429977088 / 7
  | 7 => 970455252992 / 7
  | _ => 0

/-- `P₄^{-1/2} = 2^{-256}`. -/
def tailRho : ℚ := 1 / 2 ^ 256

/-- **The tail coefficients** `C_j = ∑_{d ≥ j} c_d P₄^{-(d-j)/2}` (`eq:tail-coefficients`). -/
def tailC (j : ℕ) : ℚ := ∑ d ∈ (range 8).filter (j ≤ ·), tailCoeff d * tailRho ^ (d - j)

/-- `S₇₂(p) = 2⁹²/p + C₁/p^{1/2} + C₂/p + C₃/p^{3/2}` (`eq:tail-coefficients`). -/
noncomputable def S72 (p : ℝ) : ℝ :=
  2 ^ 92 / p + (tailC 1 : ℝ) / Real.sqrt p + (tailC 2 : ℝ) / p + (tailC 3 : ℝ) / (p * Real.sqrt p)

theorem tailC_one : tailC 1 = 5988 / 5 + 15232626 / 25 * tailRho + 24807984744 / 175 * tailRho ^ 2 +
    50638290432 / 5 * tailRho ^ 3 + 621170191872 / 5 * tailRho ^ 4 +
    1877429977088 / 7 * tailRho ^ 5 + 970455252992 / 7 * tailRho ^ 6 := by
  unfold tailC
  decide +kernel

/-- **(S7), the `C_j` bounds**: `C₁ < 1197.601`, `C₂ < 609305.05`, `C₃ < 1.4176·10⁸`. -/
theorem tailC_bounds :
    tailC 1 < 1197601 / 1000 ∧ tailC 2 < 6093050500 / 10000 ∧ tailC 3 < 141760000 := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold tailC tailRho <;> decide +kernel

/-- `r = p^{-1/2} = 1/√p`. -/
theorem tailR_eq (p : ℕ) : tailR p = 1 / Real.sqrt p := by
  unfold tailR
  rw [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg _)]
  exact (one_div _).symm

/-- For `p ≥ P₄`, `r = p^{-1/2} ≤ 2^{-256}`. -/
theorem tailR_le (p : ℕ) (hp : P4 ≤ p) : tailR p ≤ (tailRho : ℝ) := by
  rw [tailR_eq]
  have hP : ((2 : ℝ) ^ 256) ^ 2 ≤ (p : ℝ) := by
    have hP4 : P4 = (2 ^ 256) ^ 2 := by unfold P4; decide +kernel
    have : ((2 ^ 256) ^ 2 : ℕ) ≤ p := hP4 ▸ hp
    exact_mod_cast this
  have hs : (2 : ℝ) ^ 256 ≤ Real.sqrt p := Real.le_sqrt_of_sq_le hP
  unfold tailRho
  push_cast
  exact one_div_le_one_div_of_le (by positivity) hs

/-- **`lem:tail-law`(iii), the nonroot mass**: for `p ≥ P₄`, `h_p = P_μ(r) - 1` satisfies
`0 ≤ h_p ≤ C₁ p^{-1/2}`. -/
theorem tail_nonroot_mass (p : ℕ) (hp : P4 ≤ p) :
    0 ≤ upPoly tailWeights (tailR p) - 1 ∧
      upPoly tailWeights (tailR p) - 1 ≤ (tailC 1 : ℝ) * tailR p := by
  set r := tailR p with hr
  have hr0 : 0 ≤ r := tailR_nonneg p
  have hrρ : r ≤ (tailRho : ℝ) := tailR_le p hp
  rw [tailPoly_eq]
  refine ⟨?_, ?_⟩
  · have : 0 ≤ 5988 / 5 * r + 15232626 / 25 * r ^ 2 + 24807984744 / 175 * r ^ 3 +
        50638290432 / 5 * r ^ 4 + 621170191872 / 5 * r ^ 5 + 1877429977088 / 7 * r ^ 6 +
        970455252992 / 7 * r ^ 7 := by positivity
    linarith
  rw [tailC_one]
  push_cast
  generalize (tailRho : ℝ) = ρ at hrρ ⊢
  have hk : ∀ k : ℕ, r ^ (k + 1) ≤ ρ ^ k * r := by
    intro k
    rw [pow_succ, mul_comm (r ^ k) r, mul_comm (ρ ^ k) r]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hrρ k) hr0
  have h2 := hk 1
  have h3 := hk 2
  have h4 := hk 3
  have h5 := hk 4
  have h6 := hk 5
  have h7 := hk 6
  simp only [Nat.reduceAdd, pow_one] at h2 h3 h4 h5 h6 h7
  linarith [h2, h3, h4, h5, h6, h7]

end Sarkozy.PartV
