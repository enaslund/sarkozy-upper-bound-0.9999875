module

public import Sarkozy.MeanCredit.Aggregate
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

/-!
# Family (i) of the joint mean, completed: `64 Δ_α`

`paper/sections/24a_joint_mean.tex`, `prop:joint-middle-mean` (family (i): coefficient
`4/(H_*² C(n,2))` on the selected pair, "its exponential completion, after division by `64`, is
`x² ∑_{j ≥ 0} w^j/(16 H_*² (j+2)!)`"), `eq:joint-alpha`.

* `hasSum_exp_shift2`: `∑_j w^j/(j+2)! = (e^w − 1 − w)/w²` (`w ≠ 0`);
* **`hasSum_familyI`**: the per-pair coefficient `4/(H² C(j+2,2))`, completed over unordered pairs
  (`x²/2`) and `j` outside factors (`w^j/j!`), has sum `64 Δ_α = 64 · x²/(16H²) · (e^w − 1 − w)/w²`.

So the aggregation `wtP` (`1/C(j+2,2)` on the `F²` labels) is the one under which the formal mean
coefficient `4/H_*²` of `diagB` completes to the ledger's `Δ_α`; without it the completion would be
`C(j+2,2)` times larger termwise (`familyI_overclaim`).
-/

open Finset

namespace Sarkozy.MeanCredit

/-- The tail `∑_j w^j/(j+2)! = (e^w − 1 − w)/w²` of the exponential series. -/
theorem hasSum_exp_shift2 (w : ℝ) (hw : w ≠ 0) :
    HasSum (fun j : ℕ => w ^ j / (j + 2).factorial) ((Real.exp w - 1 - w) / w ^ 2) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) w
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := (hasSum_nat_add_iff' 2).mpr h
  simp only [sum_range_succ, sum_range_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, zero_add, pow_one, Nat.factorial_one] at h2
  have h3 := h2.div_const (w ^ 2)
  have e : (fun j : ℕ => w ^ (j + 2) / ((j + 2).factorial : ℝ) / w ^ 2) =
      fun j : ℕ => w ^ j / (j + 2).factorial := by
    funext j
    have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw
    rw [pow_add]
    field_simp
  rw [e] at h3
  convert h3 using 1
  ring

/-- **Family (i), completed, is `64 Δ_α`** (`prop:joint-middle-mean`, `eq:joint-alpha`): the
per-pair coefficient `4/(H² C(j+2,2))`, completed over unordered pairs (`x²/2`) and `j` outside
factors of total `w` (`w^j/j!`), sums to `64 · x²/(16 H²) · (e^w − 1 − w)/w²`. -/
theorem hasSum_familyI (H x w : ℝ) (hH : H ≠ 0) (hw : w ≠ 0) :
    HasSum (fun j : ℕ => 4 / (H ^ 2 * (Nat.choose (j + 2) 2 : ℝ)) * (x ^ 2 / 2) *
        (w ^ j / j.factorial))
      (64 * (x ^ 2 / (16 * H ^ 2) * ((Real.exp w - 1 - w) / w ^ 2))) := by
  have h := (hasSum_exp_shift2 w hw).mul_left (4 * x ^ 2 / H ^ 2)
  have e : (fun j : ℕ => 4 / (H ^ 2 * (Nat.choose (j + 2) 2 : ℝ)) * (x ^ 2 / 2) *
      (w ^ j / j.factorial)) = fun j : ℕ => 4 * x ^ 2 / H ^ 2 * (w ^ j / (j + 2).factorial) := by
    funext j
    rw [familyI_completed H x w hH j]
    ring
  rw [e]
  convert h using 1
  field_simp
  ring

end Sarkozy.MeanCredit
