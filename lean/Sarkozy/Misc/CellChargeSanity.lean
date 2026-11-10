module

public import Sarkozy.Misc.BlockChargeExact

@[expose] public section

/-!
# Non-vacuity checks for the block charges

(`lem:record:block-charge`, `lem:record:lower-start-sums`)

* `exists_eta_bound`: the error hypothesis `|θ(t; 4, 3) - t/2| ≤ e t` of the general statements
  (`Sarkozy.Misc.cell_charge`, `Sarkozy.Misc.lower_start_sums_cells`) is satisfiable on every
  interval `[x_0, x_𝗇]` with `x_0 > 0`; `thm:bmor` and the small-range bounds only make `e` small.
* The side conditions of `cell_charge_geometric_bmor` (even endpoints `x ≤ Y` with
  `x ≥ X_Ch - 1`, `𝗇 ≥ 1` cells, `n_j ≥ 1`, `a, s ≥ 0`) are discharged at `[X_Ch, 2 X_Ch)` with
  `𝗇 = 128`, `n_j = 1`, `a = s = 1`; the cell-point hypotheses (monotonicity, no endpoint a prime
  `≡ 3 (mod 4)`) are proved inside that theorem from the evenness of `x` and `Y`.
* The hypotheses of `block_charge_greedy` and `lower_start_sums_greedy` are discharged for a
  one-prime list `[3]` with a constant upper logarithm `𝔲 ≡ 2⁴¹`.
-/

open Finset

namespace Sarkozy.Misc

open Sarkozy.PartV Sarkozy.PartVLaws

theorem theta4_nonneg (t : ℝ) (r : ℕ) : 0 ≤ Target.theta4 t r :=
  Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p

theorem theta4_mono {t t' : ℝ} (h : t ≤ t') (r : ℕ) : Target.theta4 t r ≤ Target.theta4 t' r := by
  unfold Target.theta4
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset_filter _
      (range_subset_range.mpr (Nat.add_le_add_right (Nat.floor_le_floor h) 1))
  · exact fun p _ _ => Real.log_natCast_nonneg p

/-- **The error hypothesis is satisfiable**: on `[x_0, x_𝗇]` with `x_0 > 0`,
`|θ(t; 4, 3) - t/2| ≤ (θ(x_𝗇; 4, 3)/x_0 + 1/2) t`. -/
theorem exists_eta_bound {x0 xn : ℝ} (hx0 : 0 < x0) :
    ∃ e, ∀ t, x0 ≤ t → t ≤ xn → |Target.theta4 t 3 - t / 2| ≤ e * t := by
  refine ⟨Target.theta4 xn 3 / x0 + 1 / 2, fun t ht1 ht2 => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le hx0 ht1
  have hθ0 := theta4_nonneg t 3
  have hθm := theta4_mono ht2 3
  have hθn := theta4_nonneg xn 3
  have h1 : Target.theta4 xn 3 ≤ Target.theta4 xn 3 / x0 * t := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hx0]
    nlinarith
  rw [abs_le]
  constructor <;> nlinarith

/-- The side conditions of `cell_charge_geometric_bmor` are satisfiable: `[X_Ch, 2 X_Ch)`,
`128` cells, `n_j = 1`, `a = s = 1`. -/
example (hB : Target.BMOR) :=
  cell_charge_geometric_bmor hB (X := 4800162890) (Y := 9600325780) ⟨2400081445, by norm_num⟩
    ⟨4800162890, by norm_num⟩ (by norm_num) (by norm_num) (n := 128) (by norm_num) (fun _ => 1)
    (fun _ _ => le_rfl) (a := 1) (s := 1) zero_le_one zero_le_one

/-- The side conditions of `cell_charge_geometric_thetaSmallTable` are satisfiable:
`[2²⁶, 2²⁷)`, `8` cells, `n_j = 1`, `a = s = 1`. -/
example (hT : Target.ThetaSmallTable) :=
  cell_charge_geometric_thetaSmallTable hT (X := 67108864) (Y := 134217728) ⟨33554432, by norm_num⟩
    ⟨67108864, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (n := 8) (by norm_num)
    (fun _ => 1) (fun _ _ => le_rfl) (a := 1) (s := 1) zero_le_one zero_le_one

/-- The hypotheses of `block_charge_greedy` are satisfiable: the one-prime part `[3]` with
`𝔲 ≡ 2⁴¹` (so `log 3 < 2 = 𝔲(3)/2⁴⁰`), `a = 1`, `d = 2`. -/
example :=
  block_charge_greedy (fun _ => 2 ^ 41) (fun _ => by unfold integerBudget middleBudget; norm_num)
    [3] (by simp) (by simp) (by simp)
    (by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      have h3 : Real.log 3 < 2 := by
        rw [Real.log_lt_iff_lt_exp (by norm_num)]
        have := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
        linarith
      have he : ((2 ^ 41 : ℕ) : ℝ) / 2 ^ 40 = 2 := by norm_num
      rw [he]
      exact_mod_cast h3)
    (a := 1) zero_le_one (d := 2) (Or.inl rfl)

/-- The hypotheses of `lower_start_sums_greedy` are satisfiable: the one-prime part `[3]`. -/
example :=
  lower_start_sums_greedy (fun _ => 2 ^ 41) integerBudget
    (fun _ => by unfold integerBudget middleBudget; norm_num) [3] (by simp) (by simp)

end Sarkozy.Misc
