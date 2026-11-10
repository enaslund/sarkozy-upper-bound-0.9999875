module

public import Sarkozy.JointRows.StarAssembly
public import Sarkozy.JointRows.StarHoeffding

/-!
# Toy instances for the `prop:conditional-star` files

* `toy_joint_star_inputs`: the hypotheses of `joint_star_inputs` with nonzero forms on `ℝ`
  (`𝓕* = id`, `M_E = M_F = (u, w) ↦ uw`, `T_mean = κr e (x, y) ↦ xy/2`).
* `toy_mean_block_bound`: the hypotheses of `mean_block_bound` with a nonzero `𝒱 ← 𝒱` block.
* `toy_hoeffding`: two functions with different exact supports on a product of two copies of the
  uniform law on `Fin 2` are orthogonal (`hoeffding_orthogonal` is not vacuous: the exact-support
  conditions hold for the coordinate characters `x ↦ ±1`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.Star.StarSanity

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

/-- **`joint_star_inputs` applies with nonzero forms.** -/
theorem toy_joint_star_inputs :
    let tE : ℝ → ℝ → ℝ := fun x y => 2 * (x * y) + x * y / 2
    let mE : ℝ → ℝ → ℝ := fun u w => u * w
    let aE : ℝ → ℝ → ℝ := fun x y => x * y / 2
    (∀ z, jointForm tE tE z = 2 * jointForm mE mE (pairMap id z) + jointForm aE aE z) ∧
    (∀ z, ‖pairMap (id : ℝ → ℝ) z‖ ≤ ‖z‖) ∧
    (∀ z, |jointForm aE aE z| ≤ 2 * (1 / 4 + 1 / 4) * ‖z‖ ^ 2) := by
  intro tE mE aE
  refine joint_star_inputs tE tE aE aE mE mE id (by norm_num) (by norm_num) (fun x y => ?_)
    (fun x y => ?_) (fun x => le_rfl) (fun x y => ?_) (fun x y => ?_)
  · simp only [tE, mE, aE, id]
  · simp only [tE, mE, aE, id]
  all_goals
    simp only [aE, Real.norm_eq_abs]
    rw [abs_div, abs_mul, abs_two]
    nlinarith [abs_nonneg x, abs_nonneg y, mul_nonneg (abs_nonneg x) (abs_nonneg y)]

/-- **`mean_block_bound` applies with a nonzero block.** -/
theorem toy_mean_block_bound (x y : ℝ) : |x * y| ≤ 1 * eStar 1 0 * ‖x‖ * ‖y‖ := by
  refine mean_block_bound (fun x y => x * y) id (fun _ => 0) id (fun _ => 0) zero_le_one
    zero_le_one (by intro x y; simp) (by intro x; simp) (by intro y; simp) (by intro x y; simp)
    (by intro x y; simp) (by intro x y; simp) (by intro x y; simp) x y

/-- The coordinate character `x ↦ (-1)^{x_i}` of `Fin 2`. -/
def chr (i : Fin 2) (x : Fin 2 → Fin 2) : ℝ := if x i = 0 then 1 else -1

theorem exact_chr (i : Fin 2) :
    ExactSupport (fun _ : Fin 2 => FiniteLaw.uniform (Fin 2)) {i} (chr i) := by
  refine ⟨fun x x' h => ?_, fun j hj x => ?_⟩
  · simp only [chr, h i (Finset.mem_singleton_self i)]
  · rw [Finset.mem_singleton] at hj
    subst hj
    simp [condMean, chr, FiniteLaw.uniform, Fin.sum_univ_two]

/-- **`hoeffding_orthogonal` is not vacuous**: `E[χ₀ χ₁] = 0` for the two coordinate
characters. -/
theorem toy_hoeffding :
    (blockLaw (fun _ : Fin 2 => FiniteLaw.uniform (Fin 2))).expect
      (fun x => chr 0 x * chr 1 x) = 0 :=
  hoeffding_orthogonal _ (by decide) (exact_chr 0) (exact_chr 1)

end Sarkozy.JointRows.Star.StarSanity
