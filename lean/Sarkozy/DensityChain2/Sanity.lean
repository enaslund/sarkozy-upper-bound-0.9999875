module

public import Sarkozy.DensityChain2.PaperData

@[expose] public section

/-!
# Sanity checks for `DensityChain2`

* **The per-atom moment hypotheses are satisfiable**: the uniform law on `Slot → X` has unit mixed
  `L^{72/ϑ}` (`uniform_mixedLp_theta`).
* **They are not implied by uniform marginals** (`not_mixedLp_theta_diag`): the diagonal law
  (all 72 slots equal, uniform on `Bool`) has uniform one-slot marginals (so unit mixed `L^{72}`,
  `mixedLpBound_of_uniform_marginals`) but not unit mixed `L^{72/ϑ}` at the upgraded
  `ϑ = 1014587/10⁶` (`upgradedDensityExponent`). So `hatom` at `ϑ > 1` is a genuine property of
  the selected laws (`lem:density:packets`), not a consequence of the data's positivity and
  marginals. Since 7 November 2026 the endgame runs at `densityExponent = 1`, where it is.
* The parity condition holds for the paper's exponents (`paperEP_parity`), and the paper's tail
  family is monotone with its new primes above the cutoff (`paperTailPrimes_mono`,
  `paperTailPrimes_large`), so the hypotheses of the restoration lemmas are met.
-/

namespace Sarkozy.DensityChain2

open Finset
open scoped BigOperators

theorem one_le_seventytwo_div_theta : 1 ≤ 72 / densityExponent := by
  unfold densityExponent
  norm_num

/-- The uniform law has unit mixed `L^{72/ϑ}`. -/
theorem uniform_mixedLp_theta {X : Type} [Fintype X] [Nonempty X] :
    MixedLpBound (FiniteLaw.uniform (Slot → X)) (72 / densityExponent) 1 :=
  mixedLpBound_uniform one_le_seventytwo_div_theta

/-- The diagonal law: one uniform label copied to all slots. -/
noncomputable def diagLaw : FiniteLaw (Slot → Bool) :=
  (FiniteLaw.uniform Bool).map (fun x => fun _ : Slot => x)

theorem expect_diagLaw (F : (Slot → Bool) → ℝ) :
    diagLaw.expect F = (FiniteLaw.uniform Bool).expect (fun x => F (fun _ => x)) := by
  unfold diagLaw
  rw [FiniteLaw.expect_map]
  rfl

/-- The diagonal law has uniform one-slot marginals. -/
theorem hasUniformMarginals_diagLaw : HasUniformMarginals diagLaw := by
  intro v f
  rw [expect_diagLaw]

/-- **Uniform marginals do not give unit mixed `L^{72/ϑ}` at the upgraded `ϑ = 1014587/10⁶`**
(`Sarkozy.upgradedDensityExponent`; since 7 November 2026 the endgame's `densityExponent` is `1`,
where uniform marginals do give it): the diagonal law fails it (test functions `f_v = 1_{true}`:
the left side is `1/2`, the right side `(1/2)^ϑ < 1/2`). -/
theorem not_mixedLp_theta_diag : ¬ MixedLpBound diagLaw (72 / upgradedDensityExponent) 1 := by
  intro hm
  set f : Bool → ℝ := fun b => if b then 1 else 0 with hf
  have h := hm (fun _ => f)
  have hl : diagLaw.expect (fun z => ∏ v, f (z v)) = 1 / 2 := by
    rw [expect_diagLaw, FiniteLaw.expect_uniform, Fintype.sum_bool, Fintype.card_bool]
    simp only [hf, ↓reduceIte, prod_const_one, Bool.false_eq_true, prod_const, card_univ,
      card_slot]
    norm_num
  have hθ : (0 : ℝ) < 72 / upgradedDensityExponent := by unfold upgradedDensityExponent; norm_num
  have hmom : (FiniteLaw.uniform Bool).moment (72 / upgradedDensityExponent) f = 1 / 2 := by
    unfold FiniteLaw.moment
    rw [FiniteLaw.expect_uniform, Fintype.sum_bool, Fintype.card_bool]
    simp only [hf, ↓reduceIte, Bool.false_eq_true, abs_one, abs_zero, Real.one_rpow,
      Real.zero_rpow hθ.ne']
    norm_num
  have hr : ∏ v : Slot, (FiniteLaw.uniform Bool).lpNorm (72 / upgradedDensityExponent) f =
      (1 / 2 : ℝ) ^ upgradedDensityExponent := by
    rw [prod_const, card_univ, card_slot]
    unfold FiniteLaw.lpNorm
    have he : 1 / (72 / upgradedDensityExponent) * ((72 : ℕ) : ℝ) = upgradedDensityExponent := by
      unfold upgradedDensityExponent
      norm_num
    rw [hmom, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), he]
  rw [hl, hr, one_mul, abs_of_pos (by norm_num)] at h
  have hlt : (1 / 2 : ℝ) ^ upgradedDensityExponent < (1 / 2 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num)
      (by unfold upgradedDensityExponent; norm_num)
  rw [Real.rpow_one] at hlt
  linarith

end Sarkozy.DensityChain2
