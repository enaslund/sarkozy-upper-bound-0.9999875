module

public import Sarkozy.Cuts.Swapped

/-! Finite sums and bounded multipliers in the real finite-law norm. -/

@[expose] public section

namespace Sarkozy.Cuts

open Finset Sarkozy.Recentering

variable {Ω I : Type*} [Fintype Ω]

theorem nrm_sub_le (ν : FiniteLaw Ω) (f g : Ω → ℝ) :
    nrm ν (fun x => f x - g x) ≤ nrm ν f + nrm ν g := by
  have h := nrm_add_le ν f (fun x => -1 * g x)
  rw [nrm_smul] at h
  simpa only [neg_one_mul, ← sub_eq_add_neg, abs_neg, abs_one, one_mul] using h

theorem nrm_sum_le (ν : FiniteLaw Ω) (s : Finset I) (F : I → Ω → ℝ) :
    nrm ν (fun x => ∑ i ∈ s, F i x) ≤ ∑ i ∈ s, nrm ν (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nrm, ip, FiniteLaw.expect_const]
  | @insert i s hi ih =>
    simp only [sum_insert hi]
    exact (nrm_add_le ν (F i) (fun x => ∑ j ∈ s, F j x)).trans (add_le_add le_rfl ih)

theorem nrm_mul_le (ν : FiniteLaw Ω) (A f : Ω → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ x, |A x| ≤ C) : nrm ν (fun x => A x * f x) ≤ C * nrm ν f := by
  have hs : nrm ν (fun x => A x * f x) ^ 2 ≤ (C * nrm ν f) ^ 2 := by
    rw [nrm_sq_expect, mul_pow, nrm_sq_expect, ← FiniteLaw.expect_const_mul]
    apply FiniteLaw.expect_mono
    intro x
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (A x)) (hA x) 2) (sq_nonneg _)
  exact (abs_le_of_sq_le_sq' hs (mul_nonneg hC (nrm_nonneg _ _))).2

end Sarkozy.Cuts
