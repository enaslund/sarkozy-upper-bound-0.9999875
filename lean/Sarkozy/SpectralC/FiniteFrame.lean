module

public import Sarkozy.SpectralC.MatrixKernel

/-! Synthesis and analysis of a finite real feature family from its Gram matrix. -/

@[expose] public section

namespace Sarkozy.SpectralC

open Finset
open Sarkozy.JointRows.StarOps (expect_finset_sum)
open scoped BigOperators

variable {I X : Type*} [Fintype I] [Fintype X]

noncomputable def realFeatureGram (μ : FiniteLaw X) (W : I → X → ℝ) (a b : I) : ℝ :=
  μ.expect (fun x => W a x * W b x)

theorem finiteFrame_gram_bound [DecidableEq I] (μ : FiniteLaw X) (W : I → X → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hd : ∀ a, μ.expect (fun x => W a x ^ 2) ≤ 1)
    (ho : ∀ a b, a ≠ b → |realFeatureGram μ W a b| ≤ ε) :
    NormLe (fun a b => (realFeatureGram μ W a b : ℂ))
      (1 + ((Fintype.card I : ℝ) - 1) * ε) := by
  apply normLe_schur _ (fun a b => if a = b then 1 else ε)
  · intro a b
    split_ifs <;> positivity
  · intro a b
    simp only [eq_comm]
  · intro a b
    rw [Complex.norm_real, Real.norm_eq_abs]
    by_cases hab : a = b
    · subst b
      rw [ite_eq_left rfl, realFeatureGram,
        abs_of_nonneg (μ.expect_nonneg fun _ => mul_self_nonneg _)]
      simpa only [pow_two] using hd a
    · rw [ite_eq_right hab]
      exact ho a b hab
  · intro a
    calc
      _ = ∑ b : I, (ε + if a = b then 1 - ε else 0) := by
        apply sum_congr rfl
        intro b _
        split_ifs <;> ring
      _ = (Fintype.card I : ℝ) * ε + (1 - ε) := by
        rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
        simp
      _ = 1 + ((Fintype.card I : ℝ) - 1) * ε := by ring
      _ ≤ _ := le_rfl

theorem finiteFrame_gram (μ : FiniteLaw X) (W : I → X → ℝ) (u : I → ℝ) :
    μ.expect (fun x => (∑ a, u a * W a x) ^ 2) =
      ∑ a, ∑ b, u a * realFeatureGram μ W a b * u b := by
  have he (x : X) : (∑ a, u a * W a x) ^ 2 =
      ∑ a, ∑ b, (u a * u b) * (W a x * W b x) := by
    rw [pow_two, sum_mul]
    apply sum_congr rfl
    intro a _
    rw [mul_sum]
    exact sum_congr rfl fun b _ => by ring
  simp_rw [he, expect_finset_sum, FiniteLaw.expect_const_mul]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by
    unfold realFeatureGram
    ring

theorem finiteFrame_synthesis (μ : FiniteLaw X) (W : I → X → ℝ) {κ : ℝ}
    (hM : NormLe (fun a b => (realFeatureGram μ W a b : ℂ)) κ) (u : I → ℝ) :
    μ.expect (fun x => (∑ a, u a * W a x) ^ 2) ≤ κ * ∑ a, u a ^ 2 := by
  rw [finiteFrame_gram]
  have h := normLe_real hM u u
  have hs : 0 ≤ ∑ a, u a ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  calc
    _ ≤ |∑ a, ∑ b, u a * realFeatureGram μ W a b * u b| := le_abs_self _
    _ ≤ κ * Real.sqrt (∑ a, u a ^ 2) * Real.sqrt (∑ a, u a ^ 2) := h
    _ = _ := by rw [mul_assoc, Real.mul_self_sqrt hs]

/-- The dual bound, with no nondegeneracy condition on the finite law. -/
theorem finiteFrame_analysis (μ : FiniteLaw X) (W : I → X → ℝ) {κ : ℝ}
    (hκ : 0 ≤ κ)
    (hF : ∀ u : I → ℝ, μ.expect (fun x => (∑ a, u a * W a x) ^ 2) ≤ κ * ∑ a, u a ^ 2)
    (f : X → ℝ) :
    (∑ a, (μ.expect (fun x => W a x * f x)) ^ 2) ≤
      κ * μ.expect (fun x => f x ^ 2) := by
  let u := fun a => μ.expect (fun x => W a x * f x)
  let N := ∑ a, u a ^ 2
  let F := fun x => ∑ a, u a * W a x
  have hN : 0 ≤ N := sum_nonneg fun _ _ => sq_nonneg _
  have hadj : μ.expect (fun x => F x * f x) = N := by
    simp only [F, sum_mul, mul_assoc, expect_finset_sum, FiniteLaw.expect_const_mul]
    simp only [N, u, pow_two]
  have hcs := μ.cauchy_schwarz_sq F f
  rw [hadj] at hcs
  have hb := mul_le_mul_of_nonneg_right (hF u) (μ.second_moment_nonneg f)
  change N ≤ κ * μ.expect (fun x => f x ^ 2)
  rcases hN.eq_or_lt with hz | hz
  · rw [← hz]
    exact mul_nonneg hκ (μ.second_moment_nonneg f)
  · change μ.expect (fun x => F x ^ 2) * _ ≤ κ * N * _ at hb
    nlinarith

end Sarkozy.SpectralC
