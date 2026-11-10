module

public import Sarkozy.SpectralD.TailGramScalars

/-!
# Uniform Gram-comparison rows for the root cuts

Cross degrees at most 12 and the tail count and density bounds control
both error matrices. Each absolute row allowance is at most 1/2000.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Sarkozy.SpectralC

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

theorem betaG_tail_entry (N : U → Finset U) (ς : U → U → ZMod p) (e : ℕ → ℝ)
    (hr : ∀ k, (N k).card ≤ 12) (he0 : ∀ t, 0 ≤ e t)
    (he : ∀ t ≤ 24, e t ≤ 2⁻¹ ^ 50) (k l : U) : betaG N ς e k l ≤ 2⁻¹ ^ 20 := by
  have hk := he _ ((hr k).trans (by norm_num))
  have hl := he _ ((hr l).trans (by norm_num))
  have hu := he _ ((card_union_le (N k) (N l)).trans
    (show (N k).card + (N l).card ≤ 24 by have := hr k; have := hr l; omega))
  have hi : (N k ∩ N l).card ≤ 12 := (card_le_card inter_subset_left).trans (hr k)
  unfold betaG
  split_ifs
  · calc _ ≤ (2 ^ 12 * (2 : ℝ)⁻¹ ^ 50) / (1 - (2 : ℝ)⁻¹ ^ 50) := by
          apply div_le_div₀ (by positivity) _ (by norm_num) (by linarith)
          exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (hr k)) hk (he0 _) (by positivity)
      _ ≤ 2⁻¹ ^ 20 := by norm_num
  · have hm : max ((1 + e (N k ∪ N l).card) /
          ((1 - e (N k).card) * (1 - e (N l).card)) - 1)
          (1 - (1 - e (N k ∪ N l).card) /
            ((1 + e (N k).card) * (1 + e (N l).card))) ≤ (2 : ℝ)⁻¹ ^ 46 := by
      exact max_le (by linarith [tail_overlap_upper hk hl hu])
        (tail_overlap_lower (he0 _) (he0 _) hk hl hu)
    calc _ ≤ 2 ^ (N k ∩ N l).card * (2 : ℝ)⁻¹ ^ 46 :=
          mul_le_mul_of_nonneg_left hm (by positivity)
      _ ≤ 2 ^ 12 * (2 : ℝ)⁻¹ ^ 46 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) (by positivity)
      _ ≤ 2⁻¹ ^ 20 := by norm_num
  · positivity

theorem bX_tail_entry (N : U → Finset U) (ς : U → U → ZMod p) (e : ℕ → ℝ)
    (R : U → ℝ) (hr : ∀ k, (N k).card ≤ 12)
    (he : ∀ t ≤ 24, e t ≤ 2⁻¹ ^ 50) (hR1 : ∀ k, 1 ≤ R k)
    (hR : ∀ k, R k ≤ 1 + 2⁻¹ ^ 40) (k l : U) : bX N ς e R k l ≤ 2⁻¹ ^ 20 := by
  have hk := he _ ((hr k).trans (by norm_num))
  have hl := he _ ((hr l).trans (by norm_num))
  have hu := he _ ((card_union_le (N k) (N l)).trans
    (show (N k).card + (N l).card ≤ 24 by have := hr k; have := hr l; omega))
  have hi : (N k ∩ N l).card ≤ 12 := (card_le_card inter_subset_left).trans (hr k)
  have hdk0 : 0 ≤ R k - 1 := by linarith [hR1 k]
  have hdl0 : 0 ≤ R l - 1 := by linarith [hR1 l]
  have hdk : R k - 1 ≤ (2 : ℝ)⁻¹ ^ 40 := by linarith [hR k]
  have hdl : R l - 1 ≤ (2 : ℝ)⁻¹ ^ 40 := by linarith [hR l]
  unfold bX
  split_ifs
  · calc _ ≤ (2 ^ 12 * ((2 : ℝ)⁻¹ ^ 40) ^ 2) / (1 - (2 : ℝ)⁻¹ ^ 50) := by
          apply div_le_div₀ (by positivity) _ (by norm_num) (by linarith)
          exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (hr k))
            (pow_le_pow_left₀ hdk0 hdk 2) (sq_nonneg _) (by positivity)
      _ ≤ 2⁻¹ ^ 20 := by norm_num
  · have hfac : 2 ^ (N k ∩ N l).card * (1 + e (N k ∪ N l).card) /
          ((1 - e (N k).card) * (1 - e (N l).card)) ≤ (2 : ℝ) ^ 13 := by
      rw [mul_div_assoc]
      calc _ ≤ 2 ^ (N k ∩ N l).card * (1 + (2 : ℝ)⁻¹ ^ 46) :=
            mul_le_mul_of_nonneg_left (tail_overlap_upper hk hl hu) (by positivity)
        _ ≤ 2 ^ 12 * (1 + (2 : ℝ)⁻¹ ^ 46) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) (by positivity)
        _ ≤ 2 ^ 13 := by norm_num
    have hdiff : (R k - 1) + (R l - 1) + (R k - 1) * (R l - 1) ≤ (2 : ℝ)⁻¹ ^ 38 := by
      calc _ ≤ 2⁻¹ ^ 40 + 2⁻¹ ^ 40 + (2⁻¹ ^ 40) * (2⁻¹ ^ 40) := by gcongr
        _ ≤ (2 : ℝ)⁻¹ ^ 38 := by norm_num
    exact (mul_le_mul hfac hdiff (by positivity) (by positivity)).trans (by norm_num)
  · positivity

theorem betaG_tail_row (N : U → Finset U) (ς : U → U → ZMod p) (e : ℕ → ℝ)
    (hn : Fintype.card U = 36) (hr : ∀ k, (N k).card ≤ 12) (he0 : ∀ t, 0 ≤ e t)
    (he : ∀ t ≤ 24, e t ≤ 2⁻¹ ^ 50) (k : U) : ∑ l, betaG N ς e k l ≤ 1 / 2000 := by
  calc _ ≤ ∑ _l : U, (2 : ℝ)⁻¹ ^ 20 :=
        sum_le_sum fun l _ => betaG_tail_entry N ς e hr he0 he k l
    _ = 36 * (2 : ℝ)⁻¹ ^ 20 := by
        simp only [sum_const, card_univ, hn, nsmul_eq_mul, Nat.cast_ofNat]
    _ ≤ 1 / 2000 := by norm_num

theorem bX_tail_row (N : U → Finset U) (ς : U → U → ZMod p) (e : ℕ → ℝ)
    (R : U → ℝ) (hn : Fintype.card U = 36) (hr : ∀ k, (N k).card ≤ 12)
    (he : ∀ t ≤ 24, e t ≤ 2⁻¹ ^ 50)
    (hR1 : ∀ k, 1 ≤ R k) (hR : ∀ k, R k ≤ 1 + 2⁻¹ ^ 40) (k : U) :
    ∑ l, bX N ς e R k l ≤ 1 / 2000 := by
  calc _ ≤ ∑ _l : U, (2 : ℝ)⁻¹ ^ 20 :=
        sum_le_sum fun l _ => bX_tail_entry N ς e R hr he hR1 hR k l
    _ = 36 * (2 : ℝ)⁻¹ ^ 20 := by
        simp only [sum_const, card_univ, hn, nsmul_eq_mul, Nat.cast_ofNat]
    _ ≤ 1 / 2000 := by norm_num

end Sarkozy.SpectralD
