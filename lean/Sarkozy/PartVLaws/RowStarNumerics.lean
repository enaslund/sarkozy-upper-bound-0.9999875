module

public import Sarkozy.PartVLaws.RowStars

/-! Numerical slack in the paper's ten tail row caps. -/

@[expose] public section

namespace Sarkozy.PartVLaws.FieldGraphs.RowCase

open Finset Sarkozy.JointRows Sarkozy.JointRows.StarOps

theorem eStar_le_of_square {d G s : ℝ} (hG : 0 ≤ G) (hs : 0 ≤ 2 * s - d)
    (hsq : d ^ 2 + 4 * G ≤ (2 * s - d) ^ 2) : Star.eStar d (Real.sqrt G) ≤ s := by
  have h := (Real.sqrt_le_iff).mpr ⟨hs, hsq⟩
  unfold Star.eStar
  rw [Real.sq_sqrt hG]
  linarith

theorem leading_gap (c : RowCase) :
    (2 : ℝ) ^ c.pins * Star.eStar c.degree (Real.sqrt c.gram) ≤ c.cap - 1 / 20 := by
  have hb : Star.eStar c.degree (Real.sqrt c.gram) ≤
      ((c.cap : ℝ) - 1 / 20) / 2 ^ c.pins := by
    apply eStar_le_of_square (by positivity)
    · cases c <;> norm_num [pins, degree, gram, cap]
    · cases c <;> norm_num [pins, degree, gram, cap]
  calc
    _ ≤ (2 : ℝ) ^ c.pins * (((c.cap : ℝ) - 1 / 20) / 2 ^ c.pins) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp

theorem mean_count_le (c : RowCase) :
    2 * (Fintype.card c.Index : ℝ) * (sets2 c.Index).card *
      2 ^ Fintype.card c.Index ≤ 2 ^ 29 := by
  have hn : (Fintype.card c.Index : ℝ) ≤ 12 := by exact_mod_cast c.card_index
  have hs : ((sets2 c.Index).card : ℝ) ≤ 2 ^ 12 := by
    have h : (sets2 c.Index).card ≤ 2 ^ 12 :=
      (card_le_univ _).trans (by
        rw [Fintype.card_finset]
        exact Nat.pow_le_pow_right (by norm_num) c.card_index)
    exact_mod_cast h
  have hp : (2 : ℝ) ^ Fintype.card c.Index ≤ 2 ^ 12 :=
    pow_le_pow_right₀ (by norm_num) c.card_index
  have h1 : 2 * (Fintype.card c.Index : ℝ) ≤ 24 := by linarith
  have h2 := mul_le_mul h1 hs (by positivity) (by norm_num : (0 : ℝ) ≤ 24)
  have h := mul_le_mul h2 hp (by positivity) (by positivity)
  exact h.trans (by norm_num)

theorem star_coefficient_le (c : RowCase) {κ β : ℝ} (hβ : 0 ≤ β)
    (hκu : κ ≤ (2 : ℝ) ^ c.pins * (1 + 1 / 100000))
    (hβu : β ≤ (2 : ℝ)⁻¹ ^ 80) :
    κ * (Star.eStar c.degree (Real.sqrt c.gram) +
      2 * Fintype.card c.Index * (sets2 c.Index).card *
        2 ^ Fintype.card c.Index * β) ≤ c.cap - 1 / 25 := by
  have hk32 : κ ≤ 32 := hκu.trans (by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) c.pins_le
    have hm := mul_le_mul_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 1 + 1 / 100000)
    exact hm.trans (by norm_num))
  have hc : (c.cap : ℝ) ≤ 258 := by cases c <;> norm_num [cap]
  have he0 : 0 ≤ Star.eStar c.degree (Real.sqrt c.gram) := by
    unfold Star.eStar
    positivity
  have hlead : κ * Star.eStar c.degree (Real.sqrt c.gram) ≤ c.cap - 9 / 200 := by
    calc
      _ ≤ ((2 : ℝ) ^ c.pins * (1 + 1 / 100000)) *
          Star.eStar c.degree (Real.sqrt c.gram) := mul_le_mul_of_nonneg_right hκu he0
      _ = (1 + 1 / 100000) *
          ((2 : ℝ) ^ c.pins * Star.eStar c.degree (Real.sqrt c.gram)) := by ring
      _ ≤ (1 + 1 / 100000) * ((c.cap : ℝ) - 1 / 20) :=
        mul_le_mul_of_nonneg_left c.leading_gap (by norm_num)
      _ ≤ _ := by linarith
  have herr : κ * (2 * Fintype.card c.Index * (sets2 c.Index).card *
      2 ^ Fintype.card c.Index * β) ≤ 1 / 200 := by
    have h1 := mul_le_mul c.mean_count_le hβu hβ (by positivity : (0 : ℝ) ≤ 2 ^ 29)
    have h2 := mul_le_mul hk32 h1 (by positivity) (by norm_num : (0 : ℝ) ≤ 32)
    exact h2.trans (by norm_num)
  nlinarith

end Sarkozy.PartVLaws.FieldGraphs.RowCase
