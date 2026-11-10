module

public import Sarkozy.SpectralD.TailCounts

/-!
# Scalar estimates for the tail Gram comparison

These rational bounds control the count ratios and the deviations used in
beta, bX, and the coupling error. No asymptotic limiting argument is needed.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Sarkozy.SpectralC

theorem tail_overlap_upper {a b c : ℝ} (ha : a ≤ 2⁻¹ ^ 50) (hb : b ≤ 2⁻¹ ^ 50)
    (hc : c ≤ 2⁻¹ ^ 50) :
    (1 + c) / ((1 - a) * (1 - b)) ≤ 1 + 2⁻¹ ^ 46 := by
  have hden : (1 - (2 : ℝ)⁻¹ ^ 50) ^ 2 ≤ (1 - a) * (1 - b) := by
    rw [pow_two]
    apply mul_le_mul <;> linarith
  calc _ ≤ (1 + (2 : ℝ)⁻¹ ^ 50) / (1 - (2 : ℝ)⁻¹ ^ 50) ^ 2 :=
        div_le_div₀ (by positivity) (by linarith) (by positivity) hden
    _ ≤ 1 + 2⁻¹ ^ 46 := by norm_num

theorem tail_overlap_lower {a b c : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : a ≤ 2⁻¹ ^ 50) (hb : b ≤ 2⁻¹ ^ 50) (hc : c ≤ 2⁻¹ ^ 50) :
    1 - (1 - c) / ((1 + a) * (1 + b)) ≤ 2⁻¹ ^ 46 := by
  have hden : (1 + a) * (1 + b) ≤ (1 + (2 : ℝ)⁻¹ ^ 50) ^ 2 := by
    rw [pow_two]
    gcongr
  have hdiv : (1 - (2 : ℝ)⁻¹ ^ 50) / (1 + (2 : ℝ)⁻¹ ^ 50) ^ 2 ≤
      (1 - c) / ((1 + a) * (1 + b)) :=
    div_le_div₀ (by linarith) (by linarith) (by positivity) hden
  calc _ ≤ 1 - (1 - (2 : ℝ)⁻¹ ^ 50) / (1 + (2 : ℝ)⁻¹ ^ 50) ^ 2 :=
        sub_le_sub_left hdiv 1
    _ ≤ 2⁻¹ ^ 46 := by norm_num

theorem tail_devConst {e R : ℝ} (he0 : 0 ≤ e) (he : e ≤ 2⁻¹ ^ 50)
    (hR1 : 1 ≤ R) (hR : R ≤ 1 + 2⁻¹ ^ 40) :
    0 ≤ devConst R e ∧ devConst R e ≤ 2⁻¹ ^ 38 := by
  have he1 : 0 < 1 - e := by norm_num at he ⊢; linarith
  have hnonneg : 0 ≤ R / (1 - e) - 1 := by
    have : 1 ≤ R / (1 - e) := (le_div_iff₀ he1).mpr (by linarith)
    linarith
  refine ⟨hnonneg.trans (le_max_left _ _), max_le ?_ ?_⟩
  · have hdiv : R / (1 - e) ≤ (1 + (2 : ℝ)⁻¹ ^ 40) / (1 - (2 : ℝ)⁻¹ ^ 50) :=
      div_le_div₀ (by positivity) hR (by norm_num) (by linarith)
    exact (sub_le_sub_right hdiv 1).trans (by norm_num)
  · have hden : (1 + e) * R ≤ (1 + (2 : ℝ)⁻¹ ^ 50) * (1 + (2 : ℝ)⁻¹ ^ 40) := by
      gcongr
    have hdiv := inv_anti₀ (by positivity : 0 < (1 + e) * R) hden
    simpa only [one_div] using (sub_le_sub_left hdiv 1).trans (by norm_num)

end Sarkozy.SpectralD
