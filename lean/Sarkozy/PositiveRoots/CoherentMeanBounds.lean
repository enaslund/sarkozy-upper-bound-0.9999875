module

public import Sarkozy.PositiveRoots.CoherentMeanChecks

/-!
# The coherent invariant-mean matrix caps

All three bounds concern matrices collected from the actual dictionary.
The estimates for the corresponding analytic mean frames remain separate.
-/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentMean

open Finset Sarkozy.SpectralD Sarkozy.SpectralC

theorem model_eq_shift (k : Kind) (i j : Fin (size k)) :
    gaussian (modelReal k i j) 0 =
      (300 : ℂ) * ((if i = j then (cap k : ℂ) else 0) + leading k i j) := by
  unfold modelReal cap leading gaussian
  push_cast
  split_ifs <;> apply Complex.ext <;> simp <;> ring

theorem mean_bound (k : Kind) (x : Fin (size k) → ℂ) :
    -(cap k : ℝ) * ∑ i, ‖x i‖ ^ 2 ≤ (qform (leading k) x).re := by
  have h := checked_matrix_nonneg k x
  simp_rw [model_eq_shift] at h
  rw [CoherentMatrix.qform_scalar] at h
  have hb : 0 ≤ (qform
      (fun i j => (if i = j then (cap k : ℂ) else 0) + leading k i j) x).re := by
    norm_num at h
    linarith
  have he := qform_shift (fun i j => -leading k i j) (cap k : ℝ) x
  have hc : ((cap k : ℝ) : ℂ) = (cap k : ℂ) := by
    cases k <;> norm_num [cap, capNumerator]
  simp only [sub_neg_eq_add, CoherentMatrix.qform_neg, Complex.neg_re, hc] at he
  rw [he] at hb
  linarith

theorem core_leading (i j : Fin 5) :
    leading .core i j =
      (CoherentMatrix.coefficient (index .core i) (index .core j) : ℂ) := by
  simp [leading, numerator, CoherentMatrix.coefficient_eq]

theorem mixed_leading (i j : Fin 10) :
    leading .mixed i j =
      (CoherentMatrix.coefficient (index .mixed i) (index .mixed j) : ℂ) := by
  simp [leading, numerator, CoherentMatrix.coefficient_eq]

theorem layer_leading (i j : Fin 15) :
    leading .layer i j = (layerCoefficient (index .layer i) (index .layer j) : ℂ) := by
  simp [leading, numerator, layerCoefficient_eq]

theorem core_mean_bound (x : Fin 5 → ℂ) :
    -((7 : ℝ) / 100) * ∑ i, ‖x i‖ ^ 2 ≤ (qform (leading .core) x).re := by
  have h := mean_bound .core x
  norm_num [cap, capNumerator] at h ⊢
  exact h

theorem mixed_mean_bound (x : Fin 10 → ℂ) :
    -((21 : ℝ) / 100) * ∑ i, ‖x i‖ ^ 2 ≤ (qform (leading .mixed) x).re := by
  have h := mean_bound .mixed x
  norm_num [cap, capNumerator] at h ⊢
  exact h

theorem layer_mean_bound (x : Fin 15 → ℂ) :
    -((21 : ℝ) / 100) * ∑ i, ‖x i‖ ^ 2 ≤ (qform (leading .layer) x).re := by
  have h := mean_bound .layer x
  norm_num [cap, capNumerator] at h ⊢
  exact h

theorem selected_mean_below :
    CoherentMatrix.strength * (16 * cap .core + cap .mixed) < (16 : ℚ) / 5 ∧
      (16 : ℚ) / 5 < CoherentMatrix.cap := by
  decide +kernel

theorem endpoint_means_below :
    (12000 / 5021 : ℚ) * (16 * cap .core + cap .mixed) < 16 / 5 ∧
      (12000 / 5021 : ℚ) * cap .layer < 1 := by
  decide +kernel

end Sarkozy.PositiveRoots.CoherentMean
