module

public import Sarkozy.PositiveRoots.CoherentEndpointChecks
public import Sarkozy.PositiveRoots.CoherentEndpointSupport
public import Sarkozy.PositiveRoots.FiniteMatrixBound

/-!
# The exact coherent endpoint caps `5.413` and `2.19`

The active matrix certificates extend to all 64 supports, including the
inactive coordinates. Finite-prime errors and the analytic feature frames
are separate from these leading coefficient matrices.
-/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentEndpoint

open Finset Sarkozy.SpectralD Sarkozy.SpectralC

theorem model_eq_shift (c : Cut) (i j : Fin (size c)) :
    gaussian (modelReal c i j) (modelImag c i j) =
      (denominator c : ℂ) * ((if i = j then (cap c : ℂ) else 0) + leading c i j) := by
  unfold modelReal modelImag leading fullLeading
  cases c <;> simp only [denominator, dictionaryScale, diagonal, cap]
  all_goals
    push_cast
    split_ifs <;> apply Complex.ext <;> simp [gaussian] <;> ring

theorem restricted_bound (c : Cut) (x : Fin (size c) → ℂ) :
    -(cap c : ℝ) * ∑ i, ‖x i‖ ^ 2 ≤ (qform (leading c) x).re := by
  apply lower_bound_of_scaled_nonneg (leading c) (modelReal c) (modelImag c)
    (s := (denominator c : ℝ)) (by cases c <;> norm_num [denominator])
    _ (checked_matrix_nonneg c) x
  intro i j
  have hc : (cap c : ℂ) = ((cap c : ℝ) : ℂ) := by cases c <;> norm_num [cap]
  have hd : (denominator c : ℂ) = ((denominator c : ℝ) : ℂ) := by simp
  simpa only [hc, hd] using model_eq_shift c i j

theorem full_bound (c : Cut) (x : Fin 64 → ℂ) :
    -(cap c : ℝ) * ∑ i, ‖x i‖ ^ 2 ≤ (qform (fullLeading c) x).re := by
  apply lower_bound_of_restriction (fullLeading c) (embedding c)
    (by cases c <;> norm_num [cap]) (fullLeading_zero c) _ x
  exact restricted_bound c

theorem chamber_bound (x : Fin 64 → ℂ) :
    -((5413 : ℝ) / 1000) * ∑ i, ‖x i‖ ^ 2 ≤ (qform (fullLeading .chamber) x).re := by
  simpa only [cap, Rat.cast_div, Rat.cast_ofNat] using full_bound .chamber x

theorem layer_bound (x : Fin 64 → ℂ) :
    -((219 : ℝ) / 100) * ∑ i, ‖x i‖ ^ 2 ≤ (qform (fullLeading .layer) x).re := by
  simpa only [cap, Rat.cast_div, Rat.cast_ofNat] using full_bound .layer x

end Sarkozy.PositiveRoots.CoherentEndpoint
